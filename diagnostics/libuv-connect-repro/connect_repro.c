/* Issue #58 / leanprover/lean4#15807: a libuv-only reproducer for the stack-cookie
 * failure in uv__tcp_connect on the hosted Windows runner.
 *
 * It drives libuv the way the Lean runtime does (src/runtime/uv/event_loop.cpp in
 * leanprover/lean4): a dedicated loop thread runs uv_run(UV_RUN_ONCE) while holding
 * a recursive mutex, and other threads take that mutex (waking the loop with a
 * uv_async_t) to call into libuv. Each iteration matches diagnostics/connect-repro:
 * init a TCP handle, connect, wait for the result for up to 5 s, shut down and close.
 * The connect is issued from a varying stack depth, so that a write landing on a
 * stale stack slot would hit different frames.
 *
 * usage: connect_repro PORT COUNT
 */
#include <uv.h>

#include <malloc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uv_loop_t* loop;
static uv_mutex_t mutex;
static uv_cond_t cond;
static uv_async_t wake;
static int waiters; /* a plain int, as in the Lean runtime */

static void lock(void) {
  if (uv_mutex_trylock(&mutex) != 0) {
    waiters++;
    uv_async_send(&wake);
    uv_mutex_lock(&mutex);
    waiters--;
  }
}

static void unlock(void) {
  if (waiters == 0)
    uv_cond_signal(&cond);
  uv_mutex_unlock(&mutex);
}

static void run_loop(void* arg) {
  (void) arg;
  for (;;) {
    uv_mutex_lock(&mutex);
    while (waiters != 0)
      uv_cond_wait(&cond, &mutex);
    if (!uv_loop_alive(loop)) {
      uv_mutex_unlock(&mutex);
      break;
    }
    uv_run(loop, UV_RUN_ONCE);
    uv_mutex_unlock(&mutex);
  }
}

typedef struct {
  uv_tcp_t handle;
  uv_connect_t connect;
  uv_shutdown_t shutdown;
  volatile long connected; /* 0 pending, 1 done */
  int status;
} conn_t;

static void on_close(uv_handle_t* handle) {
  free(handle->data);
}

static void on_connect(uv_connect_t* req, int status) {
  conn_t* c = req->data;
  c->status = status;
  c->connected = 1;
}

static void on_shutdown(uv_shutdown_t* req, int status) {
  (void) req;
  (void) status;
}

static __attribute__((noinline)) void connect_once(const struct sockaddr_in* addr) {
  conn_t* c = calloc(1, sizeof(*c));
  if (c == NULL)
    abort();
  c->handle.data = c;
  c->connect.data = c;

  lock();
  uv_tcp_init(loop, &c->handle);
  int err = uv_tcp_connect(&c->connect, &c->handle, (const struct sockaddr*) addr, on_connect);
  unlock();
  if (err != 0) {
    lock();
    uv_close((uv_handle_t*) &c->handle, on_close);
    unlock();
    return;
  }

  for (int waited = 0; waited < 5000 && !c->connected; waited++)
    uv_sleep(1);

  lock();
  if (c->connected && c->status == 0)
    uv_shutdown(&c->shutdown, (uv_stream_t*) &c->handle, on_shutdown);
  uv_close((uv_handle_t*) &c->handle, on_close);
  unlock();
}

/* Call connect_once below a frame of `depth` extra stack bytes. */
static __attribute__((noinline)) void connect_at_depth(const struct sockaddr_in* addr,
                                                       size_t depth) {
  volatile char* pad = alloca(depth + 1);
  pad[0] = 1;
  pad[depth] = 1;
  connect_once(addr);
}

int main(int argc, char** argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: connect_repro PORT COUNT\n");
    return 2;
  }
  int port = atoi(argv[1]);
  int count = atoi(argv[2]);

  struct sockaddr_in addr;
  uv_ip4_addr("127.0.0.1", port, &addr);

  loop = uv_default_loop();
  uv_mutex_init_recursive(&mutex);
  uv_cond_init(&cond);
  uv_async_init(loop, &wake, NULL);

  uv_thread_t loop_thread;
  uv_thread_create(&loop_thread, run_loop, NULL);

  unsigned seed = 12345;
  for (int i = 0; i < count; i++) {
    seed = seed * 1103515245u + 12345u;
    connect_at_depth(&addr, (seed >> 16) % 2048);
  }

  lock();
  uv_close((uv_handle_t*) &wake, NULL);
  unlock();
  uv_thread_join(&loop_thread);
  return 0;
}
