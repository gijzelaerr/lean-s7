"""Small portability helpers for the integration harness."""

from __future__ import annotations

import select
import sys
import time
from typing import IO, Any

#: Exit status of a Windows fast-fail abort (``STATUS_STACK_BUFFER_OVERRUN``). On the
#: hosted Windows runner the lean-s7 executable sometimes dies with it while it
#: connects, in the Lean runtime's libuv (#58).
WINDOWS_FAST_FAIL = 0xC0000409


def exit_note(process: Any) -> str:
    """How the native client ended, for a peer error, or ``""`` if it has not failed.

    A peer whose connection is reset at the handshake usually means the client process
    died, and the peer's error alone hides how. ``process`` is a ``CompletedProcess``,
    a ``Popen`` or ``None``. The known Windows runtime crash is named as such.
    """
    returncode = getattr(process, "returncode", None)
    if not returncode:
        return ""
    known = ""
    if returncode & 0xFFFFFFFF == WINDOWS_FAST_FAIL:
        known = " (0xC0000409, the Windows runtime crash tracked in #58)"
    output = "\n".join(
        text.strip()
        for text in (getattr(process, "stdout", ""), getattr(process, "stderr", ""))
        if isinstance(text, str) and text.strip()
    )
    return f"; client exited {returncode}{known}" + (
        f": {output[-2048:]}" if output else ""
    )


def peer_error(error: BaseException, process: Any) -> BaseException:
    """``error`` from the scripted peer, with the client's exit attached if it failed."""
    note = exit_note(process)
    if not note:
        return error
    wrapped = RuntimeError(f"{error}{note}")
    wrapped.__cause__ = error
    return wrapped


def stdout_ready(stream: IO[Any], timeout: float) -> bool:
    """Whether ``stream`` (a subprocess pipe) has data or EOF to read within ``timeout``.

    ``select.select`` accepts only sockets on Windows, so a pipe is polled there with
    ``PeekNamedPipe``. A closed or broken pipe counts as ready so the caller's read
    returns EOF instead of waiting for the full timeout.
    """
    if sys.platform != "win32":
        return bool(select.select([stream], [], [], timeout)[0])

    import ctypes
    import msvcrt
    from ctypes import wintypes

    handle = wintypes.HANDLE(msvcrt.get_osfhandle(stream.fileno()))
    available = wintypes.DWORD(0)
    deadline = time.monotonic() + timeout
    while True:
        ok = ctypes.windll.kernel32.PeekNamedPipe(  # type: ignore[attr-defined]
            handle, None, 0, None, ctypes.byref(available), None
        )
        if not ok or available.value > 0:
            return True
        if time.monotonic() >= deadline:
            return False
        time.sleep(0.005)
