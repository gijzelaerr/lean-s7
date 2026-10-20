"""Accept TCP connections on 127.0.0.1 and close them immediately; prints the port."""
import socket, struct, sys
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", 0)); s.listen(128)
print(s.getsockname()[1], flush=True)
while True:
    c, _ = s.accept()
    if len(sys.argv) > 1 and sys.argv[1] == "rst":
        c.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    c.close()
