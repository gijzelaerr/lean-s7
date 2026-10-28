"""Apply libuv commit aabb7651d ("win: properly initialize OSVERSIONINFOW", #5107,
fixing libuv/libuv#5106) to a libuv source tree that predates it.

uv__windows10_version1709() calls RtlGetVersion() with an uninitialised
dwOSVersionInfoSize, so the call can write past the OSVERSIONINFOW on the stack.
uv__tcp_connect calls it for every loopback connect. The fix is two lines.

usage: patch_osversion.py LIBUV_SOURCE_DIR
"""
import sys
from pathlib import Path

path = Path(sys.argv[1]) / "src" / "win" / "tcp.c"
with open(path, encoding="utf-8", newline="") as source_file:
    source = source_file.read()
newline = "\r\n" if "\r\n" in source else "\n"
before = ("  if (!pRtlGetVersion)" + newline + "    return 0;" + newline +
          "  pRtlGetVersion(&os_info);")
after = ("  if (!pRtlGetVersion)" + newline + "    return 0;" + newline +
         "  os_info.dwOSVersionInfoSize = sizeof(os_info);" + newline +
         "  os_info.szCSDVersion[0] = L'\\0';" + newline +
         "  pRtlGetVersion(&os_info);")
if source.count(before) != 1:
    sys.exit(f"expected one RtlGetVersion call site, found {source.count(before)}")
with open(path, "w", encoding="utf-8", newline="") as patched_file:
    patched_file.write(source.replace(before, after))
print(f"patched {path}")
