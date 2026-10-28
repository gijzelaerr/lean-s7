"""Patch libuv's src/win/tcp.c so ConnectEx is not given a stack-local byte counter.

The connect path passes `&bytes` (a DWORD on the stack) together with an overlapped
structure. With no send buffer the count is meaningless, so the candidate fix passes
NULL instead. Exactly one call site must change.

usage: patch_connectex.py LIBUV_SOURCE_DIR
"""
import re
import sys
from pathlib import Path

path = Path(sys.argv[1]) / "src" / "win" / "tcp.c"
with open(path, encoding="utf-8", newline="") as source_file:
    source = source_file.read()
pattern = re.compile(r"(func_connectex\((?:[^;]*?),\s*)&bytes(,\s*&req->u\.io\.overlapped\);)", re.S)
patched, count = pattern.subn(r"\1NULL\2", source)
if count != 1:
    sys.exit(f"expected one ConnectEx call site, found {count}")
with open(path, "w", encoding="utf-8", newline="") as patched_file:
    patched_file.write(patched)
print(f"patched {path}")
