"""Small portability helpers for the integration harness."""

from __future__ import annotations

import select
import sys
import time
from typing import IO, Any


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
