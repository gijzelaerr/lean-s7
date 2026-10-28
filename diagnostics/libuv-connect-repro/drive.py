"""Run a connect reproducer repeatedly under ProcDump and count crashes.

Starts diagnostics/connect-repro/listener.py in `rst` mode, then runs the
reproducer (`EXE PORT COUNT`) in parallel processes for a fixed time. Unlike the
earlier diagnostic it does not stop at the first crash: it reports how many
processes crashed out of how many ran, so arms can be compared. At most five
dumps are kept.

usage: drive.py ARM EXE DUMP_DIR PROCDUMP [MINUTES]
"""
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

CRASH = 3221226505  # 0xC0000409
CONNECTS_PER_PROCESS = 200
PARALLEL = 8
KEEP_DUMPS = 5

arm, exe, dump_dir, procdump = sys.argv[1:5]
minutes = float(sys.argv[5]) if len(sys.argv) > 5 else 15.0
dumps = Path(dump_dir)
dumps.mkdir(parents=True, exist_ok=True)

listener = subprocess.Popen(
    [sys.executable, "-I", "diagnostics/connect-repro/listener.py", "rst"],
    stdout=subprocess.PIPE, text=True)
port = listener.stdout.readline().strip()


def one(index: int) -> int:
    """Run one reproducer process; return 1 if it crashed."""
    target = dumps / f"run-{index}"
    target.mkdir()
    result = subprocess.run(
        [procdump, "-accepteula", "-ma", "-e", "1", "-x", str(target),
         exe, port, str(CONNECTS_PER_PROCESS)],
        timeout=600, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    crashed = any(target.glob("*.dmp")) or result.returncode == CRASH
    if not crashed:
        target.rmdir()
    return 1 if crashed else 0


start = time.time()
processes = 0
crashes = 0
with ThreadPoolExecutor(PARALLEL) as pool:
    while time.time() - start < minutes * 60:
        batch = range(processes, processes + PARALLEL * 2)
        crashes += sum(pool.map(one, batch))
        processes += len(batch)

listener.kill()

# Keep the first few crash directories with their dumps; drop the rest.
crash_dirs = sorted(p for p in dumps.iterdir() if p.is_dir())
for extra in crash_dirs[KEEP_DUMPS:]:
    for item in extra.iterdir():
        item.unlink()
    extra.rmdir()

summary = {
    "arm": arm,
    "processes": processes,
    "connects": processes * CONNECTS_PER_PROCESS,
    "crashed_processes": crashes,
    "minutes": round((time.time() - start) / 60, 1),
}
print(json.dumps(summary))
(dumps / "summary.json").write_text(json.dumps(summary))
step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
if step_summary:
    with open(step_summary, "a", encoding="utf-8") as out:
        out.write("| arm | processes | connects | crashed processes |\n| --- | --- | --- | --- |\n")
        out.write(f"| {arm} | {processes} | {processes * CONNECTS_PER_PROCESS} | {crashes} |\n")
