"""Verify and package the versioned conformance corpus.

Standard library only; nothing here is imported by the Lean client.

    python integration/corpus_package.py --check            # CI: manifest matches files
    python integration/corpus_package.py --write            # regenerate MANIFEST.json
    python integration/corpus_package.py --verify-package   # CI: archive is reproducible
    python integration/corpus_package.py --package dist [--revision SHA]

Checksums are computed over the file bytes with CRLF normalized to LF so that
the manifest is identical on checkouts with and without `core.autocrlf`.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "conformance" / "v1"
MANIFEST = CORPUS / "MANIFEST.json"
DOCS = ("README.md", "VERSIONING.md")

# File name -> argument to `lake exe lean-s7-conformance` (empty for TPKT).
GENERATORS = {
    "tpkt.json": "",
    "cotp-data.json": "cotp",
    "s7.json": "s7",
    "operations.json": "operations",
    "values.json": "values",
    "conversations.json": "conversations",
    "sessions.json": "sessions",
    "management.json": "management",
}

# Bump per VERSIONING.md. Hashes below must match whenever this changes.
CORPUS_VERSION = "1.0.0"


class CorpusError(Exception):
    pass


def normalized(path: Path) -> bytes:
    return path.read_bytes().replace(b"\r\n", b"\n")


def lean_s7_version() -> str:
    match = re.search(
        r'^version\s*=\s*"([^"]+)"',
        (ROOT / "lakefile.toml").read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    if not match:
        raise CorpusError("lakefile.toml has no version")
    return match.group(1)


def toolchain() -> str:
    return (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()


def describe(name: str) -> dict[str, object]:
    data = normalized(CORPUS / name)
    document = json.loads(data)
    if document.get("schema_version") != 1:
        raise CorpusError(f"{name}: schema_version must be 1 in corpus v1")
    generator = "lake exe lean-s7-conformance"
    if GENERATORS[name]:
        generator += " " + GENERATORS[name]
    return {
        "name": name,
        "protocol": document["protocol"],
        "schema_version": document["schema_version"],
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "generator": generator,
    }


def build_manifest() -> dict[str, object]:
    present = sorted(
        path.name for path in CORPUS.glob("*.json") if path.name != "MANIFEST.json"
    )
    if present != sorted(GENERATORS):
        raise CorpusError(f"corpus files {present} do not match the generator table")
    return {
        "manifest_version": 1,
        "corpus": "lean-s7-conformance",
        "corpus_version": CORPUS_VERSION,
        "lean_s7_version": lean_s7_version(),
        "lean_toolchain": toolchain(),
        "files": [describe(name) for name in sorted(GENERATORS)],
    }


def render(manifest: dict[str, object]) -> bytes:
    return (json.dumps(manifest, indent=2) + "\n").encode()


def check() -> None:
    if not MANIFEST.exists():
        raise CorpusError("MANIFEST.json is missing; run with --write")
    expected = render(build_manifest())
    if MANIFEST.read_bytes().replace(b"\r\n", b"\n") != expected:
        raise CorpusError(
            "MANIFEST.json is stale: corpus files, lean-s7 version or toolchain "
            "changed. Review VERSIONING.md, bump CORPUS_VERSION if required, "
            "then run with --write."
        )
    print(f"corpus manifest ok: {len(GENERATORS)} files, corpus {CORPUS_VERSION}")


def git_revision() -> str:
    dirty = subprocess.run(
        [
            "git",
            "status",
            "--porcelain",
            "--",
            "conformance",
            "lakefile.toml",
            "lean-toolchain",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    if dirty:
        raise CorpusError(
            "corpus inputs have uncommitted changes; commit before packaging"
        )
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def archive_bytes(revision: str) -> tuple[str, bytes]:
    check()
    manifest = build_manifest()
    prefix = f"lean-s7-conformance-v1-{CORPUS_VERSION}"
    provenance = {
        "corpus_version": CORPUS_VERSION,
        "lean_s7_version": manifest["lean_s7_version"],
        "lean_toolchain": manifest["lean_toolchain"],
        "git_revision": revision,
    }
    members: dict[str, bytes] = {
        "MANIFEST.json": render(manifest),
        "PROVENANCE.json": (json.dumps(provenance, indent=2) + "\n").encode(),
    }
    for name in sorted(GENERATORS):
        members[name] = normalized(CORPUS / name)
    for name in DOCS:
        members[name] = normalized(CORPUS / name)

    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w", format=tarfile.PAX_FORMAT) as archive:
        for name in sorted(members):
            info = tarfile.TarInfo(f"{prefix}/{name}")
            info.size = len(members[name])
            info.mtime = 0
            info.mode = 0o644
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            archive.addfile(info, io.BytesIO(members[name]))
    compressed = io.BytesIO()
    with gzip.GzipFile(fileobj=compressed, mode="wb", mtime=0, filename="") as handle:
        handle.write(raw.getvalue())
    return prefix + ".tar.gz", compressed.getvalue()


def package(out: Path, revision: str) -> None:
    name, data = archive_bytes(revision)
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(data)
    digest = hashlib.sha256(data).hexdigest()
    (out / (name + ".sha256")).write_text(f"{digest}  {name}\n")
    print(f"wrote {out / name} ({len(data)} bytes, sha256 {digest})")


def verify_package() -> None:
    revision = "0" * 40
    first = archive_bytes(revision)
    second = archive_bytes(revision)
    if first != second:
        raise CorpusError("corpus archive is not reproducible")
    with tarfile.open(fileobj=io.BytesIO(first[1]), mode="r:gz") as archive:
        names = sorted(member.name.split("/", 1)[1] for member in archive.getmembers())
        for member in archive.getmembers():
            if member.name.startswith("/") or ".." in member.name.split("/"):
                raise CorpusError(f"unsafe archive member {member.name}")
    expected = sorted(
        ["MANIFEST.json", "PROVENANCE.json", *GENERATORS, *DOCS],
    )
    if names != expected:
        raise CorpusError(f"archive members {names} differ from {expected}")
    print(f"corpus archive reproducible: {first[0]}, {len(first[1])} bytes")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    group.add_argument("--verify-package", action="store_true")
    group.add_argument("--package", metavar="DIR")
    parser.add_argument("--revision", help="git revision recorded in PROVENANCE.json")
    args = parser.parse_args()
    try:
        if args.check:
            check()
        elif args.write:
            MANIFEST.write_bytes(render(build_manifest()))
            print(f"wrote {MANIFEST}")
        elif args.verify_package:
            verify_package()
        else:
            package(Path(args.package), args.revision or git_revision())
    except CorpusError as error:
        print(f"corpus: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
