"""Keep JSON/session-fixture tooling off normal client import paths."""

from __future__ import annotations

import re
from pathlib import Path

ROOTS = ("LeanS7", "LeanS7.Client", "LeanS7.Assurance", "Main", "CliMain", "DecodeMain")
TOOLING = {
    "LeanS7.SessionConformance",
    "LeanS7.SessionAssurance",
    "LeanS7.SessionFuzz",
    "LeanS7.ManagementConformance",
    "LeanS7.S7Conformance",
    "LeanS7.OperationConformance",
    "LeanS7.ValueConformance",
    "LeanS7.ConversationConformance",
}


def check(graph: dict[str, list[str]], roots: tuple[str, ...] = ROOTS) -> None:
    def visit(name: str, path: tuple[str, ...], seen: set[str]) -> None:
        if name in ("CliMain", "DecodeMain") and path:
            raise ValueError(
                "library imports the command-line tool: " + " -> ".join((*path, name))
            )
        if (
            name in TOOLING
            or name == "Lean.Data.Json"
            or name.startswith("Lean.Data.Json.")
        ):
            raise ValueError(
                "client imports test/JSON tooling: " + " -> ".join((*path, name))
            )
        if name in seen:
            return
        seen.add(name)
        for dependency in graph.get(name, []):
            visit(dependency, (*path, name), seen)

    for root in roots:
        visit(root, (), set())


def run(root: Path) -> None:
    graph = {}
    sources = [
        root / "LeanS7.lean",
        root / "Main.lean",
        root / "CliMain.lean",
        *sorted((root / "LeanS7").glob("*.lean")),
    ]
    for source in sources:
        name = ".".join(source.relative_to(root).with_suffix("").parts)
        imports = []
        for line in source.read_text(encoding="utf-8").splitlines():
            match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_. ]+?)\s*(?:--.*)?", line)
            if match:
                imports.extend(match[1].split())
        graph[name] = imports
    check(graph)
    for changed in (
        {"LeanS7": ["Lean.Data.Json"]},
        {"Main": ["LeanS7.SessionFuzz"]},
        {"LeanS7.Assurance": ["Helper"], "Helper": ["Lean.Data.Json.Parser"]},
        {"LeanS7.Assurance": ["LeanS7.SessionAssurance"]},
        {"LeanS7": ["CliMain"], "CliMain": ["LeanS7"]},
        {"CliMain": ["LeanS7.SessionFuzz"]},
    ):
        try:
            check(changed)
        except ValueError:
            continue
        raise AssertionError("import-boundary guard accepted tooling regression")
    print("client import boundaries passed: six public/executable roots")


if __name__ == "__main__":
    run(Path(__file__).resolve().parents[1])
