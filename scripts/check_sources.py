#!/usr/bin/env python3
"""Check the source inventory, dependency closure, and unchanged proof text."""
import hashlib
import json
from pathlib import Path
import re
import sys

from check_proof_holes import check, source_without_comments
from lean_sources import imports

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(str(message))


def proof_text(text):
    text = source_without_comments(text)
    text = re.sub(r"(?m)^\s*(?:import\s+[^\n]+|#(?:print|check)\s+[^\n]+)$", "", text)
    return " ".join(text.split())


def main():
    rows = json.loads((ROOT / "docs/source-map.json").read_text())
    sources = {row["module"]: ROOT / row["path"] for row in rows}
    require(len(rows) == len(sources) == 673, "incorrect source inventory")
    require(sum(row["original"] is not None for row in rows) == 672, "incorrect original inventory")
    require(set(sources.values()) == set((ROOT / "Swarm").rglob("*.lean")), "unlisted source file")
    facade = (ROOT / "Swarm.lean").read_text()
    require(imports(facade) == ["Swarm.BlkMeasure"] and proof_text(facade) == "",
            "the library facade must contain only its main import")
    dependencies = {}
    for row in rows:
        path = ROOT / row["path"]
        require(not path.is_symlink(), path)
        require(path.resolve().is_relative_to((ROOT / "Swarm").resolve()), path)
        require(path == ROOT / Path(*row["module"].split(".")).with_suffix(".lean"), path)
        text = path.read_text()
        digest = hashlib.sha256(proof_text(text).encode()).hexdigest()
        require(digest == row["proof_sha256"], f"proof text changed: {path}")
        require(check(path) == 0, f"proof-hole finding: {path}")
        deps = imports(text)
        require(all(d in sources or d.startswith("Mathlib.") for d in deps), path)
        dependencies[row["module"]] = [d for d in deps if d in sources]
    visited = set()
    active = set()

    def visit(module):
        require(module not in active, f"import cycle: {module}")
        if module in visited:
            return
        active.add(module)
        for dep in dependencies[module]:
            visit(dep)
        active.remove(module)
        visited.add(module)

    visit("Swarm.BlkMeasure")
    require(visited == set(sources), "sources outside the main proof closure")
    for path in (ROOT / "audit").glob("*.lean"):
        require(check(path) == 0, path)
    print(f"SOURCES OK: {len(sources)} modules; complete closure; proof text unchanged")
    return 0


if __name__ == "__main__":
    sys.exit(main())
