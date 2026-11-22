#!/usr/bin/env python3
"""Check the approved statement of Theorem 1.2 and scan its Lean sources."""

import hashlib
import json
from pathlib import Path

from check_proof_holes import check

ROOT = Path(__file__).resolve().parents[1]
EXPORT = "Swarming.swarm_diameter"


def main():
    manifest = json.loads((ROOT / "docs/diameter-statement.json").read_text(encoding="utf-8"))
    if manifest["export"] != EXPORT or manifest["path"] != "SwarmDiameter/Main.lean":
        raise SystemExit("Unexpected diameter export")
    path = ROOT / manifest["path"]
    data = path.read_bytes()
    marker = f"\ntheorem {EXPORT} ".encode()
    if path.is_symlink() or data.count(marker) != 1:
        raise SystemExit("Expected one diameter declaration in a regular source file")
    start = data.index(marker) + 1
    end = data.index(b" := by\n", start)
    if hashlib.sha256(data[start:end]).hexdigest() != manifest["statement_sha256"]:
        raise SystemExit("The diameter statement differs from the approved signature")
    files = [ROOT / "SwarmDiameter.lean", *sorted((ROOT / "SwarmDiameter").rglob("*.lean"))]
    if sum(check(file) for file in files):
        raise SystemExit("Unexpected proof hole or compiler-trust bypass")
    print(f"DIAMETER STATEMENT OK: {EXPORT}")
    print(f"DIAMETER SOURCES OK: {len(files)} files")


if __name__ == "__main__":
    main()
