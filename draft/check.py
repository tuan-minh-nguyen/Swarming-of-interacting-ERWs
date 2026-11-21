#!/usr/bin/env python3
"""Verify the approved diameter declaration and its isolation."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_proof_holes import check  # noqa: E402
from lean_sources import imports  # noqa: E402


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    entries = json.loads((ROOT / "draft/anchors.json").read_text(encoding="utf-8"))
    require(len(entries) == 1, "Expected one registered diameter draft")
    entry = entries[0]
    anchor = ROOT / "draft/DiameterAnchor.lean"
    provider = ROOT / "draft/DiameterProof.lean"
    require(entry["path"] == anchor.relative_to(ROOT).as_posix(), "Unexpected declaration path")
    require(entry["provider"]["path"] == provider.relative_to(ROOT).as_posix(), "Unexpected provider path")
    require(entry["export"] == "Swarming.swarm_diameter", "Unexpected declaration export")
    require(entry["state"] == "DRAFT_SORRY", "Expected draft state")
    require(entry["allowed_body"] == "by\n  sorry", "Unexpected draft body")
    require(not anchor.is_symlink(), "The draft declaration must be a regular file")
    data = anchor.read_bytes()
    suffix = (" := " + entry["allowed_body"] + "\n").encode("utf-8")
    require(data.endswith(suffix), "Draft proof differs from the registered body")
    require(sha256(data[:-len(suffix)]) == entry["declaration_sha256"], "Draft statement differs from the approved type")
    require(sha256(data) == entry["file_sha256"], "Draft file differs from the registered contents")

    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean"],
        cwd=ROOT,
    ).decode("utf-8").split("\0")
    restricted = {"DiameterAnchor", "DiameterProof", entry["module"], entry["provider"]["module"]}
    for relative in sorted(set(paths) - {""}):
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), f"Invalid Lean source {relative}")
        if path != anchor:
            require(check(path) == 0, f"Unexpected proof hole in {relative}")
        for dependency in imports(path.read_text(encoding="utf-8")):
            allowed_provider = path == anchor and dependency == entry["provider"]["module"]
            require(
                allowed_provider or (dependency not in restricted and not dependency.startswith("draft.")),
                f"{relative} imports the quarantined module {dependency}",
            )

    print("DRAFT_ANCHORS: 1 draft/DiameterAnchor.lean")
    print("UNREGISTERED_SORRIES: 0")
    print("DRAFT_IMPORT_VIOLATIONS: 0")
    print("SEALED_THIS_TURN: 0")


if __name__ == "__main__":
    main()
