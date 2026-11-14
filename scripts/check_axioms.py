#!/usr/bin/env python3
"""Reject nonstandard axiom reports and missing audit coverage."""
import re
import sys

# `choice` is Lean's displayed alias for `Classical.choice` under `open Classical`.
allowed = {"propext", "Classical.choice", "choice", "Quot.sound"}
DEPENDS = re.compile(r"'([^']*)' depends on axioms: \[(.*?)\]", re.S)
EMPTY = re.compile(r"'([^']*)' does not depend on any axioms")


def parse(log):
    """Return [(name, {axiom, ...})] in log order, both print shapes."""
    reports = [(m.start(), m.group(1),
                {n.strip() for n in m.group(2).replace("\n", " ").split(",") if n.strip()})
               for m in DEPENDS.finditer(log)]
    reports += [(m.start(), m.group(1), set()) for m in EMPTY.finditer(log)]
    return [(name, axioms) for _, name, axioms in sorted(reports)]


def main(argv):
    expect = None
    if "--expect" in argv:
        i = argv.index("--expect")
        try:
            expect = int(argv[i + 1])
        except (IndexError, ValueError):
            print("usage: check_axioms.py LOG [--expect N]", file=sys.stderr)
            return 2
        argv = argv[:i] + argv[i + 2:]
    if not argv:
        print("usage: check_axioms.py LOG [--expect N]", file=sys.stderr)
        return 2
    status = 0
    for path in argv:
        with open(path, encoding="utf-8") as handle:
            reports = parse(handle.read())
        bad = [(name, sorted(axioms)) for name, axioms in reports if not axioms <= allowed]
        empty = [name for name, axioms in reports if not axioms]
        print(f"AXIOM AUDIT: {len(reports)} declarations, {len(empty)} empty closure, "
              f"{len(bad)} nonstandard")
        if not reports:
            print(f"AXIOM AUDIT FAILED: no '#print axioms' report in {path}; "
                  "nothing was audited")
            status = 1
        if bad:
            print("NONSTANDARD AXIOMS:", bad)
            status = 1
        if expect is not None and len(reports) != expect:
            print(f"AXIOM AUDIT FAILED: expected {expect} declarations, found {len(reports)}")
            status = 1
        if status == 0:
            names = ", ".join(name for name, _ in reports)
            print(f"AXIOM AUDIT OK: {len(reports)} declarations, all only "
                  f"propext / Classical.choice / Quot.sound")
            print(f"  audited: {names}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
