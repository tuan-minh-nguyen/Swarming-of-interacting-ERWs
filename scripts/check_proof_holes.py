#!/usr/bin/env python3
"""Scan Lean sources for proof holes, custom axioms, and compiler-trust bypasses.

This lexical check supplements compilation and the project-wide axiom audit;
it is not a substitute for either check."""
from pathlib import Path
import re
import sys

# `axiom` is a Lean keyword and `sorryAx` a core constant, never identifiers, so
# a bare-word test catches them where a declaration-start test does not.
DECL = re.compile(r"\b(?:sorry|admit|sorryAx)\b|\baxiom\b")
HOLE = re.compile(r"\bnative_decide\b|\bLean\.(?:ofReduceBool|trustCompiler)\b")


def source_without_comments(text: str) -> str:
    """Blank comments while retaining literals and interpolation expressions.

    Literal contents remain visible to the token scan. Comment delimiters
    inside ordinary strings, raw strings, characters, and quoted identifiers
    never start comments. Nested interpolation expressions are scanned as code.
    """
    out = list(text)
    i = 0
    n = len(text)
    depth = 0
    # Code frames store an optional interpolation-brace depth. String frames
    # store whether braces introduce interpolated code.
    stack = [["code", None]]

    def blank(start, end):
        for pos in range(start, end):
            if text[pos] != "\n":
                out[pos] = " "

    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1
                blank(i, i + 2)
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                blank(i, i + 2)
                i += 2
            else:
                blank(i, i + 1)
                i += 1
            continue
        mode, detail = stack[-1]
        if mode == "raw":
            if text.startswith(detail, i):
                i += len(detail)
                stack.pop()
            else:
                i += 1
            continue
        if mode == "quoted":
            if text[i] == "»":
                stack.pop()
            i += 1
            continue
        if mode == "string":
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                stack.pop()
                i += 1
            elif detail and text.startswith("{{", i):
                i += 2
            elif detail and text.startswith("}}", i):
                i += 2
            elif detail and text[i] == "{":
                stack.append(["code", 1])
                i += 1
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            blank(i, i + 2)
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = n
            blank(i, end)
            i = end
        elif text[i] == "«":
            stack.append(["quoted", None])
            i += 1
        elif text[i] == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            raw = re.match(r'r(\#*)"', text[i:])
            if raw:
                stack.append(["raw", '"' + raw.group(1)])
                i += len(raw.group(0))
            else:
                i += 1
        elif text[i] == '"':
            interpolated = bool(re.search(r"[\w]+!\s*$", text[:i]))
            stack.append(["string", interpolated])
            i += 1
        elif text[i] == "'":
            char = re.match(r"'(?:\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^'\\\n])'", text[i:])
            i += len(char.group(0)) if char else 1
        elif detail is not None and text[i] in "{}":
            stack[-1][1] += 1 if text[i] == "{" else -1
            if stack[-1][1] == 0:
                stack.pop()
            i += 1
        else:
            i += 1
    if depth or len(stack) != 1:
        raise ValueError("unterminated Lean comment, literal, or interpolation")
    return "".join(out)


def check(path: Path) -> int:
    """Print one line per finding for `path`; return the number of findings."""
    raw = path.read_text(encoding="utf-8")
    text = source_without_comments(raw)
    if len(text) != len(raw):  # invariant: positions are exact
        print(f"{path}: internal error: comment stripper changed the length")
        return 1
    original_lines = raw.splitlines()
    found = 0
    seen = set()
    for pattern in (DECL, HOLE):
        for match in pattern.finditer(text):
            if match.start() in seen:
                continue
            seen.add(match.start())
            found += 1
            lineno = text.count("\n", 0, match.start()) + 1
            print(f"{path}:{lineno}:{match.group(0)}: {original_lines[lineno - 1]}")
    return found


def main(argv):
    if not argv:
        print("ERROR: no Lean source files supplied", file=sys.stderr)
        return 2
    failed = False
    for argument in argv:
        if check(Path(argument)):
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
