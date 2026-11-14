"""Shared import parsing for the normalized project source format."""
import re

from check_proof_holes import source_without_comments


def imports(text):
    result = []
    for line in source_without_comments(text).splitlines():
        if not re.match(r"\s*(?:(?:public|private|meta)\s+)?import\b", line):
            continue
        match = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
        if match is None:
            raise ValueError(f"unsupported import syntax: {line}")
        names = match.group(1).split()
        if not names or not all(re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", n) for n in names):
            raise ValueError(f"unsupported module name: {line}")
        result.extend(names)
    return result
