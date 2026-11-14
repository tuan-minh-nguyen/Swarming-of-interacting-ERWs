#!/usr/bin/env python3
"""Build only project sources in a fresh directory with bounded concurrency.

Dependencies must already have their cached compiled artifacts. No dependency
source or build artifact is modified. Each module receives a separate log and
GNU time record; summary.json records the source hashes and measured timings.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from check_proof_holes import source_without_comments
from lean_sources import imports as parse_imports

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--memory", type=int, default=8000, help="Lean memory threshold in MiB per process")
    parser.add_argument("--resume", action="store_true", help="resume a development build after validating cached artifacts")
    args = parser.parse_args()
    if args.jobs < 1 or args.memory < 1:
        parser.error("--jobs and --memory must be positive")
    timer = shutil.which("gtime") or shutil.which("time")
    if timer is None:
        parser.error("GNU time is required (install the time package)")
    work = args.work.resolve()
    if not work.is_relative_to(ROOT / ".scratch") or work == ROOT / ".scratch":
        parser.error("--work must be a new directory inside this repository's .scratch")
    if work.exists() and not args.resume:
        parser.error("--work already exists; choose a fresh directory")
    if args.resume and not (work / "summary.json").is_file():
        parser.error("--resume requires an existing summary.json")
    subprocess.run([sys.executable, str(ROOT / "scripts/check_sources.py")], check=True, cwd=ROOT)
    rows = json.loads((ROOT / "docs/source-map.json").read_text())
    sources = {row["module"]: ROOT / row["path"] for row in rows}
    sources["Swarm"] = ROOT / "Swarm.lean"
    imports = {m: parse_imports(p.read_text()) for m, p in sources.items()}
    env = dict(os.environ)
    # Obtain declared dependency paths from Lake, then exclude project artifacts
    # and any caller-supplied search paths. The new output tree is the only
    # provider of project modules.
    clean = dict(env)
    clean.pop("LEAN_PATH", None)
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, env=clean, text=True).strip()
    dependency_paths = [Path(p).resolve() for p in lean_path.split(os.pathsep) if p]
    project_build = (ROOT / ".lake/build").resolve()
    dependency_paths = [p for p in dependency_paths if not p.is_relative_to(project_build)]
    for deps in imports.values():
        for dep in deps:
            if dep in sources:
                continue
            rel = Path(*dep.split(".")).with_suffix(".olean")
            if not any((p / rel).is_file() for p in dependency_paths):
                parser.error(f"missing cached dependency: {dep}; restore the dependency cache first")
    work.mkdir(parents=True, exist_ok=args.resume)
    (work / "lib").mkdir(exist_ok=args.resume)
    (work / "logs").mkdir(exist_ok=args.resume)
    env["LEAN_PATH"] = os.pathsep.join([str(work / "lib"), *map(str, dependency_paths)])
    (work / "lean-path.txt").write_text(env["LEAN_PATH"] + "\n")
    hashes = {m: hashlib.sha256(p.read_bytes()).hexdigest() for m, p in sources.items()}
    setup = {"lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
             "manifest": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
             "config": hashlib.sha256((ROOT / "lakefile.lean").read_bytes()).hexdigest()}
    started = time.monotonic()

    def build(module):
        path = sources[module]
        out = work / "lib" / Path(*module.split(".")).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        log = work / "logs" / f"{module}.log"
        stats = work / "logs" / f"{module}.time"
        command = [timer, "-v", "-o", str(stats), "lean", "-j1", "-M", str(args.memory),
                   "-R", str(ROOT), "-o", str(out), str(path)]
        with log.open("w") as output:
            proc = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
        if proc.returncode == 0 and not out.is_file():
            raise RuntimeError(f"Lean returned success without an output file: {module}")
        elapsed = time.monotonic() - start
        if hashlib.sha256(path.read_bytes()).hexdigest() != hashes[module]:
            raise RuntimeError(f"source changed while building: {module}")
        return {"module": module, "seconds": elapsed, "returncode": proc.returncode,
                "source_sha256": hashes[module], "command": command,
                "artifact_sha256": hashlib.sha256(out.read_bytes()).hexdigest() if out.is_file() else None,
                "log": str(log.relative_to(work)), "time": str(stats.relative_to(work))}

    pending = set(sources)
    completed = set()
    results = []
    if args.resume:
        previous = json.loads((work / "summary.json").read_text())
        candidates = {}
        if previous.get("setup") == setup:
            for result in previous["results"]:
                module = result["module"]
                out = work / "lib" / Path(*module.split(".")).with_suffix(".olean")
                if (module in hashes and result["returncode"] == 0
                        and result["source_sha256"] == hashes[module] and out.is_file()
                        and result.get("artifact_sha256") == hashlib.sha256(out.read_bytes()).hexdigest()):
                    candidates[module] = result
        while True:
            ready = [m for m in candidates if all(d not in sources or d in completed for d in imports[m])]
            if not ready:
                break
            for module in ready:
                result = dict(candidates.pop(module))
                result["cached"] = True
                results.append(result)
                completed.add(module)
                pending.remove(module)
        print(f"RESUME: {len(completed)} artifacts validated against source, imports, and setup", flush=True)
    running = {}
    failed = False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = sorted(m for m in pending
                           if all(d not in sources or d in completed for d in imports[m]))
            for module in ready[:args.jobs - len(running)]:
                pending.remove(module)
                running[pool.submit(build, module)] = module
            if not running:
                if pending and not failed:
                    raise RuntimeError(f"cyclic or unresolved project imports: {sorted(pending)}")
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                result = future.result()
                results.append(result)
                if result["returncode"] == 0:
                    completed.add(module)
                    print(f"BUILT {len(completed)}/{len(sources)} {module} {result['seconds']:.3f}s", flush=True)
                else:
                    failed = True
                    print(f"FAILED {module}: see {work / result['log']}", flush=True)
    summary = {"jobs": args.jobs, "setup": setup, "resumed": args.resume, "wall_seconds": time.monotonic() - started,
               "completed": len(completed), "expected": len(sources), "results": results}
    changed = [m for m, p in sources.items()
               if hashlib.sha256(p.read_bytes()).hexdigest() != hashes[m]]
    if changed:
        summary["changed_sources"] = changed
        failed = True
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    if failed or completed != set(sources):
        return 1
    print(f"BUILD OK: {len(completed)} project modules; no dependency compilation", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
