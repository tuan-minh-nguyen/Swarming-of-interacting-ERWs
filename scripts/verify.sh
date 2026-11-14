#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m unittest discover -s tests
WORK=".scratch/verify-$(date -u +%Y%m%dT%H%M%S)-$$"
python3 scripts/build.py --work "$WORK" --jobs "${SWARM_BUILD_JOBS:-1}"
export LEAN_PATH="$(cat "$WORK/lean-path.txt")"
mkdir -p .scratch/audit
# These runs use fresh importer modules; the second also rechecks imported
# proofs with Lean's trust level set to zero.
if ! lean -j1 -M 8000 audit/Main.lean > .scratch/audit/main.log 2>&1; then
  cat .scratch/audit/main.log
  exit 1
fi
python3 scripts/check_axioms.py .scratch/audit/main.log --expect 10
python3 - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'scripts')
from check_axioms import parse
expected = ['M4Blk.' + n for n in [
    'blkEps', 'blkEps_tendsto', 'blkEps_spec', 'badBlk_ae_subset',
    'paperBadBlockProfile', 'main_claim', 'dT_tight', 'main_claim_direct']]
expected += ['main_claim_is_paper_target', 'main_claim_direct_is_paper_target']
actual = [name for name, _ in parse(Path('.scratch/audit/main.log').read_text())]
if actual != expected:
    raise SystemExit(f'Unexpected axiom reports: {actual}; expected {expected}')
print('STATEMENTS OK: both exact consumer types and all ten named axiom reports')
PY
if ! lean -j1 -t0 -M 8000 audit/All.lean > .scratch/audit/all.log 2>&1; then
  cat .scratch/audit/all.log
  exit 1
fi
cat .scratch/audit/all.log
grep -Eq '^PROJECT AXIOMS OK: [1-9][0-9]* declarations$' .scratch/audit/all.log
echo 'VERIFIED: source checks, full build, exact main statements, and project-wide axiom audit'
