#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  Swarm/Imports
  Swarm/KacDisjoint
  Swarm/RegenIid
  Swarm/Reflect/Basic
  Swarm/Reflect/Main
  Swarm/Reflect/Law
  Swarm/Reflect/Choose
  SwarmDiameter/ArithmeticRenewal
  SwarmDiameter/CycleOccupation
  SwarmDiameter/DelayedRenewal
  SwarmDiameter/FirstInterval
  SwarmDiameter/FirstIntervalOccupation
  SwarmDiameter/TailBounds
  SwarmDiameter/BinomialEndpoint
  SwarmDiameter/ReflectionExcursion
  SwarmDiameter/RenewalProcess
  SwarmDiameter/RegenerationBlocks
)
python3 scripts/check_proof_holes.py "${modules[@]/%/.lean}" audit/DiameterSupport.lean

work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT
mkdir -p "$work/Swarm/Reflect" "$work/SwarmDiameter"
export LEAN_PATH="$work:$(lake env printenv LEAN_PATH)"
for mod in "${modules[@]}"; do
    lean -j1 -o "$work/$mod.olean" "$mod.lean"
done
lean -j1 -t0 audit/DiameterSupport.lean
