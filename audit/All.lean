import Swarm.BlkMeasure
import Lean

open Lean Elab Command

/-- Check the transitive axiom dependencies of every imported project declaration. -/
elab "#audit_project_axioms" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let projectModules := modules.filter fun name => name.getRoot == `Swarm
  unless projectModules.size == 673 do
    throwError "Expected 673 project modules, imported {projectModules.size}"
  let mut checked : Nat := 0
  let mut failures : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules[idx.toNat]!.getRoot == `Swarm then
        checked := checked + 1
        let axioms ← collectAxioms name
        let unexpected := axioms.filter fun ax =>
          ax != `propext && ax != `Classical.choice && ax != `Quot.sound
        unless unexpected.isEmpty do
          failures := failures + 1
          logError m!"{name}: unexpected axioms {unexpected}"
  if checked == 0 then
    throwError "No project declarations were audited"
  unless failures == 0 do
    throwError "Axiom audit failed for {failures} declarations"
  logInfo m!"PROJECT AXIOMS OK: {checked} declarations"

#audit_project_axioms
