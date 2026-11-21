import SwarmDiameter.RenewalProcess
import SwarmDiameter.FirstInterval
import SwarmDiameter.RegenerationBlocks
import Lean

open Lean Elab Command

#print axioms Swarming.ArithmeticRenewal.renewalReward_tendsto_mean
#print axioms Swarming.CycleOccupation.occupationLaw_real_apply
#print axioms Swarming.CycleOccupation.observation_prob_eq_renewalReward
#print axioms Swarming.CycleOccupation.tendstoInDistribution_occupationLaw
#print axioms KacFormula.iIndepFun_of_fresh
#print axioms Swarming.ArithmeticRenewal.eq_renewalReward_of_first_interval
#print axioms Swarming.CycleOccupation.observation_prob_tendsto_of_delay

/-- Check the transitive axiom dependencies in the renewal and regeneration modules. -/
elab "#audit_diameter_support_axioms" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let project := modules.filter fun name => name.getRoot == `Swarm || name.getRoot == `SwarmDiameter
  let expected := #[
    `Swarm.Imports, `Swarm.KacDisjoint, `Swarm.RegenIid,
    `SwarmDiameter.ArithmeticRenewal, `SwarmDiameter.CycleOccupation,
    `SwarmDiameter.RenewalProcess, `SwarmDiameter.RegenerationBlocks,
    `SwarmDiameter.DelayedRenewal, `SwarmDiameter.FirstInterval]
  unless project.size == expected.size && project.all (fun name => expected.contains name) do
    throwError "Unexpected project imports {project}"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if project.contains modules[idx.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        let unexpected := axioms.filter fun ax =>
          ax != `propext && ax != `Classical.choice && ax != `Quot.sound
        unless unexpected.isEmpty do
          throwError "{name}: unexpected axioms {unexpected}"
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"DIAMETER SUPPORT AXIOMS OK: {checked} declarations"

#audit_diameter_support_axioms
