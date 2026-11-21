import SwarmDiameter.SwarmLowerBounds
import Lean

open Lean Elab Command

#print axioms Swarming.Diameter.exists_diameter_occupationLaw
#print axioms Swarming.Diameter.linear_trial_at_stopping_time_mass_ge
#print axioms Swarming.Diameter.two_walker_trial_at_stopping_time_mass_ge
#print axioms Swarming.Diameter.exists_positive_simultaneousRecordDensity
#print axioms Swarming.Diameter.exists_leading_walk_trial_mass_ge
#print axioms Swarming.Diameter.exists_cubic_trial_mass_ge
#print axioms Swarming.Diameter.exists_diameter_lower_bounds

elab "#audit_swarm_renewal_axioms" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules[idx.toNat]!.getRoot == `SwarmDiameter then
        checked := checked + 1
        let axioms ← collectAxioms name
        let unexpected := axioms.filter fun ax =>
          ax != `propext && ax != `Classical.choice && ax != `Quot.sound
        unless unexpected.isEmpty do
          throwError "{name}: unexpected axioms {unexpected}"
  unless checked > 0 do
    throwError "No swarm renewal declarations were checked"
  logInfo m!"SWARM RENEWAL AXIOMS OK: {checked} declarations"

#audit_swarm_renewal_axioms
