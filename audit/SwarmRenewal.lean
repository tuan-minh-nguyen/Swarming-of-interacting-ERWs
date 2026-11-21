import SwarmDiameter.SwarmRenewal
import Lean

open Lean Elab Command

#print axioms Swarming.Diameter.exists_diameter_occupationLaw

elab "#audit_swarm_renewal_axioms" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut checked := 0
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
