import SwarmDiameter.SwarmLowerBounds
import SwarmDiameter.OccupationTail
import SwarmDiameter.SwarmUpperGrowth
import SwarmDiameter.RecordExceedance
import SwarmDiameter.MarkedSpatialTail
import SwarmDiameter.ProjectedPotentialOscillation
import SwarmDiameter.RecordTrialConcentration
import Lean

open Lean Elab Command

#print axioms Swarming.Diameter.exists_diameter_occupationLaw
#print axioms Swarming.Diameter.linear_trial_at_stopping_time_mass_ge
#print axioms Swarming.Diameter.two_walker_trial_at_stopping_time_mass_ge
#print axioms Swarming.Diameter.exists_positive_simultaneousRecordDensity
#print axioms Swarming.Diameter.exists_leading_walk_trial_mass_ge
#print axioms Swarming.Diameter.exists_cubic_trial_mass_ge
#print axioms Swarming.Diameter.exists_diameter_lower_bounds
#print axioms Swarming.Diameter.tendsto_record_event_occupation
#print axioms Swarming.Diameter.first_regeneration_diameter_occupation_le_record_limsup
#print axioms Swarming.Diameter.ae_log_pow_upper_of_regeneration_occupation
#print axioms Swarming.Diameter.record_interval_exceedance_prob_le
#print axioms Swarming.Diameter.record_diameter_tail_le_of_contraction
#print axioms Swarming.Diameter.record_duration_limsup_le_of_advance
#print axioms Swarming.Diameter.sum_hof_pow_le_marked_gaps
#print axioms Swarming.Diameter.measure_union_markedGapEvent
#print axioms Swarming.Diameter.arrayMeasure_sum_hof_pow_tail
#print axioms Swarming.Diameter.arrayMeasure_local_hof_estimates
#print axioms Swarming.Diameter.record_projH_oscillation_le_cube_root
#print axioms Swarming.Diameter.gamma_trial_concentration
#print axioms Swarming.Diameter.eventually_regeneration_occupation_le_of_record_tails
#print axioms Swarming.Diameter.exists_diameter_limit_with_upper_tail_of_regeneration_occupation

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
