import SwarmDiameter.SwarmLowerBounds
import SwarmDiameter.OccupationTail
import SwarmDiameter.SwarmUpperGrowth
import SwarmDiameter.RecordExceedance
import SwarmDiameter.MarkedSpatialTail
import SwarmDiameter.ProjectedPotentialOscillation
import SwarmDiameter.RecordTrialConcentration
import SwarmDiameter.RecordOccupationMartingale
import SwarmDiameter.RecordGroupMovement
import SwarmDiameter.RecordLocalClauses
import SwarmDiameter.SwarmDiameterCubic
import SwarmDiameter.RecordDownwardCrossing
import SwarmDiameter.RecordMartingaleAtOffset
import SwarmDiameter.SwarmDiameterTwoWalker
import SwarmDiameter.MinimumProgress
import SwarmDiameter.SoftMinimum
import SwarmDiameter.BoundedPotential
import SwarmDiameter.RecordBoundedSpatial
import SwarmDiameter.RecordMinimumOccupation
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
#print axioms Swarming.Diameter.record_Qpl_maximal_deviation_le_cube_root
#print axioms Swarming.Diameter.record_Qpl_oscillation_le_cube_root
#print axioms Swarming.Diameter.record_group_drift_failure_le_cube_root
#print axioms Swarming.Diameter.record_separated_group_failure_le_cube_root
#print axioms Swarming.Diameter.record_group_advance_drift_failure_le_cube_root
#print axioms Swarming.Diameter.record_group_potential_failure_le_cube_root
#print axioms Swarming.Diameter.record_group_maximum_failure_le_cube_root
#print axioms Swarming.Diameter.record_group_movement_failure_le_cube_root
#print axioms Swarming.Diameter.record_occupation_estimate_of_local_bounds
#print axioms Swarming.Diameter.record_occupation_failure_le_cube_root
#print axioms Swarming.Diameter.record_local_clauses_failure_le_cube_root
#print axioms Swarming.Diameter.coalesced_at_of_local_errors
#print axioms Swarming.Diameter.record_defect_halves_of_local_clauses
#print axioms Swarming.Diameter.record_cubic_block_failure_le
#print axioms Swarming.Diameter.record_interval_tails_le_of_block
#print axioms Swarming.Diameter.swarm_diameter_cubic
#print axioms Swarming.Diameter.record_downward_crossing_prob_le
#print axioms Swarming.Diameter.record_downward_excursion_failure_le_sqrt
#print axioms Swarming.Diameter.record_offset_martingale_window_prob_le
#print axioms Swarming.Diameter.two_walker_front_excursion_prob_le
#print axioms Swarming.Diameter.record_offset_interval_survival_prob_le
#print axioms Swarming.Diameter.two_walker_passage_order_prob_le
#print axioms Swarming.Diameter.exists_passage_order_of_large_diameter
#print axioms Swarming.Diameter.two_walker_meeting_of_no_deviations
#print axioms Swarming.Diameter.record_two_walker_halving_failure_le_sqrt
#print axioms Swarming.Diameter.record_two_walker_exceedance_limsup_le
#print axioms Swarming.Diameter.swarm_diameter_two_walker
#print axioms Swarming.Diameter.record_minimum_progress_failure_le_exp
#print axioms Swarming.Diameter.softMinimum_sub_ge_weighted_sum
#print axioms Swarming.Diameter.softMinimum_weighted_drift_lower
#print axioms Swarming.Diameter.boundedSlope_le_window
#print axioms Swarming.Diameter.boundedPotential_mean_increment
#print axioms Swarming.Diameter.arrayMeasure_Q_intervals_gt
#print axioms Swarming.Diameter.arrayMeasure_Pz_sq_intervals_gt
#print axioms Swarming.Diameter.boundedHA_sub_le_of_Q_sum
#print axioms Swarming.Diameter.card_boundedExceptionSites_le
#print axioms Swarming.Diameter.record_weighted_jump_failure_le_exp
#print axioms Swarming.Diameter.record_minimum_occupation_failure_le_exp
#print axioms Swarming.Diameter.record_small_set_minimum_occupation_failure_le_exp
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
