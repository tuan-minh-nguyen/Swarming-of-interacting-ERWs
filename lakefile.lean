import Lake
open Lake DSL

package swarming

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib Swarm

lean_lib SwarmDiameter where
  roots := #[`SwarmDiameter.RenewalProcess, `SwarmDiameter.RegenerationBlocks,
    `SwarmDiameter.FirstIntervalOccupation, `SwarmDiameter.TailBounds,
    `SwarmDiameter.ReflectionExcursion, `SwarmDiameter.SymmetricConfinement,
    `SwarmDiameter.SwarmLowerBounds, `SwarmDiameter.OccupationTail,
    `SwarmDiameter.SwarmUpperGrowth, `SwarmDiameter.RecordExceedance,
    `SwarmDiameter.MarkedSpatialTail, `SwarmDiameter.ProjectedPotentialOscillation,
    `SwarmDiameter.RecordTrialConcentration, `SwarmDiameter.RecordOccupationMartingale,
    `SwarmDiameter.RecordGroupDrift, `SwarmDiameter.RecordGroupAdvance, `SwarmDiameter.RecordGroupMovement, `SwarmDiameter.RecordLocalClauses]
