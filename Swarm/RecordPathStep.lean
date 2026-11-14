/-
# One-step identity and frequency for the actual stopped-record path law.

This links the independently proved homogeneous Ionescu–Tulcea path identity to
`WCJF.RecFreq.RecordStepIdentity`; only actual record tightness remains in the
frequency capstone. No new invariant law or start-law assumption is introduced.
-/
import Swarm.OneStepRegenBC
import Swarm.RecordFrequency

open MeasureTheory ProbabilityTheory Filter Topology
open MeasureTheory.Filtration
open scoped ENNReal BigOperators

set_option linter.style.haveILetI false

namespace WCJF.RecFreq

open SwarmRec SimJump.RecKernel

variable {N m : ℕ}

/-- The literal `RecordStepIdentity` is the homogeneous Ionescu–Tulcea one-step identity. -/
theorem recordStepIdentity_actual (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (μ₀ : Measure (RecState N m)) [IsProbabilityMeasure μ₀] :
    RecordStepIdentity (N := N) (m := m) p hp hp1 hm μ₀ := by
  letI : IsMarkovKernel (hitKKernel (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernel p hp hp1 hm
  intro n
  have h := WCJF.OneStepBridge.condExp_indicator_succ
    (X := RecState N m) (hitKKernel (N := N) (m := m) p hm) μ₀ n
    (measurableSet_srSet N m)
  simpa only [SimJump.RecKernel.recordTraj, recordFilt,
    WCJF.OneStepBridge.pathLaw, SimJump.RecKernel.homTraj,
    WCJF.OneStepBridge.constFam, SimJump.RecKernel.homFam] using h

/-- Infinitely many simultaneous record states from the literal dT tightness,
with the one-step Markov property proved rather than assumed. -/
theorem ae_frequently_srSet_of_dT_tight (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ ω ∂(recordTraj p hp hp1 hm (ν.map Prod.fst)),
      ∃ᶠ n in atTop, ω n ∈ srSet N m := by
  letI : IsProbabilityMeasure (ν.map Prod.fst) := isProbabilityMeasure_map_fst ν
  exact ae_frequently_srSet_of_dT_tight_of_step p hp hp1 hp_lt hm hN ν
    (recordStepIdentity_actual p hp hp1 hm (ν.map Prod.fst)) htight

end WCJF.RecFreq
