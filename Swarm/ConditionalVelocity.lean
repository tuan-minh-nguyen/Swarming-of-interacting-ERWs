/-
# Positive initial regeneration and the conditional WCJF velocity

This module composes only verified inputs. The genuine dT tightness at the actual
zero-state Dirac start gives (i) the invariant stopped-record distribution, (ii) full
selection, and (iii) the actual R1 row recurrence. The selected-block no-regeneration
bridge then produces a genuine positive-level `StrictAttempt`, rather than merely
`RegenAtStrict 0 0`. The already-verified frontier converts per-`N` invariant record
laws plus this almost-sure positive initial attempt into the positive common velocity.
-/
import Swarm.M1Bridge
import Swarm.TowerForceFrontier

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open MeasureTheory Set ProbabilityTheory Filter Topology Classical
open SwarmRestart SwarmFresh SwarmRecordMeas.StartLaw SwarmRec
open SimJump SimJump.RecKernel Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

namespace SwarmDTR

variable {N m : ℕ} [Nonempty (Fin N)]

/-- The exact iterate-tail shape which an invariant law/full selection construction
needs, obtained directly from the paper's dT tail at its forced Dirac start. -/
theorem iterateTight_of_dT_tight {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0 hp1 hm ν) {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      ((SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] (ν.map Prod.fst))
        (exh N m K)ᶜ ≤ ε := by
  exact (TightAvail.iterate_tight_iff_dT_tail (N := N) (m := m) p hp0 hp1 hm ν).mpr htight

/-- An invariant stopped-record law from literal dT tightness at the canonical zero state. -/
theorem exists_invariant_of_dT_tight {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∃ (π : Measure (RecState N m)), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π := by
  letI : IsProbabilityMeasure (TightAvail.startLaw (N := N) (m := m) hm) :=
    TightAvail.isProbabilityMeasure_startLaw hm
  have htmp := iterateTight_of_dT_tight (N := N) (m := m) hp0.le hp1.le hm
    (TightAvail.startLaw (N := N) (m := m) hm) htight
  rw [TightAvail.startLaw_fst] at htmp
  obtain ⟨π, hprob, hinv, -⟩ :=
    exists_invariant_measure_pos_hitKInf_feller (N := N) (m := m) p
      hp0.le hp1.le hp1 hm hN (Measure.dirac (zeroState (N := N) (m := m) hm)) htmp
  exact ⟨π, hprob, hinv⟩
/-- The positive initial attempt from the exact dT tightness, not from a stationary start. -/
theorem ae_exists_strictAttempt_of_dT_tight {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ r, RawStrictAttemptTower.StrictAttempt p m U r := by
  let hm1 : 1 ≤ m := by omega
  letI : IsProbabilityMeasure (TightAvail.startLaw (N := N) (m := m) hm1) :=
    TightAvail.isProbabilityMeasure_startLaw hm1
  have hiter := iterateTight_of_dT_tight (N := N) (m := m) hp0.le hp1.le hm1
    (TightAvail.startLaw (N := N) (m := m) hm1) htight
  rw [TightAvail.startLaw_fst] at hiter
  apply M1Bridge.ae_exists_strictAttempt_of_fullSelection p m hp0 hp1 hm hN
    (SwarmRowTail.rowRecurrence_ae hp0 hp1 hm hN htight)
  exact SwarmActualHfull.full_selection_of_tight (N := N) hm1 hp0 hp1
    (by omega : 0 < N) (Measure.dirac (zeroState (N := N) (m := m) hm1)) hiter

/-- Conditional Theorem 1.1: literal positive common velocity from actual dT tightness
and every compatible Dirac start, with no extra invariance, stationarity or start law. -/
theorem main_claim_of_dT_tight {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (htight : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
        (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
          {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) := by
  refine TowerForceFrontier.main_claim_actual_of_tower_ae (p := p) hp0 hp1 hm ?_ ?_
  · intro N hN
    letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    exact exists_invariant_of_dT_tight (N := N) hp0 hp1 (by omega : 1 ≤ m) (by omega : 0 < N)
      (htight N hN)
  · intro N inst hN
    letI : Nonempty (Fin N) := inst
    exact ae_exists_strictAttempt_of_dT_tight (N := N) hp0 hp1 hm hN (htight N hN)

end SwarmDTR
