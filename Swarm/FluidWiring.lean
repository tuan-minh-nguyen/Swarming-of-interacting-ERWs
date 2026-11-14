/-
# Wiring the single fluid-time condition into the integrated tightness chain

`FluidBlock` shows that the paper's two block bad events are both excluded at one integer time by
the single fluid condition `GoodTime`.  This file transfers that to the **actual array**: the
canonical record data `arrQ p m U = (defect·toNat, recTimeA)` is exactly the shape `FluidBlock`
uses, and `SwarmRecordMeas.Actual.ae_isRecord_recTimeA` supplies `IsRecord` almost surely, so

    (arrayMeasure N) {U : Swarming.Uniform.Array N | BadTime … (arrQ p m U) r ℓ} ≤ (arrayMeasure N) {U : Swarming.Uniform.Array N | no good time}

and the same for `BadHalf`.  Consequently `HdefDefect.record_tightness_of_two_actual_hdef_free`
runs with a **single** profile `P` instead of the pair `(p₁, p₂)`.

What this does *not* do: it does not bound the new profile.  `noGoodTime` is not weaker than
`BadTime ∪ BadHalf` pointwise; it is the shape in which the paper's Proposition `local` +
fluid-limit argument produces a single bound, so this is the interface a formalisation of
`(goodprob)` should target.
-/
import Swarm.FluidBlock
import Swarm.HdefDefect

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace FluidWiring

open RecordDefect RecordoSupply SwarmM4C.LawBridge HblkTwo HblkFinal SwarmRecordMeas
open SwarmRecordMeas.Actual FluidBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-- On the actual array, the paper's first block bad event is dominated by the failure of the
single fluid-time condition. -/
theorem badTime_le_noGoodTime {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N | BadTime B T (arrQ p m U) r L} ≤
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n} := by
  have hrec := SwarmRecordMeas.Actual.ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hnull : (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | ¬ IsRecord (actX p m U) (recTimeA p m U)} = 0 := ae_iff.mp hrec
  have hsub : {U : Swarming.Uniform.Array N | BadTime B T (arrQ p m U) r L} ⊆
      ({U : Swarming.Uniform.Array N | ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}
        ∪ {U : Swarming.Uniform.Array N | ¬ IsRecord (actX p m U) (recTimeA p m U)}) := by
    intro U hU
    by_cases hR : IsRecord (actX p m U) (recTimeA p m U)
    · refine Set.mem_union_left _ ?_
      rintro ⟨n, hn⟩
      exact (goodTime_imp_not_bad hR (actX_step p m U) (actX_zero p m U) hC₀ hn).1 hU
    · exact Set.mem_union_right _ hR
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hnull, add_zero]

/-- On the actual array, the paper's second block bad event is dominated by the failure of the
single fluid-time condition. -/
theorem badHalf_le_noGoodTime {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N | BadHalf B (arrQ p m U) r L} ≤
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n} := by
  have hrec := SwarmRecordMeas.Actual.ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN
  have hnull : (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N | ¬ IsRecord (actX p m U) (recTimeA p m U)} = 0 := ae_iff.mp hrec
  have hsub : {U : Swarming.Uniform.Array N | BadHalf B (arrQ p m U) r L} ⊆
      ({U : Swarming.Uniform.Array N | ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r L n}
        ∪ {U : Swarming.Uniform.Array N | ¬ IsRecord (actX p m U) (recTimeA p m U)}) := by
    intro U hU
    by_cases hR : IsRecord (actX p m U) (recTimeA p m U)
    · refine Set.mem_union_left _ ?_
      rintro ⟨n, hn⟩
      exact (goodTime_imp_not_bad hR (actX_step p m U) (actX_zero p m U) hC₀ hn).2 hU
    · exact Set.mem_union_right _ hR
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hnull, add_zero]

/-- **Record-defect tightness of the canonical stopped-record path law from a single profile on
the fluid condition.**

This is `HdefDefect.record_tightness_of_two_actual_hdef_free` with the pair `(p₁, p₂)` replaced by
one profile `P` bounding the probability that no good fluid time exists, and both certificate
sums stated at `P` alone.  Nothing else changes: the speed `κ`, `hterm`, `hdef`, the record-path
law identity and `(diam)` are still the proved theorems of the integrated tree. -/
theorem record_tightness_of_goodTime {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (P : ℕ → ℝ≥0∞),
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U : Swarming.Uniform.Array N | ¬ ∃ n : ℕ,
            GoodTime (actX p m U) (recTimeA p m U) B (⌈2 * (B : ℝ) / κ⌉₊ + 2) r ℓ n} ≤ P ℓ) →
      ∀ (k : ℕ), 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ 2 ^ k →
        (∑' r : ℕ, P (2 ^ HdefDefect.g k r)) ≠ ⊤ →
        (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * P ℓ) ≠ ⊤ →
        ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
          (SimJump.RecKernel.recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
            (Measure.dirac (StartLaw.zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
            {ω | K < SimJump.RecKernel.dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, H⟩ :=
    HdefDefect.record_tightness_of_two_actual_hdef_free (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun P hP k hk hsum hcert ε hε => ?_⟩
  refine H P P ?_ ?_ k hk ?_ ?_ ε hε
  · intro ℓ hℓ r hr
    exact le_trans (badTime_le_noGoodTime (N := N) hp0 hp1 hm hN (le_rfl : B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1 ≤ _))
      (hP ℓ hℓ r hr)
  · intro ℓ hℓ r hr
    exact le_trans (badHalf_le_noGoodTime (N := N) hp0 hp1 hm hN (le_rfl : B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1 ≤ _))
      (hP ℓ hℓ r hr)
  · have hsplit : (∑' r : ℕ, (P + P) (2 ^ HdefDefect.g k r))
        = (∑' r : ℕ, P (2 ^ HdefDefect.g k r))
          + (∑' r : ℕ, P (2 ^ HdefDefect.g k r)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun r => Pi.add_apply P P _
    rw [hsplit]
    exact ENNReal.add_ne_top.2 ⟨hsum, hsum⟩
  · have hsplit : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * (P + P) ℓ)
        = (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * P ℓ)
          + (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * P ℓ) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun ℓ => by rw [Pi.add_apply, mul_add]
    rw [hsplit]
    exact ENNReal.add_ne_top.2 ⟨hcert, hcert⟩

end FluidWiring


