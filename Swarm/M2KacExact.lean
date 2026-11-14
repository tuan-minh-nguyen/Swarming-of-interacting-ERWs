/-
# The Kac quantity computed exactly in the one-sided i.i.d. model

`KacFormula.kac_tsum_le_one` bounds the tail sums `Σ_k μ (A ∩ {D > k})` by `1` for an
invertible measure-preserving map.  `M2KacExt.oneSided_kac_lintegral_le_one` transfers the
bound to the **one-sided** i.i.d. bit shift.  This file computes the same quantity exactly
there and shows the bound is **attained**:

    `Σ_k μ (A ∩ {D > k}) = ν {true} · Σ_k (ν {false})^k = ν {true} / ν {true} = 1`

for `A = {x | x 0 = true}`, `D` the first positive return time of the one-sided shift and
`μ = Measure.infinitePi ν`.  So the one-sided transfer of `M2KacExt` is sharp, while (by
`M2KacExt.translate_tsum_linear`) the *translate* masses `Σ_k μ (T^k(A ∩ {D > k}))` diverge,
which is exactly why the disjointness proof cannot be transported.

Nothing here proves `Ballistic`, `RegenAvailable` or `MainClaim`; it is a model-case
computation of the paper's Kac quantity `∫_A D dP_π`.
-/
import Swarm.M2KacExt

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace SwarmM2Kac

/-- The set where the first `k` coordinates after the origin are all `false`. -/
def off (k : ℕ) : Set (ℕ → Bool) := {x | ∀ j, 0 < j → j ≤ k → x j = false}

theorem hitSet_inter_noReturn_eq (k : ℕ) :
    hitSet ∩ KacFormula.noReturn shiftℕ hitSet k = hitSet ∩ off k := by
  ext x
  simp only [mem_inter_iff, KacFormula.noReturn, mem_ofPred_eq, off, mem_hitSet_iff]
  constructor
  · rintro ⟨h0, hnr⟩
    refine ⟨h0, fun j hj hjk => ?_⟩
    cases hxj : x j with
    | false => rfl
    | true =>
        exact absurd (by rw [shiftℕ_iterate_apply, Nat.zero_add]; exact hxj) (hnr j hj hjk)
  · rintro ⟨h0, hoff⟩
    refine ⟨h0, fun j hj hjk hmem => ?_⟩
    rw [shiftℕ_iterate_apply, Nat.zero_add] at hmem
    rw [hoff j hj hjk] at hmem
    exact Bool.false_ne_true hmem

theorem hitSet_inter_off_eq_pi (k : ℕ) :
    hitSet ∩ off k
      = (↑(Finset.Icc 0 k) : Set ℕ).pi (fun i => if i = 0 then {true} else {false}) := by
  ext x
  simp only [mem_inter_iff, mem_hitSet_iff, off, Set.mem_pi, Finset.mem_coe, Finset.mem_Icc]
  constructor
  · rintro ⟨h0, hoff⟩ i hi
    by_cases hiz : i = 0
    · subst hiz
      simp [h0]
    · have hf : x i = false := hoff i (by omega) hi.2
      simp [hiz, hf]
  · intro h
    refine ⟨?_, fun j hj hjk => ?_⟩
    · have h := h 0 ⟨le_refl 0, by omega⟩
      rw [if_pos rfl] at h
      simpa using h
    · have hxj := h j ⟨by omega, hjk⟩
      have hj0 : j ≠ 0 := by omega
      rw [if_neg hj0] at hxj
      simpa using hxj

theorem pi_measurable (k : ℕ) :
    ∀ i ∈ Finset.Icc 0 k, MeasurableSet ((fun i => if i = 0 then {true} else {false}) i) := by
  intro i _
  show MeasurableSet (if i = 0 then ({true} : Set Bool) else {false})
  by_cases hi : i = 0
  · rw [if_pos hi]; exact measurableSet_singleton true
  · rw [if_neg hi]; exact measurableSet_singleton false

theorem prod_eval (k : ℕ) {ν : Measure Bool} :
    ∏ i ∈ Finset.Icc 0 k, ν ((fun i => if i = 0 then {true} else {false}) i)
      = ν {true} * (ν {false}) ^ k := by
  have hsplit : Finset.Icc 0 k = insert 0 (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Icc 1 k := by simp
  rw [hsplit, Finset.prod_insert hnot]
  have hstep : ∏ i ∈ Finset.Icc 1 k, ν ((fun i => if i = 0 then {true} else {false}) i)
      = ∏ _i ∈ Finset.Icc 1 k, ν {false} := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    show ν (if i = 0 then ({true} : Set Bool) else {false}) = ν {false}
    rw [if_neg hi1]
  rw [hstep, Finset.prod_const, Nat.card_Icc]
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  simp

/-- **The exact tail mass in the one-sided i.i.d. model**: `ν {true} · (ν {false})^k`. -/
theorem tail_mass_eq {ν : Measure Bool} [IsProbabilityMeasure ν] (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν) (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)
      = ν {true} * (ν {false}) ^ k := by
  rw [hitSet_inter_noReturn_eq, hitSet_inter_off_eq_pi,
    Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (pi_measurable k), prod_eval]

/-- **Kac's bound is attained in the one-sided i.i.d. model.**  For `0 < ν {true}` the tail
sum equals `1` exactly, so the one-sided transfer of `M2KacExt` gives the correct value and
not merely an inequality. -/
theorem tsum_tail_mass_eq_one {ν : Measure Bool} [IsProbabilityMeasure ν]
    (hν : ν {true} ≠ 0) :
    ∑' k : ℕ, (Measure.infinitePi fun _ : ℕ => ν)
      (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k) = 1 := by
  have hcompl : ν {true} + ν {false} = 1 := by
    have h := measure_add_measure_compl (μ := ν) (s := ({true} : Set Bool)) (measurableSet_singleton true)
    have hc : ({true} : Set Bool)ᶜ = {false} := by
      ext b
      cases b <;> simp
    rw [hc, measure_univ] at h
    exact h
  have hnonatomic : ν {false} ≠ ⊤ := measure_ne_top ν _
  have hsub : (1 : ℝ≥0∞) - ν {false} = ν {true} :=
    ENNReal.sub_eq_of_eq_add hnonatomic hcompl.symm
  calc ∑' k : ℕ, (Measure.infinitePi fun _ : ℕ => ν)
        (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)
      = ∑' k : ℕ, ν {true} * (ν {false}) ^ k := tsum_congr (fun k => tail_mass_eq k)
    _ = ν {true} * ∑' k : ℕ, (ν {false}) ^ k := ENNReal.tsum_mul_left
    _ = ν {true} * (1 - ν {false})⁻¹ := by rw [ENNReal.tsum_geometric]
    _ = ν {true} * (ν {true})⁻¹ := by rw [hsub]
    _ = 1 := ENNReal.mul_inv_cancel hν (measure_ne_top ν _)

/-! ## The layer-cake form, and the exact Kac value in the model -/

section LayerCake

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The layer-cake identity for the return time of a one-sided map**:
`∫_A D dμ = Σ_k μ (A ∩ {D > k})`.  This is the first half of
`KacFormula.kac_lintegral_le_one`, isolated for a general (not necessarily invertible) map. -/
theorem lintegral_retTime_eq_tsum {f : Ω → Ω} (hf : Measurable f) (A : Set Ω)
    (hA : MeasurableSet A) :
    ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ
      = ∑' k : ℕ, μ (A ∩ KacFormula.noReturn f A k) := by
  set D : Ω → ℕ∞ := KacFormula.retTime f A with hDdef
  have hD : Measurable D := KacFormula.measurable_retTime hf hA
  have hkey : ∀ ω : Ω, (D ω : ℝ≥0∞)
      = ∑' k : ℕ, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) :=
    fun ω => (KacFormula.tsum_ite_lt (D ω)).symm
  have hmeas : ∀ k : ℕ, MeasurableSet {ω : Ω | (k : ℕ∞) < D ω} := fun k =>
    hD (show MeasurableSet (Set.Ioi (k : ℕ∞)) from trivial)
  have hrewrite : ∀ k : ℕ,
      {ω : Ω | (k : ℕ∞) < D ω} ∩ A = A ∩ KacFormula.noReturn f A k := by
    intro k
    ext ω
    simp only [mem_inter_iff, hDdef, KacFormula.lt_retTime_iff]
    tauto
  calc ∫⁻ ω in A, (D ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑' k : ℕ, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) ∂(μ.restrict A) := by
        simp only [hkey]
    _ = ∑' k : ℕ, ∫⁻ ω, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) ∂(μ.restrict A) :=
        lintegral_tsum fun k => (measurable_const.ite (hmeas k) measurable_const).aemeasurable
    _ = ∑' k : ℕ, (μ.restrict A) {ω : Ω | (k : ℕ∞) < D ω} := by
        refine tsum_congr fun k => ?_
        exact KacFormula.lintegral_ite_one (hmeas k)
    _ = ∑' k : ℕ, μ (A ∩ KacFormula.noReturn f A k) := by
        refine tsum_congr fun k => ?_
        rw [Measure.restrict_apply (hmeas k), hrewrite k]

end LayerCake

/-- **The Kac bound is attained**: in the one-sided i.i.d. model the mean return time to
`A = {x | x 0 = true}` is exactly `1`, i.e. `E_{μ(·|A)}[D] = 1/μ(A)`.  Combined with
`oneSided_kac_lintegral_le_one` (which obtains `≤ 1` from the *two-sided* extension) this
shows that the one-sided transfer of `M2KacExt` is sharp, in contrast with
`translate_tsum_linear`. -/
theorem lintegral_retTime_eq_one {ν : Measure Bool} [IsProbabilityMeasure ν]
    (hν : ν {true} ≠ 0) :
    ∫⁻ x in hitSet, (KacFormula.retTime shiftℕ hitSet x : ℝ≥0∞)
      ∂(Measure.infinitePi fun _ : ℕ => ν) = 1 := by
  rw [lintegral_retTime_eq_tsum measurable_shiftℕ hitSet measurableSet_hitSet,
    tsum_tail_mass_eq_one hν]

end SwarmM2Kac
