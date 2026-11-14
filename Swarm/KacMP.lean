/-
# Kac's inequality for a merely measure-preserving map: no invertible extension needed

`KacFormula.kac_lintegral_le_one` (`Swarm/KacDisjoint.lean`) proves
`∫⁻_A retTime θ A ≤ 1` for an **invertible** measurable equivalence `θ`, by showing that the
translated towers `θ^k (A ∩ {D > k})` are pairwise disjoint.  `areas/kac/KAC_EXTENSION.md` §2
records the consequence: for the one-sided stopped-record chain, whose shift is neither
injective nor invertible, the Kac step is left as the residual "construct an invertible
stationary extension", and `M2KacExt.kac_lintegral_le_one_of_extension` transfers the bound
through such an extension, while `M2KacExt.translate_tsum_linear` shows the *forward*-translate
masses do not decay at all.

This file removes that residual.  The Kac inequality is a theorem about **every**
measure-preserving self-map of a probability space; invertibility is not used by a correct
proof.  The proof below is the standard finite-window *backward* one.  For `N : ℕ` put

  `G k = (f^[k]) ⁻¹' (A ∩ {no return to A during the first N - k steps})`,  `0 ≤ k ≤ N`.

* the `G k` with `k ≤ N` are **pairwise disjoint**: a point of `G k ∩ G ℓ` with `k < ℓ` has
  `f^[ℓ] x ∈ A` (from `G ℓ`) and, because `0 < ℓ - k ≤ N - k`, also `f^[ℓ] x ∉ A` (from `G k`);
* `μ (G k) = μ (A ∩ {D > N - k})` by measure preservation;
* so `Σ_{m ≤ N} μ (A ∩ {D > m}) = Σ_{k ≤ N} μ (G k) = μ (⋃_{k ≤ N} G k) ≤ 1`.

Every finite partial sum of `Σ_m μ (A ∩ {D > m})` is therefore at most `1`.  Nothing beyond
measurability of `f` and `MeasurePreserving f μ μ` is used; `f` may be non-injective,
non-invertible and have no invariant-measure structure at all beyond `f_*μ = μ`.

This is a known lemma (Kac's lemma for non-invertible transformations); the point of the file
is that it is not in the campaign, and that its absence — not a missing Kolmogorov extension —
is what the record-chain Kac step was reading.

The corollaries mirror the invertible versions of `KacDisjoint.lean` one-for-one
(`kac_mp_tsum_le_one`, `kac_mp_lintegral_le_one`, `kac_mp_ae_retTime_lt_top`,
`kac_mp_integral_toReal_le_one`, `kac_mp_cond_mean_le`), so this file can replace the
extension route in `M2KacExt.kac_path_bound_of_extension` without adding any hypothesis.
-/
import Swarm.M2KacExact

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SwarmKacMP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Ω}

/-! ## The backward windows -/

/-- The `k`-th backward window: the points whose `k`-th image lies in `A` with no return to `A`
during the following `N - k` steps.  For `k ≤ N` these are the sets whose disjointness replaces
the forward towers `θ^k (A ∩ {D > k})` of the invertible proof. -/
def backWin (f : Ω → Ω) (A : Set Ω) (N k : ℕ) : Set Ω :=
  (f^[k]) ⁻¹' (A ∩ KacFormula.noReturn f A (N - k))

lemma measurableSet_backWin (hf : Measurable f) {A : Set Ω} (hA : MeasurableSet A) (N k : ℕ) :
    MeasurableSet (backWin f A N k) :=
  (hA.inter (KacFormula.measurableSet_noReturn hf hA (N - k))).preimage (hf.iterate k)

/-- Membership unfolds to the two facts used below: `f^[k] x ∈ A`, and no return during the
`N - k` steps that follow. -/
lemma mem_backWin {A : Set Ω} {N k : ℕ} {x : Ω} :
    x ∈ backWin f A N k ↔
      f^[k] x ∈ A ∧ ∀ j, 0 < j → j ≤ N - k → f^[j] (f^[k] x) ∉ A :=
  Iff.rfl

/-- The ordered disjointness that the pairwise statement reduces to: for `k < ℓ ≤ N` the `k`-th
and `ℓ`-th backward windows are disjoint.  This is where the invertible proof needs `θ`
injective; reading the tower backwards with a shrinking window makes injectivity unnecessary,
because the contradiction comes from `f^[ℓ] x` alone. -/
lemma disjoint_backWin {N k ℓ : ℕ} (A : Set Ω) (hkl : k < ℓ) (hℓN : ℓ ≤ N) :
    Disjoint (backWin f A N k) (backWin f A N ℓ) := by
  refine Set.disjoint_left.2 fun x hxk hxℓ => ?_
  obtain ⟨-, hkn⟩ := (mem_backWin (f := f) (A := A) (N := N) (k := k)).1 hxk
  obtain ⟨hℓA, -⟩ := (mem_backWin (f := f) (A := A) (N := N) (k := ℓ)).1 hxℓ
  have hpos : 0 < ℓ - k := by omega
  have hle : ℓ - k ≤ N - k := by omega
  have hno := hkn (ℓ - k) hpos hle
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkl.le] at hno
  exact hno hℓA

/-- **Pairwise disjointness of the backward windows.** -/
lemma pairwiseDisjoint_backWin (N : ℕ) (A : Set Ω) :
    PairwiseDisjoint (↑(Finset.range (N + 1))) (backWin f A N) := by
  intro k hk ℓ hℓ hkℓ
  rw [Finset.coe_range, mem_Iio] at hk hℓ
  rcases lt_or_gt_of_ne hkℓ with hlt | hlt
  · exact disjoint_backWin A hlt (by omega)
  · exact (disjoint_backWin A hlt (by omega)).symm

/-- Measure preservation turns the backward window into the ordinary tail-set, with the index
reflected: `μ (G k) = μ (A ∩ {D > N - k})`. -/
lemma measure_backWin (hmp : MeasurePreserving f μ μ) {A : Set Ω} (hA : MeasurableSet A)
    (N k : ℕ) :
    μ (backWin f A N k) = μ (A ∩ KacFormula.noReturn f A (N - k)) := by
  rw [backWin]
  exact (hmp.iterate k).measure_preimage
    (hA.inter (KacFormula.measurableSet_noReturn hmp.measurable hA (N - k))).nullMeasurableSet

/-! ## The finite partial sums -/

/-- **Every finite partial sum of the Kac tails is at most one.**  This is the whole content; the
`tsum` statement below is its monotone-convergence shadow. -/
theorem sum_range_tail_le_one (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), μ (A ∩ KacFormula.noReturn f A m)) ≤ 1 := by
  have hmeas : ∀ k ∈ Finset.range (N + 1), MeasurableSet (backWin f A N k) :=
    fun k _ => measurableSet_backWin hmp.measurable hA N k
  have hsum : (∑ k ∈ Finset.range (N + 1), μ (backWin f A N k))
      = μ (⋃ k ∈ Finset.range (N + 1), backWin f A N k) :=
    (measure_biUnion_finset (pairwiseDisjoint_backWin N A) hmeas).symm
  have hstep : ∀ k ∈ Finset.range (N + 1),
      μ (backWin f A N k) = μ (A ∩ KacFormula.noReturn f A (N - k)) := by
    intro k _
    exact measure_backWin hmp hA N k
  calc (∑ m ∈ Finset.range (N + 1), μ (A ∩ KacFormula.noReturn f A m))
      = ∑ k ∈ Finset.range (N + 1), μ (A ∩ KacFormula.noReturn f A (N - k)) :=
        (Finset.sum_range_reflect _ (N + 1)).symm
    _ = ∑ k ∈ Finset.range (N + 1), μ (backWin f A N k) :=
        Finset.sum_congr rfl fun k hk => (hstep k hk).symm
    _ = μ (⋃ k ∈ Finset.range (N + 1), backWin f A N k) := hsum
    _ ≤ μ univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- **Kac's inequality, tail-sum form, without invertibility.**
`Σ_{k≥0} μ (A ∩ {D > k}) ≤ 1` for any measure-preserving `f` on a probability space. -/
theorem kac_mp_tsum_le_one (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    (∑' k : ℕ, μ (A ∩ KacFormula.noReturn f A k)) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  exact iSup_le fun N => sum_range_tail_le_one hmp A hA N

/-- **Kac's inequality, integral form, without invertibility.**  `∫⁻_A D dμ ≤ 1`. -/
theorem kac_mp_lintegral_le_one (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1 := by
  rw [SwarmM2Kac.lintegral_retTime_eq_tsum hmp.measurable A hA]
  exact kac_mp_tsum_le_one hmp A hA

/-! ## The corollaries matching the invertible API -/

/-- Poincaré recurrence, without invertibility: on `A` the return time is almost surely finite. -/
theorem kac_mp_ae_retTime_lt_top (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(μ.restrict A), (KacFormula.retTime f A ω : ℝ≥0∞) < ⊤ := by
  have hD : Measurable (KacFormula.retTime f A) := KacFormula.measurable_retTime hmp.measurable hA
  refine ae_lt_top (KacFormula.measurable_enat_coe.comp hD) ?_
  exact ne_top_of_le_ne_top (by simp) (kac_mp_lintegral_le_one hmp A hA)

/-- Real-valued Kac inequality, without invertibility: `∫_A D dμ ≤ 1`. -/
theorem kac_mp_integral_toReal_le_one (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    ∫ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞).toReal ∂μ ≤ 1 := by
  have hD : Measurable (KacFormula.retTime f A) := KacFormula.measurable_retTime hmp.measurable hA
  have hint : ∫ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞).toReal ∂μ
      = (∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ).toReal := by
    simpa only [Function.comp_apply] using
      integral_toReal (μ := μ.restrict A)
        (f := fun ω => (KacFormula.retTime f A ω : ℝ≥0∞))
        (KacFormula.measurable_enat_coe.comp hD).aemeasurable
        (kac_mp_ae_retTime_lt_top hmp A hA)
  rw [hint]
  exact (ENNReal.toReal_mono (by simp) (kac_mp_lintegral_le_one hmp A hA)).trans_eq (by simp)

/-- **Kac's mean form, without invertibility**: under the law conditioned on `A` the mean return
time is at most `1/μ(A)`.  With `μ(A) = π(F)·P(V)` this is the paper's
`E^*D ≤ 1/(π(F)P(V))`, now for the one-sided record chain itself. -/
theorem kac_mp_cond_mean_le (hmp : MeasurePreserving f μ μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) ≤ (μ A)⁻¹ := by
  rw [lintegral_smul_measure]
  calc (μ A)⁻¹ * ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂(μ.restrict A)
      ≤ (μ A)⁻¹ * 1 := by
        gcongr
        exact kac_mp_lintegral_le_one hmp A hA
    _ = (μ A)⁻¹ := mul_one _

/-! ## The general theorem subsumes the invertible one

These two lemmas are the check that `kac_mp_tsum_le_one` and `kac_mp_lintegral_le_one` are the
*same* statement as `KacFormula.kac_tsum_le_one` / `KacFormula.kac_lintegral_le_one`
(`Swarm/KacDisjoint.lean`) on the invertible case, and not a different convention for
`noReturn` or `retTime`: they are literally the general theorem specialised to `f = e`. -/

/-- `KacFormula.kac_tsum_le_one`, recovered from the general theorem. -/
theorem kac_tsum_le_one_of_equiv (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∑' k : ℕ, μ (A ∩ KacFormula.noReturn (e : Ω → Ω) A k)) ≤ 1 :=
  kac_mp_tsum_le_one he A hA

/-- `KacFormula.kac_lintegral_le_one`, recovered from the general theorem. -/
theorem kac_lintegral_le_one_of_equiv (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫⁻ ω in A, (KacFormula.retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂μ ≤ 1 :=
  kac_mp_lintegral_le_one he A hA

/-! ## The bound is attained: no constant below `1` works

`kac_mp_tsum_le_one` is sharp as stated.  At `f = id` the tail sets vanish after the first step,
so the whole sum collapses to `μ A`; at `A = univ` that is `1`, so no constant below `1` can
bound the sum for a general measure-preserving `f`.  (`Swarm/M2KacExact.lean` records the
complementary non-degenerate case: for the one-sided Bernoulli shift the sum is exactly `1` as
well.) -/

/-- At `f = id` the Kac tails collapse: `A ∩ {D > k} = ∅` for `k ≥ 1`. -/
lemma noReturn_id_eq_empty {A : Set Ω} {k : ℕ} (hk : 1 ≤ k) :
    A ∩ KacFormula.noReturn (id : Ω → Ω) A k = ∅ := by
  ext ω
  constructor
  · rintro ⟨hA, hnr⟩
    exact (hnr 1 Nat.one_pos hk) hA
  · intro h
    exact absurd h (by simp)

/-- **The constant `1` in `kac_mp_tsum_le_one` is optimal.**  For the identity map the sum equals
`μ A` exactly, so with `A = univ` it is `1`. -/
theorem kac_tsum_id (A : Set Ω) :
    (∑' k : ℕ, μ (A ∩ KacFormula.noReturn (id : Ω → Ω) A k)) = μ A := by
  rw [tsum_eq_single 0]
  · simp only [KacFormula.noReturn_zero, inter_univ]
  · intro k hk
    rw [noReturn_id_eq_empty (A := A) (k := k) (Nat.one_le_iff_ne_zero.mpr hk), measure_empty]

end SwarmKacMP
