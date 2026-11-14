/-
  **The missing sub-σ-algebra bridge** used to pass from "all set integrals over `m`-sets are
  ordered" to the almost-everywhere ordering of the conditional expectation.  Mathlib has the
  ambient-σ-algebra version (`MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`) but not
  the version for a sub-σ-algebra `m ≤ m0`, which is what a conditional statement needs.
-/
import Swarm.Imports

open MeasureTheory Filter

namespace SwarmSpeed

/-- A function measurable for a sub-σ-algebra `m` whose integrals over every `m`-measurable set
are nonnegative is nonnegative almost everywhere. -/
theorem ae_nonneg_of_forall_setIntegral_nonneg_sub {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {h : Ω → ℝ} (hint : Integrable h μ) (hmeas : Measurable[m] h)
    (hint' : ∀ s : Set Ω, MeasurableSet[m] s → 0 ≤ ∫ x in s, h x ∂μ) :
    0 ≤ᵐ[μ] h := by
  classical
  change ∀ᵐ ω ∂μ, 0 ≤ h ω
  rw [ae_iff]
  by_contra hcon
  have hset : {ω : Ω | ¬ (0 : ℝ) ≤ h ω} = {ω | h ω < 0} := by
    ext ω; exact not_le
  rw [hset] at hcon
  have hNne : μ {ω | h ω < 0} ≠ 0 := hcon
  have hcov : {ω | h ω < 0} = ⋃ k : ℕ, {ω | h ω < -(1 / ((k : ℝ) + 1))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hω
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -h ω by linarith)
      exact ⟨k, by push_cast at hk ⊢; linarith⟩
    · rintro ⟨k, hk⟩
      have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hex : ∃ k : ℕ, μ {ω | h ω < -(1 / ((k : ℝ) + 1))} ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hNne ?_
    rw [hcov]
    exact measure_iUnion_null hall
  obtain ⟨k, hk⟩ := hex
  set s : Set Ω := {ω | h ω < -(1 / ((k : ℝ) + 1))} with hs
  have hsm : MeasurableSet[m] s := hmeas measurableSet_Iio
  have hpos : 0 < μ.real s := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hk (measure_ne_top μ s)
  have hcpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hle : ∫ x in s, h x ∂μ ≤ -(1 / ((k : ℝ) + 1)) * μ.real s := by
    have h1 : ∫ x in s, (fun _ => -(1 / ((k : ℝ) + 1))) x ∂μ
        = -(1 / ((k : ℝ) + 1)) * μ.real s := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    rw [← h1]
    refine integral_mono_ae hint.integrableOn (integrable_const _) ?_
    change ∀ᵐ x ∂(μ.restrict s), h x ≤ -(1 / ((k : ℝ) + 1))
    rw [ae_restrict_iff' (hm s hsm)]
    filter_upwards with ω hω using le_of_lt hω
  have hzero := hint' s hsm
  have hneg : -(1 / ((k : ℝ) + 1)) * μ.real s < 0 := by
    have hpp : 0 < (1 / ((k : ℝ) + 1)) * μ.real s := mul_pos hcpos hpos
    nlinarith [hpp]
  linarith [hle, hzero, hneg]

/-- If all `m`-set integrals of `f` are dominated by those of the `m`-measurable `g`, then
`μ[f | m] ≤ᵐ g`. -/
theorem condExp_le_of_forall_setIntegral_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hgm : Measurable[m] g)
    (h : ∀ s : Set Ω, MeasurableSet[m] s → ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ) :
    μ[f | m] ≤ᵐ[μ] g := by
  have hdiff : Integrable (fun ω => g ω - (μ[f | m]) ω) μ := hg.sub integrable_condExp
  have hdiffmeas : Measurable[m] (fun ω => g ω - (μ[f | m]) ω) :=
    hgm.sub stronglyMeasurable_condExp.measurable
  have hnn : ∀ s : Set Ω, MeasurableSet[m] s →
      0 ≤ ∫ x in s, (g x - (μ[f | m]) x) ∂μ := by
    intro s hs
    have h1 : ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ :=
      setIntegral_condExp hm hf hs
    have h2 : ∫ x in s, (g x - (μ[f | m]) x) ∂μ
        = ∫ x in s, g x ∂μ - ∫ x in s, (μ[f | m]) x ∂μ := by
      have h3 := integral_sub (μ := μ.restrict s) (f := g) (g := fun x => (μ[f | m]) x)
        hg.integrableOn integrable_condExp.integrableOn
      simpa using h3
    rw [h2, h1]
    linarith [h s hs]
  have hnn' := ae_nonneg_of_forall_setIntegral_nonneg_sub hm hdiff hdiffmeas hnn
  change ∀ᵐ ω ∂μ, (μ[f | m]) ω ≤ g ω
  filter_upwards [hnn'] with ω hω
  simp only [Pi.zero_apply] at hω
  linarith

end SwarmSpeed
