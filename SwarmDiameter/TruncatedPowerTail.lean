import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Positivity

open Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

private theorem exp_le_one_add_mul_exp (x : ℝ) : Real.exp x ≤ 1 + x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, add_mul, neg_mul, one_mul] at h
  linarith

/-- For independent nonnegative variables, truncation at `t` bounds the upper
tail of the sum of powers. The exponentially weighted moment bounds the
truncated part. A finite union bounds the event that a variable exceeds `t`. -/
theorem sum_pow_tail_le_of_exponential_moment
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (s : Finset ι) (q : ℕ)
    {δ K t : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (ht : 0 < t)
    (hmom : ∀ i ∈ s, (∫⁻ ω, ENNReal.ofReal ((X i ω) ^ (q + 1) * Real.exp (δ * X i ω)) ∂μ) ≤
      ENNReal.ofReal K) :
    μ.real {ω | K * (s.card : ℝ) + t ^ (q + 1) < ∑ i ∈ s, (X i ω) ^ (q + 1)} ≤
      Real.exp (-δ * t) + ∑ i ∈ s, μ.real {ω | t < X i ω} := by
  classical
  let _ : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  let θ := δ / t ^ q
  have hθ : 0 < θ := div_pos hδ (pow_pos ht _)
  let f (z : ℝ) : ℝ := if z ≤ t then z ^ (q + 1) else 0
  let g (z : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * f z))
  let Y (i : ι) (ω : Ω) := g (X i ω)
  have hf : Measurable f :=
    Measurable.ite measurableSet_Iic (measurable_id.pow_const _) measurable_const
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hf.const_mul θ))
  have hY (i : ι) : Measurable (Y i) := hg.comp (hmeas i)
  have hin (i : ι) (hi : i ∈ s) : (∫⁻ ω, Y i ω ∂μ) ≤ ENNReal.ofReal (Real.exp (θ * K)) := by
    let G (ω : Ω) := ENNReal.ofReal ((X i ω) ^ (q + 1) * Real.exp (δ * X i ω))
    have hG : Measurable G := ENNReal.measurable_ofReal.comp
      (((hmeas i).pow_const _).mul (Real.measurable_exp.comp ((hmeas i).const_mul δ)))
    have hle (ω : Ω) : Y i ω ≤ 1 + ENNReal.ofReal θ * G ω := by
      have hz := hnonneg i ω
      have hh : θ * f (X i ω) ≤ δ * X i ω := by
        by_cases h : X i ω ≤ t
        · simp only [f, if_pos h, pow_succ]
          dsimp only [θ]
          rw [← mul_assoc, div_mul_eq_mul_div]
          apply mul_le_mul_of_nonneg_right _ hz
          rw [div_le_iff₀ (pow_pos ht _)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz h _) hδ.le
        · simp only [f, if_neg h, mul_zero]
          exact mul_nonneg hδ.le hz
      have hfg : 0 ≤ f (X i ω) ∧ f (X i ω) ≤ (X i ω) ^ (q + 1) := by
        by_cases h : X i ω ≤ t <;> simp [f, h, pow_nonneg hz]
      have hmul : (θ * f (X i ω)) * Real.exp (θ * f (X i ω)) ≤
          θ * ((X i ω) ^ (q + 1) * Real.exp (δ * X i ω)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hfg.2 (Real.exp_le_exp.mpr hh) (Real.exp_pos _).le (pow_nonneg hz _)) hθ.le
      change ENNReal.ofReal (Real.exp (θ * f (X i ω))) ≤ _
      rw [← ENNReal.ofReal_mul hθ.le, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one
          (mul_nonneg hθ.le (mul_nonneg (pow_nonneg hz _) (Real.exp_pos _).le))]
      exact ENNReal.ofReal_le_ofReal ((exp_le_one_add_mul_exp _).trans (add_le_add_right hmul _))
    calc
      _ ≤ ∫⁻ ω, 1 + ENNReal.ofReal θ * G ω ∂μ := lintegral_mono hle
      _ = 1 + ENNReal.ofReal θ * ∫⁻ ω, G ω ∂μ := by
        rw [lintegral_add_left measurable_const (fun ω => ENNReal.ofReal θ * G ω),
          lintegral_const_mul _ hG]
        simp
      _ ≤ 1 + ENNReal.ofReal θ * ENNReal.ofReal K := by
        gcongr
        exact hmom i hi
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hθ.le, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (mul_nonneg hθ.le hK)]
        exact ENNReal.ofReal_le_ofReal (by simpa only [add_comm] using Real.add_one_le_exp (θ * K))
  let Z (ω : Ω) : ℝ≥0∞ := ∏ i ∈ s, Y i ω
  have hZ : Measurable Z := s.measurable_prod (fun i _ => hY i)
  have hZmean : (∫⁻ ω, Z ω ∂μ) ≤ ENNReal.ofReal (Real.exp (θ * (K * (s.card : ℝ)))) := by
    change (∫⁻ ω, ∏ i ∈ s, Y i ω ∂μ) ≤ _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun s Y
      (hX.comp (fun _ => g) (fun _ => hg)) hY]
    calc
      _ ≤ ∏ _ ∈ s, ENNReal.ofReal (Real.exp (θ * K)) := Finset.prod_le_prod' hin
      _ = _ := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
        simp [mul_assoc, mul_left_comm, mul_comm]
  let a := ENNReal.ofReal (Real.exp (θ * (K * (s.card : ℝ) + t ^ (q + 1))))
  have ha₀ : a ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have ha₁ : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hmarkov : μ.real {ω | a ≤ Z ω} ≤ Real.exp (-δ * t) := by
    have h := (meas_ge_le_lintegral_div (μ := μ) hZ.aemeasurable ha₀ ha₁).trans
      (ENNReal.div_le_div_right hZmean a)
    have he : ENNReal.ofReal (Real.exp (θ * (K * (s.card : ℝ)))) / a =
        ENNReal.ofReal (Real.exp (-δ * t)) := by
      dsimp only [a]
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      have htθ : θ * t ^ (q + 1) = δ * t := by
        dsimp only [θ]
        rw [pow_succ, ← mul_assoc, div_mul_cancel₀ _ (pow_pos ht _).ne']
      linarith [htθ]
    rw [he] at h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  have hcover : {ω | K * (s.card : ℝ) + t ^ (q + 1) < ∑ i ∈ s, (X i ω) ^ (q + 1)} ⊆
      {ω | a ≤ Z ω} ∪ ⋃ i ∈ s, {ω | t < X i ω} := by
    intro ω hω
    by_cases h : ∀ i ∈ s, X i ω ≤ t
    · left
      have he : Z ω = ENNReal.ofReal (Real.exp (θ * ∑ i ∈ s, (X i ω) ^ (q + 1))) := by
        dsimp only [Z, Y, g]
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum, mul_sum]
        congr 2
        exact sum_congr rfl fun i hi => by simp only [f, if_pos (h i hi)]
      change a ≤ Z ω
      rw [he]
      exact ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hω) hθ.le))
    · push Not at h
      obtain ⟨i, hi, hx⟩ := h
      exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩)
  calc
    _ ≤ μ.real ({ω | a ≤ Z ω} ∪ ⋃ i ∈ s, {ω | t < X i ω}) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ _ := (measureReal_union_le _ _).trans
      (add_le_add hmarkov (measureReal_biUnion_finset_le s _))

end Swarming.Diameter
