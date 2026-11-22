import Mathlib.Analysis.SpecificLimits.Normed
import SwarmDiameter.TruncatedPowerTail

open Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

/-- A finite family of independent geometric gap lengths has a stretched
exponential upper bound for the sum of its powers. The geometric measure
counts failures and the gap lengths include the final success. -/
theorem exists_geometric_gap_sum_pow_tail (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (q : ℕ) :
    ∃ ν : Measure ℕ, IsProbabilityMeasure ν ∧
      (∀ k : ℕ, ν {k} = ENNReal.ofReal (1 - p) ^ k * ENNReal.ofReal p) ∧
      ∃ δ K C : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 < C ∧ ∀ (L : ℕ) (t : ℝ), 0 < t →
        (Measure.pi (fun _ : Fin L => ν)).real
          {g | K * L + t ^ (q + 1) < ∑ i : Fin L, ((g i : ℝ) + 1) ^ (q + 1)}
          ≤ C * ((L : ℝ) + 1) * Real.exp (-δ * t) := by
  let ρ : ℝ := 1 - p
  have hρ₀ : 0 < ρ := sub_pos.mpr hp₁
  have hρ₁ : ρ < 1 := by dsimp [ρ]; linarith
  let ν : Measure ℕ := Measure.sum fun n : ℕ => ENNReal.ofReal (ρ ^ n * p) • Measure.dirac n
  have hsum : HasSum (fun n : ℕ => ρ ^ n * p) 1 := by
    have h := (hasSum_geometric_of_lt_one hρ₀.le hρ₁).mul_right p
    have he : 1 - ρ = p := by dsimp [ρ]; ring
    rwa [he, inv_mul_cancel₀ hp₀.ne'] at h
  let hν : IsProbabilityMeasure ν := hsum.isProbabilityMeasure_sum_dirac
    (fun n => mul_nonneg (pow_nonneg hρ₀.le n) hp₀.le)
  have hsingle (n : ℕ) : ν {n} = ENNReal.ofReal (ρ ^ n * p) :=
    Measure.sum_smul_dirac_singleton
  refine ⟨ν, hν, fun n => ?_, ?_⟩
  · rw [hsingle, ENNReal.ofReal_mul (pow_nonneg hρ₀.le _), ENNReal.ofReal_pow hρ₀.le]
  · let δ := -Real.log ρ / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith [Real.log_neg hρ₀ hρ₁]
    let a := ρ * Real.exp δ
    have ha₀ : 0 < a := mul_pos hρ₀ (Real.exp_pos _)
    have ha₁ : a < 1 := by
      dsimp only [a, δ]
      conv_lhs => rw [← Real.exp_log hρ₀]
      rw [Real.log_exp, ← Real.exp_add]
      apply Real.exp_lt_one_iff.mpr
      linarith [Real.log_neg hρ₀ hρ₁]
    have hb (k : ℕ) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * a ^ n) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_eq_abs, abs_of_pos ha₀])
      have h' := (summable_nat_add_iff 1).mpr h
      have hh := h'.mul_right a⁻¹
      have he : (fun n : ℕ => (↑(n + 1) : ℝ) ^ k * a ^ (n + 1) * a⁻¹) =
          (fun n : ℕ => ((n : ℝ) + 1) ^ k * a ^ n) := by
        funext n
        rw [Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc, mul_assoc, mul_inv_cancel₀ ha₀.ne', mul_one]
      rwa [he] at hh
    have hf (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
        (∫⁻ z : ℕ, ENNReal.ofReal (((z : ℝ) + 1) ^ k * Real.exp (δ * ((z : ℝ) + 1)))
          ∂(ν)) ≤ ENNReal.ofReal M := by
      let F (z : ℕ) := ((z : ℝ) + 1) ^ k * a ^ z * (Real.exp δ * p)
      have hF (z : ℕ) : 0 ≤ F z := by
        dsimp [F]
        positivity
      have hsum : Summable F := (hb k).mul_right _
      have he (z : ℕ) : ENNReal.ofReal (((z : ℝ) + 1) ^ k * Real.exp (δ * ((z : ℝ) + 1))) *
          ν {z} = ENNReal.ofReal (F z) := by
        rw [hsingle, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold F a
        rw [mul_add, mul_one, Real.exp_add, mul_comm δ (z : ℝ), Real.exp_nat_mul, mul_pow]
        ring
      refine ⟨∑' z, F z, tsum_nonneg hF, ?_⟩
      rw [lintegral_countable', tsum_congr he, ENNReal.ofReal_tsum_of_nonneg hF hsum]
    obtain ⟨K, hK, hmoment⟩ := hf (q + 1)
    obtain ⟨M, hM, hmean⟩ := hf 0
    simp only [pow_zero, one_mul] at hmean
    refine ⟨δ, K, max 1 M, hδ, hK, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
    intro L t ht
    let μ := Measure.pi (fun _ : Fin L => ν)
    let X (i : Fin L) (g : Fin L → ℕ) := (g i : ℝ) + 1
    have hind : iIndepFun X μ := by
      exact iIndepFun_pi (fun _ => (measurable_of_countable (fun n : ℕ => (n : ℝ) + 1)).aemeasurable)
    have hXm (i : Fin L) : Measurable (X i) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ) + 1)).comp (measurable_pi_apply i)
    have heval (i : Fin L) : μ.map (fun g : Fin L → ℕ => g i) = ν :=
      (measurePreserving_eval (fun _ : Fin L => ν) i).map_eq
    have hcomp (i : Fin L) (f : ℕ → ℝ≥0∞) :
        (∫⁻ g, f (g i) ∂μ) = ∫⁻ z, f z ∂(ν) := by
      rw [← lintegral_map (measurable_of_countable f) (measurable_pi_apply i), heval]
    have hmain := sum_pow_tail_le_of_exponential_moment hind hXm
      (fun (_ : Fin L) (g : Fin L → ℕ) => by dsimp [X]; positivity)
      univ q hδ hK ht (fun i _ =>
        (hcomp i (fun z => ENNReal.ofReal (((z : ℝ) + 1) ^ (q + 1) *
          Real.exp (δ * ((z : ℝ) + 1))))).trans_le hmoment)
    have htail (i : Fin L) : μ.real {g | t < X i g} ≤ M * Real.exp (-δ * t) := by
      let W (g : Fin L → ℕ) := ENNReal.ofReal (Real.exp (δ * X i g))
      let u := ENNReal.ofReal (Real.exp (δ * t))
      have hW : Measurable W := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hXm i).const_mul δ))
      have hsub : {g | t < X i g} ⊆ {g | u ≤ W g} := fun g hg =>
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hg) hδ.le))
      have h := (meas_ge_le_lintegral_div (μ := μ) hW.aemeasurable
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top).trans
          (ENNReal.div_le_div_right ((hcomp i _).trans_le hmean) u)
      have hh : ENNReal.ofReal M / u = ENNReal.ofReal (M * Real.exp (-δ * t)) := by
        dsimp only [u]
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), neg_mul, Real.exp_neg, div_eq_mul_inv]
      rw [hh] at h
      calc
        _ ≤ μ.real {g | u ≤ W g} := measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ _ := (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
          (ENNReal.toReal_ofReal (by positivity))
    have hsum := sum_le_sum (s := (univ : Finset (Fin L))) (fun i _ => htail i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    simp only [card_univ, Fintype.card_fin] at hmain
    refine hmain.trans (add_le_add_right hsum _ |>.trans ?_)
    have hM₁ : M ≤ max 1 M := le_max_right _ _
    have h1 : 1 ≤ max 1 M := le_max_left _ _
    have hh : 1 + (L : ℝ) * M ≤ max 1 M * ((L : ℝ) + 1) := by
      rw [mul_add, mul_one, mul_comm (max 1 M) (L : ℝ)]
      calc
        _ = (L : ℝ) * M + 1 := add_comm _ _
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hM₁ (Nat.cast_nonneg _)) h1
    calc
      _ = (1 + (L : ℝ) * M) * Real.exp (-δ * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end Swarming.Diameter
