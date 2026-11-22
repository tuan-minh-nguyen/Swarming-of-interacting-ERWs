import SwarmDiameter.RecordOccupationBound
import SwarmDiameter.TailBounds
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart RawStrictTransport
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem summable_exp_neg_cube_root {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ (1 / 3 : ℝ))) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (-6)).comp_tendsto
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h₁ : (fun n : ℕ => ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (-6 : ℝ)) = fun n : ℕ => (n : ℝ) ^ (-2 : ℝ) := by
    funext n
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
  rw [← h₁]
  exact h.isBigO

private theorem tsum_exp_neg_cube_root_add_le {c : ℝ} (hc : 0 < c) (u : ℕ) :
    (∑' v : ℕ, ENNReal.ofReal (Real.exp (-c * ((u + v : ℕ) : ℝ) ^ (1 / 3 : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(c / 2) * (u : ℝ) ^ (1 / 3 : ℝ))) *
        ∑' v : ℕ, ENNReal.ofReal (Real.exp (-(c / 2) * (v : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro v
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h₁ : (u : ℝ) ^ (1 / 3 : ℝ) ≤ ((u + v : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_add_right u v) (by norm_num)
  have h₂ : (v : ℝ) ^ (1 / 3 : ℝ) ≤ ((u + v : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_add_left v u) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left h₁ hc.le, mul_le_mul_of_nonneg_left h₂ hc.le]

private theorem eventually_polynomial_mul_exp_le {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    {β : ℕ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      (⌈x ^ (3 : ℕ)⌉₊ : ℝ) * (K * Real.exp (-a * x ^ (1 / (β : ℝ)))) ≤
        Real.exp (-(a / 2) * x ^ (1 / (β : ℝ))) := by
  let t (x : ℝ) := x ^ (1 / (β : ℝ))
  have hb : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have htop : Tendsto t atTop atTop := tendsto_rpow_atTop (one_div_pos.mpr hb)
  have h := ((isLittleO_exp_mul_rpow_of_lt (3 * (β : ℝ))
    (show -a < -(a / 2) by linarith)).const_mul_left (2 * K)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [htop.eventually h, eventually_ge_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 ≤ x := zero_le_one.trans hx₁
  have hxp : 1 ≤ x ^ (3 : ℕ) := one_le_pow₀ hx₁
  have hceil : (⌈x ^ (3 : ℕ)⌉₊ : ℝ) ≤ 2 * x ^ (3 : ℕ) := by
    linarith [Nat.ceil_lt_add_one (pow_nonneg hx₀ 3)]
  have hpower : t x ^ (3 * (β : ℝ)) = x ^ (3 : ℕ) := by
    dsimp only [t]
    rw [← Real.rpow_mul hx₀]
    have he : 1 / (β : ℝ) * (3 * (β : ℝ)) = 3 := by field_simp
    rw [he]
    norm_cast
  calc
    _ ≤ (2 * x ^ (3 : ℕ)) * (K * Real.exp (-a * t x)) :=
      mul_le_mul_of_nonneg_right hceil (mul_nonneg hK (Real.exp_pos _).le)
    _ = 2 * K * (Real.exp (-a * t x) * t x ^ (3 * (β : ℝ))) := by rw [hpower]; ring
    _ ≤ _ := by
      change ‖2 * K * (Real.exp (-a * t x) * t x ^ (3 * (β : ℝ)))‖ ≤
        1 * ‖Real.exp (-(a / 2) * t x)‖ at hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_pos (Real.exp_pos _), one_mul] at hx
      exact hx

/-- Upper bounds for the exceedance and duration of a record interval suffice
for a stretched exponential bound on the expected first-regeneration visit count.
The duration may have the cube-root exponent in every regime. -/
theorem eventually_regeneration_occupation_le_of_record_tails
    {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {β : ℕ} (hβ : 0 < β) {a d K H : ℝ} (ha : 0 < a) (hd : 0 < d) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hE : let X := posPath (N := N) p m
      ∀ᶠ x : ℝ in atTop, limsup
        (fun r => (arrayMeasure N).real {U | recordIntervalExceeds (X U) r x}) atTop ≤
          K * Real.exp (-a * x ^ (1 / (β : ℝ))))
    (hW : let X := posPath (N := N) p m
      ∀ᶠ u : ℕ in atTop, limsup
        (fun r => (arrayMeasure N).real {U | (u : ℕ∞) < recordDuration (X U) r}) atTop ≤
          H * Real.exp (-d * (u : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      (∑' t : ℕ, (SwarmFB.seedCond (p := p) (m := m) (N := N)).real
        {U | t < firstTime p m U ∧ x ≤ pathDiameter t (posPath p m U)}) ≤
        Real.exp (-c * x ^ (1 / (β : ℝ))) := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure
    (SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN)
  let X := posPath (N := N) p m
  let b := ∫⁻ U, (firstLevel p m U : ℝ≥0∞) ∂μstar
  let S := ∑' v : ℕ, ENNReal.ofReal (Real.exp (-(d / 2) * (v : ℝ) ^ (1 / 3 : ℝ)))
  have hS : S ≠ ∞ := (summable_exp_neg_cube_root (half_pos hd)).tsum_ofReal_ne_top
  have hb : b ≠ ∞ := (tendsto_record_duration_tail_occupation (N := N) hp₀ hp₁ hm hN 0).2.1
  let κ := min a d / 2
  have hκ : 0 < κ := half_pos (lt_min ha hd)
  have hκa : κ ≤ a / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκd : κ ≤ d / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let c := κ / 2
  refine ⟨c, half_pos hκ, ?_⟩
  let u (x : ℝ) : ℕ := ⌈x ^ (3 : ℕ)⌉₊
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp hW
  have huTop : Tendsto u atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (max (j : ℝ) 1)] with x hx
    have h₁ : (1 : ℝ) ≤ x := (le_max_right _ _).trans hx
    have hxpow : x ≤ x ^ (3 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ h₁ (by norm_num : (1 : ℕ) ≤ 3)
    have h : (j : ℝ) ≤ (u x : ℝ) := (le_max_left _ _).trans
      (hx.trans (hxpow.trans (Nat.le_ceil _)))
    exact_mod_cast h
  let B := b.toReal * (1 + H * S.toReal)
  let R (x : ℝ) := x ^ (1 / (β : ℝ))
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hrtop : Tendsto R atTop atTop := tendsto_rpow_atTop (one_div_pos.mpr hβ')
  have hlarge : ∀ᶠ x : ℝ in atTop, B ≤ Real.exp (c * R x) :=
    (Real.tendsto_exp_atTop.comp (hrtop.const_mul_atTop (half_pos hκ))).eventually_ge_atTop B
  filter_upwards [hE, (huTop.eventually (eventually_ge_atTop u₀)),
    eventually_ge_atTop (1 : ℝ), eventually_polynomial_mul_exp_le ha hK hβ, hlarge]
      with x hx hux hx₁ hpoly hxlarge
  let P := Real.exp (-κ * R x)
  have hR₀ : 0 ≤ R x := Real.rpow_nonneg (zero_le_one.trans hx₁) _
  have hP₁ : Real.exp (-(a / 2) * R x) ≤ P := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hκa hR₀]
  have hP₂ : Real.exp (-(d / 2) * (u x : ℝ) ^ (1 / 3 : ℝ)) ≤ P := by
    have hrx : R x ≤ x := by
      have hβone : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ
      have hexp : 1 / (β : ℝ) ≤ 1 := (div_le_iff₀ hβ').mpr (by simpa using hβone)
      simpa only [R, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx₁ hexp
    have hxle : x ≤ (u x : ℝ) ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (pow_nonneg (zero_le_one.trans hx₁) 3)
        (Nat.le_ceil (x ^ (3 : ℕ))) (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx₁)] at h
      norm_num at h
      exact h
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hκd hR₀,
      mul_le_mul_of_nonneg_left (hrx.trans hxle) (half_pos hd).le]
  have hA : ((u x : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (limsup (fun r => (arrayMeasure N).real {U | recordIntervalExceeds (X U) r x}) atTop) ≤
        ENNReal.ofReal P := by
    calc
      _ ≤ (u x : ℝ≥0∞) * ENNReal.ofReal (K * Real.exp (-a * R x)) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hx) zero_le
      _ = ENNReal.ofReal ((u x : ℝ) * (K * Real.exp (-a * R x))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hpoly.trans hP₁)
  have htail : (∑' v : ℕ, ENNReal.ofReal (limsup
      (fun r => (arrayMeasure N).real {U | ((u x + v : ℕ) : ℕ∞) < recordDuration (X U) r}) atTop)) ≤
        ENNReal.ofReal H * (ENNReal.ofReal P * S) := by
    calc
      _ ≤ ∑' v : ℕ, ENNReal.ofReal (H * Real.exp (-d * ((u x + v : ℕ) : ℝ) ^ (1 / 3 : ℝ))) :=
        ENNReal.tsum_le_tsum (fun v => ENNReal.ofReal_le_ofReal (hu₀ _ (by omega)))
      _ = ENNReal.ofReal H * ∑' v : ℕ,
          ENNReal.ofReal (Real.exp (-d * ((u x + v : ℕ) : ℝ) ^ (1 / 3 : ℝ))) := by
        simp_rw [ENNReal.ofReal_mul hH, ENNReal.tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((tsum_exp_neg_cube_root_add_le hd (u x)).trans
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hP₂) zero_le)) zero_le
  have hbound := (first_regeneration_diameter_occupation_le_record_limsup
    (N := N) hp₀ hp₁ hm hN x (u x)).trans
      (mul_le_mul_of_nonneg_left (add_le_add hA htail) (show 0 ≤ b from zero_le))
  have hfinite : b * (ENNReal.ofReal P + ENNReal.ofReal H * (ENNReal.ofReal P * S)) ≠ ∞ :=
    ENNReal.mul_ne_top hb (ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)⟩)
  have hreal := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.tsum_toReal_eq (fun _ => measure_ne_top μstar _), ENNReal.toReal_mul,
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hH,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  refine hreal.trans ?_
  calc
    _ = B * P := by dsimp only [B]; ring
    _ ≤ Real.exp (c * R x) * P := mul_le_mul_of_nonneg_right hxlarge (Real.exp_pos _).le
    _ = _ := by
      dsimp only [P]
      rw [← Real.exp_add]
      congr 1
      dsimp only [c]
      ring

end Swarming.Diameter
