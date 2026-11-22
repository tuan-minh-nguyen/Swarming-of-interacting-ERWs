import SwarmDiameter.BoundedSpatial
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open LocSum LocSumAct
open scoped Topology

namespace Swarming.Diameter

set_option autoImplicit false

/-- A fixed cutoff and smooth minimum parameter make both the quadratic
error and the density of exceptional sites arbitrarily small. -/
theorem exists_linearCutoff {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m N T : ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) :
    ∃ (k : ℕ) (θ : ℝ), 1 ≤ k ∧ 0 < θ ∧ 1 ≤ (2 * p - 1) * (8 * (k : ℝ)) ∧
      θ * (8 * (k : ℝ)) ≤ 1 ∧
      θ * (8 * (k : ℝ)) ^ 2 + (N : ℝ) * Real.exp (-θ * ((k ^ 3 : ℕ) : ℝ)) ≤ ε ∧
      (4 * (N : ℝ) * (2 * ((k ^ 3 : ℕ) : ℝ) + 3)) *
        (bC p (qOf p m)) ^ k * ((2 * T + 4 : ℕ) : ℝ) ≤ δ / 2 := by
  let b := bC p (qOf p m)
  have hq₀ : 0 ≤ qOf p m := by unfold qOf; positivity
  have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hq : 0 < qOf p m := pow_pos (by linarith) _
  have hb₀ : 0 ≤ b := bC_nonneg hp₀ hp₁ hq₀ hq₁
  have hb₁ : b < 1 := bC_lt_one hp₀ hp₁ hq
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hb₀ hb₁
  have hpoly := tendsto_pow_const_mul_const_pow_of_lt_one 3 hb₀ hb₁
  let D := ((2 * T + 4 : ℕ) : ℝ)
  have ht : Tendsto (fun k : ℕ =>
      (4 * (N : ℝ) * (2 * ((k ^ 3 : ℕ) : ℝ) + 3)) * b ^ k * D) atTop (𝓝 0) := by
    have hsum := (hpoly.const_mul (8 * (N : ℝ) * D)).add (hpow.const_mul (12 * (N : ℝ) * D))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr (fun k => ?_)
    push_cast
    ring
  have het := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (show 0 < ε / 128 by positivity))).const_mul (N : ℝ)
  simp only [mul_zero] at het
  have htail : ∀ᶠ k : ℕ in atTop, (N : ℝ) * Real.exp (-(ε / 128 * (k : ℝ))) ≤ ε / 2 := by
    apply Eventually.mono (tendsto_order.1 het |>.2 (ε / 2) (half_pos hε))
    intro k hk
    simpa only [Function.comp_apply, mul_zero] using hk.le
  have hμ : 0 < 2 * p - 1 := by linarith
  have hlarge : ∀ᶠ k : ℕ in atTop, 1 / (8 * (2 * p - 1)) ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hall : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧
      1 / (8 * (2 * p - 1)) ≤ (k : ℝ) ∧
      (N : ℝ) * Real.exp (-(ε / 128 * (k : ℝ))) ≤ ε / 2 ∧
      (4 * (N : ℝ) * (2 * ((k ^ 3 : ℕ) : ℝ) + 3)) * b ^ k * D ≤ δ / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge, htail,
      (tendsto_order.1 ht).2 (δ / 2) (half_pos hδ)] with k hk hkl hke hkt
    exact ⟨hk, hkl, hke, hkt.le⟩
  obtain ⟨k, hk, hkl, hke, hkt⟩ := hall.exists
  let K : ℝ := 8 * (k : ℝ)
  let θ := ε / (2 * K ^ 2)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hk']
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθK : θ * K ^ 2 = ε / 2 := by dsimp only [θ]; field_simp
  have harg : -θ * ((k ^ 3 : ℕ) : ℝ) = -(ε / 128 * (k : ℝ)) := by
    dsimp only [θ, K]
    push_cast
    field_simp
    ring
  refine ⟨k, θ, hk, hθ, ?_, ?_, ?_, hkt⟩
  · have h := (div_le_iff₀ (by positivity : 0 < 8 * (2 * p - 1))).mp hkl
    nlinarith only [h]
  · change θ * K ≤ 1
    have h := mul_le_mul_of_nonneg_left hK (mul_nonneg hθ.le hK₀.le)
    nlinarith only [h, hθK, hε₁]
  · change θ * K ^ 2 + (N : ℝ) * Real.exp (-θ * ((k ^ 3 : ℕ) : ℝ)) ≤ ε
    rw [harg, hθK]
    linarith only [hke]

end Swarming.Diameter
