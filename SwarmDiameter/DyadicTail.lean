import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- A tail tending to zero and satisfying a dyadic recurrence has the
stretched-exponential bound of the error in that recurrence. -/
theorem le_stretchedExp_of_dyadic_tail {A : ℕ → ℝ} {L₀ : ℕ}
    {K c γ : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hγ : 0 < γ)
    (hzero : Tendsto A atTop (𝓝 0))
    (hstep : ∀ L ≥ L₀, A L ≤ A (2 * L) + K * Real.exp (-c * (L : ℝ) ^ γ))
    {L : ℕ} (hL₀ : L₀ ≤ L) (hL : 1 ≤ L) :
    A L ≤ K / (1 - Real.exp (-c * ((2 : ℝ) ^ γ - 1))) * Real.exp (-c * (L : ℝ) ^ γ) := by
  let b : ℝ := (2 : ℝ) ^ γ - 1
  have hb : 0 < b := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hγ)
  let q := Real.exp (-c * b)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  let M := K / (1 - q)
  have hM : 0 ≤ M := div_nonneg hK (sub_pos.mpr hq).le
  have hMq : M * (1 - q) = K := div_mul_cancel₀ _ (sub_pos.mpr hq).ne'
  let g (n : ℕ) := M * Real.exp (-c * (n : ℝ) ^ γ)
  have hcomp (n : ℕ) (hn : 1 ≤ n) :
      Real.exp (-c * (↑(2 * n) : ℝ) ^ γ) ≤ q * Real.exp (-c * (n : ℝ) ^ γ) := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : 1 ≤ (n : ℝ) ^ γ := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hn' hγ.le
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (by positivity)]
    dsimp only [q]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h₁ : b ≤ b * (n : ℝ) ^ γ := le_mul_of_one_le_right hb.le hpow
    have h₂ := mul_le_mul_of_nonneg_left h₁ hc.le
    dsimp only [b] at h₂
    nlinarith
  have hmono (n : ℕ) (hn₀ : L₀ ≤ n) (hn : 1 ≤ n) : A n - g n ≤ A (2 * n) - g (2 * n) := by
    have hge := mul_le_mul_of_nonneg_left (hcomp n hn) hM
    have he : K + M * q = M := by linarith only [hMq]
    have hcost : K * Real.exp (-c * (n : ℝ) ^ γ) + g (2 * n) ≤ g n := by
      calc
        _ ≤ K * Real.exp (-c * (n : ℝ) ^ γ) + M * (q * Real.exp (-c * (n : ℝ) ^ γ)) :=
          add_le_add_right hge _
        _ = g n := by rw [← mul_assoc, ← add_mul, he]
    linarith [hstep n hn₀]
  let l (j : ℕ) := 2 ^ j * L
  have hl (j : ℕ) : L ≤ l j := by
    have hpow : 1 ≤ (2 : ℕ) ^ j := pow_pos (by decide : (0 : ℕ) < 2) j
    simpa only [l, one_mul] using Nat.mul_le_mul_right L hpow
  have hcumul (j : ℕ) : A L - g L ≤ A (l j) - g (l j) := by
    induction j with
    | zero => simp [l]
    | succ j ih =>
      have he : l (j + 1) = 2 * l j := by dsimp only [l]; rw [pow_succ']; exact mul_assoc _ _ _
      rw [he]
      exact ih.trans (hmono _ (hL₀.trans (hl j)) (hL.trans (hl j)))
  have hlTop : Tendsto l atTop atTop := by
    apply tendsto_atTop_mono (f := fun j : ℕ => (2 : ℕ) ^ j)
    · intro j
      simpa only [l, mul_one] using Nat.mul_le_mul_left (2 ^ j) hL
    · exact tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)
  have hg : Tendsto g atTop (𝓝 0) := by
    have hne : Tendsto (fun n : ℕ => -c * (n : ℝ) ^ γ) atTop atBot :=
      ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (neg_neg_of_pos hc)
    simpa only [g, mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp hne).const_mul M
  have ht : Tendsto (fun j => A (l j) - g (l j)) atTop (𝓝 0) := by
    simpa only [sub_zero, Function.comp_apply] using (hzero.comp hlTop).sub (hg.comp hlTop)
  have ha : A L - g L ≤ 0 := ge_of_tendsto' ht hcumul
  exact sub_nonpos.mp ha

end Swarming.Diameter
