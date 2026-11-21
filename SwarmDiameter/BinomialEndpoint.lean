import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace Swarming.Diameter

/-- A lower bound on the symmetric-walk endpoint mass at displacement `L²`
after `L³` steps, expressed in terms of its binomial coefficient. -/
theorem exp_neg_le_binomial_mass_mul {L : ℕ} (hL : 8 ≤ L) :
    Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ (L ^ 3) ≤
      ((L : ℝ) ^ 3 + 1) * (((L ^ 3).choose ((L ^ 3 + L ^ 2) / 2) : ℕ) : ℝ) := by
  let n := L ^ 3
  let d := L ^ 2
  let q : ℝ := 1 - 4 / (L : ℝ)
  have hLr : (8 : ℝ) ≤ L := by exact_mod_cast hL
  have hℓ : (0 : ℝ) < L := by linarith
  have hq : (1 / 2 : ℝ) ≤ q := by
    change 1 / 2 ≤ 1 - 4 / (L : ℝ)
    have hh := (div_le_iff₀ hℓ).mpr (show (4 : ℝ) ≤ (1 / 2) * L by linarith)
    linarith
  have hq₀ : 0 < q := by linarith
  have hd : d ≤ n := by
    dsimp only [n, d]
    exact pow_le_pow_right₀ (by omega : 1 ≤ L) (by decide : 2 ≤ 3)
  have hd₁ : 1 ≤ d := by
    change 1 ≤ L ^ 2
    exact Nat.succ_le_of_lt (pow_pos (by omega : 0 < L) _)
  let k := n / 2
  let r := (n + d) / 2 - k
  have hkr : k + r = (n + d) / 2 := by
    dsimp only [k, r]
    omega
  have hr : r ≤ d := by
    dsimp only [k, r]
    omega
  have hstep (i : ℕ) (hi : i < r) :
      q * (n.choose (k + i) : ℝ) ≤ n.choose (k + i + 1) := by
    let j := k + i
    have hj : j + 1 ≤ (n + d) / 2 := by
      change k + i + 1 ≤ (n + d) / 2
      omega
    have hjn : j ≤ n := by omega
    have hj₁ : n ≤ 2 * (j + 1) := by
      dsimp only [j, k]
      omega
    have hj₂ : 2 * j + 1 ≤ n + d + 1 := by omega
    have hdu : ((d : ℝ) + 1) * L ≤ 2 * (n : ℝ) := by
      have hd₂ : (1 : ℝ) ≤ d := by exact_mod_cast hd₁
      calc
        _ ≤ (2 * (d : ℝ)) * L := mul_le_mul_of_nonneg_right (by linarith) hℓ.le
        _ = _ := by simp only [d, n, Nat.cast_pow]; ring
    have hR : (2 * (j : ℝ) + 1 - n) * L ≤ 4 * ((j : ℝ) + 1) := by
      have h₁ : (n : ℝ) ≤ 2 * ((j : ℝ) + 1) := by exact_mod_cast hj₁
      have h₂ : 2 * (j : ℝ) + 1 ≤ (n : ℝ) + d + 1 := by exact_mod_cast hj₂
      calc
        _ ≤ ((d : ℝ) + 1) * L := mul_le_mul_of_nonneg_right (by linarith) hℓ.le
        _ ≤ _ := hdu.trans (by linarith)
    have hratio : q * ((j : ℝ) + 1) ≤ (n : ℝ) - j := by
      apply (mul_le_mul_right₀ hℓ).mp
      have he : q * ((j : ℝ) + 1) * L =
          ((j : ℝ) + 1) * ((L : ℝ) - 4) := by
        dsimp only [q]
        field_simp
        <;> ring
      rw [he]
      nlinarith
    have heq : (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (n.choose j : ℝ) * ((n : ℝ) - j) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn] using h
    change q * (n.choose j : ℝ) ≤ n.choose (j + 1)
    apply (mul_le_mul_right₀ (show 0 < (j : ℝ) + 1 by positivity)).mp
    rw [heq]
    calc
      _ = (n.choose j : ℝ) * (q * ((j : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)
  have hpow : ∀ i ≤ r, q ^ i * (n.choose k : ℝ) ≤ n.choose (k + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      rw [pow_succ']
      calc
        _ = q * (q ^ i * (n.choose k : ℝ)) := mul_assoc _ _ _
        _ ≤ q * (n.choose (k + i) : ℝ) := mul_le_mul_of_nonneg_left (ih (by omega)) hq₀.le
        _ ≤ _ := hstep i (by omega)
  have hfull : (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) := by
    have hn : 2 ^ n ≤ (n + 1) * n.choose k := by
      rw [← Nat.sum_range_choose]
      calc
        _ ≤ ∑ _ ∈ range (n + 1), n.choose k := sum_le_sum (fun i _ => Nat.choose_le_middle i n)
        _ = _ := by simp
    exact_mod_cast hn
  have hlog : -(8 / (L : ℝ)) ≤ Real.log q := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq₀)
    rw [Real.log_inv] at h
    have hinv : q⁻¹ ≤ 2 := (inv_le_iff₀ hq₀).mpr (by linarith)
    have he : q⁻¹ - 1 = (4 / (L : ℝ)) * q⁻¹ := by
      have hc : q * q⁻¹ = 1 := mul_inv_cancel₀ hq₀.ne'
      calc
        _ = (1 - q) * q⁻¹ := by rw [sub_mul, one_mul, hc]
        _ = _ := by dsimp only [q]; ring
    have hbound := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 4 / L by positivity)
    rw [he] at h
    linarith
  have hrpow : Real.exp (-8 * (L : ℝ)) ≤ q ^ r := by
    rw [← Real.exp_log (pow_pos hq₀ r), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have hr' : (r : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast hr
    calc
      _ = -(8 / (L : ℝ)) * (L : ℝ) ^ 2 := by
        field_simp
        <;> ring
      _ ≤ -(8 / (L : ℝ)) * r := mul_le_mul_of_nonpos_left hr' (by positivity)
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (r : ℝ))
  change Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ n ≤ ((L : ℝ) ^ 3 + 1) *
    (n.choose ((n + d) / 2) : ℝ)
  rw [← Nat.cast_pow, ← hkr]
  calc
    _ ≤ q ^ r * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right hrpow (by positivity)
    _ ≤ q ^ r * (((n : ℝ) + 1) * (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left hfull (pow_nonneg hq₀.le r)
    _ = ((n : ℝ) + 1) * (q ^ r * (n.choose k : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow r le_rfl) (by positivity)

end Swarming.Diameter
