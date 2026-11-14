import Swarm.Imports
import Mathlib.Tactic.NormNum.RealSqrt
import Swarm.Reflect.Choose

/-!
# The central binomial coefficient is `O(4^n / sqrt n)`

This module proves the anticoncentration estimate needed to turn the reflection law
`card_rmax_lt` into the running-maximum bound `P(max_{t ≤ n} S_t < b) ≤ C b n^{-1/2}`.

The argument avoids Stirling's formula and Wallis products. Writing
`walkMass m = m.centralBinom / 4^m` for the probability that the walk is at `0` at time `2m`,
the elementary recursion `(m+1) * (m+1).centralBinom = 2 * (2m+1) * m.centralBinom` gives

  `walkMass (m+1) = walkMass m * (2m+1)/(2m+2)`,

and the *purely algebraic* inequality `(m+2) (2m+1)^2 ≤ 4 (m+1)^3` (difference `3m+2`) yields,
by induction, `(m+1) * walkMass m ^ 2 ≤ 1`, i.e. `m.centralBinom ≤ 4^m / sqrt (m+1)`.
The odd-index case then follows from Pascal's rule
`(2m+1).choose m = (2m).choose m + (2m).choose (m-1) ≤ 2 * m.centralBinom`.
-/
open Finset

namespace SwarmReflect

open Classical

/-- The probability mass of the walk at the origin after `2m` steps. -/
noncomputable def walkMass (m : ℕ) : ℝ := (m.centralBinom : ℝ) / 4 ^ m

theorem walkMass_nonneg (m : ℕ) : 0 ≤ walkMass m := by
  unfold walkMass
  positivity

theorem walkMass_zero : walkMass 0 = 1 := by
  unfold walkMass
  simp

theorem centralBinom_cast_succ (m : ℕ) :
    ((m + 1).centralBinom : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (m.centralBinom : ℝ) / ((m : ℝ) + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have h' : ((m + 1 : ℕ) : ℝ) * (((m + 1).centralBinom : ℕ) : ℝ)
      = 2 * (2 * ((m : ℕ) : ℝ) + 1) * ((m.centralBinom : ℕ) : ℝ) := by
    exact_mod_cast h
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast at h' ⊢
  field_simp at h' ⊢
  linarith [h']

theorem walkMass_succ (m : ℕ) :
    walkMass (m + 1) = walkMass m * ((2 * (m : ℝ) + 1) / (2 * ((m : ℝ) + 1))) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpow : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
  unfold walkMass
  rw [centralBinom_cast_succ, hpow]
  field_simp
  ring

/-- **The key induction.** `(m+1) * (mass at 0 after 2m steps)^2 ≤ 1`. -/
theorem walkMass_sq_bound (m : ℕ) : ((m : ℝ) + 1) * (walkMass m) ^ 2 ≤ 1 := by
  induction m with
  | zero => norm_num [walkMass_zero]
  | succ k ih =>
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [walkMass_succ]
    have hsq : (walkMass k) ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hk]
      linarith [ih]
    have hratio_nonneg : (0 : ℝ) ≤ ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2 := by
      positivity
    have hstep : (walkMass k) ^ 2 * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2
        ≤ (1 / ((k : ℝ) + 1)) * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq hratio_nonneg
    have hrewrite : (((k + 1 : ℕ) : ℝ) + 1)
          * (walkMass k * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)))) ^ 2
        = ((k : ℝ) + 2)
          * ((walkMass k) ^ 2 * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2) := by
      push_cast
      ring
    have htarget : ((k : ℝ) + 2) * (2 * (k : ℝ) + 1) ^ 2 ≤ 4 * ((k : ℝ) + 1) ^ 3 := by
      nlinarith [sq_nonneg (k : ℝ), hk.le]
    have hden : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 3 := by positivity
    have hmid : ((k : ℝ) + 2)
          * ((1 / ((k : ℝ) + 1)) * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2)
        = ((k : ℝ) + 2) * (2 * (k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 3) := by
      field_simp
      ring
    rw [hrewrite]
    calc ((k : ℝ) + 2)
          * ((walkMass k) ^ 2 * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2)
        ≤ ((k : ℝ) + 2)
            * ((1 / ((k : ℝ) + 1)) * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hstep
          positivity
      _ = ((k : ℝ) + 2) * (2 * (k : ℝ) + 1) ^ 2 / (4 * ((k : ℝ) + 1) ^ 3) := hmid
      _ ≤ 1 := by
          rw [div_le_one hden]
          linarith [htarget]

/-- **Central binomial bound.** `m.centralBinom ≤ 4^m / sqrt (m+1)`. -/
theorem centralBinom_le_sqrt (m : ℕ) :
    (m.centralBinom : ℝ) ≤ 4 ^ m / Real.sqrt ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hb := walkMass_sq_bound m
  have hnn := walkMass_nonneg m
  have hsq : (walkMass m) ^ 2 ≤ 1 / ((m : ℝ) + 1) := by
    rw [le_div_iff₀ hm]
    linarith [hb]
  have h₁ : walkMass m ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
    have hsqrt : Real.sqrt (1 / ((m : ℝ) + 1)) = 1 / Real.sqrt ((m : ℝ) + 1) := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1)]
      simp
    rw [← hsqrt]
    exact (Real.le_sqrt hnn (by positivity)).mpr hsq
  have hpow : (0 : ℝ) < 4 ^ m := by positivity
  unfold walkMass at h₁
  have h₂ : (m.centralBinom : ℝ) / 4 ^ m ≤ 1 / Real.sqrt ((m : ℝ) + 1) := h₁
  rw [div_le_iff₀ hpow] at h₂
  calc (m.centralBinom : ℝ) ≤ 1 / Real.sqrt ((m : ℝ) + 1) * 4 ^ m := h₂
    _ = 4 ^ m / Real.sqrt ((m : ℝ) + 1) := by ring

/-- Even index: `(2m).choose m = m.centralBinom`. -/
theorem choose_even (m : ℕ) : (2 * m).choose ((2 * m) / 2) = m.centralBinom := by
  rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  exact (Nat.centralBinom_eq_two_mul_choose m).symm

theorem choose_even' (m : ℕ) : m.centralBinom = (2 * m).choose ((2 * m) / 2) :=
  (choose_even m).symm

/-- Odd index: `(2m+1).choose m ≤ 2 * (2m).choose m`. -/
theorem choose_odd_le (m : ℕ) :
    (2 * m + 1).choose ((2 * m + 1) / 2) ≤ 2 * (2 * m).choose ((2 * m) / 2) := by
  rw [Nat.mul_add_div (by norm_num : 0 < 2), Nat.div_eq_of_lt (by norm_num : 1 < 2),
    Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  rcases m with _ | k
  · norm_num
  · have hpascal : (2 * (k + 1) + 1).choose (k + 1)
        = (2 * (k + 1)).choose (k + 1) + (2 * (k + 1)).choose k := by
      have h := Nat.choose_succ_succ (2 * (k + 1)) k
      have h' : (2 * (k + 1) + 1).choose (k + 1)
          = (2 * (k + 1)).choose k + (2 * (k + 1)).choose (k + 1) := h
      rw [h', add_comm]
    rw [hpascal]
    have hle : (2 * (k + 1)).choose k ≤ (2 * (k + 1)).choose (k + 1) := by
      have h := Nat.choose_le_middle k (2 * (k + 1))
      rwa [Nat.mul_div_cancel_left (k + 1) (by norm_num : 0 < 2)] at h
    omega

/-- **Anticoncentration of the endpoint.** For every `n`,
`n.choose (n / 2) ≤ sqrt 2 * 2^n / sqrt (n+1)`. -/
theorem choose_middle_le_sqrt (n : ℕ) :
    (n.choose (n / 2) : ℝ) ≤ Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1) := by
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- even case: n = 2m
    rw [hm, ← two_mul m]
    push_cast
    have hcen := centralBinom_le_sqrt m
    have hstep : (1 : ℝ) / Real.sqrt ((m : ℝ) + 1)
        ≤ Real.sqrt 2 / Real.sqrt (2 * (m : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc Real.sqrt (2 * (m : ℝ) + 1) ≤ Real.sqrt (2 * ((m : ℝ) + 1)) := by
            apply Real.sqrt_le_sqrt
            nlinarith
        _ = Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := Real.sqrt_mul (by norm_num) _
    have h2n : (2 : ℝ) ^ (2 * m) = 4 ^ m := by
      rw [pow_mul]; norm_num
    rw [h2n, ← choose_even']
    calc (m.centralBinom : ℝ) ≤ 4 ^ m / Real.sqrt ((m : ℝ) + 1) := hcen
      _ = 4 ^ m * (1 / Real.sqrt ((m : ℝ) + 1)) := by ring
      _ ≤ 4 ^ m * (Real.sqrt 2 / Real.sqrt (2 * (m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = Real.sqrt 2 * 4 ^ m / Real.sqrt (2 * (m : ℝ) + 1) := by ring
  · -- odd case: n = 2m+1
    rw [hm]
    push_cast
    have hcen := centralBinom_le_sqrt m
    have hodd := choose_odd_le m
    have hodd' : (((2 * m + 1).choose ((2 * m + 1) / 2) : ℕ) : ℝ) ≤ 2 * (m.centralBinom : ℝ) := by
      have hcast : (((2 * m + 1).choose ((2 * m + 1) / 2) : ℕ) : ℝ)
          ≤ ((2 * (2 * m).choose ((2 * m) / 2) : ℕ) : ℝ) := by
        exact_mod_cast hodd
      push_cast at hcast
      rw [choose_even] at hcast
      linarith
    have h2n : (2 : ℝ) ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]; norm_num; ring
    rw [h2n]
    have hden : Real.sqrt ((2 * (m : ℝ) + 1) + 1) = Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [show (2 * (m : ℝ) + 1) + 1 = 2 * ((m : ℝ) + 1) by ring]
      exact Real.sqrt_mul (by norm_num) _
    rw [hden]
    have hsimp : Real.sqrt 2 * (2 * 4 ^ m) / (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1))
        = 2 * 4 ^ m / Real.sqrt ((m : ℝ) + 1) := by
      field_simp
    rw [hsimp]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    calc (((2 * m + 1).choose ((2 * m + 1) / 2) : ℕ) : ℝ) ≤ 2 * (m.centralBinom : ℝ) := hodd'
      _ ≤ 2 * (4 ^ m / Real.sqrt ((m : ℝ) + 1)) := by linarith [hcen]
      _ = 2 * 4 ^ m / Real.sqrt ((m : ℝ) + 1) := by ring

/-- **The running-maximum bound.** For every level `b ≥ 1`, the number of `±1`
step sequences of length `n` that never reach `b` is at most
`(2b+1) · sqrt 2 · 2^n / sqrt (n+1)`; equivalently, for the uniform measure on
`Fin n → Bool`,

  `P(max_{t ≤ n} S_t < b) ≤ (2b + 1) * sqrt 2 / sqrt (n + 1)`,

which is the paper's `C b n^{-1/2}` with `C = 2 * sqrt 2`. -/
theorem card_rmax_lt_le_sqrt {b : ℕ} (hb : 1 ≤ b) :
    ((Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < (b : ℤ)).card : ℝ)
      ≤ (2 * b + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1) := by
  have h1 := card_rmax_lt_le_middle (n := n) b hb
  have h2 := choose_middle_le_sqrt n
  have h1' : ((Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < (b : ℤ)).card : ℝ)
      ≤ ((2 * b + 1) * n.choose (n / 2) : ℕ) := by
    exact_mod_cast h1
  push_cast at h1'
  calc ((Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < (b : ℤ)).card : ℝ)
      ≤ (2 * b + 1) * n.choose (n / 2) := h1'
    _ ≤ (2 * b + 1) * (Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = (2 * b + 1) * Real.sqrt 2 * 2 ^ n / Real.sqrt ((n : ℝ) + 1) := by ring

end SwarmReflect
