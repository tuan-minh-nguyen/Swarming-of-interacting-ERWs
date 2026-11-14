/-
# The deterministic/local scale of the `(locgroup)` deviation estimate

  `mu.real {exists k <= n, eps <= |Q_k|} <= 2 (n+1) exp (-eps^2 / (4 n (2 envB + 1)^2)) + remainder`

with `envB p N B = 2 B + 2 ((2p-1)/p) N (1+B) B` the *quadratic* one-step envelope of
`abs_WA_step_le_of_goodW`, the truncation level `B = max (2H+6) (2G)` still free, and the
remaining scale step (`H = G = L^(1/16)`, `eps = L^(3/4)`, `n ~ T L`) left "on paper" in its
`LOG.md` §7 — with the claim `envB p N (max (2H+6) (2G)) <= kappa L^(1/16)`.

**That claim is wrong, and this file proves the correct one.**  `envB` is *quadratic* in `B`, and
`B = 2 L^(1/16) + 6 <= 8 L^(1/16)`, hence `(1+B) B <= 72 L^(1/8)` and

  `envB p N (max (2 L^(1/16) + 6) (2 L^(1/16))) <= 160 N L^(1/8)`,
  `2 envB + 1 <= 321 N L^(1/8)`     for `1/2 < p <= 1`, `1 <= N`, `1 <= L`.

Consequently, for `eps = L^(3/4)`, `n <= T L`,

  `eps^2 / (4 n (2 envB + 1)^2) >= L^(1/4) / (4 (321 N)^2 T)`,

i.e. the Azuma term is `<= 2 (n+1) exp (-L^(1/4)/(4 (321 N)^2 T))`, which is *stronger* than the
`L^(1/16)`-type exponent the paper needs (the loss `L^(1/8)` in the envelope is dominated by
`eps^2 = L^(3/2)` and the horizon `n <= T L`).

`measure_max_abs_Q_pair_le_scaled` instantiates the existing compiled window estimate with these
constants, so that *no* free `B`, `H`, `G`, `eps` remains: only `p, N, L, T`, the deterministic
start `a`, and the two geometric remainders (separation failure, static `(locmax)` failure) —
still unbounded here, as in the input file.
-/
import Swarm.Imports

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocScaleArithmetic


noncomputable def envB (p : ℝ) (N : ℕ) (B : ℝ) : ℝ :=
  2 * B + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B))

theorem envB_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {N : ℕ} {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ envB p N B := by
  have hp : (0 : ℝ) < p := by linarith
  have hc : 0 ≤ (2 * p - 1) / p := div_nonneg (by linarith) hp.le
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : 0 ≤ (1 + B) * B := mul_nonneg (by linarith) hB
  have h2 : 0 ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B) :=
    mul_nonneg (mul_nonneg hc hN) hprod
  unfold envB
  linarith

variable {N : ℕ}

/-! ## 1. `envB` is quadratic in the truncation level -/

/-- Since `(2p-1)/p ≤ 1` for `p ≤ 1`, the envelope is at most its `p = 1` value. -/
theorem envB_le_quad {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    envB p N B ≤ 2 * B + 2 * ((N : ℝ) * ((1 + B) * B)) := by
  have hp : (0 : ℝ) < p := by linarith
  have hc1 : (2 * p - 1) / p ≤ 1 := by
    rw [div_le_one hp]
    linarith
  have hc0 : 0 ≤ (2 * p - 1) / p := div_nonneg (by linarith) hp.le
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : 0 ≤ (1 + B) * B := by nlinarith
  have hmono : ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B)
      ≤ 1 * (N : ℝ) * ((1 + B) * B) := by
    refine mul_le_mul_of_nonneg_right ?_ hprod
    exact mul_le_mul_of_nonneg_right hc1 hN
  unfold envB
  linarith

/-- `(L^(1/16))^2 = L^(1/8)`. -/
theorem rpow_sq_sixteenth {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((1 : ℝ) / 16)) ^ 2 = L ^ ((1 : ℝ) / 8) := by
  rw [← Real.rpow_natCast (L ^ ((1 : ℝ) / 16)) 2, ← Real.rpow_mul hL]
  norm_num

/-- `(L^(1/8))^2 = L^(1/4)`. -/
theorem rpow_sq_eighth {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((1 : ℝ) / 8)) ^ 2 = L ^ ((1 : ℝ) / 4) := by
  rw [← Real.rpow_natCast (L ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hL]
  norm_num

/-- `(L^(3/4))^2 = L^(3/2)`. -/
theorem rpow_sq_three_quarters {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((3 : ℝ) / 4)) ^ 2 = L ^ ((3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast (L ^ ((3 : ℝ) / 4)) 2, ← Real.rpow_mul hL]
  norm_num

/-- `L^(3/2) = L^(1/4) * L^(5/4)`. -/
theorem rpow_three_halves {L : ℝ} (hL : 0 < L) :
    L ^ ((3 : ℝ) / 2) = L ^ ((1 : ℝ) / 4) * L ^ ((5 : ℝ) / 4) := by
  rw [← Real.rpow_add hL]
  norm_num

/-- `L^(5/4) = L * L^(1/4)`. -/
theorem rpow_five_quarters {L : ℝ} (hL : 0 < L) :
    L ^ ((5 : ℝ) / 4) = L * L ^ ((1 : ℝ) / 4) := by
  have h := Real.rpow_add hL (1 : ℝ) ((1 : ℝ) / 4)
  rw [Real.rpow_one] at h
  rw [← h]
  norm_num

/-! ## 2. The envelope at `H = G = L^(1/16)` -/

/-- The truncation level of the static `(locmax)` bounds at `H = G = L^(1/16)`. -/
noncomputable def truncLevel (L : ℝ) : ℝ :=
  max (2 * L ^ ((1 : ℝ) / 16) + 6) (2 * L ^ ((1 : ℝ) / 16))

theorem truncLevel_eq {L : ℝ} (hL : 1 ≤ L) : truncLevel L = 2 * L ^ ((1 : ℝ) / 16) + 6 := by
  unfold truncLevel
  refine max_eq_left ?_
  have h : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := Real.one_le_rpow hL (by norm_num)
  linarith

/-- **The correct deterministic scale of the one-step envelope**: at `H = G = L^(1/16)` the
quadratic envelope is `O(L^(1/8))`, not `O(L^(1/16))`. -/
theorem envB_truncLevel_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) (hN : 1 ≤ N) {L : ℝ}
    (hL : 1 ≤ L) :
    envB p N (truncLevel L) ≤ 160 * (N : ℝ) * L ^ ((1 : ℝ) / 8) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hr1 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := Real.one_le_rpow hL (by norm_num)
  have hr0 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := by linarith
  have hB0 : (0 : ℝ) ≤ 2 * L ^ ((1 : ℝ) / 16) + 6 := by linarith
  have hB8 : 2 * L ^ ((1 : ℝ) / 16) + 6 ≤ 8 * L ^ ((1 : ℝ) / 16) := by linarith
  have hprod : (1 + (2 * L ^ ((1 : ℝ) / 16) + 6)) * (2 * L ^ ((1 : ℝ) / 16) + 6)
      ≤ 72 * (L ^ ((1 : ℝ) / 8)) := by
    have hsq := rpow_sq_sixteenth hL0.le
    nlinarith [hr1, hr0, hsq]
  have hquad := envB_le_quad (N := N) hp0 hp1 (B := truncLevel L) (by
    rw [truncLevel_eq hL]; linarith)
  rw [truncLevel_eq hL] at hquad ⊢
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrle : L ^ ((1 : ℝ) / 16) ≤ L ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hL8 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hL0.le _
  have hstep : 2 * (2 * L ^ ((1 : ℝ) / 16) + 6)
      + 2 * ((N : ℝ) * ((1 + (2 * L ^ ((1 : ℝ) / 16) + 6))
        * (2 * L ^ ((1 : ℝ) / 16) + 6)))
      ≤ 2 * (8 * L ^ ((1 : ℝ) / 16)) + 2 * ((N : ℝ) * (72 * L ^ ((1 : ℝ) / 8))) := by
    have h2 : ((N : ℝ) * ((1 + (2 * L ^ ((1 : ℝ) / 16) + 6))
        * (2 * L ^ ((1 : ℝ) / 16) + 6)))
        ≤ (N : ℝ) * (72 * L ^ ((1 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left hprod hN0
    linarith
  have hfinal : 2 * (8 * L ^ ((1 : ℝ) / 16)) + 2 * ((N : ℝ) * (72 * L ^ ((1 : ℝ) / 8)))
      ≤ 160 * (N : ℝ) * L ^ ((1 : ℝ) / 8) := by
    nlinarith [hrle, hN1, hL8]
  linarith

/-- **The Azuma constant at the local scale**: `2 envB + 1 ≤ 321 N L^(1/8)`. -/
theorem two_envB_truncLevel_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) (hN : 1 ≤ N) {L : ℝ}
    (hL : 1 ≤ L) :
    2 * envB p N (truncLevel L) + 1 ≤ 321 * (N : ℝ) * L ^ ((1 : ℝ) / 8) := by
  have h := envB_truncLevel_le (N := N) hp0 hp1 hN hL
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL8 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 8) := Real.one_le_rpow hL (by norm_num)
  have hprod : (1 : ℝ) ≤ (N : ℝ) * L ^ ((1 : ℝ) / 8) := by nlinarith
  nlinarith [h, hprod]

/-! ## 3. The exponent at the local scale -/

/-- **The exponent gain.**  For `eps = L^(3/4)`, `n ≤ T L`, the Azuma exponent at the local scale
dominates `L^(1/4) / (4 (321 N)^2 T)`. -/
theorem exp_arg_ge {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) (hN : 1 ≤ N) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 0 < T) {n : ℕ} (hn : 1 ≤ n) (hnTL : (n : ℝ) ≤ T * L) :
    L ^ ((1 : ℝ) / 4) / (4 * (321 * (N : ℝ)) ^ 2 * T)
      ≤ ((L ^ ((3 : ℝ) / 4)) ^ 2)
        / (4 * (n : ℝ) * (2 * envB p N (truncLevel L) + 1) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL8pos : (0 : ℝ) < L ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hL0 _
  have hL4pos : (0 : ℝ) < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hC := two_envB_truncLevel_le (N := N) hp0 hp1 hN hL
  have hCpos : (0 : ℝ) < 2 * envB p N (truncLevel L) + 1 := by
    have h0 : (0 : ℝ) ≤ envB p N (truncLevel L) := by
      refine envB_nonneg hp0 hp1 ?_
      rw [truncLevel_eq hL]
      have h1 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 16) := Real.one_le_rpow hL (by norm_num)
      linarith
    linarith
  have hCsq : (2 * envB p N (truncLevel L) + 1) ^ 2
      ≤ (321 * (N : ℝ) * L ^ ((1 : ℝ) / 8)) ^ 2 := by nlinarith
  have hCsq' : (321 * (N : ℝ) * L ^ ((1 : ℝ) / 8)) ^ 2
      = (321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4) := by
    rw [mul_pow, mul_pow, rpow_sq_eighth hL0.le]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hTL0 : (0 : ℝ) ≤ T * L := by nlinarith
  -- the denominator bound
  have hden : 4 * (n : ℝ) * (2 * envB p N (truncLevel L) + 1) ^ 2
      ≤ 4 * (321 * (N : ℝ)) ^ 2 * T * L ^ ((5 : ℝ) / 4) := by
    have h1 : 4 * (n : ℝ) * (2 * envB p N (truncLevel L) + 1) ^ 2
        ≤ 4 * (n : ℝ) * ((321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4)) := by
      have hCsq'' : (2 * envB p N (truncLevel L) + 1) ^ 2
          ≤ (321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4) := by
        rw [← hCsq']
        exact hCsq
      exact mul_le_mul_of_nonneg_left hCsq'' (by positivity)
    have h2 : 4 * (n : ℝ) * ((321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4))
        ≤ 4 * (T * L) * ((321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4)) := by
      have hnn : (0 : ℝ) ≤ 4 * ((321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4)) := by positivity
      nlinarith [hnTL]
    have h3 : 4 * (T * L) * ((321 * (N : ℝ)) ^ 2 * L ^ ((1 : ℝ) / 4))
        = 4 * (321 * (N : ℝ)) ^ 2 * T * L ^ ((5 : ℝ) / 4) := by
      rw [rpow_five_quarters hL0]
      ring
    linarith
  -- cross-multiplied comparison
  have hden1 : (0 : ℝ) < 4 * (321 * (N : ℝ)) ^ 2 * T := by positivity
  have hden2 : (0 : ℝ) < 4 * (n : ℝ) * (2 * envB p N (truncLevel L) + 1) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hsq := rpow_sq_three_quarters hL0.le
  have hp3 := rpow_three_halves hL0
  calc L ^ ((1 : ℝ) / 4) * (4 * (n : ℝ) * (2 * envB p N (truncLevel L) + 1) ^ 2)
      ≤ L ^ ((1 : ℝ) / 4) * (4 * (321 * (N : ℝ)) ^ 2 * T * L ^ ((5 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hden hL4pos.le
    _ = ((L ^ ((3 : ℝ) / 4)) ^ 2) * (4 * (321 * (N : ℝ)) ^ 2 * T) := by
        rw [hsq, hp3]
        ring

end LocScaleArithmetic
