/-
  # `L34 L (Lw T L) <= C_T L^{3/4}`: the paper's explicit remainder

  The compiled displays carry the abstract remainder
  `L34 L (Lw T L) = 3 betaT (xOf (Lw T L)) + (xOf (Lw T L))^2 + L^{3/4}`, while Proposition
  `local` of the paper writes `C_T L^{3/4}`, with `C_T` depending only on `N,m,p,T`.

  Here the abstract remainder is converted into that explicit form with the coefficient
  `9 (2T+3)^{3/4} + (2T+3)^{1/8} + 1`, using

  * `LocSumAct.betaT_xOf_le_rpow34 : betaT (xOf M) <= 3 M^{3/4}`  (`M^{3/8} <= M^{3/4}`),
  * `(xOf M)^2 = M^{1/8}` and `M^{1/8} <= M^{3/4}`  (`M >= 1`),
  * `Lw T L = (2T+2) L + 1 <= (2T+3) L`  (`L >= 1`), and multiplicativity of `x |-> x^z`.

  The `T`-dependence is therefore exactly the polynomial-in-`T` factor `(2T+3)`, and nothing else.
-/
import Swarm.LocOccCarrierAssembly

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

open scoped ENNReal BigOperators

namespace L34PaperScale

open LocOccCarrierAssembly LocOccCarrier LocSumAct

/-- `Lw T L <= (2T+3) L` on the paper's range `L >= 1`. -/
theorem Lw_le (T L : ℕ) (hL : 1 ≤ L) : Lw T L ≤ (2 * T + 3) * L := by
  have h : (2 * T + 3) * L = (2 * T + 2) * L + L := by ring
  unfold Lw
  omega

/-- `M^{3/4} <= ((2T+3)L)^{3/4} = (2T+3)^{3/4} L^{3/4}`. -/
theorem rpow34_le {T L : ℕ} (hL : 1 ≤ L) :
    ((Lw T L : ℕ) : ℝ) ^ (3 / 4 : ℝ)
      ≤ (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hle : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 3) * L : ℕ) : ℝ) := by
    exact_mod_cast Lw_le T L hL
  have hcast : ((((2 * T + 3) * L : ℕ)) : ℝ) = (((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ) := by
    push_cast; ring
  calc ((Lw T L : ℕ) : ℝ) ^ (3 / 4 : ℝ)
      ≤ ((((2 * T + 3) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = ((((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ)) ^ (3 / 4 : ℝ) := by rw [hcast]
    _ = (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) :=
        Real.mul_rpow (by positivity) (by positivity)

/-- `M^{1/8} <= (2T+3)^{1/8} L^{3/4}`: the `(locmax)` cap squared, at the paper's scale. -/
theorem rpow18_le {T L : ℕ} (hL : 1 ≤ L) :
    ((Lw T L : ℕ) : ℝ) ^ (1 / 8 : ℝ)
      ≤ (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hle : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 3) * L : ℕ) : ℝ) := by
    exact_mod_cast Lw_le T L hL
  have hcast : ((((2 * T + 3) * L : ℕ)) : ℝ) = (((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ) := by
    push_cast; ring
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hmono : (L : ℝ) ^ (1 / 8 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  calc ((Lw T L : ℕ) : ℝ) ^ (1 / 8 : ℝ)
      ≤ ((((2 * T + 3) * L : ℕ)) : ℝ) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = ((((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ)) ^ (1 / 8 : ℝ) := by rw [hcast]
    _ = (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) * (L : ℝ) ^ (1 / 8 : ℝ) :=
        Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
        have h0 : (0 : ℝ) ≤ (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hmono h0

/-- `(xOf M)^2 = M^{1/8}`. -/
theorem xOf_sq (M : ℕ) : (xOf M) ^ 2 = (M : ℝ) ^ (1 / 8 : ℝ) := by
  have h0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  rw [xOf, ← Real.rpow_natCast ((M : ℝ) ^ (1 / 16 : ℝ)) 2, ← Real.rpow_mul h0]
  norm_num

/-- **The paper's explicit remainder.**  `L34 L (Lw T L) <= C_T L^{3/4}` with
`C_T = 9 (2T+3)^{3/4} + (2T+3)^{1/8} + 1`, for every `L >= 1` and every `T`. -/
theorem L34_Lw_le_rpow34 (T : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    L34 L (Lw T L)
      ≤ (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
          + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h34 : (1 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hnn34 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := le_trans zero_le_one h34
  -- the three pieces of `L34`
  have hβ : ((betaT (xOf (Lw T L)) : ℕ) : ℝ) ≤ 3 * ((Lw T L : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
    betaT_xOf_le_rpow34 (L := Lw T L) hLw1
  have hA : 3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have h := rpow34_le (T := T) hL
    nlinarith [hβ, h]
  have hB : (xOf (Lw T L)) ^ 2
      ≤ ((((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [xOf_sq]
    exact rpow18_le (T := T) hL
  have hC : (L : ℝ) ^ (3 / 4 : ℝ) ≤ 1 * (L : ℝ) ^ (3 / 4 : ℝ) := by linarith
  unfold L34
  nlinarith [hA, hB, hC, hnn34]

end L34PaperScale
