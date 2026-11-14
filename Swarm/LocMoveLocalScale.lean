import Swarm.LocMoveLocalProfile
import Swarm.A3Scale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveLocal

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart LocSumAct

variable {N : ℕ}

/-- The Chernoff side condition at `B = L^(1/16)` and horizon `TL` is automatic. -/
lemma paper_side_condition {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (L : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * (((T * L : ℕ) : ℝ)) * xOf L := by
  have hx : 1 ≤ xOf L := one_le_xOf hL
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTL : L ≤ T * L := by
    calc L = 1 * L := by ring
      _ ≤ T * L := Nat.mul_le_mul_right L hT
  have hTLr : (L : ℝ) ≤ ((T * L : ℕ) : ℝ) := by exact_mod_cast hTL
  have hpow : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) := by
    calc (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLr (by norm_num)
      _ = (L : ℝ) := Real.rpow_one _
  nlinarith

/-- `(L^(1/16))^12 = L^(3/4)`. -/
lemma xOf_pow_twelve (L : ℕ) : (xOf L) ^ 12 = (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 12, ← Real.rpow_mul hL]
  norm_num

/-- Exact exponent of the local maximal profile at the paper's scale. -/
lemma paper_exponent_eq {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    -((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (4 * (((T * L : ℕ) : ℝ)) * (2 * xOf L) ^ 2) =
      -((xOf L) ^ 6 / (16 * (T : ℝ))) := by
  have hx : 0 < xOf L := lt_of_lt_of_le zero_lt_one (one_le_xOf hL)
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  push_cast
  rw [← xOf_pow_twelve L, ← xOf_pow L]
  field_simp [ne_of_gt hx, ne_of_gt hTr]
  ring

/-- At `B = L^(1/16)` and horizon `TL`, the local maximal bound has exponent
`L^(3/8)/(16T)`. -/
theorem measure_max_abs_Lcum_paper_scale {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {T L s : ℕ}
    (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (arrayMeasure N).real
        {U | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤
          |Lcum p m (s + k) J hJ (xOf L) U - Lcum p m s J hJ (xOf L) U|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-((xOf L) ^ 6 / (16 * (T : ℝ)))) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hx : 0 < xOf L := lt_of_lt_of_le zero_lt_one (one_le_xOf hL)
  have hmain := measure_max_abs_Lcum_window_le (p := p) hp hp1 m J hJ hx
    (s := s) (K := T * L) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
    (Real.rpow_pos_of_pos hLr _) (paper_side_condition hT hL)
  rw [paper_exponent_eq hT hL] at hmain
  exact hmain

end LocMoveLocal
