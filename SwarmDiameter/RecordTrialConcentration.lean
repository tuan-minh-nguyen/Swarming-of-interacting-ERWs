import Swarm.GammaAmbient
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl
open scoped ENNReal Topology

set_option autoImplicit false

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Diameter

/-- The probability that any nonempty proper group has a deficit of
`ε * L` successful trials on a subinterval of the prescribed interval is
exponentially small in `L`. The whole interval starts at a nonnegative site. -/
theorem gamma_trial_concentration
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1) (hm : 0 < m)
    (N T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℤ, ((T + 3) * L : ℤ) ≤ r →
      (arrayMeasure N).real
        (⋃ A ∈ (properGroups N).attach, ⋃ ab ∈ ambFamily r T L, {U : Array N |
          (((Finset.Icc ab.1 ab.2).filter
            (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card : ℝ)
          < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
            - ε * L}) ≤ Real.exp (-c * (L : ℝ)) := by
  classical
  let k : ℝ := ε / (2 * (m : ℝ))
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : 0 < k := div_pos hε (by positivity)
  let d : ℝ := k ^ 2 / (2 * (T : ℝ) + 7)
  have hd : 0 < d := div_pos (pow_pos hk _) (by positivity)
  let C : ℝ := (2 ^ N : ℝ) * (2 * (T : ℝ) + 7) ^ 2 * (2 * (m : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h := ((isLittleO_exp_mul_rpow_of_lt 2 (show -d < -(d / 2) by linarith)).const_mul_left C).bound
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), tendsto_natCast_atTop_atTop.eventually h] with L hL hpoly
  intro r hr
  let t := k * (L : ℝ)
  have ht : 0 ≤ t := mul_nonneg hk.le (Nat.cast_nonneg _)
  have hthr : 2 * (m : ℝ) * t = ε * L := by
    dsimp [t, k]
    field_simp
  let E := Real.exp (-d * (L : ℝ))
  let S := (properGroups N).attach
  let I := ambFamily r T L
  let B (A : {A // A ∈ properGroups N}) (ab : ℤ × ℤ) : Set (Array N) := {U |
    (((Finset.Icc ab.1 ab.2).filter
      (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card : ℝ)
    < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ) - ε * L}
  have hB (A : {A // A ∈ properGroups N}) (ab : ℤ × ℤ) (hab : ab ∈ I) :
      (arrayMeasure N).real (B A ab) ≤ (2 * (m : ℝ)) * E := by
    obtain ⟨hlo, hle, _⟩ := ambFamily_spec hab
    have hb := gamma_interval_count_lower p hp₀ hp₁ m hm A.1 (mem_properGroups.mp A.2).1
      ((ambLo_nonneg hr).trans hlo) hle ht
    rw [hthr] at hb
    have hden : (0 : ℝ) < clsKbar ab.1 ab.2 m := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_clsKbar ab.1 ab.2 m))
    have hsize : (clsKbar ab.1 ab.2 m : ℝ) ≤ (2 * (T : ℝ) + 7) * (L : ℝ) :=
      (by exact_mod_cast clsKbar_le_ambWidth hab : (clsKbar ab.1 ab.2 m : ℝ) ≤ ambWidth T L).trans
        (ambWidth_le_linear hL)
    have hrate : Real.exp (-(t ^ 2 / (clsKbar ab.1 ab.2 m : ℝ))) ≤ E := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_le_neg_iff, le_div_iff₀ hden]
      calc
        _ ≤ d * (L : ℝ) * ((2 * (T : ℝ) + 7) * (L : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hsize (mul_nonneg hd.le (Nat.cast_nonneg _))
        _ = _ := by dsimp only [d, t]; field_simp
    have hfinite : ((2 * m : ℕ) : ℝ≥0∞) * ENNReal.ofReal E ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hfinite
      (hb.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hrate) ((2 * m : ℕ) : ℝ≥0∞)))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    simpa only [B, Measure.real_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hE, Nat.cast_mul, Nat.cast_ofNat] using hreal
  have hmass : (arrayMeasure N).real (⋃ A ∈ S, ⋃ ab ∈ I, B A ab) ≤
      (S.card : ℝ) * (I.card : ℝ) * ((2 * (m : ℝ)) * E) := by
    refine (measureReal_biUnion_finset_le S _).trans ?_
    have hsum := sum_le_sum (s := S) (fun A _ =>
      (measureReal_biUnion_finset_le I _).trans
        (sum_le_sum (g := fun _ => 2 * (m : ℝ) * E) (hB A)))
    simpa only [sum_const, nsmul_eq_mul, mul_assoc] using hsum
  have hS : (S.card : ℝ) ≤ 2 ^ N := by
    rw [card_attach]
    exact_mod_cast card_properGroups_le N
  have hI : (I.card : ℝ) ≤ ((2 * (T : ℝ) + 7) * (L : ℝ)) ^ 2 := by
    have hi : (I.card : ℝ) ≤ (ambWidth T L : ℝ) ^ 2 := by exact_mod_cast ambFamily_card_le r T L
    exact hi.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (ambWidth_le_linear hL) _)
  change (arrayMeasure N).real (⋃ A ∈ S, ⋃ ab ∈ I, B A ab) ≤ _
  refine hmass.trans ?_
  calc
    _ ≤ (2 ^ N : ℝ) * (((2 * (T : ℝ) + 7) * (L : ℝ)) ^ 2) * ((2 * (m : ℝ)) * E) := by
      gcongr
    _ = C * (Real.exp (-d * (L : ℝ)) * (L : ℝ) ^ (2 : ℝ)) := by
      dsimp only [C, E]
      rw [Real.rpow_ofNat]
      ring
    _ ≤ _ := by
      change ‖C * (Real.exp (-d * (L : ℝ)) * (L : ℝ) ^ (2 : ℝ))‖ ≤
        1 * ‖Real.exp (-(d / 2) * (L : ℝ))‖ at hpoly
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_pos (Real.exp_pos _), one_mul] at hpoly
      exact hpoly

end Swarming.Diameter
