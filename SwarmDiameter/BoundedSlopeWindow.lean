import SwarmDiameter.BoundedPotential
import Swarm.L1Trunc
import Swarm.LocCoord

open Finset
open LocSum SwarmSpatial
open Swarming.Trajectory Swarming.Uniform SepGroup.Model

namespace Swarming.Diameter

set_option autoImplicit false

/-- The affine recursion over the last `k` sites, started with value `K`. -/
noncomputable def finiteSlope (p K : ℝ) (k x : ℕ) (ω : ℕ → Bool) : ℝ :=
  Q p k x ω + (K + 1) * Pz p x k ω

private theorem finiteSlope_succ (p K : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    finiteSlope p K (k + 1) x ω = 1 + rat p ω x * (1 + finiteSlope p K k (x - 1) ω) := by
  simp only [finiteSlope, Q_succ, Pz_succ]
  ring

theorem boundedSlope_le_finiteSlope {K p : ℝ} (hK : 1 ≤ K)
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (hv₁ : ∀ n, v n ≤ 1) (ω : ℕ → Bool)
    {k x : ℕ} (hk : k ≤ x) (hle : ∀ j < k, omegaOf p (ω (x - j)) ≤ v (x - j)) :
    boundedSlope K v (x + 1) ≤ finiteSlope p K k x ω := by
  induction k generalizing x with
  | zero => simpa [finiteSlope] using (boundedSlope_bounds hK hv hv₁ (x + 1)).2
  | succ k ih =>
    let w := omegaOf p (ω x)
    have hw : 0 < w := by
      dsimp only [w]
      cases ω x
      · norm_num [omegaOf]
      · simpa [omegaOf] using (show 0 < p by linarith)
    have hw₁ : w ≤ 1 := by
      dsimp only [w]
      cases ω x <;> simp [omegaOf] <;> linarith
    have hwv : w ≤ v x := by simpa only [Nat.sub_zero, w] using hle 0 (Nat.zero_lt_succ _)
    have hprev : boundedSlope K v x ≤ finiteSlope p K k (x - 1) ω := by
      have hx : x - 1 + 1 = x := by omega
      have hl (j : ℕ) (hj : j < k) :
          omegaOf p (ω (x - 1 - j)) ≤ v (x - 1 - j) := by
        rw [show x - 1 - j = x - (j + 1) by omega]
        exact hle (j + 1) (Nat.succ_lt_succ hj)
      have hb := ih (x := x - 1) (by omega) hl
      rwa [hx] at hb
    rw [boundedSlope, finiteSlope_succ]
    calc
      _ ≤ (1 + (1 - v x) * boundedSlope K v x) / v x := min_le_right _ _
      _ ≤ (1 + (1 - w) * boundedSlope K v x) / w :=
        Cookie.step_mono hw hwv (boundedSlope_bounds hK hv hv₁ x).1
      _ ≤ (1 + (1 - w) * finiteSlope p K k (x - 1) ω) / w :=
        Cookie.step_mono_h hw hw₁ hprev
      _ = _ := by
        have he : rat p ω x = (1 - w) / w := by
          cases hω : ω x <;> norm_num [rat, w, omegaOf, hω]
        rw [he]
        field_simp [hw.ne']
        ring

/-- Below a walker's running maximum, the finite recursion on that walker's
marks dominates the bounded slope for any group containing the walker. -/
theorem boundedSlope_wA_le_finiteSlope {N : ℕ} {K p : ℝ} (hK : 1 ≤ K)
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m : ℕ} {U : Array N} {n : ℕ}
    {A : Finset (Fin N)} {i : Fin N} (hi : i ∈ A)
    {k x : ℕ} (hk : k ≤ x) (hx : (x : ℤ) < runMax p m U i n) :
    boundedSlope K (wA p m U n A) (x + 1) ≤
      finiteSlope p K k x (SwarmLogRatio.siteMarks p m U i) := by
  apply boundedSlope_le_finiteSlope hK hp₀ hp₁ (wA_pos p m U hp₀.le n A)
    (wA_le_one p m U hp₁.le n A) _ hk
  intro j hj
  rw [show omegaOf p (SwarmLogRatio.siteMarks p m U i (x - j)) =
    omegaAt p m U i ((x - j : ℕ) : ℤ) from (Loccoord.omegaN_eq i (x - j)).symm]
  simpa only [compl_compl] using omegaAt_le_wA p m U hp₀.le
    (J := Aᶜ) (by simpa only [compl_compl] using hi)
    (lt_of_le_of_lt (by exact_mod_cast Nat.sub_le x j) hx)

theorem one_le_Q {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {k : ℕ} (hk : 1 ≤ k) (x : ℕ) (ω : ℕ → Bool) : 1 ≤ Q p k x ω := by
  have h := Finset.single_le_sum
    (s := Finset.range k) (f := fun j => Pz p x j ω) (fun j _ => Pz_nonneg hp₀ hp₁ x j ω)
    (Finset.mem_range.mpr (show 0 < k from hk))
  rw [Pz_zero] at h
  unfold Q Gsum
  linarith only [h]

/-- The uniform spatial sum bound for `Q` also bounds the finite
recursions started with value `8 * k`. -/
theorem finiteSlope_le_ten_Q {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {k : ℕ} (hk : 1 ≤ k) (x : ℕ) (ω : ℕ → Bool) :
    finiteSlope p (8 * (k : ℝ)) k x ω ≤ 10 * Q p k x ω := by
  have hP (j : ℕ) (hj : j ∈ Finset.range k) : Pz p x k ω ≤ Pz p x j ω := by
    have hjk := (Finset.mem_range.mp hj).le
    rw [← Nat.add_sub_of_le hjk, Pz_add]
    exact mul_le_of_le_one_right (Pz_nonneg hp₀ hp₁ x j ω) (Pz_le_one hp₀ hp₁ (x - j) (k - j) ω)
  have hsum := Finset.sum_le_sum hP
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : (8 * (k : ℝ) + 1) * Pz p x k ω ≤ 9 * ((k : ℝ) * Pz p x k ω) := by
    nlinarith only [mul_le_mul_of_nonneg_right hk' (Pz_nonneg hp₀ hp₁ x k ω)]
  have hQ := one_le_Q hp₀ hp₁ hk x ω
  unfold finiteSlope Q Gsum at *
  linarith only [hsum, hprod, hQ]

/-- At the cutoff `8 * k`, a possible loss of unit drift requires the
product of the last `k` ratios to exceed one half. -/
theorem finiteSlope_le_cap_sub_two {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {k : ℕ} (hk : 1 ≤ k) {x : ℕ} {ω : ℕ → Bool} (hP : Pz p x k ω ≤ 1 / 2) :
    finiteSlope p (8 * (k : ℝ)) k x ω ≤ 8 * (k : ℝ) - 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod := mul_le_mul_of_nonneg_left hP (show 0 ≤ 8 * (k : ℝ) + 1 by positivity)
  unfold finiteSlope
  linarith only [Q_le hp₀ hp₁ k x ω, hprod, hk']

end Swarming.Diameter
