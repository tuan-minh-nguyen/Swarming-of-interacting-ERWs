import SwarmDiameter.BoundedGroupStep

open Finset
open Swarming.Uniform Swarming.Group Swarming.Trajectory
open SepGroup.Model SwarmJointDrift Loccoord

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ}

theorem monotone_boundedHA {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) :
    Monotone (boundedHA p m K U n A) := by
  intro x y hxy
  have h := (boundedPotential_sub_bounds hK (wA_pos p m U hp₀ n A)
    (wA_le_one p m U hp₁ n A) hxy).1
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  change (y : ℝ) - x ≤ boundedHA p m K U n A y - boundedHA p m K U n A x at h
  linarith only [h, hxy']

/-- The change in the one-step mean caused by replacing the comparison
probability by the actual jump probability. -/
noncomputable def boundedCorrection (p K : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) : ℝ :=
  let x := (X p m U n i).toNat
  let w := wA p m U n A
  (SwarmCross.alphaFun p m n i U - w x) *
    (boundedSlope K w (x + 1) + boundedSlope K w x)

private theorem comparisonMean_eq (p K : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) (hx : 0 ≤ X p m U n i) :
    comparisonMean p K m U n A i =
      wA p m U n A (X p m U n i).toNat *
          boundedSlope K (wA p m U n A) ((X p m U n i).toNat + 1) -
        (1 - wA p m U n A (X p m U n i).toNat) *
          boundedSlope K (wA p m U n A) (X p m U n i).toNat +
        boundedCorrection p K m U n A i :=
  boundedPotential_mean_increment K hx _

theorem comparisonMean_le_one_add {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) (i : Fin N)
    (hx : 0 ≤ X p m U n i) :
    comparisonMean p K m U n A i ≤ 1 + boundedCorrection p K m U n A i := by
  rw [comparisonMean_eq p K m U n A i hx]
  exact add_le_add
    (boundedSlope_increment_bounds hK (one_half_le_wA p m U hp₀ n A)
      (wA_le_one p m U hp₁ n A) _).2 le_rfl

theorem boundedCorrection_nonpos_of_sep {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) (n : ℕ)
    {I J : Finset (Fin N)} (hIJ : Disjoint I J) (hsep : SepSet p m n I J U)
    {i : Fin N} (hi : i ∈ I) : boundedCorrection p K m U n Jᶜ i ≤ 0 := by
  have h := rightProbability_le_wA_of_sep p m U hp₀ hIJ hsep hi
  rw [← alphaFun_eq_rightProb] at h
  let x := (X p m U n i).toNat
  let w := wA p m U n Jᶜ
  have hb := boundedSlope_bounds hK (wA_pos p m U hp₀ n Jᶜ) (wA_le_one p m U hp₁ n Jᶜ)
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
    (add_nonneg (zero_le_one.trans (hb (x + 1)).1) (zero_le_one.trans (hb x).1))

theorem boundedCorrection_le_of_strict {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) (i : Fin N)
    (hα : SwarmCross.alphaFun p m n i U = 1 / 2)
    (hw : wA p m U n A (X p m U n i).toNat = p) :
    boundedCorrection p K m U n A i ≤ -(2 * p - 1) := by
  have hh := boundedSlope_bounds hK (wA_pos p m U hp₀ n A) (wA_le_one p m U hp₁ n A)
  let x := (X p m U n i).toNat
  have hs : (2 : ℝ) ≤ boundedSlope K (wA p m U n A) (x + 1) + boundedSlope K (wA p m U n A) x :=
    by linarith only [(hh (x + 1)).1, (hh x).1]
  unfold boundedCorrection
  dsimp only
  rw [hα, hw]
  exact (mul_le_mul_of_nonpos_left hs (sub_nonpos.mpr hp₀)).trans_eq (by ring)

private theorem comparisonMean_ge_of_J {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (hpK : 1 ≤ (2 * p - 1) * K) (m : ℕ) (U : Array N) (n : ℕ)
    {J : Finset (Fin N)} {j : Fin N} (hj : j ∈ J) (hx : 0 ≤ X p m U n j) :
    0 ≤ comparisonMean p K m U n Jᶜ j ∧
      (boundedSlope K (wA p m U n Jᶜ) (X p m U n j).toNat ≤ K - 2 →
        1 ≤ comparisonMean p K m U n Jᶜ j) := by
  let x := (X p m U n j).toNat
  let w := wA p m U n Jᶜ
  have ha := wA_le_rightProbability_of_J p m U hp₀ hj hx
  rw [← alphaFun_eq_rightProb] at ha
  have hw := wA_pos p m U hp₀ n Jᶜ
  have hw₁ := wA_le_one p m U hp₁ n Jᶜ
  have hs := boundedSlope_bounds hK hw hw₁
  have hc : 0 ≤ boundedCorrection p K m U n Jᶜ j :=
    mul_nonneg (sub_nonneg.mpr ha) (add_nonneg (zero_le_one.trans (hs (x + 1)).1)
      (zero_le_one.trans (hs x).1))
  rw [comparisonMean_eq p K m U n Jᶜ j hx]
  refine ⟨add_nonneg (boundedSlope_increment_bounds hK (one_half_le_wA p m U hp₀ n Jᶜ) hw₁ x).1 hc, ?_⟩
  intro hnear
  have hd := boundedSlope_increment_eq_one hK hw hw₁ x (by
    rcases wA_eq_half_or p m U n Jᶜ x with he | he
    · exact Or.inr ⟨he, hnear⟩
    · exact Or.inl (he.symm ▸ hpK))
  change 1 ≤ w x * boundedSlope K w (x + 1) - (1 - w x) * boundedSlope K w x + _
  rw [hd]
  linarith only [hc]

/-- With bounded slopes, a lost unit of comparison drift can only matter
near the minimum of the second group. -/
theorem weighted_comparisonMean_ge {p K θ : ℝ}
    (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1) (hK : 1 ≤ K) (hpK : 1 ≤ (2 * p - 1) * K)
    (hθ : 0 < θ) (m : ℕ) (U : Array N) (n : ℕ) {J : Finset (Fin N)} (hJ : J.Nonempty)
    (hnonneg : ∀ j ∈ J, 0 ≤ X p m U n j) (S : Finset ℤ) (ℓ : ℕ)
    (hnear : Xmin p m U J hJ n ∉ S → ∀ j ∈ J,
      (X p m U n j : ℝ) - (Xmin p m U J hJ n : ℝ) ≤ (ℓ : ℝ) →
      boundedSlope K (wA p m U n Jᶜ) (X p m U n j).toNat ≤ K - 2) :
    1 - (if Xmin p m U J hJ n ∈ S then (1 : ℝ) else 0) -
        (J.card : ℝ) * Real.exp (-θ * (ℓ : ℝ)) ≤
      ∑ j ∈ J, softMinimumWeight θ J (fun i => boundedHA p m K U n Jᶜ (X p m U n i)) j *
        comparisonMean p K m U n Jᶜ j := by
  let H := boundedHA p m K U n Jᶜ
  let v := Xmin p m U J hJ n
  let z (i : Fin N) := H (X p m U n i)
  have hH := monotone_boundedHA hp₀ hp₁ hK m U n Jᶜ
  have hmin (i : Fin N) (hi : i ∈ J) : v ≤ X p m U n i := Finset.inf'_le _ hi
  have hz : J.inf' hJ z = H v := by
    obtain ⟨i, hi, hv⟩ := Finset.exists_mem_eq_inf' hJ (X p m U n)
    change v = X p m U n i at hv
    exact le_antisymm ((Finset.inf'_le z hi).trans_eq (congrArg H hv.symm))
      (Finset.le_inf' _ _ (fun i hi => hH (hmin i hi)))
  have ha (i : Fin N) (hi : i ∈ J) :=
    comparisonMean_ge_of_J hp₀ hp₁ hK hpK m U n hi (hnonneg i hi)
  refine softMinimum_weighted_drift_lower hθ (by split <;> norm_num) hJ (fun i hi => (ha i hi).1) ?_
  intro i hi hdist
  by_cases hs : v ∈ S
  · rw [if_pos hs, sub_self]
    exact (ha i hi).1
  · rw [if_neg hs, sub_zero]
    apply (ha i hi).2
    apply hnear hs i hi
    rw [hz] at hdist
    exact (boundedPotential_sub_bounds hK (wA_pos p m U hp₀ n Jᶜ)
      (wA_le_one p m U hp₁ n Jᶜ) (hmin i hi)).1.trans hdist

end Swarming.Diameter
