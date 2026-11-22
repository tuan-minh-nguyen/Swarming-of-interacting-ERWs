import SwarmDiameter.BoundedGroupComparison
import SwarmDiameter.RecordBoundedSpatial
import SwarmDiameter.RecordWeightedMartingale

open Finset MeasureTheory
open Swarming.Uniform Swarming.Group Swarming.Trajectory
open SepGroup.Model SwarmJointDrift

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ} [Nonempty (Fin N)]

/-- Comparison potential for separated groups, with the bounded slopes
and the smooth minimum. -/
noncomputable def boundedGroupGap (p K θ : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (I J : Finset (Fin N)) : ℝ :=
  groupComparison θ I J (fun i => boundedHA p m K U n Jᶜ (X p m U n i))

/-- Mean increment of a comparison function with the environment fixed at
time `n`. -/
noncomputable def comparisonMean (p K : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) : ℝ :=
  let H := boundedHA p m K U n A
  let x := X p m U n i
  let α := SwarmCross.alphaFun p m n i U
  α * (H (x + 1) - H x) + (1 - α) * (H (x - 1) - H x)

private noncomputable def comparisonSlope (p K : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) : ℝ :=
  let H := boundedHA p m K U n A
  let x := X p m U n i
  (H (x + 1) - H (x - 1)) / 2

/-- Coefficients of the walkers' compensated steps in the separated-group
comparison. -/
noncomputable def boundedGroupCoeff (p K θ : ℝ) (m : ℕ) (I J : Finset (Fin N))
    (n : ℕ) (i : Fin N) (U : Array N) : ℝ :=
  let z (j : Fin N) := boundedHA p m K U n Jᶜ (X p m U n j)
  let c := comparisonSlope p K m U n Jᶜ i
  (if i ∈ I then c / (I.card : ℝ) else 0) -
    (if i ∈ J then softMinimumWeight θ J z i * c else 0)

private theorem comparison_step (p K : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (i : Fin N) :
    boundedHA p m K U n A (X p m U (n + 1) i) - boundedHA p m K U n A (X p m U n i) =
      comparisonMean p K m U n A i + comparisonSlope p K m U n A i * ExcOcc.martIncr p m n i U := by
  unfold comparisonMean comparisonSlope ExcOcc.martIncr
  change _ = _ + _ * (((X p m U (n + 1) i : ℤ) : ℝ) -
    ((X p m U n i : ℤ) : ℝ) - (2 * SwarmCross.alphaFun p m n i U - 1))
  rcases ExcOcc.traj_step p m U i n with h | h
  · change X p m U (n + 1) i = X p m U n i + 1 at h
    rw [h]
    push_cast
    ring
  · change X p m U (n + 1) i = X p m U n i - 1 at h
    rw [h]
    push_cast
    ring

omit [Nonempty (Fin N)] in
private theorem comparisonSlope_bounds {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) (i : Fin N) :
    0 ≤ comparisonSlope p K m U n A i ∧ comparisonSlope p K m U n A i ≤ K := by
  let x := X p m U n i
  have h := boundedPotential_sub_bounds hK (wA_pos p m U hp₀ n A)
    (wA_le_one p m U hp₁ n A) (show x - 1 ≤ x + 1 by omega)
  push_cast at h
  change (x : ℝ) + 1 - ((x : ℝ) - 1) ≤
    boundedHA p m K U n A (x + 1) - boundedHA p m K U n A (x - 1) ∧
    boundedHA p m K U n A (x + 1) - boundedHA p m K U n A (x - 1) ≤
      K * ((x : ℝ) + 1 - ((x : ℝ) - 1)) at h
  change 0 ≤ _ / 2 ∧ _ / 2 ≤ K
  constructor <;> nlinarith only [h.1, h.2]

omit [Nonempty (Fin N)] in
theorem abs_boundedGroupCoeff_le {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (θ : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (n : ℕ) (i : Fin N) (U : Array N) :
    |boundedGroupCoeff p K θ m I J n i U| ≤ 2 * K := by
  let z (j : Fin N) := boundedHA p m K U n Jᶜ (X p m U n j)
  let c := comparisonSlope p K m U n Jᶜ i
  obtain ⟨hc, hcK⟩ := comparisonSlope_bounds hp₀ hp₁ hK m U n Jᶜ i
  have hI₁ : (1 : ℝ) ≤ I.card := by exact_mod_cast Finset.card_pos.mpr hI
  have h₁ : |if i ∈ I then c / (I.card : ℝ) else 0| ≤ K := by
    split_ifs
    · rw [abs_of_nonneg (div_nonneg hc (by positivity))]
      exact (div_le_self hc hI₁).trans hcK
    · simp only [abs_zero]
      linarith
  have h₂ : |if i ∈ J then softMinimumWeight θ J z i * c else 0| ≤ K := by
    split_ifs with hi
    · have hw₀ := softMinimumWeight_nonneg θ hJ z
      have hw : softMinimumWeight θ J z i ≤ 1 :=
        (Finset.single_le_sum (fun j _ => hw₀ j) hi).trans_eq (sum_softMinimumWeight θ hJ z)
      rw [abs_of_nonneg (mul_nonneg (hw₀ i) hc)]
      exact (mul_le_of_le_one_left hc hw).trans hcK
    · simp only [abs_zero]
      linarith
  exact (abs_sub _ _).trans (by linarith only [h₁, h₂])

private theorem boundedGroupGap_succ_le_frozen {p K θ : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (hθ : 0 < θ) (m : ℕ) (U : Array N) (n : ℕ)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : SepSet p m n I J U) :
    boundedGroupGap p K θ m U (n + 1) I J ≤
      groupComparison θ I J (fun i => boundedHA p m K U n Jᶜ (X p m U (n + 1) i)) := by
  let H := boundedHA p m K U n Jᶜ
  let H' := boundedHA p m K U (n + 1) Jᶜ
  let x (i : Fin N) := X p m U (n + 1) i
  have hd : Monotone (fun y => H y - H' y) :=
    monotone_boundedPotential_sub hK (wA_pos p m U hp₀ n Jᶜ) (wA_le_one p m U hp₁ n Jᶜ)
      (wA_le_one p m U hp₁ (n + 1) Jᶜ) (wA_mono_time p m U hp₀ (Nat.le_succ n) Jᶜ)
  have hx (i : Fin N) (hi : i ∈ I) (j : Fin N) (hj : j ∈ J) : x j ≤ x i := by
    have hgap := hsep.2 i hi j hj
    have hjM := le_runMax p m U j n
    change (trajectory p m U (n + 1)).pos j ≤ (trajectory p m U (n + 1)).pos i
    change runMax p m U j n + 2 ≤ (trajectory p m U n).pos i at hgap
    rcases ExcOcc.traj_step p m U i n with h | h <;>
      rcases ExcOcc.traj_step p m U j n with h' | h' <;> omega
  have h := groupComparison_le_of_decrease hθ hI hJ
    (z := fun i => H (x i)) (d := fun i => H (x i) - H' (x i))
    (fun i hi j hj => hd (hx i hi j hj))
  change groupComparison θ I J (fun i => H' (x i)) ≤ _
  simpa only [sub_sub_cancel] using h

/-- The increment of the separated-group comparison is bounded by its
weighted one-step means plus the predictable martingale and the quadratic
error in the smooth minimum. -/
theorem boundedGroupGap_sub_le_means {p K θ : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (hθ : 0 < θ) (hθK : θ * K ≤ 1) (m : ℕ) (U : Array N) (n : ℕ)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : SepSet p m n I J U) :
    boundedGroupGap p K θ m U (n + 1) I J - boundedGroupGap p K θ m U n I J ≤
      average I (comparisonMean p K m U n Jᶜ) -
        (∑ j ∈ J, softMinimumWeight θ J (fun i => boundedHA p m K U n Jᶜ (X p m U n i)) j *
          comparisonMean p K m U n Jᶜ j) + θ * K ^ 2 +
          weightedJump p m (boundedGroupCoeff p K θ m I J) n U := by
  let H := boundedHA p m K U n Jᶜ
  let z (i : Fin N) := H (X p m U n i)
  let u (i : Fin N) := H (X p m U (n + 1) i) - z i
  let M (i : Fin N) := ExcOcc.martIncr p m n i U
  let d := comparisonMean p K m U n Jᶜ
  let c := comparisonSlope p K m U n Jᶜ
  let w := softMinimumWeight θ J z
  have hu (j : Fin N) : |u j| ≤ K := by
    have h (x : ℤ) : 1 ≤ H (x + 1) - H x ∧ H (x + 1) - H x ≤ K :=
      boundedPotential_add_one_bounds hK (wA_pos p m U hp₀ n Jᶜ)
        (wA_le_one p m U hp₁ n Jᶜ) x
    change |H (X p m U (n + 1) j) - H (X p m U n j)| ≤ K
    rcases ExcOcc.traj_step p m U j n with hstep | hstep
    · change X p m U (n + 1) j = X p m U n j + 1 at hstep
      have hh := h (X p m U n j)
      rw [hstep, abs_of_nonneg (zero_le_one.trans hh.1)]
      exact hh.2
    · change X p m U (n + 1) j = X p m U n j - 1 at hstep
      have hh := h (X p m U n j - 1)
      rw [sub_add_cancel] at hh
      rw [hstep, abs_sub_comm, abs_of_nonneg (zero_le_one.trans hh.1)]
      exact hh.2
  have hsub := groupComparison_sub_le hθ hθK I hJ (z := z) (u := u) (fun j _ => hu j)
  have hnew : (fun i => z i + u i) = fun i => H (X p m U (n + 1) i) := by
    funext i
    dsimp only [u]
    ring
  rw [hnew] at hsub
  have hfreeze := boundedGroupGap_succ_le_frozen hp₀ hp₁ hK hθ m U n hI hJ hsep
  have he : u = fun i => d i + c i * M i := by
    funext i
    exact comparison_step p K m U n Jᶜ i
  have hnoise :
      weightedJump p m (boundedGroupCoeff p K θ m I J) n U =
        average I (fun i => c i * M i) - ∑ j ∈ J, w j * (c j * M j) := by
    change (∑ i, ((if i ∈ I then c i / (I.card : ℝ) else 0) -
      (if i ∈ J then w i * c i else 0)) * M i) = _
    simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
      mul_assoc, ← Finset.sum_filter]
    rw [show Finset.univ.filter (fun i => i ∈ I) = I by simp,
      show Finset.univ.filter (fun i => i ∈ J) = J by simp]
    rw [Swarming.Group.average, ← Finset.sum_div]
  rw [he, SepGroup.Model.average_add] at hsub
  have hw : (∑ j ∈ J, w j * (d j + c j * M j)) =
      (∑ j ∈ J, w j * d j) + ∑ j ∈ J, w j * (c j * M j) := by
    simp only [mul_add, Finset.sum_add_distrib]
  change _ ≤ average I d - (∑ j ∈ J, w j * d j) + θ * K ^ 2 + _
  change groupComparison θ I J (fun i => H (X p m U (n + 1) i)) - boundedGroupGap p K θ m U n I J ≤
    _ - (∑ j ∈ J, w j * (d j + c j * M j)) + θ * K ^ 2 at hsub
  rw [hw] at hsub
  rw [hnoise]
  linarith only [hfreeze, hsub]

end Swarming.Diameter
