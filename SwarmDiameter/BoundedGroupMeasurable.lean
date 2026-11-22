import SwarmDiameter.BoundedGroupStep

open Finset MeasureTheory
open Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SepGroup.Model

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ}

private theorem measurable_boundedSlope_wA (p K : ℝ) (m n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    Measurable[enlFilt p m n] (fun U : Array N => boundedSlope K (wA p m U n A) x) := by
  let _ : MeasurableSpace (Array N) := enlFilt (N := N) p m n
  have hw (j : ℕ) : Measurable (fun U : Array N => wA p m U n A j) :=
    (SwarmM3.measurable_wA_posFilt p m n A j).mono (posFilt_le_enlFilt p m n) le_rfl
  induction x with
  | zero => exact measurable_const
  | succ x ih =>
    simp only [boundedSlope]
    exact measurable_const.min ((measurable_const.add ((measurable_const.sub (hw x)).mul ih)).div (hw x))

private theorem measurable_boundedHA_random_site (p K : ℝ) (m n : ℕ) (A : Finset (Fin N))
    {Y : Array N → ℤ} (hY : Measurable[enlFilt p m n] Y) :
    Measurable[enlFilt p m n] (fun U => boundedHA p m K U n A (Y U)) := by
  let _ : MeasurableSpace (Array N) := enlFilt (N := N) p m n
  have hH : Measurable (fun a : Array N × ℤ => boundedHA p m K a.1 n A a.2) := by
    apply measurable_from_prod_countable_left
    intro x
    by_cases hx : x < 0
    · simp only [boundedHA, boundedPotential, if_pos hx]
      exact measurable_const
    · simp only [boundedHA, boundedPotential, if_neg hx]
      exact Finset.measurable_sum _ (fun j _ => measurable_boundedSlope_wA p K m n A (j + 1))
  exact hH.comp (measurable_id.prodMk hY)

/-- The coefficients of the bounded group comparison are predictable. -/
theorem measurable_boundedGroupCoeff (p K θ : ℝ) (m : ℕ) (I J : Finset (Fin N)) (n : ℕ) (i : Fin N) :
    Measurable[enlFilt p m n] (boundedGroupCoeff p K θ m I J n i) := by
  let _ : MeasurableSpace (Array N) := enlFilt (N := N) p m n
  let H (U : Array N) := boundedHA p m K U n Jᶜ
  let x (j : Fin N) (U : Array N) := X p m U n j
  let z (j : Fin N) (U : Array N) := H U (x j U)
  let c (U : Array N) := (H U (x i U + 1) - H U (x i U - 1)) / 2
  have hx (j : Fin N) : Measurable (x j) := enl_pos_measurable p m n le_rfl j
  have hz (j : Fin N) : Measurable (z j) := measurable_boundedHA_random_site p K m n Jᶜ (hx j)
  have hc : Measurable c :=
    ((measurable_boundedHA_random_site p K m n Jᶜ ((hx i).add measurable_const)).sub
      (measurable_boundedHA_random_site p K m n Jᶜ ((hx i).sub measurable_const))).div_const 2
  have he (j : Fin N) : Measurable (fun U => Real.exp (-θ * z j U)) :=
    Real.measurable_exp.comp ((hz j).const_mul (-θ))
  have hw : Measurable (fun U => softMinimumWeight θ J (fun j => z j U) i) := by
    change Measurable (fun U => Real.exp (-θ * z i U) / ∑ j ∈ J, Real.exp (-θ * z j U))
    exact (he i).div (Finset.measurable_sum _ fun j _ => he j)
  change Measurable (fun U =>
    (if i ∈ I then c U / (I.card : ℝ) else 0) -
      (if i ∈ J then softMinimumWeight θ J (fun j => z j U) i * c U else 0))
  apply Measurable.sub
  · by_cases hi : i ∈ I
    · simp only [if_pos hi]
      exact hc.div_const _
    · simp only [if_neg hi]
      exact measurable_const
  · by_cases hi : i ∈ J
    · simp only [if_pos hi]
      exact hw.mul hc
    · simp only [if_neg hi]
      exact measurable_const

end Swarming.Diameter
