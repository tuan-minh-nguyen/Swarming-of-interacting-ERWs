import SwarmDiameter.SoftMinimum
import Swarm.SepGroup

open Finset
open Swarming.Group

namespace Swarming.Diameter

set_option autoImplicit false

variable {ι : Type*}

/-- The average over the first group minus the smooth minimum over the second. -/
noncomputable def groupComparison (θ : ℝ) (I J : Finset ι) (z : ι → ℝ) : ℝ :=
  average I z - softMinimum θ J z

theorem group_average_const {I : Finset ι} (hI : I.Nonempty) (c : ℝ) :
    average I (fun _ => c) = c := by
  have hpos : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr hI
  rw [average, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀ _ hpos.ne']

theorem groupComparison_sub_le {θ K : ℝ} (hθ : 0 < θ) (hK : θ * K ≤ 1)
    (I : Finset ι) {J : Finset ι} (hJ : J.Nonempty) {z u : ι → ℝ}
    (hu : ∀ j ∈ J, |u j| ≤ K) :
    groupComparison θ I J (fun i => z i + u i) - groupComparison θ I J z ≤
      average I u - (∑ j ∈ J, softMinimumWeight θ J z j * u j) + θ * K ^ 2 := by
  have h := softMinimum_sub_ge_weighted_sum hθ hK hJ (z := z) hu
  unfold groupComparison
  rw [SepGroup.Model.average_add]
  linarith only [h]

theorem groupComparison_le_of_decrease {θ : ℝ} (hθ : 0 < θ)
    {I J : Finset ι} (hI : I.Nonempty) (hJ : J.Nonempty)
    {z d : ι → ℝ} (hd : ∀ i ∈ I, ∀ j ∈ J, d j ≤ d i) :
    groupComparison θ I J (fun i => z i - d i) ≤ groupComparison θ I J z := by
  let M := maximumOn J hJ d
  have hdI (i : ι) (hi : i ∈ I) : M ≤ d i :=
    Finset.sup'_le hJ d (fun j hj => hd i hi j hj)
  have hdJ (j : ι) (hj : j ∈ J) : d j ≤ M := Finset.le_sup' d hj
  have h₁ : average I (fun i => z i - d i) ≤ average I z - M := by
    have h := SepGroup.Model.average_mono (s := I)
      (fun i hi => sub_le_sub_left (hdI i hi) (z i))
    calc
      _ ≤ average I (fun i => z i + -M) := by simpa only [sub_eq_add_neg] using h
      _ = _ := by rw [SepGroup.average_add_const hI]; ring
  have h₂ : softMinimum θ J z - M ≤ softMinimum θ J (fun i => z i - d i) := by
    have h := softMinimum_mono hθ hJ
      (z := fun i => z i + -M) (w := fun i => z i - d i)
      (fun j hj => by simpa only [sub_eq_add_neg] using sub_le_sub_left (hdJ j hj) (z j))
    rw [softMinimum_add_const hθ hJ] at h
    linarith only [h]
  unfold groupComparison
  linarith only [h₁, h₂]

theorem groupComparison_le_of_bounds {θ : ℝ} (hθ : 0 < θ)
    {I J : Finset ι} (hI : I.Nonempty) (hJ : J.Nonempty)
    {z : ι → ℝ} {a b : ℝ} (ha : ∀ j ∈ J, a ≤ z j) (hb : ∀ i ∈ I, z i ≤ b) :
    groupComparison θ I J z ≤ b - a + Real.log (J.card : ℝ) / θ := by
  have h₁ := SepGroup.Model.average_mono (s := I) hb
  rw [group_average_const hI] at h₁
  have h₂ := (softMinimum_bounds hθ hJ z).1
  have h₃ : a ≤ J.inf' hJ z := Finset.le_inf' _ _ ha
  unfold groupComparison
  linarith only [h₁, h₂, h₃]

theorem le_groupComparison_of_bounds {θ : ℝ} (hθ : 0 < θ)
    {I J : Finset ι} (hI : I.Nonempty) (hJ : J.Nonempty) {z : ι → ℝ} {a b : ℝ}
    (ha : ∃ j ∈ J, z j ≤ a) (hb : ∀ i ∈ I, b ≤ z i) :
    b - a ≤ groupComparison θ I J z := by
  have h₁ := SepGroup.Model.average_mono (s := I) hb
  rw [group_average_const hI] at h₁
  obtain ⟨j, hj, hz⟩ := ha
  have h₂ := (softMinimum_bounds hθ hJ z).2.trans ((Finset.inf'_le z hj).trans hz)
  unfold groupComparison
  linarith only [h₁, h₂]

end Swarming.Diameter
