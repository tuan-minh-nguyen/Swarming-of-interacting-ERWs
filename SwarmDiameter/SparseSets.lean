import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace Swarming.Diameter

set_option autoImplicit false

private theorem sum_powerset_pow_card {ι : Type*} [DecidableEq ι] (I : Finset ι) (x : ℝ) :
    (∑ S ∈ I.powerset, x ^ S.card) = (1 + x) ^ I.card := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ, Finset.sum_powerset_insert ha]
    have he : (∑ S ∈ I.powerset, x ^ (insert a S).card) =
        (∑ S ∈ I.powerset, x ^ S.card) * x := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.card_insert_of_notMem (fun h => ha ((Finset.mem_powerset.mp hS) h)), pow_succ]
    rw [he, ih]
    ring

theorem card_small_subsets_le_exp {ι : Type*} (I : Finset ι)
    {θ d : ℝ} (hθ : 0 ≤ θ) :
    (((I.powerset.filter fun S => (S.card : ℝ) ≤ d).card : ℕ) : ℝ) ≤
      Real.exp (θ * d + (I.card : ℝ) * Real.exp (-θ)) := by
  classical
  let Q := I.powerset.filter fun S => (S.card : ℝ) ≤ d
  let x := Real.exp (-θ)
  calc
    (Q.card : ℝ) = ∑ _ ∈ Q, (1 : ℝ) := by simp
    _ ≤ ∑ S ∈ Q, Real.exp (θ * d) * x ^ S.card := by
      refine Finset.sum_le_sum fun S hS => ?_
      have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hS).2 hθ
      dsimp only [x]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by nlinarith only [h])
    _ ≤ ∑ S ∈ I.powerset, Real.exp (θ * d) * x ^ S.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun S _ _ => by positivity)
    _ = Real.exp (θ * d) * (1 + x) ^ I.card := by rw [← Finset.mul_sum, sum_powerset_pow_card]
    _ ≤ Real.exp (θ * d) * (Real.exp x) ^ I.card := by
      have hx : 1 + x ≤ Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- A sufficiently small linear bound on cardinality permits a union bound
over all subsets of an interval with at most linearly many sites. -/
theorem exists_small_subsets_card_le {D c : ℝ} (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {ι : Type} (I : Finset ι) {L : ℝ}, 0 ≤ L → (I.card : ℝ) ≤ D * L →
      (((I.powerset.filter fun S => (S.card : ℝ) ≤ δ * L).card : ℕ) : ℝ) ≤
        Real.exp (c / 2 * L) := by
  let θ := 4 * D / c + 1
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  let δ := c / (4 * θ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hbound : D * Real.exp (-θ) ≤ c / 4 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have hx : 4 * D / c ≤ Real.exp θ := by
      have he := Real.add_one_le_exp θ
      dsimp only [θ] at he ⊢
      linarith only [he]
    have he := (div_le_iff₀ hc).mp hx
    linarith only [he]
  refine ⟨δ, hδ, ?_⟩
  intro ι I L hL hI
  refine (card_small_subsets_le_exp I hθ.le).trans (Real.exp_le_exp.mpr ?_)
  have he : θ * δ = c / 4 := by dsimp only [δ]; field_simp
  have h₁ := mul_le_mul_of_nonneg_right hI (Real.exp_pos (-θ)).le
  have h₂ := mul_le_mul_of_nonneg_right hbound hL
  rw [← mul_assoc, he]
  nlinarith only [h₁, h₂]

end Swarming.Diameter
