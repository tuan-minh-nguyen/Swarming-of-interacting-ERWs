import Swarm.Reflect.Choose
import SwarmDiameter.BinomialEndpoint

open Finset
open SwarmReflect

namespace Swarming.Diameter

variable {n : ℕ}

/-- Reflection at `b` counts paths which hit `b` and end at `a < b`. -/
theorem card_reach_endpoint {a b : ℤ} (hb : 1 ≤ b) (ha : a < b) :
    (univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n ∧ psum ω n = a).card =
      (univ.filter fun ω : Fin n → Bool => psum ω n = 2 * b - a).card := by
  apply Finset.card_bij'
    (i := fun ω _ => reflect ω b) (j := fun ω _ => reflect ω b)
  · intro ω h
    obtain ⟨hr, he⟩ := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨mem_univ _, by rw [psum_reflect_end ω hb hr, he]⟩
  · intro ω h
    have he := (Finset.mem_filter.mp h).2
    have hr : b ≤ rmax ω n := le_rmax_of_psum ω le_rfl (by omega)
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _, le_rmax_reflect ω hb hr, ?_⟩
    rw [psum_reflect_end ω hb hr, he]
    omega
  · intro ω h
    exact reflect_reflect ω hb (Finset.mem_filter.mp h).2.1
  · intro ω h
    have he := (Finset.mem_filter.mp h).2
    exact reflect_reflect ω hb (le_rmax_of_psum ω le_rfl (by omega))

/-- The paths staying below the barrier and the reflected paths partition the
endpoint count in the reflection formula. -/
theorem card_below_endpoint_add_reflected {a b : ℤ} (hb : 1 ≤ b) (ha : a < b) :
    (univ.filter fun ω : Fin n → Bool => rmax ω n < b ∧ psum ω n = a).card +
      (univ.filter fun ω : Fin n → Bool => psum ω n = 2 * b - a).card =
        (univ.filter fun ω : Fin n → Bool => psum ω n = a).card := by
  rw [← card_reach_endpoint hb ha]
  have h := Finset.card_filter_add_card_filter_not
    (s := univ.filter fun ω : Fin n → Bool => psum ω n = a) (fun ω => rmax ω n < b)
  simpa only [filter_filter, not_lt, and_comm] using h

private theorem cube_add_square_even (L : ℕ) : (L ^ 3 + L ^ 2) % 2 = 0 := by
  rw [Nat.add_mod, Nat.pow_mod L 3 2, Nat.pow_mod L 2 2]
  rcases Nat.mod_two_eq_zero_or_one L with h | h <;> simp [h]

/-- Counting symmetric walks of length `L³` that stay above `-L` and end at
`L²`, after negating the path. -/
theorem exp_neg_le_card_reflection_excursion {L : ℕ} (hL : 8 ≤ L) :
    let n := L ^ 3
    (1 - Real.exp (-1)) * (Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ n) ≤
      ((n : ℝ) + 1) *
        ((univ.filter fun ω : Fin n → Bool =>
          rmax ω n < (L : ℤ) ∧ psum ω n = -((L ^ 2 : ℕ) : ℤ)).card : ℝ) := by
  let n := L ^ 3
  let d := L ^ 2
  let k := (n + d) / 2
  let C := (univ.filter fun ω : Fin n → Bool =>
    rmax ω n < (L : ℤ) ∧ psum ω n = -(d : ℤ)).card
  change (1 - Real.exp (-1)) * (Real.exp (-8 * (L : ℝ)) * (2 : ℝ) ^ n) ≤
    ((n : ℝ) + 1) * (C : ℝ)
  have hmod : (n + d) % 2 = 0 := cube_add_square_even L
  have hk : 2 * k = n + d := by dsimp only [k]; omega
  have hz : 2 * (k : ℤ) = (n : ℤ) + (d : ℤ) := by exact_mod_cast hk
  have h₁ := card_psum_eq_choose (n := n) k
  have h₂ := card_psum_eq_choose (n := n) (k + L)
  rw [show 2 * (k : ℤ) - (n : ℤ) = (d : ℤ) by omega] at h₁
  have hcast : ((k + L : ℕ) : ℤ) = (k : ℤ) + (L : ℤ) := by exact_mod_cast rfl
  rw [hcast, show 2 * ((k : ℤ) + (L : ℤ)) - (n : ℤ) =
    2 * (L : ℤ) - (-(d : ℤ)) by omega] at h₂
  have hsplit := card_below_endpoint_add_reflected (n := n) (a := -(d : ℤ)) (b := L)
    (by exact_mod_cast (show 1 ≤ L by omega)) (by omega)
  rw [card_eq_neg, h₁, h₂] at hsplit
  have heq : C + n.choose (k + L) = n.choose k := hsplit
  have heqR : (C : ℝ) + (n.choose (k + L) : ℝ) = (n.choose k : ℝ) := by exact_mod_cast heq
  rw [show (C : ℝ) = (n.choose k : ℝ) - (n.choose (k + L) : ℝ) by linarith]
  exact exp_neg_le_binomial_difference_mul hL

end Swarming.Diameter
