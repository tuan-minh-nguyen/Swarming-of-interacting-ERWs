/-
# The law of the running maximum of a simple symmetric walk

Combining the reflection bijection of `Reflect.Main` with elementary cardinality
algebra, this module proves

* `card_rmax_ge`      : `#{max ≥ b} = #{S_n ≥ b} + #{S_n > b}`,
* `card_rmax_lt`      : `#{max < b} = #{S_n = b} + #{|S_n| < b}`,
* `card_rmax_ge_le`   : `#{max ≥ b} ≤ 2 · #{S_n ≥ b}`,
* `card_rmax_lt_le`   : `#{max < b} ≤ 2b · #{S_n = b}`-flavoured bounds.

These are the combinatorial form of the reflection principle used, in the paper,
to force a simple symmetric walk above every fixed level.
-/
import Swarm.Imports
import Swarm.Reflect.Basic
import Swarm.Reflect.Main

open Finset

namespace SwarmReflect

open Classical

variable {n : ℕ}

/-! ## Splitting the endpoint conditions -/

theorem card_ge_split {b : ℤ} :
    (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n).card
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n).card := by
  have heq : (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n)
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b)
        ∪ (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'.symm
    · rintro (h | h) <;> omega
  have hdisj : Disjoint (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b)
      (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    omega
  conv_lhs => rw [heq]
  rw [Finset.card_union_of_disjoint hdisj]

theorem card_lt_split {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < b).card
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = -b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b).card := by
  have hBC : Disjoint (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b)
      (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    rw [abs_lt] at h1'
    omega
  have hA : Disjoint (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = -b)
      ((Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b)
        ∪ (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b)) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    rcases Finset.mem_union.mp h2 with h2' | h2'
    · have := (Finset.mem_filter.mp h2').2
      rw [abs_lt] at this
      omega
    · have := (Finset.mem_filter.mp h2').2
      omega
  have hD : (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < b)
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = -b)
        ∪ ((Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b)
          ∪ (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, abs_lt]
    constructor
    · intro h
      by_cases h2 : psum ω n = -b
      · exact Or.inl h2
      · refine Or.inr ?_
        by_cases h3 : -b < psum ω n
        · exact Or.inl ⟨h3, h⟩
        · exact Or.inr (by omega)
    · rintro (h | ⟨h | h⟩) <;> omega
  conv_lhs => rw [hD]
  rw [Finset.card_union_of_disjoint hA, Finset.card_union_of_disjoint hBC, add_assoc]

/-- The two endpoints symmetric about `0` are equinumerous. -/
theorem card_eq_neg {b : ℤ} :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = -b).card
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b).card := by
  apply Finset.card_bij'
    (i := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => psum ω n = -b) => negate ω)
    (j := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b) => negate ω)
  · intro ω hω
    have h : psum ω n = -b := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; omega⟩
  · intro ω hω
    have h : psum ω n = b := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; omega⟩
  · intro ω _; exact negate_negate ω
  · intro ω _; exact negate_negate ω

/-- The two strict endpoint tails symmetric about `0` are equinumerous. -/
theorem card_lt_neg {b : ℤ} :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b).card
      = (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n).card := by
  apply Finset.card_bij'
    (i := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => psum ω n < -b) => negate ω)
    (j := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n) => negate ω)
  · intro ω hω
    have h : psum ω n < -b := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; omega⟩
  · intro ω hω
    have h : b < psum ω n := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; omega⟩
  · intro ω _; exact negate_negate ω
  · intro ω _; exact negate_negate ω

theorem card_rmax_lt_add_ge {b : ℤ} :
    (Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n).card
      = (Finset.univ : Finset (Fin n → Bool)).card :=
  card_filter_lt_add_ge (n := n) (f := fun ω : Fin n → Bool => rmax ω n) (b := b)

theorem card_psum_lt_add_ge {b : ℤ} :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n < b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n).card
      = (Finset.univ : Finset (Fin n → Bool)).card :=
  card_filter_lt_add_ge (n := n) (f := fun ω : Fin n → Bool => psum ω n) (b := b)

/-! ## The main counting identities -/

/-- **Law of the running maximum.** For `b ≥ 1`, the number of step sequences of
length `n` that never reach `b` equals `#{S_n = b} + #{|S_n| < b}`. -/
theorem card_rmax_lt {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < b).card
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b).card := by
  have hA := card_rmax_ge (n := n) hb
  have hBg := card_ge_split (n := n) (b := b)
  have hS := card_lt_split (n := n) (b := b) hb
  have hF := card_eq_neg (n := n) (b := b)
  have hG := card_lt_neg (n := n) (b := b)
  have hM := card_rmax_lt_add_ge (n := n) (b := b)
  have hP := card_psum_lt_add_ge (n := n) (b := b)
  omega

/-- The running maximum reaches `b` at most twice as often as `S_n ≥ b`. -/
theorem card_rmax_ge_le {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n).card
      ≤ 2 * (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n).card := by
  have hA := card_rmax_ge (n := n) hb
  have hle : (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n).card
      ≤ (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n).card := by
    apply Finset.card_le_card
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, by omega⟩
  omega

/-- Fewer than `2b` of the endpoints in `{-b, …, b}` can be attained below `b`. -/
theorem card_rmax_lt_le {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < b).card
      ≤ (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b).card
        + ∑ k ∈ Finset.Icc (1 - b) (b - 1),
            (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k).card := by
  have hmain := card_rmax_lt (n := n) hb
  rw [hmain]
  have hsplit : (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b).card
      ≤ ∑ k ∈ Finset.Icc (1 - b) (b - 1),
          (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k).card := by
    have hpartition : (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b)
        = (Finset.Icc (1 - b) (b - 1)).biUnion
            (fun k => Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_Icc, abs_lt]
      constructor
      · intro h
        exact ⟨psum ω n, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨k, ⟨h1, h2⟩, hk⟩
        omega
    rw [hpartition]
    exact Finset.card_biUnion_le
  omega

end SwarmReflect
