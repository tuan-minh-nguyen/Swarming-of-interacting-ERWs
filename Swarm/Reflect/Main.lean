/-
# The reflection principle: bijection and cardinality form

Building on `Reflect.Basic`, this module proves the classical reflection bijection
for a simple symmetric random walk on `Fin n → Bool`:

  the paths that reach the level `b` but end below it are in explicit bijection
  with the paths that end strictly above `b`,

and derives the exact counting identities

  `#{max ≥ b} = #{S_n ≥ b} + #{S_n > b}`,
  `#{max < b} = #{S_n = b} + #{|S_n| < b}`.

The bijection reflects a path after its first visit to `b`. The first visit is
`firstHitOf ω b`, a total function of the path and the level (it returns `0` when
the level is never visited), which keeps every statement free of proof arguments.
Involutivity is `reflect_reflect`.
-/
import Swarm.Imports
import Swarm.Reflect.Basic

open Finset

namespace SwarmReflect

open Classical

variable {n : ℕ}

/-! ## First passage time of a level -/

/-- The first index at which the walk reaches `b` (`0` if it never does). -/
noncomputable def firstHitOf (ω : Fin n → Bool) (b : ℤ) : ℕ :=
  if h : ∃ j, psum ω j = b then Nat.find h else 0

theorem firstHitOf_eq (ω : Fin n → Bool) {b : ℤ} (h : ∃ j, psum ω j = b) :
    firstHitOf ω b = Nat.find h :=
  dif_pos h

theorem firstHitOf_spec (ω : Fin n → Bool) {b : ℤ} (h : ∃ j, psum ω j = b) :
    psum ω (firstHitOf ω b) = b := by
  rw [firstHitOf_eq ω h]
  exact Nat.find_spec h

theorem firstHitOf_min (ω : Fin n → Bool) {b : ℤ} (h : ∃ j, psum ω j = b) {j : ℕ}
    (hj : j < firstHitOf ω b) : psum ω j ≠ b := by
  rw [firstHitOf_eq ω h] at hj
  exact Nat.find_min h hj

theorem firstHitOf_le (ω : Fin n → Bool) {b : ℤ} (h : ∃ j, psum ω j = b) {m : ℕ}
    (hm : psum ω m = b) : firstHitOf ω b ≤ m := by
  rw [firstHitOf_eq ω h]
  exact Nat.find_le hm

/-- The first passage time of a level reached by the running maximum is at most `n`. -/
theorem firstHitOf_le_of_le_rmax (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b)
    (h : b ≤ rmax ω n) : firstHitOf ω b ≤ n := by
  obtain ⟨j, hjn, hj⟩ := exists_hit_le ω hb h
  exact le_trans (firstHitOf_le ω (exists_psum_eq_rmax ω hb h) hj) hjn

/-! ## The reflection map -/

/-- Reflect the path after its first visit to `b`. -/
noncomputable def reflect (ω : Fin n → Bool) (b : ℤ) : Fin n → Bool :=
  flipTail (firstHitOf ω b) ω

theorem reflect_def (ω : Fin n → Bool) (b : ℤ) :
    reflect ω b = flipTail (firstHitOf ω b) ω := rfl

/-- The reflection leaves the partial sums up to the first passage time unchanged. -/
theorem psum_reflect_le (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) {k : ℕ}
    (hk : k ≤ firstHitOf ω b) (hkn : k ≤ n) : psum (reflect ω b) k = psum ω k :=
  psum_flipTail_le ω hk hkn

/-- The reflected path reaches `b` at the same time. -/
theorem psum_reflect_self (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) :
    psum (reflect ω b) (firstHitOf ω b) = b := by
  have htn := firstHitOf_le_of_le_rmax ω hb h
  show psum (flipTail (firstHitOf ω b) ω) (firstHitOf ω b) = b
  rw [psum_flipTail_self ω htn]
  exact firstHitOf_spec ω (exists_psum_eq_rmax ω hb h)

/-- **Reflection identity.** The reflected path ends at the mirror image of the
original endpoint. -/
theorem psum_reflect_end (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) :
    psum (reflect ω b) n = 2 * b - psum ω n := by
  have htn := firstHitOf_le_of_le_rmax ω hb h
  show psum (flipTail (firstHitOf ω b) ω) n = 2 * b - psum ω n
  rw [psum_flipTail_end ω htn, firstHitOf_spec ω (exists_psum_eq_rmax ω hb h)]

/-- The reflection of a path whose maximum reaches `b` still has maximum at least `b`. -/
theorem le_rmax_reflect (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) :
    b ≤ rmax (reflect ω b) n := by
  have htn := firstHitOf_le_of_le_rmax ω hb h
  refine le_rmax_of_psum (reflect ω b) (j := firstHitOf ω b) htn ?_
  rw [psum_reflect_self ω hb h]

/-- The first passage time of a level is unchanged by reflection. -/
theorem firstHitOf_reflect (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) :
    firstHitOf (reflect ω b) b = firstHitOf ω b := by
  have htn := firstHitOf_le_of_le_rmax ω hb h
  have hb' : b ≤ rmax (reflect ω b) n := le_rmax_reflect ω hb h
  have hspec : psum (reflect ω b) (firstHitOf ω b) = b := psum_reflect_self ω hb h
  have h₁ : firstHitOf (reflect ω b) b ≤ firstHitOf ω b :=
    firstHitOf_le (reflect ω b) (exists_psum_eq_rmax (reflect ω b) hb hb') hspec
  have h₂ : ¬ firstHitOf (reflect ω b) b < firstHitOf ω b := by
    intro hlt
    have hspec2 : psum (reflect ω b) (firstHitOf (reflect ω b) b) = b :=
      firstHitOf_spec (reflect ω b) (exists_psum_eq_rmax (reflect ω b) hb hb')
    have hle : firstHitOf (reflect ω b) b ≤ firstHitOf ω b := le_of_lt hlt
    have heq : psum (reflect ω b) (firstHitOf (reflect ω b) b)
        = psum ω (firstHitOf (reflect ω b) b) :=
      psum_reflect_le ω hb h hle (le_trans hle htn)
    rw [heq] at hspec2
    exact firstHitOf_min ω (exists_psum_eq_rmax ω hb h) hlt hspec2
  omega

/-- **The reflection is an involution.** -/
theorem reflect_reflect (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n) :
    reflect (reflect ω b) b = ω := by
  have hmain : firstHitOf (reflect ω b) b = firstHitOf ω b := firstHitOf_reflect ω hb h
  have h₁ : reflect (reflect ω b) b = flipTail (firstHitOf ω b) (reflect ω b) := by
    show flipTail (firstHitOf (reflect ω b) b) (reflect ω b) = _
    rw [hmain]
  rw [h₁]
  show flipTail (firstHitOf ω b) (flipTail (firstHitOf ω b) ω) = ω
  exact flipTail_flipTail _ ω

/-- The reflected path ends above `b`. -/
theorem reflect_end_gt (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n)
    (hlt : psum ω n < b) : b < psum (reflect ω b) n := by
  rw [psum_reflect_end ω hb h]
  omega

/-- The reflected path ends below `b`. -/
theorem reflect_end_lt (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b) (h : b ≤ rmax ω n)
    (hgt : b < psum ω n) : psum (reflect ω b) n < b := by
  rw [psum_reflect_end ω hb h]
  omega

/-! ## The reflection bijection -/

/-- **Reflection bijection.** For `b ≥ 1`, reflecting after the first visit to `b`
bijects the paths that reach `b` but end below it with the paths that end above `b`. -/
theorem card_reach_and_below {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n ∧ ¬ b ≤ psum ω n).card
      = (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n).card := by
  apply Finset.card_bij'
    (i := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n ∧ ¬ b ≤ psum ω n) =>
      reflect ω b)
    (j := fun (ω : Fin n → Bool)
      (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n) =>
      reflect ω b)
  · intro ω hω
    have hb' : b ≤ rmax ω n := (Finset.mem_filter.mp hω).2.1
    have hlt : psum ω n < b := by
      have := (Finset.mem_filter.mp hω).2.2
      omega
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, reflect_end_gt ω hb hb' hlt⟩
  · intro ω hω
    have hgt : b < psum ω n := (Finset.mem_filter.mp hω).2
    have hb' : b ≤ rmax ω n := le_rmax_of_psum ω le_rfl (by omega)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_rmax_reflect ω hb hb', ?_⟩
    have := reflect_end_lt ω hb hb' hgt
    omega
  · intro ω hω
    exact reflect_reflect ω hb (Finset.mem_filter.mp hω).2.1
  · intro ω hω
    exact reflect_reflect ω hb (le_rmax_of_psum ω le_rfl (by
      have := (Finset.mem_filter.mp hω).2
      omega))

/-! ## Cardinality algebra -/

theorem card_filter_lt_add_ge {f : (Fin n → Bool) → ℤ} {b : ℤ} :
    (Finset.univ.filter fun ω => f ω < b).card + (Finset.univ.filter fun ω => b ≤ f ω).card
      = (Finset.univ : Finset (Fin n → Bool)).card := by
  have hdisj : Disjoint (Finset.univ.filter fun ω : Fin n → Bool => f ω < b)
      (Finset.univ.filter fun ω : Fin n → Bool => b ≤ f ω) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    omega
  have hun : (Finset.univ.filter fun ω : Fin n → Bool => f ω < b)
      ∪ (Finset.univ.filter fun ω : Fin n → Bool => b ≤ f ω) = Finset.univ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => by omega⟩
  conv_rhs => rw [← hun]
  rw [Finset.card_union_of_disjoint hdisj]

/-- Negating the walk preserves cardinalities of endpoint conditions. -/
theorem card_filter_neg (P : ℤ → Prop) :
    (Finset.univ.filter fun ω : Fin n → Bool => P (-psum ω n)).card
      = (Finset.univ.filter fun ω : Fin n → Bool => P (psum ω n)).card := by
  apply Finset.card_bij'
    (i := fun (ω : Fin n → Bool) (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => P (-psum ω n)) =>
      negate ω)
    (j := fun (ω : Fin n → Bool) (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => P (psum ω n)) =>
      negate ω)
  · intro ω hω
    have h := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; simpa using h⟩
  · intro ω hω
    have h := (Finset.mem_filter.mp hω).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [psum_negate]; simpa using h⟩
  · intro ω _
    exact negate_negate ω
  · intro ω _
    exact negate_negate ω

/-- The number of paths whose maximum reaches `b` equals
`#{S_n ≥ b} + #{S_n > b}`. -/
theorem card_rmax_ge {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n).card
      = (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n).card
        + (Finset.univ.filter fun ω : Fin n → Bool => b < psum ω n).card := by
  have hunion : (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n)
      = (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n)
        ∪ (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n ∧ ¬ b ≤ psum ω n) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_cases h2 : b ≤ psum ω n
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
    · rintro (h | ⟨h, _⟩)
      · exact le_rmax_of_psum ω le_rfl h
      · exact h
  have hdisj : Disjoint (Finset.univ.filter fun ω : Fin n → Bool => b ≤ psum ω n)
      (Finset.univ.filter fun ω : Fin n → Bool => b ≤ rmax ω n ∧ ¬ b ≤ psum ω n) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2
  rw [hunion, Finset.card_union_of_disjoint hdisj, card_reach_and_below hb]

end SwarmReflect
