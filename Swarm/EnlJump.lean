/-
The **one-step conditional jump law** of the actual interacting walk in the enlarged
filtration: on each piece of `𝓕_n` (the path up to time `n` equal to the prefix `γ`,
and an event of the revealed coordinates before time `n`), the vector of jumps at time
`n` has the product law

  `P(ΔX_n = ε) = ∏_i  (ε_i = +1 ? α_i : 1 - α_i)`

with `α_i` the paper's right-jump probability `α` computed from the local-time state of
the prefix.  This is exactly the display of §2.1 of `main_1d_revised.tex` for the actual
recursion, conditional on the enlarged σ-algebra.

There is no proof hole and no custom axiom in this file.
-/
import Swarm.Imports
import Swarm.UniformArray
import Swarm.Trajectory
import Swarm.EnlFilt
import Swarm.EnlLaw

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- The paper's right-jump probability of walker `i`, computed from the position prefix
`γ` up to time `n` (its local times are the path local times of `γ`). -/
noncomputable def alphaOf (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) (i : Fin N) : ℝ :=
  rightProbability p m (fun j x => localTime (fun s => ext γ s j) n x) i (ext γ n i)

lemma le_alphaOf (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (i : Fin N)
    (hq : 1 / 2 ≤ p) : 1 / 2 ≤ alphaOf p m n γ i :=
  one_half_le_rightProbability hq m _ i _

lemma alphaOf_lt_one (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (i : Fin N)
    (hq : 1 / 2 ≤ p) (hp2 : p < 1) : alphaOf p m n γ i < 1 :=
  lt_of_le_of_lt (rightProbability_le_p hq m _ i _) hp2

/-- On the piece `{path = γ}` the actual right-jump probability is `alphaOf`. -/
lemma rightProbability_eq_alphaOf (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (i : Fin N) :
    rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) =
      alphaOf p m n γ i := by
  have hpos : (trajectory p m U n).pos i = ext γ n i := (ext_prefOf_of_mem hU le_rfl i).symm
  have hell : ∀ (j : Fin N) (x : ℤ), (trajectory p m U n).ell j x
      = localTime (fun s => ext γ s j) n x := by
    intro j x
    rw [Swarming.Trajectory.ell_eq_localTime]
    exact localTime_congr (X := fun s => (trajectory p m U s).pos j)
      (Y := fun s => ext γ s j) (n := n) (fun s hs => (ext_prefOf_of_mem hU hs j).symm)
  have hellf : (trajectory p m U n).ell = (fun j x => localTime (fun s => ext γ s j) n x) := by
    funext j x
    exact hell j x
  rw [alphaOf, hpos, hellf]

/-- The jump of the actual trajectory at time `n` on the piece `{path = γ}`. -/
lemma jumpStep_of_prefAgree (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (i : Fin N) :
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i +
      drivenStep (U (fr (N := N) n γ i)) (alphaOf p m n γ i) := by
  have h : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i +
      drivenStep (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) := rfl
  rw [h, departureCoord_of_prefAgree p m hU i, rightProbability_eq_alphaOf p m hU i]

lemma drivenStep_eq_one_iff (u α : ℝ) : drivenStep u α = 1 ↔ u ≤ α := by
  unfold drivenStep
  split <;> simp_all

lemma drivenStep_eq_neg_one_iff (u α : ℝ) : drivenStep u α = -1 ↔ α < u := by
  unfold drivenStep
  constructor
  · intro h
    by_cases hc : u ≤ α
    · rw [if_pos hc] at h; exact absurd h (by norm_num)
    · exact not_le.1 hc
  · intro h
    rw [if_neg (not_le.2 h)]

/-- The condition "the jump vector is `ε`" in terms of the coordinates read at time `n`. -/
lemma jump_iff_read {u : Fin N → ℝ} {α : Fin N → ℝ} {e : Fin N → ℤ}
    (he : ∀ i, e i = 1 ∨ e i = -1) :
    (∀ i, drivenStep (u i) (α i) = e i) ↔
      ∀ i, u i ∈ (if e i = 1 then Set.Iic (α i) else Set.Ioi (α i)) := by
  constructor
  · intro h i
    have hi := h i
    rcases he i with h1 | h1
    · rw [h1] at hi
      rw [if_pos h1, Set.mem_Iic]
      exact (drivenStep_eq_one_iff _ _).1 hi
    · rw [h1] at hi ⊢
      rw [if_neg (by norm_num : (¬ ((-1 : ℤ) = 1))), Set.mem_Ioi]
      exact (drivenStep_eq_neg_one_iff _ _).1 hi
  · intro h i
    have hi := h i
    rcases he i with h1 | h1
    · rw [h1] at hi ⊢
      rw [if_pos (by norm_num : ((1 : ℤ) = 1))] at hi
      rw [drivenStep_eq_one_iff]
      exact hi
    · rw [h1] at hi ⊢
      rw [if_neg (by norm_num : (¬ ((-1 : ℤ) = 1)))] at hi
      rw [drivenStep_eq_neg_one_iff]
      exact hi

/-- **The one-step conditional jump law on a piece of the enlarged filtration.** -/
theorem enl_jump_pattern_piece (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (ε : Fin N → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hp1 : 1 / 2 ≤ p) (hp2 : p < 1) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ {U : Array N | ∀ i,
        (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + ε i}) =
      (∏ i, ENNReal.ofReal (if ε i = 1 then alphaOf p m n γ i
        else 1 - alphaOf p m n γ i)) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  set I : Fin N → Set ℝ :=
    fun i => if ε i = 1 then Set.Iic (alphaOf p m n γ i) else Set.Ioi (alphaOf p m n γ i) with hI
  have hImeas : ∀ i, MeasurableSet (I i) := by
    intro i
    by_cases h : ε i = 1
    · rw [hI]; simp only [h, if_true]; exact measurableSet_Iic
    · rw [hI]; simp only [h, if_false]; exact measurableSet_Ioi
  have hset : prefAgree p m γ ∩ B ∩ {U : Array N | ∀ i,
        (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + ε i}
      = prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (fr (N := N) n γ i) ∈ I i} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, fun i => ?_⟩
      have hu : drivenStep (U (fr (N := N) n γ i)) (alphaOf p m n γ i) = ε i := by
        have hi := h3 i
        rw [jumpStep_of_prefAgree p m h1 i] at hi
        omega
      refine (jump_iff_read (N := N) (u := fun j => U (fr (N := N) n γ j))
        (α := fun j => alphaOf p m n γ j) hε).1 (fun j => ?_) i
      by_cases hj : j = i
      · subst hj; exact hu
      · have hj' := h3 j
        rw [jumpStep_of_prefAgree p m h1 j] at hj'
        omega
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, fun i => ?_⟩
      have hu := (jump_iff_read (N := N) (u := fun j => U (fr (N := N) n γ j))
        (α := fun j => alphaOf p m n γ j) hε).2 h3 i
      rw [jumpStep_of_prefAgree p m h1 i]
      omega
  rw [hset, enl_fresh_law_piece p m n γ hB I hImeas]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : ε i = 1
  · rw [hI]; simp only [h, if_true]
    exact Swarming.Uniform.uniform01_Iic (by linarith [le_alphaOf p m γ i hp1])
      (alphaOf_lt_one p m γ i hp1 hp2)
  · rw [hI]; simp only [h, if_false]
    exact Swarming.Uniform.uniform01_Ioi (by linarith [le_alphaOf p m γ i hp1])
      (alphaOf_lt_one p m γ i hp1 hp2)

end Swarming.Enl
