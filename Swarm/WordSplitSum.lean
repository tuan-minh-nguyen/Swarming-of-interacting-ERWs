/-
# the two-block sum of the actual array mass

Part 2 proved the boundary and successor-weight identities *pointwise* on a word.  This file
re-indexes the fixed-horizon word sum of part 1 (`arrayMeasure_finStrict`) over the pair of blocks,
which is the exact finite "several blocks of varying length" bookkeeping the record decomposition
needs:

  `arrayMeasure {posPath ∈ finStrict (k1 + k2)}
     = ∑_{q1} ∑_{q2} [ first block positive ∧ second block positive above the boundary level ]
         · ofReal (pathW p k1 q1 (startState m) · pathW p k2 q2 (succState q1))`,

where `succState q1 = capState m (runJ m (extendPath q1) k1)` depends on the first block alone and
the second block's positivity is *shifted* by the first block's endpoint level
`posAt (extendPath q1) k1 i`.

The re-indexing is an honest bijection `w ↦ (prefWord w, suffWord w)` of the word spaces
(`wordSplitEquiv`, inverse `catWord`), so no double counting and no unrelated start occurs.  The
weights are the array's own box masses; nothing is factored as a product of independent
probabilities.

Scope: finite `k1, k2`, array side only.  No chain object, no `hstruct`, no invariant `π`.
-/
import Swarm.WordSplit

open MeasureTheory Set
open scoped ENNReal BigOperators
open Classical

attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmArrayWords

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump SimJump.Record
open SwarmRec SwarmFreshPos SwarmFreshCyl SwarmFreshArray SwarmFinHorizon SwarmRestart
  SwarmFresh

variable {N : ℕ}

/-! ## 1. The word split as a bijection -/

/-- The concatenation of two blocks, split back at `k1`. -/
noncomputable def catWord {k1 k2 : ℕ} (q1 : Fin k1 → JumpVec N) (q2 : Fin k2 → JumpVec N) :
    Fin (k1 + k2) → JumpVec N :=
  fun n => if h : (n : ℕ) < k1 then q1 ⟨n.1, h⟩ else q2 ⟨n.1 - k1, by omega⟩

theorem prefWord_catWord {k1 k2 : ℕ} (q1 : Fin k1 → JumpVec N) (q2 : Fin k2 → JumpVec N) :
    prefWord (catWord q1 q2) = q1 := by
  funext n
  simp only [prefWord, catWord, dif_pos n.2]

theorem suffWord_catWord {k1 k2 : ℕ} (q1 : Fin k1 → JumpVec N) (q2 : Fin k2 → JumpVec N) :
    suffWord (catWord q1 q2) = q2 := by
  funext n
  have h : ¬ ((k1 + (n : ℕ)) < k1) := by omega
  simp only [suffWord, catWord, dif_neg h, Nat.add_sub_cancel_left]

theorem catWord_pref_suff {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) :
    catWord (prefWord w) (suffWord w) = w := by
  funext n
  by_cases h : (n : ℕ) < k1
  · simp only [catWord, dif_pos h, prefWord]
  · have hle : k1 ≤ (n : ℕ) := le_of_not_gt h
    simp only [catWord, dif_neg h, suffWord]
    exact congrArg w (Fin.ext (by simp [Nat.add_sub_of_le hle]))

/-- **The word split is a bijection.** -/
noncomputable def wordSplitEquiv (k1 k2 : ℕ) :
    (Fin (k1 + k2) → JumpVec N) ≃ ((Fin k1 → JumpVec N) × (Fin k2 → JumpVec N)) where
  toFun w := (prefWord w, suffWord w)
  invFun p := catWord p.1 p.2
  left_inv w := catWord_pref_suff w
  right_inv p := by
    obtain ⟨q1, q2⟩ := p
    exact Prod.ext (prefWord_catWord q1 q2) (suffWord_catWord q1 q2)

/-- **Summing over a word splits into summing over its two blocks.** -/
theorem sum_split_words {M : Type*} [AddCommMonoid M] {k1 k2 : ℕ}
    (f : (Fin k1 → JumpVec N) → (Fin k2 → JumpVec N) → M) :
    (∑ w : Fin (k1 + k2) → JumpVec N, f (prefWord w) (suffWord w))
      = ∑ q1 : Fin k1 → JumpVec N, ∑ q2 : Fin k2 → JumpVec N, f q1 q2 := by
  rw [← Fintype.sum_prod_type (f := fun p : (Fin k1 → JumpVec N) × (Fin k2 → JumpVec N) =>
    f p.1 p.2)]
  refine Fintype.sum_equiv (wordSplitEquiv (N := N) k1 k2) (fun w => f (prefWord w) (suffWord w))
    (fun p => f p.1 p.2) (fun w => rfl)

/-! ## 2. The block conditions read on the blocks -/

/-- The first block agrees with the whole word on the first `k1` positions. -/
theorem posAt_prefWord_eq {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) {n : ℕ} (hn : n ≤ k1)
    (i : Fin N) :
    posAt (extendPath w) n i = posAt (extendPath (prefWord w)) n i :=
  posAt_congr (u := extendPath w) (v := extendPath (prefWord w)) (n := n)
    (fun j hj => (extendPath_pref w (lt_of_lt_of_le hj hn)).symm) i

/-- The strict positivity of a two-block word, read on the two blocks and the boundary level. -/
def blockCond {k1 k2 : ℕ} (q1 : Fin k1 → JumpVec N) (q2 : Fin k2 → JumpVec N) : Prop :=
  (∀ (n : ℕ), 0 < n → n ≤ k1 → ∀ i, 0 < posAt (extendPath q1) n i) ∧
    (∀ (n : ℕ), 0 < k1 + n → n ≤ k2 → ∀ i,
      0 < posAt (extendPath q1) k1 i + posAt (extendPath q2) n i)

/-- `blockCond` is decidable (classical). -/
theorem blockCond_iff_of_word {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) :
    PosSeqFin (N := N) w ↔ blockCond (prefWord w) (suffWord w) := by
  rw [posWord_iff]
  have key : (∀ (n : ℕ), 1 ≤ n → n ≤ k1 + k2 → ∀ i, 0 < posAt (extendPath w) n i)
      ↔ (∀ (n : ℕ), 0 < n → n ≤ k1 + k2 → ∀ i, 0 < posAt (extendPath w) n i) :=
    ⟨fun h n hn => h n hn, fun h n hn => h n hn⟩
  rw [key, finStrict_boundary_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun n hn hk i => ?_, fun n hn hk i => ?_⟩
    · rw [← posAt_prefWord_eq w hk i]
      exact h1 n hn hk i
    · rw [← posAt_boundary_pref w i]
      exact h2 n hn hk i
  · rintro ⟨h1, h2⟩
    refine ⟨fun n hn hk i => ?_, fun n hn hk i => ?_⟩
    · rw [posAt_prefWord_eq w hk i]
      exact h1 n hn hk i
    · rw [posAt_boundary_pref w i]
      exact h2 n hn hk i

/-! ## 3. The two-block sum identity for the actual array mass -/

/-- **The horizon mass as a double sum over the two blocks.**  The horizon strict-positivity mass
of the actual array is the double word sum over the first block and the second block, where

* the first block must be positive on its own times `1, …, k1`;
* the second block must be positive *above the boundary level* `posAt (extendPath q1) k1 i`;
* the weight is the array's own box mass, split at the boundary by `pathW_split` into the first
  block's weight and the second block's weight from the prefix-determined successor state.

This is the finite two-block (varying-length, level-shifted) decomposition: the words of the second
block appear in their own sum, and the boundary level is kept, rather than clamped away. -/
theorem arrayMeasure_finStrict_twoBlock (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m k1 k2 : ℕ) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) (k1 + k2)}
      = ∑ q1 : Fin k1 → JumpVec N, ∑ q2 : Fin k2 → JumpVec N,
          if blockCond (N := N) q1 q2
            then ENNReal.ofReal
              (pathW p k1 q1 (SwarmFreshArray.startState (N := N) m)
                * pathW p k2 q2 (capState m (runJ m (extendPath q1) k1))) else 0 := by
  rw [arrayMeasure_finStrict p hp0 hp1 m (k1 + k2)]
  have hstep : (∑ w : Fin (k1 + k2) → JumpVec N,
        if PosSeqFin (N := N) w
          then ENNReal.ofReal (pathW p (k1 + k2) w (SwarmFreshArray.startState (N := N) m))
          else 0)
      = ∑ w : Fin (k1 + k2) → JumpVec N,
          (if blockCond (N := N) (prefWord w) (suffWord w)
            then ENNReal.ofReal
              (pathW p k1 (prefWord w) (SwarmFreshArray.startState (N := N) m)
                * pathW p k2 (suffWord w)
                    (capState m (runJ m (extendPath (prefWord w)) k1))) else 0) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : PosSeqFin (N := N) w
    · have h' : blockCond (N := N) (prefWord w) (suffWord w) :=
        (blockCond_iff_of_word w).mp h
      rw [if_pos h, if_pos h', pathW_split]
    · have h' : ¬ blockCond (N := N) (prefWord w) (suffWord w) :=
        fun hh => h ((blockCond_iff_of_word w).mpr hh)
      rw [if_neg h, if_neg h']
  rw [hstep]
  exact sum_split_words (N := N) (fun q1 q2 => if blockCond (N := N) q1 q2
    then ENNReal.ofReal
      (pathW p k1 q1 (SwarmFreshArray.startState (N := N) m)
        * pathW p k2 q2 (capState m (runJ m (extendPath q1) k1))) else 0)

end SwarmArrayWords

/-! ## Axiom audit -/


