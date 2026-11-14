/-
# the two-block (`k1 + k2`) split of an array word

`ArrayWordDecomp.lean` decomposes a single fixed horizon into the words of the first `k` jumps.
This file adds the *block boundary*: a word of length `k1 + k2` is cut into its first block and its
second block, and

* the array mass of any event that depends on the two blocks through a predicate of
  `(prefWord, suffWord)` is the corresponding two-block word sum with the array's own weights
  (`mass_wordSet_split` — the transfer principle of part 1 at a split predicate, so no false
  independence or unrelated-start summation is used);

* the **successor-word weight** of the second block is `pathW p k2 · (succState …)`, where the
  successor state `capState m (runJ m (extendPath (prefWord w)) k1)` is *determined by the first
  block alone* (`pathW_split`).  This is the exact factorisation the record decomposition needs at
  a segment boundary: nothing is averaged, nothing is assumed independent, and the successor state
  is a function of the prefix word — not of the array beyond it;

* the **boundary level** identity: the position of walker `i` after `k1 + n` steps is the position
  after `k1` steps (a function of the first block alone) plus the net displacement of the second
  block's first `n` steps (`posAt_boundary`).  So the strict-positivity condition of the second
  block is a condition on the second word *shifted by the first block's endpoint level*
  (`finStrict_boundary_iff`); in particular it is **not** `PosSeqFin` of the second word, and it is
  not a fixed-`k` clamp.

Scope: finite `k1, k2` only, array side only.  No chain object, no `hstruct`, no invariant `π`,
no stationarity and no fresh independence is used or claimed.
-/
import Swarm.ArrayWordDecomp

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

/-! ## 1. Net displacement is additive over a block boundary -/

theorem posAt_congr {u v : ℕ → JumpVec N} {n : ℕ} (h : ∀ j, j < n → u j = v j) (i : Fin N) :
    posAt u n i = posAt v n i := by
  simp only [posAt]
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

/-- **Additivity of the net displacement over a block boundary.** -/
theorem posAt_add (u : ℕ → JumpVec N) (k1 k2 : ℕ) (i : Fin N) :
    posAt u (k1 + k2) i = posAt u k1 i + posAt (fun n => u (k1 + n)) k2 i := by
  induction k2 with
  | zero => simp [posAt]
  | succ k2 ih =>
      rw [Nat.add_succ, posAt_succ, ih, posAt_succ]
      ring

/-! ## 2. The two blocks of a word of length `k1 + k2` -/

/-- The first block of a word of length `k1 + k2`. -/
def prefWord {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) : Fin k1 → JumpVec N :=
  fun n => w ⟨n.1, by omega⟩

/-- The second block of a word of length `k1 + k2`. -/
def suffWord {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) : Fin k2 → JumpVec N :=
  fun n => w ⟨k1 + n.1, by omega⟩

/-- The continuation of the first block agrees with the continuation of the whole word on the
first block. -/
theorem extendPath_pref {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) {n : ℕ} (hn : n < k1) :
    extendPath (prefWord w) n = extendPath w n := by
  simp only [extendPath, dif_pos hn, dif_pos (show n < k1 + k2 by omega), prefWord]

/-- The continuation of the second block is the shift of the whole word's continuation. -/
theorem extendPath_suff {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) {n : ℕ} (hn : n < k2) :
    extendPath (suffWord w) n = extendPath w (k1 + n) := by
  simp only [extendPath, dif_pos hn, dif_pos (show k1 + n < k1 + k2 by omega), suffWord]

/-- **The boundary level.**  The position after `k1 + n` steps splits into the position at the
boundary `k1` (which depends on the first block only) plus the net displacement of the second
block's first `n` steps.  So the second block's positivity condition is *shifted* by the first
block's endpoint level. -/
theorem posAt_boundary {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) {n : ℕ} (hn : n ≤ k2)
    (i : Fin N) :
    posAt (extendPath w) (k1 + n) i
      = posAt (extendPath w) k1 i + posAt (extendPath (suffWord w)) n i := by
  rw [posAt_add (extendPath w) k1 n i,
    posAt_congr (u := fun j => extendPath w (k1 + j)) (v := extendPath (suffWord w))
      (n := n) (fun j hj => (extendPath_suff w (lt_of_lt_of_le hj hn)).symm) i]

/-- The boundary position really only depends on the first block. -/
theorem posAt_boundary_pref {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) (i : Fin N) :
    posAt (extendPath w) k1 i = posAt (extendPath (prefWord w)) k1 i :=
  (posAt_congr (u := extendPath (prefWord w)) (v := extendPath w) (n := k1)
    (fun _ hj => extendPath_pref w hj) i).symm

/-! ## 3. The successor-word weight of the second block -/

/-- **The successor state after a block depends on that block alone.** -/
theorem evolveFun_extendPath_pref (m k1 k2 : ℕ) (w : Fin (k1 + k2) → JumpVec N) :
    evolveFun (extendPath w) k1 (SwarmFreshArray.startState (N := N) m)
      = capState m (runJ m (extendPath (prefWord w)) k1) := by
  rw [show SwarmFreshArray.startState (N := N) m = capState m initialWalkState from rfl,
    evolveFun_capState]
  congr 1
  exact runJ_congr m k1 (fun s hs => (extendPath_pref w hs).symm)

/-- **The successor-word weight identity for the array.**  The array mass weight of a word of
length `k1 + k2` is the weight of its first block times the weight of its second block measured
from the *prefix-determined* successor state.  No independence and no state average: this is the
deterministic factorisation of the array's own box mass at a segment boundary. -/
theorem pathW_split (p : ℝ) (m k1 k2 : ℕ) (w : Fin (k1 + k2) → JumpVec N) :
    pathW p (k1 + k2) w (SwarmFreshArray.startState (N := N) m)
      = pathW p k1 (prefWord w) (SwarmFreshArray.startState (N := N) m)
        * pathW p k2 (suffWord w)
            (capState m (runJ m (extendPath (prefWord w)) k1)) := by
  rw [pathW_eq_pathWFun_ext p m (k1 + k2) w,
    pathWFun_add p m (extendPath w) k1 k2 (SwarmFreshArray.startState (N := N) m)]
  congr 1
  · show pathW p k1 (fun i : Fin k1 => extendPath w i) (SwarmFreshArray.startState (N := N) m)
      = pathW p k1 (prefWord w) (SwarmFreshArray.startState (N := N) m)
    rw [show (fun i : Fin k1 => extendPath w i) = prefWord w from
      funext fun i => by
        simp only [extendPath, dif_pos (show (i : ℕ) < k1 + k2 by omega), prefWord]]
  · rw [evolveFun_extendPath_pref m k1 k2 w]
    show pathW p k2 (fun i : Fin k2 => extendPath w (k1 + i))
        (capState m (runJ m (extendPath (prefWord w)) k1))
      = pathW p k2 (suffWord w) (capState m (runJ m (extendPath (prefWord w)) k1))
    rw [show (fun i : Fin k2 => extendPath w (k1 + i)) = suffWord w from
      funext fun i => by
        simp only [extendPath, dif_pos (show k1 + (i : ℕ) < k1 + k2 by omega), suffWord]]

/-! ## 4. The two-block word sum with the actual array measure -/

/-- **The two-block transfer principle.**  An event that depends on the array's first `k1 + k2`
jumps only through the pair `(prefWord, suffWord)` has, under the actual array law, the mass of
the two-block word sum with the array's own box masses.  The summands are indexed by the whole
word, so nothing is assumed independent across the boundary and no unrelated starts are summed. -/
theorem mass_wordSet_split (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m k1 k2 : ℕ)
    (P : (Fin k1 → JumpVec N) → (Fin k2 → JumpVec N) → Prop) [DecidableRel P] :
    (arrayMeasure N) {U : Array N |
        P (prefWord (jumpWord p m (k1 + k2) U)) (suffWord (jumpWord p m (k1 + k2) U))}
      = ∑ w : Fin (k1 + k2) → JumpVec N,
          if P (prefWord w) (suffWord w)
            then ENNReal.ofReal (pathW p (k1 + k2) w (SwarmFreshArray.startState (N := N) m))
            else 0 :=
  mass_wordSet p hp0 hp1 m (k1 + k2) (fun w => P (prefWord w) (suffWord w))

/-- The same two-block mass, with the second block's weight stated through the
prefix-determined successor state (`pathW_split`). -/
theorem mass_wordSet_split_factored (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m k1 k2 : ℕ) (P : (Fin k1 → JumpVec N) → (Fin k2 → JumpVec N) → Prop) [DecidableRel P] :
    (arrayMeasure N) {U : Array N |
        P (prefWord (jumpWord p m (k1 + k2) U)) (suffWord (jumpWord p m (k1 + k2) U))}
      = ∑ w : Fin (k1 + k2) → JumpVec N,
          if P (prefWord w) (suffWord w)
            then ENNReal.ofReal
              (pathW p k1 (prefWord w) (SwarmFreshArray.startState (N := N) m)
                * pathW p k2 (suffWord w)
                    (capState m (runJ m (extendPath (prefWord w)) k1))) else 0 := by
  rw [mass_wordSet_split p hp0 hp1 m k1 k2 P]
  exact Finset.sum_congr rfl fun w _ => by rw [pathW_split]

/-- **The second block's positivity condition is level shifted.**  `finStrict (k1+k2)` splits into
the first block's own positivity and the second block's positivity *relative to the level reached
at the boundary*.  The second condition is not `PosSeqFin` of the second word: it reads the base
level `posAt (extendPath w) k1 i`, which is determined by the first block. -/
theorem finStrict_boundary_iff {k1 k2 : ℕ} (w : Fin (k1 + k2) → JumpVec N) :
    (∀ (n : ℕ), 0 < n → n ≤ k1 + k2 → ∀ i, 0 < posAt (extendPath w) n i)
      ↔ (∀ (n : ℕ), 0 < n → n ≤ k1 → ∀ i, 0 < posAt (extendPath w) n i) ∧
        (∀ (n : ℕ), 0 < k1 + n → n ≤ k2 → ∀ i,
          0 < posAt (extendPath w) k1 i + posAt (extendPath (suffWord w)) n i) := by
  constructor
  · rintro h
    refine ⟨fun n hn hk i => h n hn (by omega) i, fun n hn hk i => ?_⟩
    rw [← posAt_boundary w (n := n) hk i]
    exact h (k1 + n) hn (by omega) i
  · rintro ⟨h1, h2⟩ n hn hnk i
    rcases Nat.lt_or_ge n k1 with hlt | hge
    · exact h1 n hn (le_of_lt hlt) i
    · have hsub : n - k1 ≤ k2 := by omega
      have hpos : 0 < k1 + (n - k1) := by rw [Nat.add_sub_of_le hge]; exact hn
      have h2' := h2 (n - k1) hpos hsub i
      rw [show n = k1 + (n - k1) from (Nat.add_sub_of_le hge).symm,
        posAt_boundary w (n := n - k1) hsub i]
      exact h2'

end SwarmArrayWords

/-! ## Axiom audit -/


