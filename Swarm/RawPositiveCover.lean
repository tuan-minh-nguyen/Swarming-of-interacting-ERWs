/-
Maximal completed-record prefixes and their genuine unfinished raw tails.

Every finite raw word has such a decomposition.  Positivity is kept as a
 predicate on the whole reassembled word, never as positivity of individual
record excursions.  The suffix weight is evaluated at the actual terminal
record state.
-/
import Swarm.RawPrefixReconstruction

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawRecord

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- A word has no completed first-record excursion among its nonempty prefixes. -/
def NoRecordPrefix {m : ℕ} (s : State N m) {r : ℕ} (q : Fin r → JumpVec N) : Prop :=
  ∀ k, 0 < k → k ≤ r → ¬ FirstRecord (extendPath q) k s

/-- A maximal completed-record prefix together with its genuine unfinished tail.
The length equation indexes the structure by the entire raw duration. -/
structure MaxRecordDecomp (hm : 1 ≤ m) (y : RecState N m) (K : ℕ) where
  completed : List (RawBlock N)
  tail : RawBlock N
  len_eq : rawLen completed + tail.1 = K
  allFirst : AllFirst hm y completed
  tail_unfinished : NoRecordPrefix (ofRecState (terminal hm y completed)) tail.2

/-- Transport a finite word along an equality of its length, without changing
any numeral index. -/
def castWord {K L : ℕ} (h : K = L) (q : Fin K → JumpVec N) : Fin L → JumpVec N :=
  fun j => q ⟨j.1, by omega⟩

@[simp] theorem castWord_apply {K L : ℕ} (h : K = L) (q : Fin K → JumpVec N)
    (j : Fin L) : castWord h q j = q ⟨j.1, by omega⟩ := rfl

/-- The actual raw word represented by a completed-prefix/unfinished-tail pair. -/
noncomputable def decompWord {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) : Fin K → JumpVec N :=
  castWord d.len_eq (catWord (rawWord d.completed) d.tail.2)

/-- Length transport preserves every finite path weight. -/
theorem pathW_castWord {K L : ℕ} (h : K = L) (q : Fin K → JumpVec N)
    (p : ℝ) (s : State N m) :
    pathW p L (castWord h q) s = pathW p K q s := by
  subst L
  rfl

/-- Exact weight of a maximal record decomposition.  No positivity or
first-record condition is imposed on the unfinished tail. -/
theorem pathW_decompWord (p : ℝ) {hm : 1 ≤ m} (y : RecState N m) {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) :
    pathW p K (decompWord d) (ofRecState y) = prefixW p hm y d.completed *
      pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)) := by
  rw [decompWord, pathW_castWord]
  exact pathW_rawWord_future_terminal p hm y d.completed d.allFirst d.tail.2

/-- Within the old horizon, a length-transported word has the same infinite
extension used by finite strict positivity. -/
theorem seqOf_castWord {K L : ℕ} (h : K = L) (q : Fin K → JumpVec N)
    {n : ℕ} (hn : n < K) :
    SwarmFreshPos.seqOf (castWord h q) n = SwarmFreshPos.seqOf q n := by
  simp [SwarmFreshPos.seqOf, castWord, hn, show n < L by omega]

/-- Positivity remains the positivity of the entire concatenation after length
transport; in particular it is not replaced by excursion-wise positivity. -/
theorem posSeqFin_decompWord_iff {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) :
    SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ↔
      SwarmFreshPos.PosSeqFin (N := N)
        (catWord (rawWord d.completed) d.tail.2) := by
  rw [SwarmFreshPos.posSeqFin_iff, SwarmFreshPos.posSeqFin_iff]
  have hlen := d.len_eq
  have heq : ∀ n, n ≤ K → ∀ i,
      SwarmFreshPos.posAt (SwarmFreshPos.seqOf (decompWord d)) n i =
        SwarmFreshPos.posAt (SwarmFreshPos.seqOf
          (catWord (rawWord d.completed) d.tail.2)) n i := by
    intro n hn i
    exact posAt_congr (fun j hj => seqOf_castWord d.len_eq
      (catWord (rawWord d.completed) d.tail.2) (by omega)) i
  constructor
  · intro h n h1 hn i
    rw [← heq n (by omega) i]
    exact h n h1 (by omega) i
  · intro h n h1 hn i
    rw [heq n hn i]
    exact h n h1 (by omega) i

/-- Restrict a first-record property to the first block of a split word. -/
theorem firstRecord_prefWord {k r : ℕ} (q : Fin (k + r) → JumpVec N)
    (s : State N m) (h : FirstRecord (extendPath q) k s) :
    FirstRecord (extendPath (prefWord q)) k s := by
  have he : ∀ t, t ≤ k → evolveFun (extendPath (prefWord q)) t s =
      evolveFun (extendPath q) t s := by
    intro t ht
    exact evolveFun_congr_prefix (fun j hj => extendPath_pref q (by omega)) s
  constructor
  · obtain ⟨i, hi⟩ := h.1
    refine ⟨i, ?_⟩
    rw [he k le_rfl]
    exact hi
  · intro t ht i
    rw [he t (Nat.le_of_lt ht)]
    exact h.2 t ht i

/-- Prepend a genuine first-record block to a decomposition of the suffix. -/
noncomputable def prependDecomp {hm : 1 ≤ m} {y : RecState N m} {r : ℕ}
    (b : RawBlock N) (hb : FirstRecord (extendPath b.2) b.1 (ofRecState y))
    (d : MaxRecordDecomp (N := N) hm (RecKernel.out hm b.2 y) r) :
    MaxRecordDecomp (N := N) hm y (b.1 + r) where
  completed := b :: d.completed
  tail := d.tail
  len_eq := by
    simpa only [rawLen, Nat.add_assoc] using congrArg (fun n => b.1 + n) d.len_eq
  allFirst := ⟨hb, d.allFirst⟩
  tail_unfinished := d.tail_unfinished

/-- The prepended decomposition reassembles as the first block followed by the
old reassembled suffix, with all dependent indices retained. -/
theorem decompWord_prependDecomp {hm : 1 ≤ m} {y : RecState N m} {r : ℕ}
    (b : RawBlock N) (hb : FirstRecord (extendPath b.2) b.1 (ofRecState y))
    (d : MaxRecordDecomp (N := N) hm (RecKernel.out hm b.2 y) r) :
    decompWord (prependDecomp b hb d) = catWord b.2 (decompWord d) := by
  funext j
  by_cases hj : (j : ℕ) < b.1
  · simp [decompWord, prependDecomp, rawLen, rawWord, castWord, catWord, hj,
      show (j : ℕ) < b.1 + rawLen d.completed by omega]
  · by_cases hj' : (j : ℕ) < b.1 + rawLen d.completed
    · have hj'' : (j : ℕ) - b.1 < rawLen d.completed := by omega
      simp [decompWord, prependDecomp, rawLen, rawWord, castWord, catWord, hj, hj', hj'']
    · have hj'' : ¬ (j : ℕ) - b.1 < rawLen d.completed := by omega
      simp [decompWord, prependDecomp, rawLen, rawWord, castWord, catWord, hj, hj', hj'',
        Nat.sub_sub]

/-- A word with no record prefix is itself the unfinished tail. -/
noncomputable def unfinishedDecomp {hm : 1 ≤ m} (y : RecState N m) {K : ℕ}
    (q : Fin K → JumpVec N) (hq : NoRecordPrefix (ofRecState y) q) :
    MaxRecordDecomp (N := N) hm y K where
  completed := []
  tail := ⟨K, q⟩
  len_eq := by simp [rawLen]
  allFirst := trivial
  tail_unfinished := hq

@[simp] theorem decompWord_unfinishedDecomp {hm : 1 ≤ m} (y : RecState N m)
    {K : ℕ} (q : Fin K → JumpVec N) (hq : NoRecordPrefix (ofRecState y) q) :
    decompWord (unfinishedDecomp (hm := hm) y q hq) = q := by
  funext j
  simp [decompWord, unfinishedDecomp, rawLen, rawWord, castWord, catWord]

/-- **Exhaustive maximal record-prefix decomposition.**  Every finite raw word,
at every actual record state and every duration, consists of a genuine
`AllFirst` prefix followed by a tail with no completed record prefix. -/
theorem exists_maxRecordDecomp {hm : 1 ≤ m} (y : RecState N m) :
    ∀ (K : ℕ) (q : Fin K → JumpVec N),
      ∃ d : MaxRecordDecomp (N := N) hm y K, decompWord d = q := by
  intro K
  induction K using Nat.strong_induction_on generalizing y with
  | h K ih =>
      intro q
      by_cases hex : ∃ k r : ℕ, 0 < k ∧ K = k + r ∧
        FirstRecord (extendPath q) k (ofRecState y)
      · obtain ⟨k, r, hk, rfl, hfr⟩ := hex
        let b : RawBlock N := ⟨k, prefWord q⟩
        have hb : FirstRecord (extendPath b.2) b.1 (ofRecState y) := by
          exact firstRecord_prefWord q (ofRecState y) hfr
        obtain ⟨d, hd⟩ := ih r (by omega) (RecKernel.out hm b.2 y) (suffWord q)
        refine ⟨prependDecomp b hb d, ?_⟩
        rw [decompWord_prependDecomp, hd]
        exact catWord_pref_suff q
      · have hq : NoRecordPrefix (ofRecState y) q := by
          intro k hk hkK hfr
          apply hex
          exact ⟨k, K - k, hk, by omega, hfr⟩
        exact ⟨unfinishedDecomp (hm := hm) y q hq,
          decompWord_unfinishedDecomp (hm := hm) y q hq⟩

end SwarmRawRecord
