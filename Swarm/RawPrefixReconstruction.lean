/-
Canonical reconstruction of raw record words from enriched record atoms.

The path stored in a genuine enriched segment determines every jump. We make
its inverse explicit, then lift it to arbitrary finite `AllFirst` lists. No
positivity, fresh-future, stationary-law, or measured independence hypothesis is
used. The second component of every emitted atom is the actual successive
`RecKernel.out` state.
-/
import Swarm.RawRecordPrefix
import Swarm.MeasuredRecordSections
import Swarm.DHStruct

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

/-- Read the jump at time `t` from the nearest-neighbour step of an enriched segment. -/
def segWord (s : SwarmConcat.Seg N) : Fin s.dur → JumpVec N :=
  fun t i => decide (s.p ((t : ℕ) + 1) i = s.p (t : ℕ) i + 1)

/-- Package the segment duration together with its decoded raw word. -/
def segBlock (s : SwarmConcat.Seg N) : RawBlock N := ⟨s.dur, segWord s⟩

/-- On actual first-record support, step-wise decoding recovers the original word. -/
theorem segWord_segOfFirst (y : RecState N m) {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N)
    (hq : FirstRecord (extendPath q) k (ofRecState y)) :
    segWord (SwarmSegKernel.segOfFirst y k q hk hq) = q := by
  change (fun j : Fin k => fun i =>
    decide ((evolveFun (extendPath q) ((j : ℕ) + 1) (ofRecState y)).pos i =
      (evolveFun (extendPath q) (j : ℕ) (ofRecState y)).pos i + 1)) = q
  funext j i
  have hqext : extendPath q (j : ℕ) i = q j i := by
    simp only [extendPath, dif_pos j.isLt]
  rw [evolveFun_succ, step_pos]
  unfold stepPos
  rw [hqext]
  cases q j i <;> simp

/-- The canonical segment decoder is a left inverse of `segOf` on first-record words. -/
theorem segBlock_segOf (y : RecState N m) {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N)
    (hq : FirstRecord (extendPath q) k (ofRecState y)) :
    segBlock (SwarmSegKernel.segOf y k q) = ⟨k, q⟩ := by
  rw [SwarmSegKernel.segOf, dif_pos ⟨hk, hq⟩]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (segWord_segOfFirst y hk q hq)

/-- The enriched atoms generated in order by a raw record list. -/
noncomputable def rawPairs (hm : 1 ≤ m) (y : RecState N m) :
    List (RawBlock N) → List (SwarmInfSeg.Pair N m)
  | [] => []
  | b :: bs =>
      (SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y) ::
        rawPairs hm (RecKernel.out hm b.2 y) bs

/-- Decode every segment of an enriched atom list, forgetting only its redundant endpoint. -/
def pairBlocks : List (SwarmInfSeg.Pair N m) → List (RawBlock N) :=
  List.map (fun a => segBlock a.1)

@[simp] theorem rawPairs_nil (hm : 1 ≤ m) (y : RecState N m) :
    rawPairs hm y [] = [] := rfl

@[simp] theorem rawPairs_cons (hm : 1 ≤ m) (y : RecState N m)
    (b : RawBlock N) (bs : List (RawBlock N)) :
    rawPairs hm y (b :: bs) =
      (SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y) ::
        rawPairs hm (RecKernel.out hm b.2 y) bs := rfl

@[simp] theorem rawPairs_length (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) : (rawPairs hm y bs).length = bs.length := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih => simp [ih]

/-- **Arbitrary-list left inverse.** Enriched paths reconstruct exactly the raw
record list, with arbitrary positive `N,m` and every actual successive endpoint. -/
theorem pairBlocks_rawPairs (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    pairBlocks (rawPairs hm y bs) = bs := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
      rcases hbs with ⟨hb, hbs⟩
      rw [rawPairs_cons, pairBlocks, List.map_cons, segBlock_segOf y
        (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb]
      change b :: pairBlocks (rawPairs hm (RecKernel.out hm b.2 y) bs) = b :: bs
      rw [ih (RecKernel.out hm b.2 y) hbs]

/-- The reconstructed list has the same record count as the enriched prefix. -/
theorem pairBlocks_rawPairs_length (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    (pairBlocks (rawPairs hm y bs)).length = (rawPairs hm y bs).length := by
  rw [pairBlocks_rawPairs hm y bs hbs, rawPairs_length]

/-- Every emitted segment has its source block's exact raw duration. -/
theorem rawPairs_durations (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    (rawPairs hm y bs).map (fun a => a.1.dur) = bs.map Sigma.fst := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
      rcases hbs with ⟨hb, hbs⟩
      rw [rawPairs_cons, List.map_cons, List.map_cons]
      have hd : (SwarmSegKernel.segOf y b.1 b.2).dur = b.1 :=
        SwarmFreshCyl.segOf_dur_of_firstRecord (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb
      rw [hd, ih (RecKernel.out hm b.2 y) hbs]

/-- Cumulative raw time is exactly the sum of enriched durations. -/
theorem rawLen_eq_enriched_duration_sum (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    rawLen bs = ((rawPairs hm y bs).map (fun a => a.1.dur)).sum := by
  rw [rawPairs_durations hm y bs hbs]
  clear hbs
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [rawLen, List.map_cons, List.sum_cons, ih]


/-- Canonical enriched prefixes at a fixed initial record state: every atom has
both its genuine first-record segment and the actual successive compact state. -/
def CanonicalPairs (hm : 1 ≤ m) (y : RecState N m) :
    List (SwarmInfSeg.Pair N m) → Prop
  | [] => True
  | a :: as => ∃ b : RawBlock N, ∃ _hb : FirstRecord (extendPath b.2) b.1 (ofRecState y),
      a = (SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y) ∧
        CanonicalPairs hm (RecKernel.out hm b.2 y) as

/-- Every raw `AllFirst` prefix generates a canonical enriched prefix. -/
theorem canonicalPairs_rawPairs (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    CanonicalPairs hm y (rawPairs hm y bs) := by
  induction bs generalizing y with
  | nil => trivial
  | cons b bs ih =>
      rcases hbs with ⟨hb, hbs⟩
      exact ⟨b, hb, rfl, ih (RecKernel.out hm b.2 y) hbs⟩

/-- Decoding a canonical enriched prefix preserves its first-record support. -/
theorem allFirst_pairBlocks_of_canonicalPairs (hm : 1 ≤ m) (y : RecState N m)
    (as : List (SwarmInfSeg.Pair N m)) (has : CanonicalPairs hm y as) :
    AllFirst hm y (pairBlocks as) := by
  induction as generalizing y with
  | nil => trivial
  | cons a as ih =>
      rcases has with ⟨b, hb, rfl, has⟩
      have hs : segBlock (SwarmSegKernel.segOf y b.1 b.2) = b := by
        simpa using segBlock_segOf y (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb
      change AllFirst hm y (segBlock (SwarmSegKernel.segOf y b.1 b.2) :: pairBlocks as)
      rw [hs]
      exact ⟨hb, ih (RecKernel.out hm b.2 y) has⟩

/-- **Arbitrary-list right inverse.**  Re-expanding the decoded words gives back
both the enriched segment and the endpoint of every canonical atom. -/
theorem rawPairs_pairBlocks_of_canonicalPairs (hm : 1 ≤ m) (y : RecState N m)
    (as : List (SwarmInfSeg.Pair N m)) (has : CanonicalPairs hm y as) :
    rawPairs hm y (pairBlocks as) = as := by
  induction as generalizing y with
  | nil => rfl
  | cons a as ih =>
      rcases has with ⟨b, hb, rfl, has⟩
      have hs : segBlock (SwarmSegKernel.segOf y b.1 b.2) = b := by
        simpa using segBlock_segOf y (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb
      change rawPairs hm y (segBlock (SwarmSegKernel.segOf y b.1 b.2) :: pairBlocks as) = _
      rw [hs, rawPairs_cons, ih (RecKernel.out hm b.2 y) has]

/-- Raw first-record prefixes at their actual initial state. -/
abbrev RawPrefixAt (hm : 1 ≤ m) (y : RecState N m) :=
  {bs : List (RawBlock N) // AllFirst hm y bs}

/-- Canonical enriched path prefixes at the same fixed initial state. -/
abbrev EnrichedPrefixAt (hm : 1 ≤ m) (y : RecState N m) :=
  {as : List (SwarmInfSeg.Pair N m) // CanonicalPairs hm y as}

/-- **Canonical raw-prefix/enriched-prefix equivalence.**  This is pathwise and
keeps the initial `y`, all raw words, all durations and all successive endpoints. -/
noncomputable def rawEnrichedEquiv (hm : 1 ≤ m) (y : RecState N m) :
    RawPrefixAt (N := N) hm y ≃ EnrichedPrefixAt (N := N) hm y where
  toFun bs := ⟨rawPairs hm y bs.1, canonicalPairs_rawPairs hm y bs.1 bs.2⟩
  invFun as := ⟨pairBlocks as.1, allFirst_pairBlocks_of_canonicalPairs hm y as.1 as.2⟩
  left_inv bs := Subtype.ext (pairBlocks_rawPairs hm y bs.1 bs.2)
  right_inv as := Subtype.ext (rawPairs_pairBlocks_of_canonicalPairs hm y as.1 as.2)

/-- Any canonical enriched prefix admits exactly the raw representation supplied
by the inverse, and that representation has the expected complete raw future. -/
theorem pairBlocks_canonicalPairs_spec (hm : 1 ≤ m) (y : RecState N m)
    (as : List (SwarmInfSeg.Pair N m)) (has : CanonicalPairs hm y as) :
    AllFirst hm y (pairBlocks as) ∧ rawPairs hm y (pairBlocks as) = as ∧
      (rawEnrichedEquiv hm y).symm ⟨as, has⟩ =
        (⟨pairBlocks as, allFirst_pairBlocks_of_canonicalPairs hm y as has⟩ :
          RawPrefixAt (N := N) hm y) := by
  exact ⟨allFirst_pairBlocks_of_canonicalPairs hm y as has,
    rawPairs_pairBlocks_of_canonicalPairs hm y as has, rfl⟩

/-- Whole-word strict positivity filters the two sides identically.  In particular,
using the inverse does not replace whole-prefix positivity by segment positivity. -/
theorem posSeqFin_pairBlocks_rawPairs_iff (hm : 1 ≤ m) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    SwarmFreshPos.PosSeqFin (N := N) (rawWord (pairBlocks (rawPairs hm y bs))) ↔
      SwarmFreshPos.PosSeqFin (N := N) (rawWord bs) := by
  rw [pairBlocks_rawPairs hm y bs hbs]


/-- Raw positions at any offset through the next record are read directly from a
canonical enriched prefix and its true next segment.  `t=r` is allowed; there is
no unit-duration assumption. -/
theorem patOf_pairBlocks_record_suffix (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (as : List (SwarmInfSeg.Pair N m))
    (has : CanonicalPairs hm y as) {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (terminal hm y (pairBlocks as)))) {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord (rawWord (pairBlocks as)) q)
        ⟨rawLen (pairBlocks as) + t, by omega⟩ i =
      ((pairBlocks as).length : ℤ) +
        (SwarmSegKernel.segOf (terminal hm y (pairBlocks as)) r q).p t i := by
  exact patOf_rawWord_record_suffix hm hy (pairBlocks as)
    (allFirst_pairBlocks_of_canonicalPairs hm y as has) q hr hq ht i

/-- In the strict interior of the next record, a path reconstructed from a
canonical enriched prefix has not exceeded its completed record level. -/
theorem patOf_pairBlocks_record_suffix_le (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (as : List (SwarmInfSeg.Pair N m))
    (has : CanonicalPairs hm y as) {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (terminal hm y (pairBlocks as)))) {t : ℕ} (ht : t < r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord (rawWord (pairBlocks as)) q)
        ⟨rawLen (pairBlocks as) + t, by omega⟩ i ≤ ((pairBlocks as).length : ℤ) := by
  exact patOf_rawWord_record_suffix_le hm hy (pairBlocks as)
    (allFirst_pairBlocks_of_canonicalPairs hm y as has) q hr hq ht i

/-- Exact arbitrary whole-prefix positivity filter in enriched coordinates.  The
old entire raw word remains a conjunct, alongside every shifted position of the
next segment, including its endpoint. -/
theorem posSeqFin_pairBlocks_record_suffix_iff (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (as : List (SwarmInfSeg.Pair N m))
    (has : CanonicalPairs hm y as) {r : ℕ} (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (terminal hm y (pairBlocks as)))) :
    SwarmFreshPos.PosSeqFin (N := N) (catWord (rawWord (pairBlocks as)) q) ↔
      SwarmFreshPos.PosSeqFin (N := N) (rawWord (pairBlocks as)) ∧
        ∀ t, 1 ≤ t → t ≤ r → ∀ i,
          0 < ((pairBlocks as).length : ℤ) +
            (SwarmSegKernel.segOf (terminal hm y (pairBlocks as)) r q).p t i := by
  exact posSeqFin_rawWord_record_suffix_iff hm hy (pairBlocks as)
    (allFirst_pairBlocks_of_canonicalPairs hm y as has) q hr hq

end SwarmRawRecord
