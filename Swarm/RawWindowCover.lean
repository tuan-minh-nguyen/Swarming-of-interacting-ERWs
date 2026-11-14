/-
Fixed raw-time events on canonical record-decomposition cylinders.

The final atom of a canonical decomposition is converted from its decoded
jump-prefix description to the stronger actual-position description.  The
conversion uses only the segment's nearest-neighbour steps and its start; it
requires no completion of the unfinished raw word and no probabilistic input.
-/
import Swarm.MixedTrajectoryWindow

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawWindowCover

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmMixedTrajectory SwarmEnrichedRawTail SwarmUnfinishedTail
open SwarmFreshArray
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SwarmFinHorizon SwarmFreshPos SwarmRestart

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- A segment with a known start and known decoded jumps is the actual raw
path through the supplied strict interior cut. -/
theorem mem_unfinishedTailSet_of_tailPrefixSet {z : RecState N m} {r : ℕ}
    {q : Fin r → JumpVec N} {a : SwarmInfSeg.Pair N m}
    (ha : a ∈ TailPrefixSet (N := N) (m := m) q)
    (hstart : ∀ i, a.1.p 0 i = relP z (extendPath q) 0 i) :
    a ∈ unfinishedTailSet (N := N) (m := m) z q := by
  refine ⟨ha.1, ?_⟩
  have hpath : ∀ t : ℕ, t ≤ r → ∀ i,
      a.1.p t i = relP z (extendPath q) t i := by
    intro t
    induction t with
    | zero => exact fun _ => hstart
    | succ t ih =>
        intro ht i
        have htr : t < r := by omega
        have htd : t < a.1.dur := lt_trans htr ha.1
        have hj := congrFun (ha.2 ⟨t, htr⟩) i
        have hstep := a.1.step t htd i
        have hmove : a.1.p (t + 1) i = a.1.p t i +
            (if q ⟨t, htr⟩ i = true then (1 : ℤ) else -1) := by
          rcases hstep with hplus | hminus
          · have hq : q ⟨t, htr⟩ i = true := by
              simpa [segJump, hplus] using hj.symm
            rw [hplus, hq, if_pos rfl]
          · have hq : q ⟨t, htr⟩ i = false := by
              simp only [segJump, hminus] at hj
              have hne : ¬ a.1.p t i - 1 = a.1.p t i + 1 := by omega
              simp [hne] at hj
              exact hj
            rw [hminus, hq]
            norm_num
            ring
        change a.1.p (t + 1) i =
          (evolveFun (extendPath q) (t + 1) (ofRecState z)).pos i
        rw [evolveFun_succ, step_pos]
        change a.1.p (t + 1) i =
          (evolveFun (extendPath q) t (ofRecState z)).pos i +
            (if extendPath q t i = true then (1 : ℤ) else -1)
        rw [hmove, ih (Nat.le_of_lt ht) i]
        simp only [extendPath, dif_pos htr]
        rfl
  intro t i
  exact hpath (t : ℕ) (by omega) i

/-- Raw positions after an already lowered record prefix also hold for an
unfinished suffix: unlike `patOf_lower_record_suffix`, no positive duration or
first-record completion of the suffix is required. -/
theorem patOf_lower_unfinished_suffix {s : State N m}
    (hs : ∀ i, s.pos i = 0) (z : RecState N m) (j : ℕ) {k r : ℕ}
    (qf : Fin k → JumpVec N)
    (hy : ofRecState z = lower j (evolveFun (extendPath qf) k s))
    (q : Fin r → JumpVec N) {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord qf q) ⟨k + t, by omega⟩ i =
      (j : ℤ) + relP z (extendPath q) t i := by
  have hsplit := posAt_boundary (N := N) (catWord qf q) ht i
  have hpre := posAt_boundary_pref (N := N) (catWord qf q) i
  rw [suffWord_catWord] at hsplit
  rw [prefWord_catWord] at hpre
  rw [hpre] at hsplit
  have hpref := SwarmFreshPos.pos_evolveFun (extendPath qf) k s i
  rw [hs i, zero_add] at hpref
  have hraw := SwarmFreshPos.pos_evolveFun (extendPath q) t
    (evolveFun (extendPath qf) k s) i
  have hseg : relP z (extendPath q) t i =
      (evolveFun (extendPath q) t (evolveFun (extendPath qf) k s)).pos i - (j : ℤ) := by
    change (evolveFun (extendPath q) t (ofRecState z)).pos i = _
    rw [hy, ← evolveFun_lower, lower_pos]
  change SwarmFreshPos.posAt (SwarmFreshPos.seqOf (catWord qf q)) (k + t) i = _
  rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath (catWord qf q) (k + t) i (by omega), hsplit]
  rw [hseg]
  omega

/-- Concatenation is associative after its necessary raw-length transport. -/
theorem catWord_assoc_cast {k r s : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (qs : Fin s → JumpVec N) :
    castWord (Nat.add_assoc k r s) (catWord (catWord qf q) qs) =
      catWord qf (catWord q qs) := by
  funext j
  by_cases hjk : (j : ℕ) < k
  · have hkr : (j : ℕ) < k + r := by omega
    simp [castWord, catWord, hjk, hkr]
  · by_cases hjr : (j : ℕ) - k < r
    · have hkr : (j : ℕ) < k + r := by omega
      simp [castWord, catWord, hjk, hjr, hkr,
        Nat.add_sub_of_le (by omega : k ≤ (j : ℕ))]
    · have hkr : ¬ (j : ℕ) < k + r := by omega
      simp [castWord, catWord, hjk, hjr, hkr, Nat.sub_sub]

/-- Position patterns agree whenever all jumps before the evaluation time do. -/
theorem patOf_congr_prefix {K L : ℕ} (w : Fin K → JumpVec N)
    (z : Fin L → JumpVec N) {n : ℕ} (hnK : n < K + 1) (hnL : n < L + 1)
    (h : ∀ j, j < n → extendPath w j = extendPath z j) (i : Fin N) :
    patOf (N := N) w ⟨n, hnK⟩ i = patOf (N := N) z ⟨n, hnL⟩ i := by
  change posAt (seqOf w) n i = posAt (seqOf z) n i
  rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath w n i (by omega),
    SwarmFreshCyl.posAt_seqOf_eq_extendPath z n i (by omega)]
  exact posAt_congr h i

/-- Reassociation of a raw word preserves every position in its horizon. -/
theorem patOf_catWord_assoc {k r s : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (qs : Fin s → JumpVec N) {n : ℕ}
    (hn : n ≤ (k + r) + s) (i : Fin N) :
    patOf (N := N) (catWord (catWord qf q) qs) ⟨n, by omega⟩ i =
      patOf (N := N) (catWord qf (catWord q qs)) ⟨n, by omega⟩ i := by
  apply patOf_congr_prefix
  intro j hj
  rw [← catWord_assoc_cast qf q qs]
  exact (extendPath_castWord (N := N) (Nat.add_assoc k r s)
    (catWord (catWord qf q) qs) (j := j) (by omega : j < k + (r + s))).symm

/-- Jumps after the second component of a concatenation do not affect its
positions. -/
theorem patOf_catWord_right_irrel {k r s : ℕ} (qf : Fin k → JumpVec N)
    (q : Fin r → JumpVec N) (qs : Fin s → JumpVec N) {t : ℕ} (ht : t ≤ r)
    (i : Fin N) :
    patOf (N := N) (catWord qf (catWord q qs)) ⟨k + t, by omega⟩ i =
      patOf (N := N) (catWord qf q) ⟨k + t, by omega⟩ i := by
  apply patOf_congr_prefix
  intro j hj
  by_cases hjk : j < k
  · rw [extendPath_catWord_left qf (catWord q qs) hjk,
      extendPath_catWord_left qf q hjk]
  · have hjt : j - k < r := by omega
    have hjeq : j = k + (j - k) := by omega
    rw [hjeq, extendPath_catWord_right qf (catWord q qs) (by omega),
      extendPath_catWord_right qf q (by omega),
      extendPath_catWord_left q qs hjt]

/-- The raw time at the start of the `j`-th block.  The totalised block
sequence makes the recursion independent of dependent `List.take` casts. -/
noncomputable def rawTime (bs : List (RawBlock N)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => rawTime bs j + (SwarmMeasuredJoin.blockSeq bs j).1

@[simp] theorem rawTime_zero (bs : List (RawBlock N)) : rawTime bs 0 = 0 := rfl

theorem rawTime_cons_succ (b : RawBlock N) (bs : List (RawBlock N)) (j : ℕ) :
    rawTime (b :: bs) (j + 1) = b.1 + rawTime bs j := by
  induction j with
  | zero => simp [rawTime, SwarmMeasuredJoin.blockSeq_cons_zero]
  | succ j ih =>
      change rawTime (b :: bs) (j + 1) + (SwarmMeasuredJoin.blockSeq (b :: bs) (j + 1)).1 =
        b.1 + (rawTime bs j + (SwarmMeasuredJoin.blockSeq bs j).1)
      rw [ih, SwarmMeasuredJoin.blockSeq_cons_succ, Nat.add_assoc]

theorem rawTime_le_rawLen (bs : List (RawBlock N)) : ∀ {j : ℕ}, j ≤ bs.length →
    rawTime bs j ≤ rawLen bs := by
  induction bs with
  | nil => intro j hj; simp only [List.length_nil, Nat.le_zero] at hj; subst j; rfl
  | cons b bs ih =>
      intro j hj
      cases j with
      | zero => exact Nat.zero_le _
      | succ j =>
          rw [rawTime_cons_succ]
          have hle := ih (by simpa using hj)
          change b.1 + rawTime bs j ≤ b.1 + rawLen bs
          omega

theorem rawTime_length (bs : List (RawBlock N)) : rawTime bs bs.length = rawLen bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, rawTime_cons_succ, ih]
      rfl

theorem rawTime_add_le_rawLen (bs : List (RawBlock N)) :
    ∀ (l : ℕ) (hl : l < bs.length) {t : ℕ}
      (ht : t ≤ (SwarmMeasuredJoin.blockSeq bs l).1),
      rawTime bs l + t ≤ rawLen bs := by
  induction bs with
  | nil => intro l hl; simp at hl
  | cons b bs ih =>
      intro l hl
      cases l with
      | zero =>
          intro t ht
          simp only [SwarmMeasuredJoin.blockSeq_cons_zero] at ht
          change 0 + t ≤ b.1 + rawLen bs
          omega
      | succ l =>
          intro t ht
          rw [rawTime_cons_succ]
          have hrec := ih l (by simpa using hl) (by
            simpa only [SwarmMeasuredJoin.blockSeq_cons_succ] using ht)
          change b.1 + rawTime bs l + t ≤ b.1 + rawLen bs
          omega

/-- The completed-record path formula with an arbitrary earlier raw prefix.
Only the selected block is required to be a first record; the later blocks are
irrelevant at the selected time. -/
theorem patOf_rawWord_record_blocks_lower {s : State N m}
    (hs : ∀ i, s.pos i = 0) (hm : 1 ≤ m) (y : RecState N m) (j : ℕ) {k : ℕ}
    (qf : Fin k → JumpVec N)
    (hy : ofRecState y = lower j (evolveFun (extendPath qf) k s))
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    ∀ (l : ℕ) (hl : l < bs.length) {t : ℕ}
      (ht : t ≤ (SwarmMeasuredJoin.blockSeq bs l).1) (i : Fin N),
      patOf (N := N) (catWord qf (rawWord bs))
        ⟨k + (rawTime bs l + t), by
          have hlen := rawTime_add_le_rawLen bs l hl ht
          omega⟩ i =
      (j + l : ℕ) + (SwarmFreshPrefix.atom hm y
        (SwarmMeasuredJoin.blockSeq bs) l).1.p t i := by
  induction bs generalizing y j k qf with
  | nil => intro l hl; simp at hl
  | cons b bs ih =>
      intro l hl
      cases l with
      | zero =>
          intro t ht i
          have hb : FirstRecord (extendPath b.2) b.1 (ofRecState y) := hbs.1
          have hbpos : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero hb
          have hshort := patOf_lower_record_suffix hs y j qf hy b.2 hbpos hb ht i
          have hirrel := patOf_catWord_right_irrel qf b.2 (rawWord bs) ht i
          simp only [SwarmFreshPrefix.atom, SwarmFreshPrefix.ep_zero]
          rw [SwarmMeasuredJoin.blockSeq_cons_zero]
          convert hirrel.trans hshort using 1 <;>
            simp [rawWord, rawTime] <;> rfl
      | succ l =>
          intro t ht i
          have hb : FirstRecord (extendPath b.2) b.1 (ofRecState y) := hbs.1
          have hforward : ofRecState (RecKernel.out hm b.2 y) =
              lower (j + 1) (evolveFun (extendPath (catWord qf b.2)) (k + b.1) s) := by
            rw [ofRecState_out hm b.2 y hb, hy, ← evolveFun_lower,
              evolveFun_catWord_right, lower_succ]
          have hrec := ih (RecKernel.out hm b.2 y) (j + 1) (catWord qf b.2)
            hforward hbs.2 l (by simpa using hl) ht i
          have htail : t ≤ (SwarmMeasuredJoin.blockSeq bs l).1 := by simpa using ht
          have hlen := rawTime_add_le_rawLen bs l (by simpa using hl) htail
          have hassoc := patOf_catWord_assoc qf b.2 (rawWord bs)
            (n := k + b.1 + (rawTime bs l + t)) (by omega) i
          convert hassoc.symm.trans hrec using 1 <;>
            simp [rawWord, rawTime_cons_succ,
              SwarmMeasuredJoin.atom_blockSeq_cons_succ, Nat.cast_add, Nat.cast_one,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> rfl

/-- Raw positions in the unfinished suffix after an arbitrary completed record
prefix, without any earlier raw word or a first-record condition on that suffix. -/
theorem patOf_rawWord_unfinished_tail (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) (bs : List (RawBlock N)) (hbs : AllFirst hm y bs)
    {r : ℕ} (q : Fin r → JumpVec N) {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    patOf (N := N) (catWord (rawWord bs) q) ⟨rawLen bs + t, by omega⟩ i =
      (bs.length : ℤ) + relP (terminal hm y bs) (extendPath q) t i := by
  exact patOf_lower_unfinished_suffix
    (s := ofRecState y) (fun i => SwarmFreshCyl.ofRecState_pos_eq_zero hy i)
    (terminal hm y bs) bs.length (rawWord bs) (ofRecState_terminal hm y bs hbs)
    q ht i

/-- On a maximal record decomposition, the actual raw word's length transport
plays no role: positions in its unfinished tail are exactly the terminal-state
segment positions shifted by the number of completed records. -/
theorem patOf_decompWord_unfinished_tail (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    {t : ℕ} (ht : t ≤ d.tail.1) (i : Fin N) :
    patOf (N := N) (decompWord d) ⟨rawLen d.completed + t, by
      have hlen := d.len_eq
      omega⟩ i =
      (d.completed.length : ℤ) +
        relP (terminal hm y d.completed) (extendPath d.tail.2) t i := by
  have hlen := d.len_eq
  have hcast :
      patOf (N := N) (decompWord d) ⟨rawLen d.completed + t, by
        have hlen := d.len_eq
        omega⟩ i =
      patOf (N := N) (catWord (rawWord d.completed) d.tail.2)
        ⟨rawLen d.completed + t, by omega⟩ i := by
    apply patOf_congr_prefix
    intro j hj
    rw [decompWord]
    exact extendPath_castWord d.len_eq (catWord (rawWord d.completed) d.tail.2)
      (by omega : j < K)
  exact hcast.trans
    (patOf_rawWord_unfinished_tail hm hy d.completed d.allFirst d.tail.2 ht i)

/-- An empty raw prefix can be removed from every position computation through
the remaining horizon. -/
theorem patOf_zero_catWord {r : ℕ} (q : Fin r → JumpVec N)
    {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    patOf (N := N) (catWord (fun x : Fin 0 => Fin.elim0 x) q) ⟨t, by omega⟩ i =
      patOf (N := N) q ⟨t, by omega⟩ i := by
  apply patOf_congr_prefix
  intro j hj
  simpa using extendPath_catWord_right (fun x : Fin 0 => Fin.elim0 x) q
    (show j < r by omega)

/-- Completed-record blocks in the actual reassembled decomposition word have
exactly their enriched-atom positions, with the fixed raw-horizon cast retained. -/
theorem patOf_decompWord_record_blocks (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    (l : ℕ) (hl : l < d.completed.length) {t : ℕ}
    (ht : t ≤ (SwarmMeasuredJoin.blockSeq d.completed l).1) (i : Fin N) :
    patOf (N := N) (decompWord d) ⟨rawTime d.completed l + t, by
      have hlen := rawTime_add_le_rawLen d.completed l hl ht
      have hdlen := d.len_eq
      omega⟩ i =
      (l : ℤ) + (SwarmFreshPrefix.atom hm y
        (SwarmMeasuredJoin.blockSeq d.completed) l).1.p t i := by
  have hlen := rawTime_add_le_rawLen d.completed l hl ht
  have hdlen := d.len_eq
  let q0 : Fin 0 → JumpVec N := fun x => Fin.elim0 x
  have hs : ∀ i, (ofRecState y).pos i = 0 :=
    fun i => SwarmFreshCyl.ofRecState_pos_eq_zero hy i
  have hraw := patOf_rawWord_record_blocks_lower (s := ofRecState y)
    hs hm y 0 q0 (by rfl) d.completed d.allFirst l hl ht i
  have hcast :
      patOf (N := N) (decompWord d) ⟨rawTime d.completed l + t, by omega⟩ i =
      patOf (N := N) (catWord (rawWord d.completed) d.tail.2)
        ⟨rawTime d.completed l + t, by omega⟩ i := by
    apply patOf_congr_prefix
    intro j hj
    rw [decompWord]
    exact extendPath_castWord d.len_eq (catWord (rawWord d.completed) d.tail.2)
      (by omega : j < K)
  have hzero := patOf_zero_catWord (N := N)
    (catWord (rawWord d.completed) d.tail.2)
    (t := rawTime d.completed l + t) (by omega) i
  have hirrel := patOf_catWord_right_irrel q0 (rawWord d.completed) d.tail.2 hlen i
  have hraw' := hirrel.trans hraw
  simp only [Nat.zero_add] at hraw'
  simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using
    hcast.trans (hzero.symm.trans hraw')

end SwarmRawWindowCover
