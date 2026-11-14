/-
Fixed-raw-time identification on canonical enriched-record cylinders.

A maximal raw record decomposition determines the completed atoms of every
compatible enriched trajectory in its canonical cylinder.  Their cumulative
chain times are exactly the raw block times.  With the genuine initial-start
profile, the strict decoded tail is the actual raw path through the whole fixed
horizon.  Extending the cylinder to K enriched atoms therefore identifies the
actual prefixWindow K K C with the raw word's positivity and pattern guards.

This is pathwise.  It asserts no joint law, independence, stationarity,
hstruct, or probability-mass identity.
-/
import Swarm.RawWindowCover

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawWindowIdentification

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmRawWindowCover SwarmMixedTrajectory SwarmEnrichedRawTail SwarmUnfinishedTail
open SwarmFreshPrefix SwarmMeasuredJoin
open SwarmFinHorizon SwarmFreshPos SwarmRestart SwarmFinFuture

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Every list of genuine first-record blocks has at least one raw time per
block. -/
theorem length_le_rawLen_of_allFirst (hm : 1 ≤ m) (y : RecState N m) :
    ∀ (bs : List (RawBlock N)), AllFirst hm y bs → bs.length ≤ rawLen bs := by
  intro bs
  induction bs generalizing y with
  | nil => intro; rfl
  | cons b bs ih =>
      intro hbs
      have hb : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero hbs.1
      have htail := ih (RecKernel.out hm b.2 y) hbs.2
      simp only [List.length_cons, rawLen]
      omega

/-- In particular, a fixed raw horizon of length K contains enough enriched
coordinates to extend the canonical cylinder to horizon K. -/
theorem completed_length_le_K {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) : d.completed.length ≤ K := by
  have h := length_le_rawLen_of_allFirst hm y d.completed d.allFirst
  have hlen := d.len_eq
  omega

/-- A time strictly before the end of a block list belongs to a
half-open block interval; we only need an existential cover with the weak
local-duration bound used by `patOf_decompWord_record_blocks`. -/
theorem exists_block_time_of_lt_rawLen (bs : List (RawBlock N)) :
    ∀ {t : ℕ}, t < rawLen bs →
      ∃ (l : ℕ) (_hl : l < bs.length) (u : ℕ),
        u ≤ (blockSeq bs l).1 ∧ t = rawTime bs l + u := by
  induction bs with
  | nil => intro t ht; simp [rawLen] at ht
  | cons b bs ih =>
      intro t ht
      by_cases htb : t < b.1
      · refine ⟨0, by simp, t, ?_, ?_⟩
        · simpa only [blockSeq_cons_zero] using Nat.le_of_lt htb
        · simp [rawTime]
      · have hb : b.1 ≤ t := by omega
        have ht' : t - b.1 < rawLen bs := by
          change t < b.1 + rawLen bs at ht
          omega
        obtain ⟨l, hl, u, hu, htime⟩ := ih ht'
        refine ⟨l + 1, by simpa using Nat.succ_lt_succ hl, u, ?_, ?_⟩
        · simpa only [blockSeq_cons_succ] using hu
        · rw [rawTime_cons_succ]
          omega

/-- The completed atoms of an actual compatible trajectory on a canonical
trajectory cylinder are exactly the decomposition's atoms. -/
theorem completed_atom_of_mem_canonical {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (A : ℕ → SwarmInfSeg.Pair N m)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d) {l : ℕ} (hl : l < d.completed.length) :
    A l = atom hm y (blockSeq d.completed) l := by
  exact hmem.1 ⟨l, hl⟩

/-- The final supplied atom has the actual strict decoded unfinished tail. -/
theorem next_mem_tailPrefixSet_of_mem_canonical {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (A : ℕ → SwarmInfSeg.Pair N m)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d) :
    A d.completed.length ∈ TailPrefixSet (N := N) (m := m) d.tail.2 := by
  exact hmem.2

/-- Completed cumulative chain times are exactly the raw block times. -/
theorem chain_cum_eq_rawTime {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d) :
    ∀ {l : ℕ}, l ≤ d.completed.length →
      (SwarmChainAssemble.chainOf A).cum l = rawTime d.completed l := by
  intro l
  induction l with
  | zero => intro; rw [SwarmConcat.Chain.cum_zero, rawTime_zero]
  | succ l ih =>
      intro hl
      have hln : l < d.completed.length := by omega
      rw [SwarmConcat.Chain.cum_succ, SwarmChainAssemble.chainOf_seg_of_compat hA,
        rawTime, ih (by omega), completed_atom_of_mem_canonical d A hmem hln]
      have hfr := firstRecord_blockSeq hm y d.allFirst hln
      have hk : 0 < (blockSeq d.completed l).1 := SwarmDHStruct.firstRecord_ne_zero hfr
      rw [show (atom hm y (blockSeq d.completed) l).1.dur =
        (blockSeq d.completed l).1 from
          SwarmFreshCyl.segOf_dur_of_firstRecord hk _ hfr]

/-- The completed chain path equals the actual atom segment, including the
upper record endpoint. -/
theorem chain_X_completed_block {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d)
    {l : ℕ} (hl : l < d.completed.length) {t : ℕ}
    (ht : t ≤ (blockSeq d.completed l).1) (i : Fin N) :
    (SwarmChainAssemble.chainOf A).X (rawTime d.completed l + t) i =
      (l : ℤ) + (atom hm y (blockSeq d.completed) l).1.p t i := by
  have hcum := chain_cum_eq_rawTime d hA hmem (show l ≤ d.completed.length by omega)
  have hfr := firstRecord_blockSeq hm y d.allFirst hl
  have hk : 0 < (blockSeq d.completed l).1 := SwarmDHStruct.firstRecord_ne_zero hfr
  have hdur : (atom hm y (blockSeq d.completed) l).1.dur =
      (blockSeq d.completed l).1 :=
    SwarmFreshCyl.segOf_dur_of_firstRecord hk _ hfr
  rw [← hcum]
  rcases t with _ | t
  · simpa using (SwarmChainAssemble.chainOf_X_record hA l i).trans
      (congrArg (fun z : ℤ => (l : ℤ) + z)
        (congrArg (fun a : SwarmInfSeg.Pair N m => a.1.p 0 i)
          (completed_atom_of_mem_canonical d A hmem hl)))
  · rw [SwarmChainAssemble.chainOf_X_cum_add hA (Nat.succ_pos t) (by
        rw [completed_atom_of_mem_canonical d A hmem hl, hdur]
        exact ht) i]
    rw [completed_atom_of_mem_canonical d A hmem hl]

/-- At the last completed atom, the segment endpoint is one level above the
actual terminal record state's own positions. -/
theorem atom_end_last {hm : 1 ≤ m} (y : RecState N m) {bs : List (RawBlock N)}
    (hbs : AllFirst hm y bs) {j : ℕ} (hj : j < bs.length)
    (hlast : j + 1 = bs.length) (i : Fin N) :
    (atom hm y (blockSeq bs) j).1.p (atom hm y (blockSeq bs) j).1.dur i =
      1 + (Record.ofRecState (terminal hm y bs)).pos i := by
  have hfr := firstRecord_blockSeq hm y hbs hj
  have hk : 0 < (blockSeq bs j).1 := SwarmDHStruct.firstRecord_ne_zero hfr
  have hseg : SwarmSegKernel.segOf (ep hm y (blockSeq bs) j)
      (blockSeq bs j).1 (blockSeq bs j).2 =
      SwarmSegKernel.segOfFirst (ep hm y (blockSeq bs) j)
        (blockSeq bs j).1 (blockSeq bs j).2 hk hfr :=
    SwarmDHStruct.segOf_of_firstRecord hk hfr
  change (SwarmSegKernel.segOf (ep hm y (blockSeq bs) j)
    (blockSeq bs j).1 (blockSeq bs j).2).p
      (SwarmSegKernel.segOf (ep hm y (blockSeq bs) j)
        (blockSeq bs j).1 (blockSeq bs j).2).dur i = _
  rw [SwarmFreshCyl.segOf_dur_of_firstRecord hk _ hfr, hseg,
    SwarmSegKernel.segOfFirst_p_dur _ hm _ hk hfr i]
  have hep : ep hm y (blockSeq bs) (j + 1) = terminal hm y bs := by
    rw [hlast]
    exact ep_blockSeq_length hm y bs
  exact congrArg (fun z : ℤ => 1 + z)
    (congrArg (fun z : RecState N m => (Record.ofRecState z).pos i) hep)

/-- Compatibility and the canonical pins determine the final atom's start at
its genuine terminal state.  Only the usual initial-start profile is imposed;
all subsequent starts are derived. -/
theorem next_start_eq_relP {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i) (i : Fin N) :
    (A d.completed.length).1.p 0 i =
      relP (terminal hm y d.completed) (extendPath d.tail.2) 0 i := by
  rcases Nat.eq_zero_or_pos d.completed.length with hn | hn
  · have hnil : d.completed = [] := List.length_eq_zero_iff.mp hn
    rw [hn, relP_zero]
    have ht : terminal hm y d.completed = y := by rw [hnil]; rfl
    rw [ht]
    exact hstart i
  · obtain ⟨j, hj⟩ : ∃ j, d.completed.length = j + 1 :=
      ⟨d.completed.length - 1, by omega⟩
    have hjl : j < d.completed.length := by omega
    have hlast : j + 1 = d.completed.length := hj.symm
    have hc := hA j i
    rw [completed_atom_of_mem_canonical d A hmem hjl,
      atom_end_last y d.allFirst hjl hlast i] at hc
    rw [hj, relP_zero]
    omega

/-- The chain path in the next, genuinely unfinished record is exactly the raw
terminal-state segment through the cut. -/
theorem chain_X_unfinished_tail {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i)
    {t : ℕ} (ht : t ≤ d.tail.1) (i : Fin N) :
    (SwarmChainAssemble.chainOf A).X (rawLen d.completed + t) i =
      (d.completed.length : ℤ) +
        relP (terminal hm y d.completed) (extendPath d.tail.2) t i := by
  have hcum : (SwarmChainAssemble.chainOf A).cum d.completed.length =
      rawLen d.completed := by
    rw [chain_cum_eq_rawTime d hA hmem le_rfl, rawTime_length]
  have htail := next_mem_tailPrefixSet_of_mem_canonical d A hmem
  have hnext := next_start_eq_relP d hA hmem hstart
  have hunfinished : A d.completed.length ∈ unfinishedTailSet
      (N := N) (m := m) (terminal hm y d.completed) d.tail.2 :=
    mem_unfinishedTailSet_of_tailPrefixSet htail hnext
  have hdur : t ≤ (A d.completed.length).1.dur :=
    le_trans ht (Nat.le_of_lt htail.1)
  rw [← hcum]
  rcases t with _ | t
  · simpa only [Nat.add_zero, relP_zero] using
      (SwarmChainAssemble.chainOf_X_record hA d.completed.length i).trans
        (congrArg (fun z : ℤ => (d.completed.length : ℤ) + z) (hnext i))
  · rw [SwarmChainAssemble.chainOf_X_cum_add hA (Nat.succ_pos t) hdur i]
    exact congrArg (fun z : ℤ => (d.completed.length : ℤ) + z)
      (hunfinished.2 ⟨t + 1, by omega⟩ i)

/-- Through the whole fixed raw horizon, the enriched chain path is the
actual raw path of the reassembled decomposition word. -/
theorem chain_X_eq_decomp_pos {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (hy : y ∈ srSet N m)
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i)
    {t : ℕ} (ht : t ≤ K) (i : Fin N) :
    (SwarmChainAssemble.chainOf A).X t i = posAt (seqOf (decompWord d)) t i := by
  change (SwarmChainAssemble.chainOf A).X t i =
    patOf (N := N) (decompWord d) ⟨t, by omega⟩ i
  by_cases htraw : t < rawLen d.completed
  · obtain ⟨l, hl, u, hu, htime⟩ := exists_block_time_of_lt_rawLen d.completed htraw
    have hindex : (⟨t, by omega⟩ : Fin (K + 1)) =
        ⟨rawTime d.completed l + u, by omega⟩ := Fin.ext htime
    rw [hindex]
    exact (congrArg (fun n => (SwarmChainAssemble.chainOf A).X n i) htime).trans
      ((chain_X_completed_block d hA hmem hl hu i).trans
        (patOf_decompWord_record_blocks hm hy d l hl hu i).symm)
  · have hle : rawLen d.completed ≤ t := by omega
    let u := t - rawLen d.completed
    have hu : u ≤ d.tail.1 := by
      have hlen := d.len_eq
      dsimp [u]
      omega
    have htime : t = rawLen d.completed + u := by
      dsimp [u]
      omega
    have hindex : (⟨t, by omega⟩ : Fin (K + 1)) =
        ⟨rawLen d.completed + u, by omega⟩ := Fin.ext htime
    rw [hindex]
    exact (congrArg (fun n => (SwarmChainAssemble.chainOf A).X n i) htime).trans
      ((chain_X_unfinished_tail d hA hmem hstart hu i).trans
        (patOf_decompWord_unfinished_tail hm hy d hu i).symm)

/-- For the raw word's infinite extension, finite strict positivity is exactly
`PosSeqFin`; no endpoint or probability condition is added. -/
theorem mem_finStrict_rawPath {K : ℕ} (q : Fin K → JumpVec N) :
    (fun n i => posAt (seqOf q) n i) ∈ finStrict (N := N) K ↔
      PosSeqFin (N := N) q := by
  rw [mem_finStrict, SwarmFreshCyl.posWord_iff]
  constructor
  · rintro ⟨-, hpos⟩ n hn hnK i
    rw [← SwarmFreshCyl.posAt_seqOf_eq_extendPath q n i hnK]
    exact hpos n (by omega) hnK i
  · intro hpos
    refine ⟨fun i => posAt_zero (seqOf q) i, ?_⟩
    intro n hn hnK i
    rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath q n i hnK]
    exact hpos n hn hnK i

/-- On a pinned canonical cylinder, the actual fixed-raw-time chain window is
literally the reassembled raw word's positivity and arbitrary pattern guard. -/
theorem mem_chainWindow_iff_raw_guards {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (hy : y ∈ srSet N m)
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : SwarmChainAssemble.TrajCompat A)
    (hmem : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    SwarmChainAssemble.chainOf A ∈ chainWindow (N := N) K K C ↔
      PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C := by
  have hX : ∀ t, t ≤ K → ∀ i,
      chainPath (SwarmChainAssemble.chainOf A) t i = posAt (seqOf (decompWord d)) t i :=
    fun t ht i => chain_X_eq_decomp_pos d hy hA hmem hstart ht i
  have hpat : pathPat (N := N) K (chainPath (SwarmChainAssemble.chainOf A)) =
      patOf (N := N) (decompWord d) := by
    funext t i
    exact hX (t : ℕ) (by have := t.2; omega) i
  have hstrict : chainPath (SwarmChainAssemble.chainOf A) ∈ finStrict (N := N) K ↔
      (fun n i => posAt (seqOf (decompWord d)) n i) ∈ finStrict (N := N) K := by
    rw [mem_finStrict, mem_finStrict]
    constructor
    · rintro ⟨h0, hpos⟩
      refine ⟨fun i => ?_, fun n hn hnK i => ?_⟩
      · rw [← hX 0 (Nat.zero_le K) i]
        exact h0 i
      · rw [← hX n hnK i]
        exact hpos n hn hnK i
    · rintro ⟨h0, hpos⟩
      refine ⟨fun i => ?_, fun n hn hnK i => ?_⟩
      · rw [hX 0 (Nat.zero_le K) i]
        exact h0 i
      · rw [hX n hnK i]
        exact hpos n hn hnK i
  change chainPath (SwarmChainAssemble.chainOf A) ∈
    finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C ↔ _
  rw [Set.mem_inter_iff, Set.mem_preimage, hstrict, hpat, mem_finStrict_rawPath]

/-- Membership in a bounded canonical extension restricts to membership in
its original canonical cylinder. -/
theorem short_canonical_of_mem_extension {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) {A : ℕ → SwarmInfSeg.Pair N m}
    (h : d.completed.length ≤ K)
    (hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      canonicalTrajectoryWindowExtension y d h) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length A ∈
      canonicalTrajectoryWindow y d := by
  exact hExt

/-- **Fixed-raw-time enriched-chain identification.**  On the canonical
cylinder extended to the genuinely common horizon K, actual `prefixWindow`
membership is exactly the raw decomposition word's positivity and arbitrary
pattern guard.  The initial-start profile is the sole additional path
condition; compatibility and all finite/Iic/time bounds are explicit. -/
theorem mem_prefixWindow_on_canonicalExtension_iff
    {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (hy : y ∈ srSet N m)
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : SwarmChainAssemble.TrajCompat A)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i)
    (h : d.completed.length ≤ K) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
        canonicalTrajectoryWindowExtension y d h ∩ prefixWindow (N := N) (m := m) K K C ↔
      Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
        canonicalTrajectoryWindowExtension y d h ∧
      (PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C) := by
  have hprefix := mem_prefixWindow_iff_chain (N := N) (m := m)
    (K := K) (n := K) (C := C) (A := A) le_rfl hA
  have hident (hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      canonicalTrajectoryWindowExtension y d h) :=
    mem_chainWindow_iff_raw_guards d hy hA
      (short_canonical_of_mem_extension d h hExt) hstart C
  constructor
  · rintro ⟨hExt, hwindow⟩
    exact ⟨hExt, (hident hExt).mp (hprefix.mp hwindow)⟩
  · rintro ⟨hExt, hraw⟩
    exact ⟨hExt, hprefix.mpr ((hident hExt).mpr hraw)⟩

/-- Conditional form of the fixed-raw-time identification, ready for a
pointwise or almost-everywhere cover argument. -/
theorem mem_prefixWindow_of_mem_canonicalExtension
    {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (hy : y ∈ srSet N m)
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : SwarmChainAssemble.TrajCompat A)
    (hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i)
    (h : d.completed.length ≤ K)
    (hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      canonicalTrajectoryWindowExtension y d h)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
        prefixWindow (N := N) (m := m) K K C ↔
      PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C := by
  have hiff := mem_prefixWindow_on_canonicalExtension_iff d hy hA hstart h C
  constructor
  · intro hwindow
    exact (hiff.mp ⟨hExt, hwindow⟩).2
  · intro hraw
    exact (hiff.mpr ⟨hExt, hraw⟩).2

/-- The forward direction needs no separate start hypothesis: actual
`prefixWindow` membership forces the time-zero chain path to vanish, while
`y ∈ srSet` says precisely the same for the initial record profile. -/
theorem raw_guards_of_mem_prefixWindow_canonicalExtension
    {hm : 1 ≤ m} {y : RecState N m} {K : ℕ}
    (d : MaxRecordDecomp (N := N) hm y K) (hy : y ∈ srSet N m)
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : SwarmChainAssemble.TrajCompat A)
    (h : d.completed.length ≤ K)
    (hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      canonicalTrajectoryWindowExtension y d h)
    {C : Set (Fin (K + 1) → Fin N → ℤ)}
    (hwindow : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      prefixWindow (N := N) (m := m) K K C) :
    PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C := by
  have hprefix := mem_prefixWindow_iff_chain (N := N) (m := m)
    (K := K) (n := K) (C := C) (A := A) le_rfl hA
  have hchain := hprefix.mp hwindow
  have hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i := by
    intro i
    have hc0 := hchain.1.1 i
    have hrecord := SwarmChainAssemble.chainOf_X_record hA 0 i
    rw [SwarmConcat.Chain.cum_zero] at hrecord
    change (SwarmChainAssemble.chainOf A).X 0 i = 0 at hc0
    rw [hrecord] at hc0
    simp only [Nat.cast_zero, zero_add] at hc0
    rw [SwarmFreshCyl.ofRecState_pos_eq_zero hy i]
    exact hc0
  exact (mem_prefixWindow_of_mem_canonicalExtension d hy hA hstart h hExt C).mp hwindow

end SwarmRawWindowIdentification
