/- Record-offset induction for the global coherent canonical cover. -/
import Swarm.RawGlobalCover

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawGlobalCover

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalFixedHorizon SwarmCanonicalJoinedWindow
open SwarmRawWindowIdentification SwarmEnrichedRawTail
open SwarmChainAssemble SwarmFinFuture SwarmFinHorizon SwarmFreshPos
open SwarmInfSeg SwarmFreshPrefix SwarmMeasuredJoin SwarmUnfinishedTail
open SwarmMixedTrajectory

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- Relative decoder, with no zero-start assumption. -/
theorem posAt_pathWord_sub {N K : ℕ} (X : ℕ → Fin N → ℤ)
    (hstep : ∀ n i, X (n + 1) i = X n i + 1 ∨ X (n + 1) i = X n i - 1) :
    ∀ {n : ℕ}, n ≤ K → ∀ i,
      posAt (seqOf (pathWord X (K := K))) n i = X n i - X 0 i := by
  intro n
  induction n with
  | zero => intro _ i; simp [posAt_zero]
  | succ n ih =>
      intro hn i
      have hnK : n < K := by omega
      rw [posAt_succ, ih (by omega) i]
      have hval : seqOf (pathWord X (K := K)) n i = pathWord X (K := K) ⟨n, hnK⟩ i := by
        exact congrFun (seqOf_val (pathWord X (K := K)) ⟨n, hnK⟩) i
      rw [hval]
      rcases hstep n i with h | h
      · simp [pathWord, h]
        ring
      · have hne : ¬ X n i - 1 = X n i + 1 := by omega
        simp [pathWord, h, hne]
        ring

/-- The raw state evolution of the decoded word is the original path whenever
its initial state is the original path's initial position. -/
theorem evolve_pathWord {N K : ℕ} (X : ℕ → Fin N → ℤ) {y : RecState N m}
    (hstart : ∀ i, X 0 i = (Record.ofRecState y).pos i)
    (hstep : ∀ n i, X (n + 1) i = X n i + 1 ∨ X (n + 1) i = X n i - 1)
    {n : ℕ} (hn : n ≤ K) (i : Fin N) :
    (evolveFun (extendPath (pathWord X (K := K))) n (ofRecState y)).pos i = X n i := by
  rw [SwarmFreshPos.pos_evolveFun, ← SwarmFreshCyl.posAt_seqOf_eq_extendPath
    (pathWord X (K := K)) n i hn, posAt_pathWord_sub X hstep hn i, hstart i]
  ring

/-- The chain path with record level `r` and its initial raw time removed. -/
noncomputable def offsetPath (A : ℕ → SwarmInfSeg.Pair N m) (r : ℕ) : ℕ → Fin N → ℤ :=
  fun t i => (SwarmChainAssemble.chainOf A).X
    ((SwarmChainAssemble.chainOf A).cum r + t) i - (r : ℤ)

/-- An offset path is still a nearest-neighbour path. -/
theorem offsetPath_step {A : ℕ → SwarmInfSeg.Pair N m} (r n : ℕ) (i : Fin N) :
    offsetPath A r (n + 1) i = offsetPath A r n i + 1 ∨
      offsetPath A r (n + 1) i = offsetPath A r n i - 1 := by
  rcases (SwarmChainAssemble.chainOf A).X_step
    ((SwarmChainAssemble.chainOf A).cum r + n) i with h | h
  · left
    dsimp [offsetPath]
    rw [show (SwarmChainAssemble.chainOf A).cum r + (n + 1) =
      (SwarmChainAssemble.chainOf A).cum r + n + 1 by omega, h]
    ring
  · right
    dsimp [offsetPath]
    rw [show (SwarmChainAssemble.chainOf A).cum r + (n + 1) =
      (SwarmChainAssemble.chainOf A).cum r + n + 1 by omega, h]
    ring

/-- Within the first atom after offset `r`, the offset chain path is exactly
that atom's own relative positions. -/
theorem offsetPath_firstSegment {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : TrajCompat A) (r : ℕ) {t : ℕ} (ht : t ≤ (A r).1.dur) (i : Fin N) :
    offsetPath A r t i = (A r).1.p t i := by
  rcases t with _ | t
  · simpa [offsetPath] using congrArg (fun z : ℤ => z - (r : ℤ))
      (SwarmChainAssemble.chainOf_X_record hA r i)
  · have h := congrArg (fun z : ℤ => z - (r : ℤ))
      (SwarmChainAssemble.chainOf_X_cum_add hA (Nat.succ_pos t)
        (by simpa using ht) i)
    simpa [offsetPath] using h

/-- On a coherent trajectory the offset path starts at the initial record
state's own positions. -/
theorem offsetPath_start {hm : 1 ≤ m} {y : RecState N m}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A) {r : ℕ}
    (hCoh : Coherent hm y (fun n => A (r + n))) (i : Fin N) :
    offsetPath A r 0 i = (Record.ofRecState y).pos i := by
  obtain ⟨b, hb, hAtom⟩ := hCoh.1
  simp only [Nat.add_zero] at hAtom
  have hzero : (A r).1.p 0 i = (Record.ofRecState y).pos i := by
    rw [hAtom]
    exact SwarmSegKernel.segOf_p_zero y b.1 b.2 i
  rw [offsetPath, Nat.add_zero, SwarmChainAssemble.chainOf_X_record hA r i, hzero]
  ring

/-- A coherent first atom's entire relative path is its represented raw
first-record evolution. -/
theorem canonicalAtom_p {hm : 1 ≤ m} {y : RecState N m}
    {a : SwarmInfSeg.Pair N m} (ha : CanonicalAtom hm y a) :
    ∃ b : RawBlock N, FirstRecord (extendPath b.2) b.1 (ofRecState y) ∧
      a = (SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y) ∧
      a.1.dur = b.1 ∧
      (∀ t i, a.1.p t i =
        (evolveFun (extendPath b.2) t (ofRecState y)).pos i) := by
  obtain ⟨b, hb, hEq⟩ := ha
  refine ⟨b, hb, hEq, ?_, ?_⟩
  · rw [hEq]
    exact SwarmFreshCyl.segOf_dur_of_firstRecord
      (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb
  · intro t i
    rw [hEq]
    change (SwarmSegKernel.segOf y b.1 b.2).p t i = _
    rw [SwarmFreshCyl.segOf_p_of_firstRecord
      (SwarmDHStruct.firstRecord_ne_zero hb) b.2 hb]
    rfl

/-- The first completed block of a decomposition of the actual offset path is
exactly the next coherent atom's decoded block. -/
theorem head_block_eq_segBlock {hm : 1 ≤ m} {y : RecState N m} {K r : ℕ}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A)
    (hCoh : Coherent hm y (fun n => A (r + n)))
    (d : MaxRecordDecomp (N := N) hm y K) {b : RawBlock N}
    {bs : List (RawBlock N)} (hd : d.completed = b :: bs)
    (hword : decompWord d = pathWord (offsetPath A r) (K := K)) :
    b = segBlock (A r).1 := by
  obtain ⟨a, ha, hAtom, hdur, hpath⟩ := canonicalAtom_p hCoh.1
  simp only [Nat.add_zero] at hAtom hdur hpath
  have hfb : FirstRecord (extendPath (decompWord d)) b.1 (ofRecState y) :=
    firstRecord_decompWord_of_completed_cons d hd
  have hbK : b.1 ≤ K := by
    have hlen := d.len_eq
    rw [hd] at hlen
    simp only [rawLen] at hlen
    omega
  have hstart := offsetPath_start hA hCoh
  have hstep := offsetPath_step (A := A) r
  have hraw : ∀ t : ℕ, t ≤ K → t ≤ (A r).1.dur → ∀ i,
      (evolveFun (extendPath (decompWord d)) t (ofRecState y)).pos i =
        (A r).1.p t i := by
    intro t htK ht i
    rw [hword, evolve_pathWord (offsetPath A r) hstart hstep htK i]
    exact offsetPath_firstSegment hA r ht i
  have hlen : b.1 = a.1 := by
    apply le_antisymm
    · by_contra hnot
      have hba : a.1 < b.1 := by omega
      have haK : a.1 ≤ K := by omega
      obtain ⟨i, hi⟩ := ha.1
      have hlt := hfb.2 a.1 hba i
      have hr := hraw a.1 haK (by omega) i
      rw [hpath a.1 i] at hr
      omega
    · by_contra hnot
      have hab : b.1 < a.1 := by omega
      obtain ⟨i, hi⟩ := hfb.1
      have hlt := ha.2 b.1 hab i
      have hr := hraw b.1 hbK (by omega) i
      rw [hpath b.1 i] at hr
      omega
  apply rawBlock_ext (hlen.trans hdur.symm)
  intro j
  have hjb : j.1 < b.1 := j.isLt
  have hjK : j.1 < K := by omega
  have hjA : j.1 < (A r).1.dur := by omega
  have hbext := extendPath_decompWord_of_completed_cons d hd j.isLt
  rw [hword] at hbext
  simp only [extendPath, dif_pos hjK, dif_pos j.isLt] at hbext
  calc
    b.2 j = pathWord (offsetPath A r) (K := K) ⟨j.1, hjK⟩ := by
      simpa using hbext.symm
    _ = segWord (A r).1 ⟨j.1, hjA⟩ := by
      funext i
      simp only [pathWord, segWord]
      rw [offsetPath_firstSegment hA r (by omega) i,
        offsetPath_firstSegment hA r (by omega) i]
    _ = (segBlock (A r).1).2 ⟨j.1, hjA⟩ := rfl

/-- Dropping `b` raw steps and lowering the path by one preserves its decoded
nearest-neighbour word. -/
theorem pathWord_shift {N K L b : ℕ} (X : ℕ → Fin N → ℤ) (hbK : b + L = K) :
    (fun j : Fin L => pathWord X (K := K) ⟨b + j.1, by omega⟩) =
      pathWord (fun t i => X (b + t) i - 1) (K := L) := by
  funext j i
  simp only [pathWord]
  by_cases h : X (b + j.1 + 1) i = X (b + j.1) i + 1
  · have h' : X (b + (j.1 + 1)) i - 1 = X (b + j.1) i - 1 + 1 := by
      rw [show b + (j.1 + 1) = b + j.1 + 1 by omega]
      omega
    simp [h, h']
  · have h' : ¬ X (b + (j.1 + 1)) i - 1 = X (b + j.1) i - 1 + 1 := by
      rw [show b + (j.1 + 1) = b + j.1 + 1 by omega]
      omega
    have h'' : ¬ X (b + (j.1 + 1)) i - 1 = X (b + j.1) i := by omega
    simp [h, h', h'']

/-- With no completed block, the next coherent atom contains precisely the
maximal unfinished tail and continues strictly beyond it. -/
theorem tail_mem_of_completed_nil {hm : 1 ≤ m} {y : RecState N m} {K r : ℕ}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A)
    (hCoh : Coherent hm y (fun n => A (r + n)))
    (d : MaxRecordDecomp (N := N) hm y K) (hd : d.completed = [])
    (hword : decompWord d = pathWord (offsetPath A r) (K := K)) :
    A r ∈ TailPrefixSet (N := N) (m := m) d.tail.2 := by
  obtain ⟨a, ha, hAtom, hdur, hpath⟩ := canonicalAtom_p hCoh.1
  simp only [Nat.add_zero] at hAtom hdur hpath
  have htlen : d.tail.1 = K := by
    have hlen := d.len_eq
    rw [hd] at hlen
    simpa [rawLen] using hlen
  have hno := noRecordPrefix_decompWord_of_completed_nil d hd
  have hstart := offsetPath_start hA hCoh
  have hstep := offsetPath_step (A := A) r
  have hraw : ∀ t : ℕ, t ≤ K → t ≤ (A r).1.dur → ∀ i,
      (evolveFun (extendPath (decompWord d)) t (ofRecState y)).pos i =
        (A r).1.p t i := by
    intro t htK ht i
    rw [hword, evolve_pathWord (offsetPath A r) hstart hstep htK i]
    exact offsetPath_firstSegment hA r ht i
  have hlt : K < (A r).1.dur := by
    by_contra hnot
    have hkK : (A r).1.dur ≤ K := by omega
    apply hno (A r).1.dur (A r).1.dur_pos hkK
    constructor
    · obtain ⟨i, hi⟩ := ha.1
      refine ⟨i, ?_⟩
      have hr := hraw a.1 (by omega) (by omega) i
      rw [hpath a.1 i] at hr
      rw [hdur]
      omega
    · intro t ht i
      have hr := hraw t (by omega) (by omega) i
      rw [hpath t i] at hr
      have hbefore := ha.2 t (by omega) i
      omega
  refine ⟨by omega, ?_⟩
  intro j
  have hjK : j.1 < K := by omega
  have hxt := extendPath_decompWord_of_completed_nil d hd hjK
  rw [hword] at hxt
  simp only [extendPath, dif_pos hjK, dif_pos j.isLt] at hxt
  rw [← hxt]
  funext i
  simp only [segJump, pathWord]
  rw [offsetPath_firstSegment hA r (by omega) i,
    offsetPath_firstSegment hA r (by omega) i]

/-- Coherence at the next record offset is the part of coherence after the
first atom, with no auxiliary trajectory construction. -/
theorem coherent_offset_succ {hm : 1 ≤ m} {y : RecState N m}
    {A : ℕ → SwarmInfSeg.Pair N m} {r : ℕ}
    (hCoh : Coherent hm y (fun n => A (r + n))) :
    Coherent hm (A r).2 (fun n => A (r + 1 + n)) := by
  refine ⟨?_, ?_⟩
  · simpa [Nat.add_zero, Nat.add_assoc] using hCoh.2 0
  · intro n
    have h := hCoh.2 (n + 1)
    simpa [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Removing the first coherent atom shifts the offset path by its raw
length and lowers the record level by one. -/
theorem offsetPath_succ {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : TrajCompat A) (r b : ℕ) (hb : b = (A r).1.dur) :
    offsetPath A (r + 1) = fun t i => offsetPath A r (b + t) i - 1 := by
  have hcum : (SwarmChainAssemble.chainOf A).cum (r + 1) =
      (SwarmChainAssemble.chainOf A).cum r + b := by
    rw [SwarmConcat.Chain.cum_succ, SwarmChainAssemble.chainOf_seg_of_compat hA, hb]
  funext t i
  change (SwarmChainAssemble.chainOf A).X
      ((SwarmChainAssemble.chainOf A).cum (r + 1) + t) i - ((r + 1 : ℕ) : ℤ) =
    (SwarmChainAssemble.chainOf A).X
      ((SwarmChainAssemble.chainOf A).cum r + (b + t)) i - (r : ℤ) - 1
  rw [hcum, show (SwarmChainAssemble.chainOf A).cum r + b + t =
    (SwarmChainAssemble.chainOf A).cum r + (b + t) by omega]
  push_cast
  ring

/-- **Pathwise coherent canonical cover at a record offset.**  The unique
maximal decomposition of the actual raw path pins every completed atom and the
next genuinely unfinished atom. -/
theorem mem_canonicalNextRecordWindow_of_coherent {hm : 1 ≤ m} {y : RecState N m}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A) :
    ∀ (K r : ℕ) (d : MaxRecordDecomp (N := N) hm y K),
      Coherent hm y (fun n => A (r + n)) →
      decompWord d = pathWord (offsetPath A r) (K := K) →
      (fun j : Fin (d.completed.length + 1) => A (r + j.1)) ∈
        canonicalNextRecordWindow y d := by
  intro K r
  induction K using Nat.strong_induction_on generalizing y r with
  | h K ih =>
      intro d hCoh hword
      by_cases hnil : d.completed = []
      · have hlen : d.completed.length = 0 := by simp [hnil]
        have htail := tail_mem_of_completed_nil hA hCoh d hnil hword
        rw [canonicalNextRecordWindow]
        refine ⟨?_, ?_⟩
        · intro j
          have hj := j.isLt
          omega
        · simpa [hlen] using htail
      · obtain ⟨b, bs, hd⟩ := List.exists_cons_of_ne_nil hnil
        have hbhead := head_block_eq_segBlock hA hCoh d hd hword
        have hbdur : b.1 = (A r).1.dur := congrArg Sigma.fst hbhead
        obtain ⟨a, ha, hEq⟩ := hCoh.1
        simp only [Nat.add_zero] at hEq
        have hseg : segBlock (A r).1 = a := by
          rw [hEq]
          exact segBlock_segOf y (SwarmDHStruct.firstRecord_ne_zero ha) a.2 ha
        have hba : b = a := hbhead.trans hseg
        have hb0 : blockSeq (b :: bs) 0 = b := blockSeq_cons_zero b bs
        have hstate : (A r).2 = RecKernel.out hm b.2 y := by
          rw [hba]
          exact congrArg Prod.snd hEq
        have hhead : A r = SwarmFreshPrefix.atom hm y (blockSeq (b :: bs)) 0 := by
          rw [hba] at hb0 ⊢
          unfold SwarmFreshPrefix.atom
          rw [hb0]
          exact hEq
        have hbfirst : FirstRecord (extendPath b.2) b.1 (ofRecState y) := by
          have hall := d.allFirst
          rw [hd] at hall
          exact hall.1
        have hbpos : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero hbfirst
        have hbK : b.1 ≤ K := by
          have hlen := d.len_eq
          rw [hd] at hlen
          simp only [rawLen] at hlen
          omega
        have hCs : Coherent hm (RecKernel.out hm b.2 y) (fun n => A (r + 1 + n)) := by
          have h := coherent_offset_succ hCoh
          rwa [hstate] at h
        have hoff := offsetPath_succ hA r b.1 hbdur
        have hrecWord : decompWord (dropHead d hd) =
            pathWord (offsetPath A (r + 1)) (K := K - b.1) := by
          funext j
          calc
            decompWord (dropHead d hd) j =
                decompWord d ⟨b.1 + j.1, by
                  have hlen := d.len_eq
                  rw [hd] at hlen
                  simp only [rawLen] at hlen
                  omega⟩ := decompWord_dropHead d hd j
            _ = pathWord (offsetPath A r) (K := K) ⟨b.1 + j.1, by
                  have hlen := d.len_eq
                  rw [hd] at hlen
                  simp only [rawLen] at hlen
                  omega⟩ := congrFun hword _
            _ = pathWord (fun t i => offsetPath A r (b.1 + t) i - 1)
                  (K := K - b.1) j := by
                exact congrFun (pathWord_shift (offsetPath A r)
                  (b := b.1) (L := K - b.1) (by omega)) j
            _ = pathWord (offsetPath A (r + 1)) (K := K - b.1) j := by rw [hoff]
        have hrec := ih (K - b.1) (by omega) (y := RecKernel.out hm b.2 y)
          (r := r + 1) (dropHead d hd) hCs hrecWord
        rw [canonicalNextRecordWindow, hd]
        refine ⟨?_, ?_⟩
        · intro j
          refine Fin.cases ?_ (fun l => ?_) j
          · simpa [SwarmChain.initF] using hhead
          · have hr := hrec.1 l
            simpa [SwarmChain.initF, dropHead, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, atom_blockSeq_cons_succ] using hr
        · have htail : A (r + 1 + bs.length) ∈
              TailPrefixSet (N := N) (m := m) d.tail.2 := by
            simpa [dropHead] using hrec.2
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- The coherent path cover at the initial record offset. -/
theorem exists_natCanonicalCylinder_and_pathPat {hm : 1 ≤ m} {y : RecState N m}
    (hy : y ∈ srSet N m) {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : TrajCompat A) (hCoh : Coherent hm y A) (K : ℕ) :
    ∃ d : MaxRecordDecomp (N := N) hm y K,
      A ∈ natCanonicalCylinder hm y d ∧
      patOf (N := N) (decompWord d) =
        pathPat (N := N) K (chainPath (SwarmChainAssemble.chainOf A)) := by
  obtain ⟨d, hd⟩ := exists_maxRecordDecomp y K (pathWord (offsetPath A 0) (K := K))
  have hCs : Coherent hm y (fun n => A (0 + n)) := by simpa using hCoh
  have hmem := mem_canonicalNextRecordWindow_of_coherent hA K 0 d hCs hd
  have hnat : A ∈ natCanonicalCylinder hm y d := by
    simpa [natCanonicalCylinder] using hmem
  have hstart : ∀ i, offsetPath A 0 0 i = 0 := by
    intro i
    rw [← SwarmFreshCyl.ofRecState_pos_eq_zero hy i]
    exact offsetPath_start hA hCs i
  have hpat0 := patOf_pathWord (K := K) (offsetPath A 0) hstart (offsetPath_step (A := A) 0)
  have hoff : offsetPath A 0 = chainPath (SwarmChainAssemble.chainOf A) := by
    funext t i
    simp only [offsetPath, chainPath, SwarmConcat.Chain.cum_zero, Nat.zero_add,
      Nat.cast_zero, Nat.add_zero, sub_zero]
  refine ⟨d, hnat, ?_⟩
  rw [hd, ← hoff]
  exact hpat0.symm

/-- A positive raw-prefix window on a coherent compatible trajectory is
covered by a canonical fibre whose reassembled raw word has exactly the window
positivity and pattern guards. -/
theorem exists_natCanonicalCylinder_raw_guards_of_prefixWindow
    {hm : 1 ≤ m} {y : RecState N m} (hy : y ∈ srSet N m)
    {K : ℕ} {C : Set (Fin (K + 1) → Fin N → ℤ)}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A) (hCoh : Coherent hm y A)
    (hwindow : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      prefixWindow (N := N) (m := m) K K C) :
    ∃ d : MaxRecordDecomp (N := N) hm y K,
      A ∈ natCanonicalCylinder hm y d ∧
      PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C := by
  obtain ⟨d, hnat, hpat⟩ := exists_natCanonicalCylinder_and_pathPat hy hA hCoh K
  have hchain := (mem_prefixWindow_iff_chain (N := N) (m := m)
    (K := K) (n := K) (C := C) (A := A) le_rfl hA).mp hwindow
  have hrawfin : (fun n i => posAt (seqOf (decompWord d)) n i) ∈ finStrict (N := N) K := by
    refine ⟨?_, ?_⟩
    · intro i
      have hp := congrFun (congrFun hpat (0 : Fin (K + 1))) i
      change SwarmFinHorizon.patOf (N := N) (decompWord d) ⟨0, by omega⟩ i = 0
      have hzeroIdx : (⟨0, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) :=
        Fin.ext rfl
      rw [hzeroIdx, hp]
      exact hchain.1.1 i
    · intro n hn hnK i
      have hp := congrFun (congrFun hpat ⟨n, by omega⟩) i
      change 0 < SwarmFinHorizon.patOf (N := N) (decompWord d) ⟨n, by omega⟩ i
      rw [hp]
      exact hchain.1.2 n hn hnK i
  refine ⟨d, hnat, (mem_finStrict_rawPath (decompWord d)).mp hrawfin, ?_⟩
  rw [hpat]
  exact hchain.2

/-- **Exact supported raw-window/canonical-fibre equivalence.**  This is a
common set on genuine coherent compatible trajectories, not an a.e. assertion
about arbitrary sequences. -/
theorem prefixWindow_iff_exists_natCanonicalCylinder_raw_guards
    {hm : 1 ≤ m} {y : RecState N m} (hy : y ∈ srSet N m)
    {K : ℕ} {C : Set (Fin (K + 1) → Fin N → ℤ)}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : TrajCompat A) (hCoh : Coherent hm y A) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
      prefixWindow (N := N) (m := m) K K C ↔
    ∃ d : MaxRecordDecomp (N := N) hm y K,
      A ∈ natCanonicalCylinder hm y d ∧
      PosSeqFin (N := N) (decompWord d) ∧ patOf (N := N) (decompWord d) ∈ C := by
  constructor
  · exact exists_natCanonicalCylinder_raw_guards_of_prefixWindow hy hA hCoh
  · rintro ⟨d, hnat, hpos, hC⟩
    let hbound := completed_length_le_raw_horizon hm y d
    have hpre : A ∈ Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K ⁻¹'
        canonicalFixedHorizonWindow hm y d := by
      rw [frestrictLe_preimage_canonicalFixedHorizonWindow]
      exact hnat
    have hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
        canonicalTrajectoryWindowExtension y d hbound := hpre
    obtain ⟨b, hb, hAtom⟩ := hCoh.1
    have hstart : ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i := by
      intro i
      rw [hAtom]
      exact SwarmSegKernel.segOf_p_zero y b.1 b.2 i
    exact (SwarmRawWindowIdentification.mem_prefixWindow_of_mem_canonicalExtension
      d hy hA hstart hbound hExt C).mpr ⟨hpos, hC⟩

end SwarmRawGlobalCover
