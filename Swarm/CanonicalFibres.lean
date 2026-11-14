/-
Exact fibres of canonical enriched cylinders and their common-horizon mass.

On one arbitrary nat-indexed enriched sequence, two canonical cylinder
memberships force equality of their raw decompositions.  The argument is
finite and pathwise: first-record segOf decoding recovers completed blocks;
strict decoded-tail duration rules out strict inclusion of completed prefixes;
and the terminal atom recovers the unfinished tail when the lengths agree.

Consequently the canonical fixed-horizon events are pairwise disjoint.  Their
union has exactly the finite sum of masses and, under an arbitrary initial
law, the previously proved per-start lintegral formula.  Exhaustion of a raw
window, trajectory compatibility, a common raw/enriched law, and a diagonal
raw-window profile are not asserted.
-/
import Swarm.CanonicalFixedHorizon
import Mathlib.Data.List.GetD
import Swarm.RawWindowCover

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmCanonicalFixedHorizon

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmMeasuredJoin SwarmFreshPrefix SwarmUnfinishedTail SwarmEnrichedRawTail
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmMixedTrajectory SwarmRawWindowCover SwarmInfSeg

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The fibre of one canonical cylinder in the consistent space of nat-indexed
 enriched sequences.  Only the first `completed.length+1` coordinates are
read; no future compatibility is built into the fibre. -/
noncomputable def natCanonicalCylinder (hm : 1 ≤ m) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Set (ℕ → SwarmInfSeg.Pair N m) :=
  {A | (fun j : Fin (d.completed.length + 1) => A j.1) ∈
    canonicalNextRecordWindow y d}

/-- Genuine first-record `segOf` segments determine their raw dependently-typed
blocks, even if the two record states used to construct them differ. -/
theorem rawBlock_eq_of_segOf_eq {y z : RecState N m}
    {b c : RawBlock N}
    (hb : FirstRecord (extendPath b.2) b.1 (ofRecState y))
    (hc : FirstRecord (extendPath c.2) c.1 (ofRecState z))
    (hseg : SwarmSegKernel.segOf y b.1 b.2 = SwarmSegKernel.segOf z c.1 c.2) :
    b = c := by
  have hbpos : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero hb
  have hcpos : 0 < c.1 := SwarmDHStruct.firstRecord_ne_zero hc
  have hlen : b.1 = c.1 := by
    rw [← SwarmFreshCyl.segOf_dur_of_firstRecord hbpos b.2 hb,
      ← SwarmFreshCyl.segOf_dur_of_firstRecord hcpos c.2 hc, hseg]
  apply rawBlock_ext hlen
  intro j
  have hjb := segJump_segOf y hbpos b.2 hb j
  have hjc := segJump_segOf z hcpos c.2 hc ⟨j.1, by omega⟩
  rw [hseg] at hjb
  exact hjb.symm.trans hjc

/-- Common completed atoms on one enriched sequence decode to the same raw
block at every index belonging to both completed prefixes. -/
theorem blockSeq_eq_of_mem_natCanonicalCylinder (hm : 1 ≤ m)
    (y : RecState N m) {K : ℕ} {d e : MaxRecordDecomp (N := N) hm y K}
    {A : ℕ → SwarmInfSeg.Pair N m}
    (hd : A ∈ natCanonicalCylinder hm y d)
    (he : A ∈ natCanonicalCylinder hm y e)
    (j : ℕ) (hjd : j < d.completed.length) (hje : j < e.completed.length) :
    blockSeq d.completed j = blockSeq e.completed j := by
  have hdmem := hd
  have hemem := he
  change (fun l : Fin (d.completed.length + 1) => A l.1) ∈
    pinNext (atom hm y (blockSeq d.completed)) d.completed.length
      (TailPrefixSet d.tail.2) at hdmem
  change (fun l : Fin (e.completed.length + 1) => A l.1) ∈
    pinNext (atom hm y (blockSeq e.completed)) e.completed.length
      (TailPrefixSet e.tail.2) at hemem
  have hda := hdmem.1 (⟨j, hjd⟩ : Fin d.completed.length)
  have hea := hemem.1 (⟨j, hje⟩ : Fin e.completed.length)
  have hatom : atom hm y (blockSeq d.completed) j =
      atom hm y (blockSeq e.completed) j := by
    exact hda.symm.trans hea
  apply rawBlock_eq_of_segOf_eq
    (firstRecord_blockSeq hm y d.allFirst hjd)
    (firstRecord_blockSeq hm y e.allFirst hje)
  exact congrArg Prod.fst hatom

/-- Equal completed block sequences through an index give equal cumulative raw
start times at that index. -/
theorem rawTime_eq_of_blockSeq_eq {bs cs : List (RawBlock N)} {j : ℕ}
    (h : ∀ k, k < j → blockSeq bs k = blockSeq cs k) :
    rawTime bs j = rawTime cs j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hprev : ∀ k, k < j → blockSeq bs k = blockSeq cs k := by
        intro k hk
        exact h k (by omega)
      rw [rawTime, rawTime, ih hprev, h j (Nat.lt_succ_self j)]

/-- Two canonical fibres cannot place one completed prefix strictly before the
other.  The shorter decomposition's strict terminal cut would lie strictly
inside a block which the longer decomposition must fit fully in the same raw
horizon. -/
theorem not_completed_length_lt_of_mem_natCanonicalCylinder
    (hm : 1 ≤ m) (y : RecState N m) {K : ℕ}
    {d e : MaxRecordDecomp (N := N) hm y K}
    {A : ℕ → SwarmInfSeg.Pair N m}
    (hd : A ∈ natCanonicalCylinder hm y d)
    (he : A ∈ natCanonicalCylinder hm y e)
    (hlen : d.completed.length < e.completed.length) : False := by
  have hblocks : ∀ j, j < d.completed.length →
      blockSeq d.completed j = blockSeq e.completed j := by
    intro j hj
    exact blockSeq_eq_of_mem_natCanonicalCylinder hm y hd he j hj (by omega)
  have htime : rawTime d.completed d.completed.length =
      rawTime e.completed d.completed.length := by
    apply rawTime_eq_of_blockSeq_eq
    intro j hj
    exact hblocks j hj
  have hpre : rawLen d.completed = rawTime e.completed d.completed.length := by
    rw [← rawTime_length d.completed, htime]
  have hstep : rawTime e.completed d.completed.length +
      (blockSeq e.completed d.completed.length).1 ≤ rawLen e.completed := by
    have hle := rawTime_le_rawLen e.completed
      (j := d.completed.length + 1) (by omega)
    exact hle
  have hdmem := hd
  have hemem := he
  change (fun l : Fin (d.completed.length + 1) => A l.1) ∈
    pinNext (atom hm y (blockSeq d.completed)) d.completed.length
      (TailPrefixSet d.tail.2) at hdmem
  change (fun l : Fin (e.completed.length + 1) => A l.1) ∈
    pinNext (atom hm y (blockSeq e.completed)) e.completed.length
      (TailPrefixSet e.tail.2) at hemem
  have hea := hemem.1
    (⟨d.completed.length, hlen⟩ : Fin e.completed.length)
  have hnext : A d.completed.length =
      atom hm y (blockSeq e.completed) d.completed.length := by
    exact hea
  have hfirst := firstRecord_blockSeq hm y e.allFirst hlen
  have hdur : (atom hm y (blockSeq e.completed) d.completed.length).1.dur =
      (blockSeq e.completed d.completed.length).1 := by
    exact SwarmFreshCyl.segOf_dur_of_firstRecord
      (SwarmDHStruct.firstRecord_ne_zero hfirst) _ hfirst
  have hcut : d.tail.1 < (blockSeq e.completed d.completed.length).1 := by
    rw [← hdur, ← hnext]
    exact hdmem.2.1
  have hdlen := d.len_eq
  have helen := e.len_eq
  omega

/-- **Exact canonical fibre.**  A nat-indexed enriched sequence belongs to at
most one decomposition-indexed canonical cylinder. -/
theorem eq_of_mem_natCanonicalCylinder (hm : 1 ≤ m)
    (y : RecState N m) {K : ℕ} {d e : MaxRecordDecomp (N := N) hm y K}
    {A : ℕ → SwarmInfSeg.Pair N m}
    (hd : A ∈ natCanonicalCylinder hm y d)
    (he : A ∈ natCanonicalCylinder hm y e) : d = e := by
  have hblocks : ∀ j, j < d.completed.length → j < e.completed.length →
      blockSeq d.completed j = blockSeq e.completed j := by
    intro j hjd hje
    exact blockSeq_eq_of_mem_natCanonicalCylinder hm y hd he j hjd hje
  rcases lt_trichotomy d.completed.length e.completed.length with hlt | heq | hgt
  · exact (not_completed_length_lt_of_mem_natCanonicalCylinder hm y hd he hlt).elim
  · have hcompleted : d.completed = e.completed := by
      apply List.ext_getElem heq
      intro j hjd hje
      have hb := hblocks j hjd hje
      simpa only [blockSeq, List.getD_eq_getElem _ _ hjd,
        List.getD_eq_getElem _ _ hje] using hb
    apply maxRecordDecomp_ext hcompleted
    have hdlen := d.len_eq
    have helen := e.len_eq
    have htailLen : d.tail.1 = e.tail.1 := by
      rw [hcompleted] at hdlen
      omega
    apply rawBlock_ext htailLen
    intro j
    have hdmem := hd
    have hemem := he
    change (fun l : Fin (d.completed.length + 1) => A l.1) ∈
      pinNext (atom hm y (blockSeq d.completed)) d.completed.length
        (TailPrefixSet d.tail.2) at hdmem
    change (fun l : Fin (e.completed.length + 1) => A l.1) ∈
      pinNext (atom hm y (blockSeq e.completed)) e.completed.length
        (TailPrefixSet e.tail.2) at hemem
    have hdlast : A d.completed.length ∈ TailPrefixSet d.tail.2 := hdmem.2
    have helast : A e.completed.length ∈ TailPrefixSet e.tail.2 := hemem.2
    rw [heq] at hdlast
    have hdj := hdlast.2 j
    have hej := helast.2 ⟨j.1, by omega⟩
    exact hdj.symm.trans hej
  · exact (not_completed_length_lt_of_mem_natCanonicalCylinder
      hm y he hd hgt).elim

/-- Distinct canonical decomposition indices have disjoint fibres in the
consistent nat-sequence space. -/
theorem pairwise_disjoint_natCanonicalCylinder (hm : 1 ≤ m)
    (y : RecState N m) (K : ℕ) :
    Pairwise (fun d e : MaxRecordDecomp (N := N) hm y K =>
      Disjoint (natCanonicalCylinder hm y d) (natCanonicalCylinder hm y e)) := by
  intro d e hne
  rw [Set.disjoint_left]
  intro A hd he
  exact hne (eq_of_mem_natCanonicalCylinder hm y hd he)

/-- Repeat the last available coordinate to view a finite enriched prefix as a
nat-indexed sequence.  Coordinates through `K` are unchanged. -/
def prefixNat {K : ℕ} (v : SwarmFinFuture.Prefix (N := N) (m := m) K) :
    ℕ → SwarmInfSeg.Pair N m :=
  fun j => v ⟨min j K, Finset.mem_Iic.mpr (min_le_right j K)⟩

/-- Membership in a common-horizon canonical event is exactly membership in
its nat-sequence fibre after this total extension. -/
theorem prefixNat_mem_natCanonicalCylinder_iff (hm : 1 ≤ m)
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    (v : SwarmFinFuture.Prefix (N := N) (m := m) K) :
    prefixNat v ∈ natCanonicalCylinder hm y d ↔
      v ∈ canonicalFixedHorizonWindow hm y d := by
  let hbound := completed_length_le_raw_horizon hm y d
  have hvec : (fun j : Fin (d.completed.length + 1) => prefixNat v j.1) =
      (finPrefixEquiv (β := SwarmInfSeg.Pair N m) d.completed.length).symm
        (Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) hbound v) := by
    funext j
    have hj : j.1 ≤ K := (Nat.le_of_lt_succ j.2).trans hbound
    simp [prefixNat, prefixToFin, min_eq_left hj]
  change (fun j : Fin (d.completed.length + 1) => prefixNat v j.1) ∈
      canonicalNextRecordWindow y d ↔
    (finPrefixEquiv (β := SwarmInfSeg.Pair N m) d.completed.length).symm
      (Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) hbound v) ∈ canonicalNextRecordWindow y d
  rw [hvec]

/-- The canonical cylinders at the single raw/enriched horizon `K` are pairwise
disjoint, not merely distinguished by extra raw-pattern guards. -/
theorem pairwise_disjoint_canonicalFixedHorizonWindow (hm : 1 ≤ m)
    (y : RecState N m) (K : ℕ) :
    Pairwise (fun d e : MaxRecordDecomp (N := N) hm y K =>
      Disjoint (canonicalFixedHorizonWindow hm y d)
        (canonicalFixedHorizonWindow hm y e)) := by
  intro d e hne
  rw [Set.disjoint_left]
  intro v hd he
  apply hne
  apply eq_of_mem_natCanonicalCylinder hm y (A := prefixNat v)
  · exact (prefixNat_mem_natCanonicalCylinder_iff hm y d v).2 hd
  · exact (prefixNat_mem_natCanonicalCylinder_iff hm y e v).2 he

/-- Measurability of the entire finite canonical union in the common horizon. -/
theorem measurableSet_iUnion_canonicalFixedHorizonWindow (hm : 1 ≤ m)
    (y : RecState N m) (K : ℕ) :
    MeasurableSet (⋃ d : MaxRecordDecomp (N := N) hm y K,
      canonicalFixedHorizonWindow hm y d) := by
  exact MeasurableSet.iUnion (fun d => measurableSet_canonicalFixedHorizonWindow hm y d)

/-- Any measure gives the canonical common-horizon union exactly the finite sum
of the individual cylinder masses. -/
theorem measure_iUnion_canonicalFixedHorizonWindow (hm : 1 ≤ m)
    (y : RecState N m) (K : ℕ)
    (μ : Measure (SwarmFinFuture.Prefix (N := N) (m := m) K)) :
    μ (⋃ d : MaxRecordDecomp (N := N) hm y K,
      canonicalFixedHorizonWindow hm y d) =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        μ (canonicalFixedHorizonWindow hm y d) := by
  rw [measure_iUnion (pairwise_disjoint_canonicalFixedHorizonWindow hm y K)
    (fun d => measurableSet_canonicalFixedHorizonWindow hm y d)]
  exact tsum_fintype _

/-- **Disjoint canonical transport at fixed raw horizon.**  The actual finite
trajectory marginal mass of the canonical union is one arbitrary-initial-law
lintegral of the exact per-start chain masses.  The union is not asserted to
be a raw-time window or to exhaust trajectories. -/
theorem infLaw_iUnion_canonicalFixedHorizonWindow_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) (K : ℕ) :
    ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K))
      (⋃ d : MaxRecordDecomp (N := N) hm y K,
        canonicalFixedHorizonWindow hm y d) =
    ∫⁻ z, ∑ d : MaxRecordDecomp (N := N) hm y K,
      (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
        (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d) ∂π := by
  rw [measure_iUnion_canonicalFixedHorizonWindow hm y K,
    infLaw_sum_canonicalFixedHorizonWindow_eq_lintegral p hm hp hp1 π y K]

end SwarmCanonicalFixedHorizon
