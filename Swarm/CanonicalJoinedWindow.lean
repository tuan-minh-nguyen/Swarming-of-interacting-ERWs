/-
Canonical finite raw/enriched joined windows.

Each maximal raw record decomposition selects an actual finite enriched-chain
cylinder: all completed atoms are pinned, and the next atom is required to
contain the decoded unfinished raw tail.  The cylinder mass is exactly the
completed-prefix weight times the tail weight.  Summing these genuine cylinder
masses with the original whole-word positivity/pattern guards gives the raw
array mass for an arbitrary horizon and an arbitrary raw predicate or pattern.

This is a finite measure identity, not a common-space independence theorem.
It does not assert arbitrary-initial-law transport, stationarity, regeneration,
or `hstruct`.
-/
import Swarm.UnfinishedTailPin
import Swarm.EnrichedRawTail

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmCanonicalJoinedWindow

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmMeasuredJoin SwarmFreshPrefix SwarmUnfinishedTail SwarmEnrichedRawTail
open SwarmFreshArray
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SwarmFinHorizon SwarmFreshPos SwarmRestart

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The enriched cylinder associated to one maximal raw record decomposition.
The completed prefix has its actual successive record states.  The final atom
has arbitrary duration beyond the strict tail cut, arbitrary continuation and
arbitrary compact endpoint, subject only to decoding to the given raw tail. -/
noncomputable def canonicalNextRecordWindow {hm : 1 ≤ m} (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Set (Fin (d.completed.length + 1) → SwarmInfSeg.Pair N m) :=
  pinNext (atom hm y (blockSeq d.completed)) d.completed.length
    (TailPrefixSet d.tail.2)

/-- Every canonical joined window is a measurable finite enriched cylinder. -/
theorem measurableSet_canonicalNextRecordWindow {hm : 1 ≤ m} (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    MeasurableSet (canonicalNextRecordWindow y d) := by
  unfold canonicalNextRecordWindow pinNext
  have hpin : MeasurableSet
      (pin (atom hm y (blockSeq d.completed)) d.completed.length) :=
    measurableSet_pin (measurableSet_atom_singleton hm y (blockSeq d.completed))
      d.completed.length
  have hlast : MeasurableSet
      ((fun v : Fin (d.completed.length + 1) → SwarmInfSeg.Pair N m =>
        v (Fin.last d.completed.length)) ⁻¹' TailPrefixSet d.tail.2) :=
    (measurable_pi_apply (Fin.last d.completed.length))
      (measurableSet_tailPrefixSet d.tail.2)
  exact (SwarmChain.measurable_initF hpin).inter hlast

/-- Exact mass of one canonical joined window.  The two factors come from the
actual pinned completed chain and the next `asegK` law at its actual terminal
state.  Empty tails and zero-weight dummy `segOf` branches are included. -/
theorem chainVec_canonicalNextRecordWindow_mass (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d) =
      ENNReal.ofReal
        (prefixW p hm y d.completed *
          pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed))) := by
  rw [canonicalNextRecordWindow,
    chainVec_rawPrefix_pinNext_mass p hm hp hp1 y d.completed d.allFirst
      (measurableSet_tailPrefixSet d.tail.2),
    asegK_tailPrefixSet_mass p hp hp1 hm _ d.tail.2 d.tail_unfinished,
    ENNReal.ofReal_mul (prefixW_nonneg p hp hp1 hm y d.completed)]

/-- **Arbitrary-horizon, arbitrary-predicate finite raw/enriched identity.**
The left side is the original positive raw-array cylinder.  On the right, each
selected term is the measure of the actual enriched cylinder above; no scalar
surrogate for the enriched side remains.  The guard is positivity of the whole
reassembled raw word, equivalently `blockCond` by
`posSeqFin_decompWord_iff_blockCond`. -/
theorem arrayMeasure_positiveWord_eq_sum_canonicalNextRecordWindow
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (K : ℕ) (P : (Fin K → JumpVec N) → Prop) :
    (arrayMeasure N) {U : Array N |
        SwarmFreshPos.PosSeqFin (N := N) (jumpWord p m K U) ∧
          P (jumpWord p m K U)} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d) then
          (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
            (SwarmSegKernel.pairK (N := N) p hm) (d.completed.length + 1))
            (canonicalNextRecordWindow y d)
        else 0 := by
  rw [arrayMeasure_positiveWord_maxRecordDecomp p hp0 hp1 hm y hy K P]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d)
  · rw [if_pos hcond, if_pos hcond,
      chainVec_canonicalNextRecordWindow_mass p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

/-- The same identity for an arbitrary finite raw spatial pattern `C`. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
            (SwarmSegKernel.pairK (N := N) p hm) (d.completed.length + 1))
            (canonicalNextRecordWindow y d)
        else 0 := by
  rw [arrayMeasure_finStrict_pattern_maxRecordDecomp p hp0 hp1 hm y hy K C]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
      patOf (N := N) (decompWord d) ∈ C
  · rw [if_pos hcond, if_pos hcond,
      chainVec_canonicalNextRecordWindow_mass p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

/-- Explicit canonical fresh-start specialization of the arbitrary-pattern
joined-window identity. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow_fresh
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (i₀ : Fin N) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm (freshRecState (N := N) hm i₀) K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          (SwarmChain.chainVec
            (SwarmSegKernel.asegK (N := N) p hm (freshRecState (N := N) hm i₀))
            (SwarmSegKernel.pairK (N := N) p hm) (d.completed.length + 1))
            (canonicalNextRecordWindow (freshRecState (N := N) hm i₀) d)
        else 0 :=
  arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow
    p hp0 hp1 hm _ (ofRecState_freshRecState hm i₀) K C

end SwarmCanonicalJoinedWindow
