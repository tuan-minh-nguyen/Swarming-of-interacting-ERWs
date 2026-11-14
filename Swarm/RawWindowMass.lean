/-
Fixed-horizon raw masses at every simultaneous-record start.

The raw-array partition is valid at every `y ∈ srSet`: whole-word positivity
makes the array's `pathW` at `startState` agree with the path weight at
`ofRecState y`.  No identification of the record state with `startState` is
needed.  Rewriting the resulting summands gives their exact enriched-chain
`prefixW * pathW` masses, with the decomposition indexed by the actual start.
-/
import Swarm.RawWindowIdentification
import Swarm.CanonicalInfiniteFibres

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawWindowMass

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmCanonicalFixedHorizon SwarmRawWindowIdentification SwarmMixedTrajectory
open SwarmFreshPrefix SwarmMeasuredJoin SwarmInfSeg
open SwarmFreshArray
open SwarmFinHorizon SwarmFreshPos SwarmRestart SwarmFinFuture

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The measured positive raw-word partition holds at every simultaneous-record
start, not only at a record state whose whole past equals `startState`. -/
theorem arrayMeasure_positiveWord_maxRecordDecomp_of_srSet
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (P : (Fin K → JumpVec N) → Prop) :
    (arrayMeasure N) {U : Array N |
        SwarmFreshPos.PosSeqFin (N := N) (jumpWord p m K U) ∧
          P (jumpWord p m K U)} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d) then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  rw [SwarmArrayWords.mass_wordSet p hp0 hp1 m K
    (fun q => SwarmFreshPos.PosSeqFin (N := N) q ∧ P q)]
  symm
  refine Fintype.sum_equiv (maxRecordDecompEquiv y K) _ _ ?_
  intro d
  rw [maxRecordDecompEquiv_apply]
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d)
  · rw [if_pos hcond, if_pos hcond]
    congr 1
    rw [SwarmFreshArray.pathW_startState_eq hm hy (decompWord d) hcond.1,
      pathW_decompWord]
  · rw [if_neg hcond, if_neg hcond]

/-- Raw finite-strict/pattern mass as one exact sum of actual-state
completed-prefix and unfinished-tail weights at every `y ∈ srSet`. -/
theorem arrayMeasure_finStrict_pattern_maxRecordDecomp_of_srSet
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  rw [SwarmArrayWords.finStrict_pattern_eq_wordSet]
  exact arrayMeasure_positiveWord_maxRecordDecomp_of_srSet p hp0 hp1 hm y hy K
    (fun q => patOf (N := N) q ∈ C)

/-- The same raw mass is a sum of masses of the actual finite enriched-chain
cylinders based at the same simultaneous-record start. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow_of_srSet
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : y ∈ srSet N m)
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
  rw [arrayMeasure_finStrict_pattern_maxRecordDecomp_of_srSet p hp0 hp1 hm y hy K C]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
      patOf (N := N) (decompWord d) ∈ C
  · rw [if_pos hcond, if_pos hcond,
      chainVec_canonicalNextRecordWindow_mass p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

/-- Actual finite enriched-trajectory version at the canonical Dirac start;
the varying decomposition horizons are deliberately kept distinct. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalTrajectoryWindow_of_srSet
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le
              (Measure.dirac y)).map
            (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m)
              d.completed.length)) (canonicalTrajectoryWindow y d)
        else 0 := by
  rw [arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow_of_srSet
    p hp0 hp1 hm y hy K C]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
      patOf (N := N) (decompWord d) ∈ C
  · rw [if_pos hcond, if_pos hcond,
      infLaw_canonicalTrajectoryWindow_eq_chainVec p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

end SwarmRawWindowMass

namespace SwarmRawWindowMass

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmCanonicalFixedHorizon SwarmRawWindowIdentification SwarmMixedTrajectory
open SwarmFreshPrefix SwarmMeasuredJoin SwarmInfSeg
open SwarmFreshArray
open SwarmFinHorizon SwarmFreshPos SwarmRestart SwarmFinFuture
open Swarming Swarming.Uniform

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- At a genuine Dirac initial record state, the first enriched atom has its
prescribed start almost surely under the actual infinite trajectory law. -/
theorem infLaw_dirac_start_ae
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : RecState N m) :
    ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)),
      ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  letI : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp hp1 (Measure.dirac y)
  have h : ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1
      (Measure.dirac y)), A 0 ∈ SwarmDHStruct.StartSet N m y := by
    have hmeas : MeasurableSet
        ((fun A : ℕ → SwarmInfSeg.Pair N m => A 0) ⁻¹'
          SwarmDHStruct.StartSet N m y) :=
      (SwarmDHStruct.measurableSet_startSet N m y).preimage (measurable_pi_apply 0)
    apply (mem_ae_iff_prob_eq_one hmeas).2
    rw [← Measure.map_apply (measurable_pi_apply (0 : ℕ))
        (SwarmDHStruct.measurableSet_startSet N m y),
      SwarmInfSeg.map_eval_zero p hm hp hp1 (Measure.dirac y),
      SwarmInitialTransport.pairLaw_dirac,
      SwarmDHStruct.ae_start_step p hm hp hp1 y]
  simpa only [SwarmDHStruct.StartSet, Set.mem_ofPred_eq] using h

/-- On the actual Dirac-started enriched trajectory, the part of the raw
window carried by the disjoint canonical fibres has exactly the guarded sum
of completed-prefix/unfinished-tail weights.  Exhaustion of that part is not
assumed; the remaining step is precisely the path-cover statement. -/
theorem infLaw_dirac_canonical_rawWindow_part_eq_sum
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le (Measure.dirac y))
        ((⋃ d : MaxRecordDecomp (N := N) hm y K,
          natCanonicalCylinder hm y d) ∩
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
          prefixWindow (N := N) (m := m) K K C) =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  let μ := SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le (Measure.dirac y)
  have hcompat : ∀ᵐ A ∂μ, SwarmChainAssemble.TrajCompat A :=
    SwarmInfSeg.trajCompat_ae p hm hp0.le hp1.le (Measure.dirac y)
  have hstart : ∀ᵐ A ∂μ, ∀ i, (A 0).1.p 0 i = (Record.ofRecState y).pos i :=
    infLaw_dirac_start_ae p hm hp0.le hp1.le y
  have hraw : MeasurableSet
      ((Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
        prefixWindow (N := N) (m := m) K K C) :=
    (SwarmFinFuture.measurableSet_prefixWindow (N := N) (m := m) (K := K) hC).preimage
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K)
  have hmass (d : MaxRecordDecomp (N := N) hm y K) :
      μ (natCanonicalCylinder hm y d) =
        ENNReal.ofReal
          (prefixW p hm y d.completed *
            pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed))) := by
    dsimp [μ]
    rw [← frestrictLe_preimage_canonicalFixedHorizonWindow hm y d,
      ← Measure.map_apply
        (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K)
        (measurableSet_canonicalFixedHorizonWindow hm y d)]
    exact infLaw_canonicalTrajectoryWindowExtension_dirac_mass
      p hm hp0.le hp1.le y d (completed_length_le_raw_horizon hm y d)
  have hfibre (d : MaxRecordDecomp (N := N) hm y K) :
      μ (natCanonicalCylinder hm y d ∩
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
          prefixWindow (N := N) (m := m) K K C) =
      if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
          patOf (N := N) (decompWord d) ∈ C then
        ENNReal.ofReal
          (prefixW p hm y d.completed *
            pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
      else 0 := by
    by_cases hguard : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
        patOf (N := N) (decompWord d) ∈ C
    · rw [if_pos hguard, ← hmass d]
      apply measure_congr
      filter_upwards [hcompat, hstart] with A hA hAstart
      apply propext
      constructor
      · exact fun h => h.1
      · intro hfibre
        refine ⟨hfibre, ?_⟩
        have hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
            canonicalFixedHorizonWindow hm y d := by
          rw [← frestrictLe_preimage_canonicalFixedHorizonWindow hm y d] at hfibre
          exact hfibre
        exact (mem_prefixWindow_of_mem_canonicalExtension d hy hA hAstart
          (completed_length_le_raw_horizon hm y d) hExt C).mpr hguard
    · rw [if_neg hguard, ← measure_empty (μ := μ)]
      apply measure_congr
      filter_upwards [hcompat] with A hA
      apply propext
      constructor
      · rintro ⟨hfibre, hwindow⟩
        have hExt : Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
            canonicalFixedHorizonWindow hm y d := by
          rw [← frestrictLe_preimage_canonicalFixedHorizonWindow hm y d] at hfibre
          exact hfibre
        exact (hguard (raw_guards_of_mem_prefixWindow_canonicalExtension
          d hy hA (completed_length_le_raw_horizon hm y d) hExt hwindow)).elim
      · intro h
        exact h.elim
  change μ ((⋃ d : MaxRecordDecomp (N := N) hm y K,
      natCanonicalCylinder hm y d) ∩
    (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
      prefixWindow (N := N) (m := m) K K C) = _
  rw [Set.iUnion_inter, measure_iUnion]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    exact hfibre d
  · intro d e hde
    change Disjoint (natCanonicalCylinder hm y d ∩
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
        prefixWindow (N := N) (m := m) K K C)
      (natCanonicalCylinder hm y e ∩
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
          prefixWindow (N := N) (m := m) K K C)
    rw [Set.disjoint_left]
    intro A hd he
    have hdis : Disjoint (natCanonicalCylinder hm y d) (natCanonicalCylinder hm y e) :=
      pairwise_disjoint_natCanonicalCylinder hm y K hde
    exact (Set.disjoint_left.mp hdis) hd.1 he.1
  · intro d
    exact (measurableSet_natCanonicalCylinder hm y d).inter hraw

end SwarmRawWindowMass

namespace SwarmRawWindowMass

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmCanonicalFixedHorizon SwarmRawWindowIdentification SwarmMixedTrajectory
open SwarmFreshPrefix SwarmMeasuredJoin SwarmInfSeg
open SwarmFreshArray
open SwarmFinHorizon SwarmFreshPos SwarmRestart SwarmFinFuture
open Swarming Swarming.Uniform

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- Common finite-horizon `chainVec` form of the exact guarded canonical-part
mass formula.  Both sides use the same raw horizon `K`; the canonical events
are first transported through `finToPrefix`, not confused with their shorter
mixed horizons. -/
theorem chainVec_canonical_rawWindow_part_eq_sum
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
      ((⋃ d : MaxRecordDecomp (N := N) hm y K,
        finToPrefix ⁻¹' canonicalFixedHorizonWindow hm y d) ∩
        rawWindowVec (N := N) (m := m) (K := K) C) =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  have hprefix : MeasurableSet (prefixWindow (N := N) (m := m) K K C) :=
    SwarmFinFuture.measurableSet_prefixWindow (N := N) (m := m) (K := K) hC
  have hE : MeasurableSet ((⋃ d : MaxRecordDecomp (N := N) hm y K,
      canonicalFixedHorizonWindow hm y d) ∩
      prefixWindow (N := N) (m := m) K K C) :=
    (measurableSet_iUnion_canonicalFixedHorizonWindow hm y K).inter hprefix
  rw [← infLaw_dirac_canonical_rawWindow_part_eq_sum p hm hp0 hp1 y hy K C hC]
  have hS : ((⋃ d : MaxRecordDecomp (N := N) hm y K,
      finToPrefix ⁻¹' canonicalFixedHorizonWindow hm y d) ∩
      rawWindowVec (N := N) (m := m) (K := K) C) =
      finToPrefix ⁻¹' ((⋃ d : MaxRecordDecomp (N := N) hm y K,
        canonicalFixedHorizonWindow hm y d) ∩
        prefixWindow (N := N) (m := m) K K C) := by
    rw [Set.preimage_inter, Set.preimage_iUnion]
    rfl
  rw [hS, ← Measure.map_apply measurable_finToPrefix hE,
    ← SwarmInitialTransport.pairLaw_dirac p hm y,
    ← SwarmInitialTransport.infLaw_prefix_eq_chainVec p hm hp0.le hp1.le
      (Measure.dirac y) K,
    Measure.map_apply
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K) hE,
    Set.preimage_inter, frestrictLe_preimage_iUnion_canonicalFixedHorizonWindow]

end SwarmRawWindowMass

namespace SwarmRawWindowMass

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmCanonicalFixedHorizon SwarmRawWindowIdentification SwarmMixedTrajectory
open SwarmFreshPrefix SwarmMeasuredJoin SwarmInfSeg
open SwarmFreshArray
open SwarmFinHorizon SwarmFreshPos SwarmRestart SwarmFinFuture
open Swarming Swarming.Uniform

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The guarded canonical part of the genuine chain raw window has exactly
the original fresh array mass, at every simultaneous-record start. -/
theorem chainVec_canonical_rawWindow_part_eq_arrayMeasure
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
      ((⋃ d : MaxRecordDecomp (N := N) hm y K,
        finToPrefix ⁻¹' canonicalFixedHorizonWindow hm y d) ∩
        rawWindowVec (N := N) (m := m) (K := K) C) =
      (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  calc
    _ = ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := chainVec_canonical_rawWindow_part_eq_sum p hm hp0 hp1 y hy K C hC
    _ = _ := (arrayMeasure_finStrict_pattern_maxRecordDecomp_of_srSet
      p hp0 hp1 hm y hy K C).symm

end SwarmRawWindowMass
