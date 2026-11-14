/-
Canonical joined windows as actual finite enriched-trajectory cylinders.

For each maximal raw record decomposition, the canonical `Fin` vector window is
transported by the accepted measurable `Fin (n+1) ≃ Iic n` equivalence.  Under
the Dirac law at its actual initial record state, its mass is therefore an
`infLaw` finite-marginal mass, not merely a `chainVec` scalar.  The completed
atoms and the strict-cut next record remain exactly those of
`CanonicalJoinedWindow`; different decompositions keep their different finite
record horizons and are never asserted to live in one common joint-space law.

The raw array identities are then rewritten as sums of these genuine finite
trajectory masses.  No arbitrary initial law, stationarity, independence,
regeneration, or `FinHorizonFamily` conclusion is assumed or claimed.
-/
import Swarm.CanonicalJoinedWindow
import Swarm.InitialLawTransport

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmCanonicalTrajectory

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport
open SwarmFreshArray
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SwarmFinHorizon SwarmFreshPos SwarmRestart

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The canonical joined window, reindexed as an actual `Iic` finite enriched
trajectory event.  Its horizon is the number of completed atoms: the last
coordinate is the next, possibly unfinished, record. -/
noncomputable def canonicalTrajectoryWindow {hm : 1 ≤ m} (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Set (SwarmFinFuture.Prefix (N := N) (m := m) d.completed.length) :=
  (finPrefixEquiv (β := SwarmInfSeg.Pair N m) d.completed.length).symm ⁻¹'
    canonicalNextRecordWindow y d

/-- Reindexing by a measurable equivalence preserves measurability. -/
theorem measurableSet_canonicalTrajectoryWindow {hm : 1 ≤ m} (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    MeasurableSet (canonicalTrajectoryWindow y d) := by
  exact (finPrefixEquiv (β := SwarmInfSeg.Pair N m) d.completed.length).symm.measurable
    (measurableSet_canonicalNextRecordWindow y d)

/-- At the canonical Dirac start, the actual enriched trajectory's finite
marginal gives exactly the original canonical `chainVec` cylinder mass. -/
theorem infLaw_canonicalTrajectoryWindow_eq_chainVec (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length))
        (canonicalTrajectoryWindow y d) =
      (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) (d.completed.length + 1))
          (canonicalNextRecordWindow y d) := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  rw [infLaw_prefix_eq_chainVec p hm hp hp1 (Measure.dirac y) d.completed.length,
    pairLaw_dirac]
  rw [Measure.map_apply measurable_finToPrefix
    (measurableSet_canonicalTrajectoryWindow y d)]
  have hset : finToPrefix ⁻¹' canonicalTrajectoryWindow y d =
      canonicalNextRecordWindow y d := by
    exact (finPrefixEquiv (β := SwarmInfSeg.Pair N m)
      d.completed.length).toEquiv.preimage_symm_preimage (canonicalNextRecordWindow y d)
  rw [hset]

/-- Exact prefix-weight/actual-tail-weight mass of the genuine finite enriched
trajectory window. -/
theorem infLaw_canonicalTrajectoryWindow_mass (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) d.completed.length))
        (canonicalTrajectoryWindow y d) =
      ENNReal.ofReal
        (prefixW p hm y d.completed *
          pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed))) := by
  rw [infLaw_canonicalTrajectoryWindow_eq_chainVec p hm hp hp1 y d,
    chainVec_canonicalNextRecordWindow_mass p hm hp hp1 y d]

/-- Arbitrary positive raw finite word and arbitrary raw predicate, expressed
as a finite sum of actual enriched trajectory marginal masses. -/
theorem arrayMeasure_positiveWord_eq_sum_canonicalTrajectoryWindow
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (K : ℕ) (P : (Fin K → JumpVec N) → Prop) :
    (arrayMeasure N) {U : Array N |
        SwarmFreshPos.PosSeqFin (N := N) (jumpWord p m K U) ∧
          P (jumpWord p m K U)} =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d) then
          ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le
              (Measure.dirac y)).map
            (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m)
              d.completed.length)) (canonicalTrajectoryWindow y d)
        else 0 := by
  rw [arrayMeasure_positiveWord_eq_sum_canonicalNextRecordWindow
    p hp0 hp1 hm y hy K P]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧ P (decompWord d)
  · rw [if_pos hcond, if_pos hcond,
      infLaw_canonicalTrajectoryWindow_eq_chainVec p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

/-- Arbitrary finite raw spatial pattern, expressed as a finite sum of actual
enriched trajectory marginal masses. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalTrajectoryWindow
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
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
  rw [arrayMeasure_finStrict_pattern_eq_sum_canonicalNextRecordWindow
    p hp0 hp1 hm y hy K C]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcond : SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
      patOf (N := N) (decompWord d) ∈ C
  · rw [if_pos hcond, if_pos hcond,
      infLaw_canonicalTrajectoryWindow_eq_chainVec p hm hp0.le hp1.le y d]
  · rw [if_neg hcond, if_neg hcond]

/-- Canonical fresh-start form of the arbitrary-pattern trajectory identity. -/
theorem arrayMeasure_finStrict_pattern_eq_sum_canonicalTrajectoryWindow_fresh
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (i₀ : Fin N) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
      ∑ d : MaxRecordDecomp (N := N) hm (freshRecState (N := N) hm i₀) K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le
              (Measure.dirac (freshRecState (N := N) hm i₀))).map
            (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m)
              d.completed.length))
            (canonicalTrajectoryWindow (freshRecState (N := N) hm i₀) d)
        else 0 :=
  arrayMeasure_finStrict_pattern_eq_sum_canonicalTrajectoryWindow
    p hp0 hp1 hm _ (ofRecState_freshRecState hm i₀) K C

end SwarmCanonicalTrajectory
