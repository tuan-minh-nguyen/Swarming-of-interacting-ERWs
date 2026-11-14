/-
Canonical exact fibres as actual infinite enriched-trajectory events.

The nat-sequence fibres of CanonicalFibres are measurable cylinders.  Their
K-coordinate restriction is exactly the common fixed-horizon event.  Hence the
disjoint canonical union has an actual infLaw mass, transported to arbitrary
initial record laws by the same exact per-start finite-chain integral.
-/
import Swarm.CanonicalFibres

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmCanonicalFixedHorizon

open SimJump.Record SwarmRec SwarmRawRecord SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmMixedTrajectory SwarmInfSeg

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- Canonical fibres in infinite enriched-sequence space are measurable finite
cylinders. -/
theorem measurableSet_natCanonicalCylinder (hm : 1 ≤ m) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    MeasurableSet (natCanonicalCylinder hm y d) := by
  exact (measurableSet_canonicalNextRecordWindow y d).preimage
    (measurable_pi_lambda _ (fun j : Fin (d.completed.length + 1) =>
      measurable_pi_apply j.1))

/-- Restricting an infinite enriched sequence to `Iic K` identifies its fixed
canonical event with the exact nat-sequence fibre. -/
theorem frestrictLe_preimage_canonicalFixedHorizonWindow (hm : 1 ≤ m)
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K ⁻¹'
      canonicalFixedHorizonWindow hm y d = natCanonicalCylinder hm y d := by
  ext A
  change Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K A ∈
    canonicalFixedHorizonWindow hm y d ↔ A ∈ natCanonicalCylinder hm y d
  rw [← prefixNat_mem_natCanonicalCylinder_iff hm y d]
  have hbound := completed_length_le_raw_horizon hm y d
  have hvec : (fun j : Fin (d.completed.length + 1) =>
      prefixNat (Preorder.frestrictLe
        (π := fun _ => SwarmInfSeg.Pair N m) K A) j.1) =
      (fun j : Fin (d.completed.length + 1) => A j.1) := by
    funext j
    have hj : j.1 ≤ K := (Nat.le_of_lt_succ j.2).trans hbound
    simp [prefixNat, min_eq_left hj]
  change (fun j : Fin (d.completed.length + 1) =>
      prefixNat (Preorder.frestrictLe
        (π := fun _ => SwarmInfSeg.Pair N m) K A) j.1) ∈
      canonicalNextRecordWindow y d ↔
    (fun j : Fin (d.completed.length + 1) => A j.1) ∈
      canonicalNextRecordWindow y d
  rw [hvec]

/-- Actual infinite enriched-trajectory mass of one exact canonical fibre,
under an arbitrary initial record law. -/
theorem infLaw_natCanonicalCylinder_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    (infLaw (N := N) (m := m) p hm hp hp1 π)
      (natCanonicalCylinder hm y d) =
    ∫⁻ z, (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
      (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
      (canonicalNextRecordWindow y d) ∂π := by
  rw [← frestrictLe_preimage_canonicalFixedHorizonWindow hm y d,
    ← Measure.map_apply
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K)
      (measurableSet_canonicalFixedHorizonWindow hm y d)]
  exact infLaw_canonicalFixedHorizonWindow_eq_lintegral p hm hp hp1 π y d

/-- The restriction of the finite canonical union is the union of the exact
infinite enriched fibres. -/
theorem frestrictLe_preimage_iUnion_canonicalFixedHorizonWindow
    (hm : 1 ≤ m) (y : RecState N m) (K : ℕ) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K ⁻¹'
      (⋃ d : MaxRecordDecomp (N := N) hm y K,
        canonicalFixedHorizonWindow hm y d) =
      (⋃ d : MaxRecordDecomp (N := N) hm y K,
        natCanonicalCylinder hm y d) := by
  rw [Set.preimage_iUnion]
  apply iUnion_congr
  intro d
  exact frestrictLe_preimage_canonicalFixedHorizonWindow hm y d

/-- **Actual infinite-law disjoint-canonical transport.**  The mass is not a
mere Dirac scalar or an unnamed joint law: it is the accepted arbitrary-π
`infLaw` evaluated on an exact measurable canonical union.  No exhaustion of a
raw prefix window or a fresh-future law is inferred. -/
theorem infLaw_iUnion_natCanonicalCylinder_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) (K : ℕ) :
    (infLaw (N := N) (m := m) p hm hp hp1 π)
      (⋃ d : MaxRecordDecomp (N := N) hm y K,
        natCanonicalCylinder hm y d) =
    ∫⁻ z, ∑ d : MaxRecordDecomp (N := N) hm y K,
      (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
        (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d) ∂π := by
  rw [← frestrictLe_preimage_iUnion_canonicalFixedHorizonWindow hm y K,
    ← Measure.map_apply
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K)
      (measurableSet_iUnion_canonicalFixedHorizonWindow hm y K)]
  exact infLaw_iUnion_canonicalFixedHorizonWindow_eq_lintegral
    p hm hp hp1 π y K

end SwarmCanonicalFixedHorizon
