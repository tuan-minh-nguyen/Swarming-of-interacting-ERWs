/-
Canonical cylinders at one common finite enriched horizon.

Positive durations of completed first-record excursions bound the record
horizon by the fixed raw horizon.  Thus every canonical cylinder has a bounded
extension to that common horizon.  InitialLawTransport makes every per-start
chainVec mass measurable, so the finite sum of arbitrary-initial-law masses is
one lintegral of the corresponding finite sum.  This is a transport identity,
not a disjointness, exhaustiveness, raw-window, or joint-law assertion.
-/
import Swarm.MixedTrajectoryWindow

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
open SwarmMixedTrajectory
open SwarmInfSeg

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- Completed genuine first-record excursions have positive duration, so there
cannot be more of them than their total raw duration. -/
theorem length_le_rawLen_of_allFirst (hm : 1 ≤ m) (y : RecState N m) :
    ∀ (bs : List (RawBlock N)), AllFirst hm y bs → bs.length ≤ rawLen bs := by
  intro bs
  induction bs generalizing y with
  | nil => intro _; simp [rawLen]
  | cons b bs ih =>
      intro hbs
      have hb : 0 < b.1 := SwarmDHStruct.firstRecord_ne_zero hbs.1
      have htail := ih (RecKernel.out hm b.2 y) hbs.2
      simp only [List.length_cons, rawLen]
      omega

/-- A maximal decomposition at raw horizon `K` uses at most `K` completed
record atoms, independently of its unfinished tail. -/
theorem completed_length_le_raw_horizon (hm : 1 ≤ m) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    d.completed.length ≤ K := by
  have hlength := length_le_rawLen_of_allFirst hm y d.completed d.allFirst
  have hraw := d.len_eq
  omega

/-- The canonical cylinder for a raw-horizon decomposition, extended to the
single enriched horizon given by that same raw horizon. -/
noncomputable def canonicalFixedHorizonWindow (hm : 1 ≤ m) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Set (SwarmFinFuture.Prefix (N := N) (m := m) K) :=
  canonicalTrajectoryWindowExtension y d (completed_length_le_raw_horizon hm y d)

/-- Common-horizon canonical cylinders are measurable finite enriched events. -/
theorem measurableSet_canonicalFixedHorizonWindow (hm : 1 ≤ m)
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    MeasurableSet (canonicalFixedHorizonWindow hm y d) :=
  measurableSet_canonicalTrajectoryWindowExtension y d
    (completed_length_le_raw_horizon hm y d)

/-- Per-start masses of a canonical cylinder are measurable, via the exact
accepted finite initialization kernel rather than a separate measurability
assumption. -/
theorem measurable_chainVec_canonicalNextRecordWindow (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    Measurable (fun z =>
      (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
        (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d)) := by
  simpa only [← initialFiniteKernel_apply p hm hp hp1] using
    (initialFiniteKernel (N := N) (m := m) p hm d.completed.length).measurable_coe
      (measurableSet_canonicalNextRecordWindow y d)

/-- Arbitrary initial-law transport for one canonical cylinder at the common
raw/enriched horizon. -/
theorem infLaw_canonicalFixedHorizonWindow_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K) :
    ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K))
      (canonicalFixedHorizonWindow hm y d) =
    ∫⁻ z, (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
      (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
      (canonicalNextRecordWindow y d) ∂π := by
  exact infLaw_canonicalTrajectoryWindowExtension_eq_lintegral
    p hm hp hp1 π y d (completed_length_le_raw_horizon hm y d)

/-- **Finite canonical-cylinder transport at one common horizon.**  All raw
horizon-`K` decompositions are measured by actual `K+1`-coordinate enriched
finite marginals, and their sum is the integral of the exact per-start chain
masses.  Different summands are not claimed disjoint or exhaustive. -/
theorem infLaw_sum_canonicalFixedHorizonWindow_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) (K : ℕ) :
    (∑ d : MaxRecordDecomp (N := N) hm y K,
      ((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K))
        (canonicalFixedHorizonWindow hm y d)) =
    ∫⁻ z, ∑ d : MaxRecordDecomp (N := N) hm y K,
      (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
        (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d) ∂π := by
  calc
    (∑ d : MaxRecordDecomp (N := N) hm y K,
      ((infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K))
        (canonicalFixedHorizonWindow hm y d)) =
        ∑ d : MaxRecordDecomp (N := N) hm y K,
          ∫⁻ z, (SwarmChain.chainVec (asegK (N := N) (m := m) p hm z)
            (pairK (N := N) (m := m) p hm) (d.completed.length + 1))
            (canonicalNextRecordWindow y d) ∂π := by
              apply Finset.sum_congr rfl
              intro d hd
              exact infLaw_canonicalFixedHorizonWindow_eq_lintegral
                p hm hp hp1 π y d
    _ = _ := by
      symm
      exact lintegral_finsetSum Finset.univ (fun d hd =>
        measurable_chainVec_canonicalNextRecordWindow p hm hp hp1 y d)

end SwarmCanonicalFixedHorizon
