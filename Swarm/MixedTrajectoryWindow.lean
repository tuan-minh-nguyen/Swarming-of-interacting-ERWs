/-
Mixed initial laws for fixed raw-time enriched windows and bounded extensions.

The actual raw-time `prefixWindow K n C` is pulled back through the accepted
measurable `Fin(n+1) ≃ Iic n` reindexing.  Its mass under an arbitrary initial
record law is therefore an integral of genuine per-start finite chain masses.
The time-zero part of `finStrict` makes this mass vanish off `srSet`; on
`srSet`, an explicitly supplied per-start array profile gives the exact
`π(srSet)` diagonal window formula through the accepted fresh-mass integral.

Canonical record-decomposition windows have their own enriched horizons.  A
bounded extension pulls such a window back to any longer `Iic` horizon, with
unchanged mass and an arbitrary-`π` finite-chain integral.  No common law for
different decompositions, raw-chain/array equality, `FinHorizonFamily`, or
`hstruct` is asserted.
-/
import Swarm.CanonicalTrajectoryWindow
import Swarm.FinHorizonK0

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmMixedTrajectory

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalJoinedWindow SwarmInitialTransport SwarmCanonicalTrajectory
open SwarmFreshArray
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SwarmFinHorizon SwarmFreshPos SwarmRestart

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The fixed raw-time enriched window in the `Fin(n+1)` indexing used by
`chainVec_pairLaw_apply_eq_lintegral`. -/
noncomputable def rawWindowVec {N m K n : ℕ}
    (C : Set (Fin (n + 1) → Fin N → ℤ)) :
    Set (Fin (n + 1) → SwarmInfSeg.Pair N m) :=
  finToPrefix ⁻¹' SwarmFinFuture.prefixWindow (N := N) (m := m) K n C

/-- The reindexed raw-time window is measurable whenever its raw pattern is. -/
theorem measurableSet_rawWindowVec {N m K n : ℕ}
    {C : Set (Fin (n + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    MeasurableSet (rawWindowVec (N := N) (m := m) (K := K) C) :=
  (SwarmFinFuture.measurableSet_prefixWindow (N := N) (m := m) (K := K) hC).preimage
    measurable_finToPrefix

/-- The initial coordinate marginal of every positive-length finite chain is
its initial enriched-atom law. -/
theorem chainVec_map_zero {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] (κ : Kernel β β) [IsMarkovKernel κ]
    (n : ℕ) :
    (SwarmChain.chainVec μ κ (n + 1)).map (fun v => v 0) = μ := by
  let h : 1 ≤ n + 1 := Nat.succ_pos n
  have htr := SwarmChain.chainVec_trunc μ κ n 1 h
  rw [SwarmChain.chainVec_succ, SwarmChain.chainStep_zero] at htr
  have hmap := congrArg
    (fun ν : Measure (Fin 1 → β) => ν.map (fun v => v 0)) htr
  rw [Measure.map_map (measurable_pi_apply (0 : Fin 1)) (SwarmChain.measurable_truncF h),
    Measure.map_map (measurable_pi_apply (0 : Fin 1)) SwarmChain.measurable_fin1_const] at hmap
  have hleft : (fun v : Fin 1 → β => v 0) ∘ SwarmChain.truncF h =
      (fun v : Fin (n + 1) → β => v 0) := by
    funext v
    rfl
  have hright : (fun v : Fin 1 → β => v 0) ∘ (fun b : β => fun _ : Fin 1 => b) = id := by
    funext b
    rfl
  rw [hleft, hright, Measure.map_id] at hmap
  exact hmap

/-- Membership in a raw strict-positivity window forces the first enriched
segment to start at zero. -/
theorem mem_segStartZero_of_mem_rawWindowVec {N m K n : ℕ}
    {C : Set (Fin (n + 1) → Fin N → ℤ)}
    {v : Fin (n + 1) → SwarmInfSeg.Pair N m}
    (hv : v ∈ rawWindowVec (N := N) (m := m) (K := K) C) :
    v 0 ∈ SwarmFinHorizon.SegStartZero N m := by
  change SwarmFinFuture.prefixPath (finToPrefix v) ∈
    SwarmFinHorizon.finStrict (N := N) K ∩
      SwarmFinHorizon.pathPat (N := N) n ⁻¹' C at hv
  intro i
  have hzero := hv.1.1 i
  have hrecord := SwarmFinFuture.prefixX_record (finToPrefix v)
    (Nat.zero_le n) i
  rw [SwarmFinFuture.prefixCum_zero] at hrecord
  change SwarmFinFuture.prefixX (finToPrefix v) 0 i = 0 at hzero
  rw [hrecord] at hzero
  simpa [finToPrefix] using hzero

/-- Away from simultaneous record states, the actual per-start mass of every
raw strict-positivity window is zero. -/
theorem chainVec_rawWindowVec_eq_zero_of_not_srSet (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    (hy : y ∉ srSet N m) {K n : ℕ}
    (C : Set (Fin (n + 1) → Fin N → ℤ)) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C) = 0 := by
  letI : IsProbabilityMeasure (SwarmSegKernel.asegK (N := N) (m := m) p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  letI : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  have hsub : rawWindowVec (N := N) (m := m) (K := K) C ⊆
      (fun v : Fin (n + 1) → SwarmInfSeg.Pair N m => v 0) ⁻¹'
        SwarmFinHorizon.SegStartZero N m :=
    fun _ hv => mem_segStartZero_of_mem_rawWindowVec hv
  have hle := measure_mono
    (μ := SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
      (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)) hsub
  rw [← Measure.map_apply (measurable_pi_apply (0 : Fin (n + 1)))
      (SwarmFinHorizon.measurableSet_segStartZero N m),
    chainVec_map_zero, SwarmFinHorizon.segStartZero_mass p hm hp hp1 y,
    if_neg hy] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- Arbitrary-`π` transport of the actual fixed raw-time enriched window. -/
theorem chainLaw_window_eq_lintegral_chainVec (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    {K n : ℕ} (hK : K ≤ n) {C : Set (Fin (n + 1) → Fin N → ℤ)}
    (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
        (SwarmFinFuture.chainWindow K n C) =
      ∫⁻ y, (SwarmChain.chainVec
        (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C) ∂π := by
  rw [SwarmFinFuture.chainLaw_window_eq_prefix p hm hp hp1 π hK hC,
    infLaw_prefix_eq_chainVec p hm hp hp1 π n,
    Measure.map_apply measurable_finToPrefix
      (SwarmFinFuture.measurableSet_prefixWindow hC)]
  exact chainVec_pairLaw_apply_eq_lintegral p hm hp hp1 π n
    (measurableSet_rawWindowVec hC)

/-- The same arbitrary-`π` mass, restricted to the simultaneous-record start
set.  The discarded integral is exactly zero by the preceding computation. -/
theorem chainLaw_window_eq_setLIntegral_srSet (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    {K n : ℕ} (hK : K ≤ n) {C : Set (Fin (n + 1) → Fin N → ℤ)}
    (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
        (SwarmFinFuture.chainWindow K n C) =
      ∫⁻ y in srSet N m, (SwarmChain.chainVec
        (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C) ∂π := by
  rw [chainLaw_window_eq_lintegral_chainVec p hm hp hp1 π hK hC]
  have hfun : (fun y : RecState N m =>
      (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C)) =
      (srSet N m).indicator (fun y : RecState N m =>
        (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
          (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
          (rawWindowVec (N := N) (m := m) (K := K) C)) := by
    funext y
    by_cases hy : y ∈ srSet N m
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy,
        chainVec_rawWindowVec_eq_zero_of_not_srSet p hm hp hp1 y hy C]
  calc
    _ = ∫⁻ y, (srSet N m).indicator (fun y : RecState N m =>
        (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
          (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1))
          (rawWindowVec (N := N) (m := m) (K := K) C)) y ∂π := by
      rw [← hfun]
    _ = _ := lintegral_indicator (μ := π) (SwarmRec.measurableSet_srSet N m) _

/-- Exact diagonal `π(srSet)` formula from the actual per-start finite-chain
profile.  This profile is an input here; it is not replaced by a canonical
scalar or inferred from the raw array's fixed start. -/
theorem chainLaw_diagonal_window_eq_pi_srSet_of_profile (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C)
    (hprofile : ∀ y : RecState N m, y ∈ srSet N m →
      (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C) =
      (arrayMeasure N) {U : Array N |
        FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
          trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C}) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
        (SwarmFinFuture.chainWindow K K C) =
      π (srSet N m) * (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  rw [chainLaw_window_eq_setLIntegral_srSet p hm hp hp1 π le_rfl hC,
    setLIntegral_congr_fun (SwarmRec.measurableSet_srSet N m) hprofile]
  exact finHorizon_mass_integral_srSet hm p π K C

/-- The diagonal finite-window family follows from the same per-start measured
profile.  This is not a proof of that profile or of the full window family. -/
theorem chainLaw_diagonal_windows_of_chainVec_profile (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hprofile : ∀ (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)),
      MeasurableSet C → ∀ y : RecState N m, y ∈ srSet N m →
        (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
          (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
          (rawWindowVec (N := N) (m := m) (K := K) C) =
        (arrayMeasure N) {U : Array N |
          FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
            trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C}) :
    ∀ (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)), MeasurableSet C →
      SwarmChainAssemble.chainLaw
          (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
          {c : SwarmConcat.Chain N | SwarmFinFuture.chainPath c ∈
            finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} =
        π (srSet N m) * (arrayMeasure N) {U : Array N |
          posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  intro K C hC
  exact chainLaw_diagonal_window_eq_pi_srSet_of_profile p hm hp hp1 π K C hC
    (hprofile K C hC)

/-- Every bounded event keeps its actual trajectory mass after extension to a
longer finite enriched horizon. -/
theorem infLaw_longerPrefix_bounded_apply (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    {r n : ℕ} (hrn : r ≤ n) {D : Set (SwarmFinFuture.Prefix (N := N) (m := m) r)}
    (hD : MeasurableSet D) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) hrn ⁻¹' D) =
      ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) D := by
  have hmap : Measurable (Preorder.frestrictLe₂
      (π := fun _ => SwarmInfSeg.Pair N m) hrn) :=
    Preorder.measurable_frestrictLe₂ hrn
  have hrest : Measurable (Preorder.frestrictLe
      (π := fun _ => SwarmInfSeg.Pair N m) n) :=
    Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) n
  rw [← Measure.map_apply hmap hD, Measure.map_map hmap hrest,
    Preorder.frestrictLe₂_comp_frestrictLe hrn]

/-- A canonical decomposition window extended unchanged to any longer enriched
horizon. -/
noncomputable def canonicalTrajectoryWindowExtension {hm : 1 ≤ m}
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    {n : ℕ} (h : d.completed.length ≤ n) :
    Set (SwarmFinFuture.Prefix (N := N) (m := m) n) :=
  Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) h ⁻¹'
    canonicalTrajectoryWindow y d

/-- Bounded canonical extensions are measurable. -/
theorem measurableSet_canonicalTrajectoryWindowExtension {hm : 1 ≤ m}
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    {n : ℕ} (h : d.completed.length ≤ n) :
    MeasurableSet (canonicalTrajectoryWindowExtension y d h) :=
  (measurableSet_canonicalTrajectoryWindow y d).preimage
    (Preorder.measurable_frestrictLe₂ h)

/-- Arbitrary-`π` mass of a bounded canonical extension, expressed by the
accepted fixed-event/fixed-horizon finite-chain integral at its original
horizon. -/
theorem infLaw_canonicalTrajectoryWindowExtension_eq_lintegral
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    {n : ℕ} (h : d.completed.length ≤ n) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (canonicalTrajectoryWindowExtension y d h) =
      ∫⁻ z, (SwarmChain.chainVec
        (SwarmSegKernel.asegK (N := N) (m := m) p hm z)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (d.completed.length + 1))
        (canonicalNextRecordWindow y d) ∂π := by
  rw [canonicalTrajectoryWindowExtension,
    infLaw_longerPrefix_bounded_apply p hm hp hp1 π h
      (measurableSet_canonicalTrajectoryWindow y d),
    infLaw_prefix_eq_chainVec p hm hp hp1 π d.completed.length,
    Measure.map_apply measurable_finToPrefix (measurableSet_canonicalTrajectoryWindow y d)]
  have hset : finToPrefix ⁻¹' canonicalTrajectoryWindow y d =
      canonicalNextRecordWindow y d := by
    exact (finPrefixEquiv (β := SwarmInfSeg.Pair N m)
      d.completed.length).toEquiv.preimage_symm_preimage (canonicalNextRecordWindow y d)
  rw [hset]
  exact chainVec_pairLaw_apply_eq_lintegral p hm hp hp1 π d.completed.length
    (measurableSet_canonicalNextRecordWindow y d)

/-- At the actual Dirac start, a bounded canonical extension retains the exact
completed-prefix/unfinished-tail weight at every longer horizon. -/
theorem infLaw_canonicalTrajectoryWindowExtension_dirac_mass
    (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : RecState N m) {K : ℕ} (d : MaxRecordDecomp (N := N) hm y K)
    {n : ℕ} (h : d.completed.length ≤ n) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (canonicalTrajectoryWindowExtension y d h) =
      ENNReal.ofReal
        (prefixW p hm y d.completed *
          pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed))) := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  rw [canonicalTrajectoryWindowExtension,
    infLaw_longerPrefix_bounded_apply p hm hp hp1 (Measure.dirac y) h
      (measurableSet_canonicalTrajectoryWindow y d),
    infLaw_canonicalTrajectoryWindow_mass p hm hp hp1 y d]

end SwarmMixedTrajectory
