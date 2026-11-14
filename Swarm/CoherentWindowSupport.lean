/-
Almost-sure first-record coherence of the actual enriched trajectory, and the
resulting full pinned raw-window mass formula.
-/
import Swarm.CoherentCover
import Swarm.RawWindowMass

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawGlobalCover

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open Swarming Swarming.Uniform SwarmRestart
open SwarmCanonicalFixedHorizon SwarmCanonicalJoinedWindow SwarmCanonicalTrajectory
open SwarmMixedTrajectory
open SwarmRawWindowIdentification SwarmEnrichedRawTail
open SwarmChainAssemble SwarmFinFuture SwarmFinHorizon SwarmFreshPos
open SwarmInfSeg SwarmFreshPrefix SwarmMeasuredJoin
open SwarmRawWindowMass SwarmInitialTransport

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- At a fixed record state, the first-record support is a countable union of
measurable singleton enriched atoms. -/
theorem measurableSet_canonicalAtom (hm : 1 ≤ m) (y : RecState N m) :
    MeasurableSet {a : SwarmInfSeg.Pair N m | CanonicalAtom hm y a} := by
  classical
  have heq : {a : SwarmInfSeg.Pair N m | CanonicalAtom hm y a} =
      ⋃ b : RawBlock N,
        if FirstRecord (extendPath b.2) b.1 (ofRecState y) then
          {(SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y)}
        else ∅ := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Set.mem_iUnion.2 ⟨b, by simp [hb]⟩
    · intro ha
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
      by_cases hfirst : FirstRecord (extendPath b.2) b.1 (ofRecState y)
      · refine ⟨b, hfirst, ?_⟩
        simpa [hfirst] using hb
      · simp [hfirst] at hb
  rw [heq]
  refine MeasurableSet.iUnion fun b => ?_
  by_cases hb : FirstRecord (extendPath b.2) b.1 (ofRecState y)
  · simp only [if_pos hb]
    have h := (SwarmFreshTwoSeg.measurableSet_seg_singleton
      (SwarmSegKernel.segOf y b.1 b.2)).prod
        (measurableSet_singleton (RecKernel.out hm b.2 y))
    rwa [Set.singleton_prod_singleton] at h
  · simp [hb]

/-- The entire mass of `asegK y` is carried by its genuine first-record atoms.
This uses the unnormalised raw words and their actual endpoint states. -/
theorem asegK_canonicalAtom (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (y : RecState N m) :
    (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
      {a | CanonicalAtom hm y a} = 1 := by
  classical
  rw [SwarmSegKernel.asegK_apply p hm y (measurableSet_canonicalAtom hm y)]
  calc
    (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
        (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈
          {a | CanonicalAtom hm y a} then 1 else 0)) =
        ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
          ENNReal.ofReal (RecKernel.hitW p pq.2 y) := by
      apply tsum_congr
      rintro ⟨k, q⟩
      by_cases hq : FirstRecord (extendPath q) k (ofRecState y)
      · have hmem : (SwarmSegKernel.segOf y k q, RecKernel.out hm q y) ∈
            {a | CanonicalAtom hm y a} := ⟨⟨k, q⟩, hq, rfl⟩
        rw [if_pos hmem, mul_one]
      · rw [RecKernel.hitW_of_not_firstRecord p q y hq,
          ENNReal.ofReal_zero, zero_mul]
    _ = 1 := SwarmDHStruct.tsum_hitW p hm hp hp1 y

/-- Almost-everywhere form of the exact one-step support. -/
theorem ae_asegK_canonicalAtom (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (y : RecState N m) :
    ∀ᵐ a ∂(SwarmSegKernel.asegK (N := N) (m := m) p hm y),
      CanonicalAtom hm y a := by
  letI : IsProbabilityMeasure (SwarmSegKernel.asegK (N := N) (m := m) p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  exact (mem_ae_iff_prob_eq_one (measurableSet_canonicalAtom hm y)).2
    (asegK_canonicalAtom p hm hp hp1 y)

/-- The variable-start successor event used by `cyl_measure` is measurable. -/
theorem measurableSet_canonicalAtom_cyl (hm : 1 ≤ m) (n : ℕ) :
    MeasurableSet {q : (Π _i : Finset.Iic n, SwarmInfSeg.Pair N m) ×
      SwarmInfSeg.Pair N m |
      CanonicalAtom hm (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 q.2} := by
  classical
  letI : MeasurableEq (SwarmConcat.Seg N) := ⟨by
    change MeasurableSet {st : SwarmConcat.Seg N × SwarmConcat.Seg N | st.1 = st.2}
    have hdiag : {st : SwarmConcat.Seg N × SwarmConcat.Seg N | st.1 = st.2} =
        {st | st.1.dur = st.2.dur} ∩
          ⋂ t, ⋂ i, {st | st.1.p t i = st.2.p t i} := by
      ext st
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro h
        rw [h]
        exact ⟨rfl, fun _ _ => rfl⟩
      · rintro ⟨hd, hp⟩
        cases st with
        | mk s t =>
          cases s
          cases t
          simp_all
          exact funext fun u => funext fun i => hp u i
    rw [hdiag]
    refine (measurableSet_eq_fun
      (SwarmConcat.measurable_seg_dur.comp measurable_fst)
      (SwarmConcat.measurable_seg_dur.comp measurable_snd)).inter ?_
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
      measurableSet_eq_fun
        ((SwarmConcat.measurable_seg_p t i).comp measurable_fst)
        ((SwarmConcat.measurable_seg_p t i).comp measurable_snd)⟩
  let lastState : ((Π _i : Finset.Iic n, SwarmInfSeg.Pair N m) ×
      SwarmInfSeg.Pair N m) → RecState N m :=
    fun q => (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩).2
  have hlast : Measurable lastState :=
    measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
  have heq : {q : (Π _i : Finset.Iic n, SwarmInfSeg.Pair N m) ×
      SwarmInfSeg.Pair N m | CanonicalAtom hm (lastState q) q.2} =
      ⋃ b : RawBlock N,
        {q | FirstRecord (extendPath b.2) b.1 (ofRecState (lastState q))} ∩
        ({q | q.2.1 = SwarmSegKernel.segOf (lastState q) b.1 b.2} ∩
        {q | q.2.2 = RecKernel.out hm b.2 (lastState q)}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Prod.ext_iff]
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨b, hb, hs, hr⟩
      exact ⟨b, hb, Prod.ext hs hr⟩
  change MeasurableSet {q | CanonicalAtom hm (lastState q) q.2}
  rw [heq]
  refine MeasurableSet.iUnion fun b => ?_
  refine ((RecKernel.measurableSet_firstRecord (N := N) (m := m) b.1 b.2).preimage
    hlast).inter ?_
  refine (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    ((SwarmSegKernel.measurable_segOf b.1 b.2).comp hlast)).inter ?_
  letI : T2Space (RecState N m) := inferInstance
  letI : SecondCountableTopology (RecState N m) := inferInstance
  letI : BorelSpace (RecState N m) := inferInstance
  exact measurableSet_eq_fun (measurable_snd.comp measurable_snd)
    ((RecKernel.measurable_out hm b.1 b.2).comp hlast)

/-- At every previous enriched atom, `pairK` has full mass on atoms starting at
that atom's actual endpoint state. -/
theorem pairK_canonicalAtom (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (a : SwarmInfSeg.Pair N m) :
    (SwarmSegKernel.pairK (N := N) (m := m) p hm a)
      {b | CanonicalAtom hm a.2 b} = 1 := by
  rw [SwarmSegKernel.pairK_apply]
  exact asegK_canonicalAtom p hm hp hp1 a.2

/-- Every successor coordinate is canonical at the previous coordinate's actual
endpoint state, for an arbitrary initial probability law. -/
theorem measure_infLaw_canonicalAtom_succ (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (π : Measure (RecState N m))
    [IsProbabilityMeasure π] (n : ℕ) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
      {A : ℕ → SwarmInfSeg.Pair N m | CanonicalAtom hm (A n).2 (A (n + 1))} = 1 := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    SwarmInfSeg.isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hinf : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp hp1 π
  have hC := measurableSet_canonicalAtom_cyl (N := N) (m := m) hm n
  have hpre : (fun A : ℕ → SwarmInfSeg.Pair N m =>
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A, A (n + 1))) ⁻¹'
      {q : (Π _i : Finset.Iic n, SwarmInfSeg.Pair N m) × SwarmInfSeg.Pair N m |
        CanonicalAtom hm (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 q.2} =
      {A : ℕ → SwarmInfSeg.Pair N m | CanonicalAtom hm (A n).2 (A (n + 1))} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Preorder.frestrictLe_apply]
  rw [← hpre, SwarmInfSeg.cyl_measure p hm hp hp1 π n hC]
  have hfib : ∀ v : Π _i : Finset.Iic n, SwarmInfSeg.Pair N m,
      (Prod.mk v ⁻¹' {q : (Π _i : Finset.Iic n, SwarmInfSeg.Pair N m) ×
        SwarmInfSeg.Pair N m |
        CanonicalAtom hm (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 q.2}) =
      {b | CanonicalAtom hm (v ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 b} := fun _ => rfl
  simp only [hfib]
  have hstep : ∀ v : Π _i : Finset.Iic n, SwarmInfSeg.Pair N m,
      (SwarmSegKernel.pairK (N := N) (m := m) p hm
        (v ⟨n, Finset.mem_Iic.2 le_rfl⟩))
        {b | CanonicalAtom hm (v ⟨n, Finset.mem_Iic.2 le_rfl⟩).2 b} = 1 :=
    fun _ => pairK_canonicalAtom p hm hp hp1 _
  simp only [hstep, lintegral_one]
  haveI hprob : IsProbabilityMeasure
      ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n)) :=
    Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) n).aemeasurable
  rw [measure_univ]

/-- The first coordinate of a Dirac-pinned trajectory is a canonical atom at
its pinned start, with probability one. -/
theorem measure_infLaw_dirac_canonicalAtom_zero (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y))
      {A : ℕ → SwarmInfSeg.Pair N m | CanonicalAtom hm y (A 0)} = 1 := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  haveI hinf : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp hp1 (Measure.dirac y)
  rw [show {A : ℕ → SwarmInfSeg.Pair N m | CanonicalAtom hm y (A 0)} =
      (fun A : ℕ → SwarmInfSeg.Pair N m => A 0) ⁻¹' {a | CanonicalAtom hm y a} from rfl,
    ← Measure.map_apply (measurable_pi_apply (0 : ℕ)) (measurableSet_canonicalAtom hm y),
    SwarmInfSeg.map_eval_zero p hm hp hp1 (Measure.dirac y),
    SwarmInitialTransport.pairLaw_dirac]
  exact asegK_canonicalAtom p hm hp hp1 y

/-- Almost-everywhere first-coordinate support under the pinned law. -/
theorem infLaw_dirac_canonicalAtom_zero_ae (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m) :
    ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)),
      CanonicalAtom hm y (A 0) := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  letI : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp hp1 (Measure.dirac y)
  exact (mem_ae_iff_prob_eq_one
    ((measurableSet_canonicalAtom hm y).preimage (measurable_pi_apply (0 : ℕ)))).2
      (measure_infLaw_dirac_canonicalAtom_zero p hm hp hp1 y)

/-- Almost-everywhere successor support for every index and arbitrary initial
probability law. -/
theorem infLaw_canonicalAtom_succ_ae (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (π : Measure (RecState N m))
    [IsProbabilityMeasure π] (n : ℕ) :
    ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π),
      CanonicalAtom hm (A n).2 (A (n + 1)) := by
  letI : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp hp1 π
  have hC := measurableSet_canonicalAtom_cyl (N := N) (m := m) hm n
  have hmeas : MeasurableSet
      {A : ℕ → SwarmInfSeg.Pair N m | CanonicalAtom hm (A n).2 (A (n + 1))} := by
    have h := hC.preimage (SwarmInfSeg.measurable_prefixSucc (N := N) (m := m) n)
    convert h using 1
    ext A
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Preorder.frestrictLe_apply]
  exact (mem_ae_iff_prob_eq_one hmeas).2
    (measure_infLaw_canonicalAtom_succ p hm hp hp1 π n)

/-- The complete countable intersection: the pinned infinite enriched
trajectory is coherent at every index almost surely. -/
theorem infLaw_dirac_coherent_ae (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p)
    (hp1 : p ≤ 1) (y : RecState N m) :
    ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)),
      Coherent hm y A := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  let μ := SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)
  have hzero : ∀ᵐ A ∂μ, CanonicalAtom hm y (A 0) :=
    infLaw_dirac_canonicalAtom_zero_ae p hm hp hp1 y
  have hsucc : ∀ᵐ A ∂μ, ∀ n, CanonicalAtom hm (A n).2 (A (n + 1)) :=
    ae_all_iff.2 (fun n => infLaw_canonicalAtom_succ_ae p hm hp hp1 (Measure.dirac y) n)
  filter_upwards [hzero, hsucc] with A hA0 hAs
  exact ⟨hA0, hAs⟩

/-- Coherence and segment compatibility hold simultaneously almost surely.
`TrajCompat` is used only through the recovered coherent cover. -/
theorem infLaw_dirac_coherent_trajCompat_ae (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m) :
    ∀ᵐ A ∂(SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)),
      Coherent hm y A ∧ SwarmChainAssemble.TrajCompat A := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  let μ := SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 (Measure.dirac y)
  filter_upwards [infLaw_dirac_coherent_ae p hm hp hp1 y,
    SwarmInfSeg.trajCompat_ae p hm hp hp1 (Measure.dirac y)] with A hCoh hCompat
  exact ⟨hCoh, hCompat⟩

/-- Full pinned raw-window mass, not merely the canonical-fibre part. -/
theorem infLaw_dirac_rawWindow_eq_sum
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le (Measure.dirac y))
      ((Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
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
  have hcoh : ∀ᵐ A ∂μ, Coherent hm y A := infLaw_dirac_coherent_ae p hm hp0.le hp1.le y
  have hcompat : ∀ᵐ A ∂μ, SwarmChainAssemble.TrajCompat A :=
    SwarmInfSeg.trajCompat_ae p hm hp0.le hp1.le (Measure.dirac y)
  have hcover : μ ((Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
        prefixWindow (N := N) (m := m) K K C) =
      μ ((⋃ d : MaxRecordDecomp (N := N) hm y K, natCanonicalCylinder hm y d) ∩
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
          prefixWindow (N := N) (m := m) K K C) := by
    apply measure_congr
    filter_upwards [hcoh, hcompat] with A hAco hAcomp
    apply propext
    constructor
    · intro hwindow
      obtain ⟨d, hnat, -, -⟩ :=
        exists_natCanonicalCylinder_raw_guards_of_prefixWindow hy hAcomp hAco hwindow
      exact ⟨Set.mem_iUnion.2 ⟨d, hnat⟩, hwindow⟩
    · exact fun h => h.2
  exact hcover.trans
    (SwarmRawWindowMass.infLaw_dirac_canonical_rawWindow_part_eq_sum
      p hm hp0 hp1 y hy K C hC)

/-- The full pinned enriched raw window has exactly the original raw-array
finite-strict/pattern mass. -/
theorem infLaw_dirac_rawWindow_eq_arrayMeasure
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le (Measure.dirac y))
      ((Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
        prefixWindow (N := N) (m := m) K K C) =
      (Swarming.Uniform.arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  calc
    _ = ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := infLaw_dirac_rawWindow_eq_sum p hm hp0 hp1 y hy K C hC
    _ = _ := (SwarmRawWindowMass.arrayMeasure_finStrict_pattern_maxRecordDecomp_of_srSet
      p hp0 hp1 hm y hy K C).symm

/-- Full pinned raw-window mass as the guarded sum of the actual canonical
trajectory cylinders at their own decomposition horizons. -/
theorem infLaw_dirac_rawWindow_eq_sum_canonicalTrajectoryWindow
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le (Measure.dirac y))
      ((Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) K) ⁻¹'
        prefixWindow (N := N) (m := m) K K C) =
      ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le
              (Measure.dirac y)).map
            (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m)
              d.completed.length)) (canonicalTrajectoryWindow y d)
        else 0 := by
  rw [infLaw_dirac_rawWindow_eq_arrayMeasure p hm hp0 hp1 y hy K C hC]
  exact SwarmRawWindowMass.arrayMeasure_finStrict_pattern_eq_sum_canonicalTrajectoryWindow_of_srSet
    p hp0 hp1 hm y hy K C

/-- The full raw window at the common finite enriched horizon `K + 1` has the
same guarded mass formula.  No family or arbitrary-`n` assertion is made. -/
theorem chainVec_rawWindow_eq_sum
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
      (rawWindowVec (N := N) (m := m) (K := K) C) =
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
  rw [← infLaw_dirac_rawWindow_eq_sum p hm hp0 hp1 y hy K C hC]
  have hS : rawWindowVec (N := N) (m := m) (K := K) C =
      finToPrefix ⁻¹' prefixWindow (N := N) (m := m) K K C := rfl
  rw [hS, ← Measure.map_apply measurable_finToPrefix hprefix,
    ← SwarmInitialTransport.pairLaw_dirac p hm y,
    ← SwarmInitialTransport.infLaw_prefix_eq_chainVec p hm hp0.le hp1.le
      (Measure.dirac y) K,
    Measure.map_apply
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) K) hprefix]

/-- Finite common-horizon full-window/raw-array identity. -/
theorem chainVec_rawWindow_eq_arrayMeasure
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (y : RecState N m) (hy : y ∈ srSet N m)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
      (rawWindowVec (N := N) (m := m) (K := K) C) =
      (Swarming.Uniform.arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  calc
    _ = ∑ d : MaxRecordDecomp (N := N) hm y K,
        if SwarmFreshPos.PosSeqFin (N := N) (decompWord d) ∧
            patOf (N := N) (decompWord d) ∈ C then
          ENNReal.ofReal
            (prefixW p hm y d.completed *
              pathW p d.tail.1 d.tail.2 (ofRecState (terminal hm y d.completed)))
        else 0 := chainVec_rawWindow_eq_sum p hm hp0 hp1 y hy K C hC
    _ = _ := (SwarmRawWindowMass.arrayMeasure_finStrict_pattern_maxRecordDecomp_of_srSet
      p hp0 hp1 hm y hy K C).symm

end SwarmRawGlobalCover
