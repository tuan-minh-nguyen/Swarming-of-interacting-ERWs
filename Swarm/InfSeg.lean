/-
# The infinite enriched record-segment trajectory on `ℕ`

`Swarm/SegKernel.lean` builds the path-enriched record step `asegK p hm y` (the law of
`(segment, next record state)` given the current record state `y`) and its Markov transition
`pairK` on `Pair = Seg N × RecState N m`; `pairLaw p hm π = π.bind asegK` is invariant for
`pairK` whenever `π` is invariant for the true stopped record kernel `hitKKernel p hm`.

This file builds a *genuine probability law on the infinite enriched trajectory*
`ℕ → Pair`, by Ionescu–Tulcea (`ProbabilityTheory.Kernel.trajMeasure`, available in Mathlib for
arbitrary measurable state spaces, so no compactness of `Seg N` and no compact retract is
needed), started from `pairLaw`.  The main results are

* `infLaw` : the law on `ℕ → Pair`, a probability measure;
* `map_eval_zero` : its first coordinate is exactly `pairLaw` (so the record state at time `0`
  has law `π`): the initial-law statement is *not* a Dirac-at-a-seed shortcut;
* `ae_compatSet` / `ae_pairCompat` : on a set of full measure, *every* consecutive pair of
  enriched steps is level-compatible in the sense of `SwarmConcat.Chain.compat`
  (`p_k(dur_k) = 1 + p_{k+1}(0)`), using `DForward.compat_step_ae`.

The stationarity of `pairLaw` under `pairK` is *not* needed for the a.e. compatibility: it is
needed only to interpret the sequence as a stationary system, which is left as the explicit
residual `shift_invariance_residual` below.
-/
import Swarm.SegKernel
import Swarm.DForward
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory Set ProbabilityTheory
open SimJump
open scoped ENNReal

namespace SwarmInfSeg

attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {N m : ℕ}

/-- The enriched state of the record chain: one segment together with the record state at its
end.  (`SegKernel.pairK` acts on this type.) -/
abbrev Pair (N m : ℕ) := SwarmConcat.Seg N × SwarmRec.RecState N m

variable (p : ℝ) (hm : 1 ≤ m)

/-! ## 1. The homogeneous Ionescu–Tulcea family and the trajectory law -/

/-- The one-step Ionescu–Tulcea kernel of the *enriched* chain: as a kernel on the record of the
chain up to time `n`, it reads the last coordinate and applies `pairK`. -/
noncomputable def homK (n : ℕ) : Kernel (Π _i : Finset.Iic n, Pair N m) (Pair N m) :=
  (SwarmSegKernel.pairK (N := N) (m := m) p hm).comap
    (fun v => v ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem isMarkovKernel_homK (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    IsMarkovKernel (homK (N := N) (m := m) p hm n) := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  unfold homK
  infer_instance

theorem isProbabilityMeasure_pairLaw (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) := by
  constructor
  rw [SwarmSegKernel.pairLaw, Measure.bind_apply MeasurableSet.univ
    (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm).aemeasurable]
  simp only [SwarmSegKernel.asegK_univ p hm hp hp1, lintegral_one, measure_univ]

/-- **The infinite enriched trajectory law**: the law on `ℕ → Pair` of the chain started with
`pairLaw` and driven by the enriched step `pairK`, obtained from the Ionescu–Tulcea theorem. -/
noncomputable def infLaw (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    Measure (ℕ → Pair N m) :=
  @ProbabilityTheory.Kernel.trajMeasure (fun _ => Pair N m) (fun _ => inferInstance)
    (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) (homK (N := N) (m := m) p hm)
    (isMarkovKernel_homK (N := N) (m := m) p hm hp hp1)

theorem isProbabilityMeasure_infLaw (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  unfold infLaw
  infer_instance

/-- The defining finite-dimensional-distribution (one-step Markov) identity of the Ionescu–Tulcea
law: the joint law of the record up to time `n` and the next coordinate is the record law
composed with the next kernel. -/
theorem jointLaw (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) n) ⊗ₘ
        (homK (N := N) (m := m) p hm n)
      = (infLaw (N := N) (m := m) p hm hp hp1 π).map
          (fun x => (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))) := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hKall : ∀ n, IsMarkovKernel (homK (N := N) (m := m) p hm n) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1
  unfold infLaw
  rw [ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]

/-! ## 2. Level compatibility of two consecutive enriched steps -/

/-- Two consecutive enriched steps are *level-compatible*: the end of the first segment equals
the start of the second segment, one level up.  This is `SwarmConcat.Chain.compat` at level
translation, with the two level shifts cancelled. -/
def CompatPair (a b : Pair N m) : Prop := ∀ i, a.1.p a.1.dur i = 1 + b.1.p 0 i

/-- Level compatibility in the exact pointwise form of `SwarmConcat.Chain.compat`. -/
theorem chain_compat_of_compatPair (a b : Pair N m) (k : ℕ) (i : Fin N)
    (h : CompatPair a b) :
    (k : ℤ) + a.1.p a.1.dur i = ((k + 1 : ℕ) : ℤ) + b.1.p 0 i := by
  have h' := h i
  push_cast
  rw [h']
  ring

theorem measurableSet_compatPair :
    MeasurableSet {q : Pair N m × Pair N m | CompatPair q.1 q.2} := by
  have heq : {q : Pair N m × Pair N m | CompatPair q.1 q.2}
      = ⋂ i : Fin N, ⋃ k : ℕ,
          ({q : Pair N m × Pair N m | q.1.1.dur = k} ∩
            {q : Pair N m × Pair N m | q.1.1.p k i = 1 + q.2.1.p 0 i}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff,
      CompatPair]
    constructor
    · intro h i
      exact ⟨q.1.1.dur, rfl, h i⟩
    · rintro h i
      obtain ⟨k, hk, hp⟩ := h i
      rw [hk]
      exact hp
  rw [heq]
  refine MeasurableSet.iInter fun i => MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.preimage (measurableSet_singleton k)
      ((SwarmConcat.measurable_seg_dur (N := N)).comp (measurable_fst.comp measurable_fst))
  · refine measurableSet_eq_fun ?_ ?_
    · exact (SwarmConcat.measurable_seg_p (N := N) k i).comp (measurable_fst.comp measurable_fst)
    · exact measurable_const.add
        ((SwarmConcat.measurable_seg_p (N := N) 0 i).comp (measurable_fst.comp measurable_snd))

theorem measurableSet_compatPair_right (a : Pair N m) :
    MeasurableSet {b : Pair N m | CompatPair a b} := by
  have heq : {b : Pair N m | CompatPair a b}
      = ⋂ i : Fin N, {b : Pair N m | 1 + b.1.p 0 i = a.1.p a.1.dur i} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, CompatPair]
    constructor
    · intro h i
      rw [h i]
    · intro h i
      have := h i
      omega
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_eq_fun
    (measurable_const.add ((SwarmConcat.measurable_seg_p (N := N) 0 i).comp measurable_fst))
    measurable_const

/-- On the consistent pairs `CompatSet`, the set of possible next segments that are compatible
with the first one contains the whole start set of the endpoint state. -/
theorem startSet_subset_compatPair {a : Pair N m}
    (ha : a ∈ SwarmDHStruct.CompatSet N m) :
    SwarmDHStruct.StartSet N m a.2 ⊆ {b : Pair N m | CompatPair a b} := by
  intro b hb i
  have h1 : b.1.p 0 i = (Record.ofRecState a.2).pos i := hb i
  have h2 : a.1.p a.1.dur i = 1 + (Record.ofRecState a.2).pos i := ha i
  rw [h1]
  exact h2

/-- Off `CompatSet` no segment that starts at the endpoint state can be compatible. -/
theorem subset_compl_startSet_of_not_mem {a : Pair N m}
    (ha : a ∉ SwarmDHStruct.CompatSet N m) :
    {b : Pair N m | CompatPair a b} ⊆ (SwarmDHStruct.StartSet N m a.2)ᶜ := by
  intro b hb hbstart
  refine ha fun i => ?_
  have h1 : a.1.p a.1.dur i = 1 + b.1.p 0 i := hb i
  have h2 : b.1.p 0 i = (Record.ofRecState a.2).pos i := hbstart i
  rw [h2] at h1
  exact h1

/-- **The key one-step computation.**  For *every* enriched state `a`, the next enriched step is
compatible with `a` with probability one exactly when `a` is itself consistent
(`a ∈ CompatSet`), and with probability zero otherwise. -/
theorem pairK_compat (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (a : Pair N m) :
    (SwarmSegKernel.pairK (N := N) (m := m) p hm a) {b : Pair N m | CompatPair a b}
      = if a ∈ SwarmDHStruct.CompatSet N m then 1 else 0 := by
  classical
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  have hStart : (SwarmSegKernel.pairK (N := N) (m := m) p hm a)
      (SwarmDHStruct.StartSet N m a.2) = 1 :=
    SwarmDHStruct.ae_start_step (N := N) (m := m) p hm hp hp1 a.2
  have hmeasS : MeasurableSet (SwarmDHStruct.StartSet N m a.2) :=
    SwarmDHStruct.measurableSet_startSet (N := N) (m := m) a.2
  by_cases ha : a ∈ SwarmDHStruct.CompatSet N m
  · rw [if_pos ha]
    refine le_antisymm (prob_le_one) ?_
    calc (1 : ℝ≥0∞) = (SwarmSegKernel.pairK (N := N) (m := m) p hm a)
          (SwarmDHStruct.StartSet N m a.2) := hStart.symm
      _ ≤ (SwarmSegKernel.pairK (N := N) (m := m) p hm a)
            {b : Pair N m | CompatPair a b} := measure_mono (startSet_subset_compatPair ha)
  · rw [if_neg ha]
    have hsub := subset_compl_startSet_of_not_mem ha
    have h0 : (SwarmSegKernel.pairK (N := N) (m := m) p hm a)
        (SwarmDHStruct.StartSet N m a.2)ᶜ = 0 := by
      rw [measure_compl hmeasS (measure_ne_top _ _), hStart, measure_univ]
      simp
    exact le_antisymm (le_trans (measure_mono hsub) h0.le) (by simp)


/-! ## 3. The cylinder identity and the first-coordinate law -/

theorem measurable_prefixSucc (n : ℕ) :
    Measurable (fun x : ℕ → Pair N m =>
      (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))) :=
  (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) n).prodMk (measurable_pi_apply _)

/-- **The cylinder identity.**  For any measurable set `C` of "record up to time `n` together with
the coordinate `n+1`", the measure of the cylinder is the integral of the next-step kernel
`pairK`, applied to the last coordinate of the record, over the law of the record. -/
theorem cyl_measure (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ)
    {C : Set ((Π _i : Finset.Iic n, Pair N m) × Pair N m)} (hC : MeasurableSet C) :
    (infLaw (N := N) (m := m) p hm hp hp1 π)
        ((fun x : ℕ → Pair N m =>
          (Preorder.frestrictLe (π := fun _ => Pair N m) n x, x (n + 1))) ⁻¹' C)
      = ∫⁻ v, (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨n, Finset.mem_Iic.2 le_rfl⟩))
          (Prod.mk v ⁻¹' C) ∂((infLaw (N := N) (m := m) p hm hp hp1 π).map
            (Preorder.frestrictLe (π := fun _ => Pair N m) n)) := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hKall : ∀ n, IsMarkovKernel (homK (N := N) (m := m) p hm n) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1
  haveI hinf : IsProbabilityMeasure (infLaw (N := N) (m := m) p hm hp hp1 π) :=
    isProbabilityMeasure_infLaw p hm hp hp1 π
  haveI hprob : IsProbabilityMeasure ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => Pair N m) n)) :=
    Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) n).aemeasurable
  haveI : SFinite ((infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => Pair N m) n)) := inferInstance
  rw [← Measure.map_apply (measurable_prefixSucc (N := N) (m := m) n) hC,
    ← jointLaw (N := N) (m := m) p hm hp hp1 π n, Measure.compProd_apply hC]
  rfl

/-- The law of the coordinate `n+1` against a measurable set of enriched states. -/
theorem measure_succ_mem (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ)
    {S : Set (Pair N m)} (hS : MeasurableSet S) :
    (infLaw (N := N) (m := m) p hm hp hp1 π) {x : ℕ → Pair N m | x (n + 1) ∈ S}
      = ∫⁻ v, (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨n, Finset.mem_Iic.2 le_rfl⟩)) S
        ∂((infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => Pair N m) n)) := by
  have hC : MeasurableSet
      {q : (Π _i : Finset.Iic n, Pair N m) × Pair N m | q.2 ∈ S} := measurable_snd hS
  have h := cyl_measure (N := N) (m := m) p hm hp hp1 π n hC
  simpa using h

/-- The initial measure of the consistent set of enriched steps is one: `π`-a.e. record state
produces a consistent first step (this is `DHStruct.ae_compat_step`, which holds for *every*
record state). -/
theorem pairLaw_compatSet (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    SwarmSegKernel.pairLaw (N := N) (m := m) p hm π
      (SwarmDHStruct.CompatSet N m) = 1 := by
  rw [SwarmSegKernel.pairLaw,
    Measure.bind_apply (SwarmDHStruct.measurableSet_compatSet (N := N) (m := m))
      (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm).aemeasurable]
  rw [lintegral_congr fun y => SwarmDHStruct.ae_compat_step (N := N) (m := m) p hm hp hp1 y]
  simp only [lintegral_one, measure_univ]

/-- **The exact initial law of the infinite trajectory**: the first coordinate has law
`pairLaw p hm π = π.bind asegK`, so the record state at time `0` has law `π`.  There is no
Dirac-at-seed initialisation here. -/
theorem map_eval_zero (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    (infLaw (N := N) (m := m) p hm hp hp1 π).map (fun x : ℕ → Pair N m => x 0)
      = SwarmSegKernel.pairLaw (N := N) (m := m) p hm π := by
  haveI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hπ : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    isProbabilityMeasure_pairLaw p hm hp hp1 π
  haveI hKall : ∀ n, IsMarkovKernel (homK (N := N) (m := m) p hm n) :=
    isMarkovKernel_homK (N := N) (m := m) p hm hp hp1
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply (0 : ℕ)) hA]
  have hpre : MeasurableSet ((fun x : ℕ → Pair N m => x 0) ⁻¹' A) :=
    (measurable_pi_apply (0 : ℕ)) hA
  unfold infLaw ProbabilityTheory.Kernel.trajMeasure
  rw [Measure.bind_apply hpre (Kernel.aemeasurable _)]
  -- the inner integral against the one-step trajectory
  have hinner : ∀ v : Π _i : Finset.Iic 0, Pair N m,
      (ProbabilityTheory.Kernel.traj (homK (N := N) (m := m) p hm) 0 v)
          ((fun x : ℕ → Pair N m => x 0) ⁻¹' A)
        = (if v ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ A then 1 else 0) := by
    intro v
    have hd : (ProbabilityTheory.Kernel.traj (homK (N := N) (m := m) p hm) 0 v).map
        (Preorder.frestrictLe (π := fun _ => Pair N m) 0) = Measure.dirac v := by
      rw [ProbabilityTheory.Kernel.traj_map_frestrictLe_apply,
        ProbabilityTheory.Kernel.partialTraj_self]
      rfl
    have hcomp : (fun x : ℕ → Pair N m => x 0)
        = (fun w : Π _i : Finset.Iic 0, Pair N m => w ⟨0, Finset.mem_Iic.2 le_rfl⟩)
            ∘ (Preorder.frestrictLe (π := fun _ => Pair N m) 0) := rfl
    have hB : MeasurableSet
        ((fun w : Π _i : Finset.Iic 0, Pair N m => w ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          ⁻¹' A) := (measurable_pi_apply _) hA
    rw [hcomp, Set.preimage_comp,
      ← Measure.map_apply (Preorder.measurable_frestrictLe (X := fun _ => Pair N m) 0) hB, hd,
      Measure.dirac_apply' _ hB]
    simp [Set.indicator_apply]
  rw [lintegral_congr hinner]
  -- the integral of the indicator is the measure of the set
  have hB0 : MeasurableSet
      ((fun w : Π _i : Finset.Iic 0, Pair N m => w ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' A) :=
    (measurable_pi_apply _) hA
  have hstep1 : ∫⁻ v, (if v ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ A then 1 else 0)
      ∂(SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Pair N m)).symm
      = ((SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Pair N m)).symm)
          ((fun w : Π _i : Finset.Iic 0, Pair N m => w ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' A) := by
    rw [← lintegral_indicator_one (μ := (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Pair N m)).symm) hB0]
    congr 1
  rw [hstep1, ← Measure.map_apply (measurable_pi_apply
      (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0)) hA,
    Measure.map_map (measurable_pi_apply
      (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0))
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Pair N m)).symm.measurable]
  have hcomp_id : ((fun w : Π _i : Finset.Iic 0, Pair N m =>
        w ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Pair N m)).symm) = id := by
    funext a
    simp [MeasurableEquiv.piUnique_symm_apply]
  rw [hcomp_id, Measure.map_id]

end SwarmInfSeg
