/-
# R1 transfer: the actual array itself has almost surely infinitely many simultaneous records

`WCJF.RecFreq.ae_frequently_srSet_of_dT_tight` (`RecordPathStep.lean`, re-verified in this
directory) proves the frequency conclusion for the *canonical stopped-record chain*
`recordTraj p hp hp1 hm (ν.map Prod.fst)`, i.e. on the abstract record path space.  The literal
`MainClaim` object is the actual array law `Swarming.Uniform.arrayMeasure N` on
`Array N = (Fin N × ℤ × ℕ) → ℝ`.  This file supplies the missing identification and the transfer:

* `arrPath` — the literal actual (record state, record time) sequence
  `r ↦ (M7Block.actRecStateT p m U hm r, recTimeA p m U r)`; total, with the documented
  `zeroState`/`0` default off `ReachAll`, and measurable (`measurable_arrPath`);
* `array_fullLaw` — **the full infinite-dimensional law identity**: the law of that sequence
  under `arrayMeasure N` is exactly the Ionescu–Tulcea stopped-record trajectory
  `recordTrajT p hp hp1 hm (δ_{(zeroState, 0)})`.  It is obtained from the already accepted
  finite windows `M7Block.actual_blockPath_map` + `M6Step.blockPathLaw_eq_recordTrajT_window`
  through the π-system/cylinder uniqueness `M2WindowLaw.measure_eq_of_forall_window`, so no
  new law input is introduced and no arbitrary start law is used (the Dirac start is forced by
  `M2RecordFinite.eq_dirac_of_finiteRecLaw_ge_two`);
* `ae_frequently_srSetT_of_dT_tight` — the frequency step on the *time-extended* chain: the
  one-step Markov identity is proved from the Ionescu–Tulcea construction itself
  (`WCJF.OneStepBridge.condExp_indicator_succ`) for the genuine kernel `hitKKernelT`, the force
  estimate is `SimJump.RecKernel.hitKKernelT_srSet_ge`, and the tightness input is the literal
  paper `dT` tail;
* `ae_frequently_srSet_array_of_dT_tight` — **the array transfer**: from actual `dT` tightness at
  the forced Dirac start,
  `∀ᵐ U ∂arrayMeasure N, ∃ᶠ r, actRecStateT p m U hm r ∈ srSet N m`, i.e. almost surely
  infinitely many *actual* record states at which all walkers sit exactly at the record
  (a simultaneous record);
* `ae_frequently_srSet_array_of_two_blocks` — the same with the two genuine block clauses
  `AdvanceClause`/`HalfClause` (the repository's `hAdv`/`hOff` residual inputs) and their
  profile decay in place of the tightness hypothesis, via
  `AuditResidual.record_tightness_of_two_actual_blocks`.

Deliberately *not* claimed: nullity of the strict-failure event `D = ⊤`, invariance or
stationarity, the Kac mean, adaptivity of the attempt rows, regeneration, or the common velocity.
No `sorry`, no custom axiom, no `native_decide`.
-/
import Swarm.RecordPathStep
import Swarm.ActualBlockPath
import Swarm.WindowLaw
import Swarm.M2WindowLaw
import Swarm.InvariantPositivity
import Swarm.TightAvail
import Swarm.AuditResidual

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter Topology Classical
open MeasureTheory.Filtration
open scoped ENNReal BigOperators

namespace WCJF.ActPath

open Swarming Swarming.Uniform SwarmRec SwarmRecordMeas SwarmRecordMeas.Actual
open SwarmRecordMeas.StartLaw
open SimJump SimJump.RecKernel

variable {N : ℕ} [Nonempty (Fin N)] {m : ℕ}

/-! ### 1. The literal actual record path -/

/-- The totalised actual record state `M7Block.actRecStateT` is the `M2RecordFinite` version with
the arguments reordered; both are the same `if U ∈ ReachAll then … else zeroState` term. -/
theorem actRecStateT_eq_actRecStateA (p : ℝ) (hm : 1 ≤ m) (U : Array N) (r : ℕ) :
    M7Block.actRecStateT p m U hm r = M2RecordFinite.actRecStateA p m hm U r := rfl

/-- **The literal actual (record state, record time) sequence.**  Off `ReachAll p m` (a null set,
`M4RecordGeom.ae_reachAll`) the record state is the documented `zeroState` fallback and the
record time is `0` (`recTimeA_eq_zero_off`). -/
noncomputable def arrPath (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (U : Array N) :
    ℕ → RecState N m × ℕ :=
  fun r => (M7Block.actRecStateT p m U hm r, recTimeA p m U r)

theorem arrPath_apply (p : ℝ) (hm : 1 ≤ m) (U : Array N) (r : ℕ) :
    arrPath p m hm U r = (M7Block.actRecStateT p m U hm r, recTimeA p m U r) := rfl

/-- The actual record path is measurable as a function of the array. -/
theorem measurable_arrPath (p : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Measurable (arrPath (N := N) p m hm) :=
  measurable_pi_lambda (X := fun _ : ℕ => RecState N m × ℕ)
    (fun U r => (M2RecordFinite.actRecStateA p m hm U r, recTimeA p m U r))
    (fun r =>
      (M2RecordFinite.measurable_actRecStateA p m hm r).prodMk (measurable_recTimeA p m r))

/-! ### 2. The full infinite-dimensional law identity at the actual array -/

/-- **The actual array's full record-state/record-time sequence has the law of the canonical
stopped-record trajectory at the forced Dirac start.**

The finite `Fin (r+1)` windows are `M7Block.actual_blockPath_map` on the array side and
`M6Step.blockPathLaw_eq_recordTrajT_window` on the trajectory side; countable-window uniqueness
`M2WindowLaw.measure_eq_of_forall_window` promotes them to the infinite law.  Both sides are
pushforwards of probability measures, so no σ-finiteness or additional integrability is used, and
no arbitrary start law appears: `δ_{(zeroState, 0)}` is the only compatible one. -/
theorem array_fullLaw (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N).map (arrPath (N := N) p m (by omega : 1 ≤ m))
      = recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))) := by
  let hm1 : 1 ≤ m := by omega
  haveI hP1 : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  haveI hP1' : IsProbabilityMeasure ((arrayMeasure N).map (arrPath (N := N) p m hm1)) :=
    Measure.isProbabilityMeasure_map (measurable_arrPath p m hm1).aemeasurable
  haveI hP2 : IsProbabilityMeasure
      (recordTrajT p hp0.le hp1.le hm1
        (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ)))) :=
    instIsProbabilityMeasure_recordTrajT p hp0.le hp1.le hm1 _
  refine M2WindowLaw.measure_eq_of_forall_window (β := RecState N m × ℕ) fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hconst : (M2WindowLaw.window (β := RecState N m × ℕ) 0)
        = (fun _ => (fun i : Fin 0 => i.elim0)) := by
      funext x i
      exact i.elim0
    rw [hconst, MeasureTheory.Measure.map_const, MeasureTheory.Measure.map_const,
      measure_univ, measure_univ, one_smul]
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    subst hr
    have hcomp : ((M2WindowLaw.window (β := RecState N m × ℕ) (r + 1))
          ∘ (arrPath (N := N) p m hm1))
        = (fun U : Array N => fun i : Fin (r + 1) =>
            (M2RecordFinite.actRecStateA p m hm1 U i, recTimeA p m U i)) := rfl
    rw [Measure.map_map (M2WindowLaw.measurable_window (r + 1)) (measurable_arrPath p m hm1),
      hcomp, M7Block.actual_blockPath_map hp0 hp1 hm1 hm hN r,
      M6Step.blockPathLaw_eq_recordTrajT_window p hp0.le hp1.le hm1
        (zeroState (N := N) (m := m) hm1) 0 r]
    rfl

/-! ### 3. The frequency step on the time-extended chain -/

/-- The natural filtration of the *time-extended* record path space: Mathlib's coordinate
filtration `piLE`, i.e. the exact σ-algebra that `condExp_indicator_succ` conditions on. -/
noncomputable def recordFiltT (N m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → RecState N m × ℕ)) :=
  MeasureTheory.Filtration.piLE (X := fun _ : ℕ => RecState N m × ℕ)

/-- Coordinate measurability for Mathlib's coordinate filtration, for an arbitrary fibre type. -/
theorem measurable_piLE_eval {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable[MeasureTheory.Filtration.piLE (X := fun _ : ℕ => X) n]
      (fun ω : ℕ → X => ω n) := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe, measurable_iff_comap_le]
  have hfun : (fun ω : ℕ → X => ω n)
      = (fun f : (i : ↥(Finset.Iic n)) → X => f ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        ∘ Preorder.frestrictLe (π := fun _ : ℕ => X) n := by
    funext ω
    rw [Function.comp_apply, Preorder.frestrictLe_apply]
  rw [hfun, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_pi_apply _))

/-- The `n`-th coordinate of the extended record path is measurable at time `n`. -/
theorem measurable_recordFiltT (N m n : ℕ) :
    Measurable[recordFiltT N m n] (fun ω : ℕ → RecState N m × ℕ => ω n) :=
  measurable_piLE_eval (X := RecState N m × ℕ) n

/-- The exhaustion set of the extended chain, written in the `dep` shape of the conditional
Borel–Cantelli engine. -/
def exhT (N m : ℕ) (K : ℕ) : Set (RecState N m × ℕ) := {z | z.1 ∈ exh N m K}

/-- The record defect of the extended chain. -/
noncomputable def dmaxT (z : RecState N m × ℕ) : ℕ := dmax z.1

/-- The `Prod.fst` preimage of `srSet` is the set used in the conditional expectation. -/
theorem preimage_fst_srSet :
    (Prod.fst ⁻¹' srSet N m : Set (RecState N m × ℕ)) = {z | z.1 ∈ srSet N m} := rfl

theorem exhT_eq_dmaxT_le (K : ℕ) : exhT N m K = {z : RecState N m × ℕ | dmaxT z ≤ K} := by
  ext z
  exact mem_exh_iff_dmax_le z.1 K

/-- **The one-step Markov identity of the time-extended stopped-record path law.**  It is the
`hstep` field of the conditional Borel–Cantelli engine at the genuine kernel `hitKKernelT`, proved
from `WCJF.OneStepBridge.condExp_indicator_succ` (the Ionescu–Tulcea construction) rather than
assumed. -/
theorem recordStepIdentityT_actual (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    ∀ n : ℕ, (recordTrajT p hp hp1 hm ν)[Set.indicator
        {ω : ℕ → RecState N m × ℕ | (ω (n + 1)).1 ∈ srSet N m} (fun _ => (1 : ℝ)) |
        recordFiltT N m n]
      =ᵐ[recordTrajT p hp hp1 hm ν]
        (fun ω => ((hitKKernelT (N := N) (m := m) p hm) (ω n)
          {z : RecState N m × ℕ | z.1 ∈ srSet N m}).toReal) := by
  letI : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT p hp hp1 hm
  intro n
  have h := WCJF.OneStepBridge.condExp_indicator_succ
    (X := RecState N m × ℕ) (hitKKernelT (N := N) (m := m) p hm) ν n
    ((measurableSet_srSet N m).preimage measurable_fst)
  simpa only [SimJump.RecKernel.recordTrajT, recordFiltT, WCJF.OneStepBridge.pathLaw,
    SimJump.RecKernel.homTraj, WCJF.OneStepBridge.constFam, SimJump.RecKernel.homFam,
    preimage_fst_srSet, Set.mem_ofPred_eq] using h

/-- **The frequency step of the time-extended stopped-record chain.**  From the literal paper
`dT` tightness of `recordTrajT` at any probability start law, almost surely infinitely many
record times have all walkers exactly at the record:

`∀ᵐ ω ∂recordTrajT …, ∃ᶠ n, (ω n).1 ∈ srSet N m`.

Every premise is either proved (one-step Markov, force, positivity of `(1-p)^{N(2K+1)}`,
exhaustion identity) or the stated `dT` tightness. -/
theorem ae_frequently_srSetT_of_dT_tight (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν),
      ∃ᶠ n in atTop, (ω n).1 ∈ srSet N m := by
  haveI hMK : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT p hp hp1 hm
  haveI hP : IsProbabilityMeasure (recordTrajT p hp hp1 hm ν) :=
    instIsProbabilityMeasure_recordTrajT p hp hp1 hm ν
  refine WCJF.RegenBC.ae_frequently_mem_of_kernel_force_of_tight
    (μ := recordTrajT p hp hp1 hm ν) (ℱ := recordFiltT N m)
    (Y := fun n (ω : ℕ → RecState N m × ℕ) => ω n)
    (F := {z : RecState N m × ℕ | z.1 ∈ srSet N m})
    (κ := hitKKernelT (N := N) (m := m) p hm)
    (Kset := exhT N m)
    (c := fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))))
    (dep := dmaxT)
    (fun n => measurable_recordFiltT N m n) ?_ ?_ ?_ ?_ ?_ ?_
  · exact (measurableSet_srSet N m).preimage measurable_fst
  · intro K z hz
    exact hitKKernelT_srSet_ge p hp hp1 hm hN K z hz
  · exact recordStepIdentityT_actual p hp hp1 hm ν
  · intro K
    exact WCJF.RegenBC.paper_constant_pos hp_lt N K
  · intro K
    exact exhT_eq_dmaxT_le (N := N) (m := m) K
  · intro ε hε
    obtain ⟨K, hK⟩ := htight ε hε
    refine ⟨K, fun r => ?_⟩
    have hset : {ω : ℕ → RecState N m × ℕ | ω r ∉ exhT N m K}
        = {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r} :=
      TightAvail.compl_exh_eq_dT_tail r K
    rw [hset]
    exact le_trans (measure_mono fun ω hω => by
      simp only [Set.mem_ofPred_eq] at hω ⊢
      omega) (hK r)

/-! ### 4. The array transfer -/

/-- **The R1 transfer to the literal actual array measure.**  From actual `dT` tightness of the
canonical stopped-record trajectory at the forced Dirac start (the exact output of
`AuditResidual.record_tightness_of_two_actual_blocks`), almost surely the actual array has
infinitely many record levels whose record state is a simultaneous record of all `N` walkers. -/
theorem ae_frequently_srSet_array_of_dT_tight (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N),
      ∃ᶠ r in atTop, M7Block.actRecStateT p m U (by omega : 1 ≤ m) r ∈ srSet N m := by
  let hm1 : 1 ≤ m := by omega
  have hN0 : 0 < N := by omega
  have hP : IsProbabilityMeasure
      (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ))) := ⟨by simp⟩
  have hT := ae_frequently_srSetT_of_dT_tight (N := N) (m := m) p hp0.le hp1.le hp1 hm1 hN0
    (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ))) htight
  rw [← array_fullLaw (N := N) (m := m) p hp0 hp1 hm hN] at hT
  have hmap := ae_of_ae_map (μ := arrayMeasure N)
    (f := arrPath (N := N) p m hm1) (measurable_arrPath p m hm1).aemeasurable hT
  filter_upwards [hmap] with U hU
  simpa only [arrPath_apply, actRecStateT_eq_actRecStateA] using hU

/-- **The same conclusion in the paper's own coordinates.**  Almost surely under the literal
array law, for infinitely many record levels `r` *every* walker sits exactly at the record level
`r` at the record time `τ_r`: the record state is a simultaneous record (`dmax = 0`), the paper's
defect `d_r = r - min_i X^i_{τ_r}` therefore vanishes, and nearest-neighbour geometry gives
`X^i_{τ_r} = r` for every walker `i`. -/
theorem ae_frequently_all_walkers_at_level (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ᶠ r in atTop,
      ∀ i : Fin N, RecordoSupply.actX p m U i (recTimeA p m U r) = (r : ℤ) := by
  let hm1 : 1 ≤ m := by omega
  filter_upwards [ae_frequently_srSet_array_of_dT_tight (N := N) (m := m) p hp0 hp1 hm hN htight,
    M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN] with U hfreq hreach
  refine Filter.Frequently.mono hfreq (fun r hr => ?_)
  have hstate : M4RecordGeom.actRecState p m U hm1 hreach r ∈ srSet N m := by
    rw [← M7Block.actRecStateT_of_reach (p := p) (m := m) (hm := hm1) hreach r]
    exact hr
  have hdmax : dmax (M4RecordGeom.actRecState p m U hm1 hreach r) = 0 :=
    (WCJF.RecFreq.dmax_eq_zero_iff_mem_srSet _).mpr hstate
  have hdef : RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r = 0 := by
    rw [M4RecordGeom.defect_eq_two_mul_dmax hm1 hreach r, hdmax]
    simp
  have hrun : RecordDefect.runMin (RecordoSupply.actX p m U) (recTimeA p m U r) = (r : ℤ) := by
    have h := hdef
    rw [RecordDefect.defect] at h
    linarith
  intro i
  have h1 : RecordDefect.runMin (RecordoSupply.actX p m U) (recTimeA p m U r)
      ≤ RecordoSupply.actX p m U i (recTimeA p m U r) :=
    RecordDefect.runMin_le (X := RecordoSupply.actX p m U) (recTimeA p m U r) i
  have h2 := M4RecordGeom.actX_le_level hreach r i
  linarith

/-- **The R1 transfer in the repository's residual-input form.**  From the two genuine block
clauses `AdvanceClause` (`hAdv`) and `HalfClause` (`hOff`) at the proved constants, with their
profile decay, almost surely the actual array has infinitely many simultaneous records.

The quantifier order is the repository's: `κ > 0` is produced by
`AuditResidual.record_tightness_of_two_actual_blocks` *before* the profiles and clauses are
quantified, so nothing is assumed about `κ`. -/
theorem ae_frequently_srSet_array_of_two_blocks {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      TightAvail.AdvanceClause (N := N) p m B κ p₁ →
      TightAvail.HalfClause (N := N) p m B κ p₂ →
      ∀ᵐ U ∂(arrayMeasure N),
        ∃ᶠ r in atTop, M7Block.actRecStateT p m U (by omega : 1 ≤ m) r ∈ srSet N m := by
  obtain ⟨κ, hκ, H⟩ :=
    AuditResidual.record_tightness_of_two_actual_blocks (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have h₁' := h₁
  have h₂' := h₂
  simp only [TightAvail.AdvanceClause] at h₁'
  simp only [TightAvail.HalfClause] at h₂'
  exact ae_frequently_srSet_array_of_dT_tight (N := N) (m := m) p hp0 hp1 hm hN
    (H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁' h₂')

/-- **The same conclusion from the iterate form of tightness** — the exact shape in which the
repository's stopped-record chain supplies tightness
(`SimJump.RecKernel.htight_iff_pathlaw`, `TightAvail.iterate_tight_iff_dT_tail`).  The start law is
the forced one, `δ_{zeroState}`, and `TightAvail.startLaw_fst` converts it to the Dirac start of
the time-extended chain. -/
theorem ae_frequently_all_walkers_at_level_of_iterate_tight (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htight : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      ((SwarmKB.step (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)))^[r]
        (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m))))
        (exh N m K)ᶜ ≤ ε) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ᶠ r in atTop,
      ∀ i : Fin N, RecordoSupply.actX p m U i (recTimeA p m U r) = (r : ℤ) := by
  let hm1 : 1 ≤ m := by omega
  have hdT : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
      (recordTrajT p hp0.le hp1.le hm1
        (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ))))
        {ω : ℕ → RecState N m × ℕ | K < dT ω u} ≤ ε := by
    haveI : IsProbabilityMeasure (TightAvail.startLaw (N := N) (m := m) hm1) :=
      TightAvail.isProbabilityMeasure_startLaw hm1
    have hiter : ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
        ((SwarmKB.step (hitKKernel (N := N) (m := m) p hm1))^[r]
          ((TightAvail.startLaw (N := N) (m := m) hm1).map Prod.fst))
          (exh N m K)ᶜ ≤ ε := by
      intro ε hε
      have h := htight ε hε
      rwa [← TightAvail.startLaw_fst hm1] at h
    have h := (TightAvail.iterate_tight_iff_dT_tail (N := N) (m := m) p hp0.le hp1.le hm1
      (TightAvail.startLaw (N := N) (m := m) hm1)).mp hiter
    simpa only [TightAvail.startLaw] using h
  exact ae_frequently_all_walkers_at_level (N := N) (m := m) p hp0 hp1 hm hN hdT

/-- **The paper-facing form of the two-block transfer.**  From the two genuine block clauses at the
proved constants, almost surely the actual array has infinitely many record levels at which *every*
walker is exactly at the record level. -/
theorem ae_frequently_all_walkers_at_level_of_two_blocks {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      TightAvail.AdvanceClause (N := N) p m B κ p₁ →
      TightAvail.HalfClause (N := N) p m B κ p₂ →
      ∀ᵐ U ∂(arrayMeasure N),
        ∃ᶠ r in atTop, ∀ i : Fin N, RecordoSupply.actX p m U i (recTimeA p m U r) = (r : ℤ) := by
  obtain ⟨κ, hκ, H⟩ :=
    AuditResidual.record_tightness_of_two_actual_blocks (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have h₁' := h₁
  have h₂' := h₂
  simp only [TightAvail.AdvanceClause] at h₁'
  simp only [TightAvail.HalfClause] at h₂'
  exact ae_frequently_all_walkers_at_level (N := N) (m := m) p hp0 hp1 hm hN
    (H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁' h₂')

/-- **Consistency with the accepted joint law identity.**  Projecting the new infinite-dimensional
identity `array_fullLaw` through the paper statistics `(dT, tauT)` and using the a.e. factor-two
identity `M2RecordFinite.ae_defect_toNat_eq_two_mul_dmax` recovers the already accepted
`M7Block.jointLawIdentity_actual`.  So `array_fullLaw` is a strictly stronger statement than the
accepted `(defect, record time)` law identity. -/
theorem jointLawIdentity_actual_of_fullLaw (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    SwarmRecordMeas.Bridge.JointLawIdentity (N := N) (m := m) p hp0.le hp1.le
      (by omega : 1 ≤ m)
      (Measure.dirac (zeroState (N := N) (m := m) (by omega : 1 ≤ m), (0 : ℕ))) := by
  let hm1 : 1 ≤ m := by omega
  have hstat : Measurable fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω) :=
    M2RecordFinite.measurable_dTtauT
  have hae : (fun U : Array N =>
        (((fun r => 2 * dmax (M7Block.actRecStateT p m U hm1 r)) : ℕ → ℕ), fun r => recTimeA p m U r))
      =ᵐ[arrayMeasure N] (fun U : Array N =>
        (((fun r => (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r)) := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr (fun r =>
      M2RecordFinite.ae_defect_toNat_eq_two_mul_dmax (N := N) (m := m) hp0 hp1 hm hN hm1 r)]
      with U hU
    have h1 : (fun r => 2 * dmax (M7Block.actRecStateT p m U hm1 r))
        = (fun r => (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r).toNat) :=
      funext fun r => (hU r).symm
    rw [h1]
  have hcomp : ((fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω))
        ∘ (arrPath (N := N) p m hm1))
      = (fun U : Array N =>
        (((fun r => 2 * dmax (M7Block.actRecStateT p m U hm1 r)) : ℕ → ℕ),
          fun r => recTimeA p m U r)) := rfl
  show (recordTrajT p hp0.le hp1.le hm1 (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ)))).map
      (fun ω => (dT ω, tauT ω))
    = (arrayMeasure N).map (fun U =>
        (((fun r => (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r))
  calc (recordTrajT p hp0.le hp1.le hm1
        (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ)))).map (fun ω => (dT ω, tauT ω))
      = ((arrayMeasure N).map (arrPath (N := N) p m hm1)).map (fun ω => (dT ω, tauT ω)) := by
        rw [array_fullLaw (N := N) (m := m) p hp0 hp1 hm hN]
    _ = (arrayMeasure N).map (((fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω))
          ∘ (arrPath (N := N) p m hm1))) :=
        Measure.map_map hstat (measurable_arrPath p m hm1)
    _ = (arrayMeasure N).map (fun U : Array N =>
          (((fun r => 2 * dmax (M7Block.actRecStateT p m U hm1 r)) : ℕ → ℕ),
            fun r => recTimeA p m U r)) := by rw [hcomp]
    _ = (arrayMeasure N).map (fun U : Array N =>
          (((fun r => (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
            fun r => recTimeA p m U r)) := Measure.map_congr hae

end WCJF.ActPath
