/-
# Finite-to-infinite record law: from finite window laws to `Bridge.JointLawIdentity`

`Bridge.JointLawIdentity` (in `Swarm/RecordLawBridge.lean`) is the exact remaining
probabilistic law input of the repaired stopped-record tightness interface: the law of the
`(defect, record time)` sequence under the Ionescu–Tulcea path law `recordTrajT p hp hp1 hm ν` of
the time-extended stopped record kernel `hitKKernelT` equals the law of the actual array's
canonical `(defect, record time)` sequence at `recTimeA`.

This file reduces that *infinite-dimensional* measure identity to countable families of
*finite-dimensional* statements, with the paper's factor two (`dT = 2 * dmax`) and the exact
quantifier order.

## Main results

* `actRecStateA p m hm U r` — the actual compact record state at level `r` as a **total**
  measurable function of the array (`zeroState` off `ReachAll`).  On `ReachAll` it is
  `M4RecordGeom.actRecState`.
* `measurable_actRecStatA` — its joint measurability with the record time in every finite window.
* `ae_defect_toNat_eq_two_mul_dmax` — on a full-measure event the paper's raw defect
  `(r - min_i X^i_{τ_r}).toNat` equals `2 * dmax (actRecStateA U r)` (`defect_eq_two_mul_dmax`).
* `FiniteRecLaw p hp hp1 hm ν n` — **the finite window law** of the actual compact record
  state and record time, of length `n`.  This is the exact finite-dimensional input taken as a
  hypothesis here (not proved here, and not pretended to be).
* `FiniteStatLaw p hp hp1 hm ν n` — the same window for the paper's `(dT, tauT)` statistics.
* `jointLawIdentity_of_finiteRecLaw` — `(∀ n, FiniteRecLaw … n) → JointLawIdentity …`.
* `jointLawIdentity_iff_finiteStatLaw` — `JointLawIdentity … ↔ ∀ n, FiniteStatLaw … n`: the
  infinite identity carries exactly the countable family of finite `(defect, time)` laws, so
  nothing is lost or silently added by the finite reformulation.
* `finiteRecLaw_one_iff` — the level-`1` window law holds **iff** the start law `ν` is the Dirac
  measure at `(zeroState, 0)`.  So the compatible start law is *forced* by the level-`0`
  statistics: no arbitrary start law can be used, and the forced one is the Dirac at the
  all-at-the-record state (the start law of `M5FirstBlock.first_iterate_law`).

Nothing here proves `FiniteRecLaw` for `n ≥ 2`; that is the successive-shifted-block law
(direction 1).  No `Ballistic`, `MainClaim`, `(diam)`, or invariant record measure is claimed.
-/
import Swarm.M2WindowLaw
import Swarm.RecordLawBridge
import Swarm.ActualRecordGeometry

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace M2RecordFinite

open Swarming Swarming.Uniform SwarmRec RecordDefect RecordoSupply SimJump SimJump.RecKernel
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw SwarmRecordMeas.Bridge

variable {N m : ℕ} [Nonempty (Fin N)]

/-! ### The totalised actual compact record state -/

/-- **The actual compact record state at level `r`, as a total function of the array.**
Off `ReachAll` (a null set) it is the all-at-the-record state; on `ReachAll` it is
`M4RecordGeom.actRecState`. -/
noncomputable def actRecStateA (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (U : Array N) (r : ℕ) :
    RecState N m :=
  if h : U ∈ ReachAll p m then M4RecordGeom.actRecState p m U hm h r else zeroState hm

theorem actRecStateA_of_mem {p : ℝ} {hm : 1 ≤ m} {U : Array N} {r : ℕ}
    (hU : U ∈ ReachAll p m) :
    actRecStateA p m hm U r = M4RecordGeom.actRecState p m U hm hU r := by
  simp only [actRecStateA, dif_pos hU]

theorem actRecStateA_val {p : ℝ} {hm : 1 ≤ m} (U : Array N) (r : ℕ) :
    (actRecStateA p m hm U r).val
      = if _h : U ∈ ReachAll p m then M4RecordGeom.actRecAmb p m U r else (zeroState hm).val := by
  by_cases hU : U ∈ ReachAll p m
  · rw [actRecStateA_of_mem (hm := hm) hU, dif_pos hU]
    rfl
  · rw [actRecStateA, dif_neg hU, dif_neg hU]

/-- **The level-`0` actual record state is the all-at-the-record state, pointwise.** -/
theorem actRecStateA_zero {p : ℝ} {hm : 1 ≤ m} (U : Array N) :
    actRecStateA p m hm U 0 = zeroState hm := by
  by_cases hU : U ∈ ReachAll p m
  · rw [actRecStateA_of_mem (hm := hm) hU, M4RecordGeom.actRecState_zero]
  · rw [actRecStateA, dif_neg hU]

/-- **Measurability of the totalised actual record state** in the array. -/
theorem measurable_actRecStateA (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (r : ℕ) :
    Measurable fun U : Array N => actRecStateA p m hm U r := by
  have hval : Measurable fun U : Array N => (actRecStateA p m hm U r).val := by
    have h : (fun U : Array N => (actRecStateA p m hm U r).val)
        = fun U => if h : U ∈ ReachAll p m then M4RecordGeom.actRecAmb p m U r
            else (zeroState hm).val := by
      funext U
      exact actRecStateA_val U r
    rw [h]
    exact Measurable.ite (measurableSet_reachAll (N := N) p m)
      (M4RecordGeom.measurable_actRecAmb p m r) measurable_const
  have := Measurable.subtype_mk (p := fun a : Amb N m => a ∈ recSet N m)
    (f := fun U : Array N => (actRecStateA p m hm U r).val) hval
    (h := fun U => (actRecStateA p m hm U r).2)
  simpa only [Subtype.mk_eq_mk] using this

/-- **Measurability of the finite window record statistic** `r ↦ (record state, record time)`. -/
theorem measurable_actRecStatA (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Measurable fun U : Array N => fun r : Fin n =>
      (actRecStateA p m hm U r, recTimeA p m U r) :=
  measurable_pi_lambda (X := fun _ : Fin n => RecState N m × ℕ)
    (fun U r => (actRecStateA p m hm U r, recTimeA p m U r))
    fun r => (measurable_actRecStateA p m hm r).prodMk (measurable_recTimeA p m r)

/-! ### The paper's raw defect is twice the compact `dmax`, almost surely -/

/-- **The factor-two identity on the actual array.**  `dT` is defined as `2 * dmax` of the compact
record state, and on a full-measure event the paper's raw defect `r - min_i X^i_{τ_r}` agrees
with it.  This is `M4RecordGeom.defect_eq_two_mul_dmax` plus almost-sure `ReachAll`. -/
theorem ae_defect_toNat_eq_two_mul_dmax {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (hm1 : 1 ≤ m) (r : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      (defect (actX p m U) (recTimeA p m U) r).toNat = 2 * dmax (actRecStateA p m hm1 U r) := by
  filter_upwards [M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN] with U hU
  rw [actRecStateA_of_mem (hm := hm1) hU, M4RecordGeom.defect_eq_two_mul_dmax hm1 hU r]
  have hcast : (2 : ℤ) * (dmax (M4RecordGeom.actRecState p m U hm1 hU r) : ℤ)
      = ((2 * dmax (M4RecordGeom.actRecState p m U hm1 hU r) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast, Int.toNat_natCast]

/-- **Almost-sure equality of the two window statistics.**  The array-side raw `(defect, time)`
window is almost everywhere the `(2 * dmax, time)` window of the compact record state. -/
theorem ae_window_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hm1 : 1 ≤ m) (n : ℕ) :
    (fun U : Array N => fun r : Fin n => (2 * dmax (actRecStateA p m hm1 U r), recTimeA p m U r))
      =ᵐ[arrayMeasure N]
    (fun U : Array N => fun r : Fin n =>
      ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)) := by
  have hpt : ∀ᵐ U ∂(arrayMeasure N), ∀ r : Fin n,
      (2 * dmax (actRecStateA p m hm1 U r), recTimeA p m U r)
        = ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r) := by
    refine Filter.eventually_all.mpr fun r => ?_
    filter_upwards [ae_defect_toNat_eq_two_mul_dmax hp0 hp1 hm hN hm1 (r : ℕ)] with U hU
    rw [hU]
  filter_upwards [hpt] with U hU
  funext r
  exact hU r

/-! ### The finite window laws -/

/-- **The finite window law of the actual record state and record time.**  The law of the first
`n` coordinates of the stopped-record path law is the law of the actual array's
`(compact record state, record time)` window.  This is the exact finite-dimensional input; it is
*not* proved here for `n ≥ 2`. -/
def FiniteRecLaw (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) (n : ℕ) : Prop :=
  (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r)
    = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
        (actRecStateA p m hm U r, recTimeA p m U r))

/-- **The finite window law of the paper's `(defect, record time)` statistics.** -/
def FiniteStatLaw (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) (n : ℕ) : Prop :=
  (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n =>
      (dT ω r, tauT ω r))
    = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))

/-- The `(dT, tauT)` window as a function of the record-state window. -/
noncomputable def statWin (n : ℕ) (f : Fin n → RecState N m × ℕ) : Fin n → ℕ × ℕ :=
  fun r => (2 * dmax (f r).1, (f r).2)

theorem measurable_statWin (n : ℕ) : Measurable (statWin (N := N) (m := m) n) :=
  measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
    (fun (f : Fin n → RecState N m × ℕ) (r : Fin n) => (2 * dmax (f r).1, (f r).2)) fun r =>
    (((measurable_dmax.comp measurable_fst).comp (measurable_pi_apply r)).const_mul 2).prodMk
      (measurable_snd.comp (measurable_pi_apply r))

theorem statWin_comp_window (n : ℕ) :
    statWin (N := N) (m := m) n ∘ (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r)
      = fun ω => fun r : Fin n => (dT ω r, tauT ω r) := by
  funext ω r
  rfl

/-- **The state window law implies the statistic window law.**  Uses the factor-two identity
`dT = 2 * dmax` and the almost-sure defect identity. -/
theorem finiteStatLaw_of_finiteRecLaw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)}
    [IsProbabilityMeasure ν] {n : ℕ}
    (h : FiniteRecLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n) :
    FiniteStatLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n := by
  have hwin : Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r :=
    M2WindowLaw.measurable_window n
  have hstat : Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => (dT ω r, tauT ω r) :=
    measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
      (fun ω r => (dT ω r, tauT ω r)) fun r =>
      (measurable_dT_eval r).prodMk (measurable_tauT_eval r)
  calc (recordTrajT p hp0.le hp1.le hm1 ν).map (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n =>
        (dT ω r, tauT ω r))
      = (recordTrajT p hp0.le hp1.le hm1 ν).map
          (statWin (N := N) (m := m) n ∘ fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r) := by
        rw [statWin_comp_window]
    _ = ((recordTrajT p hp0.le hp1.le hm1 ν).map
          (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r)).map
          (statWin (N := N) (m := m) n) :=
        (Measure.map_map (measurable_statWin n) hwin).symm
    _ = ((arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
          (actRecStateA p m hm1 U r, recTimeA p m U r))).map (statWin (N := N) (m := m) n) := by
        rw [h]
    _ = (arrayMeasure N).map ((statWin (N := N) (m := m) n) ∘ fun U : Array N => fun r : Fin n =>
          (actRecStateA p m hm1 U r, recTimeA p m U r)) :=
        Measure.map_map (measurable_statWin n) (measurable_actRecStatA p m hm1 n)
    _ = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)) :=
        Measure.map_congr (ae_window_eq hp0 hp1 hm hN hm1 n)

/-! ### From finite windows to the joint law identity -/

/-- The joint `(dT, tauT)` statistic of the stopped-record path law. -/
theorem measurable_dTtauT :
    Measurable fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω) :=
  measurable_dT.prodMk measurable_tauT

/-- The joint `(defect, record time)` statistic of the actual array. -/
theorem measurable_arrayStat (p : ℝ) (m : ℕ) :
    Measurable fun U : Array N => (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
      fun r => recTimeA p m U r) :=
  measurable_recordStat p m

/-- **The main transfer.**  If every finite window of the stopped-record path law matches the
corresponding finite window of the actual record statistics, then the infinite-dimensional
`(defect, record time)` law identity `Bridge.JointLawIdentity` holds.

The proof is the π-system/cylinder uniqueness of `M2WindowLaw.measure_eq_of_forall_window_prod`:
windows of length `n` determine a probability law on `(ℕ → ℕ) × (ℕ → ℕ)`.  Both sides are
pushforwards of probability measures, so no σ-finiteness or integrability input is needed. -/
theorem jointLawIdentity_of_finiteStatLaw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)} [IsProbabilityMeasure ν]
    (h : ∀ n, FiniteStatLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n) :
    JointLawIdentity (N := N) (m := m) p hp0.le hp1.le hm1 ν := by
  haveI : IsProbabilityMeasure (recordTrajT p hp0.le hp1.le hm1 ν) :=
    instIsProbabilityMeasure_recordTrajT p hp0.le hp1.le hm1 ν
  haveI hP1 : IsProbabilityMeasure
      ((recordTrajT p hp0.le hp1.le hm1 ν).map (fun ω => (dT ω, tauT ω))) :=
    Measure.isProbabilityMeasure_map measurable_dTtauT.aemeasurable
  haveI hP2 : IsProbabilityMeasure
      ((arrayMeasure N).map (fun U : Array N =>
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r))) :=
    Measure.isProbabilityMeasure_map (measurable_arrayStat p m).aemeasurable
  show (recordTrajT p hp0.le hp1.le hm1 ν).map (fun ω => (dT ω, tauT ω))
    = (arrayMeasure N).map (fun U : Array N =>
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r))
  refine M2WindowLaw.measure_eq_of_forall_window_prod (α := ℕ) (β := ℕ) fun n => ?_
  have hproj : Measurable fun p : (ℕ → ℕ) × (ℕ → ℕ) => fun r : Fin n => (p.1 r, p.2 r) :=
    measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
      (fun (p : (ℕ → ℕ) × (ℕ → ℕ)) (r : Fin n) => (p.1 r, p.2 r)) fun r =>
      ((measurable_pi_apply (X := fun _ : ℕ => ℕ) (r : ℕ)).comp measurable_fst).prodMk
        ((measurable_pi_apply (X := fun _ : ℕ => ℕ) (r : ℕ)).comp measurable_snd)
  rw [Measure.map_map hproj measurable_dTtauT,
    Measure.map_map hproj (measurable_arrayStat p m)]
  exact h n

/-- **The finite formulations are not a weakening.**  The infinite law identity is equivalent to
the countable family of finite `(defect, record time)` window laws. -/
theorem jointLawIdentity_iff_finiteStatLaw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)} [IsProbabilityMeasure ν] :
    JointLawIdentity (N := N) (m := m) p hp0.le hp1.le hm1 ν
      ↔ ∀ n, FiniteStatLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n := by
  constructor
  · intro hlaw n
    have hproj : Measurable fun p : (ℕ → ℕ) × (ℕ → ℕ) => fun r : Fin n => (p.1 r, p.2 r) :=
      measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
        (fun (p : (ℕ → ℕ) × (ℕ → ℕ)) (r : Fin n) => (p.1 r, p.2 r)) fun r =>
        ((measurable_pi_apply (X := fun _ : ℕ => ℕ) (r : ℕ)).comp measurable_fst).prodMk
          ((measurable_pi_apply (X := fun _ : ℕ => ℕ) (r : ℕ)).comp measurable_snd)
    have h1 : (recordTrajT p hp0.le hp1.le hm1 ν).map
        (fun ω => fun r : Fin n => (dT ω r, tauT ω r))
        = ((recordTrajT p hp0.le hp1.le hm1 ν).map (fun ω => (dT ω, tauT ω))).map
            (fun p : (ℕ → ℕ) × (ℕ → ℕ) => fun r : Fin n => (p.1 r, p.2 r)) := by
      rw [Measure.map_map hproj measurable_dTtauT]
      rfl
    have h2 : (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))
        = ((arrayMeasure N).map (fun U : Array N =>
            (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
              fun r => recTimeA p m U r))).map
          (fun p : (ℕ → ℕ) × (ℕ → ℕ) => fun r : Fin n => (p.1 r, p.2 r)) := by
      rw [Measure.map_map hproj (measurable_arrayStat p m)]
      rfl
    rw [FiniteStatLaw, h1, h2, hlaw]
  · exact jointLawIdentity_of_finiteStatLaw hp0 hp1 hm1

/-- **The main transfer from the record-state windows**: finite record-state/time window laws for
every `n` give the joint law identity.  This is the form a successive-record-block law supplies. -/
theorem jointLawIdentity_of_finiteRecLaw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)}
    [IsProbabilityMeasure ν]
    (h : ∀ n, FiniteRecLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n) :
    JointLawIdentity (N := N) (m := m) p hp0.le hp1.le hm1 ν :=
  jointLawIdentity_of_finiteStatLaw hp0 hp1 hm1 fun n =>
    finiteStatLaw_of_finiteRecLaw hp0 hp1 hm hN hm1 (h n)

/-! ### The start law is forced: level `1` -/

/-- The level-`1` array window statistic is pointwise `(zeroState, 0)`. -/
theorem actRecStatA_one_apply (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (U : Array N) :
    (fun r : Fin 1 => (actRecStateA p m hm U r, recTimeA p m U r)) = fun _ => (zeroState hm, 0) := by
  funext r
  have hr : (r : ℕ) = 0 := by
    have := r.isLt
    omega
  rw [show (r : ℕ) = 0 from hr, actRecStateA_zero, recTimeA_zero]

/-- **The finite window law of length `1` holds if and only if the start law is the Dirac measure
at the all-at-the-record state at time zero.**

Consequently no arbitrary start law `ν` can be fed to `JointLawIdentity`: the level-`0` statistics
of the array are pointwise `(zeroState, 0)`, and this pins `ν` down exactly.  Conversely this
Dirac start law is the one used by `M5FirstBlock.first_iterate_law`, so it is non-vacuous. -/
theorem finiteRecLaw_one_iff {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    FiniteRecLaw (N := N) (m := m) p hp hp1 hm ν 1 ↔
      ν = Measure.dirac (zeroState hm, (0 : ℕ)) := by
  have hev : Measurable fun f : Fin 1 → RecState N m × ℕ => f 0 := measurable_pi_apply 0
  have hwin : Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => ω r :=
    M2WindowLaw.measurable_window 1
  have hstat : Measurable fun U : Array N => fun r : Fin 1 =>
      (actRecStateA p m hm U r, recTimeA p m U r) := measurable_actRecStatA p m hm 1
  have hconst2 : (fun U : Array N => fun r : Fin 1 =>
      (actRecStateA p m hm U r, recTimeA p m U r))
      = fun _ => fun _ : Fin 1 => (zeroState hm, (0 : ℕ)) := by
    funext U
    exact actRecStatA_one_apply p m hm U
  have hev0 : Measurable fun ω : ℕ → RecState N m × ℕ => ω 0 := measurable_pi_apply 0
  have hdirac : Measurable fun z : RecState N m × ℕ => fun _ : Fin 1 => z :=
    measurable_pi_lambda (X := fun _ : Fin 1 => RecState N m × ℕ) (fun z _ => z)
      fun _ => measurable_id
  have hcomp : (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => ω r)
      = (fun z : RecState N m × ℕ => fun _ : Fin 1 => z) ∘ (fun ω => ω 0) := by
    funext ω r
    rw [Function.comp_apply, show r = (0 : Fin 1) from Subsingleton.elim r 0]
    rfl
  -- the single-coordinate image of the left-hand window law is the start law
  have hleft : ((recordTrajT p hp hp1 hm ν).map
        (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => ω r)).map
        (fun f : Fin 1 → RecState N m × ℕ => f 0) = ν := by
    rw [Measure.map_map hev hwin]
    have hc : ((fun f : Fin 1 → RecState N m × ℕ => f 0) ∘
        fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => ω r) = fun ω => ω 0 := rfl
    rw [hc, recordTrajT_eval p hp hp1 hm ν 0, Function.iterate_zero_apply]
  -- and that of the right-hand window law is the Dirac at the all-at-the-record state
  have hright : ((arrayMeasure N).map (fun U : Array N => fun r : Fin 1 =>
        (actRecStateA p m hm U r, recTimeA p m U r))).map
        (fun f : Fin 1 → RecState N m × ℕ => f 0)
      = Measure.dirac (zeroState hm, (0 : ℕ)) := by
    rw [Measure.map_map hev hstat]
    have hc : ((fun f : Fin 1 → RecState N m × ℕ => f 0) ∘
        (fun U : Array N => fun r : Fin 1 => (actRecStateA p m hm U r, recTimeA p m U r)))
        = fun _ => (zeroState hm, (0 : ℕ)) := by
      funext U
      exact congrFun (actRecStatA_one_apply p m hm U) 0
    rw [hc, Measure.map_const, measure_univ, one_smul]
  -- the right-hand window law is the constant-window Dirac
  have hRHS : (arrayMeasure N).map (fun U : Array N => fun r : Fin 1 =>
        (actRecStateA p m hm U r, recTimeA p m U r))
      = Measure.dirac (fun _ : Fin 1 => (zeroState hm, (0 : ℕ))) := by
    rw [hconst2, Measure.map_const, measure_univ, one_smul]
  constructor
  · intro h
    have h' := congrArg (fun ρ => ρ.map (fun f : Fin 1 → RecState N m × ℕ => f 0)) h
    simpa only [hleft, hright] using h'
  · intro hν
    have hLHS : (recordTrajT p hp hp1 hm ν).map
          (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => ω r)
        = Measure.dirac (fun _ : Fin 1 => (zeroState hm, (0 : ℕ))) := by
      rw [hcomp, ← Measure.map_map hdirac hev0, recordTrajT_eval p hp hp1 hm ν 0,
        Function.iterate_zero_apply, hν, Measure.map_dirac]
    rw [FiniteRecLaw, hLHS, hRHS]

/-! ### The remaining content starts at two records

Windows are monotone in the length of the window: the law of a longer window determines the law of
every shorter one by projection.  Consequently, once the start law is the forced Dirac measure,
the levels `0` and `1` of `FiniteRecLaw` are automatic and the remaining obligations are exactly
`FiniteRecLaw n` for `n ≥ 2`, i.e. the law of successive *shifted blocks*. -/

/-- **Monotonicity of the finite window laws in the window length.** -/
theorem FiniteRecLaw.of_le {p : ℝ} {hp : 1 / 2 ≤ p} {hp1 : p ≤ 1} {hm : 1 ≤ m}
    {ν : Measure (RecState N m × ℕ)} {n n' : ℕ}
    (h : FiniteRecLaw (N := N) (m := m) p hp hp1 hm ν n') (hn : n ≤ n') :
    FiniteRecLaw (N := N) (m := m) p hp hp1 hm ν n := by
  have hproj : Measurable fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r) :=
    measurable_pi_lambda (X := fun _ : Fin n => RecState N m × ℕ)
      (fun (f : Fin n' → RecState N m × ℕ) (r : Fin n) => f (Fin.castLE hn r))
      fun r => measurable_pi_apply (Fin.castLE hn r)
  have hwin : Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => ω r :=
    M2WindowLaw.measurable_window n'
  have hstat : Measurable fun U : Array N => fun r : Fin n' =>
      (actRecStateA p m hm U r, recTimeA p m U r) := measurable_actRecStatA p m hm n'
  have hc1 : ((fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
      (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => ω r))
      = fun ω => fun r : Fin n => ω r := by
    funext ω r
    rfl
  have hc2 : ((fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
      (fun U : Array N => fun r : Fin n' =>
        (actRecStateA p m hm U r, recTimeA p m U r)))
      = fun U : Array N => fun r : Fin n =>
        (actRecStateA p m hm U r, recTimeA p m U r) := by
    funext U r
    rfl
  rw [FiniteRecLaw] at h ⊢
  calc (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => ω r)
      = (recordTrajT p hp hp1 hm ν).map
          ((fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
            fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => ω r) := by
        rw [hc1]
    _ = ((recordTrajT p hp hp1 hm ν).map
          (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => ω r)).map
          (fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) :=
        (Measure.map_map hproj hwin).symm
    _ = ((arrayMeasure N).map (fun U : Array N => fun r : Fin n' =>
          (actRecStateA p m hm U r, recTimeA p m U r))).map
          (fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) := by
        rw [h]
    _ = (arrayMeasure N).map
          ((fun f : Fin n' → RecState N m × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
            fun U : Array N => fun r : Fin n' =>
              (actRecStateA p m hm U r, recTimeA p m U r)) :=
        Measure.map_map hproj hstat
    _ = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
          (actRecStateA p m hm U r, recTimeA p m U r)) := by
        rw [hc2]

/-- **The exact remaining input.**  The joint law identity follows from the finite record-state
window laws of length `n ≥ 2` alone: shorter windows are projections of the length-`2` window
(`FiniteRecLaw.of_le`).  No start-law hypothesis is needed, because the length-`2` hypothesis
already forces `ν` to be the Dirac at `(zeroState, 0)` (`eq_dirac_of_finiteRecLaw_ge_two`). -/
theorem jointLawIdentity_of_finiteRecLaw_ge_two {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)}
    [IsProbabilityMeasure ν]
    (h : ∀ n, 2 ≤ n → FiniteRecLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n) :
    JointLawIdentity (N := N) (m := m) p hp0.le hp1.le hm1 ν := by
  refine jointLawIdentity_of_finiteRecLaw hp0 hp1 hm hN hm1 fun n => ?_
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact (h 2 le_rfl).of_le (by omega)
  · exact h n hn

/-- **The length-`2` windows force the start law.**  A family of matching record-state windows of
length `≥ 2` exists only for the Dirac start law at the all-at-the-record state, so the hypothesis
of `jointLawIdentity_of_finiteRecLaw_ge_two` is not satisfiable by an arbitrary start law. -/
theorem eq_dirac_of_finiteRecLaw_ge_two {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    {ν : Measure (RecState N m × ℕ)} [IsProbabilityMeasure ν]
    (h : ∀ n, 2 ≤ n → FiniteRecLaw (N := N) (m := m) p hp hp1 hm ν n) :
    ν = Measure.dirac (zeroState hm, (0 : ℕ)) :=
  (finiteRecLaw_one_iff hp hp1 hm ν).1 ((h 2 le_rfl).of_le (by omega))

/-! ### Interface with the integrated `hterm` transfer

`SwarmRecordMeas.Bridge.hterm_pathlaw_of_array_canonical` is the repaired tightness input
`hterm` of `SwarmM4.PCtxR`, with the array-side record statistics already discharged.  Its only
residual inputs are the ballistic lower bound, `(diam)`, and `JointLawIdentity`.  Composing it with
the transfer above replaces the infinite-dimensional law identity by the finite record-state
windows of length `≥ 2`. -/

/-- **`hterm` from the finite record-state windows and `(diam)`.**  Residual hypotheses, exactly:
the one-walker ballistic lower bound with constant `κ` (a theorem for the actual array,
`RecordoSupply.speed_actual`), the diameter estimate `(diam)`, and `FiniteRecLaw n` for `n ≥ 2`.
No start-law hypothesis appears: it is forced by the finite windows. -/
theorem hterm_pathlaw_of_finiteRecLaw_ge_two {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (hdiam : ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (h : ∀ n, 2 ≤ n → FiniteRecLaw (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) ν n) :
    ∀ r L : ℕ, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
      GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
        (2 ^ j * L) :=
  hterm_pathlaw_of_array_canonical hp0 hp1 hm hN B hB hκ hspeed hdiam ν
    (jointLawIdentity_of_finiteRecLaw_ge_two hp0 hp1 hm hN (by omega : 1 ≤ m) h)


/-! ### Statistic-level form: defect-only finite window laws

The same reduction is available for a consumer that can only produce the paper's
`(defect, record time)` laws (rather than the full compact record-state laws).  The level-`1`
statistic law is characterised by the forced start law, and statistic windows are monotone in
length, so the family `FiniteStatLaw … n` for `n ≥ 2` is again exactly the remaining input. -/

theorem arrayStatA_zero (p : ℝ) (m : ℕ) (U : Array N) :
    ((defect (actX p m U) (recTimeA p m U) 0).toNat, recTimeA p m U 0) = ((0 : ℕ), (0 : ℕ)) := by
  rw [defectA_zero, recTimeA_zero]
  rfl

theorem measurable_statWinPath (n : ℕ) :
    Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => (dT ω r, tauT ω r) :=
  measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
    (fun ω r => (dT ω r, tauT ω r)) fun r =>
    (measurable_dT_eval r).prodMk (measurable_tauT_eval r)

theorem measurable_arrayStatWin (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable fun U : Array N => fun r : Fin n =>
      ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r) := by
  have hstat : Measurable fun U : Array N =>
      (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
        fun r => recTimeA p m U r) := measurable_arrayStat p m
  have h := (M2WindowLaw.measurable_window (β := ℕ × ℕ) n).comp
    ((M2WindowLaw.measurable_prodPiEquiv (α := ℕ) (β := ℕ)).comp hstat)
  have hfun : (M2WindowLaw.window (β := ℕ × ℕ) n) ∘
      (⇑(M2WindowLaw.prodPiEquiv (α := ℕ) (β := ℕ))) ∘ (fun U : Array N =>
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r))
      = fun (U : Array N) (r : Fin n) =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r) := by
    funext U r
    rfl
  rw [← hfun]
  exact h

theorem finiteStatLaw_one_iff {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    FiniteStatLaw (N := N) (m := m) p hp hp1 hm ν 1 ↔
      ν.map (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2))
        = Measure.dirac ((0 : ℕ), (0 : ℕ)) := by
  have hev : Measurable fun f : Fin 1 → ℕ × ℕ => f 0 := measurable_pi_apply 0
  have hwin1 := measurable_statWinPath (N := N) (m := m) 1
  have harr1 := measurable_arrayStatWin (N := N) p m 1
  have hpair : Measurable fun z : RecState N m × ℕ => (2 * dmax z.1, z.2) :=
    ((measurable_dmax.comp measurable_fst).const_mul 2).prodMk measurable_snd
  have hev0 : Measurable fun ω : ℕ → RecState N m × ℕ => ω 0 := measurable_pi_apply 0
  have hdirac1 : Measurable fun z : ℕ × ℕ => fun _ : Fin 1 => z :=
    measurable_pi_lambda (X := fun _ : Fin 1 => ℕ × ℕ) (fun z _ => z) fun _ => measurable_id
  have hleft : ((recordTrajT p hp hp1 hm ν).map
      (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => (dT ω r, tauT ω r))).map
      (fun f : Fin 1 → ℕ × ℕ => f 0) = ν.map (fun z => (2 * dmax z.1, z.2)) := by
    rw [Measure.map_map hev hwin1]
    have hc : ((fun f : Fin 1 → ℕ × ℕ => f 0) ∘
        fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => (dT ω r, tauT ω r))
        = (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) ∘ (fun ω => ω 0) := by
      funext ω
      rfl
    rw [hc, ← Measure.map_map hpair hev0, recordTrajT_eval p hp hp1 hm ν 0,
      Function.iterate_zero_apply]
  have hright : ((arrayMeasure N).map (fun U : Array N => fun r : Fin 1 =>
      ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))).map
      (fun f : Fin 1 → ℕ × ℕ => f 0) = Measure.dirac ((0 : ℕ), (0 : ℕ)) := by
    rw [Measure.map_map hev harr1]
    have hc : ((fun f : Fin 1 → ℕ × ℕ => f 0) ∘ (fun U : Array N => fun r : Fin 1 =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)))
        = fun _ => ((0 : ℕ), (0 : ℕ)) := by
      funext U
      exact arrayStatA_zero p m U
    rw [hc, Measure.map_const, measure_univ, one_smul]
  constructor
  · intro h
    have h' := congrArg (fun ρ => ρ.map (fun f : Fin 1 → ℕ × ℕ => f 0)) h
    simpa only [hleft, hright] using h'
  · intro hν
    have hconst2 : (fun U : Array N => fun r : Fin 1 =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))
        = fun _ => fun _ : Fin 1 => ((0 : ℕ), (0 : ℕ)) := by
      funext U r
      rw [show r = (0 : Fin 1) from Subsingleton.elim r 0]
      exact arrayStatA_zero p m U
    have hRHS : (arrayMeasure N).map (fun U : Array N => fun r : Fin 1 =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))
        = Measure.dirac (fun _ : Fin 1 => ((0 : ℕ), (0 : ℕ))) := by
      rw [hconst2, Measure.map_const, measure_univ, one_smul]
    have hcomp : (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => (dT ω r, tauT ω r))
        = (fun z : ℕ × ℕ => fun _ : Fin 1 => z) ∘
            (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) ∘ (fun ω => ω 0) := by
      funext ω r
      rw [Function.comp_apply, Function.comp_apply,
        show r = (0 : Fin 1) from Subsingleton.elim r 0]
      rfl
    have hLHS : (recordTrajT p hp hp1 hm ν).map
        (fun ω : ℕ → RecState N m × ℕ => fun r : Fin 1 => (dT ω r, tauT ω r))
        = Measure.dirac (fun _ : Fin 1 => ((0 : ℕ), (0 : ℕ))) := by
      rw [hcomp, ← Measure.map_map hdirac1 (hpair.comp hev0), ← Measure.map_map hpair hev0,
        recordTrajT_eval p hp hp1 hm ν 0, Function.iterate_zero_apply, hν, Measure.map_dirac]
    exact hLHS.trans hRHS.symm


theorem FiniteStatLaw.of_le {p : ℝ} {hp : 1 / 2 ≤ p} {hp1 : p ≤ 1} {hm : 1 ≤ m}
    {ν : Measure (RecState N m × ℕ)} {n n' : ℕ}
    (h : FiniteStatLaw (N := N) (m := m) p hp hp1 hm ν n') (hn : n ≤ n') :
    FiniteStatLaw (N := N) (m := m) p hp hp1 hm ν n := by
  have hproj : Measurable fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r) :=
    measurable_pi_lambda (X := fun _ : Fin n => ℕ × ℕ)
      (fun (f : Fin n' → ℕ × ℕ) (r : Fin n) => f (Fin.castLE hn r))
      fun r => measurable_pi_apply (X := fun _ : Fin n' => ℕ × ℕ) (Fin.castLE hn r)
  have hpath : Measurable fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => (dT ω r, tauT ω r) :=
    measurable_statWinPath n'
  have harr : Measurable fun U : Array N => fun r : Fin n' =>
      ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r) :=
    measurable_arrayStatWin p m n'
  have hc1 : ((fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
      (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => (dT ω r, tauT ω r)))
      = fun ω => fun r : Fin n => (dT ω r, tauT ω r) := by
    funext ω r
    rfl
  have hc2 : ((fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
      (fun U : Array N => fun r : Fin n' =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)))
      = fun U : Array N => fun r : Fin n =>
        ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r) := by
    funext U r
    rfl
  have h' : (recordTrajT p hp hp1 hm ν).map
      (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => (dT ω r, tauT ω r))
      = (arrayMeasure N).map (fun U : Array N => fun r : Fin n' =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)) := h
  show (recordTrajT p hp hp1 hm ν).map
      (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => (dT ω r, tauT ω r))
      = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))
  calc (recordTrajT p hp hp1 hm ν).map
        (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n => (dT ω r, tauT ω r))
      = (recordTrajT p hp hp1 hm ν).map
          ((fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
            fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => (dT ω r, tauT ω r)) := by
        rw [hc1]
    _ = ((recordTrajT p hp hp1 hm ν).map
          (fun ω : ℕ → RecState N m × ℕ => fun r : Fin n' => (dT ω r, tauT ω r))).map
          (fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) :=
        (Measure.map_map hproj hpath).symm
    _ = ((arrayMeasure N).map (fun U : Array N => fun r : Fin n' =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r))).map
          (fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) := by
        rw [h']
    _ = (arrayMeasure N).map
          ((fun f : Fin n' → ℕ × ℕ => fun r : Fin n => f (Fin.castLE hn r)) ∘
            fun U : Array N => fun r : Fin n' =>
              ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)) :=
        Measure.map_map hproj harr
    _ = (arrayMeasure N).map (fun U : Array N => fun r : Fin n =>
          ((defect (actX p m U) (recTimeA p m U) r).toNat, recTimeA p m U r)) := by
        rw [hc2]

/-- **The statistic-level exact remaining input.** -/
theorem jointLawIdentity_of_finiteStatLaw_ge_two {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (hm1 : 1 ≤ m) {ν : Measure (RecState N m × ℕ)} [IsProbabilityMeasure ν]
    (h : ∀ n, 2 ≤ n → FiniteStatLaw (N := N) (m := m) p hp0.le hp1.le hm1 ν n) :
    JointLawIdentity (N := N) (m := m) p hp0.le hp1.le hm1 ν :=
  jointLawIdentity_of_finiteStatLaw hp0 hp1 hm1 fun n => by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exact FiniteStatLaw.of_le (h 2 le_rfl) (by omega)
    · exact h n hn

/-- The statistic-level version forces the accepted start-law constraint
`ν {dmax = 0, time = 0} = 1` (`startLaw_constraint_of_jointLawIdentity`). -/
theorem eq_dirac_map_of_finiteStatLaw_ge_two {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) {ν : Measure (RecState N m × ℕ)} [IsProbabilityMeasure ν]
    (h : ∀ n, 2 ≤ n → FiniteStatLaw (N := N) (m := m) p hp hp1 hm ν n) :
    ν.map (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2))
      = Measure.dirac ((0 : ℕ), (0 : ℕ)) :=
  (finiteStatLaw_one_iff hp hp1 hm ν).1 (FiniteStatLaw.of_le (h 2 le_rfl) (by omega))

end M2RecordFinite
