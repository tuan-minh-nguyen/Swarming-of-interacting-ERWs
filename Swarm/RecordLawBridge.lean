/-
# LawBridge with the array-side record statistics discharged


`SwarmRecordMeas` (`RecordMeas.lean`) proves that the canonical record map `recTimeA` of the actual
array is measurable together with its defect sequence and satisfies the paper's `IsRecord`
description almost surely.  This file feeds those theorems into
`SwarmM4C.LawBridge.hterm_pathlaw_of_array`, which is the `hterm` field of the repaired
stopped-record tightness interface `SwarmM4.PCtxR` at the fixed constants
`T = ⌈2B/κ⌉ + 2`, `C₀ = B + T + 1`.

The point is the *residual premise list*.  Before this file the transfer needed

  (a) a record map `τf` satisfying `IsRecord` almost surely,
  (b) measurability of `U ↦ ((d_r).toNat, τ_r)`,
  (c) `(diam)`, and
  (d) the joint law identity `hlaw`.

Here (a) and (b) are theorems (`ae_isRecord_recTimeA_of_speed`, `measurable_recordStat`) for the
canonical map, so the residual inputs are exactly: the ballistic lower bound with its constant
`κ` (itself a theorem, `RecordoSupply.speed_actual`, for `1/2 < p < 1`, `2 ≤ m`), the diameter
estimate `(diam)`, and the joint `(defect, record time)` law identity `hlaw` on the stopped-record
path law.  `(diam)` and `hlaw` are *not* proved here; `hlaw` is the exact missing law identity,
stated below in both its joint-law form and its event-probability form.
-/
import Swarm.RecordMeas

open MeasureTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace SwarmRecordMeas

namespace Bridge

open RecordDefect RecordoSupply Swarming.Uniform SimJump.RecKernel SwarmRec SwarmRecordMeas.Actual

variable {N m : ℕ} [Nonempty (Fin N)]

/-- The joint law identity that remains open: the law of the stopped-record path's
`(defect, record time)` sequence equals the law of the actual array's `(defect, record time)`
sequence at the canonical record times.  This is the residual premise `hlaw` of
`SwarmM4C.LawBridge`. -/
def JointLawIdentity (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) : Prop :=
  (recordTrajT p hp hp1 hm ν).map (fun ω => (dT ω, tauT ω))
    = (Swarming.Uniform.arrayMeasure N).map (fun U =>
        (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
          fun r => recTimeA p m U r))

/-- **The event-level form of the missing identity**: for every level `r` and block scale `L`,
the probability that some dyadic multiple of `L` is a good block agrees between the
stopped-record path law and the actual array.  Both sides are measurable events
(`measurableSet_goodBlockA`), so this is an identity of genuine probabilities. -/
def EventLawIdentity (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (B C₀ T : ℕ)
    (ν : Measure (RecState N m × ℕ)) : Prop :=
  ∀ r L : ℕ, 1 ≤ L →
    (recordTrajT p hp hp1 hm ν) {ω | ∃ j : ℕ, GoodT B C₀ T ω r (2 ^ j * L)}
      = (Swarming.Uniform.arrayMeasure N) {U |
          ∃ j : ℕ, GoodBlock (defect (actX p m U) (recTimeA p m U)) (recTimeA p m U) T C₀ B r
            (2 ^ j * L)}

/-! ### The constraint the joint law identity places on the start law

The array's level-`0` statistic is *pointwise* `(0,0)` (`recTimeA_zero`, `defectA_zero`, no
probability needed).  Hence the joint law identity forces the level-`0` marginal of the
stopped-record path law, i.e. the start law `ν`, to be carried by the set
`{dmax = 0, time = 0}`.  This is the machine-checked form of the remark in `LawBridge.lean` that
no identification of the array can supply `hlaw` for an arbitrary `ν`; it is exactly the
constraint a compatible start law (the stopped path identity) must satisfy. -/

/-- The level-`0` marginal of the stopped-record path law, expressed through `ν`.
The factor two converts the compact state's half-distances to the raw paper defect. -/
theorem map_eval_zero_dT_tauT {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => (dT ω 0, tauT ω 0))
      = ν.map (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) := by
  have hpair : Measurable fun z : RecState N m × ℕ => (2 * dmax z.1, z.2) :=
    ((measurable_dmax.comp measurable_fst).const_mul 2).prodMk measurable_snd
  have hcomp : (fun ω : ℕ → RecState N m × ℕ => (dT ω 0, tauT ω 0))
      = (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) ∘ (fun ω => ω 0) := rfl
  rw [hcomp, ← Measure.map_map hpair (measurable_pi_apply 0), recordTrajT_eval]
  simp

/-- **The start-law constraint.**  If the joint `(defect, record time)` law identity holds, then
`ν` puts full mass on `dmax = 0` and record time `0`; in particular `ν` cannot be an arbitrary
probability measure, so the level-`0` field of `PCtxR` is not dischargeable by the law identity
alone. -/
theorem startLaw_constraint_of_jointLawIdentity {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : JointLawIdentity (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) ν) :
    ν {z : RecState N m × ℕ | dmax z.1 = 0 ∧ z.2 = 0} = 1 := by
  classical
  set stat : Swarming.Uniform.Array N → (ℕ → ℕ) × (ℕ → ℕ) :=
    fun U => (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
      fun r => recTimeA p m U r) with hstatdef
  set s : Set ((ℕ → ℕ) × (ℕ → ℕ)) := {q | (q.1 0, q.2 0) = ((0, 0) : ℕ × ℕ)} with hs
  have hsmeas : MeasurableSet s := by
    have hφ : Measurable fun q : (ℕ → ℕ) × (ℕ → ℕ) => ((q.1 0, q.2 0) : ℕ × ℕ) := by fun_prop
    exact (measurableSet_singleton (0, 0)).preimage hφ
  have hφ : Measurable fun q : (ℕ → ℕ) × (ℕ → ℕ) => ((q.1 0, q.2 0) : ℕ × ℕ) := by fun_prop
  have hstat : Measurable stat := measurable_recordStat (N := N) p m
  have hpair : Measurable fun z : RecState N m × ℕ => (2 * dmax z.1, z.2) :=
    ((measurable_dmax.comp measurable_fst).const_mul 2).prodMk measurable_snd
  -- the level-`0` array statistic is pointwise `(0,0)`
  have hzero : ∀ U : Swarming.Uniform.Array N, ((stat U).1 0, (stat U).2 0) = ((0, 0) : ℕ × ℕ) := by
    intro U
    have h1 : (defect (actX p m U) (recTimeA p m U) 0).toNat = 0 := by
      rw [defectA_zero (N := N) p m U]
      rfl
    have h2 : recTimeA p m U 0 = 0 := recTimeA_zero (N := N) p m U
    simp only [hstatdef, h1, h2]
  -- array side: probability one
  have hA : (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N | stat U ∈ s} = 1 := by
    have hset : {U : Swarming.Uniform.Array N | stat U ∈ s} = Set.univ := by
      ext U
      simp only [hs, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hzero U
    rw [hset, measure_univ]
  -- path side: the same event, with the law identity
  have hB : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν)
      {ω : ℕ → RecState N m × ℕ | (dT ω 0, tauT ω 0) = ((0, 0) : ℕ × ℕ)} = 1 := by
    have hdtau : Measurable fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω) :=
      measurable_dT.prodMk measurable_tauT
    have hset : {ω : ℕ → RecState N m × ℕ | (dT ω 0, tauT ω 0) = ((0, 0) : ℕ × ℕ)}
        = {ω : ℕ → RecState N m × ℕ | (dT ω, tauT ω) ∈ s} := by
      ext ω
      simp only [hs, Set.mem_ofPred_eq]
    have hpre : {ω : ℕ → RecState N m × ℕ | (dT ω, tauT ω) ∈ s}
        = (fun ω : ℕ → RecState N m × ℕ => (dT ω, tauT ω)) ⁻¹' s := rfl
    rw [hset, hpre, ← Measure.map_apply hdtau hsmeas, hlaw, Measure.map_apply hstat hsmeas]
    exact hA
  -- transfer to `ν`
  have hdt0 : Measurable fun ω : ℕ → RecState N m × ℕ => (dT ω 0, tauT ω 0) :=
    (measurable_dT_eval 0).prodMk (measurable_tauT_eval 0)
  have hν : ν ((fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) ⁻¹' {((0, 0) : ℕ × ℕ)}) = 1 := by
    rw [← Measure.map_apply hpair (measurableSet_singleton ((0, 0) : ℕ × ℕ)),
      ← map_eval_zero_dT_tauT (N := N) (m := m) hp0.le hp1.le (by omega : 1 ≤ m) ν,
      Measure.map_apply hdt0 (measurableSet_singleton ((0, 0) : ℕ × ℕ))]
    exact hB
  have hset2 : {z : RecState N m × ℕ | dmax z.1 = 0 ∧ z.2 = 0}
      = (fun z : RecState N m × ℕ => (2 * dmax z.1, z.2)) ⁻¹' {((0, 0) : ℕ × ℕ)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  rw [hset2, hν]

/-! ### The event-level identity is *not* a weaker target

Because the array's own block statement `ActualHterm.hterm_actual_fixed` is already proved, and
because the array-side block events are measurable (`measurableSet_goodBlockA`), the array side of
`EventLawIdentity` is *one*.  Consequently `EventLawIdentity` at the fixed constants is
**equivalent** to the almost-sure block statement on the stopped-record path law, i.e. to the
`hterm` conclusion itself.  So the event form is not a weaker residual premise: the content is
exactly the joint law identity `JointLawIdentity`, and anyone using the event form is assuming the
conclusion.  This is recorded so that the event form is not mistaken for an intermediate target. -/

/-- **Equivalence of the event-level identity with the path statement.** -/
theorem eventLawIdentity_iff_path_full {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    EventLawIdentity (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) B
        (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ν
      ↔ ∀ r L : ℕ, 1 ≤ L →
          (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν)
            {ω | ∃ j : ℕ, GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
              (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L)} = 1 := by
  -- the array side of the identity is one, at every level and scale
  have harr : ∀ r L : ℕ, 1 ≤ L →
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        ∃ j : ℕ, GoodBlock (defect (actX p m U) (recTimeA p m U)) (recTimeA p m U)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} = 1 := by
    intro r L hL
    have hae : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), U ∈ {U : Swarming.Uniform.Array N |
        ∃ j : ℕ, GoodBlock (defect (actX p m U) (recTimeA p m U)) (recTimeA p m U)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)} := by
      filter_upwards [hspeed, ae_isRecord_recTimeA_of_speed (N := N) (p := p) (m := m) hκ hspeed,
        hdiam] with U hU hτ hspread
      have hspd := hU (Classical.arbitrary (Fin N))
      exact SwarmM4C.FixedConst.hterm_fixed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
        (defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread)
        B hB r L hL
    have h := SwarmM4C.LawBridge.measure_eq_univ_of_ae hae
    simpa using h
  constructor
  · intro h r L hL
    rw [h r L hL]
    exact harr r L hL
  · intro h r L hL
    rw [h r L hL, harr r L hL]

/-- **The `hterm` field of `PCtxR` at fixed constants, from the actual array, with the
array-side record-statistics hypotheses discharged.**

Residual hypotheses: the one-walker ballistic bound with constant `κ` (a theorem for the actual
array, `RecordoSupply.speed_actual`), the diameter estimate `(diam)`, and the joint law identity
`JointLawIdentity`. -/
theorem hterm_pathlaw_of_array_canonical {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : JointLawIdentity (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) ν) :
    ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
        GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
          (2 ^ j * L) :=
  SwarmM4C.LawBridge.hterm_pathlaw_of_array hp0 hp1 hm N hN B hB hκ hspeed
    (fun U r => recTimeA p m U r)
    (ae_isRecord_recTimeA_of_speed (N := N) (p := p) (m := m) hκ hspeed)
    (measurable_recordStat (N := N) p m) hdiam ν hlaw

/-- **The same, with the ballistic constant existentially quantified**: no speed hypothesis is
left to the caller, because `RecordoSupply.speed_actual` supplies one for every `1/2 < p < 1` and
`2 ≤ m`.  Residual inputs: `(diam)` and the joint law identity only. -/
theorem hterm_pathlaw_of_array_canonical_exists {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : JointLawIdentity (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
        GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
          (2 ^ j * L) := by
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  exact ⟨κ, hκ, hterm_pathlaw_of_array_canonical hp0 hp1 hm hN B hB hκ (hspeed N hN) hdiam ν hlaw⟩

/-- **The `hterm` field from the event-level law identity.**  Here the array side enters only
through the probabilities of the block events, which are measurable by
`measurableSet_goodBlockA`; `EventLawIdentity` therefore relates genuine probabilities. -/
theorem hterm_pathlaw_of_eventlaw_canonical {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hlaw : EventLawIdentity (N := N) (m := m) p hp0.le hp1.le (by omega : 1 ≤ m) B
      (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ν) :
    ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m) ν), ∃ j : ℕ,
        GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
          (2 ^ j * L) :=
  SwarmM4C.LawBridge.hterm_pathlaw_of_eventlaw hp0 hp1 hm N hN B hB hκ hspeed
    (fun U r => recTimeA p m U r)
    (ae_isRecord_recTimeA_of_speed (N := N) (p := p) (m := m) hκ hspeed)
    hdiam ν hlaw

end Bridge

end SwarmRecordMeas
