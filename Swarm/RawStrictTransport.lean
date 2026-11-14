/-
Concrete finite selectors for the strict first regeneration block.

This file proves the exact translated-path law on the completed strict first-block
event, and its normalized form under `SwarmFB.seedCond` from a genuine invariant
record law.  It does not construct an initial regeneration from an arbitrary raw
path and is not the remaining raw-array input to `NeutralTransport`.
-/
import Swarm.RawTimeStrictSum
import Swarm.ChainRegenBridge
import Swarm.HfullBridge
import Swarm.FBCore
import Swarm.StarRegen

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace RawStrictTransport

open Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open SwarmRawTimeStrictSum

variable {N : ℕ}

/-- The Nat-valued first regeneration level; its fallback is irrelevant on a
completed block. -/
noncomputable def firstLevel (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  SwarmChainRegen.firstRegenLevel (SwarmRestart.posPath p m U)

/-- The extended hitting time at the first regeneration level. -/
noncomputable def firstTau (p : ℝ) (m : ℕ) (U : Array N) : ℕ∞ :=
  RegenPath.tau (SwarmRestart.posPath p m U) (firstLevel p m U : ℤ)

/-- A finite time selector on every array, equal to the genuine first-block
hitting time whenever that block exists. -/
noncomputable def firstTime (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  (firstTau p m U).toNat

/-- The integer relative future after the selected block. -/
noncomputable def firstFutureZ (p : ℝ) (m : ℕ) (U : Array N) : RegenPath.Path N :=
  SwarmFresh.relFuture p m U (firstTime p m U) (firstLevel p m U : ℤ)

/-- The literal real translated path used by `NeutralTransport`. -/
noncomputable def firstFutureR (p : ℝ) (m : ℕ) (U : Array N) : ℕ → Fin N → ℝ :=
  fun n i => Swarm.pos (Swarm.actualX (N := N) p m) (n + firstTime p m U) i U -
    (firstLevel p m U : ℝ)

/-- Coordinatewise integer-to-real cast on path space. -/
def castPath : (ℕ → Fin N → ℤ) → (ℕ → Fin N → ℝ) :=
  fun X n i => (X n i : ℝ)

/-- Fixed-level hitting time is measurable, including its infinite value. -/
theorem measurable_tau_fixed (r : ℤ) : Measurable (fun X : RegenPath.Path N =>
    RegenPath.tau X r) := by
  refine measurable_to_countable' fun e => ?_
  cases e with
  | top =>
      have hset : (fun X : RegenPath.Path N => RegenPath.tau X r) ⁻¹' {⊤} =
          (⋃ t : ℕ, {X : RegenPath.Path N | RegenPath.tau X r = (t : ℕ∞) })ᶜ := by
        ext X
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
          Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
        constructor
        · intro h t htau
          rw [htau] at h
          simp at h
        · intro h
          unfold RegenPath.tau
          split_ifs with hex
          · exfalso
            exact h (Nat.find hex) (by simp [RegenPath.tau, hex])
          · rfl
      rw [hset]
      exact (MeasurableSet.iUnion fun t =>
        SwarmRawTimeStrict.measurableSet_tau_eq r t).compl
  | coe t =>
      exact SwarmRawTimeStrict.measurableSet_tau_eq r t

/-- Measurability of the actual first-level selector. -/
theorem measurable_firstLevel (p : ℝ) (m : ℕ) : Measurable (firstLevel (N := N) p m) := by
  exact SwarmChainRegen.measurable_firstRegenLevel.comp
    (SwarmRestart.measurable_posPath p m N)

/-- Measurability of the extended hitting time at the random first level. -/
theorem measurable_firstTau (p : ℝ) (m : ℕ) : Measurable (firstTau (N := N) p m) := by
  let F : RegenPath.Path N × ℕ → ℕ∞ := fun q => RegenPath.tau q.1 (q.2 : ℤ)
  have hF : Measurable F := measurable_from_prod_countable_left fun d =>
    measurable_tau_fixed (N := N) (d : ℤ)
  have hpair : Measurable (fun U : Array N =>
      (SwarmRestart.posPath p m U, firstLevel p m U)) :=
    (SwarmRestart.measurable_posPath p m N).prodMk (measurable_firstLevel p m)
  change Measurable (fun U : Array N => RegenPath.tau
    (SwarmRestart.posPath p m U) (firstLevel p m U : ℤ))
  exact hF.comp hpair

/-- The finite first-block time selector is measurable. -/
theorem measurable_firstTime (p : ℝ) (m : ℕ) : Measurable (firstTime (N := N) p m) := by
  have htoNat : Measurable (fun e : ℕ∞ => e.toNat) := measurable_of_countable _
  exact htoNat.comp (measurable_firstTau p m)

/-- The randomly translated integer future is measurable on the actual array. -/
theorem measurable_firstFutureZ (p : ℝ) (m : ℕ) : Measurable (firstFutureZ (N := N) p m) := by
  have hlevelZ : Measurable (fun U : Array N => (firstLevel p m U : ℤ)) := by
    have hc : Measurable (fun d : ℕ => (d : ℤ)) := measurable_of_countable _
    exact hc.comp (measurable_firstLevel p m)
  have hF : Measurable (fun q : (ℕ × ℤ) × Array N =>
      SwarmFresh.relFuture p m q.2 q.1.1 q.1.2) := by
    refine measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun i => ?_
    refine M6Star.measurable_uncurry_of_forall
      (f := fun (q : ℕ × ℤ) (U : Array N) =>
        (Swarming.Trajectory.trajectory p m U (q.1 + n)).pos i - q.2) ?_
    intro q
    exact (measurable_posPath_apply p m N (q.1 + n) i).sub_const q.2
  have hpair : Measurable (fun U : Array N =>
      ((firstTime p m U, (firstLevel p m U : ℤ)), U)) :=
    ((measurable_firstTime p m).prodMk hlevelZ).prodMk measurable_id
  change Measurable (fun U : Array N =>
    SwarmFresh.relFuture p m U (firstTime p m U) (firstLevel p m U : ℤ))
  exact hF.comp hpair

/-- The real translated path is measurable. -/
theorem measurable_firstFutureR (p : ℝ) (m : ℕ) : Measurable (firstFutureR (N := N) p m) := by
  have hc : Measurable (fun U : Array N => (firstLevel p m U : ℝ)) := by
    have hcast : Measurable (fun d : ℕ => (d : ℝ)) := measurable_of_countable _
    exact hcast.comp (measurable_firstLevel p m)
  exact M6Star.measurable_shiftPath p m (firstTime p m)
    (fun U => (firstLevel p m U : ℝ)) (measurable_firstTime p m) hc

/-- The integer-to-real path cast is measurable. -/
theorem measurable_castPath : Measurable (castPath (N := N)) := by
  refine measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun i => ?_
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  exact hcast.comp ((measurable_pi_apply i).comp (measurable_pi_apply n))

/-- The actual real path is the cast of the actual integer path. -/
theorem actPath_eq_castPath_posPath (p : ℝ) (m : ℕ) :
    M6Star.actPath (N := N) p m = fun U => castPath (SwarmRestart.posPath p m U) := by
  funext U n i
  rfl

/-- On a concrete completed first block, the level selector is the true level. -/
theorem firstLevel_eq_of_mem (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hU : U ∈ FirstBlockFuture (N := N) p m q Set.univ) :
    firstLevel p m U = q.1.1 := by
  let X := SwarmRestart.posPath p m U
  have hD : RegenPath.D X = (q.1.1 : ℕ∞) := hU.2.1
  have hreg : RegenPath.Reg X (q.1.1 : ℤ) :=
    ((SwarmRawTimeStrict.D_eq_iff X q.1.1 q.2).mp hD).1
  have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := ⟨q.1.1, q.2, hreg⟩
  have hlevel : (SwarmChainRegen.firstRegenLevel X : ℕ∞) = (q.1.1 : ℕ∞) :=
    (SwarmChainRegen.raw_D_eq_firstRegenLevel_of_exists X hex).symm.trans hD
  change SwarmChainRegen.firstRegenLevel X = q.1.1
  exact_mod_cast hlevel

/-- On a concrete completed first block, the finite time selector is exactly
its strict-tail hitting time. -/
theorem firstTime_eq_of_mem (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hU : U ∈ FirstBlockFuture (N := N) p m q Set.univ) :
    firstTime p m U = q.1.2 := by
  have hlevel := firstLevel_eq_of_mem p m q hU
  have htau : RegenPath.tau (SwarmRestart.posPath p m U) (q.1.1 : ℤ) =
      (q.1.2 : ℕ∞) := hU.2.2.1
  simp [firstTime, firstTau, hlevel, htau]

/-- The selected future agrees with the concrete relative future on every
completed first-block piece. -/
theorem firstFutureZ_eq_of_mem (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hU : U ∈ FirstBlockFuture (N := N) p m q Set.univ) :
    firstFutureZ p m U = SwarmFresh.relFuture p m U q.1.2 (q.1.1 : ℤ) := by
  simp [firstFutureZ, firstTime_eq_of_mem p m q hU, firstLevel_eq_of_mem p m q hU]

/-- The real translated path is the coordinatewise cast of the integer future. -/
theorem firstFutureR_eq_cast (p : ℝ) (m : ℕ) :
    firstFutureR (N := N) p m = fun U => castPath (firstFutureZ p m U) := by
  funext U n i
  simp [firstFutureR, castPath, firstFutureZ, SwarmFresh.relFuture,
    M6Star.actPath, Swarm.pos, Swarm.actualX, Nat.add_comm]

/-- The normalized strict fresh law is the integer path law of the actual
`seedCond`. -/
theorem normalizedStrictLaw_eq_seedCond_map (p : ℝ) (m N : ℕ) :
    normalizedStrictLaw p m N =
      (SwarmFB.seedCond (p := p) (m := m) (N := N)).map
        (SwarmRestart.posPath p m) := by
  rw [normalizedStrictLaw,
    Measure.restrict_map (SwarmRestart.measurable_posPath p m N)
      SwarmFresh.measurableSet_strictPos,
    SwarmFB.seedCond, ProbabilityTheory.cond, Measure.map_smul]
  rfl

/-- Exact integer path law on the completed strict first-block event.  The
human input is the same strict-path positivity used by the normalized joint
factorization; no initial-regeneration existence is assumed. -/
theorem restrict_completed_map_firstFutureZ (p : ℝ) (m N : ℕ)
    (hpos : (arrayMeasure N) {U : Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 0) :
    ((arrayMeasure N).restrict
      (CompletedFirstBlockFuture (N := N) p m Set.univ)).map (firstFutureZ p m) =
      (arrayMeasure N) (CompletedFirstBlockFuture (N := N) p m Set.univ) •
        normalizedStrictLaw p m N := by
  ext B hB
  have hset : firstFutureZ (N := N) p m ⁻¹' B ∩
      CompletedFirstBlockFuture (N := N) p m Set.univ =
      CompletedFirstBlockFuture p m B := by
    ext U
    constructor
    · rintro ⟨hB, hA⟩
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hA
      apply Set.mem_iUnion.mpr
      refine ⟨q, hq.1, hq.2.1, hq.2.2.1, ?_⟩
      have heq := firstFutureZ_eq_of_mem p m q hq
      change firstFutureZ p m U ∈ B at hB
      rwa [heq] at hB
    · intro hU
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
      have hu : U ∈ FirstBlockFuture (N := N) p m q Set.univ :=
        ⟨hq.1, hq.2.1, hq.2.2.1, Set.mem_univ _⟩
      refine ⟨?_, Set.mem_iUnion.mpr ⟨q, hu⟩⟩
      have heq := firstFutureZ_eq_of_mem p m q hu
      change firstFutureZ p m U ∈ B
      rw [heq]
      exact hq.2.2.2
  rw [Measure.map_apply (measurable_firstFutureZ p m) hB,
    Measure.restrict_apply ((measurable_firstFutureZ p m) hB), hset,
    Measure.smul_apply, smul_eq_mul,
    array_completedFirstBlock_normalized_joint p m N hpos hB]

/-- A genuine invariant record law makes the strict no-first-block remainder null. -/
theorem noFirstBlock_null_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    (arrayMeasure N) (NoFirstBlock (N := N) p m) = 0 := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  have hfull := SwarmActualHfull.full_selection_actual_of_invariant
    (p := p) hp0 hp1 hm hN π hinv
  have hnull := (SwarmSelInd.full_iff_noRegen_null (p := p) (m := m)
    (by omega : 0 < N)).mp hfull
  have hset : {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed ∧
        ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧
          SwarmSel.isRegen t d (SwarmRestart.posPath p m U)} =
      NoFirstBlock (N := N) p m := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, NoFirstBlock]
    constructor
    · rintro ⟨hseed, hno⟩
      exact ⟨hseed, (SwarmActualHfull.noRegen_seed_eq_D_top _
        (SwarmFresh.posPath_zero p m U)
        (fun n i => SwarmFresh.posPath_step p m U n i)).mp hno⟩
    · rintro ⟨hseed, htop⟩
      exact ⟨hseed, (SwarmActualHfull.noRegen_seed_eq_D_top _
        (SwarmFresh.posPath_zero p m U)
        (fun n i => SwarmFresh.posPath_step p m U n i)).mpr htop⟩
  rw [← hset]
  exact hnull

/-- The completed strict first-block event exhausts the seed mass once the
no-block remainder is null. -/
theorem completed_mass_eq_seed_of_null (p : ℝ) (m : ℕ)
    (hno : (arrayMeasure N) (NoFirstBlock (N := N) p m) = 0) :
    (arrayMeasure N) (CompletedFirstBlockFuture (N := N) p m Set.univ) =
      (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
  have hdecomp := array_strictPath_mass_eq_NoFirstBlock_add_Completed (N := N) p m
  rw [hno, zero_add] at hdecomp
  exact hdecomp.symm

/-- Normalized integer-path first-block transport under the actual `seedCond`.
The only stochastic premise is the genuine invariant record law also used by
`HfullBridge`; raw-array stationarity is not asserted. -/
theorem seedCond_map_firstFutureZ_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    (SwarmFB.seedCond (p := p) (m := m) (N := N)).map (firstFutureZ p m) =
      normalizedStrictLaw p m N := by
  have hpos : (arrayMeasure N) {U : Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  have hno := noFirstBlock_null_of_invariant (N := N) hp0 hp1 hm hN π hinv
  have hmap := restrict_completed_map_firstFutureZ p m N hpos
  have hmass := completed_mass_eq_seed_of_null (N := N) p m hno
  have hrestrict : (arrayMeasure N).restrict {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} =
      (arrayMeasure N).restrict
        (CompletedFirstBlockFuture (N := N) p m Set.univ) := by
    rw [strictPath_eq_NoFirstBlock_union_Completed,
      Measure.restrict_union (NoFirstBlock_disjoint_Completed p m)
        (measurableSet_CompletedFirstBlockFuture p m MeasurableSet.univ),
      Measure.restrict_zero_set hno, zero_add]
  rw [SwarmFB.seedCond, ProbabilityTheory.cond, SwarmFB.seedSet, hrestrict,
    Measure.map_smul, hmap,
    hmass, smul_smul, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_smul]

/-- Under `seedCond`, the selected first-block time is almost surely the time
of a genuine finite positive regeneration level. -/
theorem ae_D_ne_top_seedCond_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      RegenPath.D (SwarmRestart.posPath p m U) ≠ ⊤ := by
  have hno := noFirstBlock_null_of_invariant (N := N) hp0 hp1 hm hN π hinv
  have htop : MeasurableSet {X : RegenPath.Path N | RegenPath.D X = ⊤} :=
    SwarmChainRegen.measurable_raw_D (measurableSet_singleton ⊤)
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  change (SwarmFB.seedCond (p := p) (m := m) (N := N))
    {U : Array N | RegenPath.D (SwarmRestart.posPath p m U) = ⊤} = 0
  rw [SwarmFB.seedCond_apply SwarmFB.measurableSet_seedSet]
  have hinter : SwarmFB.seedSet (p := p) (m := m) (N := N) ∩
      {U : Array N | RegenPath.D (SwarmRestart.posPath p m U) = ⊤} =
      NoFirstBlock (N := N) p m := by
    ext U
    rfl
  rw [hinter, hno, mul_zero]

/-- The real-path form consumed by neutral transport, still on `seedCond`
itself rather than on the unconditioned raw array. -/
theorem seedCond_map_firstFutureR_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    (SwarmFB.seedCond (p := p) (m := m) (N := N)).map (firstFutureR p m) =
      (SwarmFB.seedCond (p := p) (m := m) (N := N)).map
        (M6Star.actPath (N := N) p m) := by
  have hz := seedCond_map_firstFutureZ_of_invariant (N := N) hp0 hp1 hm hN π hinv
  have hreal := congrArg
    (fun μ : Measure (RegenPath.Path N) => μ.map (castPath (N := N))) hz
  rw [Measure.map_map measurable_castPath (measurable_firstFutureZ p m),
    normalizedStrictLaw_eq_seedCond_map,
    Measure.map_map measurable_castPath (SwarmRestart.measurable_posPath p m N)] at hreal
  have hleft : (castPath (N := N) ∘ firstFutureZ p m) = firstFutureR p m := by
    rw [Function.comp_def, firstFutureR_eq_cast]
  have hright : (castPath (N := N) ∘ SwarmRestart.posPath p m) =
      M6Star.actPath (N := N) p m := by
    rw [Function.comp_def, actPath_eq_castPath_posPath]
  rwa [hleft, hright] at hreal

end RawStrictTransport
