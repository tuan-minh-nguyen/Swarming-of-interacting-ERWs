/-
# Theorem 1.1 with the frontier restated: per-`N` almost-sure tower success

## What this file establishes

`TowerForceSharp` + `TowerForceBridge` show that the capstone's per-level *conditional force*
`(F)` is equivalent, for every `N`, to nullity of the strict-attempt all-fail event, and that
this is the same event as `{D = ⊤}`.  Hence the honest residual input of the paper's
Theorem 1.1 is not a force profile but the almost-sure statement itself:

  `(T_N)  ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r`

(equivalently `μ_N {D = ⊤} = 0`).

This file states the paper's Theorem 1.1 on the literal array under exactly
`hπ` (an invariant stopped-record law, per `N`) and `(T_N)`.  Two points make the statement a
genuine sharpening of `TowerExhaustCapstone.main_claim_actual_of_invariant_and_conditional_force`:

* the residual input is **per `N`**, with no single sequence `q` shared across all `N` — the old
  capstone needed one `q` for every `N` simultaneously, which is strictly stronger than
  per-`N` nullity (an infimum of divergent per-`N` freshness profiles need not diverge);
* the residual input contains no auxiliary sequence and no inequality: it is the paper's own
  synchronisation statement in almost-sure form.

`main_claim_actual_of_invariant_and_conditional_force'` below re-derives the old capstone from
this one, so nothing is lost: the new theorem strictly generalises it.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `opaque`, no `unsafe`.
-/
import Swarm.TowerForceBridge
import Swarm.NeutralTwoInputCapstone
import Swarm.HpathFromDtopNull

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace TowerForceFrontier

open Swarming.Uniform Swarming.Trajectory SwarmTowerExhaust RawStrictAttemptTower
open SwarmRestart SwarmFresh SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}

/-- Almost-sure success of the strict-attempt tower is nullity of the all-fail event. -/
theorem infiniteFailure_eq_zero_of_ae_strictAttempt
    (h : ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r) :
    (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0 := by
  have hiff := (MeasureTheory.ae_iff (μ := arrayMeasure N)
    (p := fun U : Array N => ∃ r, StrictAttempt p m U r)).mp h
  simpa only [InfiniteFailure, Set.mem_ofPred_eq] using hiff

/-- Almost-sure success of the strict-attempt tower is nullity of `{D = ⊤}`. -/
theorem D_top_eq_zero_of_ae_strictAttempt (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (h : ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0 :=
  (TowerForceBridge.D_top_measure_eq_zero_iff_infiniteFailure_eq_zero
    (N := N) hp0 hp1 hm hN).mpr (infiniteFailure_eq_zero_of_ae_strictAttempt h)

/-- **Theorem 1.1 of `main_1d_revised.tex` on the literal array, with the residual input in
almost-sure form.**

`κ(m,p) > 0` is chosen once, before `N`; for every `N ≥ 2` there is a single deterministic `v`
with `κ ≤ v ≤ 2p-1` and almost-sure convergence of every walker's normalised position. -/
theorem main_claim_actual_of_tower_ae {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hπ : ∀ (N : ℕ), 2 ≤ N → ∃ (π : Measure (SwarmRec.RecState N m)),
      IsProbabilityMeasure π ∧
        Kernel.Invariant
          (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π)
    (htower : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  refine ActualNeutralCapstone.main_claim_actual_of_invariant_neutral_derived_level
    hp0 hp1 hm hπ ?_
  intro N hN
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  exact HpathFromDtopNull.hpath_of_D_top_null hp0 hp1 hm hN
    (D_top_eq_zero_of_ae_strictAttempt hp0 hp1 hm hN (htower N hN))

/-- **The old capstone follows.**  A single divergent force for all `N` gives per-`N`
almost-sure tower success (`TowerExhaust.infiniteFailure_eq_zero_of_tendsto_sum`), hence the
paper's Theorem 1.1 by `main_claim_actual_of_tower_ae`.

This is the precise sense in which the new statement strictly generalises
`TowerExhaustCapstone.main_claim_actual_of_invariant_and_conditional_force`. -/
theorem main_claim_actual_of_invariant_and_conditional_force' {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hπ : ∀ (N : ℕ), 2 ≤ N → ∃ (π : Measure (SwarmRec.RecState N m)),
      IsProbabilityMeasure π ∧
        Kernel.Invariant
          (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π)
    {q : ℕ → ℝ} (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1)
    (hdiv : Tendsto (fun R : ℕ => ∑ r ∈ Finset.range R, q r) atTop atTop)
    (hforce : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ r : ℕ,
      q r * (arrayMeasure N).real (NoSucc (N := N) p m r)
        ≤ (arrayMeasure N).real (FirstSuccessCell (N := N) p m r)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  refine main_claim_actual_of_tower_ae hp0 hp1 hm hπ fun N inst hN => ?_
  exact ae_exists_strictAttempt_of_infiniteFailure_null
    (infiniteFailure_eq_zero_of_tendsto_sum hq0 hq1 hdiv (hforce N hN))

end TowerForceFrontier
