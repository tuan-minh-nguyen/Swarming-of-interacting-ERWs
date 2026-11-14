/-
# The paper's model: unconditional ballistic lower bound, and the interval from one premise

`Swarm/ProjVbound.lean` proves `projected_speed_uniform`, the
**unconditional** N-uniform positive liminf speed for the paper's actual i.i.d.-array
construction.  This file restates that theorem in the language of the public targets
(`Swarm.pos`, `Swarm.Ballistic`'s conclusion) and combines it with the integrated upper bound
`Swarm.speed_le_two_p_sub_one` (applied to the integrated instance
`SwarmCross.Actual.actual_isInteractingLaw`) to get the paper's interval
`[κ(m,p), 2p-1]` **for the paper's own model** from a single remaining premise: existence of the
almost-sure speed.

Main declarations:

* `arrX` — the actual position process of `Swarming.Trajectory.trajectory` in `Swarm`'s shape;
* `ballistic_actual` — **unconditional**: `∃ κ > 0`, independent of `N`, with
  `κ ≤ liminf_n X_n^i/n` a.s. for every walker in the actual array model.
  This is the `liminf` half of the paper's Proposition `ball` for the concrete model, restated
  in the public target's language;
* `actual_speed_le` — the upper half `v ≤ 2p-1` at a fixed walker;
* `mainClaimAtArray_of_speed` — the paper's Theorem 1.1 conclusion for the actual array model,
  from the single premise that a deterministic speed `v(N)` exists almost surely.

Nothing here is generic over the weak marginal class: the statements are about the paper's
actual construction, and they do not claim `Swarm.Ballistic`, `Swarm.CommonLimit`, or
`Swarm.MainClaim` for arbitrary `IsInteractingLaw` systems.

All declarations are proved; see `FrontAudit.lean` for the axiom audit.
-/
import Swarm.ActualInstance
import Swarm.ProjVbound

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace SwarmActualFront

open Swarming Swarming.Uniform Swarming.Trajectory

/-- The actual position process of the paper's array model, in the shape used by the public
targets (`ℕ → Ω → Fin N → ℤ`). -/
noncomputable def arrX {N : ℕ} (p : ℝ) (m : ℕ) : ℕ → Array N → Fin N → ℤ :=
  fun n U i => (trajectory p m U n).pos i

/-- `Swarm.pos` of `arrX` is the real position of the trajectory. -/
theorem pos_arrX {N : ℕ} (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    Swarm.pos (arrX (N := N) p m) n i U = (((trajectory p m U n).pos i : ℤ) : ℝ) := rfl

/-- **The paper's ballistic lower bound for the actual array model, unconditionally.**
There is `κ > 0`, depending only on `m` and `p`, such that for every `N ≥ 2`, almost surely for
every walker, `κ ≤ liminf_n X_n^i/n`. -/
theorem ballistic_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => Swarm.pos (arrX (N := N) p m) n i U / n) atTop := by
  obtain ⟨κ, hκ, h⟩ := Enl.ProjVbound.projected_speed_uniform (p := p) hp0 hp1 (m := m) hm
  refine ⟨κ, hκ, fun N hN => ?_⟩
  filter_upwards [h N hN] with U hU
  intro i
  exact hU i

/-- The upper half `v ≤ 2p-1` at a fixed walker of the actual model, from the integrated
conditional-mean bound `Swarm.speed_le_two_p_sub_one` applied to the integrated instance
`SwarmCross.Actual.actual_isInteractingLaw`. -/
theorem actual_speed_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {N : ℕ}
    (i : Fin N) {v : ℝ}
    (hconv : ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n : ℕ => Swarm.pos (arrX (N := N) p m) n i U / n) atTop (𝓝 v)) :
    v ≤ 2 * p - 1 := by
  have hlaw := SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m
  refine Swarm.speed_le_two_p_sub_one (𝓕 := SwarmCross.pathFilt (N := N) p m)
    (μ := arrayMeasure N) (X := arrX (N := N) p m) hlaw hp0.le i ?_
  simpa [Swarm.pos, arrX] using hconv

/-- **The paper's Theorem 1.1 conclusion for the actual array model, from the existence of the
speed.**  If for every `N ≥ 2` all walkers of the actual model have a common deterministic
almost-sure speed `v N`, then there is `κ > 0` (independent of `N`) with
`κ ≤ v N ≤ 2p-1` and `X_n^i/n → v N` almost surely for every walker.

The lower bound is `projected_speed_uniform` (unconditional), the upper bound is the integrated
`Swarm.speed_le_two_p_sub_one`; the only supplied datum is the almost-sure existence of the
limit. -/
theorem mainClaimAtArray_of_speed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m)
    (hspeed : ∃ v : ℕ → ℝ, ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n : ℕ => Swarm.pos (arrX (N := N) p m) n i U / n) atTop (𝓝 (v N))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∃ v : ℝ,
      κ ≤ v ∧ v ≤ 2 * p - 1 ∧ ∀ i : Fin N,
        Tendsto (fun n : ℕ => Swarm.pos (arrX (N := N) p m) n i U / n) atTop (𝓝 v) := by
  obtain ⟨κ, hκ, hball⟩ := ballistic_actual hp0 hp1 hm
  obtain ⟨v, hv⟩ := hspeed
  refine ⟨κ, hκ, fun N hN => ?_⟩
  have i₀ : Fin N := ⟨0, by omega⟩
  have hupper : v N ≤ 2 * p - 1 :=
    actual_speed_le hp0 hp1 (N := N) i₀ ((hv N hN).mono fun U h => h i₀)
  filter_upwards [hball N hN, hv N hN] with U hb hconv
  exact ⟨v N, Swarm.le_of_le_liminf_of_tendsto (hconv i₀) (hb i₀), hupper, hconv⟩

end SwarmActualFront
