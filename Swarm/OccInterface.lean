/-
  **DIRECTION F (m6) — `OccInterface.lean`: the ledger composed with the paper's `(occbnd)`.**

  `SwarmOcc.occbnd_of_pieces` (`Swarm/OccAssemble.lean`) turns the summed drift
  inequality into the occupation bound

      Occ T <= 2 M_T + (eps + 3 delta) T + max 0 (-Z_0)

  from four inputs: the per-time drift bound, and the three eventual budgets on `Z`, on the
  `J`-sum and on the compensator `Q`.  This file composes it with the Direction F assembly, so
  that all four inputs are *named objects of the actual model*:

  * the per-time drift bound is discharged from the pointwise `enlFilt` bounds of Directions A/B
    (explicit hypothesis `hAB`) through `ledger_actual` — it is the only probabilistic input;
  * `Z`, `J`, `Q` are `Zpot`, `Jcorr`, `Qcomp` at the actual record `b_n`, `M_n^j`, and `Q` is
    the centred compensator by `CorrectionDrift.compensator_unconditional`.

  The three eventual budgets are *not* proved here (they are the `(Jbound)`, `(Vbound)` and
  strong-law items of the paper); they are explicit hypotheses, each displayed in full.
-/
import Swarm.CorrectionDrift


set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace VdriftAssembly

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-- The ledger's occupation count `sum_{t<T} 1{0 <= X_t^i <= M_t^j}` as a function of the array. -/
noncomputable def occSum (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t

/-- The ledger's `J`-sum `sum_{t<T} J_{t+1}`. -/
noncomputable def Jsum (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, Jcorr p m eps i j U t

/-- **The paper's `(occbnd)` for the actual trajectory**, with every premise displayed.

`hZ`, `hJ`, `hQ` are the three eventual pathwise budgets (`(Vbound)`, `(Jbound)`, and the strong
law for `Q`), each stated as an almost-sure `forall T >= N0` statement; `hAB` is the pointwise
`enlFilt` bound of Directions A/B.  Nothing else is used: `Q` is the exact centred compensator of
`CorrectionDrift.compensator_unconditional`. -/
theorem occupation_bound_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {eps δ : ℝ} (hε : 0 < eps)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    {M : Array N → ℕ → ℝ} {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀, Zpot p m eps i j U T ≤ M U T + δ * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀, Jsum p m eps i j U T ≤ M U T + δ * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qcomp p m eps (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      occSum p m i j U T ≤ 2 * M U T + (eps + 3 * δ) * (T : ℝ)
        + max 0 (-(Zpot p m eps i j U 0)) := by
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      occSum p m i j U n
        ≤ eps * (n : ℝ) + (Zpot p m eps i j U n - Zpot p m eps i j U 0)
          + Jsum p m eps i j U n
          - Qcomp p m eps (fun t => alphaFun p m t i) i j U n := by
    filter_upwards [oneStep_all hp0 hp1 hε
      (fun t U => one_half_le_alphaFun hp0 hp1 m t i U) hAB] with U hall
    intro n
    exact ledger_pointwise p m eps (fun t => alphaFun p m t i) i j U hall n
  filter_upwards [hdrift, hZ, hJ, hQ] with U hd hZl hJl hQl
  intro T hT
  exact SwarmOcc.occbnd_of_pieces
    (Occ := fun n => occSum p m i j U n) (Z := fun n => Zpot p m eps i j U n)
    (J := fun n => Jsum p m eps i j U n)
    (Q := fun n => Qcomp p m eps (fun t => alphaFun p m t i) i j U n)
    (M := fun n => M U n) (ε := eps) (δ := δ) (N := N₀) hd
    (fun n hn => hZl n hn) (fun n hn => hJl n hn) (fun n hn => hQl n hn) T hT

/-- **The paper's `(occbnd)` with `eps = 1/32`, `delta = 1/64`** — the constant choice of
`SwarmOcc.occbnd_one_eighth`, i.e. the exact shape `SwarmSpeed.speed_lower_bound` consumes.
Note that the onset `max N0 ceil(32 max 0 (-Z_0))` is `omega`-dependent, as it must be. -/
theorem occupation_bound_one_eighth {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N}
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    {M : Array N → ℕ → ℝ} {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ max N₀ ⌈32 * max 0 (-(Zpot p m (1 / 32) i j U 0))⌉₊,
      occSum p m i j U T ≤ 2 * M U T + (1 / 8) * (T : ℝ) := by
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      occSum p m i j U n
        ≤ (1 / 32) * (n : ℝ) + (Zpot p m (1 / 32) i j U n - Zpot p m (1 / 32) i j U 0)
          + Jsum p m (1 / 32) i j U n
          - Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U n := by
    filter_upwards [oneStep_all hp0 hp1 (by norm_num : (0 : ℝ) < 1 / 32)
      (fun t U => one_half_le_alphaFun hp0 hp1 m t i U) hAB] with U hall
    intro n
    exact ledger_pointwise p m (1 / 32) (fun t => alphaFun p m t i) i j U hall n
  filter_upwards [hdrift, hZ, hJ, hQ] with U hd hZl hJl hQl
  intro T hT
  exact SwarmOcc.occbnd_one_eighth
    (Occ := fun n => occSum p m i j U n) (Z := fun n => Zpot p m (1 / 32) i j U n)
    (J := fun n => Jsum p m (1 / 32) i j U n)
    (Q := fun n => Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U n)
    (M := fun n => M U n) (N := N₀) hd
    (fun n hn => hZl n hn) (fun n hn => hJl n hn) (fun n hn => hQl n hn) T hT

/-! ## Consistency with the integrated one-step budget

The pointwise route and the integrated route agree where they overlap.  The implication below is
one-directional: it says that Directions A/B would *imply* the already-integrated budget
`DischargeInputs.integral_HpotInc_ge_paperWeight_discharged` time by time, which is why the
present assembly does not re-prove that budget and cannot be replaced by it. -/

/-- **A/B implies the integrated one-step budget** (per time). -/
theorem integral_paperWeight_le_of_pointwise {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N}
    (hAB : Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    ∫ U, Budget.paperWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  Budget.integral_le_of_condExp_ge (N := N) (p := p) hp0 hp1
    (Budget.integrable_paperWeight_w hp0 hp1 m n i j) hAB

/-- **Time aggregation of the one-step `paperWeight` budget at the weight level.**
Summing `∫ paperWeight_t <= ∫ HpotInc_t` over `t < T` and telescoping the potential gives
`Σ_{t<T} ∫ paperWeight_t <= ∫ (H_{j,T}(X_T^i) - H_{j,0}(X_0^i))`.  (The gain/loss split of
`sum_gain_le_loss_telescope` is the same statement after moving the loss term to the right.) -/
theorem sum_paperWeight_le_telescope {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N}
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (T : ℕ) :
    (∑ t ∈ Finset.range T, ∫ U, Budget.paperWeight p m t i j U ∂(arrayMeasure N))
      ≤ ∫ U, (SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U 0).pos i))
          ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hstep : ∀ t ∈ Finset.range T,
      (∫ U, Budget.paperWeight p m t i j U ∂(arrayMeasure N))
        ≤ ∫ U, HpotInc p m t i j U ∂(arrayMeasure N) :=
    fun t _ => integral_paperWeight_le_of_pointwise hp0 hp1 (hAB t)
  have hsum : (∑ t ∈ Finset.range T, ∫ U, HpotInc p m t i j U ∂(arrayMeasure N))
      = ∫ U, (SwarmOcc.Hpot (envH p m j U) ((trajectory p m U T).pos i)
          - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U 0).pos i))
          ∂(arrayMeasure N) := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun U => sum_HpotInc p m i j U T)
    · intro t _
      exact Budget.integrable_HpotInc (N := N) (p := p) hp0 hp1 hpne m t i j
  have hmain := Finset.sum_le_sum hstep
  rw [hsum] at hmain
  exact hmain

end VdriftAssembly
end Swarming.Enl
