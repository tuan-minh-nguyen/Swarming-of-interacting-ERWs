/-
  **`ProjResidual.lean` — the projected (paper-faithful) occupation budgets.**

  This file is the residual side of the occupation assembly, done with the ledger objects that are
  actually adapted: the optional projection `Zproj = E[Zpot | F_t]` and the centred projected
  martingale `Qpl` of `ProjOptionalLedger.lean`, *not* the quenched `Zpot`/`Qcomp`.

  Why this is the source-faithful object.  The paper's proof of Proposition `ball` uses

      Z_n = H_{j,n}(X_n^i) - F_{b_n}(X_n^i - M_n^j),  H_{j,n} = E[H_j | F_n],
      Q_n = sum_{t<n} ( Z_{t+1} - Z_t + J_{t+1} - E[Z_{t+1} - Z_t + J_{t+1} | F_t] )

  and its three budgets `(Vbound)`, `(Jbound)`, `Q_n = o(n)` are all statements about *that*
  adapted `Z` and *that* martingale `Q`.  The raw `Qcomp` of `VdriftAssembly` is the quenched
  ledger; it is not adapted (`QIncrementAdapted`), its optional projection is a different process
  (`QProjVarianceHonest`), and the gap between them is the terminal defect
  `Qcomp - Qproj = Zpot - E[Zpot | F_T]`, which is a genuine *additional* one-sided budget and
  must not be obtained by pushing a raw almost-sure bound through `condExp`.

  What is proved here (all with the standard axioms):

  * `inc_Qpl` : the increments of `Qpl` are exactly `projInc`, so `MartingaleLimit`'s strong law
    applies to the concrete process.
  * `Qpl_div_tendsto_zero` : the paper's `Q_n / n -> 0` for the adapted `Qpl`, from the paper's
    own second-moment input `int (Q_{t+1}-Q_t)^2 <= C log^4(t+2)`.
  * `tendsto_zero_div_eventually_lower` : `o(n)` gives the one-sided eventual budget
    `Q_n >= -delta n` for every `delta > 0`.
  * `ae_Qpl_lower` : that budget for `Qpl` at `delta = 1/64`.
  * `occ_bound_pointwise` / `ae_occ_of_proj_budgets` : the paper's `(occbnd)` from the *adapted*
    ledger, i.e. `sum 1{0 <= X_t^i <= M_t^j} <= max 1 (A+B) M_n^i + n/8`, using the verified
    `Jsum` budget and the projected `Q` budget.  No `QResidual` on `Qcomp` is used.
  * `ae_speed_of_proj_budgets` : the lower speed `7/(40 max 1 (A+B))` from that occupation front.

  The single remaining input here is the projected `(Vbound)`, i.e. the paper's upper budget for
  its *own* `H_{j,n}(X_n)`.  It is kept as an explicit hypothesis `hZ` in the exact shape the
  paper proves it.  It is deliberately **not** derived from the verified quenched `Zbudget_ae`:
  that theorem has an array-dependent onset, and a per-array onset does not pass through
  `condExp_mono` (for fixed `T` the set `{N_0 <= T}` need not be conull).  See the discussion at
  `proj_Z_budget_requires_own_argument`.
-/
import Swarm.ProjOptionalLedger
import Swarm.QProjVarianceHonest
import Swarm.BallisticInterfaceActual
import Swarm.MartingaleLimit

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmProjRes

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ## 1. The increments of `Qpl` and the strong law -/

/-- **The increments of `Qpl` are `projInc`.**  Definitional, but it is the identity that lets the
general martingale strong law of `MartingaleLimit` be applied to the concrete process. -/
theorem inc_Qpl (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) :
    MartingaleLimit.inc (fun T (U : Array N) => Qpl p m eps i j T U) t
      = projInc p m eps i j t := by
  funext U
  simp only [MartingaleLimit.inc_apply, Qpl, Finset.sum_range_succ, projInc]
  ring

/-- **Square integrability of the `Qpl` increments** is square integrability of `projInc`. -/
theorem integrable_sq_inc_Qpl {p : ℝ} (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ)
    (h2 : Integrable (fun U : Array N => projInc p m eps i j t U ^ 2) (arrayMeasure N)) :
    Integrable (fun U : Array N =>
      MartingaleLimit.inc (fun T (U : Array N) => Qpl p m eps i j T U) t U ^ 2)
      (arrayMeasure N) := by
  rw [inc_Qpl]
  exact h2

/-- **The paper's `Q_n / n -> 0` for the adapted projected ledger.**

The paper's display after `(Vbound)` is exactly this: `Q` is a martingale (here `martingale_Qpl`,
with no adaptedness or orthogonality hypothesis) and the squared increments obey
`int (Q_{t+1}-Q_t)^2 <= C log^4(t+2)`; the Hall--Heyde strong law then gives `Q_n/n -> 0`. -/
theorem Qpl_div_tendsto_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) {C : ℝ}
    (h2 : ∀ t : ℕ, Integrable (fun U : Array N => projInc p m eps i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ t : ℕ, ∫ U, projInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun T : ℕ => Qpl p m eps i j T U / T) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hQ := MartingaleLimit.martingale_strong_law_of_log_variance
    (μ := arrayMeasure N) (ℱ := enlFilt p m)
    (Q := fun T (U : Array N) => Qpl p m eps i j T U)
    (martingale_Qpl (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε)
    (fun k => integrable_sq_inc_Qpl m eps i j k (h2 k))
    (C := C) (fun k => by rw [inc_Qpl]; exact hvar k)
  have h0 : (fun U : Array N => Qpl p m eps i j 0 U) = fun _ => (0 : ℝ) := by
    funext U
    simp [Qpl]
  filter_upwards [hQ] with U hU
  simpa only [h0, sub_zero] using hU

/-! ## 2. From `o(n)` to the one-sided eventual budget -/

/-- **`o(n)` gives `Q_n >= -delta n` eventually.**  A deterministic argument about real
sequences, used twice below (the paper only ever uses the one-sided consequence). -/
theorem tendsto_zero_div_eventually_lower {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : Tendsto (fun T : ℕ => f T / T) atTop (𝓝 0)) :
    ∃ N₀ : ℕ, ∀ T ≥ N₀, -(δ * (T : ℝ)) ≤ f T := by
  have hleft : ∀ᶠ T : ℕ in atTop, -δ < f T / T :=
    (tendsto_order.1 h).1 _ (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hleft
  refine ⟨max N₀ 1, fun T hT => ?_⟩
  have hT1 : (1 : ℕ) ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hmain := hN₀ T (le_trans (le_max_left _ _) hT)
  have hmul := mul_lt_mul_of_pos_right hmain hTpos
  rw [div_mul_cancel₀ _ (ne_of_gt hTpos)] at hmul
  linarith

/-- **The one-sided projected budget at the ledger's rate `1/64`.** -/
theorem ae_Qpl_lower {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {C : ℝ}
    (h2 : ∀ t : ℕ, Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2)
      (arrayMeasure N))
    (hvar : ∀ t : ℕ, ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
      ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U := by
  filter_upwards [Qpl_div_tendsto_zero (N := N) hp0 hp1 m i j
    (by norm_num : (0 : ℝ) < 1 / 64) h2 hvar] with U hU
  exact tendsto_zero_div_eventually_lower (by norm_num : (0 : ℝ) < 1 / 64) hU

/-! ## 3. The paper's `(occbnd)` from the adapted ledger -/

/-- **The projected ledger on one almost-sure set, at every time.**  `(Vdrift)` summed with the
adapted `Zproj` and the centred martingale `Qpl`, from `proj_ledger_pointwise`. -/
theorem proj_ledger_all {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T : ℕ,
      occSum p m i j U T
        ≤ eps * (T : ℝ) + (Zproj p m eps i j T U - Zproj p m eps i j 0 U)
          + Jsum p m eps i j U T - Qpl p m eps i j T U := by
  rw [MeasureTheory.ae_all_iff]
  intro T
  filter_upwards [proj_ledger_pointwise (N := N) (p := p) (m := m) hp0 hp1 hm hij hε T] with U hU
  simpa only [occSum, Jsum] using hU

/-- **`(occbnd)` at one array**, from the three adapted-ledger budgets with abstract coefficients
and additive constants.  This is the exact arithmetic of the paper's "sum `(Vdrift)` and use
`(Jbound)` and `(Vbound)` and `Q_n = o(n)`" step, with the adapted `Z` and `Q`. -/
theorem occ_bound_pointwise {p : ℝ} {m : ℕ} {i j : Fin N}
    {A B KZ KJ KQ Kn eps δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hbud : eps + 4 * δ ≤ 1 / 8)
    (U : Array N)
    (hdrift : ∀ T : ℕ, occSum p m i j U T
      ≤ eps * (T : ℝ) + (Zproj p m eps i j T U - Zproj p m eps i j 0 U)
        + Jsum p m eps i j U T - Qpl p m eps i j T U)
    (hneg : ∀ n : ℕ,
      SwarmOccTwo.negCount (fun t => (trajectory p m U t).pos i) n ≤ Kn)
    (hZ : ∀ T ≥ N₀,
      Zproj p m eps i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ) + KZ)
    (hJ : ∀ T ≥ N₀,
      Jsum p m eps i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ) + KJ)
    (hQ : ∀ T ≥ N₀, -(δ * (T : ℝ)) - KQ ≤ Qpl p m eps i j T U) :
    ∀ n ≥ max N₀ ⌈max 0 (KZ + KJ + KQ + Kn - Zproj p m eps i j 0 U) / δ⌉₊,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
  intro n hn
  have hdrift' : ∀ k : ℕ,
      SwarmOccTwo.occTwo (fun t => (trajectory p m U t).pos i)
          (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) k
        ≤ eps * (k : ℝ) + ((fun T => Zproj p m eps i j T U) k - (fun T => Zproj p m eps i j T U) 0)
          + (fun T => Jsum p m eps i j U T) k - (fun T => Qpl p m eps i j T U) k := by
    intro k
    have hk := hdrift k
    rw [SwarmBIA.occSum_eq_OccTwoOfMax, SwarmBIA.OccTwoOfMax_eq_occTwo] at hk
    exact hk
  have hZ' : ∀ k ≥ N₀,
      (fun T => Zproj p m eps i j T U) k
        ≤ A * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) k : ℤ) : ℝ)
          + δ * (k : ℝ) + KZ := by
    intro k hk
    have h := hZ k hk
    rwa [SwarmBIA.runMax_eq_SwarmSpeed_runMax U i k] at h
  have hJ' : ∀ k ≥ N₀,
      (fun T => Jsum p m eps i j U T) k
        ≤ B * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) k : ℤ) : ℝ)
          + δ * (k : ℝ) + KJ := by
    intro k hk
    have h := hJ k hk
    rwa [SwarmBIA.runMax_eq_SwarmSpeed_runMax U i k] at h
  have hcoef := SwarmBIA.occbnd_of_twoSided_coef_le
    (A := A) (B := B) (KZ := KZ) (KJ := KJ) (KQ := KQ) (Kn := Kn) (ε := eps) (δ := δ) (N := N₀)
    (u := fun t => (trajectory p m U t).pos i)
    (v := SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j))
    (Z := fun k => Zproj p m eps i j k U) (J := fun k => Jsum p m eps i j U k)
    (Q := fun k => Qpl p m eps i j k U)
    (by simp [trajectory_zero, initialWalkState]) hδ hbud hdrift' hneg hZ' hJ' hQ n hn
  have hOcc : SwarmOccTwo.OccOfMax p m N i j U n
      = SwarmSpeed.occ (fun t => (trajectory p m U t).pos i)
          (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) n := rfl
  rw [hOcc]
  exact hcoef

/-- **The paper's `(occbnd)` from the adapted-ledger budgets**, simultaneously for every ordered
pair on one almost-sure set.  The additive constants are all zero, as in the paper's
`(Vbound)`, `(Jbound)`, `Q_n = o(n)`. -/
theorem ae_occ_of_proj_budgets {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {eps δ A B : ℝ} (hε : 0 < eps) (hδ : 0 < δ) (hbud : eps + 4 * δ ≤ 1 / 8)
    (hZ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m eps i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    (hJ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m eps i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    (hQ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qpl p m eps i j T U) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
  have hmain : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
    intro i j hij
    filter_upwards [proj_ledger_all (N := N) hp0 hp1 hm hij hε, hZ i j hij, hJ i j hij,
      hQ i j hij, SwarmOccTwo.ae_negCount_bdd (N := N) hp0 hp1 hm i j hij]
      with U hled hZU hJU hQU hneg
    obtain ⟨NZ, hZ⟩ := hZU
    obtain ⟨NJ, hJ'⟩ := hJU
    obtain ⟨NQ, hQ'⟩ := hQU
    obtain ⟨K, hK⟩ := hneg
    refine ⟨max (max NZ (max NJ NQ)) ⌈max 0 (0 + 0 + 0 + (K : ℝ) - Zproj p m eps i j 0 U) / δ⌉₊,
      fun n hn => ?_⟩
    exact occ_bound_pointwise (p := p) (m := m) (i := i) (j := j) (A := A) (B := B)
      (KZ := 0) (KJ := 0) (KQ := 0) (Kn := (K : ℝ)) (eps := eps) (δ := δ)
      (N₀ := max NZ (max NJ NQ)) hδ hbud U hled (fun k => hK k)
      (fun T hT => by simpa only [add_zero] using hZ T (le_trans (le_max_left _ _) hT))
      (fun T hT => by
        simpa only [add_zero] using
          hJ' T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT))
      (fun T hT => by
        have := hQ' T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
        linarith)
      n hn
  have hinner : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, i ≠ j → ∃ N₁ : ℕ,
      ∀ n ≥ N₁, SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
    intro i
    refine Filter.eventually_all.mpr (fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun U hne => absurd hij hne
    · exact (hmain i j hij).mono fun U hU _ => hU
  exact Filter.eventually_all.mpr hinner


/-! ## 4. The concrete corollary: `(occbnd)` at the actual trajectory

The only hypothesis left below is the projected `(Vbound)` `hZ`, i.e. the paper's upper budget for
its *own* `H_{j,n}(X_n)`.  Everything else is discharged: the `Jsum` budget is the verified
`Jsum_eventual`, the `Q` budget is `ae_Qpl_lower` (the strong law of §1), and the ledger identity
`(Vdrift)` is `proj_ledger_pointwise`.  In particular **no** budget for the raw `Qcomp` and **no**
terminal-defect budget is used. -/

/-- **`(occbnd)` from the projected `(Vbound)`.**  For almost every array and every ordered pair,
the one-sided count `#{t : X_t^i <= M_t^j}` is eventually at most
`max 1 (A + B) * M_n^i + n/8`, where `A = targetParam p m + 1` is the paper's `Z` coefficient and
`B` is the verified `J` coefficient. -/
theorem ae_occ_of_projected_Vbound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hZ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U
        ≤ (SwarmSpatial.targetParam p m + 1) * ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ))
    {C : ℝ}
    (h2 : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 ((SwarmSpatial.targetParam p m + 1) + B) * ((runMax p m U i n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hJall : ∀ i j : Fin N, ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ) :=
    fun i j => Swarming.Enl.JBudgetActual.Jsum_eventual (N := N) hp0 hp1 hm
      (by norm_num : (0 : ℝ) < 1 / 64)
  choose B hBpos hJB using hJall
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hBtotpos : 0 < ∑ i : Fin N, ∑ j : Fin N, B i j := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 < ∑ j : Fin N, B i j :=
      fun i _ => Finset.sum_pos (fun j _ => hBpos i j) Finset.univ_nonempty
    exact Finset.sum_pos hnn Finset.univ_nonempty
  have hBle : ∀ i j : Fin N, B i j ≤ ∑ i : Fin N, ∑ j : Fin N, B i j := by
    intro i j
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun k : Fin N => ∑ j : Fin N, B k j)
      (fun k _ => Finset.sum_nonneg (fun l _ => (hBpos k l).le)) (Finset.mem_univ i))
    exact Finset.single_le_sum (fun l _ => (hBpos i l).le) (Finset.mem_univ j)
  have hJtot : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T
        ≤ (∑ i : Fin N, ∑ j : Fin N, B i j) * ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ) := by
    intro i j hij
    filter_upwards [hJB i j] with U hU
    obtain ⟨N₀, hN₀⟩ := hU
    refine ⟨N₀, fun T hT => ?_⟩
    have hM : (0 : ℝ) ≤ ((runMax p m U i T : ℤ) : ℝ) := by
      have h := zero_le_runMax p m U i T
      exact_mod_cast h
    have := mul_le_mul_of_nonneg_right (hBle i j) hM
    linarith [hN₀ T hT]
  have hQ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U :=
    fun i j hij => ae_Qpl_lower (N := N) hp0 hp1 m i j (h2 i j hij) (hvar i j hij)
  exact ⟨_, hBtotpos, ae_occ_of_proj_budgets (N := N) hp0 hp1 hm
    (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num)
    hZ hJtot hQ⟩

/-! ## 5. The lower speed from the adapted ledger -/

/-- **The paper's lower speed bound from the adapted ledger.**  `7/(40 C) <= liminf X^i_n/n` with
`C = max 1 (A+B)` the occupation coefficient, simultaneously for every walker on an almost-sure
set.  Uses the verified oscillation `SwarmHosc.trajectory_hosc`, the verified upper bound
`X^i_n/n <= 1`, and `SwarmSpeed.liminf_speed`; the only probabilistic input is the projected
`(Vbound)`. -/
theorem ae_speed_of_projected_Vbound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hZ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U
        ≤ (SwarmSpatial.targetParam p m + 1) * ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ))
    {C : ℝ}
    (h2 : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / (40 * K)
        ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  obtain ⟨B, hBpos, hocc⟩ := ae_occ_of_projected_Vbound (N := N) hp0 hp1 hm hN hZ h2 hvar
  set A : ℝ := SwarmSpatial.targetParam p m + 1 with hA
  set K : ℝ := max 1 (A + B) with hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hKpos, ?_⟩
  have hosc := SwarmHosc.trajectory_hosc (p := p) hp0 hp1 m N
  filter_upwards [hocc, hosc] with U hU hoscU i
  obtain ⟨j, hji⟩ := SwarmHosc.exists_ne_of_two_le hN i
  obtain ⟨N₁, hN₁⟩ := hU i j (Ne.symm hji)
  obtain ⟨N₂, hN₂⟩ := hU j i hji
  have hkey := SwarmSpeed.liminf_speed
    (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j)
    (by simp [trajectory_zero, initialWalkState])
    (C := K) (B := 1) (le_max_left _ _) (N := max N₁ N₂)
    (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
    (hoscU i) (SwarmOccTwo.actual_pos_div_le_one (N := N) (p := p) (m := m) hp0 hp1 i U)
  simpa using hkey


/-! ## 6. From the paper's increment-size bound to the `log^4` second moment

The paper does not assume a second-moment bound directly.  It proves

    |Z_{n+1} - Z_n + J_{n+1}| <= C_eps (1 + max_{0 <= x <= n+1} h_j(x))      (a.s.)

and deduces, from `(maxmom)` `E[(1+max_{x<=n+1} h_j(x))^2] <= K log^4(n+2)`, that the martingale
increments obey `E[(Q_{n+1}-Q_n)^2] <= C log^4(n+2)`.

This section carries out that step for the adapted ledger.  Write
`D_t = Z_{t+1} - Z_t + J_{t+1}`.  Then `projInc t` is `D_t` minus its `F_t`-conditional mean
(`projInc_eq_Dinc_sub_condExp`), so the elementary inequality `(a-b)^2 <= 2a^2 + 2b^2` together with
the `L^2` contraction of conditional expectation (`ProjHonest.integral_sq_condExp_le_enl`) gives

    int (Q_{t+1}-Q_t)^2 = int (projInc t)^2 <= 4 int D_t^2 <= 4 C^2 K log^4(t+2).

Only the constant degrades from `C^2 K` to `4 C^2 K`, which is immaterial: the `C` slot of
`Qpl_div_tendsto_zero` is an arbitrary real.
-/

/-- The uncentred projected ledger increment `D_t = Z_{t+1}-Z_t+J_{t+1}`. -/
noncomputable def Dinc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) : Array N → ℝ :=
  fun U => Zproj p m eps i j (t + 1) U - Zproj p m eps i j t U + Jcorr p m eps i j U t

/-- `D_t` is strongly measurable with respect to `F_{t+1}`. -/
theorem stronglyMeasurable_Dinc {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (eps : ℝ)
    (i j : Fin N) : StronglyMeasurable[enlFilt p m (t + 1)] (Dinc p m eps i j t) := by
  have hmono : (enlFilt p m t : MeasurableSpace (Array N)) ≤ enlFilt p m (t + 1) :=
    Filtration.mono (enlFilt p m) (Nat.le_succ t)
  have h1 : StronglyMeasurable[enlFilt p m (t + 1)] (Zproj p m eps i j (t + 1)) :=
    stronglyMeasurable_Zproj p m eps i j (t + 1)
  have h2 : StronglyMeasurable[enlFilt p m (t + 1)] (Zproj p m eps i j t) :=
    (stronglyMeasurable_Zproj p m eps i j t).mono hmono
  have h3 : StronglyMeasurable[enlFilt p m (t + 1)] (fun U : Array N => Jcorr p m eps i j U t) :=
    (measurable_Jcorr_enl_succ (N := N) (p := p) hp m t i j eps).stronglyMeasurable
  exact (h1.sub h2).add h3

/-- **`projInc t` is `D_t` minus its `F_t`-conditional mean.**  This is `Edrift` identified with
the conditional expectation of the adapted ledger's increment (`condExp_proj_ledger_eq_Edrift`). -/
theorem projInc_eq_Dinc_sub_condExp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    projInc p m eps i j t
      =ᵐ[arrayMeasure N] Dinc p m eps i j t
        - condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) := by
  have h : condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t)
      =ᵐ[arrayMeasure N] fun U => Edrift p m eps (fun r => alphaFun p m r i) i j U t :=
    condExp_proj_ledger_eq_Edrift (N := N) hp0 hp1 m t i j hε
  filter_upwards [h] with U hU
  simp only [projInc, Dinc, Pi.sub_apply] at hU ⊢
  rw [hU]

/-- Elementary square inequality: `(a-b)^2 <= 2 a^2 + 2 b^2`. -/
lemma sq_sub_le_two_mul (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- **Square integrability of the centred increment from the uncentred one.** -/
theorem integrable_sq_projInc_of_sq_Dinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps)
    (hD2 : Integrable (fun U : Array N => Dinc p m eps i j t U ^ 2) (arrayMeasure N)) :
    Integrable (fun U : Array N => projInc p m eps i j t U ^ 2) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsmD : AEStronglyMeasurable (Dinc p m eps i j t) (arrayMeasure N) :=
    ((stronglyMeasurable_Dinc hp0.le m t eps i j).mono
      (Filtration.le (enlFilt p m) (t + 1))).aestronglyMeasurable
  have hc2 : Integrable (fun U : Array N =>
      condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2) (arrayMeasure N) :=
    ProjHonest.integrable_sq_condExp_enl (N := N) (p := p) m t hsmD hD2
  have hsmP : AEStronglyMeasurable (fun U : Array N => projInc p m eps i j t U ^ 2)
      (arrayMeasure N) :=
    ((stronglyMeasurable_projInc hp0.le m t eps i j).mono
      (Filtration.le (enlFilt p m) (t + 1))).aestronglyMeasurable.pow 2
  refine Integrable.mono' ((hD2.const_mul 2).add (hc2.const_mul 2)) hsmP ?_
  filter_upwards [projInc_eq_Dinc_sub_condExp (N := N) hp0 hp1 (m := m) t i j hε] with U hU
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hU]
  exact sq_sub_le_two_mul (Dinc p m eps i j t U)
    (condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U)

/-- **Contraction, with the constant `4`.**  `int (projInc)^2 <= 4 int D^2`.  The factor is
irrelevant (`C` is a free real in `Qpl_div_tendsto_zero`), and it makes the proof elementary:
`(f - E[f|F])^2 <= 2 f^2 + 2 (E[f|F])^2` plus `L^2` conditional Jensen. -/
theorem integral_sq_projInc_le_of_sq_Dinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps)
    (hD2 : Integrable (fun U : Array N => Dinc p m eps i j t U ^ 2) (arrayMeasure N)) :
    ∫ U, projInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 4 * ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsmD : AEStronglyMeasurable (Dinc p m eps i j t) (arrayMeasure N) :=
    ((stronglyMeasurable_Dinc hp0.le m t eps i j).mono
      (Filtration.le (enlFilt p m) (t + 1))).aestronglyMeasurable
  have hcj : ∫ U, condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2
      ∂(arrayMeasure N) ≤ ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N) :=
    ProjHonest.integral_sq_condExp_le_enl (N := N) (p := p) m t hsmD hD2
  have hc2 : Integrable (fun U : Array N =>
      condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2) (arrayMeasure N) :=
    ProjHonest.integrable_sq_condExp_enl (N := N) (p := p) m t hsmD hD2
  have hP2 : Integrable (fun U : Array N => projInc p m eps i j t U ^ 2) (arrayMeasure N) :=
    integrable_sq_projInc_of_sq_Dinc (N := N) hp0 hp1 m t i j hε hD2
  have hInt : Integrable (fun U : Array N => 2 * Dinc p m eps i j t U ^ 2
      + 2 * condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2)
      (arrayMeasure N) :=
    (hD2.const_mul 2).add (hc2.const_mul 2)
  have hbound : ∀ᵐ U ∂(arrayMeasure N), projInc p m eps i j t U ^ 2
      ≤ 2 * Dinc p m eps i j t U ^ 2
        + 2 * condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2 := by
    filter_upwards [projInc_eq_Dinc_sub_condExp (N := N) hp0 hp1 (m := m) t i j hε] with U hU
    rw [hU]
    exact sq_sub_le_two_mul _ _
  have hmono := integral_mono_ae hP2 hInt hbound
  have hsplit : ∫ U, (2 * Dinc p m eps i j t U ^ 2
      + 2 * condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2)
        ∂(arrayMeasure N)
      = 2 * ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        + 2 * ∫ U, condExp (enlFilt p m t) (arrayMeasure N) (Dinc p m eps i j t) U ^ 2
            ∂(arrayMeasure N) := by
    rw [integral_add (hD2.const_mul 2) (hc2.const_mul 2), integral_const_mul,
      integral_const_mul]
  rw [hsplit] at hmono
  linarith

/-- **Square integrability of `D_t` from the paper's increment-size domination.** -/
theorem integrable_sq_Dinc_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m t : ℕ) (eps : ℝ)
    (i j : Fin N) {C : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m eps i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N)) :
    Integrable (fun U : Array N => Dinc p m eps i j t U ^ 2) (arrayMeasure N) := by
  have hsm : AEStronglyMeasurable (Dinc p m eps i j t) (arrayMeasure N) :=
    ((stronglyMeasurable_Dinc hp0.le m t eps i j).mono
      (Filtration.le (enlFilt p m) (t + 1))).aestronglyMeasurable
  refine Integrable.mono' ((hYint t).const_mul (C ^ 2)) (hsm.pow 2) ?_
  filter_upwards [hdom t] with U hU
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc |Dinc p m eps i j t U| ^ 2 ≤ (C * (1 + Y t U)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hU 2
    _ = C ^ 2 * (1 + Y t U) ^ 2 := by ring

/-- **The second-moment bound from the domination and `(maxmom)`.** -/
theorem integral_sq_Dinc_le_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m t : ℕ) (eps : ℝ)
    (i j : Fin N) {C : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m eps i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N)) :
    ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ C ^ 2 * ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N) := by
  have hD2 := integrable_sq_Dinc_of_dominated (N := N) hp0 m t eps i j hC hdom hYint
  have hmaj : Integrable (fun U : Array N => C ^ 2 * (1 + Y t U) ^ 2) (arrayMeasure N) :=
    (hYint t).const_mul _
  have hb : ∀ᵐ U ∂(arrayMeasure N), Dinc p m eps i j t U ^ 2 ≤ C ^ 2 * (1 + Y t U) ^ 2 := by
    filter_upwards [hdom t] with U hU
    rw [← sq_abs]
    calc |Dinc p m eps i j t U| ^ 2 ≤ (C * (1 + Y t U)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hU 2
      _ = C ^ 2 * (1 + Y t U) ^ 2 := by ring
  calc ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, C ^ 2 * (1 + Y t U) ^ 2 ∂(arrayMeasure N) := integral_mono_ae hD2 hmaj hb
    _ = C ^ 2 * ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N) := integral_const_mul ..

/-- **The paper's `Q_n/n -> 0` from its own two inputs.**  `hdom` is the display
`|Z_{n+1}-Z_n+J_{n+1}| <= C_eps (1 + max_{x <= n+1} h_j(x))` and `hYlog` is `(maxmom)`. -/
theorem Qpl_div_tendsto_zero_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) {eps C K : ℝ} (hε : 0 < eps) (hC : 0 ≤ C)
    {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m eps i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun T : ℕ => Qpl p m eps i j T U / T) atTop (𝓝 0) := by
  have h2 : ∀ t : ℕ, Integrable (fun U : Array N => projInc p m eps i j t U ^ 2)
      (arrayMeasure N) :=
    fun t => integrable_sq_projInc_of_sq_Dinc (N := N) hp0 hp1 m t i j hε
      (integrable_sq_Dinc_of_dominated (N := N) hp0 m t eps i j hC hdom hYint)
  refine Qpl_div_tendsto_zero (N := N) hp0 hp1 m i j hε h2 (C := 4 * C ^ 2 * K) (fun t => ?_)
  have h1 := integral_sq_projInc_le_of_sq_Dinc (N := N) hp0 hp1 m t i j hε
    (integrable_sq_Dinc_of_dominated (N := N) hp0 m t eps i j hC hdom hYint)
  have h2' := integral_sq_Dinc_le_of_dominated (N := N) hp0 m t eps i j hC hdom hYint
  calc ∫ U, projInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 4 * ∫ U, Dinc p m eps i j t U ^ 2 ∂(arrayMeasure N) := h1
    _ ≤ 4 * (C ^ 2 * ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)) :=
        mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ ≤ 4 * (C ^ 2 * (K * (Real.log ((t : ℝ) + 2)) ^ 4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hYlog t) (by positivity)) (by norm_num)
    _ = 4 * C ^ 2 * K * (Real.log ((t : ℝ) + 2)) ^ 4 := by ring

/-- **The one-sided projected budget at `eps = 1/64` from the paper's two inputs.** -/
theorem ae_Qpl_lower_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U := by
  filter_upwards [Qpl_div_tendsto_zero_of_dominated (N := N) hp0 hp1 m i j
    (by norm_num : (0 : ℝ) < 1 / 64) hC hdom hYint hYlog] with U hU
  exact tendsto_zero_div_eventually_lower (by norm_num : (0 : ℝ) < 1 / 64) hU


/-! ## 7. The same corollaries with the paper's own hypotheses

`hdom` is the paper's display `|Z_{n+1}-Z_n+J_{n+1}| <= C_eps (1 + max_{x <= n+1} h_j(x))` for the
adapted ledger, and `hYlog` is `(maxmom)`.  These two are the *only* stochastic inputs to the
projected `Q` budget; `hZ` remains the projected `(Vbound)`. -/

/-- **The `Q`-side second-moment data from the paper's two inputs.** -/
theorem projInc_sq_data_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    (∀ t : ℕ, Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2)
        (arrayMeasure N))
      ∧ (∀ t : ℕ, ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ (4 * C ^ 2 * K) * (Real.log ((t : ℝ) + 2)) ^ 4) := by
  have hD : ∀ t : ℕ, Integrable (fun U : Array N => Dinc p m (1 / 64) i j t U ^ 2)
      (arrayMeasure N) :=
    fun t => integrable_sq_Dinc_of_dominated (N := N) hp0 m t (1 / 64) i j hC hdom hYint
  refine ⟨fun t => integrable_sq_projInc_of_sq_Dinc (N := N) hp0 hp1 m t i j
    (by norm_num : (0 : ℝ) < 1 / 64) (hD t), fun t => ?_⟩
  have h1 := integral_sq_projInc_le_of_sq_Dinc (N := N) hp0 hp1 m t i j
    (by norm_num : (0 : ℝ) < 1 / 64) (hD t)
  have h2' := integral_sq_Dinc_le_of_dominated (N := N) hp0 m t (1 / 64) i j hC hdom hYint
  calc ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 4 * ∫ U, Dinc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N) := h1
    _ ≤ 4 * (C ^ 2 * ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)) :=
        mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ ≤ 4 * (C ^ 2 * (K * (Real.log ((t : ℝ) + 2)) ^ 4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hYlog t) (by positivity)) (by norm_num)
    _ = 4 * C ^ 2 * K * (Real.log ((t : ℝ) + 2)) ^ 4 := by ring

/-- **`(occbnd)` for the actual trajectory from the paper's hypotheses plus the projected
`(Vbound)`.** -/
theorem ae_occ_of_projected_Vbound_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hZ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U
        ≤ (SwarmSpatial.targetParam p m + 1) * ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ))
    {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 ((SwarmSpatial.targetParam p m + 1) + B) * ((runMax p m U i n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
  have h2 : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N) :=
    fun i j hij t => (projInc_sq_data_of_dominated (N := N) hp0 hp1 m i j hC
      (hdom i j hij) hYint hYlog).1 t
  have hvar : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ (4 * C ^ 2 * K) * (Real.log ((t : ℝ) + 2)) ^ 4 :=
    fun i j hij t => (projInc_sq_data_of_dominated (N := N) hp0 hp1 m i j hC
      (hdom i j hij) hYint hYlog).2 t
  exact ae_occ_of_projected_Vbound (N := N) hp0 hp1 hm hN hZ h2 hvar

/-- **The lower speed for the actual trajectory from the paper's hypotheses plus the projected
`(Vbound)`**: a positive constant `7/(40 K)`, independent of `N`, with
`7/(40 K) <= liminf X^i_n/n` almost surely for every walker. -/
theorem ae_speed_of_projected_Vbound_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hZ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U
        ≤ (SwarmSpatial.targetParam p m + 1) * ((runMax p m U i T : ℤ) : ℝ)
          + (1 / 64) * (T : ℝ))
    {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / (40 * K')
        ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  have h2 : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N) :=
    fun i j hij t => (projInc_sq_data_of_dominated (N := N) hp0 hp1 m i j hC
      (hdom i j hij) hYint hYlog).1 t
  have hvar : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ (4 * C ^ 2 * K) * (Real.log ((t : ℝ) + 2)) ^ 4 :=
    fun i j hij t => (projInc_sq_data_of_dominated (N := N) hp0 hp1 m i j hC
      (hdom i j hij) hYint hYlog).2 t
  exact ae_speed_of_projected_Vbound (N := N) hp0 hp1 hm hN hZ h2 hvar


/-! ## 8. What transferring the quenched `(Vbound)` to the projected ledger would need

The verified quenched budget `ZBudget.Zbudget_ae_runMax` reads

    for almost every array there is an onset N_0 (depending on the array) such that for all
    T >= N_0,   Zpot_T <= (targetParam + 1) M_T^i + T/64.

The projected ledger needs the same display with `Zproj = E[Zpot_T | F_T]`.  Monotonicity of the
conditional expectation (`condExp_mono`) does give it, but **only** from the stronger
deterministic-onset form "for almost every array, for *every* `T`".  The per-array onset is not
enough: for a fixed `T` the set `{N_0 <= T}` is not conull, so `Zpot_T <= majorant` is not an
almost-sure inequality at fixed `T` and `condExp_mono` cannot be applied to it.  This is exactly
the "do not transfer a raw almost-sure upper bound through `condExp` naively" obstruction, and
`ae_Zproj_le_of_ae_Zpot_le` below records the exact strength that *is* sufficient.

(For the paper this is not an issue: its `Z` is `H_{j,n}(X_n)` from the start, so `(Vbound)` is
proved for the projected object directly, from `(projH)` and `(spav)`.  Proving it in Lean is the
projected-`(Vbound)` obligation, kept as the hypothesis `hZ` of §§4–5.)
-/

/-- The record majorant `A * M_T^i + c * T` is `F_T`-strongly measurable. -/
theorem stronglyMeasurable_runMax_majorant (p : ℝ) (m T : ℕ) (i : Fin N) (A c : ℝ) :
    StronglyMeasurable[enlFilt p m T]
      (fun U : Array N => A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ)) := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have h1 : Measurable[enlFilt p m T] (fun U : Array N => ((runMax p m U i T : ℤ) : ℝ)) :=
    hcast.comp (VdriftAssembly.measurable_runMax_enl p m T i)
  exact ((h1.const_mul A).add_const (c * (T : ℝ))).stronglyMeasurable

/-- The record majorant is integrable: `|M_T^i| <= T` and `M_T^i >= 0`. -/
theorem integrable_runMax_majorant (p : ℝ) (m T : ℕ) (i : Fin N) (A c : ℝ) :
    Integrable (fun U : Array N => A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ))
      (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsm := stronglyMeasurable_runMax_majorant (N := N) p m T i A c
  refine Integrable.of_bound (hsm.mono (Filtration.le (enlFilt p m) T)).aestronglyMeasurable
    (|A| * (T : ℝ) + |c * (T : ℝ)|) ?_
  filter_upwards with U
  have h0 : (0 : ℝ) ≤ ((runMax p m U i T : ℤ) : ℝ) := by
    have h := zero_le_runMax p m U i T
    exact_mod_cast h
  have hT : ((runMax p m U i T : ℤ) : ℝ) ≤ (T : ℝ) := by
    have h := ZBudget.runMax_le_time p m U i T
    exact_mod_cast h
  rw [Real.norm_eq_abs]
  have h2 : |A * ((runMax p m U i T : ℤ) : ℝ)| ≤ |A| * (T : ℝ) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg A)
    rwa [abs_of_nonneg h0]
  calc |A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ)|
      ≤ |A * ((runMax p m U i T : ℤ) : ℝ)| + |c * (T : ℝ)| := abs_add_le _ _
    _ ≤ |A| * (T : ℝ) + |c * (T : ℝ)| := by linarith

/-- **The honest transfer.**  If the quenched budget holds on one conull set *for every time*
then the optional projection inherits it, because the majorant is `F_T`-measurable.  The verified
`Zbudget_ae_runMax` has a per-array onset and therefore does **not** supply `hraw`. -/
theorem ae_Zproj_le_of_ae_Zpot_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {eps A c : ℝ} (hε : 0 < eps)
    (hraw : ∀ᵐ U ∂(arrayMeasure N), ∀ T : ℕ,
      Zpot p m eps i j U T ≤ A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ T : ℕ,
      Zproj p m eps i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  rw [MeasureTheory.ae_all_iff] at hraw ⊢
  intro T
  have hmono := condExp_mono (m := enlFilt p m T) (μ := arrayMeasure N)
    (f := fun U : Array N => Zpot p m eps i j U T)
    (g := fun U : Array N => A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ))
    (integrable_Zpot (N := N) hp0 hp1 m i j hε T)
    (integrable_runMax_majorant (N := N) p m T i A c) (hraw T)
  have hfix : condExp (enlFilt p m T) (arrayMeasure N)
      (fun U : Array N => A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ))
      =ᵐ[arrayMeasure N] fun U => A * ((runMax p m U i T : ℤ) : ℝ) + c * (T : ℝ) :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((enlFilt p m).le T)
      (stronglyMeasurable_runMax_majorant (N := N) p m T i A c)
      (integrable_runMax_majorant (N := N) p m T i A c))
  filter_upwards [hmono, hfix] with U h1 h2
  rw [Zproj_def]
  exact le_trans h1 (le_of_eq h2)


/-! ## 9. The paper's literal `o(n)` form, for the adapted ledger

The paper states its three inputs as `Z_n <= C M_n^i + o(n)`, `sum |J| <= C M_n^i + O(1)` and
`Q_n = o(n)`.  This section restates the adapted-ledger interface in exactly that form, so the
paper's own displays are the hypotheses and nothing is fixed at the numerical rate `1/64` except
through the constant bookkeeping `eps + 4 delta <= 1/8`.
-/

/-- **`Q_n = o(n)` for `Qpl`,** from the paper's second-moment input. -/
theorem ae_Qpl_o {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N) {C : ℝ}
    (h2 : ∀ t : ℕ, Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2)
      (arrayMeasure N))
    (hvar : ∀ t : ℕ, ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
      ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U := by
  filter_upwards [Qpl_div_tendsto_zero (N := N) hp0 hp1 m i j
    (by norm_num : (0 : ℝ) < 1 / 64) h2 hvar] with U hU δ hδ
  exact tendsto_zero_div_eventually_lower hδ hU

/-- **`Q_n = o(n)` for `Qpl` from the paper's own two inputs** (increment-size domination and
`(maxmom)`). -/
theorem ae_Qpl_o_of_dominated {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N), |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U := by
  filter_upwards [Qpl_div_tendsto_zero_of_dominated (N := N) hp0 hp1 m i j
    (by norm_num : (0 : ℝ) < 1 / 64) hC hdom hYint hYlog] with U hU δ hδ
  exact tendsto_zero_div_eventually_lower hδ hU

/-- **The adapted-ledger interface in the paper's `o(n)` form.**  `Zproj` is the paper's
`H_{j,n}(X_n^i) - F_{b_n}(X_n^i - M_n^j)`, `Qpl` its martingale `Q`. -/
def InterfacesOProj (p : ℝ) (m N : ℕ) (A B : ℝ) (i j : Fin N) : Prop :=
  ∀ᵐ U ∂(arrayMeasure N),
    (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    ∧ (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    ∧ (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U)

/-- **`(occbnd)` from the adapted interface in `o(n)` form.**  The onsets are merged by taking a
maximum, and the rate is instantiated at `1/64`, where `1/64 + 4/64 = 5/64 <= 1/8`. -/
theorem ae_occ_of_interfacesOProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {A B : ℝ}
    (h : ∀ i j : Fin N, i ≠ j → InterfacesOProj p m N A B i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
  refine ae_occ_of_proj_budgets (N := N) hp0 hp1 hm
    (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num)
    ?_ ?_ ?_
  · intro i j hij
    filter_upwards [h i j hij] with U hU
    obtain ⟨hZ, -, -⟩ := hU
    exact hZ (1 / 64) (by norm_num)
  · intro i j hij
    filter_upwards [h i j hij] with U hU
    obtain ⟨-, hJ, -⟩ := hU
    exact hJ (1 / 64) (by norm_num)
  · intro i j hij
    filter_upwards [h i j hij] with U hU
    obtain ⟨-, -, hQ⟩ := hU
    exact hQ (1 / 64) (by norm_num)

/-- **The lower speed from the adapted interface in `o(n)` form.**  The constant
`7/(40 max 1 (A+B))` is positive and independent of `N`, exactly as in the paper's
`kappa(m,p)`. -/
theorem ae_speed_of_interfacesOProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {A B : ℝ}
    (h : ∀ i j : Fin N, i ≠ j → InterfacesOProj p m N A B i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / (40 * max 1 (A + B))
        ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  have hocc := ae_occ_of_interfacesOProj (N := N) hp0 hp1 hm h
  have hosc := SwarmHosc.trajectory_hosc (p := p) hp0 hp1 m N
  have hK1 : (1 : ℝ) ≤ max 1 (A + B) := le_max_left _ _
  filter_upwards [hocc, hosc] with U hU hoscU i
  obtain ⟨j, hji⟩ := SwarmHosc.exists_ne_of_two_le hN i
  obtain ⟨N₁, hN₁⟩ := hU i j (Ne.symm hji)
  obtain ⟨N₂, hN₂⟩ := hU j i hji
  have hkey := SwarmSpeed.liminf_speed
    (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j)
    (by simp [trajectory_zero, initialWalkState])
    (C := max 1 (A + B)) (B := 1) hK1 (N := max N₁ N₂)
    (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
    (hoscU i) (SwarmOccTwo.actual_pos_div_le_one (N := N) (p := p) (m := m) hp0 hp1 i U)
  simpa using hkey

/-- **Positivity of the paper's constant** `7/(40 max 1 (A+B))`. -/
theorem speedConst_pos (A B : ℝ) : (0 : ℝ) < 7 / (40 * max 1 (A + B)) := by
  have h : (0 : ℝ) < max 1 (A + B) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity


/-! ## 10. The exact residual: `Qcomp` versus the adapted martingale `Qpl`

The raw ledger and the adapted (`Qpl`) ledger differ by exactly the *realised* terminal potential
minus its projection, with the `t = 0` correction:

    Qcomp_T = Qpl_T + (Zpot_T - E[Zpot_T | F_T]) - (Zpot_0 - E[Zpot_0 | F_0]).

Both sides telescope to the same `sum J_{t+1} - sum E_t`, so this is an identity of real numbers,
not an estimate.  It shows precisely what a budget for the raw `Qcomp` costs beyond the projected
strong law of §1: a *one-sided* almost-sure budget for the terminal defect
`Zpot_T - E[Zpot_T|F_T]`, which is **not** obtainable from the raw `(Vbound)` by monotonicity of
`condExp` (§8) and is not needed anywhere in the paper's argument.  `qresidual_of_Qpl_and_defect`
records this as an explicit reduction to the named target `SwarmActualBudget.QResidual`.
-/

/-- **The exact identity `Qcomp = Qpl + terminal defect`,** at every array and every time. -/
theorem Qcomp_eq_Qpl_add_defect (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    Qcomp p m eps (fun r => SwarmCross.alphaFun p m r i) i j U T
      = Qpl p m eps i j T U
        + ((Zpot p m eps i j U T - Zproj p m eps i j T U)
          - (Zpot p m eps i j U 0 - Zproj p m eps i j 0 U)) := by
  have hQ := Qpl_eq p m eps i j T U
  unfold Qcomp
  rw [hQ]
  ring

/-- **`QResidual` from the adapted strong law plus a one-sided terminal-defect budget.**  The
first input is `ae_Qpl_lower`-shaped (`Qpl >= -(T/128)` eventually); the second is the *only*
extra input the quenched ledger needs, and it is the one the paper never has to pay. -/
theorem qresidual_of_Qpl_and_defect {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hQ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U)
    (hd : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 128 : ℝ) * (T : ℝ))
        ≤ (Zpot p m (1 / 64) i j U T - Zproj p m (1 / 64) i j T U)
          - (Zpot p m (1 / 64) i j U 0 - Zproj p m (1 / 64) i j 0 U)) :
    SwarmActualBudget.QResidual p m N := by
  intro i j hij
  filter_upwards [hQ i j hij, hd i j hij] with U hQU hdU
  obtain ⟨NQ, hQ'⟩ := hQU
  obtain ⟨Nd, hd'⟩ := hdU
  refine ⟨max NQ Nd, fun T hT => ?_⟩
  have h1 := hQ' T (le_trans (le_max_left _ _) hT)
  have h2 := hd' T (le_trans (le_max_right _ _) hT)
  rw [Qcomp_eq_Qpl_add_defect p m (1 / 64) i j U T]
  linarith

/-- **`QResidual` from the paper's own `Q`-side inputs plus the defect budget.**  Composing §6
with the identity above: the projected half no longer needs any hypothesis, so the raw `QResidual`
is reduced to (i) the increment-size bound and `(maxmom)` for the adapted ledger, and (ii) the
one-sided terminal-defect budget. -/
theorem qresidual_of_dominated_and_defect {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {C K : ℝ} (hC : 0 ≤ C) {Y : ℕ → Array N → ℝ}
    (hdom : ∀ i j : Fin N, i ≠ j → ∀ t : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      |Dinc p m (1 / 64) i j t U| ≤ C * (1 + Y t U))
    (hYint : ∀ t : ℕ, Integrable (fun U : Array N => (1 + Y t U) ^ 2) (arrayMeasure N))
    (hYlog : ∀ t : ℕ, ∫ U, (1 + Y t U) ^ 2 ∂(arrayMeasure N)
      ≤ K * (Real.log ((t : ℝ) + 2)) ^ 4)
    (hd : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 128 : ℝ) * (T : ℝ))
        ≤ (Zpot p m (1 / 64) i j U T - Zproj p m (1 / 64) i j T U)
          - (Zpot p m (1 / 64) i j U 0 - Zproj p m (1 / 64) i j 0 U)) :
    SwarmActualBudget.QResidual p m N := by
  have hQ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U := by
    intro i j hij
    filter_upwards [Qpl_div_tendsto_zero_of_dominated (N := N) hp0 hp1 m i j
      (by norm_num : (0 : ℝ) < 1 / 64) hC (hdom i j hij) hYint hYlog] with U hU
    exact tendsto_zero_div_eventually_lower (by norm_num : (0 : ℝ) < 1 / 128) hU
  exact qresidual_of_Qpl_and_defect (N := N) hp0 hp1 hQ hd

end SwarmProjRes
