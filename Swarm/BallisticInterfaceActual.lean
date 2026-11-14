/-
  DIRECTION G (m7) — `BallisticInterfaceActual.lean`: the occupation/ballistic assembly layer.

  The verified filtration inputs (`OccInterface`, `VdriftTimeAssembly`, `CorrectionDrift`,
  `GlobalPaperCondExp`) produce the paper's ledger at the actual model with three named
  *eventual pathwise budgets* left over: `hZ` (Zpot), `hJ` (Jsum), `hQ` (Qcomp).  The verified
  occupation service (`OccTwoActual`, `OccTwoSide`, `Ballistic`, `Speed`) consumes the paper's
  *two-sided per-pair pieces* `PaperPiecesTwoSided`.  This file glues the two and nothing more.

  ## What is checked here

  * `runMax_eq_SwarmSpeed_runMax`, `occSum_eq_OccTwoOfMax`: `OccInterface.occSum` **is** the
    two-sided count `OccTwoActual.OccTwoOfMax`, and the trajectory running maximum **is** the
    path running maximum.  So the two interfaces talk about the same object: no reindexing, and
    the walker-record roles (`M^i_n` for the counted walker `i`, `M^j_n` for the record walker
    `j`) are the ones the service expects.
  * `paperWeight_budget_discharged`: the `hAB` input of `OccInterface`, discharged
    unconditionally from `GlobalPaperCondExp.paperWeight_le_condExp_discharged`.
  * `ledger_all_actual`: the summed ledger at any positive slack `eps`, on a single almost-sure
    set, valid at *every* time.
  * `Interfaces p m N i j`: the three residual budgets `hZ`, `hJ`, `hQ` at `eps = 1/64`, with
    `M` instantiated at the walker-`i` running maximum, the onset allowed to depend on the
    array, and no additive constants.  This is the exact shape of the paper's `(Vbound)`,
    `(Jbound)`, `Q_n = o(n)` as the service needs them.
  * `paperPiecesTwoSided_of_interfaces`: `Interfaces` implies `PaperPiecesTwoSided` a.e.
  * `actual_occ_of_interfaces`, `actual_speed_of_interfaces`: hence the paper's `(occbnd)` and
    `7/80 <= liminf X^i_n/n` at the actual trajectory, `7/80` free of `N`.
  * `InterfacesGen`, `occbnd_of_twoSided_coef(_slack/_le/_eighth)`,
    `actual_occ_coef_of_interfaces`, `actual_speed_coef_of_interfaces`: the same assembly with
    *arbitrary coefficients* `A` on `Zpot`, `B` on `Jsum` (the `JboundActual` shape, whose
    coefficient `2 C_eps K` is not `≤ 1`), a rate `δ`, and *additive* per-array constants on
    each budget.  The resulting speed is `7/(40 * max 1 (A+B))`, still `N`-free and positive.
  * `interfaces_of_dominating_M`, `actual_occ_of_interfaces_one_eighth`: the `M` slot can be
    weakened to any sequence `≤ M^i_n`, and the paper's `eps = 1/32` tuple (via
    `OccInterface.occupation_bound_one_eighth`) gives the same `(occbnd)`.
  * `InterfacesOGen`/`InterfacesO` and `interfacesGen_of_interfacesOGen`,
    `interfaces_of_interfacesO`, `actual_occ_of_o`, `actual_speed_of_o`: the paper's three
    `o(n)` statements (`(Vbound)`, `(Jbound)`, `Q_n = o(n)`) suffice, at the same constants:
    a.e. `7/80 <= liminf X^i_n/n`.
  * `actual_speed_of_ballistic`: `Swarm.Ballistic` implies the actual-model statement.  This is
    the *only* relation between the two available without a new input: `Swarm.Ballistic`
    quantifies over every system satisfying the marginal law `Swarm.IsInteractingLaw`, while
    everything above is a statement about the actual joint law `(arrayMeasure N, trajectory)`.
    See README.md.

  Nothing here proves, reduces or re-proves `hZ`, `hJ` or `hQ`.
-/
import Swarm.OccInterface
import Swarm.OccTwoActual
import Swarm.GlobalPaperCondExp
import Swarm.ActualInstance

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmBIA

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly Swarming.Enl.Budget

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ## 1. The two interfaces describe the same counts and the same running maximum -/

/-- The trajectory running maximum `M_n^j = max_{t <= n} X_t^j` is the path running maximum
consumed by the occupation service.  Definitional (both are `Finset.sup'` over `range (n+1)`). -/
theorem runMax_eq_SwarmSpeed_runMax (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n = SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j) n := rfl

/-- `OccInterface.occSum` is exactly `OccTwoActual.OccTwoOfMax`: the paper's two-sided count
`#{t < n : 0 <= X^i_t <= M^j_t}`.  Definitional. -/
theorem occSum_eq_OccTwoOfMax (i j : Fin N) (U : Array N) (T : ℕ) :
    occSum p m i j U T = SwarmOccTwo.OccTwoOfMax p m N i j U T := rfl

/-- `OccTwoOfMax` is the two-sided count as a `SwarmOccTwo.occTwo` sum.  Definitional. -/
theorem OccTwoOfMax_eq_occTwo (i j : Fin N) (U : Array N) (T : ℕ) :
    SwarmOccTwo.OccTwoOfMax p m N i j U T
      = SwarmOccTwo.occTwo (fun t => (trajectory p m U t).pos i)
          (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) T := rfl

/-! ## 2. The `hAB` input, discharged from the integrated global bracket -/

/-- `OccInterface`'s `hAB` for every time, from the unconditional global bound
`GlobalPaperCondExp.paperWeight_le_condExp_discharged`.  (This is the only probabilistic input
of the ledger, and it is not a residual hypothesis.) -/
theorem paperWeight_budget_discharged (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ n, paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) :=
  fun n => paperWeight_le_condExp_discharged hp0 hp1 hm hij

/-! ## 3. The summed ledger, on one almost-sure set, for every time -/

/-- **The paper's summed ledger at the actual trajectory**, with the actual right probabilities
`alphaFun` and any positive slack `eps`:

    sum_{t<T} 1{0 <= X_t^i <= M_t^j} <= eps T + (Z_T - Z_0) + sum_{t<T} J_{t+1} - Q_T.

No stochastic premise: `hAB` is discharged by `paperWeight_budget_discharged`. -/
theorem ledger_all_actual (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      occSum p m i j U n
        ≤ eps * (n : ℝ) + (Zpot p m eps i j U n - Zpot p m eps i j U 0)
          + Jsum p m eps i j U n
          - Qcomp p m eps (fun t => alphaFun p m t i) i j U n := by
  filter_upwards [oneStep_all (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε
    (fun t U => one_half_le_alphaFun hp0 hp1 m t i U)
    (paperWeight_budget_discharged (N := N) (p := p) (m := m) hp0 hp1 hm hij)] with U hall
  intro n
  simpa only [occSum, Jsum] using
    ledger_pointwise p m eps (fun t => alphaFun p m t i) i j U hall n

/-! ## 4. The residual inputs: the three eventual pathwise budgets, in `runMax` form -/

/-- **The residual stochastic inputs of the occupation assembly**: `hZ`, `hJ`, `hQ` at
`eps = 1/64`, with the running maximum of the *same* walker `i` that is being counted, and with
an onset that may depend on the array.  There are no additive constants: those are the business
of `InterfacesGen` below.

`Zpot`/`Jsum` are the paper's `Z`-potential and record-cost sum, `Qcomp` the exact centred
compensator of `CorrectionDrift.compensator_unconditional`.  This is *not* a generic statement
about marginal-law systems: every object is an actual model object on `Array N`. -/
def Interfaces (p : ℝ) (m N : ℕ) (i j : Fin N) : Prop :=
  ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ,
    (∀ T ≥ N₀,
      Zpot p m (1 / 64) i j U T ≤ ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    ∧ (∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T ≤ ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    ∧ (∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T)

/-- **`Interfaces` gives the paper's two-sided per-pair pieces.**  The single `Z`/`J`/`Q` point
used by the service is the actual `Zpot`/`Jsum`/`Qcomp` at `eps = 1/64`. -/
theorem paperPiecesTwoSided_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) (h : Interfaces p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), SwarmOccTwo.PaperPiecesTwoSided p m N i j U := by
  filter_upwards [h, ledger_all_actual (N := N) (p := p) (m := m) hp0 hp1 hm hij
    (by norm_num : (0 : ℝ) < 1 / 64)] with U hU hled
  obtain ⟨N₀, hZ, hJ, hQ⟩ := hU
  exact ⟨Zpot p m (1 / 64) i j U, Jsum p m (1 / 64) i j U,
    Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U, N₀,
    fun n => by
      have := hled n
      rwa [occSum_eq_OccTwoOfMax] at this,
    hZ, hJ, hQ⟩

/-- The all-pairs almost-sure form consumed by `OccTwoActual`. -/
theorem paperPiecesTwoSided_all_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm : 2 ≤ m) (h : ∀ i j : Fin N, i ≠ j → Interfaces p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → SwarmOccTwo.PaperPiecesTwoSided p m N i j U := by
  have hinner : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      ∀ j : Fin N, i ≠ j → SwarmOccTwo.PaperPiecesTwoSided p m N i j U := by
    intro i
    refine Filter.eventually_all.mpr (fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun U hne => absurd hij hne
    · exact (paperPiecesTwoSided_of_interfaces hp0 hp1 hm hij (h i j hij)).mono
        fun U hU _ => hU
  exact Filter.eventually_all.mpr hinner

/-- **The paper's `(occbnd)` for the actual trajectory**, from `Interfaces` only.  `M` is the
running maximum of walker `i`; the coefficient `2` and the constant `1/8` are independent of `N`. -/
theorem actual_occ_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (h : ∀ i j : Fin N, i ≠ j → Interfaces p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ 2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) :=
  SwarmOccTwo.actual_occ_of_twoSided_all (N := N) (p := p) (m := m) hp0 hp1 hm
    (paperPiecesTwoSided_all_of_interfaces hp0 hp1 hm h)

/-- **The paper's lower speed bound at the actual trajectory**, `7/80 <= liminf X^i_n/n` for
every walker, from `Interfaces` only; `7/80` does not depend on `N`.

The negative-visit correction is the verified transience `SwarmBad.ae_transience_actual`, and the
oscillation `M^i_n - X^i_n = o(n)` is the verified `SwarmHosc.trajectory_hosc`; neither is a
hypothesis here. -/
theorem actual_speed_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hN : 2 ≤ N) (h : ∀ i j : Fin N, i ≠ j → Interfaces p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / 80 ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop :=
  SwarmOccTwo.actual_liminf_speed_of_twoSided (N := N) (p := p) (m := m) hp0 hp1 hm hN
    (paperPiecesTwoSided_all_of_interfaces hp0 hp1 hm h)

/-- **Bridge from `OccInterface`'s free `M` to the fixed `runMax` form.**  A budget stated with
any bounding sequence that is at most the counted walker's running maximum gives `Interfaces`.
This is the only place where the walker-record role can go wrong: `M` must bound `M^i_n` from
above, and the *record* walker `j` appears only through `runMax p m U j`, never in the budget. -/
theorem interfaces_of_dominating_M {i j : Fin N} {M : Array N → ℕ → ℝ} {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Zpot p m (1 / 64) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T ≤ M U T + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T)
    (hM : ∀ U T, M U T ≤ ((runMax p m U i T : ℤ) : ℝ)) :
    Interfaces p m N i j := by
  filter_upwards [hZ, hJ, hQ] with U hZ' hJ' hQ'
  refine ⟨N₀, fun T hT => ?_, fun T hT => ?_, hQ'⟩
  · have h := hZ' T hT
    have h2 := hM U T
    linarith
  · have h := hJ' T hT
    have h2 := hM U T
    linarith

/-! ## 4b. The `eps = 1/32` convention, for comparison

`OccInterface.occupation_bound_one_eighth` fixes the paper's own choice `eps = 1/32`,
`δ = 1/64` and *already* produces the `(occbnd)` shape, with the constant
`max 0 (-(Zpot 0))` absorbed into the onset.  So the `eps = 1/32` tuple is interchangeable with
`Interfaces` (which uses `eps = 1/64` because that is the exact drift coefficient of
`PaperPiecesTwoSided`).  Recording this makes the two conventions explicit: whoever proves the
three budgets may use either, and in both cases `M` must be the counted walker's running
maximum. -/
theorem actual_occ_of_interfaces_one_eighth (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {N₀ : ℕ}
    (hZ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Zpot p m (1 / 32) i j U T ≤ ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    (hJ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      Jsum p m (1 / 32) i j U T ≤ ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    (hQ : ∀ᵐ U ∂(arrayMeasure N), ∀ T ≥ N₀,
      -((1 / 64) * (T : ℝ)) ≤ Qcomp p m (1 / 32) (fun t => alphaFun p m t i) i j U T) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₁ : ℕ, ∀ T ≥ N₁,
      occSum p m i j U T ≤ 2 * ((runMax p m U i T : ℤ) : ℝ) + (1 / 8) * (T : ℝ) := by
  filter_upwards [occupation_bound_one_eighth (N := N) (p := p) (m := m) hp0 hp1
    (i := i) (j := j) (M := fun U T => ((runMax p m U i T : ℤ) : ℝ)) (N₀ := N₀)
    (paperWeight_budget_discharged (N := N) (p := p) (m := m) hp0 hp1 hm hij) hZ hJ hQ]
    with U hU
  exact ⟨_, hU⟩

/-! ## 5. Coefficient-general variant (the `JboundActual` shape)

`JboundActual.occbnd_coef`/`speed_from_pieces_coef` keep the coefficient of `M^i_n` abstract,
because the paper's `(Jbound)` coefficient `2 C_eps K` is not `≤ 1`.  The same is needed here: the
`J`-sum of the ledger is by no means `≤ M^i_n + n/64`.  The lemmas below are the *two-sided*
counterparts of `SwarmOccTwo.occbnd_slack`/`occbnd_slack_one_eighth`: they keep an additive slack
(negative visits, plus a constant left over by each of the `Z`/`J`/`Q` bounds) and abstract
coefficients `A`, `B` and rate `δ`.

Arithmetic: the three budgets cost `3 δ n`, and absorbing the constant
`max 0 (KZ + KJ + KQ + Kn - Z_0)` into the onset costs one further `δ n`, so the coefficient of
`n` in the absorbed form is `eps + 4 δ`.  At the paper's `(1/64, 1/64)` this is `5/64 <= 1/8`,
which is why the service's `1/8` survives. -/

/-- **Two-sided occupation bound, abstract coefficients, slack form.**  From the summed drift
inequality for the two-sided count, the negative-visit bound and eventual bounds
`Z n ≤ A M n + δ n + KZ`, `J n ≤ B M n + δ n + KJ`, `Q n ≥ -δ n - KQ`, the one-sided count obeys

    Occ n <= (A + B) M n + (eps + 3 δ) n + max 0 (KZ + KJ + KQ + Kn - Z_0).

No onset is needed: the constant term is carried explicitly. -/
theorem occbnd_of_twoSided_coef_slack {u v : ℕ → ℤ} {Z J Q : ℕ → ℝ}
    {ε δ A B KZ KJ KQ Kn : ℝ} {N : ℕ}
    (hdrift : ∀ n, SwarmOccTwo.occTwo u v n
      ≤ ε * (n : ℝ) + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, SwarmOccTwo.negCount u n ≤ Kn)
    (hZ : ∀ n ≥ N, Z n ≤ A * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KZ)
    (hJ : ∀ n ≥ N, J n ≤ B * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KJ)
    (hQ : ∀ n ≥ N, -(δ * (n : ℝ)) - KQ ≤ Q n) :
    ∀ n ≥ N, SwarmSpeed.occ u v n
      ≤ (A + B) * (SwarmSpeed.runMax u n : ℝ) + (ε + 3 * δ) * (n : ℝ)
        + max 0 (KZ + KJ + KQ + Kn - Z 0) := by
  intro n hn
  have h1 := SwarmOccTwo.occ_le_occTwo_add u v n
  have h2 := hdrift n
  have h3 := hneg n
  have h4 := hZ n hn
  have h5 := hJ n hn
  have h6 := hQ n hn
  have h7 : KZ + KJ + KQ + Kn - Z 0 ≤ max 0 (KZ + KJ + KQ + Kn - Z 0) := le_max_right _ _
  nlinarith

/-- **Two-sided occupation bound, abstract coefficients, absorbed form**: the slack is charged at
rate `δ`, so the coefficient of `n` is `eps + 4 δ`. -/
theorem occbnd_of_twoSided_coef {u v : ℕ → ℤ} {Z J Q : ℕ → ℝ}
    {ε δ A B KZ KJ KQ Kn : ℝ} {N : ℕ}
    (hδ : 0 < δ)
    (hdrift : ∀ n, SwarmOccTwo.occTwo u v n
      ≤ ε * (n : ℝ) + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, SwarmOccTwo.negCount u n ≤ Kn)
    (hZ : ∀ n ≥ N, Z n ≤ A * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KZ)
    (hJ : ∀ n ≥ N, J n ≤ B * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KJ)
    (hQ : ∀ n ≥ N, -(δ * (n : ℝ)) - KQ ≤ Q n) :
    ∀ n ≥ max N ⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊,
      SwarmSpeed.occ u v n
        ≤ (A + B) * (SwarmSpeed.runMax u n : ℝ) + (ε + 4 * δ) * (n : ℝ) := by
  intro n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hK : max 0 (KZ + KJ + KQ + Kn - Z 0) ≤ δ * (n : ℝ) := by
    have h1 : (⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 : max 0 (KZ + KJ + KQ + Kn - Z 0) / δ
        ≤ (⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : max 0 (KZ + KJ + KQ + Kn - Z 0)
        ≤ (⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊ : ℝ) * δ := by
      rw [div_le_iff₀ hδ] at h2
      exact h2
    have h4 : (⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊ : ℝ) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right h1 hδ.le
    nlinarith
  have h := occbnd_of_twoSided_coef_slack (N := N) hdrift hneg hZ hJ hQ n hN
  nlinarith

/-- **The service's `1/8` shape with abstract coefficients** (`M` replaced by `max 1 (A+B) * M`,
which is what `SwarmSpeed.speed_lower_bound` wants).  Hypothesis `eps + 4 * δ ≤ 1/8`. -/
theorem occbnd_of_twoSided_coef_le {u v : ℕ → ℤ} (h0 : 0 ≤ u 0)
    {Z J Q : ℕ → ℝ} {A B KZ KJ KQ Kn ε δ : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hbud : ε + 4 * δ ≤ 1 / 8)
    (hdrift : ∀ n, SwarmOccTwo.occTwo u v n
      ≤ ε * (n : ℝ) + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, SwarmOccTwo.negCount u n ≤ Kn)
    (hZ : ∀ n ≥ N, Z n ≤ A * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KZ)
    (hJ : ∀ n ≥ N, J n ≤ B * (SwarmSpeed.runMax u n : ℝ) + δ * (n : ℝ) + KJ)
    (hQ : ∀ n ≥ N, -(δ * (n : ℝ)) - KQ ≤ Q n) :
    ∀ n ≥ max N ⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / δ⌉₊,
      SwarmSpeed.occ u v n
        ≤ max 1 (A + B) * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * (n : ℝ) := by
  intro n hn
  have h := occbnd_of_twoSided_coef (A := A) (B := B) (KZ := KZ) (KJ := KJ) (KQ := KQ)
    (Kn := Kn) (ε := ε) (δ := δ) hδ hdrift hneg hZ hJ hQ n hn
  have hM : (0 : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) := by
    have h1 : (0 : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast h0
    have h2 : u 0 ≤ SwarmSpeed.runMax u n := SwarmSpeed.le_runMax (Nat.zero_le n)
    have h3 : (u 0 : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) := by exact_mod_cast h2
    linarith
  have hle : (A + B) * (SwarmSpeed.runMax u n : ℝ)
      ≤ max 1 (A + B) * (SwarmSpeed.runMax u n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hM
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hεδ : (ε + 4 * δ) * (n : ℝ) ≤ (1 / 8) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hbud hn0
  linarith

/-- The paper's `(1/64, 1/64)` instance of `occbnd_of_twoSided_coef_le`. -/
theorem occbnd_of_twoSided_coef_eighth {u v : ℕ → ℤ} (h0 : 0 ≤ u 0)
    {Z J Q : ℕ → ℝ} {A B KZ KJ KQ Kn : ℝ} {N : ℕ}
    (hdrift : ∀ n, SwarmOccTwo.occTwo u v n
      ≤ (1 / 64) * (n : ℝ) + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, SwarmOccTwo.negCount u n ≤ Kn)
    (hZ : ∀ n ≥ N, Z n ≤ A * (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * (n : ℝ) + KZ)
    (hJ : ∀ n ≥ N, J n ≤ B * (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * (n : ℝ) + KJ)
    (hQ : ∀ n ≥ N, -((1 / 64) * (n : ℝ)) - KQ ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 (KZ + KJ + KQ + Kn - Z 0)⌉₊,
      SwarmSpeed.occ u v n
        ≤ max 1 (A + B) * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * (n : ℝ) := by
  intro n hn
  have hidx : ⌈max 0 (KZ + KJ + KQ + Kn - Z 0) / (1 / 64)⌉₊ ≤ n := by
    have hdiv : max 0 (KZ + KJ + KQ + Kn - Z 0) / (1 / 64)
        = 64 * max 0 (KZ + KJ + KQ + Kn - Z 0) := by ring
    rw [hdiv]
    exact le_trans (le_max_right _ _) hn
  exact occbnd_of_twoSided_coef_le (A := A) (B := B) (KZ := KZ) (KJ := KJ) (KQ := KQ)
    (Kn := Kn) (ε := 1 / 64) (δ := 1 / 64)
    h0 (by norm_num) (by norm_num) hdrift hneg hZ hJ hQ n
    (max_le (le_trans (le_max_left _ _) hn) hidx)

/-- **The residual inputs with abstract coefficients, rate `δ` and additive per-array constants.**
`Interfaces` is the case `eps = δ = 1/64`, `A = B = 1`, zero constants; the onset here may again
depend on the array. -/
def InterfacesGen (p : ℝ) (m N : ℕ) (eps δ A B : ℝ) (i j : Fin N) : Prop :=
  ∀ᵐ U ∂(arrayMeasure N), ∃ (N₀ : ℕ) (KZ KJ KQ : ℝ),
    (∀ T ≥ N₀,
      Zpot p m eps i j U T ≤ A * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ) + KZ)
    ∧ (∀ T ≥ N₀,
      Jsum p m eps i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ) + KJ)
    ∧ (∀ T ≥ N₀,
      -(δ * (T : ℝ)) - KQ ≤ Qcomp p m eps (fun t => alphaFun p m t i) i j U T)

/-- `Interfaces` is the special case of `InterfacesGen` with unit coefficients and zero constants. -/
theorem interfacesGen_of_interfaces {i j : Fin N} (h : Interfaces p m N i j) :
    InterfacesGen p m N (1 / 64) (1 / 64) 1 1 i j := by
  filter_upwards [h] with U hU
  obtain ⟨N₀, hZ, hJ, hQ⟩ := hU
  refine ⟨N₀, 0, 0, 0, ?_, ?_, ?_⟩
  · intro T hT
    have := hZ T hT
    linarith
  · intro T hT
    have := hJ T hT
    linarith
  · intro T hT
    have := hQ T hT
    linarith

/-- **`(occbnd)` for the actual trajectory with abstract coefficients**, from the ledger and
`InterfacesGen`, using the verified transience for the negative-visit slack.  The hypothesis
`eps + 4 * δ ≤ 1/8` is the paper's constant bookkeeping (`1/64 + 4/64 = 5/64` and
`1/32 + 4/64 = 3/32` both qualify). -/
theorem actual_occ_coef_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    {eps δ A B : ℝ} (heps : 0 < eps) (hδ : 0 < δ) (hbud : eps + 4 * δ ≤ 1 / 8)
    (h : ∀ i j : Fin N, i ≠ j → InterfacesGen p m N eps δ A B i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
  have hmain : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
    intro i j hij
    filter_upwards [h i j hij,
      ledger_all_actual (N := N) (p := p) (m := m) hp0 hp1 hm hij heps,
      SwarmOccTwo.ae_negCount_bdd (N := N) (p := p) (m := m) hp0 hp1 hm i j hij]
      with U hU hled hneg
    obtain ⟨N₀, KZ, KJ, KQ, hZ, hJ, hQ⟩ := hU
    obtain ⟨K, hK⟩ := hneg
    refine ⟨max N₀ ⌈max 0 (KZ + KJ + KQ + (K : ℝ) - Zpot p m eps i j U 0) / δ⌉₊,
      fun n hn => ?_⟩
    have hdrift : ∀ k, SwarmOccTwo.occTwo (fun t => (trajectory p m U t).pos i)
        (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) k
        ≤ eps * (k : ℝ) + (Zpot p m eps i j U k - Zpot p m eps i j U 0)
          + Jsum p m eps i j U k
          - Qcomp p m eps (fun t => alphaFun p m t i) i j U k := by
      intro k
      have hk := hled k
      rw [occSum_eq_OccTwoOfMax, OccTwoOfMax_eq_occTwo] at hk
      exact hk
    have hcoef := occbnd_of_twoSided_coef_le (A := A) (B := B)
      (KZ := KZ) (KJ := KJ) (KQ := KQ) (Kn := (K : ℝ)) (ε := eps) (δ := δ) (N := N₀)
      (u := fun t => (trajectory p m U t).pos i)
      (v := SwarmSpeed.runMax (fun s => (trajectory p m U s).pos j))
      (Z := fun k => Zpot p m eps i j U k) (J := fun k => Jsum p m eps i j U k)
      (Q := fun k => Qcomp p m eps (fun t => alphaFun p m t i) i j U k)
      (by simp [trajectory_zero, initialWalkState]) hδ hbud hdrift
      (fun k => hK k) hZ hJ hQ n hn
    have hOcc : SwarmOccTwo.OccOfMax p m N i j U n
        = SwarmSpeed.occ (fun t => (trajectory p m U t).pos i)
            (SwarmSpeed.runMax (fun t => (trajectory p m U t).pos j)) n := rfl
    rw [hOcc]
    exact hcoef
  have hinner : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, i ≠ j → ∃ N₁ : ℕ,
      ∀ n ≥ N₁, SwarmOccTwo.OccOfMax p m N i j U n
        ≤ max 1 (A + B) * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
    intro i
    refine Filter.eventually_all.mpr (fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun U hne => absurd hij hne
    · exact (hmain i j hij).mono fun U hU _ => hU
  exact Filter.eventually_all.mpr hinner

/-- **The lower speed bound at the actual trajectory with abstract coefficients**:
`7/(40 * max 1 (A+B)) <= liminf X^i_n/n`, a positive constant independent of `N`. -/
theorem actual_speed_coef_of_interfaces (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hN : 2 ≤ N) {eps δ A B : ℝ} (heps : 0 < eps) (hδ : 0 < δ) (hbud : eps + 4 * δ ≤ 1 / 8)
    (h : ∀ i j : Fin N, i ≠ j → InterfacesGen p m N eps δ A B i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / (40 * max 1 (A + B))
        ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  have hocc := actual_occ_coef_of_interfaces (N := N) (p := p) (m := m) hp0 hp1 hm heps hδ hbud h
  have hosc := SwarmHosc.trajectory_hosc (p := p) hp0 hp1 m N
  filter_upwards [hocc, hosc] with U hU hoscU i
  obtain ⟨j, hji⟩ := SwarmHosc.exists_ne_of_two_le hN i
  obtain ⟨N₁, hN₁⟩ := hU i j (Ne.symm hji)
  obtain ⟨N₂, hN₂⟩ := hU j i hji
  have hkey := SwarmSpeed.liminf_speed
    (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j)
    (by simp [trajectory_zero, initialWalkState])
    (C := max 1 (A + B)) (B := 1) (le_max_left _ _) (N := max N₁ N₂)
    (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
    (hoscU i) (SwarmOccTwo.actual_pos_div_le_one (N := N) (p := p) (m := m) hp0 hp1 i U)
  simpa using hkey

/-! ## 5b. The paper's `o(n)` form of the three budgets

The interfaces above fix the rates `1/64`.  The paper states `(Vbound)`, `(Jbound)` and
`Q_n = o(n)` in the *for every `δ > 0`, eventually* form, and that is what a proof usually
produces.  It is enough, and nothing is lost in the constants: the rate budget
`eps + 4 δ ≤ 1/8` holds at `eps = δ = 1/64` with room to spare (`5/64 ≤ 1/8`; the exact bound on
`δ` is `δ ≤ 7/256`), so the `o(n)` statements may simply be instantiated at `δ = 1/64`.  The
coefficient of `M^i_n` is unchanged, so the paper's own three `o(n)` statements give `(occbnd)`
with coefficient `2` and `1/8`, hence `κ = 7/80`. -/

/-- **The residual inputs in the paper's `o(n)` form**, with arbitrary coefficients `A`, `B`. -/
def InterfacesOGen (p : ℝ) (m N : ℕ) (A B : ℝ) (i j : Fin N) : Prop :=
  ∀ᵐ U ∂(arrayMeasure N),
    (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zpot p m (1 / 64) i j U T ≤ A * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    ∧ (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Jsum p m (1 / 64) i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) + δ * (T : ℝ))
    ∧ (∀ δ > 0, ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -(δ * (T : ℝ)) ≤ Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T)

/-- The unit-coefficient case: literally `Zpot ≤ M^i_n + o(n)`, `Jsum ≤ M^i_n + o(n)` and
`Qcomp ≥ -o(n)`. -/
abbrev InterfacesO (p : ℝ) (m N : ℕ) (i j : Fin N) : Prop := InterfacesOGen p m N 1 1 i j

/-- **The `o(n)` form gives the rate form at any rate.**  The three onsets are merged by taking a
maximum; no constant is needed. -/
theorem interfacesGen_of_interfacesOGen {A B δ : ℝ} (hδ : 0 < δ) {i j : Fin N}
    (h : InterfacesOGen p m N A B i j) :
    InterfacesGen p m N (1 / 64) δ A B i j := by
  filter_upwards [h] with U hU
  obtain ⟨hZ, hJ, hQ⟩ := hU
  obtain ⟨NZ, hNZ⟩ := hZ δ hδ
  obtain ⟨NJ, hNJ⟩ := hJ δ hδ
  obtain ⟨NQ, hNQ⟩ := hQ δ hδ
  refine ⟨max NZ (max NJ NQ), 0, 0, 0, ?_, ?_, ?_⟩
  · intro T hT
    have := hNZ T (le_trans (le_max_left _ _) hT)
    linarith
  · intro T hT
    have := hNJ T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
    linarith
  · intro T hT
    have := hNQ T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
    linarith

/-- **The `o(n)` form gives `Interfaces`**: instantiate at `δ = 1/64`. -/
theorem interfaces_of_interfacesO {i j : Fin N} (h : InterfacesO p m N i j) :
    Interfaces p m N i j := by
  filter_upwards [h] with U hU
  obtain ⟨hZ, hJ, hQ⟩ := hU
  obtain ⟨NZ, hNZ⟩ := hZ (1 / 64) (by norm_num)
  obtain ⟨NJ, hNJ⟩ := hJ (1 / 64) (by norm_num)
  obtain ⟨NQ, hNQ⟩ := hQ (1 / 64) (by norm_num)
  refine ⟨max NZ (max NJ NQ), ?_, ?_, ?_⟩
  · intro T hT
    have h1 := hNZ T (le_trans (le_max_left _ _) hT)
    nlinarith
  · intro T hT
    have h1 := hNJ T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
    nlinarith
  · intro T hT
    have h1 := hNQ T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
    nlinarith

/-- **The paper's `(occbnd)` from the three `o(n)` statements**: a.e.
`OccOfMax ≤ 2·M^i_n + n/8` eventually, for every ordered pair of distinct walkers. -/
theorem actual_occ_of_o (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (h : ∀ i j : Fin N, i ≠ j → InterfacesO p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
      SwarmOccTwo.OccOfMax p m N i j U n
        ≤ 2 * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
          + (1 / 8) * (n : ℝ) := by
  have h' : ∀ i j : Fin N, i ≠ j → InterfacesGen p m N (1 / 64) (1 / 64) 1 1 i j :=
    fun i j hij => interfacesGen_of_interfacesOGen (A := (1 : ℝ)) (B := (1 : ℝ))
      (by norm_num) (h i j hij)
  have hocc := actual_occ_coef_of_interfaces (N := N) (p := p) (m := m) hp0 hp1 hm
    (A := 1) (B := 1) (eps := 1 / 64) (δ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num) h'
  have hmax : max 1 ((1 : ℝ) + 1) = 2 := by norm_num
  rw [hmax] at hocc
  exact hocc

/-- **The actual lower speed bound `7/80` from the paper's three `o(n)` statements**
(`(Vbound)`, `(Jbound)`, `Q_n = o(n)`), with `7/80` independent of `N`. -/
theorem actual_speed_of_o (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m)
    (hN : 2 ≤ N) (h : ∀ i j : Fin N, i ≠ j → InterfacesO p m N i j) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      (7 : ℝ) / 80 ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  have h' : ∀ i j : Fin N, i ≠ j → InterfacesGen p m N (1 / 64) (1 / 64) 1 1 i j :=
    fun i j hij => interfacesGen_of_interfacesOGen (A := (1 : ℝ)) (B := (1 : ℝ))
      (by norm_num) (h i j hij)
  have hspeed := actual_speed_coef_of_interfaces (N := N) (p := p) (m := m) hp0 hp1 hm hN
    (A := 1) (B := 1) (eps := 1 / 64) (δ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num) h'
  have hval : (7 : ℝ) / (40 * max 1 ((1 : ℝ) + 1)) = 7 / 80 := by norm_num
  rw [hval] at hspeed
  exact hspeed

/-! ## 6. Quantification check: `Swarm.Ballistic` implies the actual-model statement

`Swarm.Ballistic m p` is a statement about **every** system `(μ, X, 𝓕)` satisfying the marginal
law `Swarm.IsInteractingLaw`.  The theorems above are statements about the **actual** array
`(arrayMeasure N, trajectory)` only.  The implication proved here is the one that holds: every
`Ballistic` bound may be evaluated at the actual system, which satisfies the marginal law by
`SwarmCross.Actual.actual_isInteractingLaw`.  The converse needs a transfer from marginal-law
systems to the actual joint law, which is not available (see README.md). -/
theorem actual_speed_of_ballistic (hball : Swarm.Ballistic m p) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (hN : 2 ≤ N) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  obtain ⟨κ, hκ, h⟩ := hball
  refine ⟨κ, hκ, ?_⟩
  have hlaw := SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m
  have hkey := h N (Array N) (arrayMeasure N)
    (fun t (U : Array N) i => (trajectory p m U t).pos i) (SwarmCross.pathFilt p m) hN hlaw
  simpa [Swarm.pos] using hkey

end SwarmBIA
