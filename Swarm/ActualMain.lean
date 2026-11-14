/-  # The occupation/ballistic half of the paper's Theorem 1.1 is a THEOREM for the paper's model

  `Swarm/Assembly.lean` states the paper's Theorem 1.1 as a reduction from three named
  inputs: `Swarm.Ballistic`, `Swarm.RegenAvailable`, `Swarm.InitialRegen`.  `Swarm.Ballistic` is
  quantified over **every** system satisfying the one-walker marginal rule
  `Swarm.IsInteractingLaw`; it is the class-level (generic-marginal) occupation bound.  The
  campaign's open state is "generic marginal Ballistic remains open".

  This file records the exact class-quantifier split that the occupation development of
  `areas/occupation/` actually proves, and then removes `Ballistic` from the hypothesis list of
  the paper's theorem **for the paper's own model**:

  * `actualProjectedBallistic` — the concrete-array form of Proposition `ball`'s lower bound,
    `κ` independent of `N`, with no hypothesis (this is
    `Swarming.Enl.ProjVbound.projected_speed_uniform`, restated in the paper's walker notation);
  * `ActualRegen` — the regeneration data of Propositions `front` + `regen`, asked for at the
    concrete array model only (one `N` at a time) instead of over the whole marginal class;
  * `actualRegen_of_regenAvailable` — the class-level `Swarm.RegenAvailable` supplies it, so the
    hypothesis is *not* a strengthening of the paper's input;
  * `main_theorem_actual_of_actual_regeneration` and `main_claim_actual_of_regenAvailable` —
    the paper's Theorem 1.1 (`κ(m,p) > 0` uniform in `N`, `v ∈ [κ, 2p-1]`, every walker, a.s.)
    for the concrete array construction, with **`Swarm.Ballistic` discharged, not assumed**.

  Nothing here proves `Swarm.Ballistic`: the class-level statement is strictly stronger than the
  paper's theorem because `IsInteractingLaw` does not impose cross-walker conditional
  independence, which the paper's `(Zdrift)` step uses (see `ACTUAL_MAIN.md`).  What is proved is
  that the paper's own theorem does not need it.
-/
import Swarm.Assembly
import Swarm.ProjVbound
import Swarm.ActualInstance
import Swarm.DensReduction

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace Swarm

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ} {m : ℕ} {p : ℝ}

/-- The concrete recursive trajectory of the paper's model, in the shape of the assembly's
integer-valued process `X : ℕ → Ω → Fin N → ℤ`. -/
noncomputable def actualX (p : ℝ) (m : ℕ) : ℕ → Array N → Fin N → ℤ :=
  fun n U => (trajectory p m U n).pos

@[simp] lemma actualX_apply (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) (i : Fin N) :
    actualX (N := N) p m n U i = (trajectory p m U n).pos i := rfl

/-- `Swarm.pos` of the concrete trajectory is the real position used throughout the occupation
development. -/
@[simp] lemma pos_actualX (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    pos (actualX (N := N) p m) n i
      = fun U : Array N => ((trajectory p m U n).pos i : ℝ) := rfl

/-- **Proposition `ball`, lower half, for the concrete array model, with no hypothesis.**

`κ(m,p) > 0` is independent of the walker count `N`, and almost surely every walker of the
actual recursive trajectory satisfies `κ ≤ liminf X_n^i / n`.  This is the concrete-array form
of `Swarming.Enl.ProjVbound.projected_speed_uniform` (proved there through the paper's
time-projected potential `H_{j,n}`, its `(Vdrift)`, `(Vbound)` and `(Jbound)` budgets, and the
martingale strong law for the projected ledger `Qpl`). -/
theorem actualProjectedBallistic {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop :=
  Swarming.Enl.ProjVbound.projected_speed_uniform hp0 hp1 hm

/-- **Proposition `ball` (both halves) for the concrete array model, with no hypothesis.**

The paper's interval `κ(m,p) ≤ liminf X_n^i/n ≤ limsup X_n^i/n ≤ 2p-1`: the lower bound is the
projected-potential occupation front (`actualProjectedBallistic`), the upper bound is the
exact drift identity of `(mart)` (`SwarmDens.ae_limsup_pos_div_le`, applied to the concrete
system through `actual_isInteractingLaw`).  `κ` is independent of `N`. -/
theorem actual_ballistic_interval {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop ∧
      limsup (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop ≤ 2 * p - 1 := by
  obtain ⟨κ, hκpos, hκlim⟩ := actualProjectedBallistic hp0 hp1 hm
  refine ⟨κ, hκpos, fun N hN => ?_⟩
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hex : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      IsInteractingLaw 𝓕 (arrayMeasure N) (actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  obtain ⟨𝓕, hlaw⟩ := hex
  filter_upwards [hκlim N hN,
    MeasureTheory.ae_all_iff.mpr (fun i : Fin N =>
      SwarmDens.ae_limsup_pos_div_le (X := actualX (N := N) p m) hlaw (le_of_lt hp0) (le_of_lt hp1) i)]
    with U hU hsup
  intro i
  exact ⟨hU i, hsup i⟩

/-- **The regeneration data of the paper, asked for at the concrete array model only.**

`Swarm.RegenAvailable` quantifies over every system satisfying `IsInteractingLaw`; the paper's
Propositions `front` + `regen` are statements about the paper's model, so this is the
source-faithful form.  It is `∃ (D T), RegenLaw ∧ Sandwich` for each `N ≥ 2`. -/
def ActualRegen (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∃ (D T : ℕ → Array N → ℕ),
    RegenLaw (arrayMeasure N) D T ∧
    Sandwich (arrayMeasure N) (actualX (N := N) p m) D T

/-- The class-level regeneration input implies its concrete-array form (so `ActualRegen` is
not a stronger hypothesis than the paper's `front` + `regen`). -/
theorem actualRegen_of_regenAvailable {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (h : RegenAvailable m p) : ActualRegen m p := by
  intro N hN
  have hex : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      IsInteractingLaw 𝓕 (arrayMeasure N) (actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  obtain ⟨𝓕, hlaw⟩ := hex
  exact h N (Array N) (arrayMeasure N) (actualX (N := N) p m) 𝓕 hN hlaw

/-- **Theorem 1.1 of `main_1d_revised.tex` for the concrete array construction, from the
regeneration input alone.**

There is `κ(m,p) > 0`, independent of `N`, such that for every `N ≥ 2` and every pair of
regeneration increments `(D,T)` with `RegenLaw` and the path structure `Sandwich`, the speed
`v = E[D_0]/E[T_0]` lies in `[κ, 2p-1]` and almost surely **every** walker has
`lim_n X_n^i/n = v`.

`Swarm.Ballistic` — the open class-level occupation bound — is *not* a hypothesis: the lower
bound is `actualProjectedBallistic`, the upper bound is `speed_le_two_p_sub_one_of_regen`, and
the limit is `ae_tendsto_of_regen`. -/
theorem main_theorem_actual_of_actual_regeneration {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hregen : ActualRegen m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  obtain ⟨κ, hκpos, hκlim⟩ := actualProjectedBallistic hp0 hp1 hm
  refine ⟨κ, hκpos, fun N hN => ?_⟩
  obtain ⟨D, T, hreg, hsand⟩ := hregen N hN
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hex : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      IsInteractingLaw 𝓕 (arrayMeasure N) (actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  obtain ⟨𝓕, hlaw⟩ := hex
  refine ⟨(∫ U, (D 0 U : ℝ) ∂(arrayMeasure N)) / (∫ U, (T 0 U : ℝ) ∂(arrayMeasure N)),
    ?_, ?_, ?_⟩
  · exact ballistic_le_speed_liminf (X := actualX (N := N) p m) hreg hsand
      (by filter_upwards [hκlim N hN] with U hU i; simpa using hU i) (by omega)
  · exact speed_le_two_p_sub_one_of_regen (X := actualX (N := N) p m) hlaw hreg hsand
      (le_of_lt hp0) (by omega)
  · filter_upwards [ae_tendsto_of_regen (X := actualX (N := N) p m) hreg hsand] with U hU i
    simpa using hU i

/-- **The paper's Theorem 1.1 for the paper's model, from `front` + `regen` only.**

The class-level `Swarm.RegenAvailable` (Propositions `front` + `regen`) alone yields, for the
concrete i.i.d.-uniform array construction, `κ(m,p) > 0` uniform in `N` and, for every `N ≥ 2`,
a common speed `v ∈ [κ, 2p-1]` for all walkers.  Neither `Swarm.Ballistic` nor
`Swarm.InitialRegen` is used. -/
theorem main_claim_actual_of_regenAvailable {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hregen : RegenAvailable m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) :=
  main_theorem_actual_of_actual_regeneration hp0 hp1 hm
    (actualRegen_of_regenAvailable hp0 hp1 hregen)

/-- The class-level target `Swarm.MainClaim` does imply the concrete-model statement, so the
theorem above is a genuine *sub-target*: the gap between `MainClaim` and the paper's Theorem 1.1
is exactly the class-level (generic-marginal) strengthening of `Ballistic` and `RegenAvailable`. -/
theorem mainClaim_implies_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (h : MainClaim m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  obtain ⟨κ, hκpos, hsys⟩ := h
  refine ⟨κ, hκpos, fun N hN => ?_⟩
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hex : ∃ 𝓕 : Filtration ℕ (inferInstanceAs (MeasurableSpace (Array N))),
      IsInteractingLaw 𝓕 (arrayMeasure N) (actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  obtain ⟨𝓕, hlaw⟩ := hex
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    hsys N (Array N) (arrayMeasure N) (actualX (N := N) p m) 𝓕 hN hlaw
  exact ⟨v, hv1, hv2, by filter_upwards [hv3] with U hU i; simpa using hU i⟩

/-- Non-vacuity witness: at `m = 2`, `p = 3/4` the paper's theorem for the concrete model holds
as soon as the regeneration input is supplied at those parameters. -/
theorem main_claim_actual_three_quarters_of_regen
    (hregen : RegenAvailable 2 (3 / 4)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * (3 / 4) - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory (3 / 4) 2 U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v) :=
  main_claim_actual_of_regenAvailable (p := 3 / 4) (by norm_num) (by norm_num)
    (m := 2) (by norm_num) hregen

end Swarm

/-! ### Axiom audit -/


