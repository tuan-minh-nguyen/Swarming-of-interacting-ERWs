/-  Everything below is *independently re-derived* in this file (not imported from another
  member's directory) and then axiom-audited.  The two re-derivations are the two structural
  facts that decide what `Swarm.MainClaim` really needs:

  * `initialRegen_free_audit` : `Swarm.InitialRegen m p` holds for **every** `m, p`, i.e. the
    third named input of `Swarm.main_theorem` is not an input.  It is a two-line consequence of
    the integrated `Swarm.ae_tendsto_of_regen` (`S = 0`, `c = 0`), which gives the *untranslated*
    limit from `RegenLaw` + `Sandwich` alone; the initial-regeneration `P*`/Kac argument of the
    paper is never needed *as the Lean statement is written*.

  * `mainClaim_of_ballistic_commonLimit_audit` : `MainClaim m p` follows from
    `Ballistic m p` together with the bare existence of a common deterministic limit
    (`CommonLimit`).  So the whole remaining content of the regeneration input for the final
    theorem is "all walkers have a common limit", not the increments, their independence, Kac's
    formula or `Sandwich`; those are only a sufficient route.

  Consequence recorded in `AUDIT.md`: `MainClaim m p` is equivalent to
  `Ballistic m p ∧ CommonLimit m p`, and no result in the repository proves either conjunct.
-/
import Swarm.Assembly
import Swarm.ActualInstance
import Swarm.Fidelity

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace SwarmAudit

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-! ## 1. `InitialRegen` is not an input -/

/-- The conclusion of `Swarm.InitialRegen`, with the shift `S = 0` and the translation `c = 0`:
the limit is already available under the original measure. -/
theorem initialRegen_conclusion {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Fin N → ℤ} {D T : ℕ → Ω → ℕ}
    (hreg : Swarm.RegenLaw μ D T) (hsand : Swarm.Sandwich μ X D T) :
    ∀ᵐ ω ∂μ, ∃ (S : ℕ) (c : ℝ), ∀ i : Fin N,
      Tendsto (fun n => (Swarm.pos X (n + S) i ω - c) / n) atTop
        (𝓝 ((∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ))) := by
  filter_upwards [Swarm.ae_tendsto_of_regen hreg hsand] with ω hω
  exact ⟨0, 0, fun i => by simpa using hω i⟩

/-- **`Swarm.InitialRegen m p` is a theorem for every `m` and `p`.** -/
theorem initialRegen_free_audit (m : ℕ) (p : ℝ) : Swarm.InitialRegen m p := by
  intro N Ω _ μ _ X 𝓕 _hN _hlaw D T hreg hsand
  exact initialRegen_conclusion hreg hsand

/-! ## 2. The exact two-input decomposition of the final target -/

/-- The bare common-limit statement.  This is *not* `Swarm.RegenAvailable`: it asks only for the
limit, and drops the regeneration increments, their independence, integrability and `Sandwich`. -/
def CommonLimit (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
      ∃ v : ℝ, ∀ᵐ ω ∂μ, ∀ i : Fin N,
        Tendsto (fun n => Swarm.pos X n i ω / n) atTop (𝓝 v)

/-- **`MainClaim m p` from `Ballistic m p` and the bare common limit.**  The lower bound is
`Ballistic`'s `kappa` (transferred through `liminf`), the upper bound is the integrated
`Swarm.speed_le_two_p_sub_one`, and the common value is the supplied `v`. -/
theorem mainClaim_of_ballistic_commonLimit_audit {m : ℕ} {p : ℝ} (_hm : 2 ≤ m)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hball : Swarm.Ballistic m p) (hlim : CommonLimit m p) : Swarm.MainClaim m p := by
  obtain ⟨κ, hκpos, hκ⟩ := hball
  refine ⟨κ, hκpos, ?_⟩
  intro N Ω _ μ _ X 𝓕 hN hlaw
  obtain ⟨v, hv⟩ := hlim N Ω μ X 𝓕 hN hlaw
  haveI : NeBot (ae μ) := ae_neBot.mpr (by
    intro hzero
    have h1 : μ Set.univ = 1 := measure_univ
    rw [hzero] at h1
    simp at h1)
  have hlow := hκ N Ω μ X 𝓕 hN hlaw
  have hpoint : ∀ᵐ ω ∂μ, κ ≤ v := by
    filter_upwards [hlow, hv] with ω hω hωv
    let i₀ : Fin N := ⟨0, by omega⟩
    rw [← (hωv i₀).liminf_eq]
    exact hω i₀
  have hκv : κ ≤ v := by
    obtain ⟨ω₀, hω₀⟩ := hpoint.exists
    exact hω₀
  have hv2 : v ≤ 2 * p - 1 := by
    have i₀ : Fin N := ⟨0, by omega⟩
    refine Swarm.speed_le_two_p_sub_one hlaw hp1.le i₀ ?_
    filter_upwards [hv] with ω hω
    exact hω i₀
  exact ⟨v, hκv, hv2, hv⟩

end SwarmAudit

/-! ## 3. Axiom audit of the integrated named targets -/


