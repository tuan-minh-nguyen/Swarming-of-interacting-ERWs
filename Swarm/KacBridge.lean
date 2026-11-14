/-
# The Kac step with `π(F) > 0` supplied by the invariant law

> "We take an invariant probability measure `π` from Proposition `front`. …
>  `P_π(A) = π(F) P(V) > 0` … `E^*D = (1/P_π(A)) ∫_A D dP_π ≤ 1/(π(F)P(V)) < ∞`."

The two halves live in different files and different spaces:

* `FrontThin.lean` produces, from tightness of the record-kernel iterates alone, an
  invariant probability `π` on `RecState N m` with `0 < π (srSet)`;
* `KacPaperED.lean` turns the Kac inequality plus the factorisation `μ A = pf * pv` into
  `1 ≤ E^*D ≤ 1/(pf * pv) < ∞` for an abstract stationary system `(Ω, μ, e)`.

This file composes them: the factor `pf` is *instantiated* at `π (srSet)` and its strict
positivity is *proved*, not assumed.  What remains a hypothesis is the identity
`μ A = π (srSet) · P(V)` together with `P(V) > 0` — the paper's `(freshlaw)` read on the
two-sided stationary record sequence.  Its formalisation needs the two-sided
Kolmogorov extension of the record Markov chain, which the campaign does not have (see
`README.md`, "Residual gap"); it is flagged here as an explicit argument, not hidden.
-/
import Swarm.KacPaperED
import Swarm.FrontThin

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFront

open SimJump SimJump.RecKernel SwarmRec SwarmKB

/-- **The paper's `(ED)` on the stationary record sequence, with `π(F) > 0` derived from the
invariant law.**  For an invariant record-state law `π` with `0 < π (srSet)` (obtained from
tightness by `exists_invariant_measure_srSet_quantitative`), an invertible
measure-preserving shift `e`, a regeneration event `A` whose mass factorises as
`μ A = π (srSet) · pv` with `pv = P(V) > 0`, an `ℕ`-valued regeneration distance `g ≥ 1`
read off the translated block through `Φ`, one obtains

  `Integrable (fun q => (g q : ℝ)) ν`, `1 ≤ E^*D`, and `E^*D ≤ 1/(π(F)P(V))`.

Only `hmass`, `hpv` and `hg1` are carried as hypotheses; `π (srSet) ≠ 0` and
`π (srSet) ≠ ⊤` are discharged by the invariant law. -/
theorem record_ED_of_invariant_mass {N m : ℕ} (π : Measure (RecState N m))
    [IsProbabilityMeasure π] (hπpos : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pv : ℝ≥0∞) (hpv : 0 < pv) (hpvt : pv ≠ ⊤)
    (hmass : μ A = π (srSet N m) * pv) :
    Integrable (fun q => (g q : ℝ)) ν ∧
      1 ≤ ∫ q, (g q : ℝ) ∂ν ∧
        ∫ q, (g q : ℝ) ∂ν ≤ ((π (srSet N m) * pv)⁻¹).toReal :=
  SwarmKac.kac_path_ED e he Φ hΦ ν A hA hfac g hg hg1 hD
    (π (srSet N m)) pv hπpos hpv (measure_ne_top π _) hpvt hmass

/-- **The same statement with the invariant law itself produced from tightness.**  The
existential `π` is the one supplied by Proposition `front`, and the side conditions on
`π (srSet)` are discharged inside. -/
theorem exists_record_ED_of_tight {N m : ℕ} (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ₀ : Measure (RecState N m)) [IsProbabilityMeasure μ₀]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm))^[r]
        μ₀ (SwarmRec.exh N m K)ᶜ ≤ ε)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pv : ℝ≥0∞) (hpv : 0 < pv) (hpvt : pv ≠ ⊤) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (srSet N m) ∧
      (μ A = π (srSet N m) * pv →
        Integrable (fun q => (g q : ℝ)) ν ∧
          1 ≤ ∫ q, (g q : ℝ) ∂ν ∧
            ∫ q, (g q : ℝ) ∂ν ≤ ((π (srSet N m) * pv)⁻¹).toReal) := by
  obtain ⟨π, hprob, hinv, hpos⟩ :=
    srSet_mass_pos (N := N) (m := m) p hp hp1 hp_lt hm hN μ₀ htight
  exact ⟨π, hprob, hinv, hpos,
    fun hmass => record_ED_of_invariant_mass π hpos e he Φ hΦ ν A hA hfac g hg hg1 hD
      pv hpv hpvt hmass⟩

end SwarmFront
