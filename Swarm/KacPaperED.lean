/-
# The paper's display `1 ≤ E^*D < ∞`

  `1 ≤ E^*D < ∞`.

`KacMean.lean` supplies the upper half `E^*D ≤ 1/(π(F)P(V))` together with Bochner
integrability of the `ℕ`-valued record distance.  The lower half is the trivial part of the
paper (`D ≥ 1`, so `E^*D ≥ 1` on a probability space), recorded here because the assembly's
`Swarm.RegenLaw` needs the increments to be integrable *before* `1 ≤ E^*D` is even
meaningful, and because the two halves together are what Proposition `regen` asserts.

Main results:

* `one_le_integral_of_one_le` — an integrable `ℕ`-valued function with `g ≥ 1` has mean at
  least `1` on a probability space;
* `kac_path_ED` — the pair `1 ≤ E^*D` and `E^*D ≤ 1/(π(F)P(V))` with integrability, all from
  the Kac bound plus `pf, pv > 0`.
-/
import Swarm.KacMean

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace SwarmKac

variable {P : Type*} [MeasurableSpace P] {ν : Measure P}

/-- A `ℕ`-valued function bounded below by `1` has integral at least `1`. -/
theorem one_le_integral_of_one_le [IsProbabilityMeasure ν] {g : P → ℕ}
    (hint : Integrable (fun p => (g p : ℝ)) ν) (hg1 : ∀ p, 1 ≤ g p) :
    1 ≤ ∫ p, (g p : ℝ) ∂ν := by
  have hone : ∫ _ : P, (1 : ℝ) ∂ν = 1 := by simp
  rw [← hone]
  refine integral_mono (integrable_const 1) hint (fun p => ?_)
  have h1 : (1 : ℝ) ≤ (g p : ℝ) := by exact_mod_cast hg1 p
  simpa using h1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The paper's `(ED)`: `1 ≤ E^*D ≤ 1/(π(F)P(V)) < ∞`**, with the mean automatically
integrable.  The hypotheses are exactly the Kac transfer's: an invertible measure-preserving
shift `e`, the regeneration event `A`, the translated-block map `Φ` with abundant law `ν`,
the paper's factorisation `(factor)`, an `ℕ`-valued distance functional `g`, and the two mass
factors `pf = π(F)`, `pv = P(V)` with `μ A = pf * pv`. -/
theorem kac_path_ED (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) [IsProbabilityMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ p, 1 ≤ g p)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      1 ≤ ∫ p, (g p : ℝ) ∂ν ∧
        ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  obtain ⟨hint, hle, -⟩ :=
    kac_path_bound_of_pos e he Φ hΦ ν A hA hfac g hg hD pf pv hpf hpv hpft hpvt hmass
  exact ⟨hint, one_le_integral_of_one_le hint hg1, hle⟩

end SwarmKac
