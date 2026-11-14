/-
# From the Kac bound to `E^*D ≤ 1/(π(F)P(V))`

`KacDisjoint.lean` proves the Kac bound `∫_A D dP_π ≤ 1` for an invertible
measure-preserving `θ` and the first return time `D` to `A`.  The paper
(`main_1d_revised.tex` §3.2, proof of Proposition `regen`) then writes

> "Since the concatenated path has law `P^*` conditional on `A`, we obtain
> `E^*D = (1/P_π(A)) ∫_A D dP_π ≤ 1/(π(F)P(V)) < ∞`."

and, just before,

> "By (freshlaw), we have `P_π(A) = π(F)P(V)`, `P_π(X ∈ B | A) = P^*(B)`."

This file isolates exactly the measure-theoretic transfer used there.  The
factorization hypothesis is the sum over `(d,t)` of the paper's identity
`(factor)`:

`hfac : ∀ B, P_π(A ∩ Φ ⁻¹' B) = P_π(A) · P^*(B)`,

where `Φ` is the map "read off the path segment from the concatenated path"
(so that the regeneration distance `D` is `g ∘ Φ` for a path functional `g`).

Conclusions:

* `map_restrict_eq_smul_of_factorization`: `(P_π ↾ A).map Φ = P_π(A) • P^*`;
* `kac_conditional_mean_eq`: `E_{P_π(·|A)}[D] = E^*[D]`, i.e. the paper's
  `E^*D = (1/P_π(A)) ∫_A D dP_π`;
* `kac_path_mean_le`: `E^*[D] ≤ (P_π A)⁻¹`;
* `kac_paper_bound`: with `P_π(A) = π(F) P(V)` this is `E^*D ≤ 1/(π(F)P(V))`.

Every declaration is checked by `verify.sh` and `Audit.lean` (`#print axioms`).
-/
import Swarm.Imports
import Swarm.KacDisjoint

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace KacFormula

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Conditioning identity for the record law.**  If the law `ν` of the
translated future satisfies the paper's factorization
`μ (A ∩ Φ ⁻¹' B) = μ A * ν B`, then the law of `Φ` under the conditioned
measure `μ(·|A)` is `ν`.  This is `P_π(X ∈ B | A) = P^*(B)` from §3.2. -/
theorem map_restrict_eq_smul_of_factorization {P : Type*} [MeasurableSpace P]
    (Φ : Ω → P) (hΦ : Measurable Φ) (A : Set Ω) (hA : MeasurableSet A)
    (ν : Measure P)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B) :
    (μ.restrict A).map Φ = μ A • ν := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hΦ hB, Measure.restrict_apply (hΦ hB), Measure.smul_apply,
    smul_eq_mul, inter_comm, hfac B hB]

/-- Integrating a function of `Φ` against the restricted measure, when the law of
`Φ` under the restriction is `c • ν`. -/
theorem lintegral_restrict_comp {P : Type*} [MeasurableSpace P]
    (Φ : Ω → P) (hΦ : Measurable Φ) (A : Set Ω) (ν : Measure P) (c : ℝ≥0∞)
    (g : P → ℝ≥0∞) (hg : Measurable g)
    (hmap : (μ.restrict A).map Φ = c • ν) :
    ∫⁻ ω in A, g (Φ ω) ∂μ = c * ∫⁻ p, g p ∂ν := by
  rw [← lintegral_map hg hΦ, hmap, lintegral_smul_measure, smul_eq_mul]

section Transfer

variable [IsProbabilityMeasure μ]

/-- **Transfer of the Kac bound to the conditioned path law**: the mean of the
regeneration distance under `μ(·|A)` equals its mean under the path law `ν`.
This is the paper's `E^*D = (1/P_π(A)) ∫_A D dP_π`. -/
theorem kac_conditional_mean_eq (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ∞) (hg : Measurable g)
    (hD : ∀ ω, retTime (e : Ω → Ω) A ω = g (Φ ω)) :
    ∫⁻ ω, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = ∫⁻ p, (g p : ℝ≥0∞) ∂ν := by
  have hgc : Measurable (fun p => (g p : ℝ≥0∞)) := measurable_enat_coe.comp hg
  have hmap := map_restrict_eq_smul_of_factorization (μ := μ) Φ hΦ A hA ν hfac
  have h1 : ∫⁻ ω, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = (μ A)⁻¹ * ∫⁻ ω in A, (g (Φ ω) : ℝ≥0∞) ∂μ := by
    rw [lintegral_smul_measure]
    congr 1
    exact lintegral_congr fun ω => by rw [hD ω]
  rw [h1, lintegral_restrict_comp Φ hΦ A ν (μ A) (fun p => (g p : ℝ≥0∞)) hgc hmap]
  have hne : μ A ≠ 0 := ne_of_gt hApos
  have hne_top : μ A ≠ ⊤ := measure_ne_top μ A
  rw [← mul_assoc, ENNReal.inv_mul_cancel hne hne_top, one_mul]

/-- **The paper's bound `E^*D ≤ 1/P_π(A)`**: the mean regeneration distance under
the conditioned path law is at most the reciprocal of the mass of `A`. -/
theorem kac_path_mean_le (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ∞) (hg : Measurable g)
    (hD : ∀ ω, retTime (e : Ω → Ω) A ω = g (Φ ω)) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (μ A)⁻¹ := by
  rw [← kac_conditional_mean_eq e he Φ hΦ ν A hA hApos hfac g hg hD]
  exact kac_cond_mean_le e he A hA

/-- **The paper's `E^*D ≤ 1/(π(F)P(V))`**, stated with the factorization mass
`a = π(F) P(V)` of `A` made explicit. -/
theorem kac_paper_bound (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ∞) (hg : Measurable g)
    (hD : ∀ ω, retTime (e : Ω → Ω) A ω = g (Φ ω))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpf_top : pf ≠ ⊤) (hpv_top : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  rw [← hmass]
  refine kac_path_mean_le e he Φ hΦ ν A hA ?_ hfac g hg hD
  rw [hmass]
  exact ENNReal.mul_pos hpf hpv

end Transfer

end KacFormula
