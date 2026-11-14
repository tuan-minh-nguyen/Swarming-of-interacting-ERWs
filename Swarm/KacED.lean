/-
# The paper's `(ED)` for a one-sided system, with no invertible extension

`M2KacExt.kac_path_ED_of_extension` and `Swarm/KacBridge.lean`'s
`SwarmFront.record_ED_of_invariant_mass` obtain the paper's

   `Integrable g ∧ 1 ≤ E^*[D] ∧ E^*[D] ≤ 1/(π(F) P(V)) < ∞`

for a one-sided stationary record system by **assuming** an invertible measure-preserving
extension of it that factors the shift, `KAC_EXTENSION.md` §2's named residual, whose
construction is the projective limit of the stationary window laws.

`KacMP.lean` proves that the Kac inequality holds for every measure-preserving self-map of a
probability space, with no extension.  This file therefore removes the extension from `(ED)`:

* `kac_path_bound_mp` / `kac_path_ED_mp` are `kac_path_bound_of_extension` /
  `kac_path_ED_of_extension` with `{g₀ : Ω' ≃ᵐ Ω'}`, the extension measure `μ'` and the factor
  map `π : Ω' → Ω` deleted, and `MeasurePreserving f μ μ` added.  Everything else — the
  factorisation `(factor)` `μ (A ∩ Φ ⁻¹' B) = μ A · ν B`, `D = g ∘ Φ`, the mass identity
  `μ A = pf · pv` — is unchanged;
* `record_ED_of_invariant_mass_mp` / `exists_record_ED_of_tight_mp` are
  `SwarmFront.record_ED_of_invariant_mass` / `exists_record_ED_of_tight` with the extension
  deleted, the invariant record law `π` still coming from `FrontThin.srSet_mass_pos`.

What is *not* claimed: the stopped record chain itself is not constructed here, `π` is not
constructed where tightness is absent, and the mass identity `μ A = π (srSet) · P(V)` is still
an explicit hypothesis (`StationaryMass`/`MassSharp` show invariance alone cannot supply it).
`MainClaim`, `Ballistic` and `RegenAvailable` are untouched.
-/
import Swarm.KacMP
import Swarm.KacBridge

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace SwarmKacMP

section PathED

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Type*} [MeasurableSpace P]

/-- **The paper's `E^*D ≤ 1/(π(F)P(V))` for a one-sided system, without any extension.**
`SwarmM2Kac.condMean_eq_oneSided` supplies the conditioning identity and `KacMP.kac_mp_*` the
Kac bound; invertibility is used by neither. -/
theorem kac_path_bound_mp {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  have hApos : 0 < μ A := by
    rw [hmass]
    exact ENNReal.mul_pos hpf hpv
  rw [← SwarmM2Kac.condMean_eq_oneSided (f := f) Φ hΦ ν A hA hApos hfac g hg hD]
  have hbound : ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1 :=
    kac_mp_lintegral_le_one hmp A hA
  have hle := SwarmM2Kac.condMean_le_of_bound (μ := μ) (f := f) A hA hbound
  simpa [hmass] using hle

/-- **The paper's `(ED)`, `1 ≤ E^*D < ∞`, for a one-sided stationary system — no extension.**
`M2KacExt.kac_path_ED_of_extension` with every extension datum removed. -/
theorem kac_path_ED_mp {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) [IsProbabilityMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ p, 1 ≤ g p)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      1 ≤ ∫ p, (g p : ℝ) ∂ν ∧
        ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  have hmain := kac_path_bound_mp hf hmp Φ hΦ ν A hA hfac g hg hD
    pf pv hpf.ne' hpv.ne' hpft hpvt hmass
  have hlt : ∫⁻ p, (g p : ℝ≥0∞) ∂ν < ⊤ :=
    lt_of_le_of_lt hmain (ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne'))
  have hint : Integrable (fun p => (g p : ℝ)) ν :=
    SwarmKac.integrable_natCast_of_lintegral_ne_top hg hlt.ne
  refine ⟨hint, SwarmKac.one_le_integral_of_one_le hint hg1, ?_⟩
  rw [SwarmKac.integral_natCast_eq_toReal hg hlt.ne]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne').ne')
    hmain

end PathED

/-! ## The record chain: `(ED)` with `π(F) > 0` from the invariant law, no extension -/

section RecordChain

open SwarmRec

/-- **The paper's `(ED)` on the stationary record sequence, without an invertible extension.**
`SwarmFront.record_ED_of_invariant_mass` with `e : Ω ≃ᵐ Ω` replaced by a merely measurable and
measure-preserving one-sided shift `f`.  The factor `pf = π (srSet)` and its strict positivity
are still supplied by the invariant record law. -/
theorem record_ED_of_invariant_mass_mp {N m : ℕ} (π : Measure (RecState N m))
    [IsProbabilityMeasure π] (hπpos : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pv : ℝ≥0∞) (hpv : 0 < pv) (hpvt : pv ≠ ⊤)
    (hmass : μ A = π (srSet N m) * pv) :
    Integrable (fun q => (g q : ℝ)) ν ∧
      1 ≤ ∫ q, (g q : ℝ) ∂ν ∧
        ∫ q, (g q : ℝ) ∂ν ≤ ((π (srSet N m) * pv)⁻¹).toReal :=
  kac_path_ED_mp hf hmp Φ hΦ ν A hA hfac g hg hg1 hD
    (π (srSet N m)) pv hπpos hpv (measure_ne_top π _) hpvt hmass

/-- **The same statement with the invariant law itself produced from tightness, and no
extension hypothesis anywhere.**  Compare `SwarmFront.exists_record_ED_of_tight`. -/
theorem exists_record_ED_of_tight_mp {N m : ℕ} (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ₀ : Measure (RecState N m)) [IsProbabilityMeasure μ₀]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm))^[r]
        μ₀ (SwarmRec.exh N m K)ᶜ ≤ ε)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pv : ℝ≥0∞) (hpv : 0 < pv) (hpvt : pv ≠ ⊤) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (srSet N m) ∧
      (μ A = π (srSet N m) * pv →
        Integrable (fun q => (g q : ℝ)) ν ∧
          1 ≤ ∫ q, (g q : ℝ) ∂ν ∧
            ∫ q, (g q : ℝ) ∂ν ≤ ((π (srSet N m) * pv)⁻¹).toReal) := by
  obtain ⟨π, hprob, hinv, hpos⟩ := SwarmFront.srSet_mass_pos (N := N) (m := m) p hp hp1 hp_lt hm hN μ₀ htight
  exact ⟨π, hprob, hinv, hpos, fun hmass =>
    record_ED_of_invariant_mass_mp π hpos hf hmp Φ hΦ ν A hA hfac g hg hg1 hD pv hpv hpvt hmass⟩

end RecordChain

end SwarmKacMP
