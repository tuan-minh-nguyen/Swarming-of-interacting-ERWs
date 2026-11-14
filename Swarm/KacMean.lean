/-
# The Kac step in numerical form: finite mean regeneration distance

Paper `main_1d_revised.tex`, proof of Proposition `regen`:

  `E^*D = (1/P_π(A)) ∫_A D dP_π ≤ 1/(π(F)P(V)) < ∞`.

`Swarm/KacDisjoint.lean` proves the disjoint-set Kac inequality `∫_A D dP_π ≤ 1`, and
`Swarm/KacTransfer.lean` transfers it to the abundant law `P^*`:
`∫⁻ p, ↑(g p) ∂ν ≤ (pf * pv)⁻¹` for an `ℕ∞`-valued path functional `g` and the factorised
mass `pf * pv` of `A`.

What the assembly consumes and what those files do not yet provide is the *numerical*
form: the record distance is `ℕ`-valued, the bound is finite, the mean is a real number,
and the functional is Bochner integrable — the `Integrable (fun ω => (D i ω : ℝ)) μ`
conjunct of `Swarm.RegenLaw` / `Swarm.RegenLawWeak`.  This file supplies it.  Every
declaration is proved outright; no conclusion is assumed.

Main results:

* `integrable_natCast_of_lintegral_ne_top`, `integral_natCast_eq_toReal` — an `ℕ`-valued
  function with finite `ℝ≥0∞` integral is Bochner integrable, with the expected real
  integral;
* `kac_path_mean_le_nat` — the paper's Kac bound for an `ℕ`-valued record distance;
* `kac_path_mean_lt_top`, `kac_path_integrable`, `kac_path_real_mean_le` — the finite-mean
  form `E^*D ≤ 1/(π(F)P(V)) < ∞`;
* `kac_path_bound_of_pos` — the same with `π(F) > 0`, `P(V) > 0` as the two strict
  inequalities (`pf ≠ 0` is *derived*);
* `retTime_toNat_coe` — the `D`/`D.toNat` conversion used by the conditioned-law form;
* `kac_cond_integrable_and_mean_le` — under the conditioned law `P_π(· | A)` the return
  time is Bochner integrable with real mean at most `1/μ(A)`.
-/
import Swarm.KacTransfer

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace SwarmKac

variable {P : Type*} [MeasurableSpace P] {ν : Measure P}

/-! ### `ℕ`-valued functions with finite `ℝ≥0∞` integral -/

/-- An `ℕ`-valued function whose `ℝ≥0∞` integral is finite is Bochner integrable. -/
theorem integrable_natCast_of_lintegral_ne_top {g : P → ℕ} (hg : Measurable g)
    (h : ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≠ ⊤) :
    Integrable (fun p => (g p : ℝ)) ν := by
  have hm : Measurable fun p => (g p : ℝ≥0∞) :=
    (show Measurable fun n : ℕ => (n : ℝ≥0∞) from by fun_prop).comp hg
  have h' : Integrable (fun p => ((g p : ℝ≥0∞)).toReal) ν :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hm.aemeasurable h
  simpa only [ENNReal.toReal_natCast] using h'

/-- The real integral of an `ℕ`-valued function is the `toReal` of its `ℝ≥0∞` integral. -/
theorem integral_natCast_eq_toReal {g : P → ℕ} (hg : Measurable g)
    (h : ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≠ ⊤) :
    ∫ p, (g p : ℝ) ∂ν = (∫⁻ p, (g p : ℝ≥0∞) ∂ν).toReal := by
  have hm : Measurable fun p => (g p : ℝ≥0∞) :=
    (show Measurable fun n : ℕ => (n : ℝ≥0∞) from by fun_prop).comp hg
  have hae : ∀ᵐ p ∂ν, (fun p => (g p : ℝ≥0∞)) p < ⊤ := MeasureTheory.ae_lt_top hm h
  have h2 := MeasureTheory.integral_toReal (μ := ν) hm.aemeasurable hae
  simpa only [ENNReal.toReal_natCast] using h2

end SwarmKac

namespace SwarmKac

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Type*} [MeasurableSpace P]

/-- **The paper's Kac bound for an `ℕ`-valued record distance**:
`∫⁻ p, ↑(g p) ∂ν ≤ (pf * pv)⁻¹`, where `pf = π(F)`, `pv = P(V)` and `μ A = pf * pv` is
the fresh-law factorisation of the regeneration event. -/
theorem kac_path_mean_le_nat (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  have hgm : Measurable fun p : P => ((g p : ℕ) : ℕ∞) :=
    (show Measurable fun n : ℕ => (n : ℕ∞) from measurable_of_countable _).comp hg
  have h := KacFormula.kac_paper_bound e he Φ hΦ ν A hA hfac
    (fun p => ((g p : ℕ) : ℕ∞)) hgm hD pf pv hpf hpv hpft hpvt hmass
  simpa only [ENat.toENNReal_coe] using h

/-- The Kac bound is finite. -/
theorem kac_path_mean_lt_top (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν < ⊤ :=
  lt_of_le_of_lt
    (kac_path_mean_le_nat e he Φ hΦ ν A hA hfac g hg hD pf pv hpf hpv hpft hpvt hmass)
    (ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf hpv))

/-- **Finite mean record distance**: the distance functional is Bochner integrable under
the abundant law `P^*`.  This is precisely the `Integrable (fun ω => (D i ω : ℝ)) μ`
conjunct of `Swarm.RegenLaw` and of the weakened `Swarm.RegenLawWeak`. -/
theorem kac_path_integrable (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν :=
  integrable_natCast_of_lintegral_ne_top hg
    (ne_top_of_lt (kac_path_mean_lt_top e he Φ hΦ ν A hA hfac g hg hD pf pv
      hpf hpv hpft hpvt hmass))

/-- **The paper's numerical bound** `E^*D ≤ 1/(π(F)P(V))` as an inequality of real
numbers, with the mean finite by `kac_path_integrable`. -/
theorem kac_path_real_mean_le (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  have hfin :=
    kac_path_mean_lt_top e he Φ hΦ ν A hA hfac g hg hD pf pv hpf hpv hpft hpvt hmass
  rw [integral_natCast_eq_toReal hg (ne_top_of_lt hfin)]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf hpv).ne')
    (kac_path_mean_le_nat e he Φ hΦ ν A hA hfac g hg hD pf pv hpf hpv hpft hpvt hmass)

/-- The bound `1/(π(F)P(V))` is finite and nonzero whenever both mass factors are. -/
theorem inv_mul_ne_top_of_ne {pf pv : ℝ≥0∞} (hpf : pf ≠ 0) (hpv : pv ≠ 0)
    (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤) :
    (pf * pv)⁻¹ ≠ ⊤ ∧ (pf * pv)⁻¹ ≠ 0 :=
  ⟨ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf hpv).ne',
    ENNReal.inv_ne_zero.2 (ENNReal.mul_ne_top hpft hpvt)⟩

/-- **The paper's bound with strict positivity of the two mass factors**, which is the form
in which the invariant-law step supplies it: `π(F) > 0` comes from Proposition `front` and
`P(V) > 0` is the seed-positivity statement.  Both `pf ≠ 0` and `pv ≠ 0` are *derived*
here, not assumed. -/
theorem kac_path_bound_of_pos (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal ∧ (pf * pv)⁻¹ < ⊤ := by
  have hpf0 : pf ≠ 0 := hpf.ne'
  have hpv0 : pv ≠ 0 := hpv.ne'
  refine ⟨kac_path_integrable e he Φ hΦ ν A hA hfac g hg hD pf pv hpf0 hpv0 hpft hpvt hmass,
    kac_path_real_mean_le e he Φ hΦ ν A hA hfac g hg hD pf pv hpf0 hpv0 hpft hpvt hmass, ?_⟩
  exact ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne')

end SwarmKac

namespace SwarmKac

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Conversion of the `ℕ∞`-valued return time to its `ℕ`-valued `toNat` form, under
finiteness. -/
theorem retTime_toNat_coe {f : Ω → Ω} {A : Set Ω} {ω : Ω}
    (h : ((KacFormula.retTime f A ω : ℕ∞) : ℝ≥0∞) < ⊤) :
    ((KacFormula.retTime f A ω).toNat : ℝ≥0∞) = ((KacFormula.retTime f A ω : ℕ∞) : ℝ≥0∞) := by
  have h' : KacFormula.retTime f A ω ≠ ⊤ := by
    intro hc
    rw [hc] at h
    simp at h
  conv_rhs => rw [← ENat.natCast_toNat h']
  exact ENat.toENNReal_coe _

/-- **Kac under the conditioned law `P_π(· | A)`, numerical form.**  The conditioned mean
return time is at most `1/μ(A)` as a real number, and the return time is Bochner integrable
under the conditioned (probability) law. -/
theorem kac_cond_integrable_and_mean_le (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving (e : Ω → Ω) μ μ) (A : Set Ω) (hA : MeasurableSet A)
    (hApos : μ A ≠ 0) :
    Integrable (fun ω => ((KacFormula.retTime (e : Ω → Ω) A ω).toNat : ℝ))
        ((μ A)⁻¹ • μ.restrict A) ∧
      ∫ ω, ((KacFormula.retTime (e : Ω → Ω) A ω).toNat : ℝ) ∂((μ A)⁻¹ • μ.restrict A)
        ≤ ((μ A)⁻¹).toReal := by
  set D := KacFormula.retTime (e : Ω → Ω) A with hDdef
  have hDm : Measurable D := KacFormula.measurable_retTime e.measurable hA
  have hDcoe : Measurable fun ω => ((D ω : ℕ∞) : ℝ≥0∞) :=
    KacFormula.measurable_enat_coe.comp hDm
  have hbase : ∫⁻ ω in A, ((D ω : ℕ∞) : ℝ≥0∞) ∂μ ≤ 1 :=
    KacFormula.kac_lintegral_le_one e he A hA
  have hae : ∀ᵐ ω ∂(μ.restrict A), ((D ω : ℕ∞) : ℝ≥0∞) < ⊤ :=
    MeasureTheory.ae_lt_top hDcoe (ne_top_of_le_ne_top (by simp) hbase)
  have hconv : ∫⁻ ω in A, ((D ω).toNat : ℝ≥0∞) ∂μ
      = ∫⁻ ω in A, ((D ω : ℕ∞) : ℝ≥0∞) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact retTime_toNat_coe hω
  have hbound : ∫⁻ ω in A, ((D ω).toNat : ℝ≥0∞) ∂μ ≤ 1 := by
    rw [hconv]; exact hbase
  have hbound' : ∫⁻ ω, ((D ω).toNat : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) ≤ (μ A)⁻¹ := by
    rw [lintegral_smul_measure]
    calc (μ A)⁻¹ * ∫⁻ ω, ((D ω).toNat : ℝ≥0∞) ∂(μ.restrict A)
        ≤ (μ A)⁻¹ * 1 := by gcongr
      _ = (μ A)⁻¹ := mul_one _
  have hne : (∫⁻ ω, ((D ω).toNat : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 hApos) hbound'
  have hgn : Measurable fun ω => (D ω).toNat :=
    (show Measurable ENat.toNat from by fun_prop).comp hDm
  refine ⟨integrable_natCast_of_lintegral_ne_top hgn hne, ?_⟩
  rw [integral_natCast_eq_toReal hgn hne]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hApos) hbound'

end SwarmKac
