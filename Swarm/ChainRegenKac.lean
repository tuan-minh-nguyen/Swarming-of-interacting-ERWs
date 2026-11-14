/-
A-restricted almost-everywhere Kac bridge for the actual raw regeneration level.

Every stationary conclusion has an explicit `Kernel.Invariant` premise.  The
mass identity is the verified arbitrary-initial-law `chainLaw_hstruct`; no
invariant measure is constructed here.
-/
import Swarm.ChainRegenBridge
import Swarm.PositiveHorizonHstruct
import Swarm.InfSegStationary
import Swarm.FreshCompose

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmChainRegen

open SwarmConcat SwarmFinFuture SwarmFreshCompose
open SimJump

variable {N : ℕ}

/-! ### Kac transfer with an A-restricted a.e. return-time bridge -/

section OnAAE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Type*} [MeasurableSpace P]

/-- The conditioned-law identity when the raw-distance/return-time bridge is
available almost everywhere on `A`, rather than pointwise. -/
theorem condMean_eq_oneSided_onA_ae {f : Ω → Ω} (Φ : Ω → P) (hΦ : Measurable Φ)
    (ν : Measure P) (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ᵐ ω ∂(μ.restrict A),
      KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞)) :
    ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) =
      ∫⁻ p, (g p : ℝ≥0∞) ∂ν := by
  have hgc : Measurable fun p => (g p : ℝ≥0∞) :=
    (show Measurable fun n : ℕ => (n : ℝ≥0∞) from by fun_prop).comp hg
  have hmap := KacFormula.map_restrict_eq_smul_of_factorization
    (μ := μ) Φ hΦ A hA ν hfac
  have hae : ∀ᵐ ω ∂(μ.restrict A),
      (KacFormula.retTime f A ω : ℝ≥0∞) = (g (Φ ω) : ℝ≥0∞) := by
    filter_upwards [hD] with ω hω
    rw [hω]
    simp
  have h1 : ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) =
      (μ A)⁻¹ * ∫⁻ ω in A, (g (Φ ω) : ℝ≥0∞) ∂μ := by
    rw [lintegral_smul_measure, lintegral_congr_ae hae]
    rfl
  rw [h1, KacFormula.lintegral_restrict_comp Φ hΦ A ν (μ A)
    (fun p => (g p : ℝ≥0∞)) hgc hmap]
  have hne : μ A ≠ 0 := ne_of_gt hApos
  have hne_top : μ A ≠ ⊤ := measure_ne_top μ A
  rw [← mul_assoc, ENNReal.inv_mul_cancel hne hne_top, one_mul]

/-- The ENNReal Kac bound with an A-restricted a.e. raw-distance bridge. -/
theorem kac_path_bound_mp_onA_ae {f : Ω → Ω} (hf : Measurable f)
    (hmp : MeasurePreserving f μ μ) (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ᵐ ω ∂(μ.restrict A),
      KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  have hApos : 0 < μ A := by
    rw [hmass]
    exact ENNReal.mul_pos hpf hpv
  rw [← condMean_eq_oneSided_onA_ae (f := f) Φ hΦ ν A hA hApos hfac g hg hD]
  have hbound : ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1 :=
    SwarmKacMP.kac_mp_lintegral_le_one hmp A hA
  have hle := SwarmM2Kac.condMean_le_of_bound (μ := μ) (f := f) A hA hbound
  simpa [hmass] using hle

/-- Integrability and the real numerical bounds with the a.e. bridge. -/
theorem kac_path_ED_mp_onA_ae {f : Ω → Ω} (hf : Measurable f)
    (hmp : MeasurePreserving f μ μ) (Φ : Ω → P) (hΦ : Measurable Φ)
    (ν : Measure P) [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ p, 1 ≤ g p)
    (hD : ∀ᵐ ω ∂(μ.restrict A),
      KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      1 ≤ ∫ p, (g p : ℝ) ∂ν ∧
        ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  have hmain := kac_path_bound_mp_onA_ae hf hmp Φ hΦ ν A hA hfac g hg hD
    pf pv hpf.ne' hpv.ne' hpft hpvt hmass
  have hlt : ∫⁻ p, (g p : ℝ≥0∞) ∂ν < ⊤ :=
    lt_of_le_of_lt hmain (ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne'))
  have hint : Integrable (fun p => (g p : ℝ)) ν :=
    SwarmKac.integrable_natCast_of_lintegral_ne_top hg hlt.ne
  refine ⟨hint, SwarmKac.one_le_integral_of_one_le hint hg1, ?_⟩
  rw [SwarmKac.integral_natCast_eq_toReal hg hlt.ne]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne').ne')
    hmain

end OnAAE

/-! ### Recurrence discharges the fallback only on a null exceptional set -/

/-- On `A`, recurrence makes both the raw regeneration distance and the chain
return time finite almost everywhere, and identifies the latter with our
Nat-valued raw statistic. -/
theorem ae_regen_bridge_onA (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∀ᵐ c ∂(μ.restrict Chain.A),
      RegenPath.D (chainPath c) ≠ ⊤ ∧
        KacFormula.retTime (fun d : Chain N => d.shift) Chain.A c =
          (firstRegenLevel (chainPath c) : ℕ∞) := by
  filter_upwards [SwarmConcat.ae_regeneration_distance_lt_top μ hmp] with c hc
  have hret : KacFormula.retTime (fun d : Chain N => d.shift) Chain.A c ≠ ⊤ := by
    intro htop
    rw [htop] at hc
    simp at hc
  have hchain : ∃ k : ℕ, 0 < k ∧ c.RegenPath k := by
    by_contra hno
    exact hret ((Chain.retTime_eq_top_iff c).mpr hno)
  have hraw : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg (chainPath c) (r : ℤ) :=
    (exists_reg_chainPath_iff c).mp hchain
  constructor
  · rw [raw_D_eq_firstRegenLevel_of_exists _ hraw]
    simp
  · exact retTime_eq_firstRegenLevel_of_ne_top c hret

/-- The no-regeneration fallback is confined to a null event under the law
restricted to `A`; this does not assert regeneration at every path. -/
theorem ae_raw_D_ne_top_onA (μ : Measure (Chain N)) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ) :
    ∀ᵐ c ∂(μ.restrict Chain.A), RegenPath.D (chainPath c) ≠ ⊤ :=
  (ae_regen_bridge_onA μ hmp).mono fun _ h => h.1

/-! ### Actual canonical chain law -/

/-- Conditional normalized fresh expectation bounds for the actual raw first
regeneration level.  The invariant-law and `π(srSet)` premises are explicit;
the strict-fresh mass may be supplied independently of stationarity. -/
theorem chainLaw_firstRegenLevel_mean_bound_of_strictPos {m : ℕ}
    (hm : 1 ≤ m) (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p hm) π)
    (hπ : 0 < π (SwarmRec.srSet N m))
    (hpv : strictLaw p m N univ ≠ 0) :
    Integrable (fun q => (firstRegenLevel q : ℝ))
        ((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
      1 ≤ ∫ q, (firstRegenLevel q : ℝ)
        ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
        ∫ q, (firstRegenLevel q : ℝ)
          ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ≤
          ((π (SwarmRec.srSet N m) * strictLaw p m N univ)⁻¹).toReal := by
  haveI hinf : IsProbabilityMeasure
      (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π) :=
    SwarmInfSeg.isProbabilityMeasure_infLaw p hm hp0.le hp1.le π
  let μ := SwarmChainAssemble.chainLaw
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
  letI hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hmp : MeasurePreserving (fun c : Chain N => c.shift) μ μ := by
    dsimp [μ]
    exact SwarmInfSeg.measurePreserving_chainLaw_shift p hm hp0.le hp1.le π hinv
  have hstruct : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (Chain.A ∩ chainPath ⁻¹' B) =
        π (SwarmRec.srSet N m) * strictLaw p m N B := by
    intro B hB
    rw [SwarmPositiveHorizon.chainLaw_hstruct p hm hp0 hp1 π B hB,
      strictLaw_apply p m N hB]
  have hmass : μ Chain.A = π (SwarmRec.srSet N m) * strictLaw p m N univ := by
    have h := hstruct univ MeasurableSet.univ
    simpa only [Set.preimage_univ, Set.inter_univ] using h
  have hfac : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (Chain.A ∩ chainPath ⁻¹' B) =
        μ Chain.A * (((strictLaw p m N univ)⁻¹ • strictLaw p m N) B) := by
    intro B hB
    rw [hstruct B hB, hmass, Measure.smul_apply, smul_eq_mul,
      mul_self_inv_mul hpv (measure_ne_top _ _)]
  have hD : ∀ᵐ c ∂(μ.restrict Chain.A),
      KacFormula.retTime (fun d : Chain N => d.shift) Chain.A c =
        (firstRegenLevel (chainPath c) : ℕ∞) :=
    (ae_regen_bridge_onA μ hmp).mono fun _ h => h.2
  have hprob : IsProbabilityMeasure ((strictLaw p m N univ)⁻¹ • strictLaw p m N) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hpv (measure_ne_top _ _)]⟩
  letI := hprob
  exact kac_path_ED_mp_onA_ae Chain.measurable_shift hmp chainPath measurable_chainPath
    ((strictLaw p m N univ)⁻¹ • strictLaw p m N) Chain.A Chain.measurableSet_A hfac
    firstRegenLevel measurable_firstRegenLevel one_le_firstRegenLevel hD
    (π (SwarmRec.srSet N m)) (strictLaw p m N univ) hπ (zero_lt_iff.mpr hpv)
    (measure_ne_top _ _) (measure_ne_top _ _) hmass

/-- Model-parameter corollary: strict fresh positivity is proved by
`FreshPast.strictPos_measure_pos`; invariant existence is not proved. -/
theorem chainLaw_firstRegenLevel_mean_bound_model {N m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p (show 1 ≤ m by omega)) π)
    (hπ : 0 < π (SwarmRec.srSet N m)) :
    Integrable (fun q => (firstRegenLevel q : ℝ))
        ((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
      1 ≤ ∫ q, (firstRegenLevel q : ℝ)
        ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
        ∫ q, (firstRegenLevel q : ℝ)
          ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ≤
          ((π (SwarmRec.srSet N m) * strictLaw p m N univ)⁻¹).toReal := by
  apply chainLaw_firstRegenLevel_mean_bound_of_strictPos
    (show 1 ≤ m by omega) p hp0 hp1 π hinv hπ
  rw [strictLaw_univ]
  exact SwarmFreshPast.strictPos_measure_pos hp0 hp1 hm hN

end SwarmChainRegen
