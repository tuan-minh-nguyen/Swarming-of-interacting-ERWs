/-
# Composing the fresh-start identity with Kac's lemma: the paper's `(ED)`

Companion of `FreshState.lean`.  Two things are supplied here.

* **The source's return-time hypothesis, weakened to `A`.**  The paper defines
  `D = inf{r ≥ 1 : τ_r is a regeneration time}` on the concatenated path and identifies it with
  the return time to `A` only *on* `A` ("For `k ≥ 1`, on `A`, we have `θ^k ω ∈ A` if and only if
  `τ_k` is a regeneration time of the concatenated path").  The existing interfaces
  (`M2KacExt.condMean_eq_oneSided`, `SwarmKacMP.kac_path_ED_mp`) require the identity on *all* of
  `Ω`.  `condMean_eq_oneSided_onA`, `kac_path_bound_mp_onA`, `kac_path_ED_mp_onA` are those
  theorems with the hypothesis restricted to `A`, which is what the source proves; the proof of
  the conditioning identity only ever evaluates the return time on `A`.

* **`(ED)` with the mass identity and the factorisation *derived*, not assumed.**
  `record_ED_of_fresh` takes the stationary one-sided system together with the structural
  display

    `μ (A ∩ Φ ⁻¹' B) = ∫⁻ y in F, P_y(V ∩ B) ∂π`

  (`P_y` the law of the actual trajectory started from the record state `y`) and returns the
  paper's `1 ≤ E^*D ≤ 1/(π(F) P(V))`.  The two hypotheses `hmass`/`hfac` of
  `kac_path_ED_mp` are produced here: the integral is computed by
  `SwarmFreshState.fresh_mass_integral_srSet` from the per-state fresh identity of
  `FreshState.lean`, and `P(V) > 0` / `P(V) ≠ ⊤` from `FreshPast`/`ModelNumbers`.

  The structural display is exactly what a stationary record-and-future system built from the
  invariant record law satisfies by construction; it is *not* proved here, and no claim about
  `MainClaim` or the common speed is made.
-/
import Swarm.FreshState
import Swarm.KacED
import Swarm.FreshPast

open MeasureTheory Set
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec SwarmFresh
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace SwarmFreshCompose

variable {N : ℕ}

/-! ### Kac with the return-time identity only on `A` -/

section OnA

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Type*} [MeasurableSpace P]

/-- **The conditioning identity `E_{P(·|A)}[D] = E^*[g]` with `D = g ∘ Φ` only on `A`.**
`M2KacExt.condMean_eq_oneSided` with the pointwise hypothesis relaxed to `A`, which is where
the source identifies the regeneration distance with the return time to `A`. -/
theorem condMean_eq_oneSided_onA {f : Ω → Ω} (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω ∈ A, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞)) :
    ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = ∫⁻ p, (g p : ℝ≥0∞) ∂ν := by
  have hgc : Measurable fun p => (g p : ℝ≥0∞) :=
    (show Measurable fun n : ℕ => (n : ℝ≥0∞) from by fun_prop).comp hg
  have hmap := KacFormula.map_restrict_eq_smul_of_factorization (μ := μ) Φ hΦ A hA ν hfac
  have hae : ∀ᵐ ω ∂(μ.restrict A),
      (KacFormula.retTime f A ω : ℝ≥0∞) = (g (Φ ω) : ℝ≥0∞) := by
    rw [ae_restrict_iff' hA]
    filter_upwards with ω hω
    rw [hD ω hω]
    simp
  have h1 : ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = (μ A)⁻¹ * ∫⁻ ω in A, (g (Φ ω) : ℝ≥0∞) ∂μ := by
    rw [lintegral_smul_measure, lintegral_congr_ae hae]
    rfl
  rw [h1, KacFormula.lintegral_restrict_comp Φ hΦ A ν (μ A) (fun p => (g p : ℝ≥0∞)) hgc hmap]
  have hne : μ A ≠ 0 := ne_of_gt hApos
  have hne_top : μ A ≠ ⊤ := measure_ne_top μ A
  rw [← mul_assoc, ENNReal.inv_mul_cancel hne hne_top, one_mul]

/-- **The paper's `E^*D ≤ 1/(π(F)P(V))` with `D = g ∘ Φ` only on `A`.** -/
theorem kac_path_bound_mp_onA {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω ∈ A, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  have hApos : 0 < μ A := by
    rw [hmass]
    exact ENNReal.mul_pos hpf hpv
  rw [← condMean_eq_oneSided_onA (f := f) Φ hΦ ν A hA hApos hfac g hg hD]
  have hbound : ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1 :=
    SwarmKacMP.kac_mp_lintegral_le_one hmp A hA
  have hle := SwarmM2Kac.condMean_le_of_bound (μ := μ) (f := f) A hA hbound
  simpa [hmass] using hle

/-- **The paper's `(ED)`, `1 ≤ E^*D < ∞`, with the return-time identity only on `A`.** -/
theorem kac_path_ED_mp_onA {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) [IsProbabilityMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ p, 1 ≤ g p)
    (hD : ∀ ω ∈ A, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      1 ≤ ∫ p, (g p : ℝ) ∂ν ∧
        ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  have hmain := kac_path_bound_mp_onA hf hmp Φ hΦ ν A hA hfac g hg hD
    pf pv hpf.ne' hpv.ne' hpft hpvt hmass
  have hlt : ∫⁻ p, (g p : ℝ≥0∞) ∂ν < ⊤ :=
    lt_of_le_of_lt hmain (ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne'))
  have hint : Integrable (fun p => (g p : ℝ)) ν :=
    SwarmKac.integrable_natCast_of_lintegral_ne_top hg hlt.ne
  refine ⟨hint, SwarmKac.one_le_integral_of_one_le hint hg1, ?_⟩
  rw [SwarmKac.integral_natCast_eq_toReal hg hlt.ne]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne').ne')
    hmain

end OnA

end SwarmFreshCompose

namespace SwarmFreshCompose

open SwarmFreshState

variable {N : ℕ}

/-! ### The fresh law `P^*` of the source, and `(ED)` with `hmass`/`hfac` derived -/

/-- The source's fresh law restricted to `V`: `P^*(B) = P(V ∩ B)` as a measure on the path
space (its total mass is `P(V)`, not `1`; it is normalised below). -/
noncomputable def strictLaw (p : ℝ) (m N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  ((arrayMeasure N).map (posPath p m)).restrict (strictPos (N := N))

theorem strictLaw_apply (p : ℝ) (m N : ℕ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    strictLaw p m N B
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  rw [strictLaw, Measure.restrict_apply hB,
    Measure.map_apply (SwarmRestart.measurable_posPath p m N)
      (hB.inter SwarmFresh.measurableSet_strictPos)]
  congr 1
  ext U
  simp [and_comm]

theorem strictLaw_univ (p : ℝ) (m N : ℕ) :
    strictLaw p m N univ
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  rw [strictLaw_apply p m N MeasurableSet.univ]
  simp

instance instIsFiniteMeasureStrictLaw (p : ℝ) (m N : ℕ) : IsFiniteMeasure (strictLaw p m N) :=
  ⟨by rw [strictLaw_univ]; exact measure_lt_top (arrayMeasure N) _⟩

/-- A trivial `ℝ≥0∞` identity used to pass from the raw fresh mass to the normalised law. -/
theorem mul_self_inv_mul {A p X : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤) :
    (A * p) * (p⁻¹ * X) = A * X := by
  calc (A * p) * (p⁻¹ * X) = A * (p * (p⁻¹ * X)) := mul_assoc A p (p⁻¹ * X)
    _ = A * ((p * p⁻¹) * X) := by rw [← mul_assoc p p⁻¹ X]
    _ = A * (1 * X) := by rw [ENNReal.mul_inv_cancel hp hpt]
    _ = A * X := by rw [one_mul]

/-- **The paper's `(ED)` with the mass identity and the factorisation derived from the
per-state fresh identity.**

The stationary one-sided system `(Ω, μ, f, A, Φ)` supplies the structural display
`hstruct`: the `μ`-mass of "the state is in `F` and the future lies in `B`" is the `π`-average
over `F` of the per-state fresh masses (this is what a stationary record-and-future system built
from the invariant record law `π` satisfies by construction).  `FreshState.lean` computes that
average as `π(F) · P(V ∩ B)`, which yields

* `μ A = π(F) · P(V)`     (the paper's `P_π(A) = π(F)P(V)`),
* `μ (A ∩ Φ ⁻¹' B) = μ A · P^*(B)`  (the paper's `(factor)`),

with `P^* = P(V)⁻¹ · P(V ∩ ·)`.  Kac's lemma for the one-sided measure-preserving `f`
(`KacMP.lean`, no invertible extension) then gives `1 ≤ E^*D ≤ 1/(π(F)P(V))`.

Remaining inputs, exactly: the structural display `hstruct`, the source's identification
`D = g ∘ Φ` **on `A`** (`hD`), the invariant record law with `π(F) > 0`, and `P(V) ≠ 0`
(`FreshPast.strictPos_measure_pos` for the model's parameter range). -/
theorem record_ED_of_fresh {N m : ℕ} (hm : 1 ≤ m) (p : ℝ)
    (hpv : strictLaw p m N univ ≠ 0)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : MeasurableSet A)
    (g : (ℕ → Fin N → ℤ) → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω ∈ A, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (hstruct : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B) = ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B} ∂π) :
    Integrable (fun q => (g q : ℝ)) ((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
      1 ≤ ∫ q, (g q : ℝ) ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
        ∫ q, (g q : ℝ) ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N)
          ≤ ((π (srSet N m) * strictLaw p m N univ)⁻¹).toReal := by
  have hpt : strictLaw p m N univ ≠ ⊤ := measure_ne_top _ _
  have hfac : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B)
        = μ A * (((strictLaw p m N univ)⁻¹ • strictLaw p m N) B) := by
    intro B hB
    have h1 : μ (A ∩ Φ ⁻¹' B) = π (srSet N m) * strictLaw p m N B := by
      rw [hstruct B hB, fresh_mass_integral_srSet (N := N) hm p π (B := B),
        strictLaw_apply p m N hB]
    have h2 : μ A = π (srSet N m) * strictLaw p m N univ := by
      have h := hstruct univ MeasurableSet.univ
      simp only [Set.preimage_univ, Set.inter_univ] at h
      rw [h, fresh_mass_integral_srSet (N := N) hm p π (B := univ), Set.inter_univ,
        strictLaw_univ]
    rw [h1, h2, Measure.smul_apply, smul_eq_mul, mul_self_inv_mul hpv hpt]
  have hpv' : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0 := by
    rw [← strictLaw_univ]
    exact hpv
  have hprob : IsProbabilityMeasure ((strictLaw p m N univ)⁻¹ • strictLaw p m N) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul, strictLaw_univ,
        ENNReal.inv_mul_cancel hpv' (measure_ne_top _ _)]⟩
  haveI := hprob
  exact kac_path_ED_mp_onA hf hmp Φ hΦ ((strictLaw p m N univ)⁻¹ • strictLaw p m N)
    A hA hfac g hg hg1 hD (π (srSet N m)) (strictLaw p m N univ)
    hπ (zero_lt_iff.mpr hpv) (measure_ne_top _ _) hpt
    (by
      have h := hstruct univ MeasurableSet.univ
      simp only [Set.preimage_univ, Set.inter_univ] at h
      rw [h, fresh_mass_integral_srSet (N := N) hm p π (B := univ), Set.inter_univ,
        strictLaw_univ])

end SwarmFreshCompose

namespace SwarmFreshCompose

open SwarmFreshState

/-- **The paper's `(ED)` for the model's parameter range**, with `P(V) > 0` discharged from
`FreshPast.strictPos_measure_pos` instead of assumed. -/
theorem record_ED_of_fresh_model {N m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {p : ℝ}
    (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → Ω} (hf : Measurable f) (hmp : MeasurePreserving f μ μ)
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : MeasurableSet A)
    (g : (ℕ → Fin N → ℤ) → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω ∈ A, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (hstruct : ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B) = ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B} ∂π) :
    Integrable (fun q => (g q : ℝ)) ((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
      1 ≤ ∫ q, (g q : ℝ) ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N) ∧
        ∫ q, (g q : ℝ) ∂((strictLaw p m N univ)⁻¹ • strictLaw p m N)
          ≤ ((π (srSet N m) * strictLaw p m N univ)⁻¹).toReal := by
  have hpv : strictLaw p m N univ ≠ 0 := by
    rw [strictLaw_univ]
    exact SwarmFreshPast.strictPos_measure_pos hp0 hp1 hm hN
  exact record_ED_of_fresh (le_trans (by norm_num : 1 ≤ 2) hm) p hpv π hπ hf hmp Φ hΦ A hA
    g hg hg1 hD hstruct

end SwarmFreshCompose
