/-
  **Direction A — the above-record one-step conditional increment.**

  For two distinct walkers `i ≠ j`, the `rho`-weighted right-jump indicator of walker `i` at time
  `n` has `infoPiece p m n j g`-conditional mean `aRec p m · alphaFun p m n i`:

      E[ stepUpInd_i · rhoStep_j(g+1) | infoPiece p m n j g ] =ᵐ aRec p m · alphaFun_i .

  The one-site multiplier at the `(g+1)`-st site above the running record `M_n^j` is

      rhoStep_j(g+1) = 1 + (rho(true) - 1) · 1{M_n^j + g + 1 is marked},

  so the weighted indicator splits *pointwise* into the marginal jump indicator plus a constant
  multiple of `1{stepUp_i ∩ site mark at M_n^j + g + 1}`.  The two conditional means are then

  * `condExp_stepUp_infoPiece` — the marginal fresh-coordinate law, and
  * `condExp_up_siteMark_infoPiece` — the **joint** law of the next right jump of `i` and the fresh
    site mark of `j` at `M_n^j + g + 1` (freshness of *both* coordinates at once),

  and the combination closes with `aRec_eq`.  The weight is *not* factored into a product of
  separate conditional means: the second term is the joint block mass
  `(1-p)^{m-1} · E[stepUpInd_i | infoPiece]`, which is the content of the joint block law.

  Everything is on the actual trajectory (`Swarming.Trajectory.trajectory`) and the actual
  `arrayMeasure N`; no `sorry`, no custom axioms, no `Ballistic` claim.
-/
import Swarm.JumpRec
import Swarm.EnlDrift
import Swarm.PullOut

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### The fresh site above the record and the multiplier decomposition -/

/-- The site-mark event at the `(g+1)`-st site above the running record `M_n^j = recVal j γ`.

  This is the site used in `condExp_up_siteMark_infoPiece`: it is *strictly* above the record
  information `infoPiece p m n j g`, whose read set only reaches the site `M_n^j + g`. -/
def aboveSiteMark (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) : Set (Array N) :=
  {U : Array N | SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))}

lemma aboveSiteMark_def (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    aboveSiteMark p m n j g =
      {U : Array N | SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))} := rfl

lemma measurableSet_aboveSiteMark (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) :
    MeasurableSet (aboveSiteMark p m n j g) :=
  measurableSet_randomSiteMark p m n j g

/-- **The multiplier decomposition.**  The one-site multiplier at the site `M_n^j + g + 1` is the
affine function of the site-mark indicator with slope `rho(true) - 1`:

    rhoStep_j(g+1) = 1 + (rho(true) - 1) · 1{M_n^j + g + 1 is marked}. -/
theorem rhoStep_succ_eq (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    rhoStep p m n j (g + 1) U =
      1 + (SwarmMarks.rhoOf p true - 1)
        * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U := by
  have hunf : rhoStep p m n j (g + 1) U =
      SwarmMarks.rhoOf p
        (markB p m j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ)) U) := rfl
  rw [hunf]
  by_cases h : SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))
  · have hm : U ∈ aboveSiteMark p m n j g := by
      simpa only [aboveSiteMark, Set.mem_ofPred_eq] using h
    rw [rhoOf_markB_pos h, Set.indicator_of_mem hm]
    ring
  · have hm : U ∉ aboveSiteMark p m n j g := by
      simpa only [aboveSiteMark, Set.mem_ofPred_eq] using h
    rw [rhoOf_markB_neg h, Set.indicator_of_notMem hm]
    ring

/-- The product of the jump indicator with the site-mark indicator is the indicator of the
intersection — this is the set whose conditional mass the joint block law computes. -/
theorem stepUpInd_mul_aboveSiteMark (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) (U : Array N) :
    stepUpInd p m n i U * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U =
      (stepUp p m n i ∩ aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U := by
  by_cases hs : U ∈ stepUp p m n i
  · by_cases hm : U ∈ aboveSiteMark p m n j g
    · rw [stepUpInd, Set.indicator_of_mem hs, Set.indicator_of_mem hm,
        Set.indicator_of_mem (Set.mem_inter hs hm)]
      ring
    · rw [stepUpInd, Set.indicator_of_mem hs, Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (fun h => hm (Set.mem_of_mem_inter_right h))]
      ring
  · rw [stepUpInd, Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (fun h => hs (Set.mem_of_mem_inter_left h))]
    ring

/-- **The pointwise split of the weight.** -/
theorem stepUpInd_mul_rhoStep_succ (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U) =
      fun U => stepUpInd p m n i U
        + (SwarmMarks.rhoOf p true - 1)
          * (stepUpInd p m n i U * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U) := by
  funext U
  rw [rhoStep_succ_eq p m n j g U]
  ring

/-! ### Integrability and measurability of the weighted indicator -/

lemma abs_aboveSiteMark_indicator_le (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    |(aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U| ≤ 1 := by
  by_cases h : U ∈ aboveSiteMark p m n j g
  · rw [Set.indicator_of_mem h]
    simp
  · rw [Set.indicator_of_notMem h]
    simp

/-- The jump indicator times the fresh site-mark indicator is integrable. -/
lemma integrable_stepUpInd_mul_aboveSiteMark {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Integrable (fun U => stepUpInd p m n i U
      * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U) (arrayMeasure N) := by
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U => stepUpInd p m n i U
      * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U) :=
    (Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
      (Measurable.indicator measurable_const (measurableSet_aboveSiteMark p m n j g))
  refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |stepUpInd p m n i U| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U
  calc |stepUpInd p m n i U| * |(aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U|
      ≤ 1 * 1 := mul_le_mul h1 (abs_aboveSiteMark_indicator_le p m n j g U) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Integrability of the `rho`-weighted jump indicator.** -/
lemma integrable_stepUpInd_mul_rhoStep {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Integrable (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U) (arrayMeasure N) := by
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U) :=
    (Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
      (measurable_rhoStep p m n j (g + 1))
  refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |stepUpInd p m n i U| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U
  calc |stepUpInd p m n i U| * |rhoStep p m n j (g + 1) U|
      ≤ 1 * 1 := mul_le_mul h1 (abs_rhoStep_le hp0 hp1 m n j (g + 1) U) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Measurability** of the `rho`-weighted jump indicator, in the ambient σ-algebra. -/
lemma measurable_stepUpInd_mul_rhoStep (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Measurable (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U) :=
  (Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
    (measurable_rhoStep p m n j (g + 1))

/-! ### Two elementary conditional-expectation lemmas -/

/-- A real scalar pulls out of a conditional expectation. -/
theorem condExp_fun_const_mul (c : ℝ) (f : Array N → ℝ) (𝓕 : MeasurableSpace (Array N)) :
    condExp 𝓕 (arrayMeasure N) (fun U => c * f U)
      =ᵐ[arrayMeasure N] fun U => c * condExp 𝓕 (arrayMeasure N) f U := by
  have h := condExp_smul (μ := arrayMeasure N) (m := 𝓕) c f
  have hL : (c • f : Array N → ℝ) = fun U => c * f U := by
    funext U
    simp
  have hR : (c • condExp 𝓕 (arrayMeasure N) f : Array N → ℝ)
      = fun U => c * condExp 𝓕 (arrayMeasure N) f U := by
    funext U
    simp
  rwa [hL, hR] at h

/-- Multiplying an almost-everywhere equality of real functions by a constant. -/
theorem eventuallyEq_const_mul {f g : Array N → ℝ} (c : ℝ)
    (h : f =ᵐ[arrayMeasure N] g) :
    (fun U => c * f U) =ᵐ[arrayMeasure N] fun U => c * g U := by
  filter_upwards [h] with U hU
  rw [hU]

/-- The marked-jump conditional mean: the joint law of the next right jump of `i` and the fresh
site mark of `j`, scaled by `(1-p)^{m-1}`.  This is a restatement of the joint block law
`condExp_up_siteMark_infoPiece` in the product form used below. -/
theorem condExp_markedStepUp_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
        (fun U => stepUpInd p m n i U
          * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U)
      =ᵐ[arrayMeasure N] fun U => (1 - p) ^ (m - 1) * alphaFun p m n i U := by
  have hEV : (fun U => (stepUp p m n i ∩ aboveSiteMark p m n j g).indicator
        (fun _ => (1 : ℝ)) U)
      =ᵐ[arrayMeasure N] fun U => stepUpInd p m n i U
        * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U :=
    Filter.Eventually.of_forall fun U => (stepUpInd_mul_aboveSiteMark p m n i j g U).symm
  refine (condExp_congr_ae hEV).symm.trans ?_
  have h := condExp_up_siteMark_infoPiece (N := N) p hp0 hp1 (m := m) (n := n) (i := i) (j := j)
    hij g
  simpa only [aboveSiteMark] using h

/-! ### The conditional-expectation form (the main statement) -/

/-- **The above-record one-step conditional increment.**  For distinct walkers `i ≠ j`,

    E[ stepUpInd_i · rhoStep_j(g+1) | infoPiece p m n j g ] =ᵐ aRec p m · alphaFun_i .

The weight is decomposed pointwise (`stepUpInd_mul_rhoStep_succ`) into the marginal jump
indicator and a constant multiple of the *marked* jump indicator; the first conditional mean is
`condExp_stepUp_infoPiece` and the second is the joint block law `condExp_markedStepUp_infoPiece`
(not a product of the two separate conditional means).  `aRec_eq` combines them. -/
theorem condExp_stepUp_mul_rhoStep_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
        (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U)
      =ᵐ[arrayMeasure N] fun U => aRec p m * alphaFun p m n i U := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp0' : p ≠ 0 := by linarith
  have hint1 : Integrable (stepUpInd p m n i) (arrayMeasure N) := integrable_stepUpInd p m n i
  have hint2 : Integrable (fun U => (SwarmMarks.rhoOf p true - 1)
      * (stepUpInd p m n i U
        * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U)) (arrayMeasure N) :=
    (integrable_stepUpInd_mul_aboveSiteMark hp0 hp1 m n i j g).const_mul _
  have hsplit := stepUpInd_mul_rhoStep_succ p m n i j g
  have h1 : condExp (infoPiece (N := N) p m n j g) (arrayMeasure N) (stepUpInd p m n i)
      =ᵐ[arrayMeasure N] alphaFun p m n i :=
    condExp_stepUp_infoPiece p hp0 hp1 hij g
  have h2 : condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
        (fun U => (SwarmMarks.rhoOf p true - 1)
          * (stepUpInd p m n i U
            * (aboveSiteMark p m n j g).indicator (fun _ => (1 : ℝ)) U))
      =ᵐ[arrayMeasure N] fun U => (SwarmMarks.rhoOf p true - 1)
        * ((1 - p) ^ (m - 1) * alphaFun p m n i U) :=
    (condExp_fun_const_mul (SwarmMarks.rhoOf p true - 1) _ _).trans
      (eventuallyEq_const_mul _ (condExp_markedStepUp_infoPiece p hp0 hp1 hij g))
  refine (condExp_congr_ae (Filter.EventuallyEq.of_eq hsplit)).trans ?_
  refine (condExp_add hint1 hint2 _).trans ?_
  refine (h1.add h2).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  have hgoal : alphaFun p m n i U + (SwarmMarks.rhoOf p true - 1)
      * ((1 - p) ^ (m - 1) * alphaFun p m n i U) = aRec p m * alphaFun p m n i U := by
    rw [aRec_eq hp0']
    ring
  simpa only [Pi.add_apply] using hgoal

/-- **The restricted form used by the `Hpot` drift.**  For an `infoPiece p m n j g`-measurable
event `A`, the conditional mean of `A.indicator (stepUpInd_i · rhoStep_j(g+1))` is
`A.indicator (aRec · alphaFun_i)`.  This is the input the above-record drift needs, with the
restricting event `A` (`{X_n^i = M_n^j + g}` in the drift application) pulled out — its
measurability is the *only* extra hypothesis. -/
theorem condExp_indicator_stepUp_mul_rhoStep_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
        (A.indicator (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U))
      =ᵐ[arrayMeasure N] A.indicator (fun U => aRec p m * alphaFun p m n i U) :=
  (condExp_indicator (integrable_stepUpInd_mul_rhoStep hp0 hp1 m n i j g) hA).trans
    ((condExp_stepUp_mul_rhoStep_infoPiece p hp0 hp1 hij g).indicator)

/-! ### The set-integral (real integral) form -/

/-- **The above-record one-step increment, integral form.**  Over every `infoPiece p m n j g`-
measurable event `A`, the `rho`-weighted right-jump indicator of `i` integrates to `aRec` times
the `alpha`-weight:

    ∫_A stepUpInd_i · rhoStep_j(g+1) = aRec p m · ∫_A alphaFun_i .

This is the set-integral reading of the conditional-expectation identity
`condExp_stepUp_mul_rhoStep_infoPiece` through `setIntegral_condExp`. -/
theorem setIntegral_stepUp_mul_rhoStep_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    ∫ U in A, stepUpInd p m n i U * rhoStep p m n j (g + 1) U ∂(arrayMeasure N) =
      aRec p m * ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
  have hle : infoPiece (N := N) p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j g
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hf : Integrable (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U)
      (arrayMeasure N) :=
    integrable_stepUpInd_mul_rhoStep hp0 hp1 m n i j g
  have hA0 : MeasurableSet A := hle A hA
  have hcond := condExp_stepUp_mul_rhoStep_infoPiece p hp0 hp1 (m := m) (n := n) hij g
  calc ∫ U in A, stepUpInd p m n i U * rhoStep p m n j (g + 1) U ∂(arrayMeasure N)
      = ∫ U in A, condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
          (fun U => stepUpInd p m n i U * rhoStep p m n j (g + 1) U) U
          ∂(arrayMeasure N) := (setIntegral_condExp hle hf hA).symm
    _ = ∫ U in A, aRec p m * alphaFun p m n i U ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA0 ?_
        filter_upwards [hcond] with U hU _
        exact hU
    _ = aRec p m * ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
        rw [integral_const_mul]

/-- **The increment as a ratio of masses.**  The `rho`-weighted jump mass above the record is
`aRec` times the plain jump mass:

    ∫_A stepUpInd_i · rhoStep_j(g+1) = aRec p m · μ.real (A ∩ stepUp_i). -/
theorem setIntegral_stepUp_mul_rhoStep_eq_mass (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    ∫ U in A, stepUpInd p m n i U * rhoStep p m n j (g + 1) U ∂(arrayMeasure N) =
      aRec p m * (arrayMeasure N).real (A ∩ stepUp p m n i) := by
  rw [setIntegral_stepUp_mul_rhoStep_infoPiece p hp0 hp1 hij g hA,
    setIntegral_stepUp_infoPiece p hp0 hp1 hij g hA]

/-! ### The restricting event `{X_n^i = M_n^j + g}` -/

/-- Agreement on a prefix determines the prefix. -/
lemma prefOf_eq_of_mem_prefAgree {p : ℝ} {m : ℕ} {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) : prefOf p m n U = γ := by
  funext t i
  exact congrFun (hU t) i

/-- The restricting event of the drift: walker `i` is at the site `M_n^j + k` at time `n`. -/
def abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) (k : ℕ) : Set (Array N) :=
  {U : Array N | ext (prefOf p m n U) n i = recVal j (prefOf p m n U) + (k : ℤ)}

/-- `{X_n^i = M_n^j + k}` is a *path-determined* event, hence measurable for every record
enlargement `infoPiece p m n j g` (in particular for `g = k - 1`, the level at which the fresh
site `M_n^j + k` is still unread). -/
theorem measurableSet_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) (k g : ℕ) :
    MeasurableSet[infoPiece p m n j g] (abovePosSet p m n i j k) := by
  refine measurableSet_pieceMeas_of_piecewise fun γ => ?_
  by_cases h : ext γ n i = recVal j γ + (k : ℤ)
  · right
    ext U
    constructor
    · intro hU
      exact hU.1
    · intro hU
      refine ⟨hU, ?_⟩
      have hp : prefOf p m n U = γ := prefOf_eq_of_mem_prefAgree hU
      show ext (prefOf p m n U) n i = recVal j (prefOf p m n U) + (k : ℤ)
      rw [hp]
      exact h
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hG⟩
    have hp : prefOf p m n U = γ := prefOf_eq_of_mem_prefAgree hU
    have hG' : ext (prefOf p m n U) n i = recVal j (prefOf p m n U) + (k : ℤ) := hG
    rw [hp] at hG'
    exact h hG'

/-! ### The index form used one step above the record -/

/-- **The same identity at the site `M_n^j + g` for `g ≥ 1`**, with the record information
`infoPiece p m n j (g-1)` that only reaches the site `M_n^j + g - 1`.  This is the indexing the
above-record potential increment `h(M+g) - h(M+g-1)` uses: the multiplier at the fresh site
`M_n^j + g` is conditionally known to `aRec`. -/
theorem condExp_stepUp_mul_rhoStep_infoPiece_pred (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        (fun U => stepUpInd p m n i U * rhoStep p m n j g U)
      =ᵐ[arrayMeasure N] fun U => aRec p m * alphaFun p m n i U := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    condExp_stepUp_mul_rhoStep_infoPiece p hp0 hp1 hij k

/-- **The set-integral identity at the site `M_n^j + g`.** -/
theorem setIntegral_stepUp_mul_rhoStep_infoPiece_pred (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g)
    {A : Set (Array N)} (hA : MeasurableSet[infoPiece p m n j (g - 1)] A) :
    ∫ U in A, stepUpInd p m n i U * rhoStep p m n j g U ∂(arrayMeasure N) =
      aRec p m * ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    setIntegral_stepUp_mul_rhoStep_infoPiece p hp0 hp1 hij k hA

/-- **The `Hpot`-ready restricted increment.**  On the drift event `A = {X_n^i = M_n^j + g}` with
`g ≥ 1`, the conditional mean of the restricted `rho`-weighted right jump is the restricted
`aRec · alpha`-weight, at the record level `infoPiece p m n j (g-1)` which does *not* yet know the
site `M_n^j + g`.  This is the exact input the above-record potential increment
`h(M_n^j+g) - h(M_n^j+g-1) = rhoStep(g)·(1+h(M_n^j+g-1))` needs. -/
theorem condExp_indicator_abovePosSet_stepUp_mul_rhoStep (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator
          (fun U => stepUpInd p m n i U * rhoStep p m n j g U))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
        (fun U => aRec p m * alphaFun p m n i U) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    condExp_indicator_stepUp_mul_rhoStep_infoPiece p hp0 hp1 (m := m) (n := n) hij k
      (measurableSet_abovePosSet p m n i j (k + 1) k)

end Swarming.Enl


