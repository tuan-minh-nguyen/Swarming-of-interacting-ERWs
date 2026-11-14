/-
  **From piecewise fresh-coordinate masses to integrals and conditional expectations.**
-/
import Swarm.JumpFresh

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-- A weighted mass identity with arbitrary prefix-determined witness events and a prefix-determined
real weight. -/
theorem setIntegral_weight_gen (p : ℝ) (m : ℕ) {n : ℕ}
    (S : Pref N n → Finset (Fin N × ℤ × ℕ)) (hS : ∀ γ, prefRead n γ ⊆ S γ)
    (E : Set (Array N)) (V : Pref N n → Set (Array N)) (w : Pref N n → ℝ)
    (W : Array N → ℝ) (A : Set (Array N))
    (hA : MeasurableSet[pieceMeas (N := N) p m n S] A)
    (hEval : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ → (U ∈ E ↔ (V γ) U))
    (hV : ∀ γ, MeasurableSet (V γ))
    (hWconst : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ → W U = w γ)
    (hWmeas : Measurable[pieceMeas (N := N) p m n S] W)
    (hWnonneg : ∀ U, 0 ≤ W U) (hWle : ∀ U, W U ≤ 1)
    (hmass : ∀ γ {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (S γ)] B),
      arrayMeasure N (prefAgree p m γ ∩ B ∩ V γ) =
        (ENNReal.ofReal (w γ)) * arrayMeasure N (prefAgree p m γ ∩ B)) :
    (arrayMeasure N).real (A ∩ E) = ∫ U in A, W U ∂(arrayMeasure N) := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hAkeep := hA
  choose B hB hEq using hA
  have hbase : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := fun γ =>
    (measurableSet_prefAgree_ambient p m γ).inter (cylAt_le_ambient (S γ) (B γ) (hB γ))
  have hGunion : A = ⋃ γ : Pref N n, prefAgree p m γ ∩ B γ := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have hh : U ∈ prefAgree p m (prefOf p m n U) ∩ A := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at hh
      exact hh.2
    · rintro ⟨γ, h1, h2⟩
      have hh : U ∈ prefAgree p m γ ∩ A := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact hh.2
  have hdisj : Pairwise (fun γ γ' : Pref N n =>
      Disjoint (prefAgree p m γ ∩ B γ) (prefAgree p m γ' ∩ B γ')) := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hpiece : ∀ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩ E =
      (prefAgree p m γ ∩ B γ) ∩ V γ := by
    intro γ
    ext U
    simp only [Set.mem_inter_iff]
    exact and_congr_right (fun hU => hEval γ U hU.1)
  have hdisjE : Pairwise (fun γ γ' : Pref N n =>
      Disjoint ((prefAgree p m γ ∩ B γ) ∩ E) ((prefAgree p m γ' ∩ B γ') ∩ E)) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmark : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩ E) =
        arrayMeasure N (prefAgree p m γ ∩ B γ) * (ENNReal.ofReal (w γ)) := by
    intro γ
    rw [hpiece γ]
    rw [hmass γ (hB γ), mul_comm]
  have hlhs : arrayMeasure N (A ∩ E) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) * (ENNReal.ofReal (w γ)) := by
    have hunion : A ∩ E = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩ E := by
      conv_lhs => rw [hGunion]
      rw [Set.iUnion_inter]
    rw [hunion, measure_iUnion hdisjE (fun γ =>
      (hpiece γ) ▸ ((hbase γ).inter (hV γ)))]
    exact tsum_congr (fun γ => hmark γ)
  have hrhs : ∫⁻ U in A, ENNReal.ofReal (W U) ∂(arrayMeasure N) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) * ENNReal.ofReal (w γ) := by
    rw [hGunion, lintegral_iUnion hbase hdisj]
    refine tsum_congr fun γ => ?_
    rw [setLIntegral_congr_fun (hbase γ) (fun U hU => by rw [hWconst γ U hU.1])]
    rw [setLIntegral_const, mul_comm]
  have hmain : arrayMeasure N (A ∩ E) =
      ∫⁻ U in A, ENNReal.ofReal (W U) ∂(arrayMeasure N) := by
    rw [hlhs, hrhs]
  have hWamb : Measurable W := fun s hs => pieceMeas_le p m n S _ (hWmeas hs)
  have hA0 : MeasurableSet A := (pieceMeas_le p m n S) _ (hAkeep)
  have hInt : Integrable (A.indicator W) (arrayMeasure N) := by
    refine Integrable.of_bound ((hWamb.indicator hA0).aestronglyMeasurable) 1 ?_
    filter_upwards with U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_of_nonneg (hWnonneg U)]
      exact hWle U
    · rw [Set.indicator_of_notMem hU]
      simp
  have hofreal : ENNReal.ofReal (∫ U in A, W U ∂(arrayMeasure N)) =
      ∫⁻ U in A, ENNReal.ofReal (W U) ∂(arrayMeasure N) := by
    rw [← integral_indicator hA0]
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun U => by
      by_cases hU : U ∈ A
      · rw [Set.indicator_of_mem hU]; exact hWnonneg U
      · rw [Set.indicator_of_notMem hU]; exact le_rfl)]
    rw [← lintegral_indicator hA0 (fun U => ENNReal.ofReal (W U))]
    refine lintegral_congr fun U => ?_
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
      simp
  have hreal : ENNReal.ofReal ((arrayMeasure N).real (A ∩ E)) =
      ENNReal.ofReal (∫ U in A, W U ∂(arrayMeasure N)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _), hofreal]
    exact hmain
  have hnonneg : 0 ≤ ∫ U in A, W U ∂(arrayMeasure N) := integral_nonneg hWnonneg
  calc
    (arrayMeasure N).real (A ∩ E)
        = (ENNReal.ofReal ((arrayMeasure N).real (A ∩ E))).toReal :=
      (ENNReal.toReal_ofReal measureReal_nonneg).symm
    _ = (ENNReal.ofReal (∫ U in A, W U ∂(arrayMeasure N))).toReal := by rw [hreal]
    _ = ∫ U in A, W U ∂(arrayMeasure N) := ENNReal.toReal_ofReal hnonneg

/-- One coordinate-free conditional-expectation packaging lemma. -/
theorem condExp_indicator_weight_gen (p : ℝ) (m : ℕ) {n : ℕ}
    (S : Pref N n → Finset (Fin N × ℤ × ℕ)) (hS : ∀ γ, prefRead n γ ⊆ S γ)
    (E : Set (Array N)) (hE : MeasurableSet E) (W : Array N → ℝ)
    (hWmeas : Measurable[pieceMeas (N := N) p m n S] W)
    (hWnonnegAll : ∀ U, 0 ≤ W U) (hWle : ∀ U, W U ≤ 1)
    (hEq : ∀ {A : Set (Array N)}, MeasurableSet[pieceMeas (N := N) p m n S] A →
      (arrayMeasure N).real (A ∩ E) = ∫ U in A, W U ∂(arrayMeasure N)) :
    condExp (pieceMeas (N := N) p m n S) (arrayMeasure N)
        (E.indicator (fun _ => (1 : ℝ))) =ᵐ[arrayMeasure N] W := by
  classical
  let μ := arrayMeasure N
  haveI : IsProbabilityMeasure μ := arrayMeasure_isProbabilityMeasure N
  have hle : pieceMeas (p := p) (m := m) (n := n) S ≤
      (inferInstance : MeasurableSpace (Array N)) := pieceMeas_le p m n S
  have hsig : SigmaFinite (μ.trim hle) := inferInstance
  have hWamb : Measurable W := fun s hs => hle _ (hWmeas hs)
  have hInt : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_const.indicator hE).aestronglyMeasurable) ?_
    filter_upwards with U
    by_cases hU : U ∈ E <;> simp [hU]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hInt ?_ ?_ hWmeas.aestronglyMeasurable).symm
  · intro s _ _
    exact ((integrable_const (1 : ℝ)).mono' hWamb.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonnegAll U)]
        exact hWle U)).integrableOn
  · intro s hs hfin
    have hs0 : MeasurableSet s := hle s hs
    have h1 : ∫ U in s, E.indicator (fun _ => (1 : ℝ)) U ∂μ = μ.real (s ∩ E) := by
      rw [← integral_indicator (μ := μ) hs0]
      have hcongr : ∫ U, s.indicator (E.indicator (fun _ => (1 : ℝ))) U ∂μ =
          ∫ U, (s ∩ E).indicator (fun _ => (1 : ℝ)) U ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        by_cases hU : U ∈ s
        · by_cases hE' : U ∈ E
          · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hE',
              Set.indicator_of_mem (Set.mem_inter hU hE')]
          · rw [Set.indicator_of_mem hU, Set.indicator_of_notMem hE',
              Set.indicator_of_notMem (fun h => hE' h.2)]
        · rw [Set.indicator_of_notMem hU,
            Set.indicator_of_notMem (fun h => hU h.1)]
      rw [hcongr]
      exact integral_indicator_one (μ := μ) (hs0.inter hE)
    rw [h1]
    exact (hEq hs).symm

end Swarming.Enl


