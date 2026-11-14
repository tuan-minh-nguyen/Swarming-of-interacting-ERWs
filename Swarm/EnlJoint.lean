/-
  **The joint one-step transition law on the enlarged filtration.**

  Companion to `EnlRight.lean`.  For a prescribed jump vector `ε : Fin N → ℤ`
  with `ε i = ±1`, the indicator of the pattern event "each walker `i` moves by
  `ε i` at time `n`" has, conditionally on the enlarged filtration
  `enlFilt p m n`, expectation the *product* of the per-walker probabilities

      ∏ i, (if ε i = 1 then alphaFun p m n i else 1 - alphaFun p m n i).

  This is the paper's conditional independence of the `N` jumps at time `n`,
  stated as a genuine `condExp` identity on the actual enlarged filtration.
-/
import Swarm.EnlRight

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open Swarming.Transition SwarmCross

variable {N : ℕ}

/-- The event that at time `n` every walker `i` jumps by `ε i`. -/
noncomputable def patSet (p : ℝ) (m : ℕ) (n : ℕ) (ε : Fin N → ℤ) : Set (Array N) :=
  {U | ∀ i, (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + ε i}

/-- Its real-valued indicator. -/
noncomputable def patInd (p : ℝ) (m : ℕ) (n : ℕ) (ε : Fin N → ℤ) : Array N → ℝ :=
  (patSet p m n ε).indicator (fun _ => (1 : ℝ))

/-- The one-step pattern weight attached to a position prefix. -/
noncomputable def weightOf (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) (ε : Fin N → ℤ) : ℝ :=
  ∏ i, if ε i = 1 then alphaOf p m n γ i else 1 - alphaOf p m n γ i

/-- The same weight as a function of the array. -/
noncomputable def weightFun (p : ℝ) (m : ℕ) (n : ℕ) (ε : Fin N → ℤ) : Array N → ℝ :=
  fun U => ∏ i, if ε i = 1 then alphaFun p m n i U else 1 - alphaFun p m n i U

/-! ### Basic properties -/

lemma factor_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (ε : Fin N → ℤ) (U : Array N) (i : Fin N) :
    0 ≤ (if ε i = 1 then alphaFun p m n i U else 1 - alphaFun p m n i U) := by
  by_cases h : ε i = 1
  · rw [if_pos h]
    exact (alphaFun_mem_Icc hp0 hp1 m n i U).1
  · rw [if_neg h]
    linarith [(alphaFun_mem_Icc hp0 hp1 m n i U).2]

lemma factor_le_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (ε : Fin N → ℤ) (U : Array N) (i : Fin N) :
    (if ε i = 1 then alphaFun p m n i U else 1 - alphaFun p m n i U) ≤ 1 := by
  by_cases h : ε i = 1
  · rw [if_pos h]
    exact (alphaFun_mem_Icc hp0 hp1 m n i U).2
  · rw [if_neg h]
    linarith [(alphaFun_mem_Icc hp0 hp1 m n i U).1]

lemma weightFun_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (ε : Fin N → ℤ) (U : Array N) : 0 ≤ weightFun p m n ε U := by
  unfold weightFun
  exact Finset.prod_nonneg fun i _ => factor_nonneg hp0 hp1 m n ε U i

lemma weightFun_le_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (ε : Fin N → ℤ) (U : Array N) : weightFun p m n ε U ≤ 1 := by
  unfold weightFun
  exact Finset.prod_le_one (fun i _ => factor_nonneg hp0 hp1 m n ε U i)
    (fun i _ => factor_le_one hp0 hp1 m n ε U i)

lemma weightFun_eq_weightOf (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (ε : Fin N → ℤ) :
    weightFun p m n ε U = weightOf p m n γ ε := by
  unfold weightFun weightOf
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : ε i = 1
  · rw [if_pos h, if_pos h, alphaFun_eq_alphaOf_on_prefix p m hU i]
  · rw [if_neg h, if_neg h, alphaFun_eq_alphaOf_on_prefix p m hU i]

lemma weightOf_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} {n : ℕ}
    (γ : Pref N n) (ε : Fin N → ℤ) : 0 ≤ weightOf p m n γ ε := by
  unfold weightOf
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : ε i = 1
  · rw [if_pos h]
    linarith [le_alphaOf p m γ i hp0.le]
  · rw [if_neg h]
    linarith [alphaOf_lt_one p m γ i hp0.le hp1]

lemma weightOf_le_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} {n : ℕ}
    (γ : Pref N n) (ε : Fin N → ℤ) : weightOf p m n γ ε ≤ 1 := by
  unfold weightOf
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · by_cases h : ε i = 1
    · rw [if_pos h]; linarith [le_alphaOf p m γ i hp0.le]
    · rw [if_neg h]; linarith [alphaOf_lt_one p m γ i hp0.le hp1]
  · by_cases h : ε i = 1
    · rw [if_pos h]; exact (alphaOf_lt_one p m γ i hp0.le hp1).le
    · rw [if_neg h]; linarith [le_alphaOf p m γ i hp0.le]

/-- A function constant on every prefix piece is measurable for the enlarged filtration. -/
lemma measurable_enl_of_eq_on_prefix (p : ℝ) (m : ℕ) (n : ℕ) {α : Type*} [MeasurableSpace α]
    {f : Array N → α} {c : Pref N n → α}
    (hf : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ → f U = c γ) :
    Measurable[enlFilt p m n] f := by
  intro S hS
  intro γ
  have hpref : ∀ U : Array N, U ∈ prefAgree p m γ → prefOf p m n U = γ := by
    intro U hU
    have h' : U ∈ {U : Array N | prefOf p m n U = γ} := by
      rwa [← prefAgree_eq_fibre]
    exact h'
  rcases Classical.em (c γ ∈ S) with h | h
  · refine ⟨Set.univ, ?_, ?_⟩
    · exact MeasurableSet.univ
    · rw [Set.inter_univ]
      refine Set.Subset.antisymm Set.inter_subset_left ?_
      rintro U hU
      refine ⟨hU, ?_⟩
      show f U ∈ S
      rw [hf γ U hU]
      exact h
  · refine ⟨∅, ?_, ?_⟩
    · exact (cylAt (prefRead n γ)).measurableSet_empty
    · rw [Set.inter_empty]
      refine Set.eq_empty_iff_forall_notMem.2 fun U hU => h ?_
      have h2 : f U ∈ S := hU.2
      rw [hf γ U hU.1] at h2
      exact h2

lemma measurable_weightFun_enl (p : ℝ) (m : ℕ) (n : ℕ) (ε : Fin N → ℤ) :
    Measurable[enlFilt p m n] (weightFun p m n ε) :=
  measurable_enl_of_eq_on_prefix p m n (fun γ _ hU => weightFun_eq_weightOf p m hU ε)

/-- The pattern event is ambient measurable. -/
lemma measurableSet_patSet (p : ℝ) (m : ℕ) (n : ℕ) (ε : Fin N → ℤ) :
    MeasurableSet (patSet (N := N) p m n ε) := by
  have hset : patSet (N := N) p m n ε =
      ⋂ i : Fin N, {U : Array N | (trajectory p m U (n + 1)).pos i -
        (trajectory p m U n).pos i = ε i} := by
    ext U
    simp only [patSet, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      have := h i
      omega
    · intro h i
      have := h i
      omega
  rw [hset]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (((Swarming.Fair.measurable_trajectory (N := N) p m (n + 1)).1 i).sub
      ((Swarming.Fair.measurable_trajectory (N := N) p m n).1 i)) measurable_const

/-! ### The pattern mass on one prefix piece -/

theorem enl_measure_pattern_piece (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (ε : Fin N → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ patSet p m n ε) =
      ENNReal.ofReal (weightOf p m n γ ε) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  have h := enl_jump_pattern_piece (N := N) p m n γ hB ε hε hp0.le hp1
  have hprod : ENNReal.ofReal (weightOf p m n γ ε) =
      ∏ i, ENNReal.ofReal
        (if ε i = 1 then alphaOf p m n γ i else 1 - alphaOf p m n γ i) := by
    unfold weightOf
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    by_cases h : ε i = 1
    · rw [if_pos h]; linarith [le_alphaOf p m γ i hp0.le]
    · rw [if_neg h]; linarith [alphaOf_lt_one p m γ i hp0.le hp1]
  rw [hprod]
  exact h

/-! ### The integral form over every enlarged-filtration event -/

theorem enl_setIntegral_pattern (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (ε : Fin N → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlFilt p m n] G) :
    (arrayMeasure N).real (G ∩ patSet p m n ε) =
      ∫ U in G, weightFun p m n ε U ∂(arrayMeasure N) := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hGn : MeasurableSet[enlMeas p m n] G := hG
  choose B hB hEq using hGn
  have hbase : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := by
    intro γ
    exact (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cyl (hB γ))
  have hGunion : G = ⋃ γ : Pref N n, prefAgree p m γ ∩ B γ := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have hh : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at hh
      exact hh.2
    · rintro ⟨γ, h1, h2⟩
      have hh : U ∈ prefAgree p m γ ∩ G := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact hh.2
  have hdisj : Pairwise (fun γ γ' : Pref N n =>
      Disjoint (prefAgree p m γ ∩ B γ) (prefAgree p m γ' ∩ B γ')) := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hdisjPat : Pairwise (fun γ γ' : Pref N n =>
      Disjoint ((prefAgree p m γ ∩ B γ) ∩ patSet p m n ε)
        ((prefAgree p m γ' ∩ B γ') ∩ patSet p m n ε)) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hstep_measure : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩ patSet p m n ε) =
        arrayMeasure N (prefAgree p m γ ∩ B γ) * ENNReal.ofReal (weightOf p m n γ ε) := by
    intro γ
    have h := enl_measure_pattern_piece (m := m) p hp0 hp1 γ (hB γ) ε hε
    rw [mul_comm]
    exact h
  have hlhs : arrayMeasure N (G ∩ patSet p m n ε) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) *
        ENNReal.ofReal (weightOf p m n γ ε) := by
    have hunion : G ∩ patSet p m n ε =
        ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩ patSet p m n ε := by
      conv_lhs => rw [hGunion]
      rw [Set.iUnion_inter]
    rw [hunion, measure_iUnion hdisjPat (fun γ =>
      (hbase γ).inter (measurableSet_patSet p m n ε))]
    exact tsum_congr hstep_measure
  have hrhs : ∫⁻ U in G, ENNReal.ofReal (weightFun p m n ε U) ∂(arrayMeasure N) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) *
        ENNReal.ofReal (weightOf p m n γ ε) := by
    rw [hGunion, lintegral_iUnion hbase hdisj]
    refine tsum_congr fun γ => ?_
    rw [setLIntegral_congr_fun (hbase γ) (fun U hU =>
      by rw [weightFun_eq_weightOf p m hU.1 ε])]
    rw [setLIntegral_const, mul_comm]
  have hmain : arrayMeasure N (G ∩ patSet p m n ε) =
      ∫⁻ U in G, ENNReal.ofReal (weightFun p m n ε U) ∂(arrayMeasure N) := by
    rw [hlhs, hrhs]
  have hαmeas : Measurable (weightFun (N := N) p m n ε) :=
    fun s hs => (enlFilt p m).le n _ (measurable_weightFun_enl p m n ε hs)
  have hG0 : MeasurableSet G := (enlFilt p m).le n G hG
  have hnn : ∀ U, 0 ≤ weightFun p m n ε U := fun U => weightFun_nonneg hp0 hp1 m n ε U
  have hle1 : ∀ U, weightFun p m n ε U ≤ 1 := fun U => weightFun_le_one hp0 hp1 m n ε U
  have hInt : Integrable (G.indicator (weightFun p m n ε)) (arrayMeasure N) := by
    refine Integrable.of_bound ((hαmeas.indicator hG0).aestronglyMeasurable) 1 ?_
    filter_upwards with U
    by_cases hU : U ∈ G
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_of_nonneg (hnn U)]
      exact hle1 U
    · rw [Set.indicator_of_notMem hU]
      simp
  have hofreal : ENNReal.ofReal (∫ U in G, weightFun p m n ε U ∂(arrayMeasure N)) =
      ∫⁻ U in G, ENNReal.ofReal (weightFun p m n ε U) ∂(arrayMeasure N) := by
    rw [← integral_indicator hG0]
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun U => by
      by_cases hU : U ∈ G
      · rw [Set.indicator_of_mem hU]; exact hnn U
      · rw [Set.indicator_of_notMem hU]; exact le_rfl)]
    rw [← lintegral_indicator hG0 (fun U => ENNReal.ofReal (weightFun p m n ε U))]
    refine lintegral_congr fun U => ?_
    by_cases hU : U ∈ G
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
      simp
  have hreal : ENNReal.ofReal ((arrayMeasure N).real (G ∩ patSet p m n ε)) =
      ENNReal.ofReal (∫ U in G, weightFun p m n ε U ∂(arrayMeasure N)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _), hofreal]
    exact hmain
  have hnonneg : 0 ≤ ∫ U in G, weightFun p m n ε U ∂(arrayMeasure N) := integral_nonneg hnn
  calc (arrayMeasure N).real (G ∩ patSet p m n ε)
      = (ENNReal.ofReal ((arrayMeasure N).real (G ∩ patSet p m n ε))).toReal :=
        (ENNReal.toReal_ofReal measureReal_nonneg).symm
    _ = (ENNReal.ofReal (∫ U in G, weightFun p m n ε U ∂(arrayMeasure N))).toReal := by
        rw [hreal]
    _ = ∫ U in G, weightFun p m n ε U ∂(arrayMeasure N) := ENNReal.toReal_ofReal hnonneg

/-- **The joint conditional one-step law on the enlarged filtration.**  Conditional on the
whole enlarged filtration at time `n`, the jump vector has the product law with walker-`i`
right mass `alphaFun p m n i`. -/
theorem condExp_pattern_enl (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (ε : Fin N → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (arrayMeasure N)[patInd p m n ε | enlFilt p m n] =ᵐ[arrayMeasure N] weightFun p m n ε := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hsig : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hwmeas : Measurable[enlFilt p m n] (weightFun p m n ε) :=
    measurable_weightFun_enl p m n ε
  have hw_ae : AEStronglyMeasurable[enlFilt p m n] (weightFun p m n ε) (arrayMeasure N) :=
    hwmeas.aestronglyMeasurable
  have hstep : MeasurableSet (patSet p m n ε) := measurableSet_patSet p m n ε
  have hind_int : Integrable (patInd p m n ε) (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator hstep).aestronglyMeasurable) ?_
    filter_upwards with U
    by_cases hU : U ∈ patSet p m n ε
    · rw [patInd, Set.indicator_of_mem hU, Real.norm_eq_abs, abs_one]
    · rw [patInd, Set.indicator_of_notMem hU]
      simp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hind_int ?_ ?_ hw_ae).symm
  · intro s hs hfin
    have hw_amb : Measurable (weightFun (N := N) p m n ε) :=
      fun t ht => hle _ (measurable_weightFun_enl p m n ε ht)
    exact ((integrable_const (1 : ℝ)).mono' hw_amb.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (weightFun_nonneg hp0 hp1 m n ε U)]
        exact weightFun_le_one hp0 hp1 m n ε U)).integrableOn
  · intro s hs hfin
    have hs' : MeasurableSet s := hle s hs
    have h1 : ∫ U in s, patInd (N := N) p m n ε U ∂(arrayMeasure N) =
        (arrayMeasure N).real (s ∩ patSet p m n ε) := by
      rw [← integral_indicator (μ := arrayMeasure N) hs' (f := patInd (N := N) p m n ε)]
      have hcongr : ∫ U, s.indicator (patInd (N := N) p m n ε) U ∂(arrayMeasure N) =
          ∫ U, (s ∩ patSet p m n ε).indicator (fun _ => (1 : ℝ)) U ∂(arrayMeasure N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        by_cases hU : U ∈ s
        · rw [Set.indicator_of_mem hU]
          by_cases h2 : U ∈ patSet p m n ε
          · rw [patInd, Set.indicator_of_mem h2, Set.indicator_of_mem (Set.mem_inter hU h2)]
          · rw [patInd, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (fun h => h2 h.2)]
        · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem (fun h => hU h.1)]
      rw [hcongr]
      exact integral_indicator_one (μ := arrayMeasure N) (hs'.inter hstep)
    rw [h1]
    exact (enl_setIntegral_pattern p hp0 hp1 ε hε hs).symm

end Swarming.Enl


