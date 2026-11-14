/-
  **The conditional one-step right-jump law on the enlarged filtration.**

  `condExp_stepUp_enl` proves, on the actual product probability space of the
  interacting excited random walks, that

      (arrayMeasure N)[1{walker i steps right at time n} | enlFilt p m n]
        =ᵐ alphaFun p m n i,

  i.e. the conditional right-jump probability given the *genuine* enlarged
  filtration `Swarm/EnlFilt.lean` is the current right probability
  `alphaFun = currentAlpha`.  This is a `condExp` statement over every
  enlarged-filtration event, not a fixed-history measure identity.

  Proof route (no new hypotheses):
  * on a single prefix piece `{path = γ}` the freshly read coordinate decides the
    right jump, so the right-jump mass is `alphaOf p m n γ i` times the piece mass
    (`enl_measure_right_piece`, from `enl_fresh_law_piece`);
  * every enlarged-filtration event is a *countable* disjoint union of such pieces
    (`enlMeas`), so the identity upgrades to a `lintegral` identity over the event
    (`enl_setIntegral_stepUp`);
  * `alphaFun` is `enlFilt`-measurable because it factors through the prefix map
    (`measurable_alphaFun_enl`), and it is bounded in `[0,1]`;
  * `ae_eq_condExp_of_forall_setIntegral_eq` finishes.
-/
import Swarm.EnlJump
import Swarm.CondExp

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open Swarming.Transition SwarmCross

variable {N : ℕ}

/-- `prefAgree` really is the fibre of the prefix map. -/
lemma prefAgree_eq_fibre (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) :
    prefAgree p m γ = {U : Array N | prefOf p m n U = γ} := by
  ext U
  rw [Set.mem_ofPred_eq, mem_prefAgree]
  constructor
  · intro h
    funext t
    exact h t
  · intro h t
    exact congrFun h t

/-- The actual one-dimensional right probability agrees with its prefix version. -/
lemma alphaFun_eq_alphaOf_on_prefix (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (i : Fin N) :
    alphaFun p m n i U = alphaOf p m n γ i := by
  unfold SwarmCross.alphaFun Swarming.Transition.currentAlpha
  exact rightProbability_eq_alphaOf p m hU i

/-- The prefix-indexed version of the actual right probability is measurable. -/
lemma measurable_alphaFun_enl (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Measurable[enlFilt p m n] (alphaFun p m n i) := by
  have hfun : alphaFun p m n i = fun U : Array N => alphaOf p m n (prefOf p m n U) i := by
    funext U
    exact alphaFun_eq_alphaOf_on_prefix p m (prefAgree_prefOf U) i
  rw [hfun]
  intro s hs
  intro γ
  have hpref : ∀ U : Array N, U ∈ prefAgree p m γ → prefOf p m n U = γ := by
    intro U hU
    have h' : U ∈ {U : Array N | prefOf p m n U = γ} := by
      rwa [← prefAgree_eq_fibre]
    exact h'
  rcases Classical.em (alphaOf p m n γ i ∈ s) with h | h
  · have hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] (Set.univ : Set (Array N)) :=
      MeasurableSet.univ
    refine ⟨Set.univ, hB, ?_⟩
    rw [Set.inter_univ]
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    refine ⟨hU, ?_⟩
    show alphaOf p m n (prefOf p m n U) i ∈ s
    rw [hpref U hU]
    exact h
  · refine ⟨∅, ?_, ?_⟩
    · exact (cylAt (prefRead n γ)).measurableSet_empty
    rw [Set.inter_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun U hU => h ?_
    rw [← hpref U hU.1]
    exact hU.2

/-- On a prefix piece, the right jump is decided by the single coordinate `fr n γ i`. -/
lemma rightJump_iff_on_prefix (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (i : Fin N) :
    U ∈ StepCross.stepUp p m n i ↔ U (fr n γ i) ≤ alphaOf p m n γ i := by
  rw [StepCross.mem_stepUp, jumpStep_of_prefAgree p m hU i, add_right_inj]
  exact drivenStep_eq_one_iff _ _

/-- Exact right-jump mass on an enlarged-filtration prefix piece. -/
theorem enl_measure_right_piece (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (i : Fin N) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ StepCross.stepUp p m n i) =
      ENNReal.ofReal (alphaOf p m n γ i) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  let I : Fin N → Set ℝ := fun j => if j = i then Set.Iic (alphaOf p m n γ i) else Set.univ
  have hImeas : ∀ j, MeasurableSet (I j) := by
    intro j
    by_cases h : j = i <;>
      simp only [I, h, if_true, if_false, measurableSet_Iic, MeasurableSet.univ]
  have hset : prefAgree p m γ ∩ B ∩ StepCross.stepUp p m n i =
      prefAgree p m γ ∩ B ∩ ⋂ j, {U : Array N | U (fr n γ j) ∈ I j} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, hb⟩, hu⟩
      refine ⟨⟨hp, hb⟩, fun j => ?_⟩
      by_cases hj : j = i
      · have h1 : U (fr n γ j) ≤ alphaOf p m n γ i := by
          rw [hj]
          exact (rightJump_iff_on_prefix p m hp i).mp hu
        simp only [I, if_pos hj]
        exact h1
      · simp only [I, if_neg hj, Set.mem_univ]
    · rintro ⟨⟨hp, hb⟩, hu⟩
      refine ⟨⟨hp, hb⟩, ?_⟩
      have hi : U (fr n γ i) ∈ I i := hu i
      simp only [I, if_pos rfl, Set.mem_Iic] at hi
      exact (rightJump_iff_on_prefix p m hp i).mpr hi
  rw [hset, enl_fresh_law_piece p m n γ hB I hImeas]
  congr 1
  calc
    (∏ j, uniform01 (I j)) = uniform01 (I i) := by
      apply Finset.prod_eq_single i
      · intro j _ hj
        simp [I, hj, uniform01]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    _ = uniform01 (Set.Iic (alphaOf p m n γ i)) := by simp [I]
    _ = ENNReal.ofReal (alphaOf p m n γ i) := by
      apply uniform01_Iic
      · linarith [le_alphaOf p m γ i hp0.le]
      · exact alphaOf_lt_one p m γ i hp0.le hp1

end Swarming.Enl


namespace Swarming.Enl

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open Swarming.Transition SwarmCross

variable {N : ℕ}

/-- **The fresh-coordinate law in real-integral form over every enlarged-filtration event.** -/
theorem enl_setIntegral_stepUp (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} {G : Set (Array N)} (hG : MeasurableSet[enlFilt p m n] G) (i : Fin N) :
    (arrayMeasure N).real (G ∩ StepCross.stepUp p m n i) =
      ∫ U in G, alphaFun p m n i U ∂(arrayMeasure N) := by
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
  have hdisjStep : Pairwise (fun γ γ' : Pref N n =>
      Disjoint ((prefAgree p m γ ∩ B γ) ∩ StepCross.stepUp p m n i)
        ((prefAgree p m γ' ∩ B γ') ∩ StepCross.stepUp p m n i)) := by
    intro γ γ' hne
    exact (hdisj hne).mono Set.inter_subset_left Set.inter_subset_left
  have hstep_measure : ∀ γ : Pref N n,
      arrayMeasure N ((prefAgree p m γ ∩ B γ) ∩ StepCross.stepUp p m n i) =
        arrayMeasure N (prefAgree p m γ ∩ B γ) * ENNReal.ofReal (alphaOf p m n γ i) := by
    intro γ
    have h := enl_measure_right_piece (m := m) p hp0 hp1 γ (hB γ) i
    rw [mul_comm]
    exact h
  have hlhs : arrayMeasure N (G ∩ StepCross.stepUp p m n i) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) *
        ENNReal.ofReal (alphaOf p m n γ i) := by
    have hunion : G ∩ StepCross.stepUp p m n i =
        ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) ∩ StepCross.stepUp p m n i := by
      conv_lhs => rw [hGunion]
      rw [Set.iUnion_inter]
    rw [hunion, measure_iUnion hdisjStep (fun γ =>
      (hbase γ).inter (StepCross.measurable_stepUp p m n i))]
    exact tsum_congr hstep_measure
  have hrhs : ∫⁻ U in G, ENNReal.ofReal (alphaFun p m n i U) ∂(arrayMeasure N) =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) *
        ENNReal.ofReal (alphaOf p m n γ i) := by
    rw [hGunion, lintegral_iUnion hbase hdisj]
    refine tsum_congr fun γ => ?_
    rw [setLIntegral_congr_fun (hbase γ) (fun U hU =>
      by rw [alphaFun_eq_alphaOf_on_prefix p m hU.1 i])]
    rw [setLIntegral_const, mul_comm]
  have hmain : arrayMeasure N (G ∩ StepCross.stepUp p m n i) =
      ∫⁻ U in G, ENNReal.ofReal (alphaFun p m n i U) ∂(arrayMeasure N) := by
    rw [hlhs, hrhs]
  have hαmeas : Measurable (alphaFun (N := N) p m n i) :=
    fun s hs => (enlFilt p m).le n _ (measurable_alphaFun_enl p m n i hs)
  have hG0 : MeasurableSet G := (enlFilt p m).le n G hG
  have hnn : ∀ U, 0 ≤ alphaFun p m n i U := fun U =>
    (alphaFun_mem_Icc hp0 hp1 m n i U).1
  have hle1 : ∀ U, alphaFun p m n i U ≤ 1 := fun U =>
    (alphaFun_mem_Icc hp0 hp1 m n i U).2
  have hInt : Integrable (G.indicator (alphaFun p m n i)) (arrayMeasure N) := by
    refine Integrable.of_bound ((hαmeas.indicator hG0).aestronglyMeasurable) 1 ?_
    filter_upwards with U
    by_cases hU : U ∈ G
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_of_nonneg (hnn U)]
      exact hle1 U
    · rw [Set.indicator_of_notMem hU]
      simp
  have hofreal : ENNReal.ofReal (∫ U in G, alphaFun p m n i U ∂(arrayMeasure N)) =
      ∫⁻ U in G, ENNReal.ofReal (alphaFun p m n i U) ∂(arrayMeasure N) := by
    rw [← integral_indicator hG0]
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun U => by
      by_cases hU : U ∈ G
      · rw [Set.indicator_of_mem hU]; exact hnn U
      · rw [Set.indicator_of_notMem hU]; exact le_rfl)]
    rw [← lintegral_indicator hG0 (fun U => ENNReal.ofReal (alphaFun p m n i U))]
    refine lintegral_congr fun U => ?_
    by_cases hU : U ∈ G
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
      simp
  have hreal : ENNReal.ofReal ((arrayMeasure N).real (G ∩ StepCross.stepUp p m n i)) =
      ENNReal.ofReal (∫ U in G, alphaFun p m n i U ∂(arrayMeasure N)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _), hofreal]
    exact hmain
  have hnonneg : 0 ≤ ∫ U in G, alphaFun p m n i U ∂(arrayMeasure N) := integral_nonneg hnn
  calc (arrayMeasure N).real (G ∩ StepCross.stepUp p m n i)
      = (ENNReal.ofReal ((arrayMeasure N).real (G ∩ StepCross.stepUp p m n i))).toReal :=
        (ENNReal.toReal_ofReal measureReal_nonneg).symm
    _ = (ENNReal.ofReal (∫ U in G, alphaFun p m n i U ∂(arrayMeasure N))).toReal := by
        rw [hreal]
    _ = ∫ U in G, alphaFun p m n i U ∂(arrayMeasure N) := ENNReal.toReal_ofReal hnonneg

end Swarming.Enl


namespace Swarming.Enl

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open Swarming.Transition SwarmCross

variable {N : ℕ}

/-- **The conditional one-step right-jump law on the enlarged filtration.**
Given the whole enlarged filtration at time `n`, the indicator of the event that walker `i`
steps one unit right at time `n` has conditional expectation the current right probability
`alphaFun p m n i`.  This is a genuine `condExp` identity over *all* enlarged-filtration
events, not a fixed-history measure identity. -/
theorem condExp_stepUp_enl (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (i : Fin N) :
    (arrayMeasure N)[stepUpInd p m n i | enlFilt p m n] =ᵐ[arrayMeasure N] alphaFun p m n i := by
  classical
  have hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hsig : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hαmeas : Measurable[enlFilt p m n] (alphaFun p m n i) := measurable_alphaFun_enl p m n i
  have hα_ae : AEStronglyMeasurable[enlFilt p m n] (alphaFun p m n i) (arrayMeasure N) :=
    hαmeas.aestronglyMeasurable
  have hstep : MeasurableSet (StepCross.stepUp p m n i) := StepCross.measurable_stepUp p m n i
  have hind_int : Integrable (stepUpInd p m n i) (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator hstep).aestronglyMeasurable) ?_
    filter_upwards with U
    by_cases hU : U ∈ StepCross.stepUp p m n i
    · rw [stepUpInd, Set.indicator_of_mem hU, Real.norm_eq_abs, abs_one]
    · rw [stepUpInd, Set.indicator_of_notMem hU]
      simp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hind_int ?_ ?_ hα_ae).symm
  · intro s hs hfin
    have hα_amb : Measurable (alphaFun (N := N) p m n i) :=
      fun t ht => hle _ (measurable_alphaFun_enl p m n i ht)
    exact ((integrable_const (1 : ℝ)).mono' hα_amb.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((alphaFun_mem_Icc hp0 hp1 m n i U).1)]
        exact (alphaFun_mem_Icc hp0 hp1 m n i U).2)).integrableOn
  · intro s hs hfin
    have hs' : MeasurableSet s := hle s hs
    have h1 : ∫ U in s, stepUpInd (N := N) p m n i U ∂(arrayMeasure N) =
        (arrayMeasure N).real (s ∩ StepCross.stepUp p m n i) := by
      rw [← integral_indicator (μ := arrayMeasure N) hs' (f := stepUpInd (N := N) p m n i)]
      have hcongr : ∫ U, s.indicator (stepUpInd (N := N) p m n i) U ∂(arrayMeasure N) =
          ∫ U, (s ∩ StepCross.stepUp p m n i).indicator (fun _ => (1 : ℝ)) U ∂(arrayMeasure N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        by_cases hU : U ∈ s
        · rw [Set.indicator_of_mem hU]
          by_cases h2 : U ∈ StepCross.stepUp p m n i
          · rw [stepUpInd, Set.indicator_of_mem h2,
              Set.indicator_of_mem (Set.mem_inter hU h2)]
          · rw [stepUpInd, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (fun h => h2 h.2)]
        · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem (fun h => hU h.1)]
      rw [hcongr]
      exact integral_indicator_one (μ := arrayMeasure N) (hs'.inter hstep)
    rw [h1]
    exact (enl_setIntegral_stepUp p hp0 hp1 hs i).symm

end Swarming.Enl

