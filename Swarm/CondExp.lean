import Swarm.CondLaw

namespace SwarmCross

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.History Swarming.HistoryDeterminism Swarming.Transition
open Swarming.StepCross
open scoped ENNReal BigOperators Function

variable {N : ℕ}

set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

/-! ### Path space, atoms, and the random right probability as a path functional -/

/-- The countable space of joint path prefixes. -/
abbrev Path (N n : ℕ) := Fin (n + 1) → Fin N → ℤ

/-- The atom of the path filtration at the path `q`. -/
noncomputable def atom (p : ℝ) (m : ℕ) (n : ℕ) (q : Path N n) : Set (Array N) :=
  pathPrefix p m n ⁻¹' {q}

lemma pathPrefix_eq_iff (p : ℝ) (m : ℕ) (n : ℕ) (ω U : Array N) :
    pathPrefix p m n ω = pathPrefix p m n U ↔
      ∀ k ≤ n, (trajectory p m ω k).pos = (trajectory p m U k).pos := by
  constructor
  · intro h k hk
    funext i
    exact congrFun (congrFun h ⟨k, by omega⟩) i
  · intro h
    funext k i
    exact congrFun (h (k : ℕ) (by omega)) i

lemma currentAlpha_eq_of_pathPrefix_eq (p : ℝ) (m : ℕ) (n : ℕ) (ω ω' : Array N)
    (h : pathPrefix p m n ω = pathPrefix p m n ω') (i : Fin N) :
    currentAlpha p m ω n i = currentAlpha p m ω' n i := by
  have hk := (pathPrefix_eq_iff p m n ω ω').mp h
  exact congrFun (currentAlpha_eq_of_state (m := m) (state_eq_of_path_eq p m ω' ω n hk)) i

lemma atom_eq_letterBox (p : ℝ) (m : ℕ) (n : ℕ) {U : Array N} {q : Path N n}
    (h : pathPrefix p m n U = q) : atom p m n q = letterBox p m U n := by
  ext ω
  rw [letterBox_iff_path]
  simp only [atom, mem_preimage, mem_singleton_iff]
  rw [← h]
  exact pathPrefix_eq_iff p m n ω U

lemma measurableSet_atom (p : ℝ) (m : ℕ) (n : ℕ) (q : Path N n) :
    MeasurableSet (atom (N := N) p m n q) :=
  measurableSet_pathPrefix_preimage p m n _

lemma measurableSet_atom_pathMeas (p : ℝ) (m : ℕ) (n : ℕ) (q : Path N n) :
    MeasurableSet[pathMeas p m n] (atom (N := N) p m n q) :=
  ⟨{q}, trivial, rfl⟩

lemma iUnion_atom (p : ℝ) (m : ℕ) (n : ℕ) : (⋃ q : Path N n, atom p m n q) = univ := by
  ext ω
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨pathPrefix p m n ω, rfl⟩

lemma disjoint_atom {p : ℝ} {m : ℕ} {n : ℕ} {q q' : Path N n} (h : q ≠ q') :
    Disjoint (atom p m n q) (atom p m n q') := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  simp only [atom, mem_preimage, mem_singleton_iff] at h1 h2
  exact h (h1.symm.trans h2)

/-- The actual right probability of walker `i`, as a function on `Array N`. -/
noncomputable def alphaFun (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : Array N → ℝ :=
  fun ω => currentAlpha p m ω n i

/-- A representative array of a path prefix (canonical, by choice). -/
noncomputable def rep (p : ℝ) (m : ℕ) (n : ℕ) (q : Path N n) : Array N := by
  classical
  exact if h : ∃ U : Array N, pathPrefix p m n U = q then Classical.choose h else 0

lemma rep_spec {p : ℝ} {m : ℕ} {n : ℕ} {q : Path N n}
    (h : ∃ U : Array N, pathPrefix p m n U = q) : pathPrefix p m n (rep p m n q) = q := by
  unfold rep
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The same quantity as a function of the path prefix only. -/
noncomputable def alphaAt (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (q : Path N n) : ℝ :=
  currentAlpha p m (rep p m n q) n i

lemma alphaFun_eq_alphaAt (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (ω : Array N) :
    alphaFun p m n i ω = alphaAt p m n i (pathPrefix p m n ω) := by
  have h : ∃ U : Array N, pathPrefix p m n U = pathPrefix p m n ω := ⟨ω, rfl⟩
  have hspec := rep_spec h
  have hh := currentAlpha_eq_of_pathPrefix_eq p m n (rep p m n (pathPrefix p m n ω)) ω hspec i
  simp only [alphaFun, alphaAt]
  exact hh.symm

lemma measurable_alphaAt (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Measurable (alphaAt (N := N) p m n i) :=
  measurable_of_countable _

lemma measurable_alphaFun (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Measurable[pathMeas p m n] (alphaFun (N := N) p m n i) := by
  have hfun : alphaFun (N := N) p m n i =
      fun ω => alphaAt (N := N) p m n i (pathPrefix p m n ω) := by
    funext ω
    exact alphaFun_eq_alphaAt p m n i ω
  rw [hfun]
  exact measurable_pathMeas_comp (N := N) p m n (alphaAt (N := N) p m n i)

lemma alphaFun_mem_Icc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ) (i : Fin N)
    (ω : Array N) : 0 ≤ alphaFun p m n i ω ∧ alphaFun p m n i ω ≤ 1 := by
  constructor
  · exact (currentAlpha_pos hp0 hp1 m ω n i).le
  · exact (currentAlpha_lt_one hp0 hp1 m ω n i).le

/-! ### The one-step law on an atom -/

theorem measure_atom_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (i : Fin N) (q : Path N n) :
    arrayMeasure N (atom p m n q ∩ stepUp p m n i) =
      arrayMeasure N (atom p m n q) * ENNReal.ofReal (alphaAt p m n i q) := by
  by_cases hq : ∃ U : Array N, pathPrefix p m n U = q
  · obtain ⟨U, hU⟩ := hq
    have hatom : atom p m n q = letterBox p m U n := atom_eq_letterBox p m n hU
    have halpha : alphaAt p m n i q = currentAlpha p m U n i := by
      have hspec : pathPrefix p m n (rep p m n q) = q := rep_spec ⟨U, hU⟩
      have hh := currentAlpha_eq_of_pathPrefix_eq p m n (rep p m n q) U
        (hspec.trans hU.symm) i
      exact hh
    rw [hatom, halpha]
    exact measure_letterBox_inter_stepUp hp0 hp1 m U n i
  · have hempty : atom p m n q = ∅ := by
      ext ω
      simp only [atom, mem_preimage, mem_singleton_iff, mem_empty_iff_false]
      exact ⟨fun h => hq ⟨ω, h⟩, fun h => h.elim⟩
    rw [hempty]
    simp

/-- On an atom the random right probability is the constant `alphaAt q`. -/
lemma alphaFun_eq_on_atom {p : ℝ} {m : ℕ} {n : ℕ} {i : Fin N} {q : Path N n} {ω : Array N}
    (h : ω ∈ atom p m n q) : alphaFun p m n i ω = alphaAt p m n i q := by
  simp only [atom, mem_preimage, mem_singleton_iff] at h
  rw [alphaFun_eq_alphaAt]
  rw [h]

/-! ### The set-integral form of the conditional one-step law -/

theorem lintegral_stepUp_eq {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (i : Fin N) {A : Set (Array N)} (hA : MeasurableSet[pathMeas p m n] A) :
    arrayMeasure N (A ∩ stepUp p m n i) =
      ∫⁻ ω in A, ENNReal.ofReal (alphaFun p m n i ω) ∂(arrayMeasure N) := by
  classical
  set μ := arrayMeasure N
  set S := pathPrefix p m n '' A with hS
  have hAle : MeasurableSet A := pathMeas_le (N := N) p m n A hA
  have hAeq : A = pathPrefix p m n ⁻¹' S := by
    obtain ⟨T, -, rfl⟩ := hA
    ext ω
    simp only [hS, mem_preimage, mem_image]
    exact ⟨fun hω => ⟨ω, hω, rfl⟩, fun ⟨U, hU, hUω⟩ => hUω ▸ hU⟩
  have hatomA : ∀ {q : Path N n}, q ∈ S → A ∩ atom p m n q = atom p m n q := by
    intro q hq
    ext ω
    simp only [mem_inter_iff, atom, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2
      refine ⟨?_, h2⟩
      rw [hAeq]
      simp only [mem_preimage]
      rw [h2]
      exact hq
  have hatomNotA : ∀ {q : Path N n}, q ∉ S → A ∩ atom p m n q = ∅ := by
    intro q hq
    ext ω
    simp only [mem_inter_iff, atom, mem_preimage, mem_singleton_iff, mem_empty_iff_false]
    exact ⟨fun h => hq (by rw [hS, mem_image]; exact ⟨ω, h.1, h.2⟩), fun h => h.elim⟩
  have hdisj : Pairwise (Disjoint on fun q : Path N n => A ∩ atom p m n q) := by
    intro q q' hne
    rw [Function.onFun]
    exact (disjoint_atom hne).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ q : Path N n, MeasurableSet (A ∩ atom p m n q) :=
    fun q => hAle.inter (measurableSet_atom p m n q)
  have hunion : A = ⋃ q : Path N n, A ∩ atom p m n q := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, atom, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨pathPrefix p m n ω, h, rfl⟩, fun ⟨q, h, hq⟩ => h⟩
  have hdisj' : Pairwise (Disjoint on fun q : Path N n => (A ∩ atom p m n q) ∩ stepUp p m n i) := by
    intro q q' hne
    rw [Function.onFun]
    exact (disjoint_atom hne).mono
      (Set.inter_subset_left.trans Set.inter_subset_right)
      (Set.inter_subset_left.trans Set.inter_subset_right)
  have hLHS : μ (A ∩ stepUp p m n i) =
      ∑' q, μ ((A ∩ atom p m n q) ∩ stepUp p m n i) := by
    have hset : A ∩ stepUp p m n i = ⋃ q, (A ∩ atom p m n q) ∩ stepUp p m n i := by
      conv_lhs => rw [hunion]
      rw [Set.iUnion_inter]
    rw [hset]
    exact measure_iUnion hdisj' (fun q => (hmeas q).inter (measurable_stepUp p m n i))
  have hRHS : ∫⁻ ω in A, ENNReal.ofReal (alphaFun p m n i ω) ∂μ =
      ∑' q, ∫⁻ ω in (A ∩ atom p m n q), ENNReal.ofReal (alphaFun p m n i ω) ∂μ := by
    have hset : A = ⋃ q, A ∩ atom p m n q := hunion
    conv_lhs => rw [hset]
    exact lintegral_iUnion hmeas hdisj _
  rw [hLHS, hRHS]
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ S
  · have hAq := hatomA hq
    rw [hAq, measure_atom_inter_stepUp hp0 hp1 m n i q,
      setLIntegral_congr_fun (measurableSet_atom p m n q)
        (fun ω hω => by rw [alphaFun_eq_on_atom hω]),
      setLIntegral_const]
    exact mul_comm _ _
  · rw [hatomNotA hq]
    simp

/-! ### The real (Bochner) form -/

theorem setIntegral_stepUp_eq {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ)
    (i : Fin N) {A : Set (Array N)} (hA : MeasurableSet[pathMeas p m n] A) :
    (arrayMeasure N).real (A ∩ stepUp p m n i) =
      ∫ ω in A, alphaFun p m n i ω ∂(arrayMeasure N) := by
  classical
  set μ := arrayMeasure N
  set α := alphaFun (N := N) p m n i with hα
  have hAle : MeasurableSet A := pathMeas_le (N := N) p m n A hA
  have hnn : ∀ ω, 0 ≤ α ω := fun ω => (alphaFun_mem_Icc hp0 hp1 m n i ω).1
  have hle1 : ∀ ω, α ω ≤ 1 := fun ω => (alphaFun_mem_Icc hp0 hp1 m n i ω).2
  have hαmeas : Measurable α :=
    fun s hs => pathMeas_le (N := N) p m n _ (measurable_alphaFun p m n i hs)
  have hmeas_ind : Measurable (fun ω => A.indicator α ω) := hαmeas.indicator hAle
  have hint_ind : Integrable (fun ω => A.indicator α ω) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas_ind.aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
      exact hle1 ω
    · rw [Set.indicator_of_notMem hω]
      simp
  have hnn_ind : 0 ≤ᵐ[μ] fun ω => A.indicator α ω := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; exact hnn ω
    · rw [Set.indicator_of_notMem hω]; simp
  have h2 : ENNReal.ofReal (∫ ω in A, α ω ∂μ) =
      ∫⁻ ω in A, ENNReal.ofReal (α ω) ∂μ := by
    have hkey := ofReal_integral_eq_lintegral_ofReal (μ := μ) hint_ind hnn_ind
    rw [integral_indicator hAle] at hkey
    rw [hkey, ← lintegral_indicator hAle]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
  have h1 : ENNReal.ofReal ((μ).real (A ∩ stepUp p m n i)) = μ (A ∩ stepUp p m n i) := by
    rw [measureReal_def]
    exact ENNReal.ofReal_toReal (measure_ne_top μ _)
  have hmain := lintegral_stepUp_eq hp0 hp1 m n i hA
  have key : ENNReal.ofReal ((μ).real (A ∩ stepUp p m n i)) =
      ENNReal.ofReal (∫ ω in A, α ω ∂μ) := by
    rw [h1, h2]
    exact hmain
  have hint_nonneg : 0 ≤ ∫ ω in A, α ω ∂μ := integral_nonneg hnn
  calc (μ).real (A ∩ stepUp p m n i)
      = (ENNReal.ofReal ((μ).real (A ∩ stepUp p m n i))).toReal :=
        (ENNReal.toReal_ofReal measureReal_nonneg).symm
    _ = (ENNReal.ofReal (∫ ω in A, α ω ∂μ)).toReal := by rw [key]
    _ = ∫ ω in A, α ω ∂μ := ENNReal.toReal_ofReal hint_nonneg

/-! ### The conditional expectation form -/

/-- The indicator of the one-step right-jump event, as a real function. -/
noncomputable def stepUpInd (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : Array N → ℝ :=
  (stepUp p m n i).indicator (fun _ => (1 : ℝ))

theorem condExp_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ) (i : Fin N) :
    (arrayMeasure N)[stepUpInd p m n i | pathMeas p m n] =ᵐ[arrayMeasure N] alphaFun p m n i := by
  classical
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : pathMeas p m n ≤ (inferInstance : MeasurableSpace (Array N)) :=
    (pathFilt (N := N) p m).le' n
  haveI hsig : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hαmeas : Measurable[pathMeas p m n] (alphaFun (N := N) p m n i) :=
    measurable_alphaFun p m n i
  have hα_ae : AEStronglyMeasurable[pathMeas p m n] (alphaFun (N := N) p m n i)
      (arrayMeasure N) := hαmeas.aestronglyMeasurable
  have hind_meas : MeasurableSet (stepUp p m n i) := measurable_stepUp p m n i
  have hind_int : Integrable (stepUpInd (N := N) p m n i) (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (((measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator
        hind_meas).aestronglyMeasurable)
    · filter_upwards with ω
      by_cases hω : ω ∈ stepUp p m n i
      · rw [stepUpInd, Set.indicator_of_mem hω, Real.norm_eq_abs, abs_one]
      · rw [stepUpInd, Set.indicator_of_notMem hω]
        simp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hind_int ?_ ?_ hα_ae).symm
  · intro s hs hfin
    have hα_amb : Measurable (alphaFun (N := N) p m n i) :=
      fun t ht => pathMeas_le (N := N) p m n _ (measurable_alphaFun p m n i ht)
    exact ((integrable_const (1 : ℝ)).mono' hα_amb.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((alphaFun_mem_Icc hp0 hp1 m n i ω).1)]
        exact (alphaFun_mem_Icc hp0 hp1 m n i ω).2)).integrableOn
  · intro s hs hfin
    have hs' : MeasurableSet s := pathMeas_le (N := N) p m n s hs
    have h1 : ∫ ω in s, stepUpInd (N := N) p m n i ω ∂(arrayMeasure N) =
        (arrayMeasure N).real (s ∩ stepUp p m n i) := by
      rw [← integral_indicator (μ := arrayMeasure N) hs' (f := stepUpInd (N := N) p m n i)]
      have hcongr : ∫ ω, s.indicator (stepUpInd (N := N) p m n i) ω ∂(arrayMeasure N) =
          ∫ ω, (s ∩ stepUp p m n i).indicator (fun _ => (1 : ℝ)) ω ∂(arrayMeasure N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ s
        · rw [Set.indicator_of_mem hω]
          by_cases h2 : ω ∈ stepUp p m n i
          · rw [stepUpInd, Set.indicator_of_mem h2, Set.indicator_of_mem (Set.mem_inter hω h2)]
          · rw [stepUpInd, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (fun h => h2 h.2)]
        · rw [Set.indicator_of_notMem hω,
            Set.indicator_of_notMem (fun h => hω h.1)]
      rw [hcongr]
      exact integral_indicator_one (μ := arrayMeasure N) (hs'.inter hind_meas)
    rw [h1]
    exact (setIntegral_stepUp_eq hp0 hp1 m n i hs).symm

end SwarmCross


