import Swarm.ArrayWordDecomp
import SwarmDiameter.LeadingWalkTrial
import SwarmDiameter.TwoWalkerTrial

open Filter Finset MeasureTheory Set
open Swarming Swarming.Enl Swarming.Uniform Swarming.Transition Swarming.CurrentState
open SwarmCross SwarmReflect SwarmRestart SwarmFreshArray SwarmArrayWords
open SimJump.Record
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ}

private def initialSteps (L u : ℕ) (i : Fin (N + 1)) : ℤ :=
  trialPreparation L (u + 1) (decide (i = Fin.last N)) -
    trialPreparation L u (decide (i = Fin.last N))

private theorem initialPositions {U : Uniform.Array (N + 1)} {n L : ℕ} {r : ℤ}
    (hr : RecordAt p m U n r)
    (h : U ∈ evWord p m n univ (initialSteps L) (4 * L)) :
    ∀ u ≤ 4 * L, ∀ i, posPath p m U (n + u) i =
      r + trialPreparation L u (decide (i = Fin.last N)) := by
  apply posPath_eq_of_mem_evWord h
  · intro i
    have hr' : posPath p m U n i = r := hr.2 i
    simp [hr']
  · intro s _ i
    unfold initialSteps
    ring

private def combine (k N : ℕ) :
    ((Fin k → Fin N → Bool) × (Fin k → Bool)) ↪ (Fin k → Fin (N + 1) → Bool) where
  toFun z u := Fin.snoc (α := fun _ => Bool) (z.1 u) (z.2 u)
  inj' z z' h := by
    apply Prod.ext
    · funext u i
      have he := congrFun (congrFun h u) i.castSucc
      simpa only [Fin.snoc_castSucc] using he
    · funext u
      have he := congrFun (congrFun h u) (Fin.last N)
      simpa only [Fin.snoc_last] using he

private theorem combine_castSucc {k : ℕ} (w : Fin k → Fin N → Bool) (v : Fin k → Bool)
    (u : Fin k) (i : Fin N) : combine k N (w, v) u i.castSucc = w u i := by
  change Fin.snoc (α := fun _ => Bool) (w u) (v u) i.castSucc = w u i
  simp

private theorem combine_last {k : ℕ} (w : Fin k → Fin N → Bool) (v : Fin k → Bool)
    (u : Fin k) : combine k N (w, v) u (Fin.last N) = v u := by
  change Fin.snoc (α := fun _ => Bool) (w u) (v u) (Fin.last N) = v u
  simp

private theorem posPath_succ_of_mem_jbox {V : Uniform.Array N} {k : ℕ} {w : Fin k → Fin N → Bool}
    (hV : V ∈ jbox p m k w) {s : ℕ} (hs : s < k) (i : Fin N) :
    posPath p m V (s + 1) i = posPath p m V s i + step (w ⟨s, hs⟩ i) := by
  change Swarming.Trajectory.nextPos p m V (Swarming.Trajectory.trajectory p m V s) i = _
  rw [nextPos_eq_nextJumpVec, show nextJumpVec p m V s i = w ⟨s, hs⟩ i from hV ⟨s, hs⟩ i]
  cases w ⟨s, hs⟩ i <;> rfl

private theorem separatedPositions {U : Uniform.Array (N + 1)} {V : Uniform.Array N} {n L k u : ℕ} {r : ℤ}
    (hL : 0 < L) (hu : u ≤ k) (hr : RecordAt p m U n r)
    (h : U ∈ evWord p m n univ (initialSteps L) (4 * L))
    {w : Fin k → Fin N → Bool} (hV : V ∈ jbox p m k w) (v : Fin k → Bool)
    (hword : U ∈ evWord p m (n + 4 * L) univ (signedSteps (combine k N (w, v))) u) :
    ∀ s ≤ u,
      (∀ i : Fin N, posPath p m U (n + 4 * L + s) i.castSucc =
        r + 4 * (L : ℤ) + posPath p m V s i) ∧
      posPath p m U (n + 4 * L + s) (Fin.last N) = r + 2 * (L : ℤ) + psum v s := by
  let f (s : ℕ) : Fin (N + 1) → ℤ := Fin.snoc (α := fun _ => ℤ)
    (fun i => r + 4 * (L : ℤ) + posPath p m V s i) (r + 2 * (L : ℤ) + psum v s)
  have h₀ (i : Fin (N + 1)) : posPath p m U (n + 4 * L) i = f 0 i := by
    rw [initialPositions hr h (4 * L) le_rfl i]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [f, trialPreparation_true_end L hL]
    · simp [f, Fin.castSucc_ne_last, SwarmFresh.posPath_zero]
  have hstep (s : ℕ) (hs : s < u) (i : Fin (N + 1)) :
      signedSteps (combine k N (w, v)) s i = f (s + 1) i - f s i := by
    have hk : s < k := hs.trans_le hu
    rw [signedSteps, dif_pos hk]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [combine_last, Fin.snoc_last, f, psum_succ_of_lt v hk]
      ring
    · simp only [combine_castSucc, Fin.snoc_castSucc, f,
        posPath_succ_of_mem_jbox hV hk]
      ring
  intro s hs
  have hf := posPath_eq_of_mem_evWord hword h₀ hstep s hs
  exact ⟨fun i => by simpa [f] using hf i.castSucc, by simpa [f] using hf (Fin.last N)⟩

private theorem stepProbabilities {U : Uniform.Array (N + 1)} {V : Uniform.Array N} {n L k u : ℕ} {r : ℤ}
    (hL : 0 < L) (hm : N + 1 ≤ m) (hu : u ≤ k) (hr : RecordAt p m U n r)
    (hprep : U ∈ evWord p m n univ (initialSteps L) (4 * L))
    {w : Fin k → Fin N → Bool} (hV : V ∈ jbox p m k w)
    (hpos : ∀ s < k, ∀ i, 0 < posPath p m V (s + 1) i)
    {v : Fin k → Bool} (hv : ∀ s ≤ k, |psum v s| ≤ (L : ℤ))
    (hword : U ∈ evWord p m (n + 4 * L) univ (signedSteps (combine k N (w, v))) u) :
    (∀ i : Fin N, alphaFun p m (n + 4 * L + u) i.castSucc U = alphaFun p m u i V) ∧
      alphaFun p m (n + 4 * L + u) (Fin.last N) U = 1 / 2 := by
  have h := separatedPositions hL hu hr hprep hV v hword
  have hpre (s : ℕ) (hs : s ≤ 4 * L) (i : Fin N) :
      posPath p m U (n + s) i.castSucc = r + (s : ℤ) := by
    rw [initialPositions hr hprep s hs]
    simp [Fin.castSucc_ne_last]
  have hbefore (s : ℕ) (hs : s < n + 4 * L) (i : Fin N) :
      posPath p m U s i.castSucc < r + 4 * (L : ℤ) := by
    by_cases hs' : s < n
    · have hlt : posPath p m U s i.castSucc < r := hr.1 s hs' i.castSucc
      omega
    · have he : s = n + (s - n) := by omega
      rw [he, hpre (s - n) (by omega) i]
      omega
  have hleading (s : ℕ) (hs₀ : 0 < s) (hs : s ≤ u) (i : Fin N) :
      r + 4 * (L : ℤ) < posPath p m U (n + 4 * L + s) i.castSucc := by
    rw [(h s hs).1]
    have hp' : 0 < posPath p m V s i := by
      have ht := hpos (s - 1) (by omega) i
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ s)] at ht
    omega
  have htrailing (s : ℕ) (hs : s ≤ u) :
      r + (L : ℤ) ≤ posPath p m U (n + 4 * L + s) (Fin.last N) ∧
      posPath p m U (n + 4 * L + s) (Fin.last N) ≤ r + 3 * (L : ℤ) := by
    rw [(h s hs).2]
    have hvs := abs_le.mp (hv s (hs.trans hu))
    omega
  have hlast (s : ℕ) (hs : s ≤ n + 4 * L + u) :
      posPath p m U s (Fin.last N) < r + 4 * (L : ℤ) := by
    by_cases hs' : s < n
    · have hlt : posPath p m U s (Fin.last N) < r := hr.1 s hs' _
      omega
    · by_cases hp' : s ≤ n + 4 * L
      · have he : s = n + (s - n) := by omega
        rw [he, initialPositions hr hprep (s - n) (by omega) (Fin.last N)]
        have ht := trialPreparation_true_le L (s - n) (by omega)
        simp only [eq_self, decide_true]
        omega
      · let t := s - (n + 4 * L)
        have he : s = n + 4 * L + t := by dsimp only [t]; omega
        rw [he]
        have ht := (htrailing t (by dsimp only [t]; omega)).2
        omega
  constructor
  · intro i
    have hi : 0 ≤ posPath p m V u i := by
      by_cases he : u = 0
      · simp [he, SwarmFresh.posPath_zero]
      · have ht := hpos (u - 1) (by omega) i
        rw [Nat.sub_add_cancel (by omega : 1 ≤ u)] at ht
        exact ht.le
    exact leading_rightProbability_eq hbefore (fun s hs => (h s hs).1) hlast i hi
  · exact trailing_rightProbability_eq_half hm (fun s hs i => hr.1 s hs i.castSucc) hpre hleading
      (htrailing u le_rfl).1 (htrailing u le_rfl).2

private theorem real_mass_jbox_eq_prod (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {k : ℕ} (w : Fin k → Fin N → Bool) :
    (arrayMeasure N).real (jbox p m k w) = ∏ u ∈ range k, ∏ i : Fin N,
      jumpWeight (extendPath w u i) (jalpha p m (extendPath w) u i) := by
  have hn (a : Fin k × Fin N) :
      0 ≤ jumpWeight (w a.1 a.2) (jalpha p m (extendPath w) a.1 a.2) :=
    jumpWeight_nonneg (jalpha_pos hp₀ m (extendPath w) _ _)
      (jalpha_lt_one hp₁ m (extendPath w) _ _)
  rw [measureReal_def, mass_jbox hp₀ hp₁, ENNReal.toReal_ofReal (Finset.prod_nonneg fun a _ => hn a),
    Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro u _
  rw [extendPath_apply w u.isLt]

private theorem mass_combined_word (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : N + 1 ≤ m)
    {n L k : ℕ} (hL : 0 < L) {G : Set (Uniform.Array (N + 1))}
    (hG : MeasurableSet[enlMeas p m (n + 4 * L)] G)
    (hrec : ∀ U ∈ G, ∃ r : ℤ, RecordAt p m U n r)
    (hprep : G ⊆ evWord p m n univ (initialSteps L) (4 * L))
    {w : Fin k → Fin N → Bool} {V : Uniform.Array N} (hV : V ∈ jbox p m k w)
    (hpos : ∀ s < k, ∀ i, 0 < posPath p m V (s + 1) i)
    {v : Fin k → Bool} (hv : ∀ s ≤ k, |psum v s| ≤ (L : ℤ)) :
    (arrayMeasure (N + 1)).real (G ∩ evWord p m (n + 4 * L) univ (signedSteps (combine k N (w, v))) k) =
      (1 / 2 : ℝ) ^ k * (arrayMeasure N).real (jbox p m k w) *
        (arrayMeasure (N + 1)).real G := by
  let W (s : ℕ) := (1 / 2 : ℝ) * ∏ i : Fin N, jumpWeight (extendPath w s i) (jalpha p m (extendPath w) s i)
  rw [word_mass_eq_mul_prod hp₀ hp₁ _ k _ (signedSteps_is_unit _) hG W]
  · simp only [W, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, real_mass_jbox_eq_prod hp₀ hp₁]
  · intro u hu U hU
    obtain ⟨r, hr⟩ := hrec U hU.1
    obtain ⟨hlead, htrail⟩ := stepProbabilities hL hm hu.le hr (hprep hU.1) hV hpos hv hU.2
    unfold weightFun
    rw [Fin.prod_univ_castSucc]
    have hweight (i : Fin N) :
        (if signedSteps (combine k N (w, v)) u i.castSucc = 1 then
            alphaFun p m (n + 4 * L + u) i.castSucc U
          else 1 - alphaFun p m (n + 4 * L + u) i.castSucc U) =
          jumpWeight (extendPath w u i) (jalpha p m (extendPath w) u i) := by
      rw [hlead i, extendPath_apply w hu]
      have ha : alphaFun p m u i V = jalpha p m (extendPath w) u i :=
        currentAlpha_eq_jalpha p m k w V hV hu.le i
      rw [ha]
      simp only [signedSteps, dif_pos hu, combine_castSucc]
      cases w ⟨u, hu⟩ i <;> simp [jumpWeight]
    simp_rw [hweight]
    rw [htrail]
    split_ifs <;> dsimp only [W] <;> ring

private def leadingEvent (p : ℝ) (m N k : ℕ) (a : ℝ) : Set (Uniform.Array N) :=
  {V | (∀ s < k, ∀ i, 0 < posPath p m V (s + 1) i) ∧
    ∀ i, a * (k : ℝ) ≤ (posPath p m V k i : ℝ)}

private theorem cubic_trial_mass_ge (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hN : 0 < N) (hm : N + 1 ≤ m) (n : ℕ) {L : ℕ} (hL : 1 ≤ L) (a : ℝ)
    {G : Set (Uniform.Array (N + 1))} (hG : MeasurableSet[enlMeas p m n] G)
    (hrec : ∀ U ∈ G, ∃ r : ℤ, RecordAt p m U n r) :
    Real.exp (-4 * (L : ℝ)) * (arrayMeasure N).real (leadingEvent p m N (L ^ 3) a) *
        ((1 - p) ^ (4 * L * (N + 1)) * (arrayMeasure (N + 1)).real G) ≤
      (arrayMeasure (N + 1)).real (G ∩ {U | a * (L : ℝ) ^ 3 ≤
        pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)}) := by
  classical
  let k := L ^ 3
  let G' := G ∩ evWord p m n univ (initialSteps L) (4 * L)
  have hG' : MeasurableSet[enlMeas p m (n + 4 * L)] G' :=
    ((enlMeas_le_add (N + 1) p m n (4 * L)) G hG).inter
      (measurableSet_evWord_enl p m n univ (initialSteps L) (4 * L))
  have hG'mass : (1 - p) ^ (4 * L * (N + 1)) * (arrayMeasure (N + 1)).real G ≤
      (arrayMeasure (N + 1)).real G' := by
    have h := ENNReal.toReal_mono (measure_ne_top (arrayMeasure (N + 1)) G')
      (evWord_mass_ge_univ p hp₀.le hp₁ m n (initialSteps L) (fun u i => trialPreparation_succ_sub L u _) hG (4 * L))
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - p)] using h
  let A := univ.filter fun w : Fin k → Fin N → Bool => ∃ V ∈ jbox p m k w, V ∈ leadingEvent p m N k a
  let B := univ.filter fun v : Fin k → Bool => ∀ u ≤ k, |psum v u| ≤ (L : ℤ)
  let W := (A ×ˢ B).map (combine k N)
  have hpair {ω} (hω : ω ∈ W) : ∃ w ∈ A, ∃ v ∈ B, combine k N (w, v) = ω := by
    obtain ⟨⟨w, v⟩, hab, he⟩ := Finset.mem_map.mp hω
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨w, ha, v, hb, he⟩
  have hE : (⋃ w ∈ A, jbox p m k w) = leadingEvent p m N k a := by
    ext U
    constructor
    · intro hU
      obtain ⟨w, hw, hU'⟩ := Set.mem_iUnion₂.mp hU
      obtain ⟨V, hV, hgood⟩ := (Finset.mem_filter.mp hw).2
      have hpath (s : ℕ) (hs : s ≤ k) (i : Fin N) :
          posPath p m U s i = posPath p m V s i := by
        change (Swarming.Trajectory.trajectory p m U s).pos i = (Swarming.Trajectory.trajectory p m V s).pos i
        rw [trajectory_eq_runJ_extendPath p m k w U hU' hs, trajectory_eq_runJ_extendPath p m k w V hV hs]
      refine ⟨fun s hs i => ?_, fun i => ?_⟩
      · rw [hpath _ (by omega) i]
        exact hgood.1 s hs i
      · rw [hpath _ le_rfl i]
        exact hgood.2 i
    · intro hU
      have hu := mem_jbox_jumpWord p m k U
      exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_filter.mpr ⟨mem_univ _, U, hu, hU⟩, hu⟩
  have hA : (∑ w ∈ A, (arrayMeasure N).real (jbox p m k w)) =
      (arrayMeasure N).real (leadingEvent p m N k a) := by
    rw [← hE, measureReal_biUnion_finset (fun w _ v _ hne => disjoint_jbox hne)
      (fun w _ => measurableSet_jbox p m k w) (fun _ _ => measure_ne_top _ _)]
  have hB : Real.exp (-4 * (L : ℝ)) ≤ (B.card : ℝ) * (1 / 2 : ℝ) ^ k := by
    have hb := exp_neg_le_card_symmetric_confinement hL
    have hb' := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)
    rw [mul_assoc, ← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, mul_one] at hb'
    exact hb'
  have hmass : (arrayMeasure (N + 1)).real
      (⋃ ω ∈ W, G' ∩ evWord p m (n + 4 * L) univ (signedSteps ω) k) =
        ((B.card : ℝ) * (1 / 2 : ℝ) ^ k) * (arrayMeasure N).real (leadingEvent p m N k a) *
        (arrayMeasure (N + 1)).real G' := by
    rw [words_mass_eq_sum _ _ _ hG']
    calc
      _ = ∑ z ∈ A ×ˢ B, (1 / 2 : ℝ) ^ k * (arrayMeasure N).real (jbox p m k z.1) *
          (arrayMeasure (N + 1)).real G' := by
        rw [show W = (A ×ˢ B).map (combine k N) from rfl, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro z hz
        obtain ⟨hw, hv⟩ := Finset.mem_product.mp hz
        obtain ⟨V, hV, hpos⟩ := (Finset.mem_filter.mp hw).2
        exact mass_combined_word hp₀ hp₁ hm (by omega) hG' (fun U hU => hrec U hU.1)
          Set.inter_subset_right hV hpos.1 (Finset.mem_filter.mp hv).2
      _ = _ := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, ← Finset.mul_sum, hA]
  have hsub : (⋃ ω ∈ W, G' ∩ evWord p m (n + 4 * L) univ (signedSteps ω) k) ⊆
      G ∩ {U | a * (L : ℝ) ^ 3 ≤ pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)} := by
    intro U hU
    obtain ⟨ω, hω, hU'⟩ := Set.mem_iUnion₂.mp hU
    obtain ⟨w, hw, v, hv, rfl⟩ := hpair hω
    obtain ⟨V, hV, hpos⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨r, hr⟩ := hrec U hU'.1.1
    obtain ⟨hs₁, hs₂⟩ :=
      separatedPositions (by omega) le_rfl hr hU'.1.2 hV v hU'.2 k le_rfl
    let i : Fin N := ⟨0, hN⟩
    have hD := sub_le_pathDiameter (n + 4 * L + k) (posPath p m U) i.castSucc (Fin.last N)
    rw [hs₁ i, hs₂] at hD
    have hv' := (abs_le.mp ((Finset.mem_filter.mp hv).2 k le_rfl)).2
    have hi := hpos.2 i
    change a * (k : ℝ) ≤ (posPath p m V k i : ℝ) at hi
    push_cast at hD hi
    refine ⟨hU'.1.1, ?_⟩
    change a * (L : ℝ) ^ 3 ≤ pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)
    rw [← Nat.add_assoc]
    change a * (L : ℝ) ^ 3 ≤ pathDiameter (n + 4 * L + k) (posPath p m U)
    have hi' : a * (L : ℝ) ^ 3 ≤ (posPath p m V k i : ℝ) := by simpa only [k, Nat.cast_pow] using hi
    linarith [show (psum v k : ℝ) ≤ (L : ℝ) by exact_mod_cast hv', Nat.cast_nonneg (α := ℝ) L]
  calc
    _ ≤ ((B.card : ℝ) * (1 / 2 : ℝ) ^ k) * (arrayMeasure N).real (leadingEvent p m N k a) *
        (arrayMeasure (N + 1)).real G' :=
      mul_le_mul (mul_le_mul_of_nonneg_right hB measureReal_nonneg) hG'mass
        (mul_nonneg (pow_nonneg (by linarith) _) measureReal_nonneg)
        (mul_nonneg (by positivity) measureReal_nonneg)
    _ = _ := hmass.symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

/-- The conditional trial with diameter of order `L³` for `N + 1` walkers
and threshold at least `N + 1`. -/
theorem exists_cubic_trial_mass_ge (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hN : 2 ≤ N) (hm : N + 1 ≤ m) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ᶠ L : ℕ in atTop,
      ∀ n : ℕ, ∀ {G : Set (Uniform.Array (N + 1))}, MeasurableSet[enlMeas p m n] G →
        (∀ U ∈ G, ∃ r : ℤ, RecordAt p m U n r) →
      Real.exp (-C * (L : ℝ)) * (arrayMeasure (N + 1)).real G ≤
        (arrayMeasure (N + 1)).real (G ∩ {U | a * (L : ℝ) ^ 3 ≤
          pathDiameter (n + (4 * L + L ^ 3)) (posPath p m U)}) := by
  obtain ⟨κ, hκ, h⟩ := exists_leading_walk_trial_mass_ge hp₀ hp₁ (by omega : 2 ≤ m)
  let V := {U : Uniform.Array N | posPath p m U ∈ SwarmFresh.strictPos}
  let b := ((arrayMeasure N) V / 2).toReal
  obtain ⟨hb, hlarge⟩ := h N hN
  have hbtop : (arrayMeasure N) V / 2 ≠ ∞ :=
    ENNReal.div_ne_top (measure_ne_top _ _) (by norm_num)
  have hb₀ : 0 < b := ENNReal.toReal_pos hb.ne' hbtop
  have hp : 0 < 1 - p := by linarith
  have hlog : Real.log (1 - p) < 0 := Real.log_neg hp (by linarith)
  let c := -(4 * (N + 1 : ℝ) * Real.log (1 - p))
  have hc : 0 ≤ c := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog.le)
  let D := max 0 (-Real.log b)
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨κ / 2, 4 + c + D, by positivity, by positivity, ?_⟩
  have hpow := (tendsto_pow_atTop (α := ℕ) (n := 3) (by decide)).eventually hlarge
  filter_upwards [eventually_ge_atTop 1, hpow] with L hL hb'
  intro n G hG hrec
  have hbReal : b ≤ (arrayMeasure N).real (leadingEvent p m N (L ^ 3) (κ / 2)) :=
    ENNReal.toReal_mono (measure_ne_top _ _) hb'
  have hbexp : Real.exp (-D * (L : ℝ)) ≤ b := by
    rw [← Real.exp_log hb₀]
    apply Real.exp_le_exp.mpr
    have hD' : -Real.log b ≤ D := le_max_right _ _
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hle : D ≤ D * (L : ℝ) := le_mul_of_one_le_right hD hL'
    linarith
  have hjump : (1 - p) ^ (4 * L * (N + 1)) = Real.exp (-c * (L : ℝ)) := by
    rw [show -c * (L : ℝ) = (↑(4 * L * (N + 1) : ℕ) : ℝ) * Real.log (1 - p) by
      dsimp only [c]; push_cast; ring, Real.exp_nat_mul, Real.exp_log hp]
  have hf : Real.exp (-(4 + c + D) * (L : ℝ)) =
      (Real.exp (-4 * (L : ℝ)) * Real.exp (-D * (L : ℝ))) * (1 - p) ^ (4 * L * (N + 1)) := by
    rw [hjump, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hf, mul_assoc]
  refine (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbexp.trans hbReal) (Real.exp_pos _).le)
    (mul_nonneg (pow_nonneg hp.le _) measureReal_nonneg)).trans ?_
  exact cubic_trial_mass_ge hp₀ hp₁ (by omega) hm n hL (κ / 2) hG hrec

end Swarming.Diameter
