/-
  **One actual `Γ`-trial step: the A-restricted joint jump pattern with its uniform factor.**

  The paper (`main_1d_revised.tex`, proof of Proposition `local`, display `(trialp)`) needs

      P(Γ_y^A | F_{σ_y^A}) ≥ (1-p)^{(2m-1)|A|} ,

  where `Γ_y^A` prescribes, for `2m-1` consecutive steps, the *whole group* `A`'s jumps
  (a zig-zag `+1,-1,+1,...` for the selected walker `i_y` and `-1` for the others).

  This file builds the one-step ingredient on the actual model (`Swarming.Trajectory`):
  the mass of a prescribed jump pattern of a *subgroup* `A` of walkers on one piece of the
  enlarged filtration, exactly, with the product weight, and the uniform lower bound
  `(1-p)^{|A|}`.  Working with a subgroup (rather than the whole swarm) is what produces the
  exponent `|A|` rather than `N`.

  No proof hole, no custom axiom: everything is derived from `enl_fresh_law_piece`
  (the paper's §2.1 conditional law on the actual i.i.d. uniform array).
-/
import Swarm.EnlJoint
import Swarm.RecFresh

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The uniform law of the whole line -/

lemma uniform01_univ : uniform01 (Set.univ : Set ℝ) = 1 := by
  rw [uniform01, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo]
  norm_num

/-! ### Partial jump patterns and their weights -/

/-- The event that at time `n` every walker of `A` makes the prescribed jump `ε`. -/
noncomputable def patSetA (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (ε : Fin N → ℤ) :
    Set (Array N) :=
  {U | ∀ i ∈ A, (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + ε i}

/-- The per-walker weight of the prescribed jump on the piece `γ`. -/
noncomputable def factorA (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) (ε : Fin N → ℤ)
    (i : Fin N) : ℝ :=
  if ε i = 1 then alphaOf p m n γ i else 1 - alphaOf p m n γ i

/-- The weight of the prescribed partial pattern on the piece `γ`. -/
noncomputable def weightA (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) (A : Finset (Fin N))
    (ε : Fin N → ℤ) : ℝ :=
  ∏ i ∈ A, factorA p m n γ ε i

lemma alphaOf_le_p {p : ℝ} (hp0 : 1 / 2 ≤ p) (m : ℕ) {n : ℕ} (γ : Pref N n) (i : Fin N) :
    alphaOf p m n γ i ≤ p := by
  unfold alphaOf
  exact rightProbability_le_p hp0 m _ i _

/-- Each factor of a partial pattern is at least `1 - p`. -/
lemma one_sub_p_le_factorA {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (ε : Fin N → ℤ) (i : Fin N) :
    1 - p ≤ factorA p m n γ ε i := by
  unfold factorA
  by_cases h : ε i = 1
  · rw [if_pos h]
    linarith [le_alphaOf p m γ i hp0]
  · rw [if_neg h]
    linarith [alphaOf_le_p hp0 m γ i]

lemma factorA_nonneg {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (ε : Fin N → ℤ) (i : Fin N) :
    0 ≤ factorA p m n γ ε i := by
  have h := one_sub_p_le_factorA hp0 hp1 m γ ε i
  have hp : 0 < 1 - p := by linarith
  exact le_trans hp.le h

lemma factorA_le_one {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (ε : Fin N → ℤ) (i : Fin N) :
    factorA p m n γ ε i ≤ 1 := by
  unfold factorA
  by_cases h : ε i = 1
  · rw [if_pos h]
    linarith [alphaOf_lt_one p m γ i hp0 hp1]
  · rw [if_neg h]
    linarith [le_alphaOf p m γ i hp0]

/-- The exact weight of a partial pattern is bounded below by `(1-p)^{|A|}`. -/
lemma one_sub_p_pow_le_weightA {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) {n : ℕ}
    (γ : Pref N n) (A : Finset (Fin N)) (ε : Fin N → ℤ) :
    (1 - p) ^ A.card ≤ weightA p m n γ A ε := by
  have hconst : ∏ _i ∈ A, (1 - p) = (1 - p) ^ A.card := Finset.prod_const _
  rw [← hconst, weightA]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => one_sub_p_le_factorA hp0 hp1 m γ ε i)
  have hp : 0 < 1 - p := by linarith
  exact hp.le

/-! ### The exact mass of a partial pattern on one piece -/

/-- On the piece `{path = γ}` the prescribed jump of walker `i` is the assertion that the
freshly read coordinate at `fr n γ i` lies in the corresponding half-line. -/
lemma patSetA_iff_read (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) {A : Finset (Fin N)}
    (ε : Fin N → ℤ) {U : Array N} (hU : U ∈ prefAgree p m γ)
    (hε : ∀ i ∈ A, ε i = 1 ∨ ε i = -1) :
    U ∈ patSetA p m n A ε ↔
      ∀ i ∈ A, U (fr (N := N) n γ i) ∈
        (if ε i = 1 then Set.Iic (alphaOf p m n γ i) else Set.Ioi (alphaOf p m n γ i)) := by
  constructor
  · intro h i hi
    have hpos := jumpStep_of_prefAgree p m hU i
    have hd : drivenStep (U (fr (N := N) n γ i)) (alphaOf p m n γ i) = ε i := by
      have hh := h i hi
      rw [hpos] at hh
      omega
    rcases hε i hi with h1 | h1
    · rw [h1] at hd ⊢
      rw [if_pos rfl, Set.mem_Iic]
      exact (drivenStep_eq_one_iff _ _).1 hd
    · rw [h1] at hd ⊢
      rw [if_neg (by norm_num : (¬ ((-1 : ℤ) = 1))), Set.mem_Ioi]
      exact (drivenStep_eq_neg_one_iff _ _).1 hd
  · intro h i hi
    have hpos := jumpStep_of_prefAgree p m hU i
    have hi' := h i hi
    rcases hε i hi with h1 | h1
    · rw [h1, if_pos rfl, Set.mem_Iic] at hi'
      rw [hpos, (drivenStep_eq_one_iff _ _).2 hi', h1]
    · rw [h1, if_neg (by norm_num : (¬ ((-1 : ℤ) = 1))), Set.mem_Ioi] at hi'
      rw [hpos, (drivenStep_eq_neg_one_iff _ _).2 hi', h1]

/-- **The exact mass of a partial jump pattern on a piece of the enlarged filtration.** -/
theorem enl_measure_patternA_piece (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (A : Finset (Fin N)) (ε : Fin N → ℤ) (hε : ∀ i ∈ A, ε i = 1 ∨ ε i = -1) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ patSetA p m n A ε) =
      ENNReal.ofReal (weightA p m n γ A ε) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  set I : Fin N → Set ℝ := fun i =>
    if i ∈ A then (if ε i = 1 then Set.Iic (alphaOf p m n γ i) else Set.Ioi (alphaOf p m n γ i))
    else Set.univ with hI
  have hImeas : ∀ i : Fin N, MeasurableSet (I i) := by
    intro i
    by_cases hi : i ∈ A
    · rw [hI]
      simp only [hi, if_true]
      by_cases h : ε i = 1
      · rw [if_pos h]; exact measurableSet_Iic
      · rw [if_neg h]; exact measurableSet_Ioi
    · rw [hI]
      simp only [hi, if_false]
      exact MeasurableSet.univ
  have hset : prefAgree p m γ ∩ B ∩ patSetA p m n A ε =
      prefAgree p m γ ∩ B ∩
        Set.iInter (fun i : Fin N => {U : Array N | U (fr (N := N) n γ i) ∈ I i}) := by
    ext U
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hread := (patSetA_iff_read p m γ ε h1 hε).1 h3
      refine ⟨⟨h1, h2⟩, Set.mem_iInter.2 (fun i => ?_)⟩
      by_cases hi : i ∈ A
      · rw [hI]
        simp only [hi, if_true]
        exact hread i hi
      · rw [hI]
        simp only [hi, if_false]
        exact Set.mem_univ _
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      refine (patSetA_iff_read p m γ ε h1 hε).2 fun i hi => ?_
      have hi' := Set.mem_iInter.1 h3 i
      rw [hI] at hi'
      simp only [hi, if_true] at hi'
      exact hi'
  rw [hset, enl_fresh_law_piece p m n γ hB I hImeas]
  congr 1
  have hstep : ∀ i : Fin N, uniform01 (I i) =
      if i ∈ A then ENNReal.ofReal (factorA p m n γ ε i) else 1 := by
    intro i
    by_cases hi : i ∈ A
    · rw [hI]
      simp only [hi, if_true]
      by_cases h : ε i = 1
      · rw [if_pos h]
        simp only [factorA, h, if_true]
        exact uniform01_Iic (by linarith [le_alphaOf p m γ i hp0])
          (alphaOf_lt_one p m γ i hp0 hp1)
      · rw [if_neg h]
        simp only [factorA, h, if_false]
        exact uniform01_Ioi (by linarith [le_alphaOf p m γ i hp0])
          (alphaOf_lt_one p m γ i hp0 hp1)
    · rw [hI]
      simp only [hi, if_false]
      exact uniform01_univ
  have hprod : (∏ i : Fin N, uniform01 (I i)) =
      ∏ i ∈ A, ENNReal.ofReal (factorA p m n γ ε i) := by
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
    rw [← Finset.prod_filter]
    congr 1
    ext i
    simp
  rw [hprod]
  rw [weightA]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => factorA_nonneg hp0 hp1 m γ ε i)).symm

/-- **The uniform factor of one trial step.**  On any piece of the enlarged filtration, the
probability that the whole group `A` makes a prescribed joint jump is at least
`(1-p)^{|A|}` times the piece mass. -/
theorem patternA_step_ge (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (A : Finset (Fin N)) (ε : Fin N → ℤ) (hε : ∀ i ∈ A, ε i = 1 ∨ ε i = -1) :
    ENNReal.ofReal (1 - p) ^ A.card * arrayMeasure N (prefAgree p m γ ∩ B) ≤
      arrayMeasure N (prefAgree p m γ ∩ B ∩ patSetA p m n A ε) := by
  rw [enl_measure_patternA_piece p m γ hB hp0 hp1 A ε hε]
  have hkey : ENNReal.ofReal (1 - p) ^ A.card ≤ ENNReal.ofReal (weightA p m n γ A ε) := by
    rw [← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - p)]
    exact ENNReal.ofReal_le_ofReal (one_sub_p_pow_le_weightA hp0 hp1 m γ A ε)
  exact mul_le_mul' hkey le_rfl


/-! ### The one-step inequality over arbitrary enlarged-filtration events -/

/-- Events determined by the path up to time `n` are *unions of pieces*: each piece of the
enlarged filtration at time `n` is either contained in the event or disjoint from it. -/
def pathDet (p : ℝ) (m : ℕ) (n : ℕ) (S : Set (Array N)) : Prop :=
  ∀ γ : Pref N n, prefAgree p m γ ⊆ S ∨ Disjoint (prefAgree p m γ) S

lemma pathDet_prefAgree (p : ℝ) (m : ℕ) {n : ℕ} (δ : Pref N n) :
    pathDet p m n (prefAgree p m δ) := by
  intro γ
  by_cases h : γ = δ
  · exact Or.inl (le_of_eq (by rw [h]))
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro U h1 h2
    exact h (by funext t i; rw [← congrFun (h1 t) i, ← congrFun (h2 t) i])

lemma pathDet_mono (p : ℝ) (m : ℕ) {n' n : ℕ} {S : Set (Array N)} (h : pathDet p m n' S)
    (hn : n' ≤ n) : pathDet p m n S := by
  intro γ
  set δ : Pref N n' := fun t i => ext γ t.1 i with hδ
  have hsub : prefAgree p m γ ⊆ prefAgree p m δ := by
    intro U hU t
    funext i
    rw [hδ]
    simp only
    exact (ext_prefOf_of_mem hU (s := t.1) (by omega) i).symm
  rcases h δ with h1 | h2
  · exact Or.inl (Set.Subset.trans hsub h1)
  · refine Or.inr ?_
    rw [Set.disjoint_left] at h2 ⊢
    intro U hU hUS
    exact h2 (hsub hU) hUS

lemma pathDet_inter (p : ℝ) (m : ℕ) {n : ℕ} {S T : Set (Array N)}
    (h1 : pathDet p m n S) (h2 : pathDet p m n T) : pathDet p m n (S ∩ T) := by
  intro γ
  rcases h1 γ with a | a
  · rcases h2 γ with b | b
    · exact Or.inl (Set.subset_inter a b)
    · refine Or.inr ?_
      rw [Set.disjoint_left] at b ⊢
      intro U hU hST
      exact b hU hST.2
  · refine Or.inr ?_
    rw [Set.disjoint_left] at a ⊢
    intro U hU hST
    exact a hU hST.1

/-- A prescribed jump pattern at time `n` is determined by the path up to time `n+1`. -/
lemma pathDet_patSetA (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (ε : Fin N → ℤ) :
    pathDet p m (n + 1) (patSetA p m n A ε) := by
  intro γ
  by_cases h : ∀ i ∈ A, γ ⟨n + 1, by omega⟩ i = γ ⟨n, by omega⟩ i + ε i
  · refine Or.inl ?_
    intro U hU i hi
    have h1 := hU ⟨n + 1, by omega⟩
    have h2 := hU ⟨n, by omega⟩
    rw [h1, h2]
    exact h i hi
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro U hU hP
    exact h fun i hi => by
      have h1 := hU ⟨n + 1, by omega⟩
      have h2 := hU ⟨n, by omega⟩
      rw [← h1, ← h2]
      exact hP i hi

/-- If a piece at a higher level is contained in a piece at a lower level, then the read set of
the lower level is contained in the read set of the higher one. -/
lemma prefRead_subset_of_prefAgree_subset (p : ℝ) (m : ℕ) {n₀ n₁ : ℕ} (hn : n₀ ≤ n₁)
    {γ : Pref N n₀} {γ' : Pref N n₁} (hne : (prefAgree p m γ').Nonempty)
    (hsub : prefAgree p m γ' ⊆ prefAgree p m γ) : prefRead n₀ γ ⊆ prefRead n₁ γ' := by
  obtain ⟨U, hU⟩ := hne
  have hext : ∀ t, t ≤ n₀ → ext γ' t = ext γ t := by
    intro t ht
    funext i
    have h1 : ext γ' t i = (trajectory p m U t).pos i :=
      ext_prefOf_of_mem hU (s := t) (by omega) i
    have h2 : ext γ t i = (trajectory p m U t).pos i :=
      ext_prefOf_of_mem (hsub hU) (s := t) ht i
    rw [h1, h2]
  rintro ⟨i, x, k⟩ hc
  rw [mem_prefRead] at hc ⊢
  obtain ⟨t, ht, hx, hk⟩ := hc
  refine ⟨t, by omega, ?_, ?_⟩
  · rw [hext t (by omega), hx]
  · rw [localTime_congr (X := fun s => ext γ' s i) (Y := fun s => ext γ s i)
      (fun s hs => congrFun (hext s (by omega)) i), hk]

/-- **Measurability of path-determined events cut by a cylinder event.** -/
theorem measurableSet_enlMeas_of_pathDet_cyl (p : ℝ) (m : ℕ) {n₀ n₁ : ℕ} (hn : n₀ ≤ n₁)
    {γ : Pref N n₀} {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (prefRead n₀ γ)] B)
    {S : Set (Array N)} (hS : pathDet p m n₁ S) (hγS : S ⊆ prefAgree p m γ) :
    MeasurableSet[enlMeas p m n₁] (S ∩ B) := by
  intro γ'
  by_cases hcase : (prefAgree p m γ').Nonempty ∧ prefAgree p m γ' ⊆ S
  · obtain ⟨hne, hsub⟩ := hcase
    refine ⟨B, ?_, ?_⟩
    · refine cylAt_mono ?_ B hB
      exact prefRead_subset_of_prefAgree_subset p m hn hne (Set.Subset.trans hsub hγS)
    · rw [← Set.inter_assoc, Set.inter_eq_left.2 hsub]
  · -- either the piece is empty or it misses `S`
    have hempty_or : prefAgree p m γ' = ∅ ∨ Disjoint (prefAgree p m γ') S := by
      rcases hS γ' with h | h
      · by_cases hne : (prefAgree p m γ').Nonempty
        · exact absurd ⟨hne, h⟩ hcase
        · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)
      · exact Or.inr h
    have hL : prefAgree p m γ' ∩ (S ∩ B) = ∅ := by
      rcases hempty_or with h | h
      · rw [h, Set.empty_inter]
      · rw [← Set.inter_assoc, Set.disjoint_iff_inter_eq_empty.1 h, Set.empty_inter]
    refine ⟨∅, @MeasurableSet.empty (Array N) (cylAt (prefRead n₁ γ')), ?_⟩
    rw [hL, Set.inter_empty]

lemma measurableSet_patSetA (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (ε : Fin N → ℤ) :
    MeasurableSet (patSetA p m n A ε) := by
  have hset : patSetA p m n A ε = ⋂ i : Fin N,
      (if i ∈ A then {U : Array N | (trajectory p m U (n + 1)).pos i -
        (trajectory p m U n).pos i = ε i} else Set.univ) := by
    ext U
    constructor
    · intro h
      refine Set.mem_iInter.2 (fun i => ?_)
      by_cases hi : i ∈ A
      · rw [if_pos hi]
        simp only [Set.mem_ofPred_eq]
        have hh := h i hi
        omega
      · rw [if_neg hi]; exact Set.mem_univ _
    · intro h i hi
      have h1 := Set.mem_iInter.1 h i
      rw [if_pos hi] at h1
      simp only [Set.mem_ofPred_eq] at h1
      omega
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    exact measurableSet_eq_fun (((Swarming.Fair.measurable_trajectory (N := N) p m (n + 1)).1 i).sub
      ((Swarming.Fair.measurable_trajectory (N := N) p m n).1 i)) measurable_const
  · rw [if_neg hi]
    exact MeasurableSet.univ

/-- **The uniform one-step factor over an arbitrary enlarged-filtration event.**  For every
event `G` of `𝓕_n` and every prescribed joint jump of the group `A`, the probability of the
pattern is at least `(1-p)^{|A|}` times the mass of `G`. -/
theorem patternA_set_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) {m n : ℕ}
    (A : Finset (Fin N)) (ε : Fin N → ℤ) (hε : ∀ i ∈ A, ε i = 1 ∨ ε i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) :
    ENNReal.ofReal (1 - p) ^ A.card * arrayMeasure N G ≤
      arrayMeasure N (G ∩ patSetA p m n A ε) := by
  classical
  choose B hB hEq using hG
  have hGunion : G = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have h3 : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at h3
      exact h3.2
    · rintro ⟨γ, h1, h2⟩
      have h3 : U ∈ prefAgree p m γ ∩ G := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact h3.2
  have hpart : G ∩ patSetA p m n A ε =
      ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ ∩ patSetA p m n A ε) := by
    rw [hGunion, Set.iUnion_inter]
  have hdisjB : Pairwise (Function.onFun Disjoint (fun γ : Pref N n => prefAgree p m γ ∩ B γ)) := by
    intro γ γ' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hmeasB : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := fun γ =>
    (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cyl (hB γ))
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun γ : Pref N n => prefAgree p m γ ∩ B γ ∩ patSetA p m n A ε)) := by
    intro γ γ' hne
    exact (hdisjB hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ ∩ patSetA p m n A ε) :=
    fun γ => (hmeasB γ).inter (measurableSet_patSetA p m n A ε)
  have hGmass : arrayMeasure N G =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    rw [hGunion]
    exact measure_iUnion hdisjB hmeasB
  have hstep : ∀ γ : Pref N n, ENNReal.ofReal (1 - p) ^ A.card *
        arrayMeasure N (prefAgree p m γ ∩ B γ) ≤
      arrayMeasure N (prefAgree p m γ ∩ B γ ∩ patSetA p m n A ε) :=
    fun γ => patternA_step_ge p m γ (hB γ) hp0 hp1 A ε hε
  calc ENNReal.ofReal (1 - p) ^ A.card * arrayMeasure N G
      = ENNReal.ofReal (1 - p) ^ A.card *
          (∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ)) := by rw [hGmass]
    _ = ∑' γ : Pref N n, ENNReal.ofReal (1 - p) ^ A.card *
          arrayMeasure N (prefAgree p m γ ∩ B γ) := by rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' γ : Pref N n,
          arrayMeasure N (prefAgree p m γ ∩ B γ ∩ patSetA p m n A ε) :=
        ENNReal.tsum_le_tsum hstep
    _ = arrayMeasure N (G ∩ patSetA p m n A ε) := by
        rw [hpart, measure_iUnion hdisj hmeas]

/-! ### The prescribed multi-step attempt -/

/-- The event that the group `A` follows the prescribed jump word `ε` during the `k` steps
starting at time `n`, intersected with the piece `{path = γ}`. -/
noncomputable def evPrefix (m n : ℕ) (γ : Pref N n) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ)
    (p : ℝ) : ℕ → Set (Array N)
  | 0 => prefAgree p m γ
  | (k + 1) => evPrefix m n γ A ε p k ∩ patSetA p m (n + k) A (ε k)

lemma evPrefix_pathDet (p : ℝ) (m n : ℕ) (γ : Pref N n) (A : Finset (Fin N))
    (ε : ℕ → Fin N → ℤ) (k : ℕ) : pathDet p m (n + k) (evPrefix m n γ A ε p k) := by
  induction k with
  | zero => simpa [evPrefix] using pathDet_prefAgree p m γ
  | succ k ih =>
    have h1 : pathDet p m (n + k + 1) (evPrefix m n γ A ε p k) :=
      pathDet_mono p m ih (by omega)
    have h2 : pathDet p m (n + k + 1) (patSetA p m (n + k) A (ε k)) :=
      pathDet_patSetA p m (n + k) A (ε k)
    have h3 := pathDet_inter p m h1 h2
    have he : evPrefix m n γ A ε p (k + 1) =
        evPrefix m n γ A ε p k ∩ patSetA p m (n + k) A (ε k) := rfl
    rw [he]
    exact h3

lemma evPrefix_subset_prefAgree (p : ℝ) (m n : ℕ) (γ : Pref N n) (A : Finset (Fin N))
    (ε : ℕ → Fin N → ℤ) (k : ℕ) : evPrefix m n γ A ε p k ⊆ prefAgree p m γ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [evPrefix]
    exact Set.Subset.trans Set.inter_subset_left ih

/-- **The multi-step trial mass.**  The probability that the group `A` follows the prescribed
word of `k` jumps is at least `(1-p)^{k|A|}` times the mass of the piece. -/
theorem evPrefix_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m n : ℕ) (γ : Pref N n)
    (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) (k : ℕ) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N (prefAgree p m γ ∩ B) ≤
      arrayMeasure N (evPrefix m n γ A ε p k ∩ B) := by
  induction k with
  | zero =>
    have h0 : evPrefix m n γ A ε p 0 = prefAgree p m γ := rfl
    rw [h0]
    simpa using le_rfl (a := arrayMeasure N (prefAgree p m γ ∩ B))
  | succ k ih =>
    have hS : MeasurableSet[enlMeas p m (n + k)] (evPrefix m n γ A ε p k ∩ B) :=
      measurableSet_enlMeas_of_pathDet_cyl p m (le_add_right le_rfl) hB
        (evPrefix_pathDet p m n γ A ε k) (evPrefix_subset_prefAgree p m n γ A ε k)
    have hstep := patternA_set_ge p hp0 hp1 (m := m) (n := n + k) A (ε k)
      (fun i _ => hε k i) (G := evPrefix m n γ A ε p k ∩ B) hS
    have hEq : evPrefix m n γ A ε p (k + 1) ∩ B =
        (evPrefix m n γ A ε p k ∩ B) ∩ patSetA p m (n + k) A (ε k) := by
      simp only [evPrefix]
      ext U
      simp only [Set.mem_inter_iff]
      tauto
    calc ENNReal.ofReal (1 - p) ^ ((k + 1) * A.card) *
          arrayMeasure N (prefAgree p m γ ∩ B)
        = ENNReal.ofReal (1 - p) ^ A.card *
            (ENNReal.ofReal (1 - p) ^ (k * A.card) *
              arrayMeasure N (prefAgree p m γ ∩ B)) := by
          rw [← mul_assoc, ← pow_add]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (1 - p) ^ A.card *
            arrayMeasure N (evPrefix m n γ A ε p k ∩ B) := mul_le_mul' le_rfl ih
      _ ≤ arrayMeasure N (evPrefix m n γ A ε p (k + 1) ∩ B) := by
          rw [hEq]
          exact hstep

/-- The paper's prescribed zig-zag word: the selected walker `i_y` alternates `+1, -1`, every
other walker steps `-1`. -/
noncomputable def gammaWord (iy : Fin N) : ℕ → Fin N → ℤ :=
  fun u i => if i = iy then (if u % 2 = 0 then (1 : ℤ) else -1) else -1

lemma gammaWord_isUnit (iy : Fin N) (u : ℕ) (i : Fin N) :
    gammaWord iy u i = 1 ∨ gammaWord iy u i = -1 := by
  unfold gammaWord
  split_ifs <;> simp

/-- **The `Γ_y^A` trial bound.**  The probability that the group `A` performs the paper's
prescribed `2m-1`-step zig-zag attempt is at least `(1-p)^{(2m-1)|A|}` times the mass of the
piece, on any piece of the enlarged filtration. -/
theorem gamma_trial_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m n : ℕ) (hm : 1 ≤ m)
    (γ : Pref N n) {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (A : Finset (Fin N)) (iy : Fin N) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) * arrayMeasure N (prefAgree p m γ ∩ B) ≤
      arrayMeasure N (evPrefix m n γ A (gammaWord iy) p (2 * m - 1) ∩ B) :=
  evPrefix_mass_ge p hp0 hp1 m n γ A (gammaWord iy) (fun u i => gammaWord_isUnit iy u i) hB
    (2 * m - 1)


/-! ### The trial event in the paper's position form -/

/-- The position dictated by the paper's zig-zag word at offset `u`: the selected walker `i_y`
alternates between its starting site and the next site, every other walker steps down by one
each time. -/
noncomputable def wordPos (γ : Pref N n) (iy : Fin N) (u : ℕ) (i : Fin N) : ℤ :=
  if i = iy then ext γ n i + ((u % 2 : ℕ) : ℤ) else ext γ n i - (u : ℤ)

lemma wordPos_zero (γ : Pref N n) (iy : Fin N) (i : Fin N) :
    wordPos γ iy 0 i = ext γ n i := by
  rw [wordPos]
  by_cases hii : i = iy
  · simp only [hii, if_true, Nat.zero_mod, Nat.cast_zero, add_zero]
  · simp only [hii, if_false, Nat.cast_zero, sub_zero]

/-- One step of the word moves the dictated position by the prescribed jump. -/
lemma wordPos_succ (γ : Pref N n) (iy : Fin N) (u : ℕ) (i : Fin N) :
    wordPos γ iy (u + 1) i = wordPos γ iy u i + gammaWord iy u i := by
  rw [wordPos, wordPos, gammaWord]
  by_cases hii : i = iy
  · simp only [hii, if_true]
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · rw [h]
      simp only [if_true]
      omega
    · rw [h]
      simp only [if_neg (by norm_num : (¬ ((1 : ℕ) = 0)))]
      omega
  · simp only [hii, if_false]
    push_cast
    ring

/-- **Jump bookkeeping.**  A prescribed run of jumps forces the paper's positions. -/
lemma pos_eq_wordPos (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (iy : Fin N) {A : Finset (Fin N)}
    {U : Array N} (hU : U ∈ prefAgree p m γ) :
    ∀ (u k : ℕ), u ≤ k →
      (∀ v < k, ∀ i ∈ A, (trajectory p m U (n + v + 1)).pos i =
        (trajectory p m U (n + v)).pos i + gammaWord iy v i) →
      ∀ i ∈ A, (trajectory p m U (n + u)).pos i = wordPos γ iy u i := by
  intro u
  induction u with
  | zero =>
    intro k _ _ i hi
    rw [Nat.add_zero, wordPos_zero]
    exact (ext_prefOf_of_mem hU (s := n) le_rfl i).symm
  | succ u ihu =>
    intro k hle hj i hi
    have hstep := hj u (by omega) i hi
    have hprev := ihu k (by omega) hj i hi
    rw [show n + (u + 1) = n + u + 1 from rfl, hstep, hprev]
    exact (wordPos_succ γ iy u i).symm

/-- **Jump bookkeeping, converse.**  The prescribed positions force the word's jumps. -/
lemma jumps_of_pos_eq (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (iy : Fin N) {A : Finset (Fin N)}
    {U : Array N} {k : ℕ}
    (hpos : ∀ u, u ≤ k → ∀ i ∈ A, (trajectory p m U (n + u)).pos i = wordPos γ iy u i) :
    ∀ v < k, ∀ i ∈ A, (trajectory p m U (n + v + 1)).pos i =
      (trajectory p m U (n + v)).pos i + gammaWord iy v i := by
  intro v hv i hi
  have h1 := hpos (v + 1) (by omega) i hi
  have h2 := hpos v (by omega) i hi
  have h1' : (trajectory p m U (n + v + 1)).pos i = wordPos γ iy (v + 1) i := by
    rw [show n + v + 1 = n + (v + 1) from rfl]
    exact h1
  rw [h1', h2, wordPos_succ]

/-- **The trial event of the paper.**  On the piece `{path = γ}`, following the prescribed word
for `k` steps is the same as being at the dictated position at every offset `0, …, k`. -/
theorem evPrefix_eq_pos (p : ℝ) (m : ℕ) {n : ℕ} (γ : Pref N n) (iy : Fin N)
    (A : Finset (Fin N)) :
    ∀ k, evPrefix m n γ A (gammaWord iy) p k =
      prefAgree p m γ ∩ {U : Array N | ∀ u, u ≤ k → ∀ i ∈ A,
        (trajectory p m U (n + u)).pos i = wordPos γ iy u i} := by
  intro k
  induction k with
  | zero =>
    have h0 : evPrefix m n γ A (gammaWord iy) p 0 = prefAgree p m γ := rfl
    rw [h0]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨h, fun u hu i hi => ?_⟩
      have hu0 : u = 0 := Nat.le_zero.1 hu
      subst hu0
      rw [Nat.add_zero, wordPos_zero]
      exact (ext_prefOf_of_mem h (s := n) le_rfl i).symm
    · rintro ⟨h, -⟩
      exact h
  | succ k ih =>
    have h0 : evPrefix m n γ A (gammaWord iy) p (k + 1) =
        evPrefix m n γ A (gammaWord iy) p k ∩ patSetA p m (n + k) A (gammaWord iy k) := rfl
    rw [h0, ih]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hU, hpos⟩, hjump⟩
      refine ⟨hU, fun u hu i hi => ?_⟩
      rcases Nat.lt_or_ge u (k + 1) with hlt | hge
      · exact hpos u (by omega) i hi
      · have hu' : u = k + 1 := by omega
        subst hu'
        have hj := hjump i hi
        have hp := hpos k (by omega) i hi
        rw [wordPos_succ, ← hp]
        exact hj
    · rintro ⟨hU, hpos⟩
      refine ⟨⟨hU, fun u hu i hi => hpos u (by omega) i hi⟩, fun i hi => ?_⟩
      have h1 := hpos (k + 1) (by omega) i hi
      have h2 := hpos k (by omega) i hi
      have h1' : (trajectory p m U (n + k + 1)).pos i = wordPos γ iy (k + 1) i := by
        rw [show n + k + 1 = n + (k + 1) from rfl]
        exact h1
      rw [h1', h2, wordPos_succ]

/-- **The paper's `(trialp)` display, in its own event form.**  On every piece of the enlarged
filtration, the probability that the group `A` follows the paper's prescribed `2m-1`-step
zig-zag (described by the positions `y, y+1, y, y+1, …` for the selected walker and
`X_σ - u` for the others) is at least `(1-p)^{(2m-1)|A|}` times the mass of the piece. -/
theorem gamma_paper_event_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m n : ℕ) (hm : 1 ≤ m)
    (γ : Pref N n) {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (A : Finset (Fin N)) (iy : Fin N) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
        arrayMeasure N (prefAgree p m γ ∩ B) ≤
      arrayMeasure N ((prefAgree p m γ ∩ {U : Array N | ∀ u, u ≤ 2 * m - 1 → ∀ i ∈ A,
        (trajectory p m U (n + u)).pos i = wordPos γ iy u i}) ∩ B) := by
  rw [← evPrefix_eq_pos p m γ iy A (2 * m - 1)]
  exact gamma_trial_mass_ge p hp0 hp1 m n hm γ hB A iy

end Swarming.Enl


