/-
  **The stopped one-trial `Γ` law: the prescribed joint jump word after a stopping time.**

      (1-p)^{k|A|} · μ({path = γ} ∩ B) ≤ μ(Γ-word of length k starting at n ∩ B).

  What that leaves open is the *stopped* form the paper actually needs: the `2m-1` steps are
  taken after a random time `σ`, not after a fixed `n`.  This file closes exactly that part:

  * `wordRun p m n A iy k` is the paper's trial event in absolute-position form
    (walker `iy` alternates `y, y+1, y, …`, every `i ∈ A` moves down one site per step);
  * `wordRun_eq_iUnion_evPrefix` identifies it with the union of the verified `evPrefix`
    events over all pieces at level `n`, so the verified multi-step estimate applies piecewise;
  * `wordRun_mass_ge` upgrades the piecewise estimate to an *arbitrary* event
    `G ∈ enlMeas p m n` — i.e. to a genuine conditional law given the whole enlarged history,
    with no independence assumption;
  * `stopped_wordRun_mass_ge` sums the estimate over the level at which a stopping time `τ`
    of the enlarged filtration fires, giving an unconditional lower bound
    `(1-p)^{k|A|} ≤ μ(⋃_n {τ = n} ∩ wordRun n)` with **no** boundedness or structural
    hypothesis on `τ` beyond `{τ = n} ∈ enlMeas p m n`.

  Honest residue (see the closing comment block): the paper's `σ_y^A` must still be shown to be
  a stopping time of `enlMeas` *here*, and the `(2m-1)`-step word must still be matched against
  the record/level structure of the proof of Proposition `local`.  Neither is claimed below.

  No proof hole, no custom axiom: everything is derived from `GammaBase` (hence from
  `enl_fresh_law_piece`, the paper's §2.1 conditional law on the actual i.i.d. uniform array).
-/
import Swarm.GammaBase

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The trial word in absolute position form -/

/-- The paper's prescribed zig-zag word, written in absolute positions: during the `k` steps
starting at time `n`, the selected walker `iy` alternates between its site at time `n` and the
next one (`+ (u % 2)`), and every walker of `A` moves down one site at every step (`- u`). -/
noncomputable def wordRun (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) :
    Set (Array N) :=
  {U | ∀ u, u ≤ k → ∀ i ∈ A,
    (trajectory p m U (n + u)).pos i = (trajectory p m U n).pos i +
      (if i = iy then ((u % 2 : ℕ) : ℤ) else -((u : ℕ) : ℤ))}

/-- `wordPos` is the starting site plus the word's displacement. -/
lemma wordPos_eq_offset (γ : Pref N n) (iy : Fin N) (u : ℕ) (i : Fin N) :
    wordPos γ iy u i =
      ext γ n i + (if i = iy then ((u % 2 : ℕ) : ℤ) else -((u : ℕ) : ℤ)) := by
  rw [wordPos]
  by_cases h : i = iy
  · simp only [h, if_true]
  · simp only [h, if_false]
    ring

/-- The verified `evPrefix` trial event implies the absolute-position word event. -/
lemma evPrefix_subset_wordRun (p : ℝ) (m n : ℕ) (γ : Pref N n) (A : Finset (Fin N))
    (iy : Fin N) (k : ℕ) :
    evPrefix m n γ A (gammaWord iy) p k ⊆ wordRun p m n A iy k := by
  rw [evPrefix_eq_pos p m γ iy A k]
  rintro U ⟨hpref, hpos⟩ u hu i hi
  have h1 : wordPos γ iy u i =
      (trajectory p m U n).pos i +
        (if i = iy then ((u % 2 : ℕ) : ℤ) else -((u : ℕ) : ℤ)) := by
    rw [wordPos_eq_offset, ext_prefOf_of_mem hpref (s := n) le_rfl i]
  rw [← h1]
  exact hpos u hu i hi

/-- Conversely, the absolute-position word event is covered by the `evPrefix` event of the
piece the path is actually on. -/
lemma wordRun_subset_iUnion (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) :
    wordRun p m n A iy k ⊆ ⋃ γ : Pref N n, evPrefix m n γ A (gammaWord iy) p k := by
  intro U hU
  refine Set.mem_iUnion.2 ⟨prefOf p m n U, ?_⟩
  rw [evPrefix_eq_pos p m (prefOf p m n U) iy A k]
  refine ⟨prefAgree_prefOf U, fun u hu i hi => ?_⟩
  have h1 : (trajectory p m U n).pos i +
      (if i = iy then ((u % 2 : ℕ) : ℤ) else -((u : ℕ) : ℤ)) = wordPos (prefOf p m n U) iy u i := by
    rw [wordPos_eq_offset,
      ext_prefOf_of_mem (prefAgree_prefOf (p := p) (m := m) (n := n) U) (s := n) le_rfl i]
  rw [← h1]
  exact hU u hu i hi

/-- The two forms of the trial event agree: on each piece the absolute-position word is the
verified `evPrefix` event, and the union over pieces is the absolute-position word globaly. -/
theorem wordRun_eq_iUnion_evPrefix (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (iy : Fin N)
    (k : ℕ) :
    wordRun p m n A iy k = ⋃ γ : Pref N n, evPrefix m n γ A (gammaWord iy) p k :=
  Set.Subset.antisymm (wordRun_subset_iUnion p m n A iy k)
    (Set.iUnion_subset fun γ => evPrefix_subset_wordRun p m n γ A iy k)

/-! ### Measurability of the trial word -/

lemma wordRun_zero (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (iy : Fin N) :
    wordRun p m n A iy 0 = Set.univ := by
  ext U
  simp only [wordRun, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro u hu i _
  have hu0 : u = 0 := Nat.le_zero.1 hu
  subst hu0
  simp

lemma wordRun_succ (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) :
    wordRun p m n A iy (k + 1) = wordRun p m n A iy k ∩
      ⋂ i : {i : Fin N // i ∈ A}, {U : Array N |
        (trajectory p m U (n + (k + 1))).pos i.1 = (trajectory p m U n).pos i.1 +
          (if i.1 = iy then (((k + 1) % 2 : ℕ) : ℤ) else -(((k + 1) : ℕ) : ℤ))} := by
  ext U
  simp only [wordRun, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    exact ⟨fun u hu => h u (by omega), fun i => h (k + 1) le_rfl i.1 i.2⟩
  · rintro ⟨h1, h2⟩ u hu i hi
    rcases Nat.lt_or_eq_of_le hu with hlt | heq
    · exact h1 u (by omega) i hi
    · subst heq
      exact h2 ⟨i, hi⟩

/-- The trial word of length `k` is a measurable event of the ambient product space. -/
theorem measurableSet_wordRun (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) :
    MeasurableSet (wordRun p m n A iy k) := by
  induction k with
  | zero => rw [wordRun_zero]; exact MeasurableSet.univ
  | succ k ih =>
    rw [wordRun_succ]
    refine MeasurableSet.inter ih (MeasurableSet.iInter fun i => ?_)
    have hf : Measurable fun U : Array N => (trajectory p m U (n + (k + 1))).pos i.1 :=
      (Swarming.Fair.measurable_trajectory p m (n + (k + 1))).1 i.1
    have hg : Measurable fun U : Array N => (trajectory p m U n).pos i.1 +
        (if i.1 = iy then (((k + 1) % 2 : ℕ) : ℤ) else -(((k + 1) : ℕ) : ℤ)) :=
      ((Swarming.Fair.measurable_trajectory p m n).1 i.1).add measurable_const
    exact measurableSet_eq_fun hf hg

/-! ### The trial word over an arbitrary enlarged-filtration event -/

/-- **The trial word from an arbitrary enlarged history.**  For every event `G` of the enlarged
filtration `enlMeas p m n` and every prescribed joint `k`-step word of the group `A`, the mass of
the word is at least `(1-p)^{k|A|}` times the mass of `G` — a genuine conditional law given the
whole enlarged history, with no independence assumption. -/
theorem wordRun_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m n : ℕ)
    (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[enlMeas p m n] G) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ wordRun p m n A iy k) := by
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
  have hpart : G ∩ wordRun p m n A iy k =
      ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ ∩ wordRun p m n A iy k) := by
    rw [hGunion, Set.iUnion_inter]
  have hdisjB : Pairwise (Function.onFun Disjoint (fun γ : Pref N n => prefAgree p m γ ∩ B γ)) := by
    intro γ γ' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hmeasB : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) := by
    intro γ
    have hB' : MeasurableSet (B γ) := by
      obtain ⟨C, hC, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 (hB γ)
      rw [← hBeq]
      exact hC.preimage (measurable_pi_lambda _ fun c => measurable_pi_apply _)
    exact (measurableSet_prefAgree_ambient p m γ).inter hB'
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun γ : Pref N n => prefAgree p m γ ∩ B γ ∩ wordRun p m n A iy k)) := by
    intro γ γ' hne
    exact (hdisjB hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ γ : Pref N n,
      MeasurableSet (prefAgree p m γ ∩ B γ ∩ wordRun p m n A iy k) :=
    fun γ => (hmeasB γ).inter (measurableSet_wordRun p m n A iy k)
  have hGmass : arrayMeasure N G =
      ∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    rw [hGunion]
    exact measure_iUnion hdisjB hmeasB
  have hstep : ∀ γ : Pref N n, ENNReal.ofReal (1 - p) ^ (k * A.card) *
        arrayMeasure N (prefAgree p m γ ∩ B γ) ≤
      arrayMeasure N (prefAgree p m γ ∩ B γ ∩ wordRun p m n A iy k) := by
    intro γ
    refine le_trans (evPrefix_mass_ge p hp0 hp1 m n γ A (gammaWord iy)
      (fun u i => gammaWord_isUnit iy u i) (hB γ) k) (measure_mono ?_)
    intro U hU
    exact ⟨⟨evPrefix_subset_prefAgree p m n γ A (gammaWord iy) k hU.1, hU.2⟩,
      evPrefix_subset_wordRun p m n γ A iy k hU.1⟩
  calc ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N G
      = ENNReal.ofReal (1 - p) ^ (k * A.card) *
          (∑' γ : Pref N n, arrayMeasure N (prefAgree p m γ ∩ B γ)) := by rw [hGmass]
    _ = ∑' γ : Pref N n, ENNReal.ofReal (1 - p) ^ (k * A.card) *
          arrayMeasure N (prefAgree p m γ ∩ B γ) := by rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' γ : Pref N n,
          arrayMeasure N (prefAgree p m γ ∩ B γ ∩ wordRun p m n A iy k) :=
        ENNReal.tsum_le_tsum hstep
    _ = arrayMeasure N (G ∩ wordRun p m n A iy k) := by
        rw [hpart, measure_iUnion hdisj hmeas]

/-- The same bound written as a conditional probability: given any enlarged-history event `G` of
positive mass, the conditional probability of the prescribed word is at least
`(1-p)^{k|A|}`. -/
theorem wordRun_condProb_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m n : ℕ)
    (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[enlMeas p m n] G) (hG0 : arrayMeasure N G ≠ 0) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) ≤
      arrayMeasure N (G ∩ wordRun p m n A iy k) / arrayMeasure N G := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hG0) (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top
    (by rw [← measure_univ (μ := arrayMeasure N)]; exact measure_mono (Set.subset_univ G))))]
  exact wordRun_mass_ge p hp0 hp1 m n A iy k hG

/-! ### The stopping-time form -/

/-- The trial word taken after the stopping time `τ`: at the level `n` where `τ` fires, the
group `A` follows the paper's prescribed word for the next `k` steps. -/
noncomputable def stopWordAll (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (iy : Fin N) (k : ℕ)
    (τ : Array N → ℕ) : Set (Array N) :=
  ⋃ n : ℕ, ({U : Array N | τ U = n} ∩ wordRun p m n A iy k)

/-- The word after the stop, conditioned on `τ` firing at level `n` together with an
enlarged-history event `H` at that level. -/
theorem wordRun_after_stop_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) (τ : Array N → ℕ)
    (hτ : ∀ n, MeasurableSet[enlMeas p m n] {U : Array N | τ U = n}) (n : ℕ)
    {H : Set (Array N)} (hH : MeasurableSet[enlMeas p m n] H) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) *
        arrayMeasure N (H ∩ {U : Array N | τ U = n}) ≤
      arrayMeasure N (H ∩ {U : Array N | τ U = n} ∩ wordRun p m n A iy k) :=
  wordRun_mass_ge p hp0 hp1 m n A iy k (hH.inter (hτ n))

/-- **The stopped trial law.**  If `τ` is a stopping time of the enlarged filtration (only its
level-wise measurability `{τ = n} ∈ enlMeas p m n` is used) and `A` is any subgroup of walkers,
then with probability at least `(1-p)^{k|A|}` the whole group `A` follows the paper's prescribed
zig-zag word during the `k` steps starting at `τ`.  No boundedness, independence or product
structure is assumed. -/
theorem stopped_wordRun_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) (τ : Array N → ℕ)
    (hτ : ∀ n, MeasurableSet[enlMeas p m n] {U : Array N | τ U = n}) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) ≤
      arrayMeasure N (stopWordAll p m A iy k τ) := by
  classical
  have hlev : ∀ n : ℕ, MeasurableSet {U : Array N | τ U = n} :=
    fun n => enlMeas_le p m n _ (hτ n)
  have hdisj : Pairwise (Function.onFun Disjoint (fun n : ℕ => {U : Array N | τ U = n})) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro U h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact hab (h1.symm.trans h2)
  have huniv : (Set.univ : Set (Array N)) = ⋃ n : ℕ, {U : Array N | τ U = n} := by
    ext U
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun _ => ⟨τ U, rfl⟩, fun _ => trivial⟩
  have hμuniv : arrayMeasure N (Set.univ) =
      ∑' n : ℕ, arrayMeasure N {U : Array N | τ U = n} := by
    rw [huniv, measure_iUnion hdisj hlev]
  have hdisjW : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => {U : Array N | τ U = n} ∩ wordRun p m n A iy k)) := by
    intro a b hab
    exact (hdisj hab).mono Set.inter_subset_left Set.inter_subset_left
  have hmeasW : ∀ n : ℕ,
      MeasurableSet ({U : Array N | τ U = n} ∩ wordRun p m n A iy k) :=
    fun n => (hlev n).inter (measurableSet_wordRun p m n A iy k)
  calc ENNReal.ofReal (1 - p) ^ (k * A.card)
      = ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N (Set.univ) := by
        rw [measure_univ, mul_one]
    _ = ENNReal.ofReal (1 - p) ^ (k * A.card) *
          ∑' n : ℕ, arrayMeasure N {U : Array N | τ U = n} := by rw [hμuniv]
    _ = ∑' n : ℕ, ENNReal.ofReal (1 - p) ^ (k * A.card) *
          arrayMeasure N {U : Array N | τ U = n} := by rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' n : ℕ, arrayMeasure N ({U : Array N | τ U = n} ∩ wordRun p m n A iy k) :=
        ENNReal.tsum_le_tsum fun n => wordRun_mass_ge p hp0 hp1 m n A iy k (hτ n)
    _ = arrayMeasure N (stopWordAll p m A iy k τ) := by
        rw [stopWordAll, measure_iUnion hdisjW hmeasW]

/-- The paper's `(trialp)` display in stopped form: for the paper's `2m-1`-step zig-zag word
(`+1, -1, …` for the selected walker `iy`, `-1` for every other member of `A`), the probability
of following it for `2m-1` steps after any stopping time of the enlarged filtration is at least
`(1-p)^{(2m-1)|A|}`. -/
theorem stopped_gamma_paper_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 1 ≤ m)
    (A : Finset (Fin N)) (iy : Fin N) (τ : Array N → ℕ)
    (hτ : ∀ n, MeasurableSet[enlMeas p m n] {U : Array N | τ U = n}) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) ≤
      arrayMeasure N (stopWordAll p m A iy (2 * m - 1) τ) :=
  stopped_wordRun_mass_ge p hp0 hp1 m A iy (2 * m - 1) τ hτ

/-- Sanity instance: for the constant stopping time `τ ≡ n₀` the stopped bound is the fixed-level
bound, so the stopping-time hypothesis is satisfiable and the stopped theorem is a genuine
generalisation of the verified piecewise statement (not a weakening of it). -/
theorem stopped_gamma_const (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 1 ≤ m)
    (n₀ : ℕ) (A : Finset (Fin N)) (iy : Fin N) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) ≤
      arrayMeasure N (stopWordAll p m A iy (2 * m - 1) (fun _ => n₀)) := by
  classical
  refine stopped_gamma_paper_ge p hp0 hp1 m hm A iy (fun _ => n₀) ?_
  intro n
  by_cases h : n = n₀
  · subst h
    have : {U : Array N | (fun _ : Array N => n) U = n} = Set.univ := by
      ext U; simp
    rw [this]
    exact @MeasurableSet.univ (Array N) (enlMeas p m n)
  · have hne : {U : Array N | (fun _ : Array N => n₀) U = n} = ∅ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h h'.symm
    rw [hne]
    exact @MeasurableSet.empty (Array N) (enlMeas p m n)

/-! ### Interface: stopping times of `enlFilt` give the level-wise hypothesis -/

lemma enlMeas_mono' (p : ℝ) (m : ℕ) {a b : ℕ} (h : a ≤ b) :
    enlMeas (N := N) p m a ≤ enlMeas (N := N) p m b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (enlMeas_mono (N := N) p m)

/-- A stopping time of the enlarged filtration `enlFilt = (enlMeas p m n)_n`, with the natural
coercion of an `ℕ`-valued `τ` into `WithTop ℕ`, satisfies the level-wise measurability
hypothesis `{τ = n} ∈ enlMeas p m n` used above.  (This is the only interface condition my
stopped law needs; it is exactly `IsStoppingTime.measurableSet_eq_of_countable` transported along
`enlFilt_apply`.) -/
theorem isStoppingTime_levels (p : ℝ) (m : ℕ) {τ : Array N → ℕ}
    (hτ : IsStoppingTime (enlFilt (N := N) p m) (fun U => (τ U : WithTop ℕ))) :
    ∀ n : ℕ, MeasurableSet[enlMeas p m n] {U : Array N | τ U = n} := by
  intro n
  have h := hτ.measurableSet_eq_of_countable n
  rw [enlFilt_apply] at h
  have hset : {U : Array N | τ U = n} =
      {U : Array N | (fun U => (τ U : WithTop ℕ)) U = (n : WithTop ℕ)} := by
    ext U
    exact WithTop.coe_inj.symm
  rw [hset]
  exact h

/-- **The stopped trial law, in the shape the rest of the development uses.**  For any stopping
time `τ` of the enlarged filtration `enlFilt` (an `Array N → ℕ` function, coerced to
`WithTop ℕ`), the group `A` follows the paper's prescribed `k`-step zig-zag word after `τ` with
probability at least `(1-p)^{k|A|}`. -/
theorem stopped_wordRun_mass_ge_isStoppingTime (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (iy : Fin N) (k : ℕ) (τ : Array N → ℕ)
    (hτ : IsStoppingTime (enlFilt (N := N) p m) (fun U => (τ U : WithTop ℕ))) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) ≤
      arrayMeasure N (stopWordAll p m A iy k τ) :=
  stopped_wordRun_mass_ge p hp0 hp1 m A iy k τ (isStoppingTime_levels p m hτ)

end Swarming.Enl


/-! ### What is and is not discharged here

Discharged (compiled above, axioms `propext, Classical.choice, Quot.sound` only):

* `wordRun_mass_ge` — the `(1-p)^{k|A|}` local jump law holds conditionally on an *arbitrary*
  event of the enlarged filtration `enlMeas p m n`, not merely on a piece `{path = γ}`.
* `wordRun_after_stop_mass_ge` — the same, conditioned on the stopping time firing at a
  prescribed level `n` and on any further enlarged-history event at that level.
* `stopped_wordRun_mass_ge`, `stopped_gamma_paper_ge` — the unconditional lower bound after the
  stop, valid for every `ℕ`-valued stopping time of `enlMeas`, with no boundedness or
  independence hypothesis.
* `isStoppingTime_levels`, `stopped_wordRun_mass_ge_isStoppingTime` — the interface that turns a
  `MeasureTheory.IsStoppingTime (enlFilt p m) τ` (the form every stopping time in this repository
  is stated in) into the level-wise hypothesis, and hence into the stopped bound.

Not discharged, hence *not* claimed:

* that the paper's `σ_y^A` itself is a stopping time of `enlFilt` (the file takes the
  `IsStoppingTime`/level-wise measurability of `τ` as a hypothesis; `enl_pos_measurable`,
  `enl_ell_measurable` and `isStoppingTime_trajExit_enlFilt` in `EnlFilt` are the ingredients,
  but the record/`σ_y^A` construction is not built here);
* that the word event above is the paper's full `Γ_y^A` event with its `2m-1`-step level
  bookkeeping and its disjointness in `y`; the file only supplies the stopped jump law.

All of the above are `ℕ`-level statements: `τ : Array N → ℕ` is total, so no `WithTop` residue is
needed.  The corresponding unbounded-count form over `2m` trials is deliberately left out.
-/
