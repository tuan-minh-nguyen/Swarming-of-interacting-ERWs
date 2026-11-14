/-
  **The actual Gamma residue-class count tail** (paper's `(locsum)` ingredients).

  This file instantiates the abstract stopped-conditional trial tail (`TailChain.lean`)
  on the actual i.i.d.-uniform array `Swarming.Trajectory.trajectory`, with

  * `σ_i = σ_{y_i}^A` the first passage of the group record to the level `y_i = y0 + 2 m i`
    (`Swarming.Enl.sigmaA`, a genuine `enlFilt`-stopping time, `GammaSigma.lean`);
  * `Γ_i = Γ_{y_i}^A` the paper's `2m-1`-step trial at that passage
    (`Swarming.Enl.GammaSet`), whose stopped conditional mass bound `(trialp)` is
    `Swarming.Enl.GammaSet_cond_mass`;
  * `c = (1-p)^{(2m-1)|A|}`.

  The genuinely new geometric input here is `measurableSet_sigmaA_lvl_inter_GammaSet`:
  the trial `Γ_i` is already decided at the level of the *next* record time `σ_{i+1}`,
  and the record times of one residue class are monotone, so
  `{σ_k = n} ∩ Γ_i` is `enlFilt n`-measurable for every `i < k`.  This is what makes
  `Γ_i` an admissible weight for the conditional-mass bound at `σ_k`, i.e. the paper's
  "the times `σ_y + 2m - 1` are distinct".
-/
import Swarm.GammaSigma
import Swarm.TailChain

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Enl

variable {N : ℕ}

/-! ## The residue-class levels -/

/-- The levels of one residue class: `y_i = y0 + 2 m i`. -/
def lvl (y0 : ℤ) (m i : ℕ) : ℤ := y0 + (i : ℤ) * ((2 * m : ℕ) : ℤ)

lemma lvl_zero (y0 : ℤ) (m : ℕ) : lvl y0 m 0 = y0 := by simp [lvl]

lemma lvl_succ (y0 : ℤ) (m : ℕ) (i : ℕ) :
    lvl y0 m (i + 1) = lvl y0 m i + ((2 * m : ℕ) : ℤ) := by
  simp only [lvl]
  push_cast
  ring

lemma lvl_mono (y0 : ℤ) (m : ℕ) : Monotone (lvl y0 m) := by
  intro a b hab
  simp only [lvl]
  have hab' : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  have h2m : (0 : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by positivity
  nlinarith

lemma lvl_nonneg {y0 : ℤ} (hy0 : 0 ≤ y0) {m i : ℕ} : 0 ≤ lvl y0 m i := by
  simp only [lvl]
  have : (0 : ℤ) ≤ (i : ℤ) * ((2 * m : ℕ) : ℤ) := by positivity
  linarith

/-! ## Measurability of a trial at the next record time -/

/-- **`Γ_i` is measurable at every later record time of the same residue class.**
For `i < k`, the set `{σ_k = n} ∩ Γ_i` is `enlFilt p m n`-measurable: the trial `Γ_i` is
decided by time `σ_{i+1} - 1 = σ_i + 2m - 1`, and on `{σ_k = n}` the earlier record time
`σ_{i+1}` is at most `n`. -/
theorem measurableSet_sigmaA_lvl_inter_GammaSet {p : ℝ} {m : ℕ} {A : Finset (Fin N)}
    {hA : A.Nonempty} {y0 : ℤ} (hy0 : 0 ≤ y0) {i k n : ℕ} (hik : i < k) :
    MeasurableSet[enlFilt p m n]
      ({U : Array N | sigmaA p m U hA (lvl y0 m k) = (n : WithTop ℕ)} ∩
        GammaSet p m hA (lvl y0 m i)) := by
  classical
  set B : Set (Array N) := {U : Array N | sigmaA p m U hA (lvl y0 m k) = (n : WithTop ℕ)}
    with hB
  set G : Set (Array N) := GammaSet p m hA (lvl y0 m i) with hG
  have hEq : B ∩ G = ⋃ j ∈ Finset.range (n + 1),
      (({U : Array N | sigmaA p m U hA (lvl y0 m (i + 1)) = (j : WithTop ℕ)} ∩ G) ∩ B) := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨hU1, hU2⟩
      have hARk : ARMax p m U hA (lvl y0 m k) n := sigmaA_eq_coe_iff.mp hU1
      have hRk : runMaxA p m U hA n = lvl y0 m k := hARk.eq (lvl_nonneg hy0)
      have hle : sigmaA p m U hA (lvl y0 m (i + 1)) ≤ (n : WithTop ℕ) := by
        refine sigmaA_le_of_record_le ⟨n, le_rfl, ?_⟩
        rw [hRk]
        exact lvl_mono y0 m (Nat.succ_le_of_lt hik)
      obtain ⟨j, hjle, hARj⟩ := sigmaA_le_iff.mp hle
      exact ⟨j, ⟨Nat.lt_succ_of_le hjle, ⟨sigmaA_eq_coe_iff.mpr hARj, hU2⟩, hU1⟩⟩
    · rintro ⟨j, -, ⟨-, hG'⟩, hB'⟩
      exact ⟨hB', hG'⟩
  rw [hEq]
  refine Finset.measurableSet_biUnion _ fun j hj => ?_
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : MeasurableSet[enlFilt p m n]
      ({U : Array N | sigmaA p m U hA (lvl y0 m (i + 1)) = (j : WithTop ℕ)} ∩ G) := by
    rw [hG, lvl_succ]
    exact (enlFilt (N := N) p m).mono hjle _ <|
      measurableSet_GammaSet_next p m j A hA (lvl y0 m i) (lvl_nonneg hy0)
  have h2 : MeasurableSet[enlFilt p m n] B := by
    rw [hB]
    have heq : {U : Array N | sigmaA p m U hA (lvl y0 m k) = (n : WithTop ℕ)}
        = {U : Array N | ARMax p m U hA (lvl y0 m k) n} := by
      ext U; exact sigmaA_eq_coe_iff
    rw [heq]
    exact measurableSet_ARMax p m n A hA (lvl y0 m k)
  exact h1.inter h2

/-! ## Ambient measurability of the trial -/

theorem measurableSet_GammaSet {p : ℝ} (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) : MeasurableSet (GammaSet p m hA y) := by
  classical
  simp only [GammaSet]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun iy => ?_
  refine MeasurableSet.iUnion fun hiy => ?_
  have hbase : MeasurableSet[enlFilt p m (n + (2 * m - 1))]
      ({U : Array N | ARMax p m U hA y n} ∩ {U : Array N | IsLeader p m U A y n iy}) :=
    (enlFilt (N := N) p m).mono (by omega) _ <|
      (measurableSet_ARMax p m n A hA y).inter (measurableSet_leader p m n A y iy)
  exact enlMeas_le p m (n + (2 * m - 1)) _ (hbase.inter (measurableSet_wordRun_enl p m n A iy (2 * m - 1)))

/-! ## The instance of the abstract tail -/

/-- **The actual count tail on one residue class of the group record.**
For the i.i.d. uniform array, the levels `y_i = y0 + 2 m i`, any `0 < ρ ≤ 1` and any `K, j`,

`P (# {i < K : Γ_{y_i}} ≤ j) ≤ P(σ_{y_0} = ⊤) + ρ^{-j} (1 - c + c ρ)^K + P(σ_{y_K} = ⊤)`,

with `c = (1-p)^{(2m-1)|A|}`.  The two exceptional terms are exactly the *record-window*
exceptions: the class never starts, or the record stops before the `K`-th trial.  No freshness,
independence or terminal-window hypothesis is used. -/
theorem gamma_count_tail (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y0 : ℤ} (hy0 : 0 ≤ y0)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (K j : ℕ) :
    arrayMeasure N {U : Array N | ((Finset.range K).filter
        (fun i => U ∈ GammaSet p m hA (lvl y0 m i))).card ≤ j}
      ≤ arrayMeasure N {U : Array N | sigmaA p m U hA (lvl y0 m 0) = ⊤}
        + ENNReal.ofReal ((ρ ^ j)⁻¹ *
            (1 - (1 - p) ^ ((2 * m - 1) * A.card)
              + (1 - p) ^ ((2 * m - 1) * A.card) * ρ) ^ K)
        + arrayMeasure N {U : Array N | sigmaA p m U hA (lvl y0 m K) = ⊤} := by
  classical
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcl : (1 - p) ^ ((2 * m - 1) * A.card) ≤ 1 :=
    pow_le_one₀ h1mp (by linarith)
  have : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine TrialTail.count_tail (μ := arrayMeasure N) (ℱ := enlFilt p m)
    (σ := fun i U => sigmaA p m U hA (lvl y0 m i))
    (Γ := fun i => GammaSet p m hA (lvl y0 m i))
    (c := (1 - p) ^ ((2 * m - 1) * A.card)) (ρ := ρ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K j
  · exact fun n => (enlFilt (N := N) p m).le n
  · intro i n
    have heq : {U : Array N | sigmaA p m U hA (lvl y0 m i) = (n : WithTop ℕ)}
        = {U : Array N | ARMax p m U hA (lvl y0 m i) n} := by
      ext U; exact sigmaA_eq_coe_iff
    rw [heq]
    exact measurableSet_ARMax p m n A hA (lvl y0 m i)
  · exact fun i k n hik => measurableSet_sigmaA_lvl_inter_GammaSet hy0 hik
  · -- the stopped conditional mass bound `(trialp)`
    intro i n H hH hsub
    have h := GammaSet_cond_mass (N := N) p hp0 hp1 m A hA (lvl_nonneg (m := m) (i := i) hy0) n
      (H := H) hH
    rw [Set.inter_eq_left.mpr hsub, ← ENNReal.ofReal_pow h1mp] at h
    exact h
  · exact fun i => measurableSet_GammaSet m A hA (lvl y0 m i)
  · exact pow_nonneg h1mp _
  · exact hcl
  · exact hρ0
  · exact hρ1
  · -- nesting of record times
    intro k U hU
    have hne : sigmaA p m U hA (lvl y0 m (k + 1)) ≠ ⊤ := hU
    rw [lvl_succ] at hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [eq_comm] at hn
    obtain ⟨j, -, hj⟩ := sigmaA_nesting_two_m p m (lvl_nonneg (m := m) (i := k) hy0) hn
    show sigmaA p m U hA (lvl y0 m k) ≠ ⊤
    rw [hj]
    exact WithTop.coe_ne_top
  · -- `Γ_i ⊆ {σ_i ≠ ⊤}`
    intro i U hU
    simp only [GammaSet, Set.mem_iUnion, Set.mem_setOf_eq] at hU
    obtain ⟨n, iy, -, ⟨⟨hAR, -⟩, -⟩⟩ := hU
    show sigmaA p m U hA (lvl y0 m i) ≠ ⊤
    rw [sigmaA_eq_coe_iff.mpr hAR]
    exact WithTop.coe_ne_top

end Swarming.Enl
