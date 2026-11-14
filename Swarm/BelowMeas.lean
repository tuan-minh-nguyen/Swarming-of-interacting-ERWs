/-
  **Direction B (m2): the environment values below the running record are `enlFilt`-measurable.**

  The measurability inputs of `PullOut.condExp_drift_of_adapted` at the sites *below* the record,
  in the genuine enlarged-filtration form (not the record-enlarged `enlRecMeas` of `RecEnv`):
  for `x : ℕ`,

      Measurable[enlFilt p m n] (fun U => if (x : ℤ) < runMax p m U j n then h_j(x) else 0),

  i.e. `h_j(x)` *restricted* to the event that `x` lies strictly below the running record of
  walker `j`.

  Contents:

  * `measurableSet_enl_of_piecewise` — a set which on every path piece is empty or the whole piece
    is `enlMeas p m n`-measurable;
  * `measurableSet_runMax_eq`, `measurableSet_lt_runMax` — `{M_n^j = y}` and `{x < M_n^j}` for a
    deterministic site; the record is path-determined (`RecEnv.runMax_eq_recVal`);
  * `measurableSet_below_mark` — **the marked event at a site strictly below the record is
    `enlFilt`-measurable.**  On each piece the revelation gate `m <= L_n^j(x)` either passes — and
    then the mark is the cylinder set of `EnlReveal.measurableSet_cylAt_mark` over
    `prefRead n γ` — or fails, and then `SeedMeas.gate_of_siteMark_of_lt_recVal` forbids *every*
    mark at that site.  This is the ground fact: a mark at a site below the record forces the
    gate, hence was read; a failing gate forbids a mark;
  * `measurable_below_hof` — the whole value `h_j(x)` restricted to `{x < M_n^j}`, by induction on
    `x` over the mark recursion `hof_succ = hstep p (ω (x+1)) (hof x)`;
  * `measurable_indicator_hof_of_below` — for `A ∈ F_n` with `A ⊆ {x < M_n^j}`, the restricted
    function `A.indicator (h_j(x))` is `F_n`-measurable.  This is the form consumed by the
    one-step drift on the interior region.

  No probability enters, and no two arrays with the same position prefix are ever assumed to agree
  on their revealed values: every step goes through an explicit cylinder set or the gate.
-/
import Swarm.PiMeas
import Swarm.EnlProjection

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmCross

variable {N : ℕ}

/-! ### Bounds on the position -/

/-- Positions stay inside the time horizon: `-(n : ℤ) <= X_n^i <= n`. -/
theorem pos_bounds {p : ℝ} {m : ℕ} (U : Array N) (n : ℕ) (i : Fin N) :
    -((n : ℤ)) ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ (n : ℤ) := by
  induction n with
  | zero =>
      have h0 : (trajectory p m U 0).pos i = 0 := rfl
      rw [h0]; simp
  | succ k ih =>
      rcases StepCross.pos_succ_eq_or p m U k i with h | h
      · rw [h]; push_cast; constructor <;> omega
      · rw [h]; push_cast; constructor <;> omega

lemma runMax_eq_recVal_of_mem {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (j : Fin N) : runMax p m U j n = recVal j γ := by
  rw [runMax_eq_recVal, recVal_prefOf_of_mem hU j]

/-- The actual `siteMarks` entry is the Boolean mark at the same site. -/
lemma siteMarks_eq_true {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {x : ℕ}
    (h : SiteMark p m U j (x : ℤ)) : SwarmLogRatio.siteMarks p m U j x = true := by
  simp [SwarmLogRatio.siteMarks, h]

lemma siteMarks_eq_false {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {x : ℕ}
    (h : ¬ SiteMark p m U j (x : ℤ)) : SwarmLogRatio.siteMarks p m U j x = false := by
  simp [SwarmLogRatio.siteMarks, h]

/-! ### Path-determined sets are measurable for the enlarged filtration -/

/-- A set which, on every path piece, is either empty or the whole piece is measurable for the
enlarged σ-algebra. -/
theorem measurableSet_enl_of_piecewise {p : ℝ} {m n : ℕ} {G : Set (Array N)}
    (h : ∀ γ : Pref N n, prefAgree p m γ ∩ G = ∅ ∨ prefAgree p m γ ∩ G = prefAgree p m γ) :
    MeasurableSet[enlMeas p m n] G := by
  intro γ
  rcases h γ with h | h
  · exact ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, by rw [h, Set.inter_empty]⟩
  · exact ⟨Set.univ, MeasurableSet.univ, by rw [h, Set.inter_univ]⟩

/-- **The running record takes `enlFilt`-measurable values.** -/
theorem measurableSet_runMax_eq (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (y : ℤ) :
    MeasurableSet[enlFilt p m n] {U : Array N | runMax p m U j n = y} := by
  refine measurableSet_enl_of_piecewise (fun γ => ?_)
  by_cases hy : recVal j γ = y
  · right
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    refine ⟨hU, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [runMax_eq_recVal_of_mem hU j, hy]
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hUy⟩
    simp only [Set.mem_ofPred_eq] at hUy
    exact hy (by rw [runMax_eq_recVal_of_mem hU j] at hUy; exact hUy)

/-- `{x < M_n^j}` for a deterministic natural site `x` is `enlFilt`-measurable. -/
theorem measurableSet_lt_runMax (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (x : ℕ) :
    MeasurableSet[enlFilt p m n] {U : Array N | (x : ℤ) < runMax p m U j n} := by
  refine measurableSet_enl_of_piecewise (fun γ => ?_)
  by_cases hlt : (x : ℤ) < recVal j γ
  · right
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    refine ⟨hU, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [runMax_eq_recVal_of_mem hU j]
    exact hlt
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hlt'⟩
    simp only [Set.mem_ofPred_eq] at hlt'
    exact hlt (by rw [runMax_eq_recVal_of_mem hU j] at hlt'; exact hlt')

/-! ### The marked event below the record -/

/-- **A mark at a site strictly below the running record is `enlFilt`-measurable.**  On a piece
either the revelation gate passes, and then the mark is the cylinder set of
`EnlReveal.measurableSet_cylAt_mark` over `prefRead n γ`, or the gate fails, and then
`SeedMeas.gate_of_siteMark_of_lt_recVal` says that no array on the piece is marked there. -/
theorem measurableSet_below_mark {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) (x : ℕ) :
    MeasurableSet[enlFilt p m n]
      {U : Array N | (x : ℤ) < runMax p m U j n ∧ SiteMark p m U j (x : ℤ)} := by
  classical
  intro γ
  by_cases hne : ∃ U : Array N, U ∈ prefAgree p m γ
  · obtain ⟨U₀, hU₀⟩ := hne
    by_cases hlt : (x : ℤ) < recVal j γ
    · by_cases hg : m ≤ localTime (fun t => ext γ t j) n (x : ℤ)
      · have hgate : m ≤ (trajectory p m U₀ n).ell j (x : ℤ) := by
          rw [ell_eq_localTime_of_prefAgree p m n hU₀ le_rfl j (x : ℤ)]
          exact hg
        have hcyl := measurableSet_cylAt_mark p m n le_rfl hU₀ j (x : ℤ) hgate
        refine ⟨{U : Array N | SiteMark p m U j (x : ℤ)}, hcyl, ?_⟩
        refine Set.Subset.antisymm ?_ ?_
        · rintro U ⟨hU, -, hmark⟩
          exact ⟨hU, hmark⟩
        · rintro U ⟨hU, hmark⟩
          refine ⟨hU, ?_, hmark⟩
          rw [runMax_eq_recVal_of_mem hU j]
          exact hlt
      · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
        rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
        rintro U ⟨hU, -, hmark⟩
        exact hg (gate_of_siteMark_of_lt_recVal hp m n hU j hlt hmark)
    · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
      rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
      rintro U ⟨hU, hlt', -⟩
      exact hlt (by rw [runMax_eq_recVal_of_mem hU j] at hlt'; exact hlt')
  · refine ⟨∅, (cylAt (prefRead n γ)).measurableSet_empty, ?_⟩
    rw [Set.inter_empty, Set.eq_empty_iff_forall_notMem]
    rintro U ⟨hU, -⟩
    exact hne ⟨U, hU⟩

/-! ### The restricted value `h_j(x)` below the record -/

/-- **`h_j(x)` restricted to `{x < M_n^j}` is `enlFilt`-measurable**, for every natural site `x`.
Induction over the mark recursion: at the site `x+1` the two branches of `hstep` are affine in
the value at `x`, the marked event below the record is `measurableSet_below_mark`, and the
restriction `{x+1 < M} ⊆ {x < M}` lets the inductive hypothesis be substituted. -/
theorem measurable_below_hof {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) (x : ℕ) :
    Measurable[enlFilt p m n]
      (fun U : Array N => if (x : ℤ) < runMax p m U j n
        then SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x else 0) := by
  classical
  have hS : MeasurableSet[enlFilt p m n] {U : Array N | (x : ℤ) < runMax p m U j n} :=
    measurableSet_lt_runMax (p := p) m n j x
  -- the marked sets at the sites `0, ..., x`, restricted to the event `{x < M}`
  have hmark : ∀ y : ℕ, MeasurableSet[enlFilt p m n]
      ({U : Array N | (x : ℤ) < runMax p m U j n}
        ∩ {U : Array N | (y : ℤ) < runMax p m U j n ∧ SiteMark p m U j (y : ℤ)}) :=
    fun y => hS.inter (measurableSet_below_mark (p := p) hp m n j y)
  -- the marked sets at `0, ..., x` are measurable for the enlarged filtration, hence ambient
  -- the modified mark sequence, measurable as a map into `ℕ → Bool`
  have hω : Measurable[enlFilt p m n] (fun U : Array N => fun y : ℕ =>
      if y ≤ x then (if (x : ℤ) < runMax p m U j n
        then SwarmLogRatio.siteMarks p m U j y else false) else false) := by
    refine measurable_pi_iff_enl.2 (fun y => ?_)
    by_cases hy : y ≤ x
    · have heq : (fun U : Array N => if y ≤ x then (if (x : ℤ) < runMax p m U j n
            then SwarmLogRatio.siteMarks p m U j y else false) else false)
          = fun U => if U ∈ ({U : Array N | (x : ℤ) < runMax p m U j n}
              ∩ {U : Array N | (y : ℤ) < runMax p m U j n ∧ SiteMark p m U j (y : ℤ)})
            then true else false := by
        funext U
        rw [if_pos hy]
        by_cases hU : (x : ℤ) < runMax p m U j n
        · have h1 : ((y : ℤ)) ≤ ((x : ℤ)) := by exact_mod_cast hy
          have hY : (y : ℤ) < runMax p m U j n := by omega
          by_cases hM : SiteMark p m U j (y : ℤ)
          · rw [if_pos hU, siteMarks_eq_true hM, if_pos ⟨hU, hY, hM⟩]
          · rw [if_pos hU, siteMarks_eq_false hM]
            simp [hM]
        · rw [if_neg hU]
          simp [hU]
      rw [heq]
      exact Measurable.ite (hmark y) measurable_const measurable_const
    · have heq : (fun U : Array N => if y ≤ x then (if (x : ℤ) < runMax p m U j n
            then SwarmLogRatio.siteMarks p m U j y else false) else false) = fun _ => false := by
        funext U; rw [if_neg hy]
      rw [heq]
      exact measurable_const
  -- on the event the two mark sequences agree at `0, ..., x`
  have hagree : ∀ U : Array N, (x : ℤ) < runMax p m U j n →
      SwarmMarks.hof p (fun y : ℕ => if y ≤ x then
        (if (x : ℤ) < runMax p m U j n
          then SwarmLogRatio.siteMarks p m U j y else false) else false) x
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x := by
    intro U hU
    refine SwarmMarks.hof_congr x (fun i hi => ?_)
    rw [if_pos hi, if_pos hU]
  have heq : (fun U : Array N => if (x : ℤ) < runMax p m U j n
        then SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x else 0)
      = fun U => if (x : ℤ) < runMax p m U j n
          then SwarmMarks.hof p (fun y : ℕ => if y ≤ x then
            (if (x : ℤ) < runMax p m U j n
              then SwarmLogRatio.siteMarks p m U j y else false) else false) x
          else 0 := by
    funext U
    by_cases hU : (x : ℤ) < runMax p m U j n
    · rw [if_pos hU, if_pos hU, hagree U hU]
    · rw [if_neg hU, if_neg hU]
  rw [heq]
  have hcomp : Measurable[enlFilt p m n]
      (fun U : Array N => SwarmMarks.hof p (fun y : ℕ => if y ≤ x then
        (if (x : ℤ) < runMax p m U j n
          then SwarmLogRatio.siteMarks p m U j y else false) else false) x) :=
    Measurable.comp (g := fun (ω : ℕ → Bool) => SwarmMarks.hof p ω x)
      (measurable_hof_any p x) hω
  exact Measurable.ite hS hcomp measurable_const

/-- **The restricted environment value at a site below the record.**  If `A ∈ F_n` and
`A ⊆ {x < M_n^j}`, then `A.indicator (h_j(x))` is `F_n`-measurable.  This is exactly the
substitution input of the one-step drift on the interior region. -/
theorem measurable_indicator_hof_of_below {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (x : ℕ) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (hAM : A ⊆ {U : Array N | (x : ℤ) < runMax p m U j n}) :
    Measurable[enlFilt p m n]
      (A.indicator (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)) := by
  have hbelow := measurable_below_hof (p := p) hp m n j x
  have heq : A.indicator (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x)
      = fun U => A.indicator (fun _ => (1 : ℝ)) U
        * (if (x : ℤ) < runMax p m U j n
            then SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x else 0) := by
    funext U
    by_cases hU : U ∈ A
    · have hlt : (x : ℤ) < runMax p m U j n := hAM hU
      rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, if_pos hlt]
      ring
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
      ring
  rw [heq]
  exact (Measurable.indicator measurable_const hA).mul hbelow

end Swarming.Enl


