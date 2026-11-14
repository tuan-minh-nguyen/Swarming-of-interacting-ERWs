/-
  **DIRECTION C (m3) — `QIncrementAdapted.lean`: is `ZJinc t` measurable for `𝓕_{t+1}`?**

  The file `CompensatorMeanZero.lean` reduced the martingale property of `Qcomp` to the single
  named hypothesis

      hadapt : ∀ t, StronglyMeasurable[enlFilt p m (t + 1)] (fun U => ZJinc p m eps i j U t)

  and deliberately did not assert it.  This file settles the question **negatively** for the
  actual model, and supplies the corrected (projected) statement.

  The mechanism is the *quenched environment*: `envH p m j U = hof p (siteMarks p m U j)` is a
  function of the whole row `(j, x, k)` of the array, including coordinates that no walker has
  read by time `t + 1`.  Concretely:

  * §1 proves the purely pointwise invariance lemma: if a map `T` fixes every coordinate of
    `prefRead n γ` (the coordinates read strictly before `n`), then **every** `𝓕_n`-measurable
    set — hence every `𝓕_n`-strongly-measurable real function — is pointwise `T`-invariant.
    (`StronglyMeasurable` in Mathlib is pointwise, so no measure theory enters.)
  * §2 builds an explicit array `testArray`, flips the single coordinate `(j, 0, 3)` (never read
    before time `1`), and computes that the flip changes `HpotInc 0` — hence `ZJinc 0` — from
    `hstep p false 1 = 3` to `hstep p true 1 = (2-p)/p`, which differ for `p > 1/2`.
    Therefore `¬ StronglyMeasurable[enlFilt p m 1] (ZJinc p m eps i j · 0)`: `hadapt` is
    **false** at the actual model, for every `m ≥ 3`, `p ∈ (1/2,1)`, `eps > 0`, `i ≠ j`.
  * §3 gives the corrected statement that is true without any adaptedness hypothesis: the
    *optional projection* `T ↦ condExp (𝓕_T) (Qcomp T)` is a genuine martingale.  This is the
    honest replacement for `martingale_Qcomp`.

  No `sorry`, no custom axiom; all axioms are checked at the end of `Audit.lean`.
-/
import Swarm.CompensatorMeanZero

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ## 1. A single-coordinate flip that no path reads before time `n` -/

/-- Flip one array coordinate `c₀` by `y ↦ 1 - y`. -/
noncomputable def flipAt (c₀ : Fin N × ℤ × ℕ) (U : Array N) : Array N :=
  Function.update U c₀ (1 - U c₀)

@[simp] lemma flipAt_self (c₀ : Fin N × ℤ × ℕ) (U : Array N) : flipAt c₀ U c₀ = 1 - U c₀ := by
  simp [flipAt]

lemma flipAt_of_ne {c₀ c : Fin N × ℤ × ℕ} (h : c ≠ c₀) (U : Array N) : flipAt c₀ U c = U c := by
  simp only [flipAt, Function.update_of_ne h]

lemma flipAt_involutive (c₀ : Fin N × ℤ × ℕ) (U : Array N) : flipAt c₀ (flipAt c₀ U) = U := by
  funext c
  by_cases h : c = c₀
  · subst h; simp
  · rw [flipAt_of_ne h, flipAt_of_ne h]

section Invariance

variable {p : ℝ} {m n : ℕ}

/-- A local time is at most the number of times it has counted. -/
lemma localTime_le_succ (X : ℕ → ℤ) (n : ℕ) (x : ℤ) : localTime X n x ≤ n + 1 := by
  rw [localTime_def]
  calc ((Finset.range (n + 1)).filter fun t => X t = x).card
      ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range _

/-- The coordinates read strictly before time `n` have third component `≤ n`. -/
lemma mem_prefRead_third_le {γ : Pref N n} {c : Fin N × ℤ × ℕ} (hc : c ∈ prefRead n γ) :
    c.2.2 ≤ n := by
  rcases c with ⟨i, x, k⟩
  rw [mem_prefRead] at hc
  obtain ⟨t, ht, -, hk⟩ := hc
  rw [← hk]
  exact le_trans (localTime_le_succ _ _ _) (by omega)

/-- **The flip fixes every coordinate read before time `n`**, provided its index exceeds `n`. -/
lemma flipAt_prefRead_eq {c₀ : Fin N × ℤ × ℕ} (h3 : n < c₀.2.2) {γ : Pref N n} {c : Fin N × ℤ × ℕ}
    (hc : c ∈ prefRead n γ) (U : Array N) : flipAt c₀ U c = U c := by
  refine flipAt_of_ne ?_ U
  rintro rfl
  have := mem_prefRead_third_le hc
  omega

/-- Consequently a flipped array follows the same position prefix. -/
lemma prefAgree_flipAt {c₀ : Fin N × ℤ × ℕ} (h3 : n < c₀.2.2) {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) : flipAt c₀ U ∈ prefAgree p m γ := by
  intro t
  have h := traj_depends_on_prefRead p m γ U (flipAt c₀ U) hU
    (fun c hc => (flipAt_prefRead_eq h3 hc U).symm) t.1 (by omega)
  rw [← h]
  exact hU t

/-- Cylinder sets only see the coordinates of their index set. -/
lemma cylAt_congr {S : Finset (Fin N × ℤ × ℕ)} {B : Set (Array N)} (hB : MeasurableSet[cylAt S] B)
    {U U' : Array N} (h : ∀ c ∈ S, U c = U' c) : (U ∈ B ↔ U' ∈ B) := by
  obtain ⟨A, -, hBA⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hproj : (fun c : S => U c) = (fun c : S => U' c) := funext fun c => h c.1 c.2
  have key : ∀ W : Array N, (W ∈ B) ↔ ((fun c : S => W c) ∈ A) := by
    intro W; rw [← hBA]; rfl
  rw [key U, key U', hproj]

/-- **Every `𝓕_n`-measurable set is invariant under a flip of a coordinate with index `> n`.** -/
theorem enlMeas_flipAt_mem {c₀ : Fin N × ℤ × ℕ} (h3 : n < c₀.2.2) {G : Set (Array N)}
    (hG : MeasurableSet[enlMeas p m n] G) (U : Array N) : flipAt c₀ U ∈ G ↔ U ∈ G := by
  classical
  obtain ⟨B, hB, hEq⟩ := hG (prefOf p m n U)
  have hU : U ∈ prefAgree p m (prefOf p m n U) := prefAgree_prefOf U
  have hTU : flipAt c₀ U ∈ prefAgree p m (prefOf p m n U) := prefAgree_flipAt h3 hU
  have h1 : (U ∈ G ↔ U ∈ B) := by
    have h' : U ∈ prefAgree p m (prefOf p m n U) ∩ G ↔
        U ∈ prefAgree p m (prefOf p m n U) ∩ B := by rw [hEq]
    simpa [hU] using h'
  have h2 : (flipAt c₀ U ∈ G ↔ flipAt c₀ U ∈ B) := by
    have h' : flipAt c₀ U ∈ prefAgree p m (prefOf p m n U) ∩ G ↔
        flipAt c₀ U ∈ prefAgree p m (prefOf p m n U) ∩ B := by rw [hEq]
    simpa [hTU] using h'
  have h3' : (flipAt c₀ U ∈ B ↔ U ∈ B) :=
    cylAt_congr hB (fun c hc => flipAt_prefRead_eq h3 hc U)
  exact h2.trans (h3'.trans h1.symm)

/-- **Every `𝓕_n`-measurable real function is pointwise invariant** under such a flip. -/
theorem measurable_flipAt_eq {c₀ : Fin N × ℤ × ℕ} (h3 : n < c₀.2.2) {g : Array N → ℝ}
    (hg : Measurable[enlMeas p m n] g) (U : Array N) : g (flipAt c₀ U) = g U := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    push Not at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    have hG : MeasurableSet[enlMeas p m n] {W : Array N | g W < (q : ℝ)} :=
      hg measurableSet_Iio
    have hiff := enlMeas_flipAt_mem (p := p) (m := m) h3 hG U
    have : g (flipAt c₀ U) < (q : ℝ) := hiff.mpr (by exact_mod_cast hq1)
    exact absurd this (not_lt.mpr (le_of_lt hq2))
  · by_contra hcon
    push Not at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    have hG : MeasurableSet[enlMeas p m n] {W : Array N | g W < (q : ℝ)} :=
      hg measurableSet_Iio
    have hiff := enlMeas_flipAt_mem (p := p) (m := m) h3 hG U
    have : g U < (q : ℝ) := hiff.mp (by exact_mod_cast hq1)
    exact absurd this (not_lt.mpr (le_of_lt hq2))

/-- The `StronglyMeasurable` form used by `CompensatorMeanZero.hadapt`. -/
theorem stronglyMeasurable_flipAt_eq {c₀ : Fin N × ℤ × ℕ} (h3 : n < c₀.2.2) {g : Array N → ℝ}
    (hg : StronglyMeasurable[enlFilt p m n] g) (U : Array N) : g (flipAt c₀ U) = g U :=
  measurable_flipAt_eq h3 (stronglyMeasurable_iff_measurable.mp hg) U

end Invariance

/-! ## 2. The countermodel: `ZJinc 0` is not `𝓕₁`-measurable

The environment `envH p m j U = hof p (siteMarks p m U j)` reads the *whole* row `j` of the
array: `SiteMark p m U j x` asks that all `m-1` coordinates `(j,x,1), …, (j,x,m-1)` exceed
`p`.  At time `0` walker `j` reads only `(j,0,1)`, so with `m ≥ 4` the coordinate `(j,0,3)`
is invisible to `𝓕₁` — but it decides the mark at site `0`, hence `h_j(0) = envH p m j U 0`.

We flip that coordinate.  §1 says `ZJinc 0` would have to be invariant; the computation below
says it is not. -/

section Countermodel

open VdriftAssembly

/-- The test array for the flip of the coordinate `(j, 0, m-1)`: that mark coordinate is below
`p` (mark false), walker `i`'s first coordinate is `1/2` (a right jump at time `0`), and every
other coordinate is above `p`. -/
noncomputable def testArray (p : ℝ) (m : ℕ) (i j : Fin N) : Array N :=
  fun c => if c = (j, (0 : ℤ), m - 1) then (1 - p) / 2
    else if c = (i, (0 : ℤ), 1) then 1 / 2
    else (1 + p) / 2

lemma testArray_mark_coord (p : ℝ) (m : ℕ) (i j : Fin N) :
    testArray p m i j (j, (0 : ℤ), m - 1) = (1 - p) / 2 := by
  simp [testArray]

lemma testArray_other (p : ℝ) (m : ℕ) (i j : Fin N) {c : Fin N × ℤ × ℕ}
    (h1 : c ≠ (j, (0 : ℤ), m - 1)) (h2 : c ≠ (i, (0 : ℤ), 1)) :
    testArray p m i j c = (1 + p) / 2 := by
  simp only [testArray, if_neg h1, if_neg h2]

lemma testArray_first (p : ℝ) (m : ℕ) (i j : Fin N) (hm : 3 ≤ m) :
    testArray p m i j (i, (0 : ℤ), 1) = 1 / 2 := by
  have h : (i, (0 : ℤ), 1) ≠ (j, (0 : ℤ), m - 1) := by
    intro h
    have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) h
    simp only at this
    omega
  simp [testArray, h]

lemma flipAt_mark_coord (p : ℝ) (m : ℕ) (i j : Fin N) :
    flipAt (j, (0 : ℤ), m - 1) (testArray p m i j) (j, (0 : ℤ), m - 1) = (1 + p) / 2 := by
  rw [flipAt_self, testArray_mark_coord]
  ring

lemma flipAt_other_coord (p : ℝ) (m : ℕ) (i j : Fin N) {c : Fin N × ℤ × ℕ}
    (h : c ≠ (j, (0 : ℤ), m - 1)) :
    flipAt (j, (0 : ℤ), m - 1) (testArray p m i j) c = testArray p m i j c :=
  flipAt_of_ne h _

/-! ### The mark at site `0` flips -/

lemma siteMark_testArray_false {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hm : 3 ≤ m) (i j : Fin N) :
    ¬ SiteMark p m (testArray p m i j) j 0 := by
  intro h
  have h3 : m - 1 ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hlt := h (m - 1) h3
  rw [testArray_mark_coord] at hlt
  linarith

lemma siteMark_flipAt_true {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 3 ≤ m)
    {i j : Fin N} (hij : i ≠ j) :
    SiteMark p m (flipAt (j, (0 : ℤ), m - 1) (testArray p m i j)) j 0 := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  by_cases hk3 : k = m - 1
  · subst hk3
    rw [flipAt_mark_coord]
    linarith
  · have hne : ((j, (0 : ℤ), k) : Fin N × ℤ × ℕ) ≠ (j, (0 : ℤ), m - 1) := by
      intro h
      exact hk3 (by simpa using congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) h)
    rw [flipAt_other_coord _ _ _ _ hne]
    have hne2 : ((j, (0 : ℤ), k) : Fin N × ℤ × ℕ) ≠ (i, (0 : ℤ), 1) := by
      intro h
      have h1 : j = i := congrArg (fun c : Fin N × ℤ × ℕ => c.1) h
      exact hij h1.symm
    rw [testArray_other _ _ _ _ hne hne2]
    linarith

/-! ### The value of the `Hpot` increment at time `0` -/

/-- `HpotInc 0` at a path at position `1` is the environment value at site `0`. -/
lemma HpotInc_zero_eq {p : ℝ} {m : ℕ} {i j : Fin N} {U : Array N}
    (hX : (trajectory p m U 1).pos i = 1) :
    HpotInc p m 0 i j U = envH p m j U 0 := by
  unfold HpotInc
  rw [hX]
  have h0 : (trajectory p m U 0).pos i = 0 := by simp
  rw [h0]
  simp [SwarmOcc.Hpot]

/-- The environment value at site `0` is the first two-branch step of the mark recursion. -/
lemma envH_zero_eq_hstep {p : ℝ} {m : ℕ} (j : Fin N) (U : Array N) :
    envH p m j U 0 = SwarmMarks.hstep p (SwarmLogRatio.siteMarks p m U j 0) 1 := rfl

lemma siteMarks_zero_eq_false {p : ℝ} {m : ℕ} (j : Fin N) {U : Array N}
    (h : ¬ SiteMark p m U j (0 : ℤ)) : SwarmLogRatio.siteMarks p m U j 0 = false := by
  classical
  simp [SwarmLogRatio.siteMarks, h]

lemma siteMarks_zero_eq_true {p : ℝ} {m : ℕ} (j : Fin N) {U : Array N}
    (h : SiteMark p m U j (0 : ℤ)) : SwarmLogRatio.siteMarks p m U j 0 = true := by
  classical
  simp [SwarmLogRatio.siteMarks, h]

/-- The environment value at site `0` when the mark is false: `3`. -/
lemma envH_zero_of_not_siteMark {p : ℝ} {m : ℕ} (j : Fin N) {U : Array N}
    (h : ¬ SiteMark p m U j (0 : ℤ)) : envH p m j U 0 = 3 := by
  have hs := siteMarks_zero_eq_false (p := p) (m := m) j h
  rw [envH_zero_eq_hstep, hs, SwarmMarks.hstep_false]
  norm_num

/-- The environment value at site `0` when the mark is true: `(2-p)/p`. -/
lemma envH_zero_of_siteMark {p : ℝ} {m : ℕ} (j : Fin N) {U : Array N}
    (hp0 : p ≠ 0) (h : SiteMark p m U j (0 : ℤ)) : envH p m j U 0 = 2 / p - 1 := by
  have hs := siteMarks_zero_eq_true (p := p) (m := m) j h
  rw [envH_zero_eq_hstep, hs, SwarmMarks.hstep_true]
  field_simp
  ring

/-- The two values differ for `p > 1/2`. -/
lemma two_div_sub_one_ne_three {p : ℝ} (hp : (1 : ℝ) / 2 < p) : (2 : ℝ) / p - 1 ≠ 3 := by
  intro h
  have h2 : 2 / p = 4 := by linarith
  field_simp at h2
  linarith

/-! ### The value of `ZJinc 0` at position `1` -/

/-- `bRec` at time `0` is the constant `3`: the record is `0`, so `HprevAt` is the boundary
value `1`. -/
lemma bRec_zero (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) : bRec p m 0 j U = 3 := by
  have h0 : recVal j (prefOf p m 0 U) = 0 := by
    rw [← runMax_eq_recVal]
    exact VdriftAssembly.runMax_zero p m U j
  simp [bRec, HprevAt, h0]
  norm_num

/-- **`ZJinc 0` at position `1` is `h_j(0) - F_3(1)`.** -/
lemma ZJinc_zero_eq {p : ℝ} {m : ℕ} {eps : ℝ} {i j : Fin N} {U : Array N}
    (hX : (trajectory p m U 1).pos i = 1) :
    ZJinc p m eps i j U 0
      = HpotInc p m 0 i j U - SwarmOcc.Fcorr (aRec p m) eps 3 1 := by
  have h := Zpot_add_J p m eps i j U 0
  have hZJ : ZJinc p m eps i j U 0 = HpotInc p m 0 i j U - Cinc p m eps i j U 0 := h
  rw [hZJ]
  have hC : Cinc p m eps i j U 0 = SwarmOcc.Fcorr (aRec p m) eps 3 1 := by
    simp only [Cinc]
    rw [hX, VdriftAssembly.runMax_zero]
    have h0 : (trajectory p m U 0).pos i = 0 := by simp
    rw [h0, sub_zero, sub_zero, bRec_zero]
    simp [SwarmOcc.Fcorr]
  rw [hC]

/-- **The right jump of walker `i` at time `0`.** -/
lemma trajectory_one_testArray {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m : ℕ) (hm : 3 ≤ m) (i j : Fin N) :
    (trajectory p m (testArray p m i j) 1).pos i = 1 := by
  have hα : (1 : ℝ) / 2 ≤ rightProbability p m (initialWalkState (N := N)).ell i 0 :=
    one_half_le_rightProbability hp m _ i 0
  have hval : (trajectory p m (testArray p m i j) 1).pos i
      = drivenStep (testArray p m i j (i, (0 : ℤ), 1))
          (rightProbability p m (initialWalkState (N := N)).ell i 0) := by
    simp [trajectory_succ, nextWalkState_pos, nextPos, initialWalkState]
  rw [hval, testArray_first p m i j hm, drivenStep, if_pos hα]

/-- **The flip does not change walker `i`'s position at time `1`.** -/
lemma trajectory_one_flipAt {p : ℝ} (m : ℕ) (hm : 3 ≤ m) (i j : Fin N) :
    (trajectory p m (flipAt (j, (0 : ℤ), m - 1) (testArray p m i j)) 1).pos i
      = (trajectory p m (testArray p m i j) 1).pos i := by
  have hU : testArray p m i j ∈ prefAgree p m (prefOf p m 1 (testArray p m i j)) :=
    prefAgree_prefOf _
  have h := traj_depends_on_prefRead p m (prefOf p m 1 (testArray p m i j)) (testArray p m i j)
    (flipAt (j, (0 : ℤ), m - 1) (testArray p m i j)) hU
    (fun c hc => (flipAt_prefRead_eq (c₀ := (j, (0 : ℤ), m - 1)) (by
      simp only; omega) hc _).symm)
    1 le_rfl
  rw [← h]

/-- **The countermodel: for every `m ≥ 3`, `p ∈ (1/2,1)` and `i ≠ j`, the increment
`ZJinc · 0` is not `𝓕₁`-strongly measurable.**  Hence the hypothesis `hadapt` of
`CompensatorMeanZero.martingale_Qcomp` is false at the actual model. -/
theorem not_stronglyMeasurable_ZJinc_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 3 ≤ m) {eps : ℝ} {i j : Fin N} (hij : i ≠ j) :
    ¬ StronglyMeasurable[enlFilt p m 1] (fun U : Array N => ZJinc p m eps i j U 0) := by
  intro hg
  have hinv := stronglyMeasurable_flipAt_eq (p := p) (m := m) (n := 1)
    (c₀ := (j, (0 : ℤ), m - 1)) (by simp only; omega) hg (testArray p m i j)
  have hX : (trajectory p m (testArray p m i j) 1).pos i = 1 :=
    trajectory_one_testArray hp0.le m hm i j
  have hX' : (trajectory p m (flipAt (j, (0 : ℤ), m - 1) (testArray p m i j)) 1).pos i = 1 := by
    rw [trajectory_one_flipAt m hm]; exact hX
  rw [ZJinc_zero_eq hX', ZJinc_zero_eq hX] at hinv
  have hval : HpotInc p m 0 i j (flipAt (j, (0 : ℤ), m - 1) (testArray p m i j))
      = HpotInc p m 0 i j (testArray p m i j) := by linarith
  rw [HpotInc_zero_eq hX', HpotInc_zero_eq hX] at hval
  rw [envH_zero_of_siteMark (p := p) (m := m) j (by linarith)
      (siteMark_flipAt_true hp0 hp1 hm hij),
    envH_zero_of_not_siteMark (p := p) (m := m) j (siteMark_testArray_false hp0 hm i j)] at hval
  exact two_div_sub_one_ne_three hp0 hval

end Countermodel

/-! ## 3. The corrected statement: the optional projection of `Qcomp` is a martingale

`hadapt` fails, but the *usable* martingale statement survives in projected form.  The reason
is `condExp_Qcomp_block_eq_zero`: every block `Qcomp b - Qcomp a` is centred given `𝓕_s`,
`s ≤ a ≤ b`.  Hence `condExp (𝓕_a) (Qcomp b) =ᵐ condExp (𝓕_a) (Qcomp a)`, so the optional
projection `T ↦ condExp (𝓕_T) (Qcomp T)` is a genuine martingale.  This needs no adaptedness of
`Zpot`/`ZJinc` and no `hadapt`. -/

section Projection

open VdriftAssembly

/-- The optional projection of `Qcomp` on the enlarged filtration. -/
noncomputable def Qproj (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (T : ℕ) : Array N → ℝ :=
  condExp (enlFilt p m T) (arrayMeasure N)
    (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U T)

/-- **The corrected martingale statement.**  `T ↦ E[Qcomp T | 𝓕_T]` is a martingale for the
enlarged filtration, with **no** adaptedness hypothesis. -/
theorem martingale_Qproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} (hε : 0 < eps) :
    Martingale (fun T (U : Array N) => Qproj p m eps i j T U) (enlFilt p m) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine ⟨fun T => stronglyMeasurable_condExp, fun a b hab => ?_⟩
  have hQb : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U b) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε b
  have hQa : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U a) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε a
  have htower : condExp (enlFilt p m a) (arrayMeasure N)
      (fun U : Array N => Qproj p m eps i j b U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m a) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b) :=
    condExp_condExp_of_le (m₁ := enlFilt p m a) (m₂ := enlFilt p m b)
      (f := fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
      (Filtration.mono (enlFilt p m) hab) ((enlFilt p m).le b)
  have hblock := condExp_Qcomp_block_eq_zero (p := p) (m := m) (s := a) (i := i) (j := j)
    hp0 hp1 hε a b le_rfl hab
  have hsplit : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
      = ((fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
          - (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a))
        + fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a := by
    funext U
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hstep : condExp (enlFilt p m a) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m a) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a) := by
    have h1 : condExp (enlFilt p m a) (arrayMeasure N)
        (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
        =ᵐ[arrayMeasure N] condExp (enlFilt p m a) (arrayMeasure N)
          (((fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U b)
            - (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a))
            + fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U a) :=
      Filter.EventuallyEq.of_eq (congrArg
        (fun f : Array N → ℝ => condExp (enlFilt p m a) (arrayMeasure N) f) hsplit)
    refine h1.trans ?_
    refine (condExp_add (hQb.sub hQa) hQa ((enlFilt p m) a)).trans ?_
    refine (Filter.EventuallyEq.add hblock (Filter.EventuallyEq.refl _ _)).trans ?_
    exact Filter.EventuallyEq.of_eq (zero_add _)
  simpa only [Qproj] using htower.trans hstep

end Projection
