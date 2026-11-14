/-
  **`σ_y^A` is a genuine stopping time of the enlarged filtration `enlFilt p m`.**

  The paper (`main_1d_revised.tex`, proof of Proposition `local`) needs, for every nonempty
  `A ⊆ {1,…,N}` and every `y`, the first passage `σ_y^A = inf{n ≥ 0 : R_n^A = y}` of the
  *group record* `R_n^A = max_{i ∈ A} M_n^i`, together with the leader `i_y`, as the stopping
  time at which the `2m-1`-step trial `Γ_y^A` starts.  `GammaStopped.lean` proves the stopped
  trial law for an *arbitrary* `IsStoppingTime`, and its file header records as missing exactly
  the construction of `σ_y^A` on the actual array.  That is the content of this file.

  What is proved here (all on the actual trajectory `Swarming.Trajectory.trajectory` of the
  i.i.d. uniform array, with no hypothesis beyond `A` nonempty and `y ≥ 0`):

  * `runMaxA` — the group record `R_n^A`, with `runMaxA_le_iff`, monotonicity in `n`,
    `runMaxA_succ_le` (`R_{n+1}^A ≤ R_n^A + 1`), `runMaxA_zero` (`R_0^A = 0`);
  * `ARMax` — the group first-passage predicate `R_n^A ≥ y` and `R_t^A < y` for `t < n`;
    `ARMax.eq` (at first passage the record **equals** `y`), `ARMax.exists_pos` (**the leader
    exists**: some `j ∈ A` sits exactly at `y` at first passage), `ARMax_unique`;
  * `measurableSet_ARMax` — no future leakage: the first-passage event at `n` is
    `enlMeas p m n`-measurable (path-prefix criterion `measurableSet_enl_of_prefPred`);
  * `sigmaA` — the first passage as an `Array N → WithTop ℕ` function, with the exact level
    sets `sigmaA_eq_coe_iff` (`{σ_y^A = n} = {ARMax n}`) and `sigmaA_le_iff`;
  * `isStoppingTime_sigmaA` — `IsStoppingTime (enlFilt p m) σ_y^A`, hence
    `stopped_wordRun_mass_ge_isStoppingTime` applies to the paper's `σ_y^A`.

  Not claimed here: the conditional/stopped mass bound for the paper's `Γ_y^A` itself and the
  residue-class martingale count (`(locsum)`); those are the remaining gap, recorded at the end.
-/
import Swarm.StopFresh
import Swarm.GammaStopped
import Swarm.BelowMeas

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ## 1. The group running record `R_n^A = max_{i ∈ A} M_n^i` -/

/-- The paper's group record `R_n^A = max_{i ∈ A} M_n^i`. -/
noncomputable def runMaxA (p : ℝ) (m : ℕ) (U : Array N) {A : Finset (Fin N)}
    (hA : A.Nonempty) (n : ℕ) : ℤ :=
  A.sup' hA fun j => runMax p m U j n

lemma le_runMaxA {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {n : ℕ} {j : Fin N} (hj : j ∈ A) : runMax p m U j n ≤ runMaxA p m U hA n :=
  Finset.le_sup' (fun j => runMax p m U j n) hj

/-- Every walker of the group is at or below the group record. -/
lemma pos_le_runMaxA {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {n : ℕ} {j : Fin N} (hj : j ∈ A) :
    (trajectory p m U n).pos j ≤ runMaxA p m U hA n :=
  (le_runMax p m U j n).trans (le_runMaxA hj)

lemma runMaxA_le_iff {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {n : ℕ} {c : ℤ} :
    runMaxA p m U hA n ≤ c ↔ ∀ j ∈ A, runMax p m U j n ≤ c :=
  Finset.sup'_le_iff hA _

/-- The group record is nondecreasing in time. -/
lemma runMaxA_mono {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {a b : ℕ} (h : a ≤ b) : runMaxA p m U hA a ≤ runMaxA p m U hA b :=
  Finset.sup'_le hA _ (fun j hj => (runMax_mono U j h).trans (le_runMaxA hj))

/-- A single walker's record increases by at most one per step. -/
lemma runMax_succ_le {p : ℝ} {m : ℕ} (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j (n + 1) ≤ runMax p m U j n + 1 := by
  refine runMax_le_of_forall U j (fun t ht => ?_)
  rcases Nat.lt_or_eq_of_le ht with hlt | heq
  · have h1 : (trajectory p m U t).pos j ≤ runMax p m U j t := le_runMax p m U j t
    have h2 : runMax p m U j t ≤ runMax p m U j n := runMax_mono U j (by omega)
    omega
  · subst heq
    have h1 : (trajectory p m U (n + 1)).pos j ≤ (trajectory p m U n).pos j + 1 :=
      pos_succ_le p m U n j
    have h2 : (trajectory p m U n).pos j ≤ runMax p m U j n := le_runMax p m U j n
    omega

/-- **`R_{n+1}^A ≤ R_n^A + 1`**: the group record cannot advance by more than one per step. -/
lemma runMaxA_succ_le {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    (n : ℕ) : runMaxA p m U hA (n + 1) ≤ runMaxA p m U hA n + 1 :=
  Finset.sup'_le hA _ (fun j hj => (runMax_succ_le U j n).trans (by
    have := le_runMaxA (p := p) (m := m) (U := U) (hA := hA) (n := n) hj
    omega))

/-- `R_0^A = 0`: all walkers start at the origin. -/
lemma runMaxA_zero {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} (hA : A.Nonempty) :
    runMaxA p m U hA 0 = 0 := by
  have h1 : runMaxA p m U hA 0 ≤ 0 := by
    refine Finset.sup'_le hA _ (fun j _ => ?_)
    rw [runMax_zero]
  have h2 : 0 ≤ runMaxA p m U hA 0 := by
    have hmem : hA.choose ∈ A := hA.choose_spec
    have h := le_runMaxA (p := p) (m := m) (U := U) (hA := hA) (n := 0) hmem
    rwa [runMax_zero] at h
  omega

/-! ## 2. Reading the record off a position prefix -/

/-- The running max of walker `j` read off a position prefix. -/
noncomputable def runMaxExt {n : ℕ} (γ : Pref N n) (j : Fin N) (t : ℕ) : ℤ :=
  (Finset.range (t + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos t)⟩
    (fun s => ext γ s j)

/-- The group record read off a position prefix. -/
noncomputable def runMaxAExt {N : ℕ} {n : ℕ} {A : Finset (Fin N)} (hA : A.Nonempty)
    (γ : Pref N n) (t : ℕ) : ℤ :=
  A.sup' hA fun j => runMaxExt γ j t

/-- On a piece the actual running max is the prefix's running max. -/
lemma runMax_eq_ext {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {t : ℕ} (ht : t ≤ n) (j : Fin N) :
    runMax p m U j t = runMaxExt γ j t := by
  have hpos : ∀ s, s ≤ t → (trajectory p m U s).pos j = ext γ s j := by
    intro s _
    rw [ext_of_lt γ (by omega)]
    exact congrFun (hU ⟨s, by omega⟩) j
  simp only [runMax, runMaxExt]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun s hs => ?_)
    rw [hpos s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))]
    exact Finset.le_sup' (fun s => ext γ s j) hs
  · refine Finset.sup'_le _ _ (fun s hs => ?_)
    rw [← hpos s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))]
    exact Finset.le_sup' (fun s => (trajectory p m U s).pos j) hs

/-- On a piece the actual group record is the prefix's group record. -/
lemma runMaxA_eq_ext {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N} {A : Finset (Fin N)}
    {hA : A.Nonempty} (hU : U ∈ prefAgree p m γ) {t : ℕ} (ht : t ≤ n) :
    runMaxA p m U hA t = runMaxAExt hA γ t := by
  simp only [runMaxA, runMaxAExt]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun j hj => ?_)
    rw [runMax_eq_ext hU ht j]
    exact Finset.le_sup' (fun j => runMaxExt γ j t) hj
  · refine Finset.sup'_le _ _ (fun j hj => ?_)
    rw [← runMax_eq_ext hU ht j]
    exact Finset.le_sup' (fun j => runMax p m U j t) hj

/-- A set that is decided by the position prefix is measurable for the enlarged filtration. -/
lemma measurableSet_enl_of_prefPred {p : ℝ} {m n : ℕ} {G : Set (Array N)}
    {P : Pref N n → Prop}
    (h : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ → (U ∈ G ↔ P γ)) :
    MeasurableSet[enlMeas p m n] G := by
  refine measurableSet_enl_of_piecewise (fun γ => ?_)
  by_cases hP : P γ
  · right
    refine Set.Subset.antisymm Set.inter_subset_left ?_
    rintro U hU
    exact ⟨hU, (h γ U hU).2 hP⟩
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hGU⟩
    exact hP ((h γ U hU).1 hGU)

/-! ## 3. The group first passage `R^A` reaches the level `y` -/

/-- `ARMax y n`: the group record reaches the level `y` for the first time at time `n`. -/
def ARMax (p : ℝ) (m : ℕ) (U : Array N) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y : ℤ) (n : ℕ) : Prop :=
  y ≤ runMaxA p m U hA n ∧ ∀ t < n, runMaxA p m U hA t < y

/-- **At first passage the group record equals the level** (no overshoot). -/
lemma ARMax.eq {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {n : ℕ} (hy : 0 ≤ y) (hr : ARMax p m U hA y n) :
    runMaxA p m U hA n = y := by
  refine le_antisymm ?_ hr.1
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [runMaxA_zero]
    omega
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    subst hk
    have h1 : runMaxA p m U hA k < y := hr.2 k (Nat.lt_succ_self k)
    have h2 : runMaxA p m U hA (k + 1) ≤ runMaxA p m U hA k + 1 := runMaxA_succ_le k
    omega

/-- **At first passage a leader exists**: some walker of `A` sits exactly at `y`. -/
lemma ARMax.exists_pos {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {n : ℕ} (hy : 0 ≤ y) (hr : ARMax p m U hA y n) :
    ∃ j ∈ A, (trajectory p m U n).pos j = y := by
  classical
  have hmax : runMaxA p m U hA n = y := hr.eq hy
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hA (fun j => runMax p m U j n)
  have hMj : runMax p m U j n = y := by
    rw [← hjeq]
    exact hmax
  refine ⟨j, hj, ?_⟩
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j n
  rcases Nat.lt_or_eq_of_le ht with hlt | heq
  · exfalso
    have h1 : (trajectory p m U t).pos j < y :=
      lt_of_le_of_lt ((le_runMax p m U j t).trans (le_runMaxA hj)) (hr.2 t hlt)
    rw [hte, hMj] at h1
    exact lt_irrefl y h1
  · rw [← heq, hte, hMj]

/-- First passage times of the group record are unique. -/
lemma ARMax_unique {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {n n' : ℕ} (h : ARMax p m U hA y n) (h' : ARMax p m U hA y n') : n = n' := by
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exfalso
    have h1 : runMaxA p m U hA n < y := h'.2 n hlt
    have h2 : y ≤ runMaxA p m U hA n := h.1
    omega
  · exact heq
  · exfalso
    have h1 : runMaxA p m U hA n' < y := h.2 n' hgt
    have h2 : y ≤ runMaxA p m U hA n' := h'.1
    omega

/-- **No future leakage**: the group first-passage event at time `n` is `enlFilt p m n`-measurable. -/
theorem measurableSet_ARMax (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) : MeasurableSet[enlFilt p m n] {U : Array N | ARMax p m U hA y n} := by
  refine measurableSet_enl_of_prefPred (n := n) (P := fun γ =>
    y ≤ runMaxAExt hA γ n ∧ ∀ t < n, runMaxAExt hA γ t < y) ?_
  intro γ U hU
  have h1 : runMaxA p m U hA n = runMaxAExt hA γ n := runMaxA_eq_ext hU le_rfl
  have h2 : ∀ t < n, runMaxA p m U hA t = runMaxAExt hA γ t :=
    fun t ht => runMaxA_eq_ext hU ht.le
  simp only [Set.mem_ofPred_eq, ARMax, h1]
  refine and_congr Iff.rfl ?_
  exact forall_congr' fun t => forall_congr' fun ht => by rw [h2 t ht]

/-! ## 4. First passage times as `WithTop ℕ`-valued functions -/

/-- The least `n` with `P n`, as an element of `WithTop ℕ` (`⊤` if there is none).  Kept
generic so that the (large) predicate is never unfolded below. -/
noncomputable def firstIdx (P : ℕ → Prop) : WithTop ℕ := by
  classical
  exact if h : ∃ n, P n then (Nat.find h : WithTop ℕ) else ⊤

/-- The level sets of `firstIdx`: it equals `n` exactly at the *least* index satisfying `P`. -/
theorem firstIdx_eq_coe_iff {P : ℕ → Prop} {n : ℕ} :
    firstIdx P = (n : WithTop ℕ) ↔ P n ∧ ∀ m < n, ¬ P m := by
  classical
  constructor
  · intro h
    unfold firstIdx at h
    by_cases hh : ∃ n, P n
    · rw [dif_pos hh] at h
      have hnk : Nat.find hh = n := WithTop.coe_inj.mp h
      refine ⟨by rw [← hnk]; exact Nat.find_spec hh, ?_⟩
      intro m hm hP
      have hle : Nat.find hh ≤ m := Nat.find_le hP
      omega
    · rw [dif_neg hh] at h
      exact absurd h (by simp)
  · rintro ⟨hP, hmin⟩
    unfold firstIdx
    by_cases hh : ∃ n, P n
    · rw [dif_pos hh]
      have hspec : P (Nat.find hh) := Nat.find_spec hh
      have hle : Nat.find hh ≤ n := Nat.find_le hP
      have hnle : n ≤ Nat.find hh := by
        by_contra hcon
        exact hmin (Nat.find hh) (by omega) hspec
      exact WithTop.coe_inj.mpr (le_antisymm hle hnle)
    · exact absurd ⟨n, hP⟩ hh

/-- `{firstIdx P ≤ n} = {∃ k ≤ n, P k}`. -/
theorem firstIdx_le_iff {P : ℕ → Prop} {n : ℕ} :
    firstIdx P ≤ (n : WithTop ℕ) ↔ ∃ k ≤ n, P k := by
  classical
  constructor
  · intro h
    unfold firstIdx at h
    by_cases hh : ∃ n, P n
    · rw [dif_pos hh] at h
      exact ⟨Nat.find hh, WithTop.coe_le_coe.mp h, Nat.find_spec hh⟩
    · rw [dif_neg hh] at h
      exact absurd h (by simp)
  · rintro ⟨k, hk, hP⟩
    unfold firstIdx
    by_cases hh : ∃ n, P n
    · rw [dif_pos hh]
      exact WithTop.coe_le_coe.mpr ((Nat.find_le hP).trans hk)
    · exact absurd ⟨k, hP⟩ hh

/-- The paper's `σ_y^A = inf{n ≥ 0 : R_n^A = y}`, with value `⊤` when the record never reaches
`y`. -/
noncomputable def sigmaA (p : ℝ) (m : ℕ) (U : Array N) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y : ℤ) : WithTop ℕ :=
  firstIdx fun n => ARMax p m U hA y n

/-- **The level sets of `σ_y^A`**: `σ_y^A = n` exactly when the group record first reaches `y`
at time `n`. -/
theorem sigmaA_eq_coe_iff {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {n : ℕ} : sigmaA p m U hA y = (n : WithTop ℕ) ↔ ARMax p m U hA y n := by
  rw [sigmaA, firstIdx_eq_coe_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact h1
  · intro h
    refine ⟨h, ?_⟩
    rintro m hm ⟨hge, hm2⟩
    have hlt := h.2 m hm
    omega

/-- Characterisation of `{σ_y^A ≤ n}`. -/
theorem sigmaA_le_iff {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {n : ℕ} :
    sigmaA p m U hA y ≤ (n : WithTop ℕ) ↔ ∃ k ≤ n, ARMax p m U hA y k :=
  firstIdx_le_iff

/-- **The paper's `σ_y^A` is a stopping time of the enlarged filtration.**  Together with
`GammaStopped.stopped_wordRun_mass_ge_isStoppingTime` this closes the interface residue recorded
in `GAMMA_TRIAL.md` (`σ_y^A` was only a hypothesis there). -/
theorem isStoppingTime_sigmaA (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) :
    IsStoppingTime (enlFilt (N := N) p m) (fun U => sigmaA p m U hA y) := by
  intro n
  have hgoal : MeasurableSet[enlFilt p m n]
      (⋃ k ∈ Finset.range (n + 1), {U : Array N | ARMax p m U hA y k}) :=
    Finset.measurableSet_biUnion _ (fun k hk =>
      (enlFilt (N := N) p m).mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) _
        (measurableSet_ARMax p m k A hA y))
  have hset :
      (⋃ k ∈ Finset.range (n + 1), {U : Array N | ARMax p m U hA y k}) =
        {ω : Array N | (fun U => sigmaA p m U hA y) ω ≤ (n : WithTop ℕ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    rw [sigmaA_le_iff]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, Nat.lt_succ_iff.mp hk, h⟩,
      fun ⟨k, hk, h⟩ => ⟨k, Nat.lt_succ_of_le hk, h⟩⟩
  exact hset ▸ hgoal

/-! ## 5. Positions read off the prefix -/

/-- On a piece, the position at any time `s ≤ n` is read off the prefix. -/
lemma pos_ext_eq {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N} (hU : U ∈ prefAgree p m γ)
    {s : ℕ} (hs : s ≤ n) (i : Fin N) : (trajectory p m U s).pos i = ext γ s i := by
  rw [ext_of_lt γ (by omega)]
  exact congrFun (hU ⟨s, by omega⟩) i

/-! ## 6. The leader at the record -/

/-- `iy ∈ A` is the *smallest* member of `A` sitting at `y` at time `n` (the paper's `i_y`). -/
def IsLeader (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (y : ℤ) (n : ℕ)
    (iy : Fin N) : Prop :=
  (trajectory p m U n).pos iy = y ∧ ∀ j ∈ A, j < iy → (trajectory p m U n).pos j ≠ y

theorem measurableSet_leader (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (y : ℤ)
    (iy : Fin N) : MeasurableSet[enlFilt p m n] {U : Array N | IsLeader p m U A y n iy} := by
  refine measurableSet_enl_of_prefPred (n := n) (P := fun γ =>
    ext γ n iy = y ∧ ∀ j ∈ A, j < iy → ext γ n j ≠ y) ?_
  intro γ U hU
  have h2 : ∀ j, (trajectory p m U n).pos j = ext γ n j := fun j => pos_ext_eq hU le_rfl j
  simp only [IsLeader, Set.mem_ofPred_eq, h2]

/-- **At the first passage the leader exists**: there is a member of `A` sitting at `y` at which
all smaller members of `A` sit strictly away from `y`. -/
lemma exists_leader (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (hA : A.Nonempty)
    {y : ℤ} (hy : 0 ≤ y) {n : ℕ} (hAR : ARMax p m U hA y n) :
    ∃ iy, iy ∈ A ∧ IsLeader p m U A y n iy := by
  classical
  obtain ⟨j, hj, hjy⟩ := ARMax.exists_pos (hA := hA) hy hAR
  set S : Finset (Fin N) := A.filter fun j => (trajectory p m U n).pos j = y with hS
  have hSne : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hjy⟩⟩
  refine ⟨S.min' hSne, (Finset.mem_filter.mp (S.min'_mem hSne)).1, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (S.min'_mem hSne)).2
  · intro k hkA hklt hcon
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨hkA, hcon⟩
    have hle : S.min' hSne ≤ k := S.min'_le k hkS
    omega

/-! ## 7. Measurability of the paper's trial word at the level it ends -/

/-- The prescribed `k`-step word is measurable at the level `n + k` at which it ends. -/
theorem measurableSet_wordRun_enl (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (iy : Fin N)
    (k : ℕ) : MeasurableSet[enlFilt p m (n + k)] (wordRun p m n A iy k) := by
  induction k with
  | zero => rw [wordRun_zero]; exact MeasurableSet.univ
  | succ k ih =>
      rw [wordRun_succ]
      refine MeasurableSet.inter ((enlFilt (N := N) p m).mono (by omega) _ ih) ?_
      refine MeasurableSet.iInter fun i => ?_
      refine measurableSet_enl_of_prefPred (n := n + (k + 1)) (P := fun γ =>
        ext γ (n + (k + 1)) i.1 = ext γ n i.1 +
          (if i.1 = iy then (((k + 1) % 2 : ℕ) : ℤ) else -(((k + 1) : ℕ) : ℤ))) ?_
      intro γ U hU
      have h1 : (trajectory p m U (n + (k + 1))).pos i.1 = ext γ (n + (k + 1)) i.1 :=
        pos_ext_eq hU (by omega) i.1
      have h2 : (trajectory p m U n).pos i.1 = ext γ n i.1 := pos_ext_eq hU (by omega) i.1
      simp only [Set.mem_ofPred_eq, h1, h2]

/-! ## 8. The paper's trial event `Γ_y^A` and its stopped conditional mass -/

/-- The paper's `Γ_y^A`: at the first passage of the group record to `y`, the smallest leader
alternates `y, y+1, …` for `2m-1` steps while every other member of `A` steps down one site. -/
noncomputable def GammaSet (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty) (y : ℤ) :
    Set (Array N) :=
  ⋃ n : ℕ, ⋃ iy ∈ A,
    ({U : Array N | ARMax p m U hA y n} ∩ {U : Array N | IsLeader p m U A y n iy}) ∩
      wordRun p m n A iy (2 * m - 1)

/-- The piece of `Γ_y^A` cut by the first-passage level `n` and the label `iy`. -/
noncomputable def GammaPiece (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (y : ℤ)
    (n : ℕ) (iy : Fin N) : Set (Array N) :=
  {U : Array N | ARMax p m U hA y n} ∩ {U : Array N | IsLeader p m U A y n iy}

lemma measurableSet_GammaPiece (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) (iy : Fin N) : MeasurableSet[enlFilt p m n] (GammaPiece p m A hA y n iy) :=
  (measurableSet_ARMax p m n A hA y).inter (measurableSet_leader p m n A y iy)

lemma GammaPiece_disjoint {p : ℝ} {m n : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {y : ℤ}
    {iy iy' : Fin N} (hiy : iy ∈ A) (hiy' : iy' ∈ A) (h : iy ≠ iy') :
    Disjoint (GammaPiece p m A hA y n iy) (GammaPiece p m A hA y n iy') := by
  rw [Set.disjoint_left]
  rintro U ⟨-, h1, h2⟩ ⟨-, h3, h4⟩
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact (h4 iy hiy hlt) h1
  · exact (h2 iy' hiy' hgt) h3

/-- **The paper's `(trialp)` in the stopped conditional form used by the residue-class
martingale.**  For every event `H` of the enlarged history at the first-passage level `n`, the
mass of `H ∩ {σ_y^A = n} ∩ Γ_y^A` is at least `(1-p)^{(2m-1)|A|}` times the mass of
`H ∩ {σ_y^A = n}`.  No independence, boundedness or freshness hypothesis is used. -/
theorem GammaSet_cond_mass (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (A : Finset (Fin N))
    (hA : A.Nonempty) {y : ℤ} (hy : 0 ≤ y) (n : ℕ) {H : Set (Array N)}
    (hH : MeasurableSet[enlFilt p m n] H) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
        arrayMeasure N (H ∩ {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)}) ≤
      arrayMeasure N (H ∩ GammaSet p m hA y) := by
  classical
  have hsig : {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)} =
      {U : Array N | ARMax p m U hA y n} := by
    ext U
    exact sigmaA_eq_coe_iff
  rw [hsig]
  -- the pieces of the enlarged-history event at level `n`
  let P : Fin N → Set (Array N) := fun iy => H ∩ GammaPiece p m A hA y n iy
  -- and the part of `Γ` on which the trial succeeds
  let Q : Fin N → Set (Array N) := fun iy => P iy ∩ wordRun p m n A iy (2 * m - 1)
  have hPQ : ∀ iy ∈ A,
      ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) * arrayMeasure N (P iy) ≤
        arrayMeasure N (Q iy) := by
    intro iy hiy
    exact wordRun_mass_ge p hp0 hp1 m n A iy (2 * m - 1)
      (hH.inter (measurableSet_GammaPiece p m n A hA y iy))
  have hQsub : ∀ iy ∈ A, Q iy ⊆ H ∩ GammaSet p m hA y := by
    intro iy hiy U hU
    exact ⟨hU.1.1, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨iy, Set.mem_iUnion.mpr
      ⟨hiy, ⟨hU.1.2.1, hU.1.2.2⟩, hU.2⟩⟩⟩⟩
  have hQdisj : (A : Set (Fin N)).PairwiseDisjoint Q := by
    intro iy hiy iy' hiy' hne
    exact Disjoint.mono (show Q iy ⊆ GammaPiece p m A hA y n iy from fun U hU => hU.1.2)
      (show Q iy' ⊆ GammaPiece p m A hA y n iy' from fun U hU => hU.1.2)
      (GammaPiece_disjoint hiy hiy' hne)
  have hQmeas : ∀ iy ∈ A, MeasurableSet (Q iy) := fun iy hiy =>
    enlMeas_le p m (n + (2 * m - 1)) (Q iy) <|
      MeasurableSet.inter
        ((enlFilt (N := N) p m).mono (by omega) _ (hH.inter (measurableSet_GammaPiece p m n A hA y iy)))
        (measurableSet_wordRun_enl p m n A iy (2 * m - 1))
  have hQsum : arrayMeasure N (⋃ iy ∈ A, Q iy) = ∑ iy ∈ A, arrayMeasure N (Q iy) :=
    measure_biUnion_finset hQdisj hQmeas
  -- the pieces `P iy` are disjoint and cover `H ∩ {σ_y = n}`
  have hPdisj : (A : Set (Fin N)).PairwiseDisjoint P := by
    intro iy hiy iy' hiy' hne
    exact Disjoint.mono (show P iy ⊆ GammaPiece p m A hA y n iy from fun U hU => hU.2)
      (show P iy' ⊆ GammaPiece p m A hA y n iy' from fun U hU => hU.2)
      (GammaPiece_disjoint hiy hiy' hne)
  have hPcover : (⋃ iy ∈ A, P iy) = H ∩ {U : Array N | ARMax p m U hA y n} := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion₂_subset fun iy _ => ?_
      exact Set.inter_subset_inter_right _ Set.inter_subset_left
    · rintro U ⟨hU, hAR⟩
      obtain ⟨j0, hj0A, hj0lead⟩ := exists_leader p m U A hA hy hAR
      exact Set.mem_iUnion.mpr ⟨j0, Set.mem_iUnion.mpr ⟨hj0A, hU, hAR, hj0lead⟩⟩
  have hPsum : arrayMeasure N (⋃ iy ∈ A, P iy) = ∑ iy ∈ A, arrayMeasure N (P iy) :=
    measure_biUnion_finset hPdisj (fun iy _ =>
      enlMeas_le p m n _ (hH.inter (measurableSet_GammaPiece p m n A hA y iy)))
  calc ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
        arrayMeasure N (H ∩ {U : Array N | ARMax p m U hA y n})
      = ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
          ∑ iy ∈ A, arrayMeasure N (P iy) := by rw [← hPcover, hPsum]
    _ = ∑ iy ∈ A, ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
          arrayMeasure N (P iy) := Finset.mul_sum _ _ _
    _ ≤ ∑ iy ∈ A, arrayMeasure N (Q iy) := Finset.sum_le_sum hPQ
    _ = arrayMeasure N (⋃ iy ∈ A, Q iy) := hQsum.symm
    _ ≤ arrayMeasure N (H ∩ GammaSet p m hA y) :=
        measure_mono (Set.iUnion₂_subset hQsub)

/-! ## 9. Nesting: `σ_y^A + k ≤ σ_{y+k}^A`, and `Γ_y^A ∈ F_{σ_{y+2m}^A}` -/

/-- **Telescoping the record**: `R_b^A ≤ R_a^A + (b - a)`. -/
lemma runMaxA_telescope {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {a b : ℕ} (h : a ≤ b) :
    runMaxA p m U hA b ≤ runMaxA p m U hA a + (((b - a : ℕ)) : ℤ) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ c hc ih =>
      have h1 : runMaxA p m U hA (c + 1) ≤ runMaxA p m U hA c + 1 := runMaxA_succ_le c
      have h2 : (((c + 1) - a : ℕ) : ℤ) = ((c - a : ℕ) : ℤ) + 1 := by
        have h3 : c + 1 - a = (c - a) + 1 := by omega
        rw [h3]
        push_cast
        ring
      omega

/-- The record never exceeds the current time. -/
lemma runMaxA_le_time {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    (n : ℕ) : runMaxA p m U hA n ≤ (n : ℤ) := by
  have h1 : runMaxA p m U hA n ≤ runMaxA p m U hA 0 + (((n - 0 : ℕ)) : ℤ) :=
    runMaxA_telescope (Nat.zero_le n)
  rw [runMaxA_zero, Nat.sub_zero] at h1
  simpa using h1

/-- If the record is at level `y` by time `K` then `σ_y^A ≤ K`. -/
lemma sigmaA_le_of_record_le {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} {K : ℕ} (hex : ∃ k ≤ K, y ≤ runMaxA p m U hA k) :
    sigmaA p m U hA y ≤ (K : WithTop ℕ) := by
  classical
  have hne : ∃ k, k ≤ K ∧ y ≤ runMaxA p m U hA k := hex
  have hspec : Nat.find hne ≤ K ∧ y ≤ runMaxA p m U hA (Nat.find hne) := Nat.find_spec hne
  have har : ARMax p m U hA y (Nat.find hne) := by
    refine ⟨hspec.2, fun s hs => ?_⟩
    by_contra hcon
    exact Nat.find_min hne hs ⟨le_trans (le_of_lt hs) hspec.1, not_lt.mp hcon⟩
  exact sigmaA_le_iff.mpr ⟨Nat.find hne, hspec.1, har⟩

/-- **Nesting in the level**: if the record first reaches `y + k` at time `n`, then it first
reached `y` at a time `j ≤ n - k`.  This is the paper's `σ_{y+k}^A ≥ σ_y^A + k`. -/
theorem sigmaA_nesting {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} (hy : 0 ≤ y) {k n : ℕ} (h : sigmaA p m U hA (y + (k : ℤ)) = (n : WithTop ℕ)) :
    ∃ j ≤ n - k, sigmaA p m U hA y = (j : WithTop ℕ) := by
  have hAR : ARMax p m U hA (y + (k : ℤ)) n := sigmaA_eq_coe_iff.mp h
  have hyk : (0 : ℤ) ≤ y + (k : ℤ) := by positivity
  have hRn : runMaxA p m U hA n = y + (k : ℤ) := hAR.eq hyk
  have hbound : runMaxA p m U hA n ≤ (n : ℤ) := runMaxA_le_time n
  have hkn : k ≤ n := by
    have : ((k : ℕ) : ℤ) ≤ (n : ℤ) := by
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
      omega
    exact_mod_cast this
  have htelescope : runMaxA p m U hA n ≤
      runMaxA p m U hA (n - k) + (((n - (n - k) : ℕ)) : ℤ) := runMaxA_telescope (by omega)
  have hsub : ((n - (n - k) : ℕ) : ℤ) = (k : ℤ) := by
    have h3 : n - (n - k) = k := by omega
    rw [h3]
  rw [hsub, hRn] at htelescope
  have hy1 : y ≤ runMaxA p m U hA (n - k) := by omega
  have hle : sigmaA p m U hA y ≤ ((n - k : ℕ) : WithTop ℕ) :=
    sigmaA_le_of_record_le ⟨n - k, le_rfl, hy1⟩
  rcases eq_or_ne (sigmaA p m U hA y) ⊤ with htop | hfin
  · rw [htop] at hle
    exact absurd hle (by simp)
  · obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hfin
    refine ⟨j, ?_, hj.symm⟩
    rw [← hj] at hle
    exact WithTop.coe_le_coe.mp hle

/-- The paper's `σ_{y+2m}^A ≥ σ_y^A + 2m`, in the only form used below. -/
theorem sigmaA_nesting_two_m (p : ℝ) (m : ℕ) {U : Array N} {A : Finset (Fin N)}
    {hA : A.Nonempty} {y : ℤ} (hy : 0 ≤ y) {n : ℕ}
    (h : sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ)) :
    ∃ j ≤ n - 2 * m, sigmaA p m U hA y = (j : WithTop ℕ) :=
  sigmaA_nesting hy h

/-! ### Reading `ARMax`, `IsLeader` and `wordRun` off a prefix at different levels -/

lemma ARMax_iff_ext {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {A : Finset (Fin N)} {hA : A.Nonempty} {y : ℤ} {t : ℕ}
    (ht : t ≤ n) :
    ARMax p m U hA y t ↔ (y ≤ runMaxAExt hA γ t ∧ ∀ s < t, runMaxAExt hA γ s < y) := by
  have h1 : runMaxA p m U hA t = runMaxAExt hA γ t := runMaxA_eq_ext hU ht
  have h2 : ∀ s < t, runMaxA p m U hA s = runMaxAExt hA γ s :=
    fun s hs => runMaxA_eq_ext hU (le_trans (le_of_lt hs) ht)
  simp only [ARMax, h1]
  exact and_congr Iff.rfl (forall_congr' fun s => forall_congr' fun hs => by rw [h2 s hs])

lemma leader_iff_ext {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (A : Finset (Fin N)) {y : ℤ} {t : ℕ} (ht : t ≤ n)
    (iy : Fin N) :
    IsLeader p m U A y t iy ↔ (ext γ t iy = y ∧ ∀ k ∈ A, k < iy → ext γ t k ≠ y) := by
  have h2 : ∀ k, (trajectory p m U t).pos k = ext γ t k := fun k => pos_ext_eq hU ht k
  simp only [IsLeader, h2]

lemma wordRun_iff_ext {p : ℝ} {m n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) {A : Finset (Fin N)} {iy : Fin N} {j k : ℕ}
    (hk : j + k ≤ n) :
    U ∈ wordRun p m j A iy k ↔
      (∀ u ≤ k, ∀ i ∈ A, ext γ (j + u) i = ext γ j i +
        (if i = iy then (((u % 2 : ℕ)) : ℤ) else -((u : ℕ) : ℤ))) := by
  simp only [wordRun, Set.mem_ofPred_eq]
  refine forall_congr' fun u => forall_congr' fun hu => forall_congr' fun i =>
    forall_congr' fun _ => ?_
  rw [pos_ext_eq hU (by omega) i, pos_ext_eq hU (by omega) i]

/-- One slice of `{σ_{y+2m}^A = n} ∩ Γ_y^A` at the first-passage level `j` and label `iy`. -/
noncomputable def GammaSlice (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (y : ℤ)
    (n j : ℕ) (iy : Fin N) : Set (Array N) :=
  {U : Array N | ARMax p m U hA (y + ((2 * m : ℕ) : ℤ)) n} ∩ GammaPiece p m A hA y j iy ∩
    wordRun p m j A iy (2 * m - 1)

lemma measurableSet_GammaSlice (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (y : ℤ) {j : ℕ} (hj : j + 2 * m ≤ n) (iy : Fin N) :
    MeasurableSet[enlFilt p m n] (GammaSlice p m A hA y n j iy) := by
  refine measurableSet_enl_of_prefPred (n := n) (P := fun γ =>
    (y + ((2 * m : ℕ) : ℤ) ≤ runMaxAExt hA γ n ∧
        ∀ s < n, runMaxAExt hA γ s < y + ((2 * m : ℕ) : ℤ)) ∧
      ((y ≤ runMaxAExt hA γ j ∧ ∀ s < j, runMaxAExt hA γ s < y) ∧
        (ext γ j iy = y ∧ ∀ k ∈ A, k < iy → ext γ j k ≠ y)) ∧
      (∀ u ≤ 2 * m - 1, ∀ i ∈ A, ext γ (j + u) i = ext γ j i +
        (if i = iy then (((u % 2 : ℕ)) : ℤ) else -((u : ℕ) : ℤ)))) ?_
  intro γ U hU
  have hAn := ARMax_iff_ext hU (A := A) (hA := hA) (y := y + ((2 * m : ℕ) : ℤ)) (t := n) le_rfl
  have hAj := ARMax_iff_ext hU (A := A) (hA := hA) (y := y) (t := j) (by omega)
  have hL := leader_iff_ext hU A (y := y) (t := j) (by omega) iy
  have hW := wordRun_iff_ext hU (A := A) (iy := iy) (j := j) (k := 2 * m - 1) (by omega)
  simp only [GammaSlice, GammaPiece, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hAn, hAj, hL, hW]
  tauto

/-- **`Γ_y^A ∈ F_{σ_{y+2m}^A}`**: the trial at level `y` is measurable at the next passage of the
same residue class.  This is the filtration nesting the paper's residue-class martingale uses. -/
theorem measurableSet_GammaSet_next (p : ℝ) (m : ℕ) (n : ℕ) (A : Finset (Fin N))
    (hA : A.Nonempty) (y : ℤ) (hy : 0 ≤ y) :
    MeasurableSet[enlFilt p m n]
      ({U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ)} ∩
        GammaSet p m hA y) := by
  classical
  have hsig : {U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ)} =
      {U : Array N | ARMax p m U hA (y + ((2 * m : ℕ) : ℤ)) n} := by
    ext U
    exact sigmaA_eq_coe_iff
  rw [hsig]
  rcases lt_or_ge n (2 * m) with hsmall | hbig
  · -- below `2m` the first passage to `y + 2m` cannot have happened yet
    have hempty : {U : Array N | ARMax p m U hA (y + ((2 * m : ℕ) : ℤ)) n} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr (fun U hAR => ?_)
      have hyk : (0 : ℤ) ≤ y + ((2 * m : ℕ) : ℤ) := by positivity
      have h1 : runMaxA p m U hA n = y + ((2 * m : ℕ) : ℤ) := hAR.eq hyk
      have h2 : runMaxA p m U hA n ≤ (n : ℤ) := runMaxA_le_time n
      have h3 : ((n : ℕ) : ℤ) < (((2 * m : ℕ)) : ℤ) := by exact_mod_cast hsmall
      omega
    rw [hempty, Set.empty_inter]
    exact @MeasurableSet.empty (Array N) (enlFilt p m n)
  · have hEq : {U : Array N | ARMax p m U hA (y + ((2 * m : ℕ) : ℤ)) n} ∩ GammaSet p m hA y =
        ⋃ j ∈ Finset.range (n - 2 * m + 1), ⋃ iy ∈ A, GammaSlice p m A hA y n j iy := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro U hU
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, GammaSet] at hU
        obtain ⟨hAR2, j, iy, hiy, hpiece, hWord⟩ := hU
        obtain ⟨hARj, hLead⟩ := hpiece
        have hnest := sigmaA_nesting_two_m p m hy (n := n) (sigmaA_eq_coe_iff.mpr hAR2)
        obtain ⟨j', hj'le, hj'eq⟩ := hnest
        have hjeq : j' = j := by
          rw [sigmaA_eq_coe_iff.mpr hARj] at hj'eq
          exact WithTop.coe_inj.mp hj'eq.symm
        subst j'
        refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨?_, Set.mem_iUnion.mpr
          ⟨iy, Set.mem_iUnion.mpr ⟨hiy, ?_⟩⟩⟩⟩
        · exact Finset.mem_range.mpr (by omega)
        · exact ⟨⟨hAR2, hARj, hLead⟩, hWord⟩
      · rintro U hU
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, GammaSet, GammaSlice,
          GammaPiece] at hU ⊢
        obtain ⟨j, _hjmem, iy, hiy, hslice, hWord⟩ := hU
        obtain ⟨hAR2, hARj, hLead⟩ := hslice
        exact ⟨hAR2, j, iy, hiy, ⟨⟨hARj, hLead⟩, hWord⟩⟩
    rw [hEq]
    refine Finset.measurableSet_biUnion _ (fun j hj => ?_)
    refine Finset.measurableSet_biUnion _ (fun iy _ => ?_)
    exact measurableSet_GammaSlice p m n A hA y (by
      have := Finset.mem_range.mp hj
      omega) iy

/-- **The paper's `(trialp)` at a single level** (the `H = univ` case of
`GammaSet_cond_mass`): unconditionally, the trial at the level `n` of `σ_y^A` succeeds with
conditional-probability factor `(1-p)^{(2m-1)|A|}`. -/
theorem GammaSet_mass_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y : ℤ} (hy : 0 ≤ y) (n : ℕ) :
    ENNReal.ofReal (1 - p) ^ ((2 * m - 1) * A.card) *
        arrayMeasure N {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)} ≤
      arrayMeasure N ({U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)} ∩ GammaSet p m hA y) := by
  have hH : MeasurableSet[enlFilt p m n]
      {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)} := by
    have hEq : {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)} =
        {U : Array N | ARMax p m U hA y n} := by
      ext U
      exact sigmaA_eq_coe_iff
    rw [hEq]
    exact measurableSet_ARMax p m n A hA y
  have h := GammaSet_cond_mass p hp0 hp1 m A hA hy n
    (H := {U : Array N | sigmaA p m U hA y = (n : WithTop ℕ)}) hH
  simpa only [Set.inter_self] using h

/-- **The trial times are separated along a residue class**: the trial at the level `y + 2m`
starts at least `2m` steps after the trial at the level `y`.  In particular the finishing times
`σ_y^A + 2m - 1` are strictly increasing along `y ≡ q (mod 2m)`, which is what makes the
residue-class sum of the trial indicators a martingale with increments of size at most one. -/
theorem sigmaA_trial_sep {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {y : ℤ} (hy : 0 ≤ y) {j n : ℕ}
    (h1 : sigmaA p m U hA y = (j : WithTop ℕ))
    (h2 : sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ)) :
    j + 2 * m ≤ n := by
  obtain ⟨j', hj'le, hj'eq⟩ := sigmaA_nesting_two_m p m hy h2
  rw [hj'eq] at h1
  have hjj : j' = j := WithTop.coe_inj.mp h1
  subst j'
  have hAR : ARMax p m U hA (y + ((2 * m : ℕ) : ℤ)) n := sigmaA_eq_coe_iff.mp h2
  have hyk : (0 : ℤ) ≤ y + ((2 * m : ℕ) : ℤ) := by positivity
  have hRn : runMaxA p m U hA n = y + ((2 * m : ℕ) : ℤ) := hAR.eq hyk
  have hbound : runMaxA p m U hA n ≤ (n : ℤ) := runMaxA_le_time n
  have hmn : 2 * m ≤ n := by
    have hle : (((2 * m : ℕ)) : ℤ) ≤ (n : ℤ) := by omega
    exact_mod_cast hle
  omega

end Swarming.Enl


