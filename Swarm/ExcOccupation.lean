/-
# Excitation occupation on the actual array: a deterministic lower bound,
# the drift-martingale tail, and the swarm-stall reduction

## What this file proves

The frontier file `Swarm/RecordAdvanceWindow.lean` isolates the one
missing input of the record-advance (`timeLag` / `swarmStall`) tail:

  "The missing input must therefore be a lower bound on the *excitation surplus*
   of the record-fibre walker, i.e. on the number of its window steps that are
   excited, and no such bound is proved or assumed here."

This file supplies two of the three ingredients and reduces the third to a
single, explicitly stated deterministic occupation statement.

### 1. A deterministic, unconditional excitation-occupation bound (part 1 below)

For the **actual** interacting array, at **every** time and for **every** array:

    N  ≤  2 * m  +  ∑_i  1{walker i is excited at time t}

i.e. the swarm's total excitation occupation is at least `N - 2m` per time step.
This is *not* a probabilistic statement and involves no marks, no independence
and no invariant law.  The mechanism is the paper's two-sided local-time count:
a walker sitting at a nonnegative level `y` is excited as soon as `m` other
walkers sit at levels `≥ y` (each of them has then visited `y` at least once),
and symmetrically at nonpositive levels.  Summing over the window gives

    (N - 2m) * W  ≤  ∑_i  (excited steps of walker i in the window).

Consequently, for `N > 2m` **some** walker collects a positive linear number of
excited steps in every window, uniformly in the window's starting time and in
the record level.

### 2. The drift-martingale tail on the enlarged filtration (part 2)

The paper's martingale `M_n^i = X_n^i - (2p-1) ∑_t 1{excited}` is a genuine
martingale difference sequence for the enlarged filtration `enlFilt p m`
(`condExp_inc_enl`), with increments bounded by `2`.  Azuma–Hoeffding therefore
gives the two-sided tail

    P(|M_{n+W}^i - M_n^i| ≥ ε)  ≤  2 exp(-ε² / (16 W)),

uniform in the starting time `n` and in every other parameter.  This is a real
rate, not a limsup, and it is not conditional on any seed law.

### 3. The swarm-stall reduction (part 3)

Combining 1 and 2:

    swarmStall ⊆  { defect at the fibre ≥ c L / (2N) }
                  ∪  ⋃_i { |M^i jump| ≥ c L / (2N) },

    c := (2p-1) (N - 2m) T - N B .

Part 2 starts at a fixed time, whereas this displacement starts at the random
record clock.  The genuinely proved quantitative consequence is therefore

    P(stall ∩ {τ_r ≤ K})
      ≤ P(defect ≥ cL/(2N)) + (K+1) N · 2 exp(-c² L / (64 T N²)),

under the explicit positivity and window-size hypotheses of
`stall_measure_le_trunc`.  A record-clock-tail bound is still required to turn
this into a full stall profile; it is **not** hidden by setting `K` or by
interpreting the fixed-start Azuma bound as optional stopping.  The
excitation surplus has been removed from the ledger.  The bound bites for
`N > 2m` with `T` large relative to `N B / (N - 2m)`.

Nothing here asserts tightness, an invariant law, regeneration, `Ballistic` or
`MainClaim`.
-/
import Swarm.ActualRecordFiltration
import Swarm.EnlDrift
import Swarm.Azuma
import Swarm.RecordDefect

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open RecordDefect

namespace ExcOcc

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 0. One-step geometry of the actual trajectory -/

/-- Every step of walker `i` of the actual interacting trajectory has length exactly one. -/
theorem traj_step (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + 1 ∨
      (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  rcases Enl.drivenStep_cases (U (i, (trajectory p m U n).pos i,
      (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
      (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i))
    with h | h <;> rw [h] <;> omega

/-- Unit step bound in the form used by the discrete intermediate value lemma. -/
theorem traj_step_abs (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    |(trajectory p m U (n + 1)).pos i - (trajectory p m U n).pos i| ≤ 1 := by
  rcases traj_step p m U i n with h | h <;> rw [h] <;> norm_num

/-- Walker positions at time zero all vanish. -/
@[simp] theorem traj_pos_zero (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    (trajectory p m U 0).pos i = 0 := by
  rw [trajectory_zero]; exact initial_pos i

/-! ## 1. The deterministic excitation occupation bound -/

/-- **Discrete intermediate value property.**  A path with steps of length at most one
that starts weakly below `y` and ends weakly above `y` hits `y`. -/
theorem exists_hit_of_le_of_le {X : ℕ → ℤ} (hstep : ∀ k, |X (k + 1) - X k| ≤ 1)
    {a b : ℕ} (hab : a ≤ b) {y : ℤ} (ha : X a ≤ y) (hb : y ≤ X b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ X c = y := by
  classical
  have hex : ∃ c, a ≤ c ∧ y ≤ X c := ⟨b, hab, hb⟩
  have h₁ : a ≤ Nat.find hex := (Nat.find_spec hex).1
  have h₂ : y ≤ X (Nat.find hex) := (Nat.find_spec hex).2
  have h₃ : Nat.find hex ≤ b := Nat.find_le ⟨hab, hb⟩
  refine ⟨Nat.find hex, h₁, h₃, ?_⟩
  by_contra hne
  have hyx : y < X (Nat.find hex) := lt_of_le_of_ne h₂ (Ne.symm hne)
  have hac : a < Nat.find hex := by
    rcases lt_or_eq_of_le h₁ with h | h
    · exact h
    · exfalso
      have : X a = X (Nat.find hex) := congrArg X h
      linarith
  have hpos : 0 < Nat.find hex := lt_of_le_of_lt (Nat.zero_le a) hac
  have hne0 : Nat.find hex ≠ 0 := by omega
  have hdlt : Nat.find hex - 1 < Nat.find hex := Nat.sub_one_lt hne0
  have had : a ≤ Nat.find hex - 1 := by omega
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos hpos
  have hnotmem : ¬ (a ≤ Nat.find hex - 1 ∧ y ≤ X (Nat.find hex - 1)) :=
    Nat.find_min hex hdlt
  have hdy : ¬ y ≤ X (Nat.find hex - 1) := fun h => hnotmem ⟨had, h⟩
  have hstepd := hstep (Nat.find hex - 1)
  rw [hsucc] at hstepd
  have hone : X (Nat.find hex) - X (Nat.find hex - 1) ≤ 1 := (abs_le.1 hstepd).2
  omega

/-- Downward form of the discrete intermediate value property. -/
theorem exists_hit_of_ge_of_ge {X : ℕ → ℤ} (hstep : ∀ k, |X (k + 1) - X k| ≤ 1)
    {a b : ℕ} (hab : a ≤ b) {y : ℤ} (ha : y ≤ X a) (hb : X b ≤ y) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ X c = y := by
  have hstep' : ∀ k, |(fun s => -X s) (k + 1) - (fun s => -X s) k| ≤ 1 := by
    intro k
    have h := hstep k
    have hfun : (fun s => -X s) (k + 1) - (fun s => -X s) k = -(X (k + 1) - X k) := by
      simp only; ring
    rw [hfun, abs_neg]
    exact h
  obtain ⟨c, h1, h2, h3⟩ := exists_hit_of_le_of_le (X := fun s => -X s) hstep' hab
    (by show -X a ≤ -y; linarith) (by show -y ≤ -X b; linarith)
  exact ⟨c, h1, h2, by linarith⟩

/-- The trajectory of walker `j` has unit steps. -/
theorem traj_path_step (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) :
    ∀ k, |(fun s => (trajectory p m U s).pos j) (k + 1) -
      (fun s => (trajectory p m U s).pos j) k| ≤ 1 :=
  fun k => traj_step_abs p m U j k

/-- A walker sitting at a nonnegative level has visited every level between `0` and
its own level strictly more than zero times. -/
theorem one_le_ell_of_ge {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {t : ℕ} {y : ℤ}
    (hy : 0 ≤ y) (h : y ≤ (trajectory p m U t).pos j) :
    1 ≤ (trajectory p m U t).ell j y := by
  obtain ⟨c, -, hc, hval⟩ := exists_hit_of_le_of_le (X := fun s => (trajectory p m U s).pos j)
    (traj_path_step p m U j) (a := 0) (b := t) (y := y) (Nat.zero_le t)
    (by simpa using hy) (by simpa using h)
  rw [ell_eq_localTime]
  have := (localTime_pos_iff (fun s => (trajectory p m U s).pos j) t y).2 ⟨c, hc, hval⟩
  omega

/-- Dual form: a walker sitting at a nonpositive level has visited every level between
its own level and `0`. -/
theorem one_le_ell_of_le {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {t : ℕ} {y : ℤ}
    (hy : y ≤ 0) (h : (trajectory p m U t).pos j ≤ y) :
    1 ≤ (trajectory p m U t).ell j y := by
  obtain ⟨c, -, hc, hval⟩ := exists_hit_of_ge_of_ge (X := fun s => (trajectory p m U s).pos j)
    (traj_path_step p m U j) (a := 0) (b := t) (y := y) (Nat.zero_le t)
    (by simpa using hy) (by simpa using h)
  rw [ell_eq_localTime]
  have := (localTime_pos_iff (fun s => (trajectory p m U s).pos j) t y).2 ⟨c, hc, hval⟩
  omega

/-- The position vector of the actual trajectory at time `t`. -/
def posOf (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) : Fin N → ℤ :=
  fun i => (trajectory p m U t).pos i

/-- **Excitation from walkers above.**  At a nonnegative level, `m` other walkers at
levels `≥ y` excite the walker sitting at `y`. -/
theorem excited_of_ge {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {i : Fin N} {y : ℤ}
    (hy : 0 ≤ y) (hyi : (trajectory p m U t).pos i = y)
    (hcnt : m ≤ ((Finset.univ.erase i).filter
      (fun j => y ≤ (trajectory p m U t).pos j)).card) :
    Excited m (trajectory p m U t).ell i y := by
  classical
  unfold Excited otherVisits
  have hle : ((Finset.univ.erase i).filter
      (fun j => y ≤ (trajectory p m U t).pos j)).card ≤
      ∑ j, if j = i then 0 else (trajectory p m U t).ell j y := by
    have hsub : ((Finset.univ.erase i).filter
        (fun j => y ≤ (trajectory p m U t).pos j)) ⊆
        Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
          else (trajectory p m U t).ell j y) j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        at hj ⊢
      rw [if_neg hj.1]
      exact one_le_ell_of_ge hy (by omega)
    calc ((Finset.univ.erase i).filter
          (fun j => y ≤ (trajectory p m U t).pos j)).card
        ≤ (Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j)).card := Finset.card_le_card hsub
      _ = ∑ j ∈ Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j), 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j),
            (fun j => if j = i then 0 else (trajectory p m U t).ell j y) j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.1 hj).2)
      _ ≤ ∑ j, (fun j => if j = i then 0 else (trajectory p m U t).ell j y) j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => by split_ifs <;> exact Nat.zero_le _)
  omega

/-- **Excitation from walkers below.**  Dual form at nonpositive levels. -/
theorem excited_of_le {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {i : Fin N} {y : ℤ}
    (hy : y ≤ 0) (hyi : (trajectory p m U t).pos i = y)
    (hcnt : m ≤ ((Finset.univ.erase i).filter
      (fun j => (trajectory p m U t).pos j ≤ y)).card) :
    Excited m (trajectory p m U t).ell i y := by
  classical
  unfold Excited otherVisits
  have hle : ((Finset.univ.erase i).filter
      (fun j => (trajectory p m U t).pos j ≤ y)).card ≤
      ∑ j, if j = i then 0 else (trajectory p m U t).ell j y := by
    have hsub : ((Finset.univ.erase i).filter
        (fun j => (trajectory p m U t).pos j ≤ y)) ⊆
        Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
          else (trajectory p m U t).ell j y) j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        at hj ⊢
      rw [if_neg hj.1]
      exact one_le_ell_of_le hy (by omega)
    calc ((Finset.univ.erase i).filter
          (fun j => (trajectory p m U t).pos j ≤ y)).card
        ≤ (Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j)).card := Finset.card_le_card hsub
      _ = ∑ j ∈ Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j), 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => 1 ≤ (fun j => if j = i then 0
            else (trajectory p m U t).ell j y) j),
            (fun j => if j = i then 0 else (trajectory p m U t).ell j y) j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.1 hj).2)
      _ ≤ ∑ j, (fun j => if j = i then 0 else (trajectory p m U t).ell j y) j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => by split_ifs <;> exact Nat.zero_le _)
  omega

/-! ### The cardinal-counting core -/

/-- The predicate "at least `m` others sit at levels `≥` mine". -/
def AbovePred (y : Fin N → ℤ) (m : ℕ) (i : Fin N) : Prop :=
  m ≤ ((Finset.univ.erase i).filter (fun j => y i ≤ y j)).card

/-- **Counting walkers with many walkers above them.**  Among the walkers sitting at
nonnegative levels, all but at most `m` have at least `m` other walkers at levels
`≥` their own. -/
theorem card_le_card_above_add (y : Fin N → ℤ) (m : ℕ) :
    (Finset.univ.filter (fun i => 0 ≤ y i)).card ≤
      (Finset.univ.filter (fun i => 0 ≤ y i ∧ AbovePred y m i)).card + m := by
  classical
  have hgoal : (Finset.univ.filter (fun i => 0 ≤ y i ∧ AbovePred y m i)) =
      (Finset.univ.filter (fun i => 0 ≤ y i)).filter (AbovePred y m) := by
    rw [Finset.filter_filter]
  rw [hgoal]
  set A : Finset (Fin N) := Finset.univ.filter (fun i => 0 ≤ y i) with hA
  set T : Finset (Fin N) := A.filter (fun i => ¬ AbovePred y m i) with hT
  have hpart : A.card = (A.filter (AbovePred y m)).card + T.card := by
    rw [hT, Finset.card_filter_add_card_filter_not]
  rw [hpart]
  suffices hTle : T.card ≤ m by omega
  rcases Finset.eq_empty_or_nonempty T with hemp | hne
  · rw [hemp]; exact Nat.zero_le _
  · obtain ⟨i₀, hi₀T, hmin⟩ := Finset.exists_min_image T y hne
    have hk : ¬ AbovePred y m i₀ := (Finset.mem_filter.1 hi₀T).2
    have hk' : ((Finset.univ.erase i₀).filter (fun j => y i₀ ≤ y j)).card < m := by
      unfold AbovePred at hk; omega
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0] at hk'
      omega
    have hcompl : ((Finset.univ.erase i₀).filter (fun j => y i₀ ≤ y j)).card +
        ((Finset.univ.erase i₀).filter (fun j => ¬ (y i₀ ≤ y j))).card =
        (Finset.univ.erase i₀).card :=
      Finset.card_filter_add_card_filter_not (s := Finset.univ.erase i₀)
        (fun j => y i₀ ≤ y j)
    have herase : (Finset.univ.erase i₀ : Finset (Fin N)).card = N - 1 := by simp
    have hbelow : ((Finset.univ.erase i₀).filter (fun j => ¬ (y i₀ ≤ y j))) =
        (Finset.univ.filter (fun j => y j < y i₀)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hji, hj⟩; omega
      · rintro h; exact ⟨by rintro rfl; omega, by omega⟩
    have hbelowcard : ((Finset.univ.erase i₀).filter (fun j => ¬ (y i₀ ≤ y j))).card =
        (Finset.univ.filter (fun j => y j < y i₀)).card := by rw [hbelow]
    have hNm : N - m ≤ (Finset.univ.filter (fun j => y j < y i₀)).card := by
      have hce : ((Finset.univ.erase i₀).filter (fun j => y i₀ ≤ y j)).card +
          ((Finset.univ.erase i₀).filter (fun j => ¬ (y i₀ ≤ y j))).card = N - 1 := by
        rw [hcompl, herase]
      have h1 : (N - 1) - (m - 1) ≤ (N - 1) -
          ((Finset.univ.erase i₀).filter (fun j => y i₀ ≤ y j)).card :=
        Nat.sub_le_sub_left (by omega) (N - 1)
      have h2 : (N - 1) - ((Finset.univ.erase i₀).filter (fun j => y i₀ ≤ y j)).card =
          ((Finset.univ.erase i₀).filter (fun j => ¬ (y i₀ ≤ y j))).card := by omega
      rw [h2, hbelowcard] at h1
      have h4 : (N - 1) - (m - 1) = N - m := by rw [Nat.sub_sub]; congr 1; omega
      omega
    have hcardle : (Finset.univ.filter (fun j => y j < y i₀)).card ≤ N - T.card := by
      have hsub : (Finset.univ.filter (fun j => y j < y i₀)) ⊆ Finset.univ \ T := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hjT
        have := hmin j hjT
        omega
      calc (Finset.univ.filter (fun j => y j < y i₀)).card
          ≤ (Finset.univ \ T).card := Finset.card_le_card hsub
        _ = N - T.card := by simp [Finset.card_sdiff]
    have hTle' : T.card ≤ N := by
      calc T.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (by simp)
        _ = N := by simp
    have hle2 : N - m ≤ N - T.card := le_trans hNm hcardle
    exact (Nat.sub_le_sub_iff_left (n := T.card) (m := m) (k := N) hTle').1 hle2

/-- **Total excitation occupation per time step.**  At every time the swarm
contributes at least `N - 2m` excited walkers. -/
theorem card_excited_add (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) :
    N ≤ 2 * m + (Finset.univ.filter (fun i =>
      Excited m (trajectory p m U t).ell i ((trajectory p m U t).pos i))).card := by
  classical
  set A : Finset (Fin N) := Finset.univ.filter (fun i => 0 ≤ posOf p m U t i) with hA
  set B : Finset (Fin N) := Finset.univ.filter (fun i => posOf p m U t i ≤ 0) with hB
  set Z : Finset (Fin N) := Finset.univ.filter (fun i => posOf p m U t i = 0) with hZ
  set QA : Finset (Fin N) := Finset.univ.filter (fun i =>
    0 ≤ posOf p m U t i ∧ AbovePred (posOf p m U t) m i) with hQA
  set QB : Finset (Fin N) := Finset.univ.filter (fun i =>
    posOf p m U t i ≤ 0 ∧ AbovePred (fun j => -posOf p m U t j) m i) with hQB
  set E : Finset (Fin N) := Finset.univ.filter (fun i =>
    Excited m (trajectory p m U t).ell i ((trajectory p m U t).pos i)) with hE
  have hQAE : QA ⊆ E := by
    intro i hi
    simp only [hQA, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
    exact excited_of_ge hi.1 rfl hi.2
  have hQBE : QB ⊆ E := by
    intro i hi
    simp only [hQB, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
    have heq : ((Finset.univ.erase i).filter
        (fun j => (trajectory p m U t).pos j ≤ (trajectory p m U t).pos i)) =
        ((Finset.univ.erase i).filter (fun j => -posOf p m U t i ≤ -posOf p m U t j)) := by
      apply Finset.filter_congr
      intro j _
      constructor <;> intro h <;> simp only [posOf] at h ⊢ <;> omega
    refine excited_of_le hi.1 rfl ?_
    rw [heq]
    exact hi.2
  have hAcard : A.card ≤ QA.card + m := card_le_card_above_add (posOf p m U t) m
  have hBcard : B.card ≤ QB.card + m := by
    have h := card_le_card_above_add (fun i => -posOf p m U t i) m
    have e1 : (Finset.univ.filter (fun i => 0 ≤ -posOf p m U t i)) = B := by
      rw [hB]
      apply Finset.filter_congr
      intro i _
      constructor <;> intro h <;> omega
    have e2 : (Finset.univ.filter (fun i => 0 ≤ -posOf p m U t i ∧
        AbovePred (fun j => -posOf p m U t j) m i)) = QB := by
      rw [hQB]
      apply Finset.filter_congr
      intro i _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [e1, e2] at h
    exact h
  have hAunionB : A ∪ B = Finset.univ := by
    rw [hA, hB]
    refine Finset.eq_univ_of_forall (fun i => ?_)
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_total 0 (posOf p m U t i)
  have hAinterB : A ∩ B = Z := by
    rw [hA, hB, hZ]
    ext i
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩
  have hsplit : A.card + B.card = N + Z.card := by
    have h := (Finset.card_union_add_card_inter A B).symm
    rw [hAunionB, hAinterB] at h
    simpa using h
  have hQAsplit : QA.card + QB.card = (QA ∪ QB).card + (QA ∩ QB).card :=
    (Finset.card_union_add_card_inter QA QB).symm
  have hQAZ : (QA ∩ QB).card ≤ Z.card := by
    refine Finset.card_le_card ?_
    intro i hi
    simp only [Finset.mem_inter, hQA, hQB, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hEQ : (QA ∪ QB).card ≤ E.card := Finset.card_le_card (Finset.union_subset hQAE hQBE)
  have hmain : N + Z.card ≤ E.card + Z.card + 2 * m := by
    calc N + Z.card = A.card + B.card := hsplit.symm
      _ ≤ (QA.card + m) + (QB.card + m) := Nat.add_le_add hAcard hBcard
      _ = QA.card + QB.card + 2 * m := by ring
      _ = (QA ∪ QB).card + (QA ∩ QB).card + 2 * m := by rw [hQAsplit]
      _ ≤ E.card + Z.card + 2 * m :=
          Nat.add_le_add (Nat.add_le_add hEQ hQAZ) (le_refl (2 * m))
  omega

/-! ### Window form -/

/-- Number of excited steps of walker `i` in the window `[n, n+W)`. -/
def excOcc (p : ℝ) (m : ℕ) (U : Array N) (n W : ℕ) (i : Fin N) : ℕ :=
  ∑ t ∈ Finset.range W, currentExcited m (U := U) (p := p) (n + t) i

/-- Reformulation of the per-step bound as a sum over walkers. -/
theorem sum_currentExcited_ge (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) :
    N ≤ 2 * m + ∑ i, currentExcited m (U := U) (p := p) t i := by
  have h2 := card_excited_add p m U t
  have h1 : (Finset.univ.filter (fun i =>
      Excited m (trajectory p m U t).ell i ((trajectory p m U t).pos i))).card ≤
      ∑ i, currentExcited m (U := U) (p := p) t i := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ i ∈ Finset.univ.filter (fun i =>
          Excited m (trajectory p m U t).ell i ((trajectory p m U t).pos i)), (1 : ℕ)
        ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            Excited m (trajectory p m U t).ell i ((trajectory p m U t).pos i)),
            currentExcited m (U := U) (p := p) t i := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          unfold currentExcited
          rw [if_pos (Finset.mem_filter.1 hi).2]
      _ ≤ ∑ i, currentExcited m (U := U) (p := p) t i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun i => currentExcited m (U := U) (p := p) t i)
            (Finset.filter_subset _ _) (fun i _ _ => Nat.zero_le _)
  omega

/-- **Deterministic window bound on the swarm's total excitation occupation.** -/
theorem window_excOcc_sum (p : ℝ) (m : ℕ) (U : Array N) (n W : ℕ) :
    N * W ≤ 2 * m * W + ∑ i, excOcc p m U n W i := by
  have hsumW : ∑ t ∈ Finset.range W, N ≤ ∑ t ∈ Finset.range W,
      (2 * m + ∑ i, currentExcited m (U := U) (p := p) (n + t) i) :=
    Finset.sum_le_sum (fun t _ => sum_currentExcited_ge p m U (n + t))
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm] at hsumW
  have hrhs : ∑ t ∈ Finset.range W,
      (2 * m + ∑ i, currentExcited m (U := U) (p := p) (n + t) i)
      = 2 * m * W + ∑ i, excOcc p m U n W i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Finset.sum_comm]
    simp only [excOcc]
    ring
  rw [hrhs] at hsumW
  exact hsumW

/-! ## 2. The drift-martingale tail on the enlarged filtration -/

/-- The walker is at all times within distance `k` of its starting point. -/
theorem abs_pos_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ k : ℕ, |(trajectory p m U k).pos i| ≤ (k : ℤ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h := traj_step_abs p m U i k
      have h2 : |(trajectory p m U (k + 1)).pos i| ≤
          |(trajectory p m U k).pos i| + 1 := by
        have hsplit : (trajectory p m U (k + 1)).pos i = (trajectory p m U k).pos i +
            ((trajectory p m U (k + 1)).pos i - (trajectory p m U k).pos i) := by ring
        rw [hsplit]
        have h3 := abs_add_le ((trajectory p m U k).pos i)
          ((trajectory p m U (k + 1)).pos i - (trajectory p m U k).pos i)
        linarith
      push_cast
      linarith

/-- The real-valued position at time `k` is bounded by `k`. -/
theorem abs_pos_cast_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (k : ℕ) :
    |((trajectory p m U k).pos i : ℝ)| ≤ (k : ℝ) := by
  have h := abs_pos_le p m U i k
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- The real-valued position at a fixed time is integrable. -/
theorem integrable_pos_cast (p : ℝ) (m : ℕ) (n k : ℕ) (hk : k ≤ n) (i : Fin N) :
    Integrable (fun U : Array N => ((trajectory p m U k).pos i : ℝ)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have hmeas : Measurable (fun U : Array N => ((trajectory p m U k).pos i : ℝ)) :=
    fun s hs => (Enl.enlFilt p m).le n _
      ((hcast.comp (Enl.enl_pos_measurable p m n hk i)) hs)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (k : ℝ) ?_
  filter_upwards with U
  exact abs_pos_cast_le p m U i k

/-- The martingale increment `M^i_{n+1} - M^i_n`, written through the conditional right
probability of the enlarged filtration. -/
noncomputable def martIncr (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) : ℝ :=
  Increment.inc p m n i U - (2 * SwarmCross.alphaFun p m n i U - 1)

/-- The increment is the increment of the paper's drift martingale. -/
theorem martIncr_eq_driftMartingale (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    martIncr p m n i U = driftMartingale p m U (n + 1) i - driftMartingale p m U n i := by
  rw [martIncr, Increment.driftMartingale_increment]
  unfold Increment.centredInc
  rfl

/-- The drift-martingale increment is bounded by `2` in absolute value, as in the paper's
display `(mart)`. -/
theorem martIncr_abs_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i : Fin N) (U : Array N) : |martIncr p m n i U| ≤ 2 := by
  have hinc : |Increment.inc p m n i U| ≤ 1 := by
    rcases traj_step p m U i n with h | h
    · rw [Increment.inc_apply, h]; push_cast; norm_num
    · rw [Increment.inc_apply, h]; push_cast; norm_num
  have hexc_ge : (0 : ℝ) ≤ Increment.excitedAt p m n i U := by
    unfold Increment.excitedAt; exact Nat.cast_nonneg _
  have hexc_le : Increment.excitedAt p m n i U ≤ 1 := by
    unfold Increment.excitedAt
    exact_mod_cast currentExcited_le_one m n i (U := U) (p := p)
  have hc0 : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hc1 : 2 * p - 1 ≤ 1 := by linarith
  have hexc : |(2 * p - 1) * Increment.excitedAt p m n i U| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hc0 hexc_ge)]
    nlinarith
  have heq : martIncr p m n i U = Increment.inc p m n i U -
      (2 * p - 1) * Increment.excitedAt p m n i U := by
    rw [martIncr]
    congr 1
    exact Increment.two_mul_currentAlpha_sub_one p m n i U
  rw [heq]
  calc |Increment.inc p m n i U - (2 * p - 1) * Increment.excitedAt p m n i U|
      ≤ |Increment.inc p m n i U| + |(2 * p - 1) * Increment.excitedAt p m n i U| :=
        abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hinc hexc
    _ = 2 := by norm_num

/-- The drift-martingale increment is measurable one step ahead of the enlarged
filtration. -/
theorem stronglyMeasurable_martIncr (p : ℝ) (m n : ℕ) (i : Fin N) :
    StronglyMeasurable[Enl.enlFilt p m (n + 1)] (martIncr p m n i) := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have h1 : Measurable[Enl.enlFilt p m (n + 1)]
      (fun U : Array N => ((trajectory p m U (n + 1)).pos i : ℝ)) :=
    hcast.comp (Enl.enl_pos_measurable p m (n + 1) (le_refl (n + 1)) i)
  have h0 : Measurable[Enl.enlFilt p m (n + 1)]
      (fun U : Array N => ((trajectory p m U n).pos i : ℝ)) :=
    hcast.comp (Enl.enl_pos_measurable p m (n + 1) (by omega) i)
  have hα : Measurable[Enl.enlFilt p m (n + 1)] (SwarmCross.alphaFun p m n i) :=
    (Enl.measurable_alphaFun_enl p m n i).mono
      ((Enl.enlFilt p m).mono (Nat.le_succ n)) le_rfl
  have hfun : martIncr p m n i = fun U : Array N =>
      (((trajectory p m U (n + 1)).pos i : ℝ) - ((trajectory p m U n).pos i : ℝ))
        - (2 * SwarmCross.alphaFun p m n i U - 1) := rfl
  rw [hfun]
  exact (((h1.sub h0).sub ((hα.const_mul 2).sub measurable_const))).stronglyMeasurable

/-- Integrability of the conditional right probability. -/
theorem integrable_alphaFun {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i : Fin N) :
    Integrable (SwarmCross.alphaFun p m n i) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hαm : Measurable (SwarmCross.alphaFun p m n i) :=
    fun s hs => (Enl.enlFilt p m).le n _ ((Enl.measurable_alphaFun_enl p m n i) hs)
  refine Integrable.of_bound hαm.aestronglyMeasurable 1 ?_
  filter_upwards with U
  have hb := SwarmCross.alphaFun_mem_Icc (N := N) hp0 hp1 m n i U
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- **The drift martingale has conditionally vanishing increments** on the enlarged
filtration. -/
theorem condExp_martIncr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i : Fin N) :
    (arrayMeasure N)[martIncr p m n i | Enl.enlFilt p m n] =ᵐ[arrayMeasure N] 0 := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hαint := integrable_alphaFun (N := N) hp0 hp1 m n i
  have hconst1 : Integrable (fun _ : Array N => (1 : ℝ)) (arrayMeasure N) :=
    integrable_const _
  have hgint : Integrable (fun U : Array N => 2 * SwarmCross.alphaFun p m n i U - 1)
      (arrayMeasure N) := (hαint.const_mul 2).sub hconst1
  have hincint : Integrable (Increment.inc p m n i) (arrayMeasure N) :=
    (integrable_pos_cast p m (n + 1) (n + 1) (le_refl _) i).sub
      (integrable_pos_cast p m (n + 1) n (by omega) i)
  have hinc0 := Enl.condExp_inc_enl (N := N) p hp0 hp1 (m := m) (n := n) i
  have hinc : (arrayMeasure N)[Increment.inc p m n i | Enl.enlFilt p m n] =ᵐ[arrayMeasure N]
      (fun U : Array N => 2 * SwarmCross.alphaFun p m n i U - 1) := hinc0
  have hgm : StronglyMeasurable[Enl.enlFilt p m n]
      (fun U : Array N => 2 * SwarmCross.alphaFun p m n i U - 1) :=
    (((Enl.measurable_alphaFun_enl p m n i).const_mul 2).sub measurable_const).stronglyMeasurable
  have hg := condExp_of_stronglyMeasurable ((Enl.enlFilt p m).le n) hgm hgint
  have hsub := condExp_sub hincint hgint (Enl.enlFilt p m n)
  have hfun : martIncr p m n i = (fun U : Array N => Increment.inc p m n i U) -
      (fun U : Array N => 2 * SwarmCross.alphaFun p m n i U - 1) := rfl
  rw [hfun]
  filter_upwards [hsub, hinc] with U h1 h2
  rw [h1, Pi.sub_apply, h2, hg]
  simp

/-- The filtration shifted to start at the deterministic time `n`. -/
noncomputable def shiftFilt (p : ℝ) (m : ℕ) (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Array N)) where
  seq k := Enl.enlFilt p m (n + k)
  mono' := by
    intro a b hab
    exact (Enl.enlFilt p m).mono (by omega)
  le' := fun k => (Enl.enlFilt p m).le (n + k)

/-- Telescoping the increments recovers the drift martingale over the window. -/
theorem psum_martIncr (p : ℝ) (m n W : ℕ) (i : Fin N) (U : Array N) :
    LocMart.psum (fun k => martIncr p m (n + k) i) W U
      = driftMartingale p m U (n + W) i - driftMartingale p m U n i := by
  induction W with
  | zero => simp [LocMart.psum]
  | succ W ih =>
      rw [LocMart.psum_succ, ih, martIncr_eq_driftMartingale]
      have hidx : n + (W + 1) = n + W + 1 := rfl
      rw [hidx]
      ring

/-- **Azuma–Hoeffding tail of the paper's drift martingale on the actual array.** -/
theorem driftMartingale_tail {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n W : ℕ) (hW : 1 ≤ W) (i : Fin N) {ε : ℝ} (hε : 0 < ε) (hεW : ε ≤ 4 * W) :
    (arrayMeasure N).real
        {U : Array N | ε ≤ |driftMartingale p m U (n + W) i - driftMartingale p m U n i|}
      ≤ 2 * Real.exp (-(ε ^ 2) / (16 * (W : ℝ))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : ∀ k : ℕ, StronglyMeasurable[(shiftFilt (N := N) p m n) (k + 1)]
      (fun U : Array N => martIncr p m (n + k) i U) :=
    fun k => stronglyMeasurable_martIncr p m (n + k) i
  have hmean : ∀ k : ℕ, (arrayMeasure N)[(fun U : Array N => martIncr p m (n + k) i U) |
      (shiftFilt (N := N) p m n) k] =ᵐ[arrayMeasure N] 0 :=
    fun k => condExp_martIncr hp0 hp1 m (n + k) i
  have hmain := LocMart.measure_abs_psum_ge_le (μ := arrayMeasure N)
    (ℱ := shiftFilt (N := N) p m n) (ξ := fun k U => martIncr p m (n + k) i U)
    (C := 2) hmeas (by norm_num) (fun k U => martIncr_abs_le hp0 hp1 m (n + k) i U) hmean hW hε
    (by
      have h2 : (2 : ℝ) * (W : ℝ) * 2 = 4 * (W : ℝ) := by ring
      linarith)
  have hset : {U : Array N | ε ≤ |LocMart.psum (fun k U => martIncr p m (n + k) i U) W U|}
      = {U : Array N | ε ≤ |driftMartingale p m U (n + W) i - driftMartingale p m U n i|} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    rw [psum_martIncr]
  rw [hset] at hmain
  have hexp : -(ε ^ 2) / (4 * (W : ℝ) * 2 ^ 2) = -(ε ^ 2) / (16 * (W : ℝ)) := by
    have : 4 * (W : ℝ) * 2 ^ 2 = 16 * (W : ℝ) := by ring
    rw [this]
  rwa [hexp] at hmain

/-! ## 3. The swarm-stall reduction -/

/-- The configuration maximum increases by at most one per step. -/
theorem actX_le_succ (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    RecordoSupply.actX p m U i (n + 1) ≤ RecordoSupply.actX p m U i n + 1 := by
  rcases traj_step p m U i n with h | h
  · show (trajectory p m U (n + 1)).pos i ≤ (trajectory p m U n).pos i + 1
    omega
  · show (trajectory p m U (n + 1)).pos i ≤ (trajectory p m U n).pos i + 1
    omega

theorem runMax_zero_actX (p : ℝ) (m : ℕ) (U : Array N) :
    runMax (RecordoSupply.actX p m U) 0 = 0 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le (s := Finset.univ) (f := fun i => RecordoSupply.actX p m U i 0)
      Finset.univ_nonempty (fun i _ => ?_)
    show (trajectory p m U 0).pos i ≤ 0
    simp
  · have h := le_runMax (X := RecordoSupply.actX p m U) 0 (Classical.arbitrary (Fin N))
    show (0 : ℤ) ≤ runMax (RecordoSupply.actX p m U) 0
    have : RecordoSupply.actX p m U (Classical.arbitrary (Fin N)) 0 = 0 := by
      show (trajectory p m U 0).pos _ = 0
      simp
    linarith

theorem runMax_succ_le_actX (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    runMax (RecordoSupply.actX p m U) (n + 1) ≤ runMax (RecordoSupply.actX p m U) n + 1 := by
  refine Finset.sup'_le (s := Finset.univ) (f := fun i => RecordoSupply.actX p m U i (n + 1))
    Finset.univ_nonempty (fun i _ => ?_)
  have hstep := actX_le_succ p m U i n
  have hle := le_runMax (X := RecordoSupply.actX p m U) n i
  linarith

/-- Up to the record time the configuration maximum never exceeds the record level. -/
theorem runMax_le_of_le_record {p : ℝ} {m : ℕ} {U : Array N}
    (hU : U ∈ SwarmRecordMeas.Actual.ReachAll p m) (r : ℕ) :
    ∀ n ≤ SwarmRecordMeas.Actual.recTimeA p m U r,
      runMax (RecordoSupply.actX p m U) n ≤ (r : ℤ) := by
  have hspec : runMax (RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U r)
      = (r : ℤ) :=
    (SwarmRecordMeas.Actual.recTimeA_spec p m U r).resolve_left (fun h => h hU)
  intro n
  induction n with
  | zero => intro _; rw [runMax_zero_actX]; exact Nat.cast_nonneg r
  | succ n ih =>
      intro hn
      by_cases hlast : n + 1 = SwarmRecordMeas.Actual.recTimeA p m U r
      · rw [hlast]; exact le_of_eq hspec
      · have hlt : n + 1 < SwarmRecordMeas.Actual.recTimeA p m U r := by omega
        have hnlt : n < SwarmRecordMeas.Actual.recTimeA p m U r := by omega
        have hneN : runMax (RecordoSupply.actX p m U) n ≠ (r : ℤ) :=
          fun hc => SwarmRecordMeas.Actual.recTimeA_min p m U r n hnlt (Or.inr hc)
        have h1 : runMax (RecordoSupply.actX p m U) n ≤ (r : ℤ) := ih (le_of_lt hnlt)
        have h2 : runMax (RecordoSupply.actX p m U) (n + 1)
            ≤ runMax (RecordoSupply.actX p m U) n + 1 := runMax_succ_le_actX p m U n
        have h2' : runMax (RecordoSupply.actX p m U) (n + 1) ≤ (r : ℤ) + 1 := by linarith
        by_contra hcon
        have h3 : (r : ℤ) + 1 ≤ runMax (RecordoSupply.actX p m U) (n + 1) := by omega
        have heq : runMax (RecordoSupply.actX p m U) (n + 1) = (r : ℤ) + 1 :=
          le_antisymm h2' h3
        have hnk : runMax (RecordoSupply.actX p m U) n = (r : ℤ) := by linarith
        exact hneN hnk

/-- On `ReachAll` the defaulted clock is a genuine record clock. -/
theorem isRecord_recTimeA_actX {p : ℝ} {m : ℕ} {U : Array N}
    (hU : U ∈ SwarmRecordMeas.Actual.ReachAll p m) :
    IsRecord (RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) := by
  intro r
  refine ⟨fun n hn => ?_, ?_⟩
  · have hle := runMax_le_of_le_record hU r n (le_of_lt hn)
    have hne : runMax (RecordoSupply.actX p m U) n ≠ (r : ℤ) :=
      fun hc => SwarmRecordMeas.Actual.recTimeA_min p m U r n hn (Or.inr hc)
    rcases lt_or_eq_of_le hle with h1 | h1
    · exact h1
    · exact absurd h1 hne
  · exact (SwarmRecordMeas.Actual.recTimeA_spec p m U r).resolve_left (fun h => h hU)

/-- **The record-fibre swarm-stall set.**  This is *definitionally* the frontier's
`RecordAdvanceWindow.swarmStall`: every walker's position `T*L` steps after the
level-`r` record fibre is still strictly below level `r + B*L`. -/
def stallSet (p : ℝ) (m B T r L : ℕ) : Set (Array N) :=
  {U | U ∈ SwarmRecordMeas.Actual.ReachAll p m ∧ ∀ i : Fin N,
      RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L)
        < ((r + B * L : ℕ) : ℤ)}

/-- The absolute-defect threshold set at the record fibre. -/
def defectSet (p : ℝ) (m r : ℕ) (θ : ℝ) : Set (Array N) :=
  {U | θ ≤ (defect (RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r : ℝ)}

/-- The drift-martingale displacement of some walker over the record window exceeds `θ`. -/
def martJumpSet (p : ℝ) (m r W : ℕ) (θ : ℝ) : Set (Array N) :=
  {U | ∃ i : Fin N,
    θ ≤ |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + W) i
      - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|}

/-- The record-advance exception is a swarm stall. -/
theorem timeLag_subset_stallSet (p : ℝ) (m B T r L : ℕ) :
    {U : Array N | SwarmRecordMeas.Actual.recTimeA p m U r + T * L <
        SwarmRecordMeas.Actual.recTimeA p m U (r + B * L)} ⊆ stallSet (N := N) p m B T r L := by
  intro U hU
  by_cases hR : U ∈ SwarmRecordMeas.Actual.ReachAll p m
  · refine ⟨hR, fun i => ?_⟩
    have hrec := isRecord_recTimeA_actX (N := N) hR (r + B * L)
    have hlt : runMax (RecordoSupply.actX p m U)
        (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) < ((r + B * L : ℕ) : ℤ) :=
      hrec.1 _ hU
    have hle := le_runMax (X := RecordoSupply.actX p m U)
      (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
    linarith
  · exfalso
    have h0 : SwarmRecordMeas.Actual.recTimeA p m U r = 0 :=
      SwarmRecordMeas.Actual.recTimeA_eq_zero_of_not_reach hR r
    have h0' : SwarmRecordMeas.Actual.recTimeA p m U (r + B * L) = 0 :=
      SwarmRecordMeas.Actual.recTimeA_eq_zero_of_not_reach hR _
    have hU' : SwarmRecordMeas.Actual.recTimeA p m U r + T * L <
        SwarmRecordMeas.Actual.recTimeA p m U (r + B * L) := hU
    rw [h0, h0'] at hU'
    omega

/-- **The excitation-occupation decomposition over the record window.** -/
theorem excitedSteps_add_excOcc (p : ℝ) (m : ℕ) (U : Array N) (τ W : ℕ) (i : Fin N) :
    excitedSteps p m U (τ + W) i = excitedSteps p m U τ i + excOcc p m U τ W i := by
  unfold excitedSteps excOcc
  exact Finset.sum_range_add _ _ _

/-- **The drift decomposition over the record window.** -/
theorem driftMartingale_window (p : ℝ) (m : ℕ) (U : Array N) (τ W : ℕ) (i : Fin N) :
    driftMartingale p m U (τ + W) i - driftMartingale p m U τ i =
      (((trajectory p m U (τ + W)).pos i : ℝ) - ((trajectory p m U τ).pos i : ℝ))
        - (2 * p - 1) * (excOcc p m U τ W i : ℝ) := by
  have h := excitedSteps_add_excOcc p m U τ W i
  have hcast : ((excitedSteps p m U (τ + W) i : ℕ) : ℝ) =
      (excitedSteps p m U τ i : ℝ) + (excOcc p m U τ W i : ℝ) := by
    rw [h]; push_cast; ring
  simp only [driftMartingale, hcast]
  ring

/-- **The pointwise stall reduction.**  On the swarm-stall event at the record fibre, with
`N ≥ 2m`, the accumulated drift of the whole swarm is bounded by the total defect at the
fibre plus the total drift-martingale displacement.  This is where the excitation surplus
stops being an input: the deterministic occupation bound `window_excOcc_sum` supplies the
left-hand side. -/
theorem stall_reduction {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B T r L : ℕ}
    (hmN : 2 * m ≤ N) {U : Array N} (hU : U ∈ stallSet (N := N) p m B T r L) :
    (2 * p - 1) * (((N : ℝ) - 2 * m) * (T : ℝ) * (L : ℝ)) ≤
      (N : ℝ) * (B : ℝ) * (L : ℝ)
        + (N : ℝ) * ((defect (RecordoSupply.actX p m U)
            (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ)
        + ∑ i, |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i| := by
  classical
  obtain ⟨hReach, hstall⟩ := hU
  have hcoef : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hτspec : runMax (RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U r)
      = (r : ℤ) :=
    (SwarmRecordMeas.Actual.recTimeA_spec p m U r).resolve_left (fun h => h hReach)
  have hXτ : ∀ i : Fin N,
      ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)
        ≤ (r : ℝ) := by
    intro i
    have := le_runMax (X := RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U r) i
    rw [hτspec] at this
    exact_mod_cast this
  have hXW : ∀ i : Fin N,
      ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
        < (r : ℝ) + (B : ℝ) * (L : ℝ) := by
    intro i
    have hh := hstall i
    have hcast : (((r + B * L : ℕ)) : ℤ) = (r : ℤ) + (B : ℤ) * (L : ℤ) := by push_cast; ring
    rw [hcast] at hh
    have := hh
    exact_mod_cast this
  have hdisp : ∀ i : Fin N,
      ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
          - ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)
        = (2 * p - 1) * (excOcc p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i : ℝ)
          + (driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
              - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i) := by
    intro i
    have h := driftMartingale_window p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i
    have hpos : (RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℝ)
        = ((trajectory p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L)).pos i : ℝ) := rfl
    have hpos' : (RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℝ)
        = ((trajectory p m U (SwarmRecordMeas.Actual.recTimeA p m U r)).pos i : ℝ) := rfl
    rw [hpos, hpos']
    linarith
  -- upper bound: the sum of the swarm's displacements
  have hupper : ∑ i : Fin N,
      (((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
        - ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
      ≤ (N : ℝ) * ((B : ℝ) * (L : ℝ))
        + (N : ℝ) * ((defect (RecordoSupply.actX p m U)
            (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) := by
    have h1 : ∑ i : Fin N,
        (((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
          - ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
        ≤ ∑ i : Fin N, (((r : ℝ) + (B : ℝ) * (L : ℝ)) -
            ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)) :=
      Finset.sum_le_sum (fun i _ => by linarith [hXW i])
    have h2 : ∑ i : Fin N, (((r : ℝ) + (B : ℝ) * (L : ℝ)) -
        ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
        = (N : ℝ) * ((B : ℝ) * (L : ℝ)) + ∑ i : Fin N,
          ((r : ℝ) - ((RecordoSupply.actX p m U i
            (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)) := by
      calc ∑ i : Fin N, (((r : ℝ) + (B : ℝ) * (L : ℝ)) -
            ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
          = ∑ i : Fin N, (((r : ℝ) - ((RecordoSupply.actX p m U i
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
              + (B : ℝ) * (L : ℝ)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = ∑ i : Fin N, ((r : ℝ) - ((RecordoSupply.actX p m U i
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
              + ∑ _i : Fin N, ((B : ℝ) * (L : ℝ)) := Finset.sum_add_distrib
        _ = ∑ i : Fin N, ((r : ℝ) - ((RecordoSupply.actX p m U i
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
              + (N : ℝ) * ((B : ℝ) * (L : ℝ)) := by
            simp
        _ = (N : ℝ) * ((B : ℝ) * (L : ℝ)) + ∑ i : Fin N,
              ((r : ℝ) - ((RecordoSupply.actX p m U i
                (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)) := by ring
    have h3 : ∑ i : Fin N,
        ((r : ℝ) - ((RecordoSupply.actX p m U i
          (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
        ≤ (N : ℝ) * ((defect (RecordoSupply.actX p m U)
            (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) := by
      have hper : ∀ i : Fin N,
          ((r : ℝ) - ((RecordoSupply.actX p m U i
            (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
            ≤ ((defect (RecordoSupply.actX p m U)
                (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) := by
        intro i
        have hle : runMin (RecordoSupply.actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U r)
            ≤ RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) :=
          runMin_le _ i
        have hdef : (defect (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ)
            = (r : ℤ) - runMin (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U r) := rfl
        have hcast : ((defect (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ)
            = (r : ℝ) - ((runMin (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ) := by
          rw [hdef]; push_cast; ring
        rw [hcast]
        have h2' : ((runMin (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)
            ≤ ((RecordoSupply.actX p m U i
              (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ) := by exact_mod_cast hle
        linarith
      calc ∑ i : Fin N,
          ((r : ℝ) - ((RecordoSupply.actX p m U i
            (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
          ≤ ∑ _i : Fin N, ((defect (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) :=
            Finset.sum_le_sum (fun i _ => hper i)
        _ = (N : ℝ) * ((defect (RecordoSupply.actX p m U)
              (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) := by
            simp
    linarith
  -- lower bound: the deterministic occupation bound
  have hoccraw := window_excOcc_sum p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L)
  have hocc : ((N : ℝ) - 2 * m) * ((T * L : ℕ) : ℝ)
      ≤ ∑ i : Fin N, (excOcc p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i : ℝ) := by
    have hcast : ((N * (T * L) : ℕ) : ℝ) ≤ ((2 * m * (T * L) : ℕ) : ℝ) +
        ((∑ i, excOcc p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i : ℕ) : ℝ) := by
      exact_mod_cast hoccraw
    rw [Nat.cast_sum] at hcast
    have hpush : ((N * (T * L) : ℕ) : ℝ) = (N : ℝ) * ((T * L : ℕ) : ℝ) := by push_cast; ring
    have hpush2 : ((2 * m * (T * L) : ℕ) : ℝ) = 2 * (m : ℝ) * ((T * L : ℕ) : ℝ) := by
      push_cast; ring
    rw [hpush, hpush2] at hcast
    nlinarith
  have hsum_lower : (2 * p - 1) * (((N : ℝ) - 2 * m) * ((T * L : ℕ) : ℝ))
      - ∑ i : Fin N, |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
          - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|
      ≤ ∑ i : Fin N,
        (((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
          - ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ)) := by
    have hrew : ∑ i : Fin N,
        (((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) : ℤ) : ℝ)
          - ((RecordoSupply.actX p m U i (SwarmRecordMeas.Actual.recTimeA p m U r) : ℤ) : ℝ))
        = (2 * p - 1) * ∑ i : Fin N,
            (excOcc p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i : ℝ)
          + ∑ i : Fin N, (driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
              - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => hdisp i)
    rw [hrew]
    have hlow : ∀ i : Fin N,
        -( |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|)
          ≤ (driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
              - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i) := by
      intro i
      have h := neg_abs_le (driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
        - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i)
      linarith
    have h4 : ∑ i : Fin N,
        (driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
          - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i)
        ≥ ∑ i : Fin N, -( |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|) :=
      Finset.sum_le_sum (fun i _ => hlow i)
    have h5 : ∑ i : Fin N,
        -( |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|)
        = -(∑ i : Fin N, |driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|) := by
      rw [Finset.sum_neg_distrib]
    rw [h5] at h4
    have h6 : (2 * p - 1) * (((N : ℝ) - 2 * m) * ((T * L : ℕ) : ℝ))
        ≤ (2 * p - 1) * ∑ i : Fin N,
            (excOcc p m U (SwarmRecordMeas.Actual.recTimeA p m U r) (T * L) i : ℝ) :=
      mul_le_mul_of_nonneg_left hocc hcoef
    linarith
  have hTL : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  rw [hTL] at hsum_lower
  have hassoc : (2 * p - 1) * (((N : ℝ) - 2 * m) * ((T : ℝ) * (L : ℝ))) =
      (2 * p - 1) * (((N : ℝ) - 2 * m) * (T : ℝ) * (L : ℝ)) := by ring
  rw [hassoc] at hsum_lower
  linarith

/-! ### The explicit coefficient and the measure consequence -/

/-- The explicit drift coefficient of the reduction, `c = (2p-1)(N-2m)T - NB`. -/
noncomputable def cCoef (N : ℕ) (p : ℝ) (m B T : ℕ) : ℝ :=
  (2 * p - 1) * ((N : ℝ) - 2 * m) * (T : ℝ) - (N : ℝ) * (B : ℝ)

/-- **The stall reduction as a set inclusion.**  If the drift coefficient `c` is positive,
no `2m`-dominated swarm can stall at a record fibre unless either the defect at the fibre is
at least `c L / (2N)` or some walker's drift martingale moves by at least `c L / (2N)` inside
the window.  There is no excitation input left. -/
theorem stall_subset_defect_union_mart {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B T r L : ℕ}
    (hmN : 2 * m ≤ N) (hNpos : 0 < N) {U : Array N}
    (hU : U ∈ stallSet (N := N) p m B T r L)
    (hdef : U ∉ defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))) :
    U ∈ martJumpSet (N := N) p m r (T * L) (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) := by
  classical
  have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hred := stall_reduction (N := N) hp hmN hU
  have hDlt : ((defect (RecordoSupply.actX p m U)
      (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ)
      < cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) := by
    have h := hdef
    simp only [defectSet, Set.mem_ofPred_eq, not_le] at h
    exact h
  by_contra hcon
  simp only [martJumpSet, Set.mem_ofPred_eq, not_exists, not_le] at hcon
  set θ : ℝ := cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) with hθ
  have hSle : (∑ i : Fin N, |driftMartingale p m U
        (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
          - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|)
      ≤ (N : ℝ) * θ := by
    calc ∑ i : Fin N, |driftMartingale p m U
          (SwarmRecordMeas.Actual.recTimeA p m U r + T * L) i
            - driftMartingale p m U (SwarmRecordMeas.Actual.recTimeA p m U r) i|
        ≤ ∑ _i : Fin N, θ := Finset.sum_le_sum (fun i _ => le_of_lt (hcon i))
      _ = (N : ℝ) * θ := by simp
  have hND : (N : ℝ) * ((defect (RecordoSupply.actX p m U)
      (SwarmRecordMeas.Actual.recTimeA p m U) r : ℤ) : ℝ) < (N : ℝ) * θ :=
    mul_lt_mul_of_pos_left (by rw [hθ]; exact hDlt) hNpos'
  have hNL : (N : ℝ) * θ = cCoef N p m B T * (L : ℝ) / 2 := by
    rw [hθ]
    field_simp
  have hcc : (2 * p - 1) * (((N : ℝ) - 2 * m) * (T : ℝ) * (L : ℝ))
      - (N : ℝ) * ((B : ℝ) * (L : ℝ)) = cCoef N p m B T * (L : ℝ) := by
    rw [cCoef]; ring
  rw [hθ] at hND
  nlinarith [hred, hND, hSle, hNL, hcc]

/-- **The measure consequence of the reduction.**  The swarm-stall mass at the record fibre
is bounded by the defect mass at the fibre plus the mass of the (fibre-time) drift-martingale
displacement event. -/
theorem stall_measure_le {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B T r L : ℕ}
    (hmN : 2 * m ≤ N) (hNpos : 0 < N) {U : Array N} :
    (arrayMeasure N) (stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N) (defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
        + (arrayMeasure N) (martJumpSet (N := N) p m r (T * L)
            (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))) := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro U hU
  by_cases h : U ∈ defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
  · exact Or.inl h
  · exact Or.inr (stall_subset_defect_union_mart (N := N) hp hmN hNpos hU h)

/-! ### The quantitative record-time-truncated form -/

/-- **The fibre-time martingale alternative on a truncated record-time event.**  If the record
time is at most `K`, the drift-martingale alternative of the stall reduction costs only the
union bound over the `K+1` possible starts, each of which is covered by the fixed-start Azuma
bound `driftMartingale_tail`.  This is the exact place where the record time enters. -/
theorem martJumpSet_inter_recordTime_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r W K : ℕ} (hW : 1 ≤ W) {θ : ℝ} (hθ : 0 < θ) (hθW : θ ≤ 4 * (W : ℝ)) :
    (arrayMeasure N).real (martJumpSet (N := N) p m r W θ ∩
        {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K})
      ≤ ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) := by
  classical
  have hsub : martJumpSet (N := N) p m r W θ ∩
      {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K} ⊆
      ⋃ n : Fin (K + 1), ⋃ i : Fin N,
        {U | θ ≤ |driftMartingale p m U (n.val + W) i - driftMartingale p m U n.val i|} := by
    rintro U ⟨⟨i, hi⟩, hτ⟩
    simp only [Set.mem_ofPred_eq] at hi hτ
    have hK : SwarmRecordMeas.Actual.recTimeA p m U r < K + 1 := by omega
    refine Set.mem_iUnion.2 ⟨⟨SwarmRecordMeas.Actual.recTimeA p m U r, hK⟩, ?_⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc (arrayMeasure N).real (martJumpSet (N := N) p m r W θ ∩
        {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K})
      ≤ (arrayMeasure N).real (⋃ n : Fin (K + 1), ⋃ i : Fin N,
          {U | θ ≤ |driftMartingale p m U (n.val + W) i
            - driftMartingale p m U n.val i|}) := measureReal_mono hsub (by simp)
    _ ≤ ∑ n : Fin (K + 1), (arrayMeasure N).real (⋃ i : Fin N,
          {U | θ ≤ |driftMartingale p m U (n.val + W) i
            - driftMartingale p m U n.val i|}) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (K + 1), ∑ i : Fin N, (arrayMeasure N).real
          {U | θ ≤ |driftMartingale p m U (n.val + W) i
            - driftMartingale p m U n.val i|} :=
        Finset.sum_le_sum (fun n _ => measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _n : Fin (K + 1), ∑ _i : Fin N, (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun i _ =>
          driftMartingale_tail hp0 hp1 m n.val W hW i hθ hθW))
    _ = ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * (W : ℝ)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **The stall tail on a truncated record-time event.**  Combining the stall reduction with
the truncated martingale bound: for every `K`, the swarm-stall mass at the record fibre
restricted to `{τ_r ≤ K}` is at most the defect mass at the fibre plus
`(K+1) · N · 2 exp(-θ²/(16TL))` at the explicit threshold `θ = c L/(2N)`.  A tail bound on
`recTimeA` turns this into a summable bound; without one, the `K`-dependence is exactly the
remaining cost. -/
theorem stall_measure_le_trunc {p : ℝ} (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m B T r L K : ℕ}
    (hmN : 2 * m ≤ N) (hNpos : 0 < N) (hW : 1 ≤ T * L)
    (hθ : 0 < cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
    (hθW : cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)) ≤ 4 * ((T * L : ℕ) : ℝ)) :
    (arrayMeasure N).real (stallSet (N := N) p m B T r L ∩
        {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K})
      ≤ (arrayMeasure N).real (defectSet (N := N) p m r
            (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
        + ((K : ℝ) + 1) * (N : ℝ) *
            (2 * Real.exp (-((cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
              / (16 * ((T * L : ℕ) : ℝ)))) := by
  have hsub : stallSet (N := N) p m B T r L ∩
      {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K} ⊆
      defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∪
        (martJumpSet (N := N) p m r (T * L) (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∩
          {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K}) := by
    rintro U ⟨hU, hK⟩
    by_cases h : U ∈ defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
    · exact Or.inl h
    · exact Or.inr ⟨stall_subset_defect_union_mart (N := N) hp hmN hNpos hU h, hK⟩
  calc (arrayMeasure N).real (stallSet (N := N) p m B T r L ∩
        {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K})
      ≤ (arrayMeasure N).real
          (defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∪
            (martJumpSet (N := N) p m r (T * L) (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∩
              {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K})) :=
        measureReal_mono hsub (by simp)
    _ ≤ (arrayMeasure N).real
          (defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
          + (arrayMeasure N).real
            (martJumpSet (N := N) p m r (T * L) (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ∩
              {U | SwarmRecordMeas.Actual.recTimeA p m U r ≤ K}) :=
        measureReal_union_le _ _
    _ ≤ (arrayMeasure N).real
          (defectSet (N := N) p m r (cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))))
          + ((K : ℝ) + 1) * (N : ℝ) *
              (2 * Real.exp (-((cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
                / (16 * ((T * L : ℕ) : ℝ)))) := by
        have hb := martJumpSet_inter_recordTime_le (N := N) hp hp1 hW
          (m := m) (r := r) (W := T * L) (K := K) (θ := cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ)))
          hθ hθW
        linarith

end ExcOcc
