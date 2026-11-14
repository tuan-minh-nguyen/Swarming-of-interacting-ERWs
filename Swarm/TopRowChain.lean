/-
# The record-clock top row is a thinning chain, and thick sites are hot

`TopRowLaw.lean` / `TopRowMeasure.lean` prove the exact one-step law at a record prefix:
for a thin top row (`#topRow ≤ m`) the walkers standing at the record level have right
probability exactly `1/2`, and the exact mass of "the whole top row steps left" is
`(1/2)^(#topRow)` times the past mass.  This file and its companion
`TopRowChainMeasure.lean` settle what that law does when it is *iterated at record
clocks*, and record the exact structural obstruction that follows.

Deterministic content of this file (all on the actual array of
`Swarming.Trajectory.trajectory`, no probability):

* `step_abs`, `step_up_le`, `step_pos_lower`, `step_upper`, `step_lower` -- a walker moves
  `±1` at every step, so `X_j` changes by at most one per unit time.
* `rowAt_succ_eq` -- **the non-thickening identity**.  If no position exceeds the record
  level `s` at time `n`, then at time `n+1` the walkers standing at level `s+1` are exactly
  the walkers of the row at level `s` that stepped *up*.  Hence the row count cannot
  increase when the record advances, and `rowAt_succ_card_eq_iff` says it is preserved
  exactly when the whole row advanced together.
* `leader_stays_alone` -- consequently a unique leader at a record clock is again the
  unique leader at the next record clock: **the unique-leader state is absorbing along
  record advances**.
* `rowAt_succ_card_lt_of_not_all` -- if any walker of the row fails to step up, the next
  row is strictly thinner: thickness can only decay along advances.
* `thick_site_excited` / `rightProbability_thick_site` / `rightProbability_of_card_site`
  -- **a thick site is hot at any time and at any integer site**: if at least `m+1` walkers
  stand on the *same* site, every one of them is excited and has right probability exactly
  `p`.  No record hypothesis, no positivity of the site, and no relation between `m` and
  `N`.  In particular the large advance force of the coalescence picture is *always*
  available at a thick site; thickness itself is the only thing that has to be produced.

Measure content (the exact multistep iterate at record clocks) is in
`TopRowChainMeasure.lean`.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Swarm.TopRowMeasure

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Finset

namespace TopRowChain

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl RecordDefect
open TopRow

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 0. The row at a level, at a time -/

/-- The walkers standing on the site `y` at time `t`. -/
noncomputable def rowAt (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (y : ℤ) : Finset (Fin N) :=
  univ.filter (fun j => (trajectory p m U t).pos j = y)

theorem mem_rowAt {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {y : ℤ} {j : Fin N} :
    j ∈ rowAt p m U t y ↔ (trajectory p m U t).pos j = y := by
  simp [rowAt]

/-- The prefix top row of a record prefix is the row at that time. -/
theorem topRowPref_eq_rowAt {p : ℝ} {m n : ℕ} {γ : Pref N n} {s : ℤ} {U : Array N}
    (hU : U ∈ prefAgree p m γ) :
    topRowPref n γ s = rowAt p m U n s := by
  classical
  refine filter_congr (fun j _ => ?_)
  rw [ext_prefOf_of_mem hU le_rfl j]

/-! ## 1. The step is `±1`, hence positions move by at most one per unit time -/

/-- Every jump of every walker is a unit step. -/
theorem step_abs (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    |(trajectory p m U (n + 1)).pos i - (trajectory p m U n).pos i| = 1 := by
  have hstep : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i +
      drivenStep (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) := rfl
  rw [hstep]
  rcases Enl.drivenStep_cases _ _ with h | h <;> rw [h] <;> norm_num

theorem step_up_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U (n + 1)).pos i ≤ (trajectory p m U n).pos i + 1 := by
  obtain ⟨-, h2⟩ := abs_le.1 (le_of_eq (step_abs p m U n i))
  omega

theorem step_pos_lower (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U n).pos i - 1 ≤ (trajectory p m U (n + 1)).pos i := by
  obtain ⟨h1, -⟩ := abs_le.1 (le_of_eq (step_abs p m U n i))
  omega

/-- A walker never rises by more than the number of elapsed steps. -/
theorem step_upper (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ {a b : ℕ}, a ≤ b → (trajectory p m U b).pos i
      ≤ (trajectory p m U a).pos i + ((b - a : ℕ) : ℤ) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have h1 : (trajectory p m U (b + 1)).pos i ≤ (trajectory p m U b).pos i + 1 :=
        step_up_le p m U b i
      have hcast : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by
        have : b + 1 - a = (b - a) + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast]; linarith

/-- A walker never falls by more than the number of elapsed steps. -/
theorem step_lower (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ {a b : ℕ}, a ≤ b → (trajectory p m U a).pos i - ((b - a : ℕ) : ℤ)
      ≤ (trajectory p m U b).pos i := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have h1 : (trajectory p m U b).pos i - 1 ≤ (trajectory p m U (b + 1)).pos i :=
        step_pos_lower p m U b i
      have hcast : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by
        have : b + 1 - a = (b - a) + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast]; linarith

/-! ## 2. The non-thickening identity at a record advance -/

/-- **The non-thickening identity.**  Suppose that at time `n` no walker is above the level
`s` (a record state).  Then at time `n+1` the walkers standing on level `s+1` are exactly
the walkers of the row at level `s` that stepped up. -/
theorem rowAt_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s) :
    rowAt p m U (n + 1) (s + 1)
      = (rowAt p m U n s).filter (fun j => (trajectory p m U (n + 1)).pos j = s + 1) := by
  classical
  ext j
  rw [mem_rowAt, mem_filter, mem_rowAt]
  constructor
  · intro hj
    refine ⟨?_, hj⟩
    obtain ⟨-, hupper⟩ := abs_le.1 (le_of_eq (step_abs p m U n j))
    rw [hj] at hupper
    have hge : s ≤ (trajectory p m U n).pos j := by omega
    exact le_antisymm (hle j) hge
  · rintro ⟨-, hj⟩
    exact hj

/-- The row count at the next level is at most the old row count. -/
theorem rowAt_succ_card_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s) :
    (rowAt p m U (n + 1) (s + 1)).card ≤ (rowAt p m U n s).card := by
  rw [rowAt_succ_eq p m U n hle]
  exact card_le_card (filter_subset _ _)

/-- **When is the row preserved?**  Exactly when every walker of the row stepped up. -/
theorem rowAt_succ_card_eq_iff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s) :
    (rowAt p m U (n + 1) (s + 1)).card = (rowAt p m U n s).card ↔
      ∀ j ∈ rowAt p m U n s, (trajectory p m U (n + 1)).pos j = s + 1 := by
  rw [rowAt_succ_eq p m U n hle]
  constructor
  · intro h j hj
    have hsub : (rowAt p m U n s).filter
        (fun j => (trajectory p m U (n + 1)).pos j = s + 1) ⊆ rowAt p m U n s :=
      filter_subset _ _
    have heq : (rowAt p m U n s).filter
        (fun j => (trajectory p m U (n + 1)).pos j = s + 1) = rowAt p m U n s :=
      eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    have hm : j ∈ (rowAt p m U n s).filter
        (fun j => (trajectory p m U (n + 1)).pos j = s + 1) := by
      rw [heq]; exact hj
    exact (mem_filter.mp hm).2
  · intro h
    rw [filter_true_of_mem h]

/-- **A unique leader stays alone.**  If the row at the record level is the singleton `{i}`
and `i` steps up, the row at the next level is again the singleton `{i}`. -/
theorem leader_stays_alone (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ} {i : Fin N}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s)
    (huniq : rowAt p m U n s = {i})
    (hup : (trajectory p m U (n + 1)).pos i = s + 1) :
    rowAt p m U (n + 1) (s + 1) = {i} := by
  rw [rowAt_succ_eq p m U n hle, huniq, filter_singleton, if_pos hup]

/-- **Thickness decays along an advance.**  If some walker of the row does not step up, the
next row is strictly thinner. -/
theorem rowAt_succ_card_lt_of_not_all (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s)
    (hne : ∃ j ∈ rowAt p m U n s, (trajectory p m U (n + 1)).pos j ≠ s + 1) :
    (rowAt p m U (n + 1) (s + 1)).card < (rowAt p m U n s).card := by
  rw [rowAt_succ_eq p m U n hle]
  have hsub : (rowAt p m U n s).filter
      (fun j => (trajectory p m U (n + 1)).pos j = s + 1) ⊆ rowAt p m U n s :=
    filter_subset _ _
  have hproper : (rowAt p m U n s).filter
      (fun j => (trajectory p m U (n + 1)).pos j = s + 1) ≠ rowAt p m U n s := by
    intro heq
    obtain ⟨j, hj, hjne⟩ := hne
    have hm : j ∈ (rowAt p m U n s).filter
        (fun j => (trajectory p m U (n + 1)).pos j = s + 1) := by
      rw [heq]; exact hj
    exact hjne (mem_filter.mp hm).2
  exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hproper⟩)

/-- **No thickening across a record advance.**  If the row at the record level is thin, so is
the row at the next level: a thick top row can never be produced by a record advance. -/
theorem next_row_card_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s) (hthin : (rowAt p m U n s).card ≤ m) :
    (rowAt p m U (n + 1) (s + 1)).card ≤ m :=
  le_trans (rowAt_succ_card_le p m U n hle) hthin

/-- The same statement in "the row is preserved" form: if the row at the next level is at least
as large as the old one, then every walker of the old row stepped up. -/
theorem next_row_card_le_iff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : ℤ}
    (hle : ∀ j : Fin N, (trajectory p m U n).pos j ≤ s) :
    (rowAt p m U (n + 1) (s + 1)).card ≤ (rowAt p m U n s).card :=
  rowAt_succ_card_le p m U n hle

/-! ## 3. A thick site is hot, at any time -/

/-- A walker standing on a site has visited it at least once. -/
theorem one_le_ell_self (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    1 ≤ (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
  induction n with
  | zero => simp [initialWalkState]
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_ell, nextWalkState_pos]
      split_ifs <;> omega

/-- **A thick site is hot.**  If at least `m+1` walkers stand on the same site `x` at time
`n`, then every walker standing on `x` is excited: its peer-visit count at `x` is at least
the number of its peers standing there.  No record hypothesis is used, `x` may be any
integer, and `m` and `N` are unrelated. -/
theorem thick_site_excited (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {x : ℤ} {i : Fin N}
    (hthick : m ≤ ((univ.erase i).filter
      (fun j => (trajectory p m U n).pos j = x)).card) :
    Excited m (trajectory p m U n).ell i x := by
  classical
  have hterm : ∀ j ∈ (univ.erase i).filter
      (fun j => (trajectory p m U n).pos j = x),
      (1 : ℕ) ≤ (if j = i then 0 else (trajectory p m U n).ell j x) := by
    intro j hj
    simp only [mem_filter, mem_erase, mem_univ, true_and, ne_eq] at hj
    obtain ⟨⟨hji, -⟩, hjx⟩ := hj
    rw [if_neg hji, ← hjx]
    exact one_le_ell_self p m U n j
  have hmain : ((univ.erase i).filter
        (fun j => (trajectory p m U n).pos j = x)).card
      ≤ otherVisits (trajectory p m U n).ell i x := by
    unfold otherVisits
    calc ((univ.erase i).filter (fun j => (trajectory p m U n).pos j = x)).card
        = ∑ j ∈ (univ.erase i).filter (fun j => (trajectory p m U n).pos j = x), 1 :=
          card_eq_sum_ones _
      _ ≤ ∑ j ∈ (univ.erase i).filter
            (fun j => (trajectory p m U n).pos j = x),
            (if j = i then 0 else (trajectory p m U n).ell j x) := sum_le_sum hterm
      _ ≤ ∑ j, (if j = i then 0 else (trajectory p m U n).ell j x) :=
          sum_le_sum_of_subset_of_nonneg
            ((filter_subset _ _).trans (erase_subset _ _)) (fun j _ _ => Nat.zero_le _)
  unfold Excited
  omega

/-- **A thick site is hot, right-probability form.**  At least `m+1` walkers on one site
force right probability exactly `p` for every walker standing there. -/
theorem rightProbability_thick_site (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {x : ℤ}
    {i : Fin N}
    (hthick : m ≤ ((univ.erase i).filter
      (fun j => (trajectory p m U n).pos j = x)).card) :
    rightProbability p m (trajectory p m U n).ell i x = p := by
  unfold rightProbability
  rw [if_pos (thick_site_excited p m U n hthick)]

/-- The same statement in row-cardinality form: a site carrying at least `m+1` walkers puts
every one of them at right probability `p`. -/
theorem rightProbability_of_card_site (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {x : ℤ}
    {i : Fin N} (hi : (trajectory p m U n).pos i = x)
    (hcard : m + 1 ≤ (rowAt p m U n x).card) :
    rightProbability p m (trajectory p m U n).ell i x = p := by
  classical
  refine rightProbability_thick_site p m U n ?_
  have hset : rowAt p m U n x
      = insert i ((univ.erase i).filter (fun j => (trajectory p m U n).pos j = x)) := by
    ext j
    simp only [rowAt, mem_filter, mem_insert, mem_erase, mem_univ, true_and, ne_eq]
    by_cases hji : j = i
    · subst hji; simp [hi]
    · simp [hji]
  have hnot : i ∉ (univ.erase i).filter
      (fun j => (trajectory p m U n).pos j = x) := by
    simp
  rw [hset, Finset.card_insert_of_notMem hnot] at hcard
  omega

end TopRowChain
