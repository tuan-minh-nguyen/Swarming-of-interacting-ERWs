/-
# The record-time top row: the leader is cold, exactly

The paper's coalescence mechanism for the halving clause `(half)` rests on the qualitative
statement that a walker standing at the running maximum is *not* excited, so the top of the
pack moves with right probability `1/2` while the bottom of the pack moves with right
probability `p`.  This file proves the exact form of that statement on the actual array of
`Swarming.Trajectory.trajectory`, with no fluid limit, no compactness, no invariance and no
regularity assumption.

The key input is the first half of the definition of a record clock
(`RecordDefect.IsRecord X τ`): for every `r`, no position reaches level `r` before `τ r`.
Hence at time `τ s` the level `s` has never been occupied, so the *only* visits to level `s`
up to that time are the ones made at time `τ s` itself.  Consequently, for a walker `i`
standing at level `s` at time `τ s`, the number of peer visits at that level is exactly the
number of peers standing there (`otherVisits_top`), so

  `Excited m … i s ↔ m ≤ #{j ≠ i | pos j (τ s) = s}`   (`excited_top_iff`),

  `rightProbability … i s = if m ≤ #{j ≠ i | …} then p else 1/2`   (`rightProbability_top`).

Consequences proved here:

* `rightProbability_unique_leader`: a **unique** leader at a record time has right probability
  exactly `1/2` (`1 ≤ m`), strictly below `p`;
* `rightProbability_top_cold` / `rightProbability_top_hot`: the top row is a **threshold**
  phenomenon in its own count `a`: cold (all right probabilities `1/2`) iff `a ≤ m`, hot (all
  equal to `p`) iff `a ≥ m+1`;
* `rightProbability_top_of_N_le_m`: if `m ≥ N` the top row is **always** cold, for every record
  level and every trajectory (the `m ≥ N` regime);
* `rightProbability_bottom`: if `m ≤ N-1` and the lowest walker stands at a nonnegative site,
  its right probability is exactly `p` (the existing `excited_of_isMin`, repackaged);
* `top_cold_bottom_hot`: at a record time with a unique leader, a nonnegative laggard and
  `m ≤ N-1`, the leader-laggard drift gap is exactly `-(2p-1)`; this is the compression force
  of the paper's `(meet)`/coalescence step, in exact form;
* `top_row_product_cold` / `top_row_product_of_N_le_m`: the product of the top row's
  left-step probabilities is exactly `(1/2)^a` for a thin row, the kernel of the exact
  record-advance law `P(level advances) = 1 - ∏ (1 - q_i)`.

Everything is deterministic (an identity about `rightProbability` values), stated for an
arbitrary record clock with `IsRecord`; no probability space is used here.  The measure-level
record-advance law additionally needs the fresh-coordinate independence of the actual array,
which is *not* claimed in this file.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Swarm.DeepExc
import Swarm.RecordDefect

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Classical
open Finset

namespace TopRow

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory RecordDefect

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. Record-time geometry: the level has never been occupied -/

/-- Every position at a record time is at most the record level. -/
theorem pos_le_level {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) (s : ℕ) (i : Fin N) :
    X i (τ s) ≤ (s : ℤ) := by
  have h : runMax X (τ s) = (s : ℤ) := (hτ s).2
  calc X i (τ s) ≤ runMax X (τ s) := le_runMax (τ s) i
    _ = (s : ℤ) := h

/-- Strictly before a record time every position is strictly below the level. -/
theorem pos_lt_level_before {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {s n : ℕ}
    (hn : n < τ s) (i : Fin N) : X i n < (s : ℤ) := by
  have h : runMax X n < (s : ℤ) := (hτ s).1 n hn
  calc X i n ≤ runMax X n := le_runMax n i
    _ < (s : ℤ) := h

/-- **No earlier visit.**  If a path has not reached a level before time `n`, its local time at
that level at time `n` is exactly the indicator of standing there. -/
theorem localTime_level_of_lt {X : Fin N → ℕ → ℤ} {n : ℕ} {i : Fin N} {s : ℤ}
    (hlt : ∀ t, t < n → X i t < s) :
    Swarming.localTime (fun t => X i t) n s = if X i n = s then 1 else 0 := by
  classical
  have hsub : ∀ t ∈ (range (n + 1)).filter (fun t => X i t = (s : ℤ)), t = n := by
    intro t ht
    rw [mem_filter, mem_range] at ht
    by_contra hne
    exact absurd ht.2 (ne_of_lt (hlt t (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp ht.1) hne)))
  rw [Swarming.localTime]
  by_cases hx : X i (n) = (s : ℤ)
  · have hmem : n ∈ (range (n + 1)).filter (fun t => X i t = (s : ℤ)) := by
      rw [mem_filter]
      exact ⟨mem_range.mpr (Nat.lt_succ_self _), hx⟩
    have hsingle : (range (n + 1)).filter (fun t => X i t = (s : ℤ)) = {n} := by
      refine Subset.antisymm (fun t ht => ?_) (fun t ht => ?_)
      · rw [mem_singleton]
        exact hsub t ht
      · rw [mem_singleton] at ht
        rw [ht]
        exact hmem
    rw [hsingle, if_pos hx, card_singleton]
  · have hempty : (range (n + 1)).filter (fun t => X i t = (s : ℤ)) = ∅ := by
      refine filter_eq_empty_iff.mpr (fun t ht hval => ?_)
      exact hx (by rw [← hsub t (mem_filter.mpr ⟨ht, hval⟩)]; exact hval)
    rw [hempty, if_neg hx, card_empty]


/-- **No earlier visit to the record level.**  A walker's local time at the level of the
current record time is exactly the indicator of standing there. -/
theorem localTime_level {X : Fin N → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) (s : ℕ)
    (i : Fin N) :
    Swarming.localTime (fun n => X i n) (τ s) (s : ℤ)
      = if X i (τ s) = (s : ℤ) then 1 else 0 :=
  localTime_level_of_lt (fun n hn => pos_lt_level_before hτ hn i)

/-- The same statement for the stored local times of the actual trajectory. -/
theorem ell_level {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ) (i : Fin N) :
    (trajectory p m U (τ s)).ell i (s : ℤ)
      = if (trajectory p m U (τ s)).pos i = (s : ℤ) then 1 else 0 := by
  rw [ell_eq_localTime p m U (τ s) i (s : ℤ)]
  exact localTime_level hτ s i

/-! ## 2. The exact peer-visit count at the record level -/

/-- **The top-row identity.**  For a walker standing at the record level, the number of peer
visits at that level is exactly the number of peers standing there at the record time. -/
theorem otherVisits_top {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    otherVisits (trajectory p m U (τ s)).ell i (s : ℤ)
      = ((univ.erase i).filter
          (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card := by
  classical
  have hell : ∀ j : Fin N, (trajectory p m U (τ s)).ell j (s : ℤ)
      = if (trajectory p m U (τ s)).pos j = (s : ℤ) then 1 else 0 :=
    fun j => ell_level U hτ s j
  unfold otherVisits
  calc ∑ j, (if j = i then 0 else (trajectory p m U (τ s)).ell j (s : ℤ))
      = ∑ j ∈ univ.erase i, (trajectory p m U (τ s)).ell j (s : ℤ) := by
        rw [← sum_erase_add _ _ (mem_univ i), if_pos rfl, Nat.add_zero]
        exact sum_congr rfl (fun j hj => by rw [if_neg (ne_of_mem_erase hj)])
    _ = ∑ j ∈ univ.erase i,
          (if (trajectory p m U (τ s)).pos j = (s : ℤ) then 1 else 0) :=
        sum_congr rfl (fun j _ => hell j)
    _ = ((univ.erase i).filter
          (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card := by
        rw [card_eq_sum_ones, sum_filter]

/-! ## 3. The top row and its exact excitation threshold -/

/-- The top row at a record time: the walkers standing at the record level. -/
def topRow (p : ℝ) (m : ℕ) (U : Array N) (τ : ℕ → ℕ) (s : ℕ) : Finset (Fin N) :=
  univ.filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))

/-- The peer count in top-row form `a - 1`. -/
theorem otherVisits_topRow {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    otherVisits (trajectory p m U (τ s)).ell i (s : ℤ) = (topRow p m U τ s).card - 1 := by
  classical
  have hi' : i ∈ topRow p m U τ s := by
    rw [topRow, mem_filter]
    exact ⟨mem_univ i, hi⟩
  have herase : (topRow p m U τ s).erase i
      = (univ.erase i).filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ)) := by
    ext j
    simp only [topRow, mem_erase, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hji, hpj⟩
      exact ⟨⟨hji, trivial⟩, hpj⟩
    · rintro ⟨⟨hji, -⟩, hpj⟩
      exact ⟨hji, hpj⟩
  rw [otherVisits_top U hτ hi, ← herase, card_erase_of_mem hi']

/-- Excitation of a top-row walker is exactly the top-row count threshold. -/
theorem excited_top_iff {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    Excited m (trajectory p m U (τ s)).ell i (s : ℤ) ↔ m ≤ (topRow p m U τ s).card - 1 := by
  unfold Excited
  rw [otherVisits_topRow U hτ hi]

/-- The peer count in the two forms used below. -/
theorem peerCount_eq {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    ((univ.erase i).filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card
      = (topRow p m U τ s).card - 1 := by
  rw [← otherVisits_top U hτ hi, otherVisits_topRow U hτ hi]

/-- **The exact right probability of a top-row walker at a record time.** -/
theorem rightProbability_top {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ)
      = if m ≤ (topRow p m U τ s).card - 1 then p else 1 / 2 := by
  unfold rightProbability
  by_cases h : Excited m (trajectory p m U (τ s)).ell i (s : ℤ)
  · rw [if_pos h, if_pos ((excited_top_iff U hτ hi).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((excited_top_iff U hτ hi).mpr hc))]

/-- **A unique leader is cold.**  At a record time, a walker that is alone at the record level
has right probability exactly `1/2`, for every `m ≥ 1`. -/
theorem rightProbability_unique_leader {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N)
    {τ : ℕ → ℕ} (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ))
    (huniq : ∀ j : Fin N, j ≠ i → (trajectory p m U (τ s)).pos j ≠ (s : ℤ)) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = 1 / 2 := by
  have hempty : (univ.erase i).filter
      (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ)) = ∅ := by
    refine filter_eq_empty_iff.mpr (fun j hj hval => ?_)
    exact huniq j (ne_of_mem_erase hj) hval
  have hzero : ((univ.erase i).filter
      (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card = 0 := by
    rw [hempty, card_empty]
  have htop : (topRow p m U τ s).card - 1 = 0 := by
    rw [← peerCount_eq U hτ hi, hzero]
  unfold rightProbability
  rw [excited_top_iff U hτ hi, htop, if_neg (by omega : ¬ m ≤ 0)]

/-- **Thin top row is cold.**  If the top-row count is at most `m`, every top-row walker has
right probability exactly `1/2`. -/
theorem rightProbability_top_cold {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ))
    (hthin : (topRow p m U τ s).card ≤ m) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = 1 / 2 := by
  have hnot : ¬ Excited m (trajectory p m U (τ s)).ell i (s : ℤ) := by
    rw [excited_top_iff U hτ hi]
    have hpos1 : 1 ≤ m := hm
    omega
  unfold rightProbability
  rw [if_neg hnot]

/-- **Thick top row is hot.**  If the top-row count is at least `m + 1`, every top-row walker
is excited and has right probability exactly `p`. -/
theorem rightProbability_top_hot {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ))
    (hthick : m + 1 ≤ (topRow p m U τ s).card) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = p := by
  have hexc : Excited m (trajectory p m U (τ s)).ell i (s : ℤ) := by
    rw [excited_top_iff U hτ hi]
    omega
  unfold rightProbability
  rw [if_pos hexc]

/-- **The `m ≥ N` regime: the top row is always cold.**  When `N ≤ m` the top row of every
record time of every trajectory is unexcited, so every leader has right probability exactly
`1/2`. -/
theorem rightProbability_top_of_N_le_m {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (hNm : N ≤ m) {s : ℕ} {i : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ)) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = 1 / 2 := by
  refine rightProbability_top_cold hm U hτ hi ?_
  have hle : (topRow p m U τ s).card ≤ N := by
    rw [topRow]
    calc (univ.filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card
        ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
      _ = N := by simp
  omega

/-! ## 4. Hot laggard and the exact compression force -/

/-- **A hot laggard.**  If `m ≤ N-1` and the lowest walker of the pack stands at a nonnegative
site at a record time, its right probability is exactly `p`. -/
theorem rightProbability_bottom {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N - 1) (U : Array N)
    {τ : ℕ → ℕ} (hs : ℕ) {k : Fin N}
    (hk : (trajectory p m U (τ hs)).pos k
      = runMin (fun i n => (trajectory p m U n).pos i) (τ hs))
    (hpos : 0 ≤ (trajectory p m U (τ hs)).pos k) :
    rightProbability p m (trajectory p m U (τ hs)).ell k ((trajectory p m U (τ hs)).pos k) = p := by
  classical
  have hmin : ∀ j : Fin N,
      (trajectory p m U (τ hs)).pos k ≤ (trajectory p m U (τ hs)).pos j := by
    intro j
    rw [hk]
    exact runMin_le (X := fun i n => (trajectory p m U n).pos i) (τ hs) j
  have hexc : Excited m (trajectory p m U (τ hs)).ell k ((trajectory p m U (τ hs)).pos k) :=
    excited_of_isMin p m U (τ hs) k hpos rfl hmin hmN
  unfold rightProbability
  rw [if_pos hexc]

/-- **The compression force at a record time, exactly.**  With a unique leader, a nonnegative
laggard and `m ≤ N-1`, the leader's right probability is `1/2`, the laggard's is `p`, and the
leader-minus-laggard one-step drift is exactly `-(2p-1)`. -/
theorem top_cold_bottom_hot {p : ℝ} (hp : 1 / 2 < p) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N - 1)
    (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i k : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ))
    (huniq : ∀ j : Fin N, j ≠ i → (trajectory p m U (τ s)).pos j ≠ (s : ℤ))
    (hk : (trajectory p m U (τ s)).pos k
      = runMin (fun i n => (trajectory p m U n).pos i) (τ s))
    (hpos : 0 ≤ (trajectory p m U (τ s)).pos k) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = 1 / 2 ∧
      rightProbability p m (trajectory p m U (τ s)).ell k
        ((trajectory p m U (τ s)).pos k) = p ∧
      (2 * rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) - 1)
        - (2 * rightProbability p m (trajectory p m U (τ s)).ell k
            ((trajectory p m U (τ s)).pos k) - 1) = -(2 * p - 1) := by
  have hlead := rightProbability_unique_leader hm U hτ hi huniq
  have hlag := rightProbability_bottom hm hmN U s hk hpos
  refine ⟨hlead, hlag, ?_⟩
  rw [hlead, hlag]
  ring

/-! ## 5. The exact top-row left-factor product -/

/-- **The cold top-row product.**  The product of the top row's left-step probabilities is
exactly `(1/2)^a` when the row is thin, where `a` is the row count. -/
theorem top_row_product_cold {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ)
    (hthin : (topRow p m U τ s).card ≤ m) :
    ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = (1 / 2) ^ (topRow p m U τ s).card := by
  calc ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = ∏ _i ∈ topRow p m U τ s, (1 / 2 : ℝ) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        rw [topRow, mem_filter] at hi
        rw [rightProbability_top_cold hm U hτ hi.2 hthin]
        norm_num
    _ = (1 / 2) ^ (topRow p m U τ s).card := by
        simp

/-- **The `m ≥ N` cold-row product.**  In the regime `N ≤ m`, every top row of every record time
has left-factor product exactly `(1/2)^a`: no excitation at the record level is possible. -/
theorem top_row_product_of_N_le_m {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (hNm : N ≤ m) (s : ℕ) :
    ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = (1 / 2) ^ (topRow p m U τ s).card := by
  refine top_row_product_cold hm U hτ s ?_
  have hle : (topRow p m U τ s).card ≤ N := by
    rw [topRow]
    calc (univ.filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card
        ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
      _ = N := by simp
  omega

/-- The top row is nonempty: at a record time some walker stands at the level. -/
theorem topRow_card_pos {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ) :
    0 < (topRow p m U τ s).card := by
  have h := (hτ s).2
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
    (s := (univ : Finset (Fin N))) univ_nonempty
    (fun i => (trajectory p m U (τ s)).pos i)
  have hmem : i ∈ topRow p m U τ s := by
    rw [topRow, mem_filter]
    exact ⟨mem_univ i, by rw [← hi]; exact h⟩
  exact card_pos.mpr ⟨i, hmem⟩

/-- The top row never exceeds the population. -/
theorem topRow_card_le {p : ℝ} {m : ℕ} (U : Array N) (τ : ℕ → ℕ) (s : ℕ) :
    (topRow p m U τ s).card ≤ N := by
  rw [topRow]
  calc (univ.filter (fun j => (trajectory p m U (τ s)).pos j = (s : ℤ))).card
      ≤ (univ : Finset (Fin N)).card := card_le_card (filter_subset _ _)
    _ = N := by simp

/-- **Thin top row, hot laggard.**  The exact compression force without uniqueness of the
leader: a thin top row is cold, a nonnegative laggard is hot, and the drift gap is `-(2p-1)`. -/
theorem thin_top_hot_bottom {p : ℝ} (hp : 1 / 2 < p) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N - 1)
    (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ} {i k : Fin N}
    (hi : (trajectory p m U (τ s)).pos i = (s : ℤ))
    (hthin : (topRow p m U τ s).card ≤ m)
    (hk : (trajectory p m U (τ s)).pos k
      = runMin (fun i n => (trajectory p m U n).pos i) (τ s))
    (hpos : 0 ≤ (trajectory p m U (τ s)).pos k) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = 1 / 2 ∧
      rightProbability p m (trajectory p m U (τ s)).ell k
        ((trajectory p m U (τ s)).pos k) = p ∧
      (2 * rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) - 1)
        - (2 * rightProbability p m (trajectory p m U (τ s)).ell k
            ((trajectory p m U (τ s)).pos k) - 1) = -(2 * p - 1) := by
  have hlead := rightProbability_top_cold hm U hτ hi hthin
  have hlag := rightProbability_bottom hm hmN U s hk hpos
  refine ⟨hlead, hlag, ?_⟩
  rw [hlead, hlag]
  ring

/-! ## 6. Coalescence is exactly the thick-top regime -/

/-- The top row is everything iff the pack is coalesced at the record level. -/
theorem topRow_eq_univ_iff {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ) :
    topRow p m U τ s = univ ↔ ∀ j : Fin N, (trajectory p m U (τ s)).pos j = (s : ℤ) := by
  constructor
  · intro h j
    have hj : j ∈ topRow p m U τ s := by
      rw [h]
      exact mem_univ j
    rw [topRow, mem_filter] at hj
    exact hj.2
  · intro h
    ext j
    simp [topRow, h j]

/-- **Coalescence is the hot regime.**  If every walker stands at the record level and
`m ≤ N-1`, the top row is all of `univ`, hence thick, and every walker's right probability is
exactly `p`.  The top-row count is therefore an order parameter for coalescence: a fully
coalesced record state is hot, a thin top row is cold. -/
theorem rightProbability_coalesced_hot {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N - 1)
    (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) {s : ℕ}
    (hc : ∀ j : Fin N, (trajectory p m U (τ s)).pos j = (s : ℤ)) (i : Fin N) :
    rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ) = p := by
  have hun : topRow p m U τ s = univ := (topRow_eq_univ_iff U hτ s).mpr hc
  have hcard : (topRow p m U τ s).card = N := by
    rw [hun]
    simp
  refine rightProbability_top_hot U hτ (hc i) ?_
  omega

/-- **The two-walker, `m = 1` record state.**  For `N = 2` and `m = 1`, at a record time of a
nonnegative window with a unique leader, the leader is cold (`1/2`), the laggard is hot (`p`),
and the leader-minus-laggard drift is exactly `-(2p-1)`.  This is the minimal non-degenerate
case of the paper's coalescence step, with the `N = m = 2` degenerate case excluded. -/
theorem two_walker_record_drift {p : ℝ} (hp : 1 / 2 < p) (U : Array 2) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p 1 U n).pos i) τ) {s : ℕ} {i k : Fin 2}
    (hi : (trajectory p 1 U (τ s)).pos i = (s : ℤ))
    (huniq : ∀ j : Fin 2, j ≠ i → (trajectory p 1 U (τ s)).pos j ≠ (s : ℤ))
    (hk : (trajectory p 1 U (τ s)).pos k
      = runMin (fun i n => (trajectory p 1 U n).pos i) (τ s))
    (hpos : 0 ≤ (trajectory p 1 U (τ s)).pos k) :
    rightProbability p 1 (trajectory p 1 U (τ s)).ell i (s : ℤ) = 1 / 2 ∧
      rightProbability p 1 (trajectory p 1 U (τ s)).ell k
        ((trajectory p 1 U (τ s)).pos k) = p ∧
      (2 * rightProbability p 1 (trajectory p 1 U (τ s)).ell i (s : ℤ) - 1)
        - (2 * rightProbability p 1 (trajectory p 1 U (τ s)).ell k
            ((trajectory p 1 U (τ s)).pos k) - 1) = -(2 * p - 1) := by
  exact top_cold_bottom_hot hp le_rfl (by norm_num : 1 ≤ 2 - 1) U hτ hi huniq hk hpos

/-- **The hot top-row product.**  The product of the top row's left-step probabilities is
exactly `(1-p)^a` when the row is thick. -/
theorem top_row_product_hot {p : ℝ} {m : ℕ} (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ)
    (hthick : m + 1 ≤ (topRow p m U τ s).card) :
    ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = (1 - p) ^ (topRow p m U τ s).card := by
  calc ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = ∏ _i ∈ topRow p m U τ s, (1 - p) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        rw [topRow, mem_filter] at hi
        rw [rightProbability_top_hot U hτ hi.2 hthick]
    _ = (1 - p) ^ (topRow p m U τ s).card := by
        simp

/-- **The top-row left-factor product, unified.**  At a record time the product of the top
row's left-step probabilities is `(1/2)^a` for a thin row and `(1-p)^a` for a thick row, where
`a` is the row count.  Since "the top row all steps left" is the complement of "the record level
advances", this is the exact one-step factor of the record-advance law. -/
theorem top_row_product {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (U : Array N) {τ : ℕ → ℕ}
    (hτ : IsRecord (fun i n => (trajectory p m U n).pos i) τ) (s : ℕ) :
    ∏ i ∈ topRow p m U τ s,
        (1 - rightProbability p m (trajectory p m U (τ s)).ell i (s : ℤ))
      = if (topRow p m U τ s).card ≤ m then (1 / 2) ^ (topRow p m U τ s).card
          else (1 - p) ^ (topRow p m U τ s).card := by
  by_cases hthin : (topRow p m U τ s).card ≤ m
  · rw [if_pos hthin]
    exact top_row_product_cold hm U hτ s hthin
  · rw [if_neg hthin]
    refine top_row_product_hot U hτ s ?_
    omega

end TopRow
