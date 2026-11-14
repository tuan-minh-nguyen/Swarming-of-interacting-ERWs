/-
Local times (occupation times) of a path, §1-§3 of `main_1d_revised.tex`.

The paper defines, for the `i`-th walker,

  L_n^i(x) = ∑_{t=0}^{n} 1{X_t^i = x}                                 (local time)

and uses three facts about this object that are *purely combinatorial* (no probability):

*  the fibre-counting identity `∑_x L_n(x) = n + 1` and `L_n(x) = 0` off the range
   (used implicitly whenever the paper counts visits, and in the state description
   (states) of §3.1, where the constraint `η_i(-d_i) ≥ 1` encodes "the walker is at
   a site it has visited");
*  the truncation equivalence

     ∑_{j≠i} ℓ_j ≥ m  ⟺  ∑_{j≠i} (ℓ_j ∧ m) ≥ m ,

   which is the sentence in §3.1 justifying that the record chain may keep the local
   times *capped at `m`* ("We therefore preserve the transition probabilities when we
   truncate the local times at `m`.");
*  the one-step update `L_{n+1}(x) = L_n(x) + 1{X_{n+1} = x}`, matching the recipe
   "After each jump of walker `i`, we increase its capped local time at its new
   position by one, up to a maximum of `m`."

Everything below is proved from `Finset` counting only.
-/
import Swarm.Imports

namespace Swarming

open Finset

variable {σ : Type*} [DecidableEq σ]

/-- Local time of the path `X` at the site `x` up to time `n` (inclusive):
the paper's `L_n(x) = ∑_{t=0}^n 1{X_t = x}`. -/
def localTime (X : ℕ → σ) (n : ℕ) (x : σ) : ℕ :=
  #((range (n + 1)).filter fun t => X t = x)

lemma localTime_def (X : ℕ → σ) (n : ℕ) (x : σ) :
    localTime X n x = #((range (n + 1)).filter fun t => X t = x) := rfl

@[simp]
lemma localTime_zero (X : ℕ → σ) (x : σ) :
    localTime X 0 x = if X 0 = x then 1 else 0 := by
  rw [localTime, Finset.card_filter, Finset.sum_range_one]

/-- The one-step update of the local time. -/
lemma localTime_succ (X : ℕ → σ) (n : ℕ) (x : σ) :
    localTime X (n + 1) x = localTime X n x + if X (n + 1) = x then 1 else 0 := by
  have h : range (n + 1 + 1) = insert (n + 1) (range (n + 1)) :=
    Finset.range_add_one
  rw [localTime, localTime, h, filter_insert]
  split_ifs with hx
  · rw [card_insert_of_notMem, add_comm]
    simp
  · simp

/-- Local times are monotone in time. -/
lemma localTime_mono (X : ℕ → σ) {n m : ℕ} (hnm : n ≤ m) (x : σ) :
    localTime X n x ≤ localTime X m x := by
  apply card_le_card
  intro t ht
  simp only [mem_filter, mem_range] at ht ⊢
  exact ⟨by omega, ht.2⟩

/-- The local time at `x` vanishes exactly when `x` is not visited before time `n`. -/
lemma localTime_eq_zero_iff (X : ℕ → σ) (n : ℕ) (x : σ) :
    localTime X n x = 0 ↔ ∀ t, t ≤ n → X t ≠ x := by
  rw [localTime, card_eq_zero, filter_eq_empty_iff]
  simp

/-- The local time at `x` is positive exactly when `x` is visited by time `n`. -/
lemma localTime_pos_iff (X : ℕ → σ) (n : ℕ) (x : σ) :
    0 < localTime X n x ↔ ∃ t, t ≤ n ∧ X t = x := by
  rw [localTime, card_pos, filter_nonempty_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, by simpa using ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, by simp [ht], hx⟩

lemma localTime_eq_zero_of_ne (X : ℕ → σ) (n : ℕ) {x : σ} (h : ∀ t, t ≤ n → X t ≠ x) :
    localTime X n x = 0 :=
  (localTime_eq_zero_iff X n x).2 h

/-- The local time is bounded by the number of time instants. -/
lemma localTime_le (X : ℕ → σ) (n : ℕ) (x : σ) : localTime X n x ≤ n + 1 := by
  calc localTime X n x ≤ #(range (n + 1)) := card_filter_le _ _
    _ = n + 1 := card_range _

/-- **Fibre counting**: the local times of a path sum to the number of time instants.
The paper's `∑_x L_n(x) = n + 1`, stated for an arbitrary finite set of sites containing
the range of the path. -/
theorem sum_localTime (X : ℕ → σ) (n : ℕ) (s : Finset σ) (hs : ∀ t, t ≤ n → X t ∈ s) :
    ∑ x ∈ s, localTime X n x = n + 1 := by
  have h := card_eq_sum_card_fiberwise (s := range (n + 1)) (t := s) (f := X)
    (fun t ht => hs t (by simpa using ht))
  rw [card_range] at h
  simpa only [localTime] using h.symm

/-- **Fibre counting**, global form. -/
theorem sum_localTime_univ [Fintype σ] (X : ℕ → σ) (n : ℕ) :
    ∑ x, localTime X n x = n + 1 :=
  sum_localTime X n univ (fun _ _ => mem_univ _)

/-- The set of sites with positive local time is exactly the range of the path. -/
theorem support_localTime [Fintype σ] (X : ℕ → σ) (n : ℕ) :
    (univ.filter fun x => 0 < localTime X n x) = (range (n + 1)).image X := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_range, Nat.lt_succ_iff]
  exact localTime_pos_iff X n x

/-- Consequently the number of visited sites is the size of the range. -/
theorem card_support_localTime [Fintype σ] (X : ℕ → σ) (n : ℕ) :
    #(univ.filter fun x => 0 < localTime X n x) = #((range (n + 1)).image X) := by
  rw [support_localTime]

/-- At a site that has never been visited the local time is zero, so in particular
the local time at a site strictly above the running maximum vanishes.  This is the
combinatorial content of "`η_i(x) = 0` for `x > 0`" in (states). -/
lemma localTime_eq_zero_of_lt_all (X : ℕ → σ) (n : ℕ) {x : σ} (h : ∀ t, t ≤ n → x ≠ X t) :
    localTime X n x = 0 :=
  localTime_eq_zero_of_ne X n (fun t ht => (h t ht).symm)

/-! ### Capping the local times at `m` -/

/-- **Truncation lemma.**  For nonnegative integers `ℓ_j`, capping the summands at `m`
does not change whether their sum reaches `m`.  This is the exact step used in §3.1:

  `∑_{j≠i} ℓ_j ≥ m  ⟺  ∑_{j≠i} (ℓ_j ∧ m) ≥ m`. -/
theorem min_cap_sum_ge_iff {ι : Type*} (s : Finset ι) (ℓ : ι → ℕ) (m : ℕ) :
    m ≤ ∑ i ∈ s, min (ℓ i) m ↔ m ≤ ∑ i ∈ s, ℓ i := by
  constructor
  · intro h
    exact le_trans h (sum_le_sum fun i _ => min_le_left _ _)
  · intro h
    by_cases hex : ∃ i ∈ s, m ≤ ℓ i
    · obtain ⟨i, hi, him⟩ := hex
      have h1 : min (ℓ i) m = m := min_eq_right him
      calc m = min (ℓ i) m := h1.symm
        _ ≤ ∑ j ∈ s, min (ℓ j) m :=
            single_le_sum (f := fun j => min (ℓ j) m) (fun j _ => Nat.zero_le _) hi
    · push Not at hex
      have h2 : ∑ i ∈ s, min (ℓ i) m = ∑ i ∈ s, ℓ i := by
        refine sum_congr rfl fun i hi => ?_
        exact min_eq_left (hex i hi).le
      rw [h2]
      exact h

/-- The excited/not-excited dichotomy of the paper's transition rule depends only on the
capped local times: with `ℓ_j` the visits paid by walker `j` to the current position of
walker `i`, "at least `m` visited by the others" is the same for `ℓ` and for `ℓ ∧ m`. -/
theorem excited_iff_capped {N : ℕ} (m : ℕ) (ℓ : Fin N → ℕ) (i : Fin N) :
    m ≤ ∑ j ∈ univ.erase i, ℓ j ↔ m ≤ ∑ j ∈ univ.erase i, min (ℓ j) m :=
  (min_cap_sum_ge_iff (univ.erase i) ℓ m).symm

/-- The same statement for the local times themselves: the indicator in (rule) is
unchanged when every local time is capped at `m`. -/
theorem excited_iff_capped_localTime {N : ℕ} (X : Fin N → ℕ → σ) (m n : ℕ) (i : Fin N) :
    m ≤ ∑ j ∈ univ.erase i, localTime (X j) n (X i n) ↔
      m ≤ ∑ j ∈ univ.erase i, min (localTime (X j) n (X i n)) m :=
  excited_iff_capped m (fun j => localTime (X j) n (X i n)) i

end Swarming
