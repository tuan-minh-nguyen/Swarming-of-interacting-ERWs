/-
# Deep-walker excitation from aggregate visits (count-based excitation)

The campaign's record-kernel layer treats one record step with the worst-case per-step
probability `(1-p)` per coordinate, so its only force estimate is
`(1-p)^(N(2K+1))` (`RecCompactReturn.hitKInf_srSet_ge`), which decays geometrically in the
level.  That loss is not a property of the model: on the *actual* interacting array a
walker standing on a nonnegative site that other walkers have already **crossed** is
excited by the raw visit count, without any cookie/mark information.  This file proves
that mechanism and its counting consequence.

Main content (all deterministic, on the actual trajectory `Swarming.Trajectory.trajectory`):

* `exists_pos_eq_of_nonneg_le` -- the path visits every site between `0` and its current
  position (nearest-neighbour intermediate value property);
* `one_le_ell_of_runMax_ge` -- if the running maximum of walker `j` reaches the
  nonnegative site `x`, then `j` has visited `x` at least once;
* `otherVisits_ge_card_crossedSet` -- consequently the number of other walkers whose
  running maximum reaches `x` is a lower bound for `otherVisits`;
* `excited_of_card_crossedSet` -- `m` such walkers already make the walker excited;
* `card_excited_ge_card_nonneg_sub` -- **at most `m` of the walkers standing on
  nonnegative sites can be non-excited**, i.e. the excited set has at least
  `#{i | 0 <= X_n^i} - m` elements.  Equivalently: a non-excited walker on a nonnegative
  site must have at least `N - m` walkers strictly above it, so only the `m` shallowest
  walkers can fail to be excited (ties included);
* `excited_of_isMin` -- consequently, when `m <= N - 1`, every walker standing at the
  swarm minimum on a nonnegative site is excited.

Two further groups of results extend the mechanism beyond the `m <= N - 1` regime:

* `exists_eq_between` and its two one-sided forms -- the general `+-1` lattice intermediate
  value property on an arbitrary pair of times (not only from the initial site);
* `two_le_ell_of_above_and_back` -- a walker that has been **above** a nonnegative site and
  is now at or below it has visited that site at least **twice** (up-crossing and
  down-crossing).  Summed with multiplicity (`otherVisits_ge_card_crossedSet_add`,
  `excited_of_card_crossedSet_add`) this makes the count criterion fire for thresholds
  `m > N - 1` whenever other walkers have oscillated over the site, i.e. exactly in the
  configurations in which the plain `N - 1` count is too small.

A third, **geometry-free** mechanism closes in on the same conclusion from occupation
concentration instead of geometry (`le_otherVisits_of_ne`,
`excited_of_two_mul_le_own_add_other`, `two_not_excited_impossible`): once the swarm has
visited a site `2m` times, a walker owning at most `m` of those visits is excited there —
for **any** integer site, positive or not — and at most one walker at the site can be
non-excited.

The probabilistic consequence (the `2p-1` drift of the swarm sum) is in `DeepExcDrift.lean`.

No `sorry`, no custom axiom, no `native_decide`.
-/
import Swarm.Reveal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Swarming.Trajectory

open Swarming Swarming.Model Swarming.Uniform Swarming.Paths
open Finset

noncomputable section

variable {N : ℕ}

/-! ### One step is exactly `±1` -/

lemma drivenStep_ge_neg_one (u α : ℝ) : -1 ≤ drivenStep u α := by
  unfold drivenStep
  split <;> norm_num

/-- One step moves the walker down by at most one. -/
lemma pos_succ_ge {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (j : Fin N) :
    (trajectory p m U n).pos j - 1 ≤ (trajectory p m U (n + 1)).pos j := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  have h := drivenStep_ge_neg_one
    (U (j, (trajectory p m U n).pos j, (trajectory p m U n).ell j ((trajectory p m U n).pos j)))
    (rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j))
  omega

/-! ### Intermediate value property of one coordinate -/

/-- A nearest-neighbour path started at `0` passes through every site between `0` and its
current position. -/
theorem exists_pos_eq_of_nonneg_le {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) :
    ∀ (n : ℕ) {x : ℤ}, 0 ≤ x → x ≤ (trajectory p m U n).pos j →
      ∃ t ≤ n, (trajectory p m U t).pos j = x := by
  intro n
  induction n with
  | zero =>
      intro x hx hle
      refine ⟨0, le_rfl, ?_⟩
      have h0 : (trajectory p m U 0).pos j = 0 := by simp
      omega
  | succ n ih =>
      intro x hx hle
      by_cases hxn : x ≤ (trajectory p m U n).pos j
      · obtain ⟨t, ht, hte⟩ := ih hx hxn
        exact ⟨t, le_trans ht (Nat.le_succ n), hte⟩
      · refine ⟨n + 1, le_rfl, ?_⟩
        have h1 := pos_succ_le p m U n j
        have h2 := pos_succ_ge p m U n j
        omega

/-- If the running maximum of walker `j` reaches the nonnegative site `x`, then walker `j`
has visited `x`. -/
theorem one_le_ell_of_runMax_ge {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    {n : ℕ} {x : ℤ} (hx : 0 ≤ x) (hmax : x ≤ runMax p m U j n) :
    1 ≤ (trajectory p m U n).ell j x := by
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j n
  have hreach : x ≤ (trajectory p m U t).pos j := by rw [hte]; exact hmax
  obtain ⟨s, hs, hse⟩ := exists_pos_eq_of_nonneg_le p m U j t hx hreach
  have hpos : 0 < localTime (fun k => (trajectory p m U k).pos j) n x :=
    (localTime_pos_iff _ _ _).mpr ⟨s, le_trans hs ht, hse⟩
  rw [ell_eq_localTime p m U n j x]
  omega

/-! ### The aggregate visit count -/

/-- Walkers other than `i` whose running maximum reaches the nonnegative site `x`. -/
def crossedSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    Finset (Fin N) :=
  by
  classical
  exact univ.filter fun j => j ≠ i ∧ x ≤ runMax p m U j n

/-- The number of other walkers that have reached the nonnegative site `x` is a lower
bound for the number of visits to `x` by the others. -/
theorem otherVisits_ge_card_crossedSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) :
    #(crossedSet p m U n i x) ≤ otherVisits (trajectory p m U n).ell i x := by
  classical
  have hpt : ∀ j : Fin N, (if j = i then 0 else if x ≤ runMax p m U j n then (1 : ℕ) else 0)
      ≤ (if j = i then 0 else (trajectory p m U n).ell j x) := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, if_false]
      split
      · exact one_le_ell_of_runMax_ge p m U j hx ‹x ≤ runMax p m U j n›
      · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ univ) => hpt j)
  have hleft : (∑ j : Fin N,
      (if j = i then 0 else if x ≤ runMax p m U j n then (1 : ℕ) else 0))
      = #(crossedSet p m U n i x) := by
    rw [crossedSet, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · simp [hji]
    · by_cases hc : x ≤ runMax p m U j n <;> simp [hji, hc]
  have hright : (∑ j : Fin N, (if j = i then 0 else (trajectory p m U n).ell j x))
      = otherVisits (trajectory p m U n).ell i x := rfl
  rw [hleft, hright] at hsum
  exact hsum

/-- **Count-based excitation.**  A walker sitting at a nonnegative site is excited as soon
as `m` other walkers have reached that site (their running maxima are at least it); no
cookie information is used, only the raw visit counts. -/
theorem excited_of_card_crossedSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) (hpos : (trajectory p m U n).pos i = x)
    (hcard : m ≤ #(crossedSet p m U n i x)) :
    Excited m (trajectory p m U n).ell i x := by
  have hbound := otherVisits_ge_card_crossedSet p m U n i hx
  exact le_trans hcard hbound

/-! ### At most `m` non-excited walkers on nonnegative sites -/

/-- The walkers standing on nonnegative sites. -/
def nonnegSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : Finset (Fin N) :=
  univ.filter fun i => 0 ≤ (trajectory p m U n).pos i

/-- The walkers that are excited at their own current site. -/
def excitedSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : Finset (Fin N) :=
  by
  classical
  exact univ.filter fun i => Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i)

/-- **At most `m` walkers on nonnegative sites are non-excited.**

If `i` is non-excited at its nonnegative site `x` and `j` stands weakly above `x`, then the
running maximum of `j` reaches `x`, so `j` counts as a visit; hence at most `m-1` walkers
lie weakly above `i`.  Applying this to the lowest non-excited walker bounds the whole
non-excited set by `m`. -/
theorem card_excited_ge_card_nonneg_sub {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    #(nonnegSet p m U n) ≤ #(excitedSet p m U n) + m := by
  classical
  set T : Finset (Fin N) :=
    (nonnegSet p m U n).filter fun i => ¬ Excited m (trajectory p m U n).ell i
      ((trajectory p m U n).pos i) with hT
  have hcard_le : #T ≤ m := by
    rcases T.eq_empty_or_nonempty with hemp | hne
    · simp [hemp]
    · obtain ⟨i₀, hi₀T, hmin⟩ := Finset.exists_min_image T
        (fun i => (trajectory p m U n).pos i) hne
      have hi₀nonneg : 0 ≤ (trajectory p m U n).pos i₀ := by
        have hmem := (Finset.mem_filter.mp hi₀T).1
        rw [nonnegSet, Finset.mem_filter] at hmem
        exact hmem.2
      have hi₀nonexc : ¬ Excited m (trajectory p m U n).ell i₀
          ((trajectory p m U n).pos i₀) := (Finset.mem_filter.mp hi₀T).2
      have hT_erase_sub : T.erase i₀ ⊆ crossedSet p m U n i₀ ((trajectory p m U n).pos i₀) := by
        intro j hj
        rw [Finset.mem_erase] at hj
        obtain ⟨hji, hjT⟩ := hj
        have hjpos : (trajectory p m U n).pos i₀ ≤ (trajectory p m U n).pos j := hmin j hjT
        rw [crossedSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ j, hji, le_trans hjpos (le_runMax p m U j n)⟩
      have hcardT : #T = #(T.erase i₀) + 1 := (Finset.card_erase_add_one hi₀T).symm
      have hle1 : #(T.erase i₀)
          ≤ #(crossedSet p m U n i₀ ((trajectory p m U n).pos i₀)) :=
        Finset.card_le_card hT_erase_sub
      have hle2 : #(crossedSet p m U n i₀ ((trajectory p m U n).pos i₀))
          ≤ otherVisits (trajectory p m U n).ell i₀ ((trajectory p m U n).pos i₀) :=
        otherVisits_ge_card_crossedSet p m U n i₀ hi₀nonneg
      have hlt : otherVisits (trajectory p m U n).ell i₀ ((trajectory p m U n).pos i₀) < m := by
        have := hi₀nonexc
        simp only [Excited] at this
        omega
      omega
  have hsplit : #(nonnegSet p m U n)
      = #((nonnegSet p m U n).filter fun i => Excited m (trajectory p m U n).ell i
            ((trajectory p m U n).pos i)) + #T := by
    rw [hT, Finset.card_filter_add_card_filter_not]
  have hsub : (nonnegSet p m U n).filter
      (fun i => Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i))
      ⊆ excitedSet p m U n := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [excitedSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hi.2⟩
  have hmono := Finset.card_le_card hsub
  omega

/-- When `m ≤ N - 1`, every walker standing at the swarm minimum on a nonnegative site is
excited: all `N - 1` other walkers stand weakly above it, so their running maxima reach
its site. -/
theorem excited_of_isMin {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {x : ℤ} (hx : 0 ≤ x) (hpos : (trajectory p m U n).pos i = x)
    (hmin : ∀ j : Fin N, x ≤ (trajectory p m U n).pos j) (hmN : m ≤ N - 1) :
    Excited m (trajectory p m U n).ell i x := by
  classical
  refine excited_of_card_crossedSet p m U n i hx hpos ?_
  have hsub : (univ.erase i : Finset (Fin N)) ⊆ crossedSet p m U n i x := by
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [crossedSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, hj.1, le_trans (hmin j) (le_runMax p m U j n)⟩
  have hcard : #(univ.erase i : Finset (Fin N)) = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hmono := Finset.card_le_card hsub
  omega

/-- **Excitation of every walker that is not among the `m` highest.**  If at least `m`
other walkers stand weakly above walker `i` (at a nonnegative site), then `i` is excited. -/
theorem excited_of_le_card {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {x : ℤ} (hx : 0 ≤ x) (hpos : (trajectory p m U n).pos i = x)
    (hcard : m ≤ #((univ.erase i).filter fun j =>
      x ≤ (trajectory p m U n).pos j)) :
    Excited m (trajectory p m U n).ell i x := by
  classical
  refine excited_of_card_crossedSet p m U n i hx hpos ?_
  refine le_trans hcard (Finset.card_le_card ?_)
  intro j hj
  rw [Finset.mem_filter, Finset.mem_erase] at hj
  rw [crossedSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ j, hj.1.1, le_trans hj.2 (le_runMax p m U j n)⟩

/-! ### The general lattice intermediate value property

A `±1` lattice path crosses every level between any two of its values.  This is what lets a
walker that has been *above* a site and is now *below* it be counted twice at that site. -/

section LatticeIVT

variable {X : ℕ → ℤ}

/-- A `±1` lattice path crosses every level between its two endpoints. -/
theorem exists_eq_between (hstep : ∀ t, X t - 1 ≤ X (t + 1) ∧ X (t + 1) ≤ X t + 1) :
    ∀ (n : ℕ) {x : ℤ}, (X 0 ≤ x ∧ x ≤ X n) ∨ (X n ≤ x ∧ x ≤ X 0) →
      ∃ t ≤ n, X t = x := by
  intro n
  induction n with
  | zero =>
      intro x h
      refine ⟨0, le_rfl, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  | succ n ih =>
      intro x h
      by_cases hprev : (X 0 ≤ x ∧ x ≤ X n) ∨ (X n ≤ x ∧ x ≤ X 0)
      · obtain ⟨t, ht, hte⟩ := ih hprev
        exact ⟨t, le_trans ht (Nat.le_succ n), hte⟩
      · have hup := (hstep n).1
        have hdn := (hstep n).2
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- `x` lies above `X n`
          have hxn : X n < x := by
            by_contra hcon
            push Not at hcon
            exact hprev (Or.inl ⟨h1, hcon⟩)
          refine ⟨n + 1, le_rfl, ?_⟩
          omega
        · -- `x` lies below `X n`
          have hxn : x < X n := by
            by_contra hcon
            push Not at hcon
            exact hprev (Or.inr ⟨hcon, h2⟩)
          refine ⟨n + 1, le_rfl, ?_⟩
          omega

/-- Upward form: a path starting at or below `x` that reaches `x` visits it. -/
theorem exists_eq_of_le_of_reaches (hstep : ∀ t, X t - 1 ≤ X (t + 1) ∧ X (t + 1) ≤ X t + 1)
    {n : ℕ} {x : ℤ} (h0 : X 0 ≤ x) (hn : x ≤ X n) : ∃ t ≤ n, X t = x :=
  exists_eq_between hstep n (Or.inl ⟨h0, hn⟩)

/-- Downward form: a path starting at or above `x` that descends to `x` visits it. -/
theorem exists_eq_of_ge_of_descends (hstep : ∀ t, X t - 1 ≤ X (t + 1) ∧ X (t + 1) ≤ X t + 1)
    {n : ℕ} {x : ℤ} (h0 : x ≤ X 0) (hn : X n ≤ x) : ∃ t ≤ n, X t = x :=
  exists_eq_between hstep n (Or.inr ⟨hn, h0⟩)

end LatticeIVT

/-- The two-sided one-step bound for one coordinate of the actual trajectory. -/
lemma pos_step_bounds (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    (trajectory p m U t).pos j - 1 ≤ (trajectory p m U (t + 1)).pos j ∧
      (trajectory p m U (t + 1)).pos j ≤ (trajectory p m U t).pos j + 1 :=
  ⟨pos_succ_ge p m U t j, pos_succ_le p m U t j⟩

/-- **A walker that has been above a nonnegative site and is now at or below it has visited
that site at least twice.**  It crossed the site on the way up, and crosses it again on the
way down. -/
theorem two_le_ell_of_above_and_back {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    {n : ℕ} {x : ℤ} (hx : 0 ≤ x) (habove : x + 1 ≤ runMax p m U j n)
    (hback : (trajectory p m U n).pos j ≤ x) :
    2 ≤ (trajectory p m U n).ell j x := by
  classical
  -- a time at which walker `j` is weakly above `x + 1`
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j n
  have htup : x + 1 ≤ (trajectory p m U t).pos j := by rw [hte]; exact habove
  -- first visit: between `0` and `t` the path rises from `0` to `x + 1`
  have hfirst : ∃ s ≤ t, (trajectory p m U s).pos j = x :=
    exists_eq_of_le_of_reaches (X := fun k => (trajectory p m U k).pos j)
      (pos_step_bounds p m U j) (by simpa using hx) (by omega)
  -- second visit: between `t` and `n` the path descends from `x + 1` to at most `x`
  obtain ⟨s, hs, hse⟩ := hfirst
  have hdesc : ∃ v, t ≤ v ∧ v ≤ n ∧ (trajectory p m U v).pos j = x := by
    -- shift the trajectory to start at `t`
    have hstep' : ∀ r, (fun k => (trajectory p m U (t + k)).pos j) r - 1 ≤
        (fun k => (trajectory p m U (t + k)).pos j) (r + 1) ∧
        (fun k => (trajectory p m U (t + k)).pos j) (r + 1) ≤
        (fun k => (trajectory p m U (t + k)).pos j) r + 1 := fun r =>
      pos_step_bounds p m U j (t + r)
    have hstart : x ≤ (fun k => (trajectory p m U (t + k)).pos j) 0 := by
      simpa using (show x ≤ (trajectory p m U t).pos j by omega)
    have hend : (fun k => (trajectory p m U (t + k)).pos j) (n - t) ≤ x := by
      have : t + (n - t) = n := Nat.add_sub_cancel' ht
      simp only [this]
      exact hback
    obtain ⟨w, hw, hwe⟩ := exists_eq_of_ge_of_descends (X := fun k =>
      (trajectory p m U (t + k)).pos j) hstep' hstart hend
    have hle : t + w ≤ n := by omega
    exact ⟨t + w, Nat.le_add_right t w, hle, hwe⟩
  -- the two visits are distinct
  obtain ⟨v, htv, hvn, hve⟩ := hdesc
  have hdistinct : s ≠ v := by
    intro hEq
    rw [hEq] at hs
    have hvt : v = t := le_antisymm hs htv
    rw [hvt] at hve
    omega
  have hmem1 : s ∈ (range (n + 1)).filter (fun k => (trajectory p m U k).pos j = x) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hse⟩
  have hmem2 : v ∈ (range (n + 1)).filter (fun k => (trajectory p m U k).pos j = x) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hve⟩
  have hpair : 2 ≤ #({s, v} : Finset ℕ) := by
    rw [Finset.card_pair hdistinct]
  have hsub : ({s, v} : Finset ℕ)
      ⊆ (range (n + 1)).filter (fun k => (trajectory p m U k).pos j = x) := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hmem1
    · exact hmem2
  have := Finset.card_le_card hsub
  rw [ell_eq_localTime p m U n j x, localTime]
  omega

/-- Walkers other than `i` that have been above the site `x` and are now at or below it;
they contribute **two** visits to `x`. -/
def returnedSet {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    Finset (Fin N) := by
  classical
  exact univ.filter fun j => j ≠ i ∧ x + 1 ≤ runMax p m U j n ∧
    (trajectory p m U n).pos j ≤ x

/-- **Visits with multiplicity.**  Each other walker whose running maximum reaches `x`
contributes one visit, and each that has been above `x` and is now at or below it
contributes a second one. -/
theorem otherVisits_ge_card_crossedSet_add {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) :
    #(crossedSet p m U n i x) + #(returnedSet p m U n i x)
      ≤ otherVisits (trajectory p m U n).ell i x := by
  classical
  have hpt : ∀ j : Fin N, (if j = i then 0 else if x ≤ runMax p m U j n then (1 : ℕ) else 0)
      + (if j = i then 0
          else if x + 1 ≤ runMax p m U j n ∧ (trajectory p m U n).pos j ≤ x then 1 else 0)
      ≤ (if j = i then 0 else (trajectory p m U n).ell j x) := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, if_false]
      by_cases h1 : x ≤ runMax p m U j n
      · have h11 : 1 ≤ (trajectory p m U n).ell j x :=
          one_le_ell_of_runMax_ge p m U j hx h1
        by_cases h2 : x + 1 ≤ runMax p m U j n ∧ (trajectory p m U n).pos j ≤ x
        · have h22 : 2 ≤ (trajectory p m U n).ell j x :=
            two_le_ell_of_above_and_back p m U j hx h2.1 h2.2
          rw [if_pos h1, if_pos h2]
          omega
        · rw [if_pos h1, if_neg h2]
          omega
      · have h2 : ¬ (x + 1 ≤ runMax p m U j n ∧ (trajectory p m U n).pos j ≤ x) := by
          intro hc
          exact h1 (le_trans (by omega : x ≤ x + 1) hc.1)
        rw [if_neg h1, if_neg h2]
        omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ univ) => hpt j)
  have hleft1 : (∑ j : Fin N,
      (if j = i then 0 else if x ≤ runMax p m U j n then (1 : ℕ) else 0))
      = #(crossedSet p m U n i x) := by
    rw [crossedSet, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · simp [hji]
    · by_cases hc : x ≤ runMax p m U j n <;> simp [hji, hc]
  have hleft2 : (∑ j : Fin N,
      (if j = i then 0
        else if x + 1 ≤ runMax p m U j n ∧ (trajectory p m U n).pos j ≤ x then 1 else 0))
      = #(returnedSet p m U n i x) := by
    rw [returnedSet, Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · simp [hji]
    · by_cases hc : x + 1 ≤ runMax p m U j n ∧ (trajectory p m U n).pos j ≤ x <;>
        simp [hji, hc]
  rw [Finset.sum_add_distrib, hleft1, hleft2] at hsum
  exact hsum

/-- **Excitation with multiplicity.**  If `m` is at most the number of other walkers that
reached the nonnegative site plus the number of those that have been above it and are now at
or below it, then the walker is excited.  This covers thresholds `m > N - 1` whenever other
walkers have oscillated over the site. -/
theorem excited_of_card_crossedSet_add {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) (hpos : (trajectory p m U n).pos i = x)
    (hcard : m ≤ #(crossedSet p m U n i x) + #(returnedSet p m U n i x)) :
    Excited m (trajectory p m U n).ell i x := by
  have hbound := otherVisits_ge_card_crossedSet_add p m U n i hx
  exact le_trans hcard hbound

end

/-! ### Occupation concentration: a geometry-free excitation criterion

The criteria above used the geometry (walkers above a nonnegative site have crossed it).
There is also a purely occupation-theoretic mechanism: once the swarm's visits to a site
exceed `2m`, only a walker that itself owns most of those visits can be non-excited. -/

/-- A walker's own visits at a site are part of the others' visit count of every *other*
walker standing there. -/
theorem le_otherVisits_of_ne {N : ℕ} (ell : LocalTimes N) {i j : Fin N} (hij : i ≠ j)
    (x : ℤ) : ell j x ≤ otherVisits ell i x := by
  classical
  rw [otherVisits]
  have h := Finset.single_le_sum (s := (univ : Finset (Fin N)))
    (f := fun k : Fin N => if k = i then 0 else ell k x)
    (fun k _ => by split <;> exact Nat.zero_le _) (Finset.mem_univ j)
  rwa [if_neg (Ne.symm hij)] at h

/-- **Excitation from occupation concentration**: if the swarm's visits to the site `x`
(own plus others') are at least `2m` and the walker itself owns at most `m` of them, then the
walker is excited at `x`.  No sign condition on `x` is needed. -/
theorem excited_of_two_mul_le_own_add_other {N : ℕ} (m : ℕ) (ell : LocalTimes N) (i : Fin N)
    {x : ℤ} (htot : 2 * m ≤ ell i x + otherVisits ell i x) (hown : ell i x ≤ m) :
    Excited m ell i x := by
  rw [Excited]
  omega

/-- **At most one walker per site is non-excited** once the swarm has `2m` visits there and
two non-excited walkers would each own every visit of the other. -/
theorem two_not_excited_impossible {N : ℕ} (m : ℕ) (ell : LocalTimes N) {i j : Fin N}
    (hij : i ≠ j) {x : ℤ} (htot : 2 * m ≤ ell i x + otherVisits ell i x)
    (hi : ¬ Excited m ell i x) (hj : ¬ Excited m ell j x) : False := by
  rw [Excited] at hi hj
  have h1 : ell j x ≤ otherVisits ell i x := le_otherVisits_of_ne ell hij x
  have h2 : ell i x ≤ otherVisits ell j x := le_otherVisits_of_ne ell (Ne.symm hij) x
  omega


end Swarming.Trajectory
