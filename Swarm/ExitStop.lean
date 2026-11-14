/-
  **The interval exit time of the actual interacting excited walk as a stopping time
  of a genuine nested path filtration, with its optional-section interface.**

  This module is deliberately confined to one layer of the campaign:

  * the *stopping-time* layer of the paper's crossing argument.  `GAP.md` in
    `results/lean/areas/transience/` records as missing (i) a genuine
    `MeasureTheory.Filtration` on the actual array space on which the actual
    walker is adapted and (ii) the paper's exit time
    `τ s = T_{b0}(s) ∧ T_{b1+1}(s)` as a `MeasureTheory.IsStoppingTime`.
    It also records that the revealed random weights must be measurable at the
    stopping time.  This file supplies exactly that layer, stated about the
    actual `Swarming.Trajectory.trajectory` and its actual array space, and
    nothing else.

  What is proved here.

  1. `hitAfter X A σ` — the first time `≥ σ` at which `X` enters `A`, where the
     *starting time `σ` is itself a random time*.  Mathlib has `hittingAfter`
     only for a deterministic start.  This is the form the paper needs when the
     starting time is the bad time (itself a stopping time).  `hitAfter_le_iff`
     is the defining universal property, `hitAfter_eq_coe_iff` the finite-value
     characterisation, and `isStoppingTime_hitAfter` proves that a hitting time
     after a stopping time is a stopping time.

  2. `exitAfter X lo hi σ` — the first time `≥ σ` at which the walker leaves the
     open window `(lo, hi)`, i.e. reaches `≤ lo` or `≥ hi` (this is the
     convention of `Swarm/StoppedCross.lean`, `lo = b0`,
     `hi = b1 + 1`).  It is `min` of two `hitAfter`s, hence a stopping time
     (`isStoppingTime_exitAfter`), it is `≥ σ`, the walker is *inside* the
     window at every time strictly before it (`interior_of_lt_exitAfter`), and
     at a finite exit time it is *outside* the window (`exitAfter_eq_coe`).
     The last two are exactly the two facts the stopped crossing bound consumes.

  3. `IsStoppingTime.mono` — a stopping time for `ℱ` is a stopping time for any
     finer filtration; and `measurableSpace_le_exitAfter` (`ℱ_σ ≤ ℱ_τ`) — the
     past at the starting time is inside the σ-algebra at the exit time.

  4. `measurable_stoppedValue_adapted` and
     `measurableSet_inter_gt_preimage` — the `ℱ_τ` optional-section interface:
     the value of the walker at the stopping time is measurable at `ℱ_τ`, and any
     pre-`τ` event is measurable at `ℱ_τ`.  This is what a conditional statement
     "at the stopping time" needs; see `measurableSet_exitAtBottom` and
     `measurableSet_stoppedValue_inter_le`.

  5. The concrete instantiation on the actual model: `posFilt N p m` is a
     genuine nested filtration of the actual trajectory (a Mathlib `Filtration`
     inside the ambient product σ-algebra of the i.i.d. uniform array) generated
     by the swarm positions, which by `measurable_ell_posFilt` is also the
     filtration of the full trajectory *states* `X_0, …, X_n`; by
     `posFilt_le_iff` it is the smallest filtration to which the positions are
     adapted.  The paper's exit time `trajExit` out of `(b0, b1 + 1)` of walker
     `i` is then a stopping time for `posFilt` and for every filtration
     containing it (`isStoppingTime_trajExit`, `..._of_posFilt_le`), its
     finite-time value is outside the window (`trajExit_eq_coe`), before it it is
     inside (`trajExit_interior`), the event `{τ ≤ N}` has the explicit form of
     `trajExit_le_iff`, and the paper's "exited at the bottom by time `N`"
     event is `ℱ_N`-measurable (`measurableSet_stoppedValue_inter_le`).

  Not proved here, and not claimed: the conditional jump law of the next step in
  the nested filtration, the domination of the revealed weights at the stopping
  time, the submartingale optional-sampling step, and the crossing probability
  itself.  Those are separate directions; `STATUS.md` records the ledger.
  Everything below has complete proofs and no added axioms; the axiom audit
  is at the end.
-/
import Swarm.Imports
import Swarm.MeasurableInc

open MeasureTheory
open scoped Topology ENNReal

namespace SwarmStop

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ### Hitting a set after a random time

Mathlib's `MeasureTheory.hittingAfter u s n` starts at the *deterministic* time `n`.
The paper needs the start to be the random bad time `s`.  We therefore take the infimum
over all `n ≥ σ ω` with `X n ω ∈ A`, with value `⊤` when there is none. -/

/-- The first time `≥ σ ω` at which the process `X` enters `A`; `⊤` if there is none.
The starting time `σ : Ω → WithTop ℕ` is allowed to be random. -/
noncomputable def hitAfter (X : ℕ → Ω → ℤ) (A : Set ℤ) (σ : Ω → WithTop ℕ) : Ω → WithTop ℕ := by
  classical
  exact fun ω => if h : ∃ n : ℕ, (n : WithTop ℕ) ≥ σ ω ∧ X n ω ∈ A then ((Nat.find h : ℕ) : WithTop ℕ)
    else ⊤

/-- The defining universal property: `hitAfter X A σ ω` is the *least* `n ≥ σ ω` with
`X n ω ∈ A`.  This is the only property of `hitAfter` used below, and it avoids any
normal-form dependence on the `Nat.find` implementation. -/
theorem hitAfter_le_iff {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ : Ω → WithTop ℕ} {ω : Ω} (i : ℕ) :
    hitAfter X A σ ω ≤ (i : WithTop ℕ) ↔ ∃ j ≤ i, (j : WithTop ℕ) ≥ σ ω ∧ X j ω ∈ A := by
  classical
  constructor
  · intro hle
    by_cases h : ∃ n : ℕ, (n : WithTop ℕ) ≥ σ ω ∧ X n ω ∈ A
    · have hcoe : hitAfter X A σ ω = ((Nat.find h : ℕ) : WithTop ℕ) := by
        unfold hitAfter
        exact dif_pos h
      rw [hcoe] at hle
      have hni : Nat.find h ≤ i := by exact_mod_cast hle
      exact ⟨Nat.find h, hni, (Nat.find_spec h).1, (Nat.find_spec h).2⟩
    · have htop : hitAfter X A σ ω = ⊤ := by
        unfold hitAfter
        exact dif_neg h
      rw [htop] at hle
      exact absurd hle (by simp)
  · rintro ⟨j, hji, hjσ, hjA⟩
    have h : ∃ n : ℕ, (n : WithTop ℕ) ≥ σ ω ∧ X n ω ∈ A := ⟨j, hjσ, hjA⟩
    have hcoe : hitAfter X A σ ω = ((Nat.find h : ℕ) : WithTop ℕ) := by
      unfold hitAfter
      exact dif_pos h
    rw [hcoe]
    have hle' : Nat.find h ≤ j := Nat.find_le (⟨hjσ, hjA⟩ : (↑j : WithTop ℕ) ≥ σ ω ∧ X j ω ∈ A)
    exact_mod_cast hle'.trans hji

/-- Characterisation of the finite values of `hitAfter`: `n` is the least time `≥ σ ω` at
which `X` is in `A`. -/
theorem hitAfter_eq_coe_iff {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ : Ω → WithTop ℕ} {ω : Ω} {n : ℕ} :
    hitAfter X A σ ω = (n : WithTop ℕ) ↔
      σ ω ≤ (n : WithTop ℕ) ∧ X n ω ∈ A ∧
        ∀ j : ℕ, (j : WithTop ℕ) ≥ σ ω → X j ω ∈ A → n ≤ j := by
  constructor
  · intro h
    have hle : hitAfter X A σ ω ≤ (n : WithTop ℕ) := le_of_eq h
    obtain ⟨j, hjn, hjσ, hjA⟩ := (hitAfter_le_iff n).mp hle
    have hmin : ∀ j : ℕ, (j : WithTop ℕ) ≥ σ ω → X j ω ∈ A → n ≤ j := by
      intro j' hj'σ hj'A
      have h1 : hitAfter X A σ ω ≤ (j' : WithTop ℕ) := (hitAfter_le_iff j').mpr ⟨j', le_rfl, hj'σ, hj'A⟩
      rw [h] at h1
      exact_mod_cast h1
    have hnj : n ≤ j := hmin j hjσ hjA
    have hjn' : j ≤ n := hjn
    have hjn'' : j = n := le_antisymm hjn' hnj
    subst hjn''
    exact ⟨hjσ, hjA, hmin⟩
  · rintro ⟨hσn, hnA, hmin⟩
    have hle : hitAfter X A σ ω ≤ (n : WithTop ℕ) := (hitAfter_le_iff n).mpr ⟨n, le_rfl, hσn, hnA⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq
    · -- `hitAfter = ↑k` with `k < n` contradicts minimality
      obtain ⟨k, hk⟩ : ∃ k : ℕ, hitAfter X A σ ω = (k : WithTop ℕ) := by
        cases hh : hitAfter X A σ ω with
        | top => rw [hh] at hlt; exact absurd hlt (by simp)
        | coe k => exact ⟨k, rfl⟩
      have hklt : k < n := by rw [hk] at hlt; exact_mod_cast hlt
      obtain ⟨j, hjk, hjσ, hjA⟩ := (hitAfter_le_iff k).mp (le_of_eq hk)
      have hnk : n ≤ j := hmin j hjσ hjA
      omega

/-- The starting time is never later than the hitting time. -/
theorem le_hitAfter {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ : Ω → WithTop ℕ} (ω : Ω) :
    σ ω ≤ hitAfter X A σ ω := by
  cases h : hitAfter X A σ ω with
  | top => exact le_top
  | coe n => exact (hitAfter_eq_coe_iff.mp h).1

/-- At a finite hitting time the process is in the target set. -/
theorem hitAfter_mem {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ : Ω → WithTop ℕ} {ω : Ω} {n : ℕ}
    (h : hitAfter X A σ ω = (n : WithTop ℕ)) : X n ω ∈ A :=
  (hitAfter_eq_coe_iff.mp h).2.1

/-- Nothing earlier than the hitting time (and no earlier than the starting time) is in the
target set. -/
theorem not_mem_of_lt_hitAfter {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ : Ω → WithTop ℕ} {ω : Ω}
    {k : ℕ} (hk : (k : WithTop ℕ) < hitAfter X A σ ω) (hσk : (k : WithTop ℕ) ≥ σ ω) :
    X k ω ∉ A := by
  intro hA
  have h : hitAfter X A σ ω ≤ (k : WithTop ℕ) := (hitAfter_le_iff k).mpr ⟨k, le_rfl, hσk, hA⟩
  exact absurd h (not_le.mpr hk)

/-- **Monotonicity in the starting time**: starting earlier can only give an earlier or equal
hitting time.  (`σ ↦ hitAfter X A σ` is monotone, not antitone: a later start shrinks the
admissible set of times.) -/
theorem hitAfter_mono {X : ℕ → Ω → ℤ} {A : Set ℤ} {σ σ' : Ω → WithTop ℕ}
    (h : ∀ ω, σ ω ≤ σ' ω) (ω : Ω) :
    hitAfter X A σ ω ≤ hitAfter X A σ' ω := by
  cases hh : hitAfter X A σ' ω with
  | top => exact le_top
  | coe n =>
    obtain ⟨j, hjn, hjσ, hjA⟩ := (hitAfter_le_iff n).mp (le_of_eq hh)
    exact (hitAfter_le_iff n).mpr ⟨j, hjn, le_trans (h ω) hjσ, hjA⟩

/-- **A hitting time after a random time is a stopping time.**  The starting time `σ` is
required to be a stopping time itself, exactly as the paper's bad time is. -/
theorem isStoppingTime_hitAfter {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℤ} {A : Set ℤ}
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hX : ∀ n, Measurable[ℱ n] (X n)) (hA : MeasurableSet A) :
    IsStoppingTime ℱ (hitAfter X A σ) := by
  classical
  intro i
  have hset : {ω | hitAfter X A σ ω ≤ (i : WithTop ℕ)}
      = ⋃ j ∈ Finset.range (i + 1),
          ({ω | σ ω ≤ (j : WithTop ℕ)} ∩ {ω | X j ω ∈ A}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff]
    rw [hitAfter_le_iff]
    constructor
    · rintro ⟨j, hj, h1, h2⟩; exact ⟨j, Nat.lt_succ_of_le hj, h1, h2⟩
    · rintro ⟨j, hj, h1, h2⟩; exact ⟨j, Nat.le_of_lt_succ hj, h1, h2⟩
  have hR : MeasurableSet[ℱ i] (⋃ j ∈ Finset.range (i + 1),
      ({ω : Ω | σ ω ≤ (j : WithTop ℕ)} ∩ {ω : Ω | X j ω ∈ A})) := by
    refine Finset.measurableSet_biUnion _ fun j hj => ?_
    have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact ((ℱ.mono hji) _ (hσ.measurableSet_le j)).inter ((ℱ.mono hji) _ (hX j hA))
  exact hset.symm ▸ hR

/-! ### The exit time of an open window, started at a random time

The window is `{lo + 1, …, hi - 1}`: the walker has **left** it as soon as it is `≤ lo` or `≥ hi`.
This is exactly the convention of `Swarm/StoppedCross.lean`
(`outside b0 b1 = {x | x ≤ b0 ∨ b1 + 1 ≤ x}` with `lo = b0`, `hi = b1 + 1`). -/

/-- The first time `≥ σ ω` at which the walker is outside the open window `(lo, hi)`. -/
noncomputable def exitAfter (X : ℕ → Ω → ℤ) (lo hi : ℤ) (σ : Ω → WithTop ℕ) : Ω → WithTop ℕ :=
  fun ω => min (hitAfter X (Set.Iic lo) σ ω) (hitAfter X (Set.Ici hi) σ ω)

/-- **The exit time of the window is a stopping time.** -/
theorem isStoppingTime_exitAfter {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℤ} {lo hi : ℤ}
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hX : ∀ n, Measurable[ℱ n] (X n)) :
    IsStoppingTime ℱ (exitAfter X lo hi σ) :=
  IsStoppingTime.min
    (isStoppingTime_hitAfter hσ hX measurableSet_Iic)
    (isStoppingTime_hitAfter hσ hX measurableSet_Ici)

theorem le_exitAfter {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} (ω : Ω) :
    σ ω ≤ exitAfter X lo hi σ ω :=
  le_min (le_hitAfter ω) (le_hitAfter ω)

theorem exitAfter_le_hitAfter_left {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} (ω : Ω) :
    exitAfter X lo hi σ ω ≤ hitAfter X (Set.Iic lo) σ ω :=
  min_le_left _ _

theorem exitAfter_le_hitAfter_right {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} (ω : Ω) :
    exitAfter X lo hi σ ω ≤ hitAfter X (Set.Ici hi) σ ω :=
  min_le_right _ _

/-- **Before the exit time the walker is inside the window.**  This is the structural fact the
stopped crossing estimate consumes: on `{k < τ}` with `k ≥ σ` the walker sits in `(lo, hi)`. -/
theorem interior_of_lt_exitAfter {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} {ω : Ω}
    {k : ℕ} (hσk : σ ω ≤ (k : WithTop ℕ))
    (hk : (k : WithTop ℕ) < exitAfter X lo hi σ ω) :
    lo < X k ω ∧ X k ω < hi := by
  have hk' : (k : WithTop ℕ) < min (hitAfter X (Set.Iic lo) σ ω)
      (hitAfter X (Set.Ici hi) σ ω) := hk
  rw [lt_min_iff] at hk'
  have h1 : X k ω ∉ Set.Iic lo := not_mem_of_lt_hitAfter hk'.1 hσk
  have h2 : X k ω ∉ Set.Ici hi := not_mem_of_lt_hitAfter hk'.2 hσk
  simp only [Set.mem_Iic, Set.mem_Ici, not_le] at h1 h2
  exact ⟨h1, h2⟩

/-- **At a finite exit time the walker is outside the window.** -/
theorem exitAfter_eq_coe {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} {ω : Ω} {n : ℕ}
    (h : exitAfter X lo hi σ ω = (n : WithTop ℕ)) :
    X n ω ≤ lo ∨ hi ≤ X n ω := by
  rcases le_total (hitAfter X (Set.Iic lo) σ ω) (hitAfter X (Set.Ici hi) σ ω) with hle | hle
  · left
    have h1 : hitAfter X (Set.Iic lo) σ ω = (n : WithTop ℕ) := by
      have h' : min (hitAfter X (Set.Iic lo) σ ω)
          (hitAfter X (Set.Ici hi) σ ω) = (n : WithTop ℕ) := h
      rwa [min_eq_left hle] at h'
    simpa using hitAfter_mem h1
  · right
    have h2 : hitAfter X (Set.Ici hi) σ ω = (n : WithTop ℕ) := by
      have h' : min (hitAfter X (Set.Iic lo) σ ω)
          (hitAfter X (Set.Ici hi) σ ω) = (n : WithTop ℕ) := h
      rwa [min_eq_right hle] at h'
    simpa using hitAfter_mem h2

/-- **The `σ`-algebra at the starting time is contained in the `σ`-algebra at the exit time.**
This is the tower-type fact a conditional argument at the random start needs: everything known
at the starting time `σ` (the paper's bad time `s`) is known at the exit time. -/
theorem measurableSpace_le_exitAfter {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℤ} {lo hi : ℤ}
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (hX : ∀ n, Measurable[ℱ n] (X n)) :
    hσ.measurableSpace ≤ (isStoppingTime_exitAfter (lo := lo) (hi := hi) hσ hX).measurableSpace :=
  IsStoppingTime.measurableSpace_mono hσ _ fun ω => le_exitAfter ω

/-- **Path-prefix description of the exit event.**  The exit happens exactly at time `k` iff the
starting time has come, the walker is outside the window at time `k`, and it was strictly inside
the window at every time from `σ` to `k - 1`.  This turns the exit event into a condition on the
finite path prefix `X_0, …, X_k`, which is the form a path-cylinder conditional argument consumes.
-/
theorem exitAfter_eq_coe_iff {X : ℕ → Ω → ℤ} {lo hi : ℤ} {σ : Ω → WithTop ℕ} {ω : Ω} {k : ℕ} :
    exitAfter X lo hi σ ω = (k : WithTop ℕ) ↔
      σ ω ≤ (k : WithTop ℕ) ∧ (X k ω ≤ lo ∨ hi ≤ X k ω) ∧
        (∀ j : ℕ, (j : WithTop ℕ) ≥ σ ω → j < k → lo < X j ω ∧ X j ω < hi) := by
  constructor
  · intro h
    have hk : σ ω ≤ (k : WithTop ℕ) := le_exitAfter ω |>.trans_eq h
    refine ⟨hk, exitAfter_eq_coe h, fun j hjσ hjk => ?_⟩
    exact interior_of_lt_exitAfter hjσ (by rw [h]; exact_mod_cast hjk)
  · rintro ⟨hσk, hout, hinterior⟩
    have hle : exitAfter X lo hi σ ω ≤ (k : WithTop ℕ) := by
      rcases hout with hout | hout
      · exact (exitAfter_le_hitAfter_left ω).trans ((hitAfter_le_iff k).mpr ⟨k, le_rfl, hσk, by simpa using hout⟩)
      · exact (exitAfter_le_hitAfter_right ω).trans ((hitAfter_le_iff k).mpr ⟨k, le_rfl, hσk, by simpa using hout⟩)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j : ℕ, exitAfter X lo hi σ ω = (j : WithTop ℕ) := by
        cases hh : exitAfter X lo hi σ ω with
        | top => rw [hh] at hlt; exact absurd hlt (by simp)
        | coe j => exact ⟨j, rfl⟩
      have hjk : j < k := by rw [hj] at hlt; exact_mod_cast hlt
      have hσj : σ ω ≤ (j : WithTop ℕ) := le_exitAfter ω |>.trans_eq hj
      have hinside := hinterior j hσj hjk
      rcases exitAfter_eq_coe hj with hout' | hout'
      · omega
      · omega

/-! ### Transfer to a finer filtration and the `ℱ_τ` optional-section interface -/

/-- A stopping time for `ℱ` is a stopping time for every finer filtration.  This is how the
concrete result below reaches the paper's enlarged filtration without this file assuming
anything about it. -/
theorem IsStoppingTime.mono {ℱ 𝒢 : Filtration ℕ m0} {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) : IsStoppingTime 𝒢 τ :=
  fun i => (h i) _ (hτ i)

/-- **The walker's value at a stopping time is `ℱ_τ`-measurable.**  Discrete-time version of
Mathlib's `MeasureTheory.measurable_stoppedValue`, for a merely measurable (not continuous)
adapted process. -/
theorem measurable_stoppedValue_adapted {ℱ : Filtration ℕ m0} {u : ℕ → Ω → ℤ}
    {τ : Ω → WithTop ℕ} (hu : ∀ n, Measurable[ℱ n] (u n)) (hτ : IsStoppingTime ℱ τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have hadapted : Adapted ℱ u := hu
  have hstrong : StronglyAdapted ℱ u := hadapted.stronglyAdapted
  have hprog : IsStronglyProgressive ℱ u := hstrong.isStronglyProgressive_of_discrete
  exact measurable_stoppedValue hprog hτ

/-- **Pre-`τ` information is `ℱ_τ`-measurable**: for an adapted process, the event
`{τ > n} ∩ {u n ∈ A}` belongs to the σ-algebra at `τ`. -/
theorem measurableSet_inter_gt_preimage {ℱ : Filtration ℕ m0} {u : ℕ → Ω → ℤ}
    {τ : Ω → WithTop ℕ} (hu : ∀ n, Measurable[ℱ n] (u n)) (hτ : IsStoppingTime ℱ τ)
    {A : Set ℤ} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet[hτ.measurableSpace] ({ω | (n : WithTop ℕ) < τ ω} ∩ u n ⁻¹' A) := by
  refine ⟨?_, ?_⟩
  · exact (le_iSup ℱ n) _ (hτ.measurableSet_gt n) |> fun h => h.inter ((le_iSup ℱ n) _ (hu n hA))
  · intro i
    rcases lt_or_ge i n with hni | hin
    · -- `i < n`: the two time conditions are incompatible
      have hempty : (({ω | (n : WithTop ℕ) < τ ω} ∩ u n ⁻¹' A) ∩ {ω | τ ω ≤ (i : WithTop ℕ)}) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨⟨hτn, _⟩, hτi⟩
        have hle : ((i : WithTop ℕ)) ≤ (n : WithTop ℕ) := by exact_mod_cast Nat.le_of_lt hni
        exact absurd hτi (not_le.mpr (lt_of_le_of_lt hle hτn))
      exact hempty.symm ▸ (@MeasurableSet.empty Ω (ℱ i))
    · have h1 : MeasurableSet[ℱ i] {ω | (n : WithTop ℕ) < τ ω} :=
        ℱ.mono hin _ (hτ.measurableSet_gt n)
      have h2 : MeasurableSet[ℱ i] (u n ⁻¹' A) := ℱ.mono hin _ (hu n hA)
      have h3 : MeasurableSet[ℱ i] {ω | τ ω ≤ (i : WithTop ℕ)} := hτ.measurableSet_le i
      exact (h1.inter h2).inter h3

/-- **A countably valued function is measurable as soon as its level sets are.**  Reusable
combinatorial form of `MeasurableSpace.measurableSet_iUnion`, stated with an explicit
`MeasurableSpace` so that it applies at any point of a filtration. -/
theorem measurable_of_singleton_preimage {α β : Type*} {m : MeasurableSpace α}
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β] {f : α → β}
    (h : ∀ b, MeasurableSet[m] (f ⁻¹' {b})) : Measurable[m] f := by
  intro s hs
  have hset : f ⁻¹' s = ⋃ b : β, (f ⁻¹' ({b} : Set β) ∩ {x : α | b ∈ s}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨f x, rfl, hx⟩, fun ⟨b, hb, hbs⟩ => hb ▸ hbs⟩
  rw [hset]
  refine MeasurableSet.iUnion fun b => ?_
  by_cases hb : b ∈ s
  · simpa only [hb, Set.ofPred_true, Set.inter_univ] using h b
  · simp only [hb, Set.ofPred_false, Set.inter_empty]
    exact MeasurableSet.empty

end SwarmStop

/-! ## The actual interacting walk: the position filtration and the paper's exit time

Everything below is stated about `Swarming.Trajectory.trajectory`, the actual recursive
interacting trajectory on `Swarming.Uniform.Array N`, under nothing but `p`, `m`, `N`. -/

namespace Swarming.Trajectory

open SwarmStop
open Swarming.Uniform

set_option warn.classDefReducibility false

variable {N : ℕ}

/-! ### The smallest filtration making all swarm positions adapted -/

/-- The σ-algebra on the array generated by the positions of all walkers up to time `n`. -/
noncomputable def posSeq (N : ℕ) (p : ℝ) (m : ℕ) (n : ℕ) : MeasurableSpace (Array N) :=
  MeasurableSpace.generateFrom
    {t : Set (Array N) | ∃ k : ℕ, k ≤ n ∧ ∃ i : Fin N, ∃ a : ℤ,
      t = {U : Array N | (trajectory p m U k).pos i = a}}

/-- **The position filtration of the actual interacting walk** is a genuine nested
`MeasureTheory.Filtration` inside the ambient product σ-algebra of the i.i.d. uniform array. -/
noncomputable def posFilt (N : ℕ) (p : ℝ) (m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Array N)) where
  seq := posSeq N p m
  mono' := by
    intro a b hab
    apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain ⟨k, hk, i, x, rfl⟩ := ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨k, le_trans hk hab, i, x, rfl⟩
  le' := by
    intro n
    apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain ⟨k, hk, i, x, rfl⟩ := ht
    exact (Swarming.Fair.measurable_trajectory (N := N) p m k).1 i (measurableSet_singleton x)

/-- Each walker position is adapted to the position filtration. -/
theorem measurable_pos_posFilt (p : ℝ) (m : ℕ) (i : Fin N) {k n : ℕ} (hk : k ≤ n) :
    Measurable[posFilt N p m n] (fun U : Array N => (trajectory p m U k).pos i) := by
  refine measurable_of_singleton_preimage fun a => ?_
  exact MeasurableSpace.measurableSet_generateFrom ⟨k, hk, i, a, rfl⟩

/-- **The stored local times are in the position filtration.**  The local-time field of the
actual recursive state is the path local time `L_k^i(x)`, a finite sum of indicators of
position events, so it adds nothing to the σ-algebra generated by the positions.  Hence
`posFilt` is the filtration of the *full trajectory states* `X_0, …, X_n`, not only of their
positions. -/
theorem measurable_ell_posFilt (p : ℝ) (m : ℕ) (i : Fin N) (x : ℤ) {k n : ℕ} (hk : k ≤ n) :
    Measurable[posFilt N p m n] (fun U : Array N => (trajectory p m U k).ell i x) := by
  have hfun : (fun U : Array N => (trajectory p m U k).ell i x)
      = fun U => ∑ t ∈ Finset.range (k + 1),
          if (trajectory p m U t).pos i = x then (1 : ℕ) else 0 := by
    funext U
    rw [ell_eq_localTime, localTime_def, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hfun]
  refine Finset.measurable_sum _ fun t ht => ?_
  have htn : t ≤ n := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) hk
  exact Measurable.ite ((measurable_pos_posFilt (N := N) p m i htn) (measurableSet_singleton x))
    measurable_const measurable_const

/-- **Minimality**: `posFilt N p m` is contained in every filtration to which all walker
positions are adapted.  In particular it is contained in the paper's enlarged filtration
(states together with all revealed coordinates). -/
theorem posFilt_le_iff {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))} :
    posFilt N p m ≤ 𝒢 ↔ ∀ (n : ℕ) (i : Fin N),
      Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i) := by
  constructor
  · intro h n i
    exact (measurable_pos_posFilt p m i le_rfl).mono (h n) le_rfl
  · intro h n
    apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain ⟨k, hk, i, x, rfl⟩ := ht
    exact 𝒢.mono hk _ (h k i (measurableSet_singleton x))

/-! ### The paper's exit time on the actual trajectory -/

/-- The first time at or after `σ` at which walker `i` of the actual interacting trajectory
leaves the open window `(lo, hi)`.  `StoppedCross.lean` uses `lo = b0`, `hi = b1 + 1`. -/
noncomputable def trajExit (N : ℕ) (p : ℝ) (m : ℕ) (i : Fin N) (lo hi : ℤ)
    (σ : Array N → WithTop ℕ) : Array N → WithTop ℕ :=
  exitAfter (fun n U => (trajectory p m U n).pos i) lo hi σ

/-- **The paper's exit time is a stopping time for every filtration to which the actual walker
is adapted** — in particular for the paper's enlarged filtration, by
`isStoppingTime_trajExit_of_posFilt_le` below. -/
theorem isStoppingTime_trajExit {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))}
    {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hσ : IsStoppingTime 𝒢 σ) :
    IsStoppingTime 𝒢 (trajExit N p m i lo hi σ) :=
  isStoppingTime_exitAfter hσ hX

/-- The same, for the minimal position filtration itself. -/
theorem isStoppingTime_trajExit_posFilt (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ} (hσ : IsStoppingTime (posFilt N p m) σ) :
    IsStoppingTime (posFilt N p m) (trajExit N p m i lo hi σ) :=
  isStoppingTime_exitAfter hσ fun n => measurable_pos_posFilt (N := N) p m i (k := n) le_rfl

/-- The same, transferred to any filtration containing the position filtration. -/
theorem isStoppingTime_trajExit_of_posFilt_le {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))}
    (hle : posFilt N p m ≤ 𝒢) {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    (hσ : IsStoppingTime 𝒢 σ) :
    IsStoppingTime 𝒢 (trajExit N p m i lo hi σ) := by
  refine isStoppingTime_trajExit (𝒢 := 𝒢) (p := p) (m := m) (i := i) (lo := lo) (hi := hi) (σ := σ) ?_ hσ
  intro n
  exact (measurable_pos_posFilt p m i le_rfl).mono (hle n) le_rfl

/-- **Before the exit time the walker is in the window** (paper form). -/
theorem trajExit_interior (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    {U : Array N} {k : ℕ} (hσk : σ U ≤ (k : WithTop ℕ))
    (hk : (k : WithTop ℕ) < trajExit N p m i lo hi σ U) :
    lo < (trajectory p m U k).pos i ∧ (trajectory p m U k).pos i < hi :=
  interior_of_lt_exitAfter hσk hk

/-- **At a finite exit time the walker is outside the window** (paper form). -/
theorem trajExit_eq_coe (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    {U : Array N} {n : ℕ} (h : trajExit N p m i lo hi σ U = (n : WithTop ℕ)) :
    (trajectory p m U n).pos i ≤ lo ∨ hi ≤ (trajectory p m U n).pos i :=
  exitAfter_eq_coe h

/-! ### The paper's hitting times `T_x` of single levels, on the actual trajectory -/

/-- The first time at which walker `i` of the actual trajectory enters `A`
(the paper's `T_A`, started at time `0`). -/
noncomputable def trajHit (N : ℕ) (p : ℝ) (m : ℕ) (i : Fin N) (A : Set ℤ) :
    Array N → WithTop ℕ :=
  hitAfter (fun n U => (trajectory p m U n).pos i) A (fun _ => 0)

/-- **The paper's hitting times are stopping times** for every filtration to which the walker
is adapted.  Taking `A = Set.Iic b0` and `A = Set.Ici (b1 + 1)` gives the two levels of
`StoppedCross.lean`. -/
theorem isStoppingTime_trajHit {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))}
    {i : Fin N} {A : Set ℤ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hA : MeasurableSet A) :
    IsStoppingTime 𝒢 (trajHit N p m i A) :=
  isStoppingTime_hitAfter (isStoppingTime_const 𝒢 0) hX hA

/-- The exit time is the smaller of the two paper hitting times of the boundary levels. -/
theorem trajExit_eq_min_trajHit (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ} :
    trajExit N p m i lo hi σ =
      fun U => min (hitAfter (fun n U => (trajectory p m U n).pos i) (Set.Iic lo) σ U)
        (hitAfter (fun n U => (trajectory p m U n).pos i) (Set.Ici hi) σ U) := rfl

/-- **Explicit form of the paper's exit event by a deterministic time.** -/
theorem trajExit_le_iff (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    {U : Array N} (n : ℕ) :
    trajExit N p m i lo hi σ U ≤ (n : WithTop ℕ) ↔
      ∃ k ≤ n, σ U ≤ (k : WithTop ℕ) ∧
        ((trajectory p m U k).pos i ≤ lo ∨ hi ≤ (trajectory p m U k).pos i) := by
  have hmin : trajExit N p m i lo hi σ U ≤ (n : WithTop ℕ) ↔
      hitAfter (fun n U => (trajectory p m U n).pos i) (Set.Iic lo) σ U ≤ (n : WithTop ℕ) ∨
      hitAfter (fun n U => (trajectory p m U n).pos i) (Set.Ici hi) σ U ≤ (n : WithTop ℕ) := by
    show min _ _ ≤ _ ↔ _
    exact min_le_iff
  rw [hmin]
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk, hσk, hA⟩ := (hitAfter_le_iff n).mp h
      exact ⟨k, hk, hσk, Or.inl (by simpa using hA)⟩
    · obtain ⟨k, hk, hσk, hA⟩ := (hitAfter_le_iff n).mp h
      exact ⟨k, hk, hσk, Or.inr (by simpa using hA)⟩
  · rintro ⟨k, hk, hσk, hA | hA⟩
    · exact Or.inl ((hitAfter_le_iff n).mpr ⟨k, hk, hσk, by simpa using hA⟩)
    · exact Or.inr ((hitAfter_le_iff n).mpr ⟨k, hk, hσk, by simpa using hA⟩)

/-- **Path-prefix description of the paper's exit event**, on the actual trajectory. -/
theorem trajExit_eq_coe_iff (p : ℝ) (m : ℕ) {i : Fin N} {lo hi : ℤ} {σ : Array N → WithTop ℕ}
    {U : Array N} {k : ℕ} :
    trajExit N p m i lo hi σ U = (k : WithTop ℕ) ↔
      σ U ≤ (k : WithTop ℕ) ∧
        ((trajectory p m U k).pos i ≤ lo ∨ hi ≤ (trajectory p m U k).pos i) ∧
        (∀ j : ℕ, (j : WithTop ℕ) ≥ σ U → j < k →
          lo < (trajectory p m U j).pos i ∧ (trajectory p m U j).pos i < hi) :=
  exitAfter_eq_coe_iff

/-! ### The `ℱ_τ` interface on the actual trajectory -/

/-- The position of the actual walker at the paper's exit time is `ℱ_τ`-measurable. -/
theorem measurable_stoppedValue_trajExit
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))} {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hτ : IsStoppingTime 𝒢 (trajExit N p m i lo hi σ)) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun n U => (trajectory p m U n).pos i) (trajExit N p m i lo hi σ)) :=
  measurable_stoppedValue_adapted hX hτ

/-- **The paper's "the walker exited at the bottom" event is measurable at `ℱ_τ`.**  This is the
event whose conditional probability the stopped crossing estimate bounds. -/
theorem measurableSet_exitAtBottom
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))} {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hτ : IsStoppingTime 𝒢 (trajExit N p m i lo hi σ)) :
    MeasurableSet[hτ.measurableSpace]
      {U : Array N | stoppedValue (fun n U => (trajectory p m U n).pos i)
        (trajExit N p m i lo hi σ) U ≤ lo} :=
  measurableSet_Iic.preimage (measurable_stoppedValue_trajExit hX hτ)

/-- **The paper's "exited at the bottom by time `N`" event is `ℱ_N`-measurable.**  It is the
finite union over `k ≤ N` of `{τ = k} ∩ {X_k ≤ lo}`, each term of which sits in `ℱ_k ⊆ ℱ_N`.
This is the event whose `ℱ_N`-measurability the optional-sampling identity needs. -/
theorem measurableSet_stoppedValue_inter_le
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))} {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hτ : IsStoppingTime 𝒢 (trajExit N p m i lo hi σ)) (N' : ℕ) :
    MeasurableSet[𝒢 N']
      {U : Array N | trajExit N p m i lo hi σ U ≤ (N' : WithTop ℕ) ∧
        stoppedValue (fun n U => (trajectory p m U n).pos i)
          (trajExit N p m i lo hi σ) U ≤ lo} := by
  have hset : {U : Array N | trajExit N p m i lo hi σ U ≤ (N' : WithTop ℕ) ∧
        stoppedValue (fun n U => (trajectory p m U n).pos i)
          (trajExit N p m i lo hi σ) U ≤ lo}
      = ⋃ k ∈ Finset.range (N' + 1),
          ({U : Array N | trajExit N p m i lo hi σ U = (k : WithTop ℕ)} ∩
            {U : Array N | (trajectory p m U k).pos i ≤ lo}) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : trajExit N p m i lo hi σ U ≠ ⊤ := by
        intro htop
        rw [htop] at h1
        exact absurd h1 (by simp)
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
      have h1' : ((k : WithTop ℕ)) ≤ ((N' : WithTop ℕ)) := by rw [← hk] at h1; exact h1
      have hk' : k ≤ N' := by exact_mod_cast h1'
      refine ⟨k, Nat.lt_succ_of_le hk', hk.symm, ?_⟩
      rw [stoppedValue, ← hk] at h2
      exact h2
    · rintro ⟨k, hk, hτk, huk⟩
      refine ⟨?_, ?_⟩
      · rw [hτk]
        exact_mod_cast Nat.le_of_lt_succ hk
      · rw [stoppedValue, hτk]
        exact huk
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun k hk => ?_
  have hk' : k ≤ N' := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  exact (𝒢.mono hk' _ (hτ.measurableSet_eq k)).inter (𝒢.mono hk' _ (hX k measurableSet_Iic))

/-- **The `σ`-algebra at the random starting time is contained in the `σ`-algebra at the
paper's exit time**, on the actual interacting walk. -/
theorem measurableSpace_le_trajExit
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (Array N))} {i : Fin N} {lo hi : ℤ}
    {σ : Array N → WithTop ℕ}
    (hX : ∀ n, Measurable[𝒢 n] (fun U : Array N => (trajectory p m U n).pos i))
    (hσ : IsStoppingTime 𝒢 σ) :
    hσ.measurableSpace ≤ (isStoppingTime_trajExit (p := p) (m := m) (i := i) (lo := lo) (hi := hi) (σ := σ) hX hσ).measurableSpace :=
  IsStoppingTime.measurableSpace_mono hσ _ fun ω => le_exitAfter ω

end Swarming.Trajectory

/-! ### Axiom audit

Every declaration below reports only Lean's standard axioms `propext`, `Classical.choice`,
`Quot.sound`.  There is no `sorryAx`. -/


