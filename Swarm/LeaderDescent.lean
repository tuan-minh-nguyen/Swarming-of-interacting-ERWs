/-
# Leader-set descent for the diameter estimate `(diam)`


The paper (`main_1d_revised.tex`, Proposition `group`) proves

  (diam)   `(max_i X_n^i - min_i X_n^i) / n → 0`   almost surely

by induction on `k`, bounding the difference between the `k`-th and the `(k+1)`-th largest
position.  Two ingredients are purely deterministic and were missing from the tree:

* **the leader decomposition** — the spread of the configuration is exactly the sum of the
  gaps `min_A X_n - max_{A^c} X_n` over the nested chain of leading blocks `A` (ties included, so
  no sorting of the walkers is needed), and the internal spread of the top group is the sum of the
  lower-level gaps;
* **the reset descent** — at the first time `s ≤ n` from which the separation condition `(sep)`
  holds continuously, the failure of `(sep)` at `s-1` forces the block gap at `s-1` to be
  controlled by the *deficit* `max_{j∈A^c}(M_{s-1}^j - X_{s-1}^j)`, hence the gap at `s` by that
  deficit plus `2`.

Both are proved here, together with the bridge from the block gap to the paper's group potential
`W^{A,A^c}` and the reduction of `(diam)` to two explicit residual premises: the deficit estimate
(the paper's `(prelim)`) and the separated-block gap estimate (what `(Wdrift)`, `(Wstrict)` and
`(Qslln)` supply at the reset time).  No probability space, filtration, conditional expectation or
almost-sure statement is used: everything below is a statement about a single unit-step path array.

Nothing in this file is the public target.  The residual premises are listed in the docstring of
`spread_div_tendsto_zero`, and `PROOF.md` records what remains unproved.
-/
import Swarm.Imports

open Filter Finset Topology
open scoped BigOperators

namespace LeaderDescent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part A: the leader chain of a configuration and its exact gap decomposition -/

section Chain

/-- The top layer of `s`: the elements of `s` with maximal `f`-value. -/
noncomputable def leadLayer (f : ι → ℤ) (s : Finset ι) : Finset ι :=
  s.filter (fun i => ∀ j ∈ s, f j ≤ f i)

/-- The leader chain of `f`: `leadChain f k` collects the walkers of largest `f`-value, one whole
tie-class at a time. -/
noncomputable def leadChain (f : ι → ℤ) : ℕ → Finset ι
  | 0 => ∅
  | (k + 1) => leadChain f k ∪ leadLayer f (univ \ leadChain f k)

@[simp] theorem leadChain_zero (f : ι → ℤ) : leadChain f 0 = ∅ := rfl

theorem leadChain_succ (f : ι → ℤ) (k : ℕ) :
    leadChain f (k + 1) = leadChain f k ∪ leadLayer f (univ \ leadChain f k) := rfl

theorem leadChain_subset_succ (f : ι → ℤ) (k : ℕ) : leadChain f k ⊆ leadChain f (k + 1) :=
  subset_union_left

theorem leadChain_mono (f : ι → ℤ) : Monotone (leadChain f) :=
  monotone_nat_of_le_succ (leadChain_subset_succ f)

theorem leadChain_subset_univ (f : ι → ℤ) (k : ℕ) : leadChain f k ⊆ univ := subset_univ _

theorem mem_leadLayer {f : ι → ℤ} {s : Finset ι} {i : ι} :
    i ∈ leadLayer f s ↔ i ∈ s ∧ ∀ j ∈ s, f j ≤ f i := by
  unfold leadLayer
  rw [mem_filter]

theorem leadLayer_nonempty (f : ι → ℤ) {s : Finset ι} (hs : s.Nonempty) :
    (leadLayer f s).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image s f hs
  exact ⟨a, mem_leadLayer.mpr ⟨ha, fun j hj => hmax j hj⟩⟩

theorem leadLayer_le {f : ι → ℤ} {s : Finset ι} {i j : ι} (hi : i ∈ leadLayer f s) (hj : j ∈ s) :
    f j ≤ f i := (mem_leadLayer.mp hi).2 j hj

theorem leadLayer_subset (f : ι → ℤ) {s : Finset ι} : leadLayer f s ⊆ s :=
  fun _ h => (mem_leadLayer.mp h).1

/-- The leader chain dominates its complement. -/
theorem leadChain_dominates (f : ι → ℤ) (k : ℕ) {i j : ι} (hi : i ∈ leadChain f k)
    (hj : j ∉ leadChain f k) : f j ≤ f i := by
  induction k with
  | zero => simp at hi
  | succ k ih =>
    rw [leadChain_succ] at hi hj
    rcases mem_union.mp hi with h | h
    · exact ih h (fun h' => hj (mem_union.mpr (Or.inl h')))
    · have hj' : j ∈ univ \ leadChain f k :=
        mem_sdiff.mpr ⟨mem_univ j, fun h' => hj (mem_union.mpr (Or.inl h'))⟩
      exact leadLayer_le h hj'

theorem leadChain_ne_univ_iff (f : ι → ℤ) {k : ℕ} :
    leadChain f k ≠ univ ↔ (univ \ leadChain f k).Nonempty := by
  constructor
  · intro h
    rw [nonempty_iff_ne_empty]
    intro hemp
    apply h
    ext x
    simp only [mem_univ, iff_true]
    by_contra hx
    have hmem : x ∈ univ \ leadChain f k := mem_sdiff.mpr ⟨mem_univ x, hx⟩
    rw [hemp] at hmem
    simp at hmem
  · rintro ⟨x, hx⟩ h
    rw [h] at hx
    simp at hx

theorem leadChain_card_lt (f : ι → ℤ) {k : ℕ} (h : leadChain f k ≠ univ) :
    (leadChain f k).card < (leadChain f (k + 1)).card := by
  obtain ⟨a, ha⟩ := leadLayer_nonempty f ((leadChain_ne_univ_iff f).mp h)
  have hanot : a ∉ leadChain f k := (mem_sdiff.mp (mem_leadLayer.mp ha).1).2
  have hssub : leadChain f k ⊂ leadChain f (k + 1) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨leadChain_subset_succ f k, fun heq => ?_⟩
    have hmem : a ∈ leadChain f (k + 1) := by
      rw [leadChain_succ]; exact mem_union.mpr (Or.inr ha)
    rw [← heq] at hmem
    exact hanot hmem
  exact card_lt_card hssub

theorem leadChain_card_ge (f : ι → ℤ) : ∀ k : ℕ, (∀ m < k, leadChain f m ≠ univ) →
    k ≤ (leadChain f k).card
  | 0, _ => Nat.zero_le _
  | (k + 1), h => by
    have hk := leadChain_card_ge f k (fun m hm => h m (Nat.lt_succ_of_lt hm))
    have hlt := leadChain_card_lt f (h k (Nat.lt_succ_self k))
    omega

/-- The chain fills the index set within `Fintype.card ι` steps. -/
theorem leadChain_univ (f : ι → ℤ) [Nonempty ι] : leadChain f (Fintype.card ι) = univ := by
  by_contra h
  have hmono : ∀ m ≤ Fintype.card ι, leadChain f m ≠ univ := by
    intro m hm heq
    apply h
    have hsub : (univ : Finset ι) ⊆ leadChain f (Fintype.card ι) := by
      rw [← heq]; exact leadChain_mono f hm
    exact top_unique hsub
  have hne := hmono (Fintype.card ι) (le_refl _)
  have hge : Fintype.card ι ≤ (leadChain f (Fintype.card ι)).card :=
    leadChain_card_ge f _ (fun m hm => hmono m (le_of_lt hm))
  have hle : (leadChain f (Fintype.card ι)).card ≤ Fintype.card ι := card_le_univ _
  have huc : (univ : Finset ι).card = Fintype.card ι := card_univ
  exact hne (eq_of_subset_of_card_le (leadChain_subset_univ f _) (by omega))

theorem leadChain_one_nonempty (f : ι → ℤ) [Nonempty ι] : (leadChain f 1).Nonempty := by
  have h := leadLayer_nonempty f (univ_nonempty (α := ι))
  simpa [leadChain_succ, leadChain_zero] using h

theorem leadChain_nonempty_of_pos (f : ι → ℤ) [Nonempty ι] {k : ℕ} (hk : 1 ≤ k) :
    (leadChain f k).Nonempty :=
  (leadChain_one_nonempty f).mono (leadChain_mono f hk)

/-- The minimum of the `k`-th leader layer (junk value `0` at `k = 0`). -/
noncomputable def chainMin (f : ι → ℤ) (k : ℕ) : ℤ :=
  if h : (leadChain f k).Nonempty then (leadChain f k).inf' h f else 0

theorem chainMin_eq (f : ι → ℤ) {k : ℕ} (h : (leadChain f k).Nonempty) :
    chainMin f k = (leadChain f k).inf' h f := by
  unfold chainMin
  rw [dif_pos h]

/-- The gap of a leading block: `min` over the block minus `max` over its complement; `0` when the
block is empty or full. -/
noncomputable def gapAt (f : ι → ℤ) (s : Finset ι) : ℤ :=
  if h : s.Nonempty ∧ (univ \ s).Nonempty then s.inf' h.1 f - (univ \ s).sup' h.2 f else 0

theorem gapAt_eq_zero (f : ι → ℤ) {s : Finset ι} (h : ¬ (s.Nonempty ∧ (univ \ s).Nonempty)) :
    gapAt f s = 0 := by
  unfold gapAt
  rw [dif_neg h]

theorem gapAt_nonneg (f : ι → ℤ) (k : ℕ) : 0 ≤ gapAt f (leadChain f k) := by
  unfold gapAt
  split_ifs with h
  · have hsup : (univ \ leadChain f k).sup' h.2 f ≤ (leadChain f k).inf' h.1 f := by
      refine sup'_le h.2 f (fun j hj => ?_)
      exact le_inf' h.1 f (fun i hi => leadChain_dominates f k hi (mem_sdiff.mp hj).2)
    linarith
  · exact le_refl 0

/-- A layer whose members are all of `univ` has the minimum of `f`. -/
theorem chainMin_eq_inf_univ (f : ι → ℤ) [Nonempty ι] {k : ℕ}
    (hmem : ∀ i, i ∈ leadChain f k ↔ i ∈ (univ : Finset ι)) :
    chainMin f k = univ.inf' univ_nonempty f := by
  have hk : (leadChain f k).Nonempty := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact ⟨a, (hmem a).mpr (mem_univ a)⟩
  rw [chainMin_eq f hk]
  refine le_antisymm ?_ ?_
  · refine le_inf' univ_nonempty f (fun b hb => ?_)
    exact inf'_le f ((hmem b).mpr hb)
  · refine le_inf' hk f (fun b hb => ?_)
    exact inf'_le f ((hmem b).mp hb)

/-- The first layer is exactly the set of maxima, so its minimum is the maximum of `f`. -/
theorem chainMin_one (f : ι → ℤ) [Nonempty ι] :
    chainMin f 1 = univ.sup' univ_nonempty f := by
  have h1 : (leadChain f 1).Nonempty := leadChain_nonempty_of_pos f (le_refl 1)
  have hmem : ∀ i, i ∈ leadChain f 1 ↔ i ∈ leadLayer f univ := by
    intro i
    rw [leadChain_succ, leadChain_zero]
    simp
  have hval : ∀ a ∈ leadChain f 1, ∀ b ∈ leadChain f 1, f a = f b := by
    intro a ha b hb
    exact le_antisymm
      (leadLayer_le (s := univ) (i := b) (j := a) ((hmem b).mp hb) (mem_univ a))
      (leadLayer_le (s := univ) (i := a) (j := b) ((hmem a).mp ha) (mem_univ b))
  have hle : ∀ a ∈ leadChain f 1, univ.sup' univ_nonempty f ≤ f a := by
    intro a ha
    refine sup'_le univ_nonempty f (fun c _ => ?_)
    by_cases hc : c ∈ leadChain f 1
    · rw [hval c hc a ha]
    · exact leadChain_dominates f 1 (i := a) (j := c) ha hc
  rw [chainMin_eq f h1]
  have h1' := h1
  obtain ⟨a, ha⟩ := h1'
  have hmin : (leadChain f 1).inf' h1 f = f a :=
    le_antisymm (inf'_le f ha) (le_inf' h1 f (fun b hb => le_of_eq (hval a ha b hb)))
  rw [hmin]
  exact le_antisymm (le_sup' f (mem_univ a)) (hle a ha)

/-- The full chain has the minimum of `f`. -/
theorem chainMin_last (f : ι → ℤ) [Nonempty ι] :
    chainMin f (Fintype.card ι + 1) = univ.inf' univ_nonempty f := by
  refine chainMin_eq_inf_univ f (k := Fintype.card ι + 1) (fun i => ?_)
  have hU : leadChain f (Fintype.card ι + 1) = univ := by
    refine top_unique ?_
    show (univ : Finset ι) ⊆ leadChain f (Fintype.card ι + 1)
    rw [← leadChain_univ f]
    exact leadChain_mono f (by omega)
  rw [hU]

/-- **The exact order-statistic telescoping**: at a leading block the gap is the difference of two
successive layer minima. -/
theorem gapAt_leadChain (f : ι → ℤ) [Nonempty ι] (m : ℕ) :
    gapAt f (leadChain f (m + 1)) = chainMin f (m + 1) - chainMin f (m + 2) := by
  have h1 : (leadChain f (m + 1)).Nonempty := leadChain_nonempty_of_pos f (by omega)
  by_cases hU : leadChain f (m + 1) = univ
  · have hguard : ¬ ((leadChain f (m + 1)).Nonempty ∧ (univ \ leadChain f (m + 1)).Nonempty) := by
      intro hc
      obtain ⟨x, hx⟩ := hc.2
      rw [hU] at hx
      simp at hx
    rw [gapAt_eq_zero f hguard]
    have h2 : leadChain f (m + 2) = univ := by
      have hsub : leadChain f (m + 1) ⊆ leadChain f (m + 2) := leadChain_mono f (by omega)
      rw [hU] at hsub
      exact top_unique hsub
    have hc1 : chainMin f (m + 1) = univ.inf' univ_nonempty f :=
      chainMin_eq_inf_univ f (fun i => by rw [hU])
    have hc2 : chainMin f (m + 2) = univ.inf' univ_nonempty f :=
      chainMin_eq_inf_univ f (fun i => by rw [h2])
    rw [hc1, hc2, sub_self]
  · obtain ⟨hd, hdmem⟩ := (leadChain_ne_univ_iff f).mp hU
    have hdn : (univ \ leadChain f (m + 1)).Nonempty := ⟨hd, hdmem⟩
    set c : Finset ι := leadChain f (m + 1) with hc
    set l : Finset ι := leadLayer f (univ \ leadChain f (m + 1)) with hl
    have hlne : l.Nonempty := leadLayer_nonempty f hdn
    have h2ne : (leadChain f (m + 2)).Nonempty := leadChain_nonempty_of_pos f (by omega)
    -- every element of `l` is a maximum of the complement
    have hval : ∀ a ∈ l, ∀ b ∈ l, f a = f b := by
      intro a ha b hb
      have hab : a ∈ univ \ leadChain f (m + 1) := (mem_leadLayer.mp ha).1
      have hbb : b ∈ univ \ leadChain f (m + 1) := (mem_leadLayer.mp hb).1
      exact le_antisymm (leadLayer_le hb hab) (leadLayer_le ha hbb)
    have hstep : chainMin f (m + 2) = (c ∪ l).inf' (h1.mono subset_union_left) f := by
      rw [chainMin_eq f h2ne]
      rfl
    have key : (c ∪ l).inf' (h1.mono subset_union_left) f = (univ \ leadChain f (m + 1)).sup' hdn f := by
      have hlne' := hlne
      obtain ⟨a, ha⟩ := hlne'
      have hac : a ∈ univ \ leadChain f (m + 1) := (mem_leadLayer.mp ha).1
      have hminl : l.inf' hlne f = f a :=
        le_antisymm (inf'_le f ha) (le_inf' hlne f (fun b hb => le_of_eq (hval a ha b hb)))
      have hmaxc : (univ \ leadChain f (m + 1)).sup' hdn f = f a :=
        le_antisymm (sup'_le hdn f (fun b hb => leadLayer_le ha hb))
          (le_sup' f hac)
      have hinf : (c ∪ l).inf' (h1.mono subset_union_left) f = f a := by
        refine le_antisymm (inf'_le f (mem_union.mpr (Or.inr ha))) ?_
        refine le_inf' (h1.mono subset_union_left) f (fun b hb => ?_)
        rcases mem_union.mp hb with hbc | hbl
        · exact leadChain_dominates f (m + 1) (i := b) (j := a) hbc (mem_sdiff.mp hac).2
        · exact le_of_eq (hval b hbl a ha).symm
      rw [hinf, hmaxc]
    rw [gapAt, dif_pos ⟨h1, hdn⟩, chainMin_eq f (k := m + 1) h1, hstep, key]

/-- **The internal spread of the leading group is the sum of the lower-level gaps.**  For the
`(k+1)`-th chain element `A = leadChain f (k+1)` (the top group of the configuration), the difference
between the global maximum and the minimum of `A` is exactly the sum of the gaps of the chain
elements at levels `1, …, k`.  This is the nested structure used to bound the internal spread
`max_A X - min_A X` of a leading group by the lower order statistics. -/
theorem chainMin_one_sub_eq_sum (f : ι → ℤ) [Nonempty ι] (k : ℕ) :
    chainMin f 1 - chainMin f (k + 1) = ∑ j ∈ range k, gapAt f (leadChain f (j + 1)) := by
  have hterm : ∀ j ∈ range k, gapAt f (leadChain f (j + 1)) = chainMin f (j + 1) - chainMin f (j + 2) :=
    fun j _ => gapAt_leadChain f j
  rw [sum_congr rfl hterm, sum_range_sub' (fun j => chainMin f (j + 1))]

/-- **The spread of a configuration is the sum of the leader-block gaps.** -/
theorem spread_eq_sum_gaps (f : ι → ℤ) [Nonempty ι] :
    (univ.sup' univ_nonempty f - univ.inf' univ_nonempty f)
      = ∑ k ∈ range (Fintype.card ι), gapAt f (leadChain f (k + 1)) := by
  have hterm : ∀ k ∈ range (Fintype.card ι),
      gapAt f (leadChain f (k + 1)) = chainMin f (k + 1) - chainMin f (k + 2) :=
    fun k _ => gapAt_leadChain f k
  rw [sum_congr rfl hterm, sum_range_sub' (fun k => chainMin f (k + 1)), chainMin_one f,
    chainMin_last f]

end Chain

/-! ## Part B: the reset time of the separation condition and its descent -/

section Dynamics

variable (X : ι → ℕ → ℤ)

/-- The running maximum of walker `i` up to time `n`. -/
noncomputable def runMax (i : ι) (n : ℕ) : ℤ :=
  (range (n + 1)).sup' ⟨0, mem_range.mpr (Nat.succ_pos n)⟩ (fun t => X i t)

theorem le_runMax (i : ι) (n : ℕ) : X i n ≤ runMax X i n :=
  le_sup' (fun t => X i t) (mem_range.mpr (Nat.lt_succ_self n))

theorem runMax_le_of {i : ι} {n t : ℕ} (ht : t ≤ n) : X i t ≤ runMax X i n :=
  le_sup' (fun s => X i s) (mem_range.mpr (Nat.lt_succ_of_le ht))

theorem runMax_mono (i : ι) {m n : ℕ} (h : m ≤ n) : runMax X i m ≤ runMax X i n := by
  refine sup'_le ⟨0, mem_range.mpr (Nat.succ_pos m)⟩ (fun t => X i t) (fun t ht => ?_)
  exact runMax_le_of X (i := i) (n := n) (by simp only [mem_range] at ht; omega)

theorem runMax_zero {i : ι} (h0 : X i 0 = 0) : runMax X i 0 = 0 := by
  have h1 : runMax X i 0 ≤ X i 0 := by
    refine sup'_le ⟨0, mem_range.mpr (Nat.succ_pos 0)⟩ (fun t => X i t) (fun t ht => ?_)
    have ht' : t = 0 := by simp only [mem_range] at ht; omega
    rw [ht']
  have h2 : X i 0 ≤ runMax X i 0 := le_runMax X i 0
  rw [le_antisymm h1 h2, h0]

/-- Unit-step (nearest-neighbour) paths. -/
def UnitStep : Prop := ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1

theorem step_le (hX : UnitStep X) (i : ι) (n : ℕ) : X i (n + 1) ≤ X i n + 1 := by
  have h := hX i n
  have h2 : X i (n + 1) - X i n ≤ 1 := (abs_le.mp (le_of_eq h)).2
  omega

theorem step_ge (hX : UnitStep X) (i : ι) (n : ℕ) : X i n ≤ X i (n + 1) + 1 := by
  have h := hX i n
  have h2 : -(1 : ℤ) ≤ X i (n + 1) - X i n := (abs_le.mp (le_of_eq h)).1
  omega

/-- The paper's `(sep)` with running maxima: every walker of `A` is at least `2` above every
running maximum reached by a walker outside `A`, and all positions are nonnegative. -/
def SepMax (A : Finset ι) (n : ℕ) : Prop :=
  (∀ i, 0 ≤ X i n) ∧ ∀ i ∈ A, ∀ j ∉ A, runMax X j n + 2 ≤ X i n

/-- The current-position version of `(sep)`. -/
def SepSet (A : Finset ι) (n : ℕ) : Prop :=
  (∀ i, 0 ≤ X i n) ∧ ∀ i ∈ A, ∀ j ∉ A, X j n + 2 ≤ X i n

theorem leading_of_sepMax {A : Finset ι} {n : ℕ} (h : SepMax X A n) :
    ∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n := by
  intro i hi j hj
  have h1 := h.2 i hi j hj
  have h2 := le_runMax X j n
  omega

theorem leading_of_sepSet {A : Finset ι} {n : ℕ} (h : SepSet X A n) :
    ∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n := by
  intro i hi j hj
  have h1 := h.2 i hi j hj
  omega

theorem sepSet_of_sepMax {A : Finset ι} {n : ℕ} (h : SepMax X A n) : SepSet X A n :=
  ⟨h.1, fun i hi j hj => by have := h.2 i hi j hj; have := le_runMax X j n; omega⟩

/-- Failure of `(sep)` with running maxima, given nonnegative positions, bounds a member of `A` by
a running maximum of a walker outside `A`. -/
theorem exists_le_runMax_add_of_not_sepMax {A : Finset ι} {n : ℕ}
    (hnn : ∀ i, 0 ≤ X i n) (h : ¬ SepMax X A n) :
    ∃ i ∈ A, ∃ j ∉ A, X i n ≤ runMax X j n + 1 := by
  have h' : ¬ (∀ i ∈ A, ∀ j ∉ A, runMax X j n + 2 ≤ X i n) := fun hc => h ⟨hnn, hc⟩
  push_neg at h'
  obtain ⟨i, hi, j, hj, hij⟩ := h'
  exact ⟨i, hi, j, hj, by omega⟩

/-- **The gap at a leading block is bounded by the deficit when separation fails.** -/
theorem inf_sub_sup_le_deficit_of_not_sepMax {A : Finset ι} {n : ℕ}
    (hnn : ∀ i, 0 ≤ X i n) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (h : ¬ SepMax X A n) :
    A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun j => X j n)
      ≤ 1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) := by
  obtain ⟨i, hi, j, hjA, hij⟩ := exists_le_runMax_add_of_not_sepMax X hnn h
  have hj : j ∈ univ \ A := mem_sdiff.mpr ⟨mem_univ j, hjA⟩
  have hmin : A.inf' hA (fun i => X i n) ≤ X i n := inf'_le _ hi
  have hsup : X j n ≤ (univ \ A).sup' hAc (fun j => X j n) := le_sup' (fun j => X j n) hj
  have hdefj : runMax X j n - X j n
      ≤ (univ \ A).sup' hAc (fun j => runMax X j n - X j n) :=
    le_sup' (fun j => runMax X j n - X j n) hj
  linarith

/-- The separation clause of `(sep)` alone, without the nonnegativity clause.  This is the form
that the deterministic diameter argument actually uses: the nonnegativity of positions only enters
the paper's proof to exclude the bad case at small times. -/
def SepGap (A : Finset ι) (n : ℕ) : Prop :=
  ∀ i ∈ A, ∀ j ∉ A, runMax X j n + 2 ≤ X i n

theorem leading_of_sepGap {A : Finset ι} {n : ℕ} (h : SepGap X A n) :
    ∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n := by
  intro i hi j hj
  have h1 := h i hi j hj
  have h2 := le_runMax X j n
  omega

/-- Failure of the separation clause bounds a member of `A` by a running maximum outside `A`.  No
nonnegativity of the positions is needed. -/
theorem exists_le_runMax_add_of_not_sepGap {A : Finset ι} {n : ℕ} (h : ¬ SepGap X A n) :
    ∃ i ∈ A, ∃ j ∉ A, X i n ≤ runMax X j n + 1 := by
  have h' : ¬ (∀ i ∈ A, ∀ j ∉ A, runMax X j n + 2 ≤ X i n) := h
  push Not at h'
  obtain ⟨i, hi, j, hj, hij⟩ := h'
  exact ⟨i, hi, j, hj, by omega⟩

/-- **The block gap is bounded by the deficit when the separation clause fails** (no nonnegativity
needed). -/
theorem inf_sub_sup_le_deficit_of_not_sepGap {A : Finset ι} {n : ℕ}
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (h : ¬ SepGap X A n) :
    A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun j => X j n)
      ≤ 1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) := by
  obtain ⟨i, hi, j, hjA, hij⟩ := exists_le_runMax_add_of_not_sepGap X h
  have hj : j ∈ univ \ A := mem_sdiff.mpr ⟨mem_univ j, hjA⟩
  have hmin : A.inf' hA (fun i => X i n) ≤ X i n := inf'_le _ hi
  have hsup : X j n ≤ (univ \ A).sup' hAc (fun j => X j n) := le_sup' (fun j => X j n) hj
  have hdefj : runMax X j n - X j n
      ≤ (univ \ A).sup' hAc (fun j => runMax X j n - X j n) :=
    le_sup' (fun j => runMax X j n - X j n) hj
  linarith

/-- The first time `s ≤ n` from which `(sep)` with running maxima holds continuously on `[s,n]`
(`n+1` when it holds nowhere). -/
noncomputable def resetTime (A : Finset ι) (n : ℕ) : ℕ := by
  classical
  refine Nat.find (p := fun s => ∀ t, s ≤ t → t ≤ n → SepMax X A t) ⟨n + 1, ?_⟩
  intro t h1 h2
  omega

theorem resetTime_spec (A : Finset ι) (n : ℕ) :
    ∀ t, resetTime X A n ≤ t → t ≤ n → SepMax X A t := by
  classical
  unfold resetTime
  exact Nat.find_spec (p := fun s => ∀ t, s ≤ t → t ≤ n → SepMax X A t) _

theorem resetTime_minimal (A : Finset ι) (n : ℕ) {s : ℕ}
    (h : ∀ t, s ≤ t → t ≤ n → SepMax X A t) : resetTime X A n ≤ s := by
  classical
  unfold resetTime
  exact Nat.find_min' _ h

theorem not_resetTime_pred (A : Finset ι) (n : ℕ) (hpos : 1 ≤ resetTime X A n) :
    ¬ (∀ t, resetTime X A n - 1 ≤ t → t ≤ n → SepMax X A t) := by
  intro hc
  have hmin := resetTime_minimal X A n hc
  omega

/-- `(sep)` cannot hold at time `0` for a nontrivial block. -/
theorem not_sepMax_zero {A : Finset ι} (h0 : ∀ i, X i 0 = 0) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) : ¬ SepMax X A 0 := by
  intro h
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ := hAc
  have hjA : j ∉ A := (mem_sdiff.mp hj).2
  have h1 := h.2 i hi j hjA
  have h2 : runMax X j 0 = 0 := runMax_zero X (h0 j)
  have h3 : X i 0 = 0 := h0 i
  omega

/-- **The reset time is positive.** -/
theorem resetTime_pos {A : Finset ι} (h0 : ∀ i, X i 0 = 0) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (n : ℕ) : 1 ≤ resetTime X A n := by
  by_contra h
  have hz : resetTime X A n = 0 := by omega
  have hspec : SepMax X A 0 := resetTime_spec X A n 0 (le_of_eq hz) (Nat.zero_le n)
  exact not_sepMax_zero X h0 hA hAc hspec

/-- **The reset descent.**  If `(sep)` holds at time `n` for the block `A`, then at the first time
`s` of the final separating run the block's gap is controlled by the deficit at `s-1`: the block
had not yet separated at `s-1`, so one of its members was still below the running maximum of a
walker outside it. -/
theorem reset_descent (hX : UnitStep X) {A : Finset ι} {n : ℕ} (h0 : ∀ i, X i 0 = 0)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hnn : ∀ i, 0 ≤ X i (resetTime X A n - 1)) :
    A.inf' hA (fun i => X i (resetTime X A n - 1))
        - (univ \ A).sup' hAc (fun j => X j (resetTime X A n - 1))
      ≤ 1 + (univ \ A).sup' hAc (fun j => runMax X j (resetTime X A n - 1)
          - X j (resetTime X A n - 1)) := by
  have hpos := resetTime_pos X h0 hA hAc n
  have hnot := not_resetTime_pred X A n hpos
  push_neg at hnot
  obtain ⟨t, ht1, ht2, ht3⟩ := hnot
  have hte : t = resetTime X A n - 1 := by
    refine le_antisymm ?_ ht1
    by_contra hc
    push_neg at hc
    have hc' : resetTime X A n ≤ t := by omega
    exact ht3 (resetTime_spec X A n t hc' ht2)
  rw [← hte]
  exact inf_sub_sup_le_deficit_of_not_sepMax X (by rw [hte]; exact hnn) hA hAc ht3

end Dynamics

/-! ## Part B': step bounds for the block gap and the reset-time gap bound -/

section GapStep

variable (X : ι → ℕ → ℤ)

theorem gapAt_succ_le (hX : UnitStep X) {A : Finset ι} (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (n : ℕ) :
    gapAt (fun i => X i (n + 1)) A ≤ gapAt (fun i => X i n) A + 2 := by
  obtain ⟨a, ha, hmina⟩ := exists_min_image A (fun i => X i n) hA
  obtain ⟨b, hb, hmaxb⟩ := exists_max_image (univ \ A) (fun j => X j n) hAc
  have hmin_eq : A.inf' hA (fun i => X i n) = X a n :=
    le_antisymm (inf'_le _ ha) (le_inf' hA _ (fun c hc => hmina c hc))
  have hmax_eq : (univ \ A).sup' hAc (fun j => X j n) = X b n :=
    le_antisymm (sup'_le hAc _ (fun c hc => hmaxb c hc)) (le_sup' (fun j => X j n) hb)
  have hstep1 : A.inf' hA (fun i => X i (n + 1)) ≤ X a n + 1 :=
    le_trans (inf'_le _ ha) (step_le X hX a n)
  have hstep2 : X b n - 1 ≤ (univ \ A).sup' hAc (fun j => X j (n + 1)) :=
    le_trans (by linarith [step_ge X hX b n]) (le_sup' _ hb)
  rw [gapAt, gapAt, dif_pos ⟨hA, hAc⟩, dif_pos ⟨hA, hAc⟩, hmin_eq, hmax_eq]
  linarith

/-- **The reset-time gap bound.**  At the first time `s` of the final separating run of `A`, the
block gap is at most `3` plus the deficit of the complement at `s-1`.  This is the deterministic
input of the paper's step `W_s = o(n)` in the proof of `(diam)`: the group potential `W_s` is
comparable to this gap ([`gapAt_le_potential_gap`]). -/
theorem gapAt_reset_le (hX : UnitStep X) {A : Finset ι} {n : ℕ} (h0 : ∀ i, X i 0 = 0)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hnn : ∀ i, 0 ≤ X i (resetTime X A n - 1)) :
    gapAt (fun i => X i (resetTime X A n)) A
      ≤ 3 + (univ \ A).sup' hAc
          (fun j => runMax X j (resetTime X A n - 1) - X j (resetTime X A n - 1)) := by
  have hpos := resetTime_pos X h0 hA hAc n
  have hstep := gapAt_succ_le X hX hA hAc (resetTime X A n - 1)
  have hgap : gapAt (fun i => X i (resetTime X A n - 1)) A
      = A.inf' hA (fun i => X i (resetTime X A n - 1))
        - (univ \ A).sup' hAc (fun j => X j (resetTime X A n - 1)) := by
    rw [gapAt, dif_pos ⟨hA, hAc⟩]
  have hdes := reset_descent X hX h0 hA hAc hnn
  rw [show resetTime X A n - 1 + 1 = resetTime X A n from by omega] at hstep
  rw [hgap] at hstep
  linarith

end GapStep

/-! ## Part C': the group-potential bridge -/

section Potential

variable (X : ι → ℕ → ℤ) {H : ℤ → ℝ}

/-- **The block gap is dominated by the group potential.**  For any nondecreasing `H : ℤ → ℝ` whose
increments dominate the identity (both hold for `SepGroup.HZ` with `1/2 ≤ w ≤ 1`), the leading-block
gap `min_A X_n - max_{A^c} X_n` is at most the paper's observable
`(|A|)⁻¹ ∑_{i∈A} H(X_n^i) - max_{j∉A} H(X_n^j)` (the paper's `W_n^{A,A^c}`). -/
theorem gapAt_le_potential_gap [Nonempty ι] (hH : Monotone H)
    (hslope : ∀ x y : ℤ, x ≤ y → ((y : ℝ) - (x : ℝ)) ≤ H y - H x)
    {A : Finset ι} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (n : ℕ)
    (hlead : ∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n) :
    ((gapAt (fun i => X i n) A : ℤ) : ℝ)
      ≤ ((A.card : ℝ)⁻¹ * ∑ i ∈ A, H (X i n))
        - (univ \ A).sup' hAc (fun j => H (X j n)) := by
  obtain ⟨a, ha, hmina⟩ := exists_min_image A (fun i => X i n) hA
  obtain ⟨b, hb, hmaxb⟩ := exists_max_image (univ \ A) (fun j => X j n) hAc
  have hbA : b ∉ A := (mem_sdiff.mp hb).2
  have hba : X b n ≤ X a n := hlead a ha b hbA
  have hmin_eq : A.inf' hA (fun i => X i n) = X a n :=
    le_antisymm (inf'_le _ ha) (le_inf' hA _ (fun c hc => hmina c hc))
  have hmax_eq : (univ \ A).sup' hAc (fun j => X j n) = X b n :=
    le_antisymm (sup'_le hAc _ (fun c hc => hmaxb c hc)) (le_sup' (fun j => X j n) hb)
  have hHsup : (univ \ A).sup' hAc (fun j => H (X j n)) = H (X b n) :=
    le_antisymm (sup'_le hAc _ (fun c hc => hH (hmaxb c hc)))
      (le_sup' (fun j => H (X j n)) hb)
  have hHmin : H (X a n) ≤ (A.card : ℝ)⁻¹ * ∑ i ∈ A, H (X i n) := by
    have hcard : (0 : ℝ) < (A.card : ℝ) := by
      have := Finset.card_pos.mpr hA
      exact_mod_cast this
    have hsum : (A.card : ℝ) * H (X a n) ≤ ∑ i ∈ A, H (X i n) := by
      have h1 : ∑ _i ∈ A, H (X a n) ≤ ∑ i ∈ A, H (X i n) :=
        Finset.sum_le_sum (fun i hi => hH (hmina i hi))
      rwa [Finset.sum_const, nsmul_eq_mul] at h1
    rw [← div_eq_inv_mul, le_div_iff₀ hcard]
    linarith
  rw [gapAt, dif_pos ⟨hA, hAc⟩, hmin_eq, hmax_eq, hHsup]
  push_cast
  linarith [hslope (X b n) (X a n) hba]

end Potential


/-- Casting a finite maximum of integers to `ℝ`. -/
theorem sup'_cast {s : Finset ι} (h : s.Nonempty) (f : ι → ℤ) :
    ((s.sup' h f : ℤ) : ℝ) = s.sup' h (fun i => (f i : ℝ)) := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image s f h
  have h1 : s.sup' h f = f a := le_antisymm (sup'_le h f (fun b hb => hmax b hb)) (le_sup' f ha)
  have h2 : s.sup' h (fun i => (f i : ℝ)) = (f a : ℝ) :=
    le_antisymm (sup'_le h _ (fun b hb => by exact_mod_cast hmax b hb))
      (le_sup' (fun i => (f i : ℝ)) ha)
  rw [h1, h2]

/-! ## Part C: `(diam)` from the deficit estimate and the separated-block gap estimate -/

section Reduction

variable (X : ι → ℕ → ℤ)

/-- The spread (diameter) of the configuration at time `n`. -/
noncomputable def spreadZ [Nonempty ι] (n : ℕ) : ℤ :=
  univ.sup' univ_nonempty (fun i => X i n) - univ.inf' univ_nonempty (fun i => X i n)

theorem spreadZ_nonneg [Nonempty ι] (n : ℕ) : 0 ≤ spreadZ X n := by
  have h : univ.inf' univ_nonempty (fun i => X i n) ≤ univ.sup' univ_nonempty (fun i => X i n) := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact le_trans (inf'_le (fun i => X i n) (mem_univ a)) (le_sup' (fun i => X i n) (mem_univ a))
  exact sub_nonneg.mpr h

/-- The spread is the sum of the leader-block gaps of the configuration. -/
theorem spreadZ_eq_sum [Nonempty ι] (n : ℕ) :
    spreadZ X n = ∑ k ∈ range (Fintype.card ι),
      gapAt (fun i => X i n) (leadChain (fun i => X i n) (k + 1)) :=
  spread_eq_sum_gaps (fun i => X i n)

/-- **`(diam)`, reduced to two explicit premises.**  Assume

* `(prelim)` the deficit `max_{t≤n} X_t^i - X_n^i` is `o(n)`, uniformly in `i`;
* `(Wdrift)` at every **separated leading block** `A` (all members of `A` above all members of
  `A^c`, with `(sep)` holding) the block gap `min_{i∈A} X_n^i - max_{j∉A} X_n^j` is `o(n)`.

Then the spread `max_i X_n^i - min_i X_n^i` is `o(n)`.  This is a deterministic statement about one
finite unit-step path array; applied to `ω ↦ Swarming.Trajectory.trajectory p m ω` it gives the
paper's display `(diam)` pointwise on the event where `(prelim)` and `(Wdrift)` hold for that `ω`.

No unit-step or nonnegativity (transience) hypothesis is needed: unit steps only enter the reset
analysis (`gapAt_reset_le`), and the nonnegativity clause of `(sep)` is removed by `SepGap`.
Premise `(Wdrift)` is exactly what Proposition `group` supplies for a separated leader group
(positivity `W ≥ gap` = `gapAt_le_potential_gap`, the supermartingale `(Wdrift)`/`(Wstrict)` and
`(Qslln)`); it is *not* proved here. -/
theorem spread_div_tendsto_zero [Nonempty ι]
    (hdef : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, ((runMax X i n - X i n : ℤ) : ℝ) ≤ ε * (n : ℝ))
    (hsep : ∀ ε > 0, ∀ᶠ n in atTop, ∀ A : Finset ι, A.Nonempty → (univ \ A).Nonempty →
        (∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n) → SepGap X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ ε * (n : ℝ)) :
    Tendsto (fun n => ((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by positivity
  set e : ℝ := ε / (4 * (N + 1)) with he
  have he0 : 0 < e := by positivity
  have hNd : Tendsto (fun n : ℕ => N / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hNev : ∀ᶠ n : ℕ in atTop, N / (n : ℝ) ≤ ε / 4 :=
    ((tendsto_order.1 hNd).2 (ε / 4) (by linarith)).mono (fun n hn => le_of_lt hn)
  have hmain : ∀ᶠ n : ℕ in atTop, dist (((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) 0 < ε := by
    filter_upwards [hdef e he0, hsep e he0, hNev, eventually_ge_atTop 1] with n hd hs hNn hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have henn : (0 : ℝ) ≤ e * (n : ℝ) := by positivity
    have hterm : ∀ k ∈ range (Fintype.card ι),
        ((gapAt (fun i => X i n) (leadChain (fun i => X i n) (k + 1)) : ℤ) : ℝ)
          ≤ 1 + e * (n : ℝ) := by
      intro k _
      set A : Finset ι := leadChain (fun i => X i n) (k + 1) with hAc_def
      by_cases hguard : A.Nonempty ∧ (univ \ A).Nonempty
      · obtain ⟨hAne, hAc⟩ := hguard
        have hlead : ∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n :=
          fun i hi j hj => leadChain_dominates (fun i => X i n) (k + 1) hi hj
        by_cases hS : SepGap X A n
        · have h1 := hs A hAne hAc hlead hS
          linarith
        · have hb := inf_sub_sup_le_deficit_of_not_sepGap X hAne hAc hS
          have hsupdef : (((univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ) ≤ e * (n : ℝ) := by
            rw [sup'_cast]
            exact sup'_le hAc _ (fun j _ => by simpa using hd j)
          have hg : gapAt (fun i => X i n) A
              = A.inf' hAne (fun i => X i n) - (univ \ A).sup' hAc (fun j => X j n) := by
            rw [gapAt, dif_pos ⟨hAne, hAc⟩]
          rw [hg]
          have key : ((A.inf' hAne (fun i => X i n) - (univ \ A).sup' hAc (fun j => X j n) : ℤ) : ℝ)
              ≤ 1 + e * (n : ℝ) := by
            have hcast : ((A.inf' hAne (fun i => X i n) - (univ \ A).sup' hAc (fun j => X j n) : ℤ) : ℝ)
                ≤ ((1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ) :=
              by exact_mod_cast hb
            have hstep : ((1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ)
                = 1 + (((univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ) := by
              rw [Int.cast_add, Int.cast_one]
            rw [hstep] at hcast
            linarith
          exact key
      · have hz : gapAt (fun i => X i n) A = 0 := gapAt_eq_zero _ hguard
        rw [hz]
        push_cast
        linarith
    have hsum : ((spreadZ X n : ℤ) : ℝ) ≤ N * (1 + e * (n : ℝ)) := by
      rw [spreadZ_eq_sum X n]
      push_cast
      have hsum1 : (∑ k ∈ range (Fintype.card ι),
            ((gapAt (fun i => X i n) (leadChain (fun i => X i n) (k + 1)) : ℤ) : ℝ))
          ≤ ∑ _k ∈ range (Fintype.card ι), (1 + e * (n : ℝ)) := Finset.sum_le_sum hterm
      have hsum2 : (∑ _k ∈ range (Fintype.card ι), (1 + e * (n : ℝ)))
          = N * (1 + e * (n : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNdef]
      rwa [hsum2] at hsum1
    have hspreadnn : (0 : ℝ) ≤ ((spreadZ X n : ℤ) : ℝ) := by
      have h := spreadZ_nonneg X n
      exact_mod_cast h
    have hNe : N * e ≤ ε / 4 := by
      have hkey : N * e = (ε / 4) * (N / (N + 1)) := by
        rw [he]; field_simp
      rw [hkey]
      have h3 : (0 : ℝ) < ε / 4 := by linarith
      have hN1 : N / (N + 1) ≤ 1 := by
        have hp : (0 : ℝ) < N + 1 := by positivity
        rw [div_le_one hp]
        linarith
      calc (ε / 4) * (N / (N + 1)) ≤ (ε / 4) * 1 :=
            mul_le_mul_of_nonneg_left hN1 (le_of_lt h3)
        _ = ε / 4 := by ring
    have hfinal : ((spreadZ X n : ℤ) : ℝ) / (n : ℝ) ≤ ε / 2 := by
      rw [div_le_iff₀ hn0]
      have hNn' : N ≤ (ε / 4) * (n : ℝ) := by
        have h := (div_le_iff₀ hn0).mp hNn
        linarith
      have h2 : N * e * (n : ℝ) ≤ (ε / 4) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hNe (le_of_lt hn0)
      nlinarith [hsum, h2, hNn']
    calc dist (((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) 0
        = |((spreadZ X n : ℤ) : ℝ) / (n : ℝ)| := by rw [Real.dist_eq]; simp
      _ = ((spreadZ X n : ℤ) : ℝ) / (n : ℝ) :=
          abs_of_nonneg (div_nonneg hspreadnn (le_of_lt hn0))
      _ ≤ ε / 2 := hfinal
      _ < ε := by linarith
  exact Filter.eventually_atTop.1 hmain

/-- The integer spread cast to `ℝ` is the paper's diameter `max_i X_n^i - min_i X_n^i`. -/
theorem spreadZ_cast_eq [Nonempty ι] (n : ℕ) :
    ((spreadZ X n : ℤ) : ℝ)
      = (((univ.sup' univ_nonempty (fun i => X i n) : ℤ)) : ℝ)
        - (((univ.inf' univ_nonempty (fun i => X i n) : ℤ)) : ℝ) := by
  rw [spreadZ, Int.cast_sub]

/-- **`(diam)` in the paper's real-valued form.**  Same hypotheses as
`spread_div_tendsto_zero`. -/
theorem spread_div_tendsto_zero_real [Nonempty ι]
    (hdef : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, ((runMax X i n - X i n : ℤ) : ℝ) ≤ ε * (n : ℝ))
    (hsep : ∀ ε > 0, ∀ᶠ n in atTop, ∀ A : Finset ι, A.Nonempty → (univ \ A).Nonempty →
        (∀ i ∈ A, ∀ j ∉ A, X j n ≤ X i n) → SepGap X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ ε * (n : ℝ)) :
    Tendsto (fun n => ((((univ.sup' univ_nonempty (fun i => X i n) : ℤ)) : ℝ)
        - (((univ.inf' univ_nonempty (fun i => X i n) : ℤ)) : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  have h := spread_div_tendsto_zero X hdef hsep
  refine h.congr' ?_
  filter_upwards with n
  rw [spreadZ, Int.cast_sub]

end Reduction

end LeaderDescent
