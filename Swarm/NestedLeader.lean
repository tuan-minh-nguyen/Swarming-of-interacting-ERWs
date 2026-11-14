/-
# Nested leader induction: the paper's induction on the leading block size

This module formalises the *nested* part of the paper's proof of

  (diam)   `(max_i X_n^i - min_i X_n^i)/n → 0`,

i.e. the induction on `k` that bounds the difference between the largest and the `(k+1)`-th
largest position (Proposition `group` in `main_1d_revised.tex`).

The existing `Swarm/LeaderDescent.lean` reduces `(diam)` to a premise about *every*
separated leading block at time `n`.  The paper's actual input is weaker and has a different
shape: at the reset time `s` of a leading block `A`, the group potential is comparable to

  `max_A X_s - min_A X_s + deficit_s + 2`,

and the *internal* spread `max_A X_s - min_A X_s` is not known to be small.  This file proves that
the internal spread is nevertheless harmless, because it is exactly the level-`|A|` spread, which
the induction on the block size has already controlled at the earlier time `s ≤ n`.  Nothing here
is probabilistic: the only stochastic input is the single hypothesis `DriftInput` (the telescoped
`(Wdrift)` with the `hcomp` comparison and the `Q` martingale correction), which is stated as an
explicit residual and is *not* the conclusion.

Main results:

* `blockSpread_sdiff_min` — the exact recursion `spread(A) = spread(A \ {a}) + gap(A \ {a})` at a
  minimal element `a` of a leading block `A`;
* `P_succ` — the induction step `P k → G k → P (k+1)`;
* `G_of_P` — the level-`k` gap bound from the level-`k` spread bound and the drift input;
* `spread_div_tendsto_zero_of_drift` — `(diam)` from the drift input, the deficit estimate
  `(prelim)` and eventual nonnegativity (transience).
-/
import Swarm.LeaderDescent

open Filter Finset Topology
open scoped BigOperators
open LeaderDescent

namespace NestedLeader

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part A: leading blocks and their exact spread/gap recursion -/

/-- `A` is a leading block of the configuration `f`: every member of `A` is at least as high as
every non-member. -/
def Leading (f : ι → ℤ) (A : Finset ι) : Prop := ∀ i ∈ A, ∀ j ∉ A, f j ≤ f i

theorem leading_univ (f : ι → ℤ) : Leading f univ := fun _ _ j hj => absurd (mem_univ j) hj

/-- The internal spread `max_A f - min_A f` of a block; junk value `0` for the empty block. -/
noncomputable def blockSpread (f : ι → ℤ) (A : Finset ι) : ℤ :=
  if h : A.Nonempty then A.sup' h f - A.inf' h f else 0

theorem blockSpread_eq {f : ι → ℤ} {A : Finset ι} (h : A.Nonempty) :
    blockSpread f A = A.sup' h f - A.inf' h f := by
  unfold blockSpread
  rw [dif_pos h]

theorem blockSpread_empty (f : ι → ℤ) : blockSpread f ∅ = 0 := by
  unfold blockSpread
  rw [dif_neg (by simp)]

theorem blockSpread_nonneg {f : ι → ℤ} (A : Finset ι) : 0 ≤ blockSpread f A := by
  by_cases h : A.Nonempty
  · rw [blockSpread_eq h]
    have hmem := h
    obtain ⟨a, ha⟩ := h
    have h1 : A.inf' hmem f ≤ f a := inf'_le _ ha
    have h2 : f a ≤ A.sup' hmem f := le_sup' f ha
    linarith
  · unfold blockSpread
    rw [dif_neg h]

theorem blockSpread_singleton (f : ι → ℤ) (i : ι) : blockSpread f {i} = 0 := by
  have h : ({i} : Finset ι).Nonempty := ⟨i, mem_singleton_self i⟩
  rw [blockSpread_eq h]
  simp

/-- A block obtained by removing the minimal element of a leading block is leading. -/
theorem leading_erase {f : ι → ℤ} {A : Finset ι} {a : ι} (hLA : Leading f A) (ha : a ∈ A)
    (hmin : ∀ i ∈ A, f a ≤ f i) : Leading f (A.erase a) := by
  intro i hi j hj
  have hiA : i ∈ A := mem_of_mem_erase hi
  by_cases hjA : j ∈ A
  · have hja : j = a := by
      by_contra hne
      exact hj (mem_erase.mpr ⟨hne, hjA⟩)
    rw [hja]
    exact hmin i hiA
  · exact hLA i hiA j hjA

theorem inf'_eq_of_min {f : ι → ℤ} {A : Finset ι} {a : ι} (ha : a ∈ A)
    (hmin : ∀ i ∈ A, f a ≤ f i) : A.inf' ⟨a, ha⟩ f = f a :=
  le_antisymm (inf'_le _ ha) (le_inf' _ f hmin)

theorem sup'_erase_of_min {f : ι → ℤ} {A : Finset ι} {a : ι} (ha : a ∈ A)
    (hmin : ∀ i ∈ A, f a ≤ f i) (hne : (A.erase a).Nonempty) :
    (A.erase a).sup' hne f = A.sup' ⟨a, ha⟩ f := by
  refine le_antisymm (sup'_le hne f (fun b hb => le_sup' f (mem_of_mem_erase hb))) ?_
  refine sup'_le ⟨a, ha⟩ f (fun i hi => ?_)
  by_cases hia : i = a
  · obtain ⟨b, hb⟩ := hne
    have hbA : f a ≤ f b := hmin b (mem_of_mem_erase hb)
    rw [hia]
    exact le_trans hbA (le_sup' f hb)
  · exact le_sup' f (mem_erase.mpr ⟨hia, hi⟩)

theorem sup'_compl_erase {f : ι → ℤ} {A : Finset ι} {a : ι} (ha : a ∈ A) (hLA : Leading f A) :
    (univ \ A.erase a).sup' ⟨a, mem_sdiff.mpr ⟨mem_univ a, by simp⟩⟩ f = f a := by
  refine le_antisymm (sup'_le _ f (fun j hj => ?_))
    (le_sup' f (mem_sdiff.mpr ⟨mem_univ a, by simp⟩))
  obtain ⟨-, hja⟩ := mem_sdiff.mp hj
  by_cases hjA : j ∈ A
  · have hje : j = a := by
      by_contra hne
      exact hja (mem_erase.mpr ⟨hne, hjA⟩)
    rw [hje]
  · exact hLA a ha j hjA

/-- The gap of the block obtained by removing the minimal element `a` of a leading block `A`. -/
theorem gapAt_erase_eq {f : ι → ℤ} {A : Finset ι} {a : ι} (ha : a ∈ A) (hLA : Leading f A)
    (hmin : ∀ i ∈ A, f a ≤ f i) (hne : (A.erase a).Nonempty) :
    gapAt f (A.erase a) = (A.erase a).inf' hne f - f a := by
  have hc : (univ \ A.erase a).Nonempty := ⟨a, mem_sdiff.mpr ⟨mem_univ a, by simp⟩⟩
  rw [gapAt, dif_pos ⟨hne, hc⟩, sup'_compl_erase ha hLA]

/-- **The spread/gap recursion at a minimal element.**  For a leading block `A` and a minimal
element `a` of `A`, the internal spread of `A` is the internal spread of `A \ {a}` plus the gap of
`A \ {a}`.  This is the exact recursion the induction on the block size uses. -/
theorem blockSpread_sdiff_min {f : ι → ℤ} {A : Finset ι} {a : ι} (ha : a ∈ A)
    (hLA : Leading f A) (hmin : ∀ i ∈ A, f a ≤ f i) :
    blockSpread f A = blockSpread f (A.erase a) + gapAt f (A.erase a) := by
  by_cases hne : (A.erase a).Nonempty
  · rw [blockSpread_eq ⟨a, ha⟩, blockSpread_eq hne, gapAt_erase_eq ha hLA hmin hne,
      sup'_erase_of_min ha hmin hne, inf'_eq_of_min ha hmin]
    ring
  · have hemp : A.erase a = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hsingle : A = {a} := by
      rw [← insert_erase ha, hemp]
      simp
    subst hsingle
    rw [blockSpread_singleton, hemp, blockSpread_empty, gapAt_eq_zero f (by simp)]
    ring

/-! ## Part A': casting finite minima and bounding the spread of a bounded block -/

theorem inf'_cast {s : Finset ι} (h : s.Nonempty) (f : ι → ℤ) :
    ((s.inf' h f : ℤ) : ℝ) = s.inf' h (fun i => (f i : ℝ)) := by
  obtain ⟨a, ha, hmin⟩ := exists_min_image s f h
  have h1 : s.inf' h f = f a := le_antisymm (inf'_le _ ha) (le_inf' _ f hmin)
  have h2 : s.inf' h (fun i => (f i : ℝ)) = (f a : ℝ) :=
    le_antisymm (inf'_le _ ha) (le_inf' _ _ (fun b hb => by exact_mod_cast hmin b hb))
  rw [h1, h2]

/-! ## Part B: the deficit, the drift input and the nested induction -/

section Main

variable (X : ι → ℕ → ℤ) [Nonempty ι]

/-- The deficit `max_j (M^j_t - X^j_t)` at time `t`: the paper's `(prelim)` quantity. -/
noncomputable def deficit (t : ℕ) : ℤ :=
  univ.sup' univ_nonempty (fun j => runMax X j t - X j t)

theorem le_deficit (t : ℕ) (j : ι) : runMax X j t - X j t ≤ deficit X t :=
  le_sup' (fun j => runMax X j t - X j t) (mem_univ j)

theorem deficit_nonneg (t : ℕ) : 0 ≤ deficit X t := by
  have h2 : 0 ≤ runMax X (Classical.arbitrary ι) t - X (Classical.arbitrary ι) t :=
    sub_nonneg.mpr (le_runMax X _ t)
  have h3 := le_deficit X t (Classical.arbitrary ι)
  linarith

theorem sup_compl_le_deficit {A : Finset ι} (hAc : (univ \ A).Nonempty) (t : ℕ) :
    (univ \ A).sup' hAc (fun j => runMax X j t - X j t) ≤ deficit X t :=
  sup'_le _ _ (fun j _ => le_deficit X t j)

/-! ### Unit steps give bounded positions -/

theorem step_dichotomy (hX : UnitStep X) (i : ι) (n : ℕ) :
    X i (n + 1) = X i n + 1 ∨ X i (n + 1) = X i n - 1 := by
  have h := hX i n
  have h1 : -1 ≤ X i (n + 1) - X i n := (abs_le.mp (le_of_eq h)).1
  have h2 : X i (n + 1) - X i n ≤ 1 := (abs_le.mp (le_of_eq h)).2
  have hne : X i (n + 1) - X i n ≠ 0 := by
    intro hc
    rw [hc] at h
    simp at h
  omega

theorem abs_X_le (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) (i : ι) (n : ℕ) :
    |X i n| ≤ (n : ℤ) := by
  induction n with
  | zero => simp [h0 i]
  | succ n ih =>
    rcases step_dichotomy X hX i n with h | h
    · rw [h]
      have habs : |X i n + 1| ≤ |X i n| + |(1 : ℤ)| := abs_add_le _ _
      rw [abs_one] at habs
      push_cast
      linarith
    · have hrew : X i n - 1 = X i n + (-1 : ℤ) := by ring
      rw [h, hrew]
      have habs : |X i n + (-1 : ℤ)| ≤ |X i n| + |(-1 : ℤ)| := abs_add_le _ _
      rw [abs_neg, abs_one] at habs
      push_cast
      linarith

theorem blockSpread_le_two_mul (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    {A : Finset ι} (hA : A.Nonempty) (t : ℕ) :
    ((blockSpread (fun i => X i t) A : ℤ) : ℝ) ≤ 2 * (t : ℝ) := by
  rw [blockSpread_eq hA]
  have hhi : ∀ i ∈ A, X i t ≤ (t : ℤ) := fun i _ => (abs_le.mp (abs_X_le X hX h0 i t)).2
  have hlo : ∀ i ∈ A, -(t : ℤ) ≤ X i t := fun i _ => (abs_le.mp (abs_X_le X hX h0 i t)).1
  have hsup : ((A.sup' hA (fun i => X i t) : ℤ) : ℝ) ≤ (t : ℝ) := by
    rw [sup'_cast hA (fun i => X i t)]
    exact sup'_le hA _ (fun i hi => by exact_mod_cast hhi i hi)
  have hinf : (-(t : ℝ)) ≤ ((A.inf' hA (fun i => X i t) : ℤ) : ℝ) := by
    rw [inf'_cast hA (fun i => X i t)]
    exact le_inf' hA _ (fun i hi => by exact_mod_cast hlo i hi)
  have hcast : (((A.sup' hA (fun i => X i t) - A.inf' hA (fun i => X i t) : ℤ)) : ℝ)
      = ((A.sup' hA (fun i => X i t) : ℤ) : ℝ)
        - ((A.inf' hA (fun i => X i t) : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

theorem deficit_le_self (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) (t : ℕ) :
    ((deficit X t : ℤ) : ℝ) ≤ 2 * (t : ℝ) := by
  rw [deficit, sup'_cast univ_nonempty (fun j => runMax X j t - X j t)]
  refine sup'_le univ_nonempty _ (fun j _ => ?_)
  have hle : runMax X j t ≤ (t : ℤ) := by
    refine sup'_le ⟨0, mem_range.mpr (Nat.succ_pos t)⟩ (fun s => X j s) (fun s hs => ?_)
    have hst : s ≤ t := by
      simp only [mem_range] at hs
      omega
    exact le_trans (abs_le.mp (abs_X_le X hX h0 j s)).2 (by exact_mod_cast hst)
  have hge : -(t : ℤ) ≤ X j t := (abs_le.mp (abs_X_le X hX h0 j t)).1
  have hcast : ((runMax X j t - X j t : ℤ) : ℝ)
      = ((runMax X j t : ℤ) : ℝ) - ((X j t : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  have h1 : ((runMax X j t : ℤ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hle
  have h2 : (-(t : ℝ)) ≤ ((X j t : ℤ) : ℝ) := by exact_mod_cast hge
  linarith

end Main

/-! ## Part C: the two level predicates and the drift residual -/

section Levels

variable (X : ι → ℕ → ℤ) [Nonempty ι]

/-- `P k`: every nonempty leading block of size `k` has internal spread `o(n)`. -/
def P (k : ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ∀ (A : Finset ι) (hA : A.Nonempty),
    A.card = k → Leading (fun i => X i t) A →
    ((blockSpread (fun i => X i t) A : ℤ) : ℝ) ≤ ε * (t : ℝ)

/-- `G k`: every proper leading block of size `k` has block gap `o(n)`. -/
def G (k : ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
    A.card = k → Leading (fun i => X i n) A →
    ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ ε * (n : ℝ)

/-- **The residual drift input.**  The composite of `gap ≤ W` (`gapAt_le_potential_gap`), the
telescoped `(Wdrift)` with its `Q` martingale correction (`WdriftJoint.telescope_of_sep`,
`Qslln`) and the `hcomp` comparison: at the reset time `s` of a separated leading block `A` the
block potential is bounded by `C` times the *internal* spread of `A` at `s` plus the deficit at `s`
plus `2`, up to `o(n)`.  This is exactly the paper's display
`W_s^{A,A^c} ≤ C(max_{i∈A}X_s^i - min_{i∈A}X_s^i + max_{j∈A^c}(M_s^j - X_s^j) + 2) + o(n)`.
It is *not* the conclusion: the internal spread is at the same (earlier) time `s` and only enters
through the level-`|A|` induction hypothesis. -/
def DriftInput (C : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
    Leading (fun i => X i n) A → SepMax X A n →
    ((gapAt (fun i => X i n) A : ℤ) : ℝ)
      ≤ C * (((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
              + ((deficit X (resetTime X A n) : ℤ) : ℝ) + 2) + ε * (n : ℝ)

end Levels

/-! ## Part D: the level transfer and the nested induction -/

section Induction

variable (X : ι → ℕ → ℤ) [Nonempty ι]

/-- **The level-`k` transfer.**  From the level-`k` internal-spread bound `P k`, the drift residual
and the deficit estimate `(prelim)` one gets the level-`k` block-gap bound `G k`.

For a leading block `A` of size `k` at time `n`:
* if the separation clause fails at `n`, the gap is at most `1 + deficit_n` (the paper's first
  case);
* otherwise `A` is separated from its complement from its reset time `s` on, so the drift residual
  bounds the gap at `n` by `C (spread_A(s) + deficit_s + 2) + o(n)`; the reset time satisfies
  `s ≤ n`, so `P k` at `s` (or the crude bound `spread ≤ 2s ≤ 2T` when `s` is small) makes the
  internal spread part of `o(n)`.  This is the place where the induction is *nested*. -/
theorem G_of_P (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hdrift : DriftInput X C)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 ≤ X i n)
    {k : ℕ} (hP : P X k) : G X k := by
  intro ε hε
  set δ : ℝ := ε / (8 * (C + 1)) with hδdef
  have hden : (0:ℝ) < 8 * (C + 1) := by linarith
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε hden
  have hδeq : δ * (8 * (C + 1)) = ε := by rw [hδdef]; field_simp
  have hδle : δ ≤ ε / 8 := by nlinarith [hδeq, hδ, hC]
  have hCδ : 3 * C * δ ≤ 3 * ε / 8 := by nlinarith [hδeq, hδ, hC]
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp (hP δ hδ)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hdef δ hδ)
  obtain ⟨T₃, hT₃⟩ := Filter.eventually_atTop.mp (hdrift δ hδ)
  obtain ⟨T₄, hT₄⟩ := Filter.eventually_atTop.mp hpos
  set T : ℕ := max T₁ T₂ with hTdef
  have hT1T : T₁ ≤ T := le_max_left _ _
  have hT2T : T₂ ≤ T := le_max_right _ _
  obtain ⟨N₅, hN₅⟩ := exists_nat_gt (16 * (C * (8 * (T : ℝ) + 6)) / ε)
  obtain ⟨N₆, hN₆⟩ := exists_nat_gt (8 / ε)
  filter_upwards [Filter.eventually_ge_atTop T₃, Filter.eventually_ge_atTop T₄,
    Filter.eventually_ge_atTop T, Filter.eventually_ge_atTop N₅,
    Filter.eventually_ge_atTop N₆] with n hn₃ hn₄ hnT hn₅ hn₆
  intro A hA hAc hcard hlead
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hTnn : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  have hδn : (0:ℝ) ≤ δ * (n:ℝ) := mul_nonneg (le_of_lt hδ) hnn
  have hC4 : C * (8 * (T:ℝ) + 6) ≤ ε * (n:ℝ) / 16 := by
    have h1 : (N₅:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn₅
    have h3 : 16 * (C * (8 * (T:ℝ) + 6)) / ε ≤ (n:ℝ) := le_trans (le_of_lt hN₅) h1
    rw [div_le_iff₀ hε] at h3
    linarith
  have hεn : 1 ≤ ε * (n:ℝ) / 4 := by
    have h1 : (N₆:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn₆
    have h3 : 8 / ε ≤ (n:ℝ) := le_trans (le_of_lt hN₆) h1
    rw [div_le_iff₀ hε] at h3
    nlinarith
  by_cases hsep : SepGap X A n
  · have hSepMax : SepMax X A n := ⟨fun i => hT₄ n hn₄ i, hsep⟩
    have hdr := hT₃ n hn₃ A hA hAc hlead hSepMax
    have hsle : resetTime X A n ≤ n :=
      resetTime_minimal X A n (fun t h1 h2 => by
        have htn : t = n := le_antisymm h2 h1
        rw [htn]
        exact hSepMax)
    have hlead_s : Leading (fun i => X i (resetTime X A n)) A :=
      leading_of_sepGap X (resetTime_spec X A n (resetTime X A n) le_rfl hsle).2
    have hsleR : (resetTime X A n : ℝ) ≤ (n:ℝ) := by exact_mod_cast hsle
    have hspread : ((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
        ≤ δ * (n:ℝ) + (8 * (T:ℝ) + 6) := by
      by_cases hs : T ≤ resetTime X A n
      · have h1 := hT₁ (resetTime X A n) (le_trans hT1T hs) A hA hcard hlead_s
        have h2 : δ * (resetTime X A n : ℝ) ≤ δ * (n:ℝ) :=
          mul_le_mul_of_nonneg_left hsleR (le_of_lt hδ)
        linarith
      · have h1 := blockSpread_le_two_mul X hX h0 hA (resetTime X A n)
        have h2 : (resetTime X A n : ℝ) ≤ (T:ℝ) := by
          have := Nat.lt_of_not_le hs
          exact_mod_cast le_of_lt this
        linarith
    have hdefs : ((deficit X (resetTime X A n) : ℤ) : ℝ)
        ≤ 2 * δ * (n:ℝ) + (8 * (T:ℝ) + 6) := by
      by_cases hs : T ≤ resetTime X A n
      · have h1 := hT₂ (resetTime X A n) (le_trans hT2T hs)
        have h2 : δ * (resetTime X A n : ℝ) ≤ δ * (n:ℝ) :=
          mul_le_mul_of_nonneg_left hsleR (le_of_lt hδ)
        linarith
      · have h1 := deficit_le_self X hX h0 (resetTime X A n)
        have h2 : (resetTime X A n : ℝ) ≤ (T:ℝ) := by
          have := Nat.lt_of_not_le hs
          exact_mod_cast le_of_lt this
        linarith
    have hsum : ((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
        + ((deficit X (resetTime X A n) : ℤ) : ℝ) + 2
        ≤ 3 * δ * (n:ℝ) + (16 * (T:ℝ) + 18) := by linarith
    have hC16 : C * (16 * (T:ℝ) + 18) ≤ ε * (n:ℝ) / 4 := by
      nlinarith [hC4, hC, hTnn]
    have hCsum : C * (((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
        + ((deficit X (resetTime X A n) : ℤ) : ℝ) + 2)
        ≤ 3 * C * δ * (n:ℝ) + C * (16 * (T:ℝ) + 18) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum hC]
    have hstep1 : 3 * C * δ * (n:ℝ) ≤ 3 * ε / 8 * (n:ℝ) :=
      mul_le_mul_of_nonneg_right hCδ hnn
    have hstep2 : δ * (n:ℝ) ≤ ε / 8 * (n:ℝ) :=
      mul_le_mul_of_nonneg_right hδle hnn
    have hfin : 3 * C * δ * (n:ℝ) + C * (16 * (T:ℝ) + 18) + δ * (n:ℝ)
        ≤ ε * (n:ℝ) := by nlinarith [hC16, hstep1, hstep2]
    linarith [hdr, hCsum, hfin]
  · have h1 := inf_sub_sup_le_deficit_of_not_sepGap X hA hAc hsep
    have hgap_eq : gapAt (fun i => X i n) A
        = A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun i => X i n) := by
      rw [gapAt, dif_pos ⟨hA, hAc⟩]
    have h2 := sup_compl_le_deficit X hAc n
    have h3 := hT₂ n (le_trans hT2T hnT)
    have hcast1 : (((A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun i => X i n) : ℤ)) : ℝ)
        = ((A.inf' hA (fun i => X i n) : ℤ) : ℝ)
          - (((univ \ A).sup' hAc (fun i => X i n) : ℤ) : ℝ) := by push_cast; ring
    have hc1 : (((A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun i => X i n) : ℤ)) : ℝ)
        ≤ ((1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ) := by
      exact_mod_cast h1
    have hcast2 : ((1 + (univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ)
        = 1 + (((univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ) := by
      push_cast; ring
    have hc2 : (((univ \ A).sup' hAc (fun j => runMax X j n - X j n) : ℤ) : ℝ)
        ≤ ((deficit X n : ℤ) : ℝ) := by exact_mod_cast h2
    have h4 : (((A.inf' hA (fun i => X i n) - (univ \ A).sup' hAc (fun i => X i n) : ℤ)) : ℝ)
        ≤ 1 + δ * (n:ℝ) := by linarith
    rw [hgap_eq]
    have hstep3 : δ * (n:ℝ) ≤ ε / 8 * (n:ℝ) :=
      mul_le_mul_of_nonneg_right hδle hnn
    linarith

/-- **The nested induction step.**  The level-`(k+1)` internal-spread bound follows from the
level-`k` internal-spread bound and the level-`k` gap bound, through the exact recursion
`spread(A) = spread(A \ {a}) + gap(A \ {a})` at a minimal element `a` of `A`. -/
theorem P_succ {k : ℕ} (hP : P X k) (hG : G X k) : P X (k + 1) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp (hP (ε / 2) hε2)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hG (ε / 2) hε2)
  filter_upwards [Filter.eventually_ge_atTop T₁, Filter.eventually_ge_atTop T₂] with t ht1 ht2
  intro A hA hcard hlead
  obtain ⟨a, ha, hmin⟩ := exists_min_image A (fun i => X i t) hA
  have hsplit := blockSpread_sdiff_min (f := fun i => X i t) ha hlead hmin
  have hca : (A.erase a).card = k := by
    rw [card_erase_of_mem ha, hcard]
    omega
  have hleadB : Leading (fun i => X i t) (A.erase a) := leading_erase hlead ha hmin
  have hcastsum : (((blockSpread (fun i => X i t) (A.erase a)
      + gapAt (fun i => X i t) (A.erase a) : ℤ)) : ℝ)
      = ((blockSpread (fun i => X i t) (A.erase a) : ℤ) : ℝ)
        + ((gapAt (fun i => X i t) (A.erase a) : ℤ) : ℝ) := by push_cast; ring
  rw [hsplit, hcastsum]
  by_cases hne : (A.erase a).Nonempty
  · have h1 := hT₁ t ht1 (A.erase a) hne hca hleadB
    have h2 := hT₂ t ht2 (A.erase a) hne ⟨a, mem_sdiff.mpr ⟨mem_univ a, by simp⟩⟩ hca hleadB
    linarith
  · have hemp : A.erase a = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hemp, blockSpread_empty, gapAt_eq_zero (fun i => X i t) (by simp)]
    push_cast
    have ht : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
    nlinarith [hε]

/-- The nested induction: `P k` holds for every `k`. -/
theorem P_all (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hdrift : DriftInput X C)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 ≤ X i n) :
    ∀ k, P X k := by
  intro k
  induction k with
  | zero =>
    intro ε hε
    filter_upwards with t A hA hcard hlead
    have hpos' : 0 < A.card := Finset.card_pos.mpr hA
    exact absurd hcard (by omega : A.card ≠ 0)
  | succ k ih =>
    exact P_succ X ih (G_of_P X hX h0 hC hdrift hdef hpos ih)

/-- **`(diam)` from the drift residual.**  The whole spread is `o(n)`. -/
theorem spread_le_of_drift (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hdrift : DriftInput X C)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 ≤ X i n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ((spreadZ X n : ℤ) : ℝ) ≤ ε * (n : ℝ) := by
  intro ε hε
  have hPN := P_all X hX h0 hC hdrift hdef hpos (Fintype.card ι) ε hε
  filter_upwards [hPN] with n hn
  have h1 := hn univ univ_nonempty (by simp) (leading_univ (fun i => X i n))
  have h2 : ((spreadZ X n : ℤ) : ℝ) = ((blockSpread (fun i => X i n) univ : ℤ) : ℝ) := by
    rw [blockSpread_eq univ_nonempty]
    rfl
  rw [h2]
  exact h1

/-- **`(diam)` in the paper's normalised form.** -/
theorem spread_div_tendsto_zero_of_drift (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0) {C : ℝ}
    (hC : 0 ≤ C) (hdrift : DriftInput X C)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 ≤ X i n) :
    Tendsto (fun n => ((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hbound := spread_le_of_drift X hX h0 hC hdrift hdef hpos
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hbound (ε / 2) (by linarith))
  refine ⟨max N₁ 1, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn := hN₁ n hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn2
  have hnn : (0:ℝ) ≤ ((spreadZ X n : ℤ) : ℝ) := by
    have h := spreadZ_nonneg X n
    exact_mod_cast h
  have hnonneg : 0 ≤ ((spreadZ X n : ℤ) : ℝ) / (n:ℝ) := div_nonneg hnn (le_of_lt hnpos)
  have hdiv : ((spreadZ X n : ℤ) : ℝ) / (n:ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hnpos]
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- The gap estimate used by `LeaderDescent.spread_div_tendsto_zero` implies the drift residual
with `C = 0`: the drift formulation strictly generalises the earlier reduction. -/
theorem driftInput_zero_of_gap (hsep : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
      Leading (fun i => X i n) A → SepMax X A n →
      ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ ε * (n : ℝ)) :
    DriftInput X 0 := by
  intro ε hε
  filter_upwards [hsep ε hε] with n hn A hA hAc hlead hsepMax
  have := hn A hA hAc hlead hsepMax
  simpa using this

/-- **Decomposition of the drift residual into the paper's three named inputs.**  If a block
potential `W` satisfies

* `hgap` — `gap(A,n) ≤ W_n(A)`: `gapAt_le_potential_gap` for the actual `H`-potential;
* `htel` — `W_n(A) ≤ W_s(A) + o(n)` at the reset time `s`: the telescoped `(Wdrift)` with its `Q`
  martingale correction (`WdriftJoint.telescope_of_sep` together with `Qslln`);
* `hcomp` — `W_s(A) ≤ K (spread_A(s) + deficit_s + 2) + o(n)`: the `hcomp` comparison of the
  paper, with the reset-time gap replaced by the internal spread;

then `DriftInput X K` holds, so `spread_div_tendsto_zero_of_drift` applies.  This isolates the
three obligations and shows that the drift residual above is not a restatement of `(diam)`: each
of the three is a statement about the potential, not about the block gap at time `n`. -/
theorem DriftInput_of_W (W : Finset ι → ℕ → ℝ)
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ W A n + ε * (n : ℝ))
    (htel : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A n ≤ W A (resetTime X A n) + ε * (n : ℝ))
    (hcomp : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A (resetTime X A n)
          ≤ K * (((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
              + ((deficit X (resetTime X A n) : ℤ) : ℝ) + 2) + ε * (n : ℝ)) :
    DriftInput X K := by
  intro ε hε
  have h3 : 0 < ε / 3 := by linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hgap (ε / 3) h3)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htel (ε / 3) h3)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp (hcomp (ε / 3) h3)
  filter_upwards [Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop N₂,
    Filter.eventually_ge_atTop N₃] with n hn1 hn2 hn3
  intro A hA hAc hlead hsepMax
  have h1 := hN₁ n hn1 A hA hAc hlead hsepMax
  have h2 := hN₂ n hn2 A hA hAc hlead hsepMax
  have h4 := hN₃ n hn3 A hA hAc hlead hsepMax
  linarith

/-- **`(diam)` from the three named potential inputs.** -/
theorem spread_div_tendsto_zero_of_W {K : ℝ} (hK : 0 ≤ K) (W : Finset ι → ℕ → ℝ)
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ W A n + ε * (n : ℝ))
    (htel : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A n ≤ W A (resetTime X A n) + ε * (n : ℝ))
    (hcomp : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A (resetTime X A n)
          ≤ K * (((blockSpread (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
              + ((deficit X (resetTime X A n) : ℤ) : ℝ) + 2) + ε * (n : ℝ))
    (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 ≤ X i n) :
    Tendsto (fun n => ((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
  spread_div_tendsto_zero_of_drift X hX h0 hK
    (DriftInput_of_W X W hgap htel hcomp) hdef hpos

end Induction

end NestedLeader


