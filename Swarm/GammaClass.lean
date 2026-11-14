/-
  **Residue-class arithmetic for a finite integer interval `[a0,b0]`.**

  This is the endpoint/cardinality layer of the paper's `(locsum)` finite-interval
  assembly, and it is free of probability.

  For `m ≥ 1` we split the integers of `[a0,b0]` into the `2m` residue classes modulo
  `2m`, indexed by `j ∈ {0,…,2m-1}`.  Class `j` starts at the *chosen first level*
  `clsY0 a0 j = a0 + j ≥ a0`, and its levels are `lvl (clsY0 a0 j) m i` for
  `i < clsK a0 b0 m j`, where `clsK a0 b0 m j` is the number of levels of class `j`
  inside `[a0,b0]` (explicitly `⌊(L-j)/2m⌋+1` for `L = b0-a0` and `j ≤ L`, and `0`
  otherwise).

  Proved here:

  * `mem_clsLevels_iff` : membership in class `j` (both set inclusions);
  * `clsLevels_disjoint` : the classes are pairwise disjoint;
  * `clsLevels_biUnion` : the classes cover `[a0,b0]` exactly;
  * `card_clsLevels` : `#(class j) = clsK`;
  * `sum_clsK` : `∑_j clsK = b0 - a0 + 1` (the exact endpoint arithmetic);
  * `sum_card_filter_clsLevels` / `card_filter_clsLevels` : for every level predicate
    `P` (e.g. "the trial `Γ_y` occurs"), the count over the whole interval equals the
    sum of the per-class counts, each of which is the corresponding count over
    `i < clsK` — the transfer that lets the residue-class count tail be summed;
  * `clsK_le_Kbar`, `len_succ_le_two_m_mul_clsK_succ` : the two size bounds on the
    number of levels per class, used for the Chernoff exponent and for the length
    hypothesis of the finite-interval theorem.
-/
import Swarm.GammaTailExp

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Enl

variable {N : ℕ}

/-! ## §1. Class data -/

/-- The first level of the class indexed by `j`: `a0 + j`.  Class `j` is the residue class
of `a0 + j` modulo `2m`. -/
def clsY0 (a0 : ℤ) (j : ℕ) : ℤ := a0 + (j : ℤ)

@[simp] lemma clsY0_apply (a0 : ℤ) (j : ℕ) : clsY0 a0 j = a0 + (j : ℤ) := rfl

lemma lvl_clsY0 (a0 : ℤ) (m j i : ℕ) :
    lvl (clsY0 a0 j) m i = a0 + (j : ℤ) + (i : ℤ) * ((2 * m : ℕ) : ℤ) := by
  simp only [lvl, clsY0]

/-- A level of class `j` as `a0` plus a natural number. -/
lemma lvl_clsY0_natCast {a0 : ℤ} {m j i : ℕ} :
    lvl (clsY0 a0 j) m i = a0 + (((j + i * (2 * m) : ℕ)) : ℤ) := by
  rw [lvl_clsY0]; push_cast; ring

lemma clsY0_nonneg {a0 : ℤ} (ha0 : 0 ≤ a0) (j : ℕ) : 0 ≤ clsY0 a0 j := by
  simp only [clsY0]; positivity

/-- The residue class of `y`, as a natural number in `[0, 2m)` (`0` for `y < a0`). -/
def clsIdx (a0 : ℤ) (m : ℕ) (y : ℤ) : ℕ := (y - a0).toNat % (2 * m)

/-- The index of `y` inside its class (`y = a0 + clsIdx + 2m * clsOff`). -/
def clsOff (a0 : ℤ) (m : ℕ) (y : ℤ) : ℕ := (y - a0).toNat / (2 * m)

/-- The number of levels of class `j` inside `[a0,b0]`.  For `a0 ≤ b0` this is the
cardinality of `{i : ℕ | a0 + j + 2m * i ≤ b0}`. -/
def clsK (a0 b0 : ℤ) (m j : ℕ) : ℕ :=
  if j ≤ (b0 - a0).toNat then ((b0 - a0).toNat - j) / (2 * m) + 1 else 0

/-- The levels of class `j` inside `[a0,b0]`. -/
def clsLevels (a0 b0 : ℤ) (m j : ℕ) : Finset ℤ :=
  (Finset.range (clsK a0 b0 m j)).image (fun i => lvl (clsY0 a0 j) m i)

/-- The uniform bound on the number of levels per class: `⌊L/2m⌋+1`. -/
def clsKbar (a0 b0 : ℤ) (m : ℕ) : ℕ := (b0 - a0).toNat / (2 * m) + 1

/-! ## §2. Elementary facts -/

lemma clsK_of_le {a0 b0 : ℤ} {m j : ℕ} (hj : j ≤ (b0 - a0).toNat) :
    clsK a0 b0 m j = ((b0 - a0).toNat - j) / (2 * m) + 1 := by
  simp only [clsK, if_pos hj]

lemma clsK_of_gt {a0 b0 : ℤ} {m j : ℕ} (hj : (b0 - a0).toNat < j) :
    clsK a0 b0 m j = 0 := by
  simp only [clsK, if_neg (Nat.not_le.mpr hj)]

lemma clsK_pos {a0 b0 : ℤ} {m j : ℕ} (hj : j ≤ (b0 - a0).toNat) :
    0 < clsK a0 b0 m j := by
  rw [clsK_of_le hj]
  exact Nat.zero_lt_succ _

lemma clsIdx_lt {a0 : ℤ} {m : ℕ} (hm : 0 < m) (y : ℤ) : clsIdx a0 m y < 2 * m := by
  simp only [clsIdx]
  exact Nat.mod_lt _ (by omega)

/-- For `y = a0 + n` the reduced offset is `n` itself. -/
lemma toNat_sub_clsY0 {a0 : ℤ} {n : ℕ} : ((a0 + (n : ℤ)) - a0).toNat = n := by
  rw [show a0 + (n : ℤ) - a0 = (n : ℤ) by ring, Int.toNat_natCast]

/-- `y` is the level of its own class at its own offset. -/
lemma level_eq_of_idx {a0 : ℤ} {m : ℕ} {y : ℤ} (ha0 : a0 ≤ y) :
    y = lvl (clsY0 a0 (clsIdx a0 m y)) m (clsOff a0 m y) := by
  have h1 : ((y - a0).toNat : ℤ) = y - a0 := Int.toNat_of_nonneg (by omega)
  have hnat : clsIdx a0 m y + clsOff a0 m y * (2 * m) = (y - a0).toNat := by
    simp only [clsIdx, clsOff]
    have := Nat.div_add_mod ((y - a0).toNat) (2 * m)
    rw [show (2 * m) * ((y - a0).toNat / (2 * m)) + (y - a0).toNat % (2 * m) =
      (y - a0).toNat % (2 * m) + (y - a0).toNat / (2 * m) * (2 * m) from by ring] at this
    exact this
  have h2 : ((clsIdx a0 m y + clsOff a0 m y * (2 * m) : ℕ) : ℤ) = y - a0 := by
    rw [hnat, h1]
  rw [lvl_clsY0_natCast]
  linarith

lemma toNat_sub_succ {a0 b0 : ℤ} (hab : a0 ≤ b0) :
    (b0 - a0).toNat + 1 = (b0 + 1 - a0).toNat := by
  have h1 : (((b0 - a0).toNat : ℕ) : ℤ) = b0 - a0 := Int.toNat_of_nonneg (by omega)
  have h2 : (((b0 + 1 - a0).toNat : ℕ) : ℤ) = b0 + 1 - a0 := Int.toNat_of_nonneg (by omega)
  omega

/-! ## §3. The class index and offset of a level -/

/-- A level of class `j` minus `a0` is the natural number `j + i * 2m`. -/
lemma lvl_sub_a0 {a0 : ℤ} {m j i : ℕ} :
    lvl (clsY0 a0 j) m i - a0 = (((j + i * (2 * m) : ℕ)) : ℤ) := by
  rw [lvl_clsY0_natCast]; ring

/-- **A level of class `j` stays in the interval.**  If `i` is one of the first `clsK`
indices then `j + i * 2m ≤ b0 - a0`. -/
lemma clsK_le_of_lt {a0 b0 : ℤ} {m j i : ℕ} (hm : 0 < m)
    (hi : i < clsK a0 b0 m j) :
    j ≤ (b0 - a0).toNat ∧ j + i * (2 * m) ≤ (b0 - a0).toNat := by
  have h2m : 0 < 2 * m := by omega
  by_cases hjL : j ≤ (b0 - a0).toNat
  · rw [clsK_of_le hjL] at hi
    have hile : i ≤ ((b0 - a0).toNat - j) / (2 * m) := by omega
    have hmul : i * (2 * m) ≤ (b0 - a0).toNat - j := (Nat.le_div_iff_mul_le h2m).mp hile
    exact ⟨hjL, by omega⟩
  · rw [clsK_of_gt (Nat.lt_of_not_le hjL)] at hi
    omega

/-- The class index of the `i`-th level of class `j` is `j`. -/
lemma clsIdx_lvl {a0 : ℤ} {m j i : ℕ} (hj : j < 2 * m) :
    clsIdx a0 m (lvl (clsY0 a0 j) m i) = j := by
  simp only [clsIdx]
  rw [lvl_sub_a0, Int.toNat_natCast]
  rw [show j + i * (2 * m) = j + (2 * m) * i by rw [Nat.mul_comm]]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-- `i ↦ lvl (clsY0 a0 j) m i` is injective. -/
lemma lvl_clsY0_injective {a0 : ℤ} {m j : ℕ} (hm : 0 < m) :
    Function.Injective (fun i : ℕ => lvl (clsY0 a0 j) m i) := by
  intro i i' h
  simp only [lvl_clsY0_natCast] at h
  have h2 : ((j + i * (2 * m) : ℕ) : ℤ) = ((j + i' * (2 * m) : ℕ) : ℤ) := by linarith
  have h3 : j + i * (2 * m) = j + i' * (2 * m) := by exact_mod_cast h2
  have h4 : i * (2 * m) = i' * (2 * m) := Nat.add_left_cancel h3
  exact Nat.mul_right_cancel (by omega) h4

/-! ## §4. Membership: the classes cover `[a0,b0]` -/

/-- A level of class `j` is at least `a0`. -/
lemma a0_le_lvl_clsY0 {a0 : ℤ} {m j i : ℕ} : a0 ≤ lvl (clsY0 a0 j) m i := by
  rw [lvl_clsY0_natCast]
  have h : (0 : ℤ) ≤ ((j + i * (2 * m) : ℕ) : ℤ) := by positivity
  linarith

/-- A level of class `j` is at most `b0` when it is one of the first `clsK` levels. -/
lemma lvl_clsY0_le_of_lt {a0 b0 : ℤ} {m j i : ℕ} (hm : 0 < m) (hab : a0 ≤ b0)
    (hi : i < clsK a0 b0 m j) : lvl (clsY0 a0 j) m i ≤ b0 := by
  obtain ⟨-, hile⟩ := clsK_le_of_lt hm hi
  rw [lvl_clsY0_natCast]
  have h1 : (((b0 - a0).toNat : ℕ) : ℤ) = b0 - a0 := Int.toNat_of_nonneg (by omega)
  have h2 : ((j + i * (2 * m) : ℕ) : ℤ) ≤ (((b0 - a0).toNat : ℕ) : ℤ) := by exact_mod_cast hile
  linarith

/-- **Membership in class `j`.**  For `m ≥ 1` and `a0 ≤ b0`, an integer `y` of `[a0,b0]`
is a level of class `j` (`j < 2m`) exactly when its own class index is `j`; the level is
then one of the first `clsK a0 b0 m j`. -/
theorem mem_clsLevels_iff {a0 b0 : ℤ} {m j : ℕ} (hm : 0 < m) (hab : a0 ≤ b0)
    (hj : j < 2 * m) {y : ℤ} :
    y ∈ clsLevels a0 b0 m j ↔ a0 ≤ y ∧ y ≤ b0 ∧ clsIdx a0 m y = j := by
  have h2m : 0 < 2 * m := by omega
  constructor
  · intro hy
    simp only [clsLevels, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, hi, hy⟩ := hy
    subst hy
    exact ⟨a0_le_lvl_clsY0, lvl_clsY0_le_of_lt hm hab hi, clsIdx_lvl hj⟩
  · rintro ⟨hge, hle, hidx⟩
    -- `y` is its own class level at its own offset
    have hyeq : y = lvl (clsY0 a0 j) m (clsOff a0 m y) := by
      rw [← hidx]; exact level_eq_of_idx hge
    have hnat : ((clsIdx a0 m y + (2 * m) * clsOff a0 m y : ℕ) : ℤ) = y - a0 := by
      have h1 : ((y - a0).toNat : ℤ) = y - a0 := Int.toNat_of_nonneg (by omega)
      have hmul : clsIdx a0 m y + (2 * m) * clsOff a0 m y = (y - a0).toNat := by
        simp only [clsIdx, clsOff]; exact Nat.mod_add_div _ _
      rw [hmul, h1]
    have hcast : (((j + clsOff a0 m y * (2 * m) : ℕ)) : ℤ) = y - a0 := by
      rw [hidx] at hnat
      rw [show j + clsOff a0 m y * (2 * m) = j + (2 * m) * clsOff a0 m y by rw [Nat.mul_comm]]
      exact hnat
    have hle' : j + clsOff a0 m y * (2 * m) ≤ (b0 - a0).toNat := by
      have h1 : (((b0 - a0).toNat : ℕ) : ℤ) = b0 - a0 := Int.toNat_of_nonneg (by omega)
      have h2 : ((j + clsOff a0 m y * (2 * m) : ℕ) : ℤ) ≤ (((b0 - a0).toNat : ℕ) : ℤ) := by
        rw [h1]; linarith
      exact_mod_cast h2
    have hjL : j ≤ (b0 - a0).toNat := by omega
    refine Finset.mem_image.mpr ⟨clsOff a0 m y, ?_, hyeq.symm⟩
    rw [Finset.mem_range, clsK_of_le hjL]
    have hmul : clsOff a0 m y * (2 * m) ≤ (b0 - a0).toNat - j := by omega
    have hfin := (Nat.le_div_iff_mul_le h2m).mpr hmul
    omega

/-! ## §5. Disjointness, covering, cardinality -/

/-- Distinct classes are disjoint. -/
theorem clsLevels_disjoint {a0 b0 : ℤ} {m : ℕ} (hm : 0 < m) (hab : a0 ≤ b0)
    {j j' : ℕ} (hj : j < 2 * m) (hj' : j' < 2 * m) (hne : j ≠ j') :
    Disjoint (clsLevels a0 b0 m j) (clsLevels a0 b0 m j') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  rw [mem_clsLevels_iff hm hab hj] at hy
  rw [mem_clsLevels_iff hm hab hj'] at hy'
  exact hne (hy.2.2.symm.trans hy'.2.2)

/-- The classes partition `[a0,b0]`. -/
theorem clsLevels_biUnion {a0 b0 : ℤ} {m : ℕ} (hm : 0 < m) (hab : a0 ≤ b0) :
    (Finset.range (2 * m)).biUnion (clsLevels a0 b0 m) = Finset.Icc a0 b0 := by
  ext y
  rw [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, hy⟩
    obtain ⟨h1, h2, -⟩ := (mem_clsLevels_iff hm hab (Finset.mem_range.mp hj)).mp hy
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨clsIdx a0 m y, Finset.mem_range.mpr (clsIdx_lt hm y),
      (mem_clsLevels_iff hm hab (clsIdx_lt hm y)).mpr ⟨h1, h2, rfl⟩⟩

/-- The levels of a class are exactly `clsK` many. -/
theorem card_clsLevels {a0 b0 : ℤ} {m j : ℕ} (hm : 0 < m) :
    (clsLevels a0 b0 m j).card = clsK a0 b0 m j := by
  rw [clsLevels, Finset.card_image_of_injective _ (lvl_clsY0_injective hm), Finset.card_range]

/-- **The endpoint arithmetic**: the class sizes sum to the length of the interval. -/
theorem sum_clsK {a0 b0 : ℤ} {m : ℕ} (hm : 0 < m) (hab : a0 ≤ b0) :
    ∑ j ∈ Finset.range (2 * m), clsK a0 b0 m j = (b0 - a0).toNat + 1 := by
  have hpd : (Finset.range (2 * m) : Set ℕ).PairwiseDisjoint (clsLevels a0 b0 m) := by
    intro a ha b hb hne
    exact clsLevels_disjoint hm hab
      (Finset.mem_range.mp (Finset.mem_coe.mp ha))
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hne
  have h1 : ∑ j ∈ Finset.range (2 * m), clsK a0 b0 m j =
      ∑ j ∈ Finset.range (2 * m), (clsLevels a0 b0 m j).card := by
    refine Finset.sum_congr rfl ?_
    intro j _
    exact (card_clsLevels (m := m) (j := j) hm).symm
  rw [h1, ← Finset.card_biUnion hpd, clsLevels_biUnion hm hab, Int.card_Icc,
    toNat_sub_succ hab]

/-- **Counting a level predicate over a finite interval, class by class.** -/
theorem sum_card_filter_clsLevels {a0 b0 : ℤ} {m : ℕ} (hm : 0 < m) (hab : a0 ≤ b0)
    (P : ℤ → Prop) [DecidablePred P] :
    ((Finset.Icc a0 b0).filter P).card =
      ∑ j ∈ Finset.range (2 * m), ((clsLevels a0 b0 m j).filter P).card := by
  have hpd : (Finset.range (2 * m) : Set ℕ).PairwiseDisjoint
      (fun j => (clsLevels a0 b0 m j).filter P) := by
    intro a ha b hb hne
    exact (clsLevels_disjoint hm hab
      (Finset.mem_range.mp (Finset.mem_coe.mp ha))
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.card_biUnion hpd, ← Finset.filter_biUnion, clsLevels_biUnion hm hab]

/-- A per-class count is a count over the first `clsK` levels of the class. -/
theorem card_filter_clsLevels {a0 b0 : ℤ} {m j : ℕ} (hm : 0 < m)
    (P : ℤ → Prop) [DecidablePred P] :
    ((clsLevels a0 b0 m j).filter P).card =
      ((Finset.range (clsK a0 b0 m j)).filter (fun i => P (lvl (clsY0 a0 j) m i))).card := by
  rw [clsLevels, Finset.filter_image, Finset.card_image_of_injective _ (lvl_clsY0_injective hm)]

/-! ## §6. Size bounds on the number of levels per class -/

/-- Uniform upper bound: a class never has more than `L / 2m + 1` levels. -/
theorem clsK_le_Kbar {a0 b0 : ℤ} {m j : ℕ} (hm : 0 < m) (hab : a0 ≤ b0) :
    clsK a0 b0 m j ≤ clsKbar a0 b0 m := by
  by_cases hj : j ≤ (b0 - a0).toNat
  · rw [clsK_of_le hj]
    have h := Nat.div_le_div_right (Nat.sub_le ((b0 - a0).toNat) j) (c := 2 * m)
    simp only [clsKbar]
    omega
  · rw [clsK_of_gt (Nat.lt_of_not_le hj)]
    exact Nat.zero_le _

/-- Every class `j < 2m` has at least `(L+1)/2m - 1` levels: `L+1 ≤ 2m (clsK+1)`. -/
theorem len_succ_le_two_m_mul_clsK_succ {a0 b0 : ℤ} {m j : ℕ} (hm : 0 < m) (hab : a0 ≤ b0)
    (hj : j < 2 * m) :
    (b0 - a0).toNat + 1 ≤ 2 * m * (clsK a0 b0 m j + 1) := by
  have h2m : 0 < 2 * m := by omega
  by_cases hjL : j ≤ (b0 - a0).toNat
  · rw [clsK_of_le hjL]
    have hdm : (2 * m) * (((b0 - a0).toNat - j) / (2 * m)) +
        ((b0 - a0).toNat - j) % (2 * m) = (b0 - a0).toNat - j := Nat.div_add_mod _ _
    have hmod : ((b0 - a0).toNat - j) % (2 * m) < 2 * m := Nat.mod_lt _ h2m
    have he : 2 * m * (((b0 - a0).toNat - j) / (2 * m) + 1 + 1) =
        (2 * m) * (((b0 - a0).toNat - j) / (2 * m)) + 2 * m + 2 * m := by ring
    rw [he]
    omega
  · rw [clsK_of_gt (Nat.lt_of_not_le hjL)]
    omega

end Swarming.Enl
