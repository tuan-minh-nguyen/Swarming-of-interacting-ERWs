/-
Certified core of the potential-theoretic part of  main_1d.tex
("Swarming of interacting excited random walks", §2.1-2.2).

Everything here is the *deterministic* skeleton that the probabilistic
arguments of the paper consume:

*  (unit)      w(x) h(x) - (1-w(x)) h(x-1) = 1                  (eq. (unit))
*  h(x) >= 1                                                     ("By (hrec), we have h^w(x) >= 1")
*  w <= w'  =>  h^{w'} <= h^w                                    (comparison used for (hcomp),(dominate))
*  H^w - H^{w'} >= 0 and nondecreasing                           (eq. (hmono))
*  the Poisson-equation drift identity
      alpha h(x) - (1-alpha) h(x-1) = 1 + (alpha - w(x)) (h(x)+h(x-1))
   which is the displayed computation in the proof of Proposition (group) and
   the basis of (Zdrift).
*  the closed form of the affine recursion
      y(x+1) = c + a*y(x)   ==>   y(x) = L + a^x (y(0)-L),  L = c/(1-a)
   and of its partial sums, i.e. eqs. (projh) and (projH).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Cookie

open Finset

/-- The potential `h^w` of the paper, on `x >= 0`, with the boundary convention `h(-1) = 1`:
`h(x) = (1 + (1 - w x) * h(x-1)) / w x`. -/
noncomputable def hfix (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 + (1 - w 0) * 1) / w 0
  | (n + 1) => (1 + (1 - w (n + 1)) * hfix w n) / w (n + 1)

/-- `h(x-1)`, with the convention `h(-1) = 1`. -/
noncomputable def hprev (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else hfix w (n - 1)

@[simp] lemma hprev_zero (w : ℕ → ℝ) : hprev w 0 = 1 := by simp [hprev]

@[simp] lemma hprev_succ (w : ℕ → ℝ) (n : ℕ) : hprev w (n + 1) = hfix w n := by
  simp [hprev]

lemma hfix_eq (w : ℕ → ℝ) (n : ℕ) :
    hfix w n = (1 + (1 - w n) * hprev w n) / w n := by
  cases n with
  | zero => simp [hfix, hprev]
  | succ k => simp [hfix, hprev]

/-- **(unit)**: the one-dimensional Poisson equation of §2.1. -/
theorem unit (w : ℕ → ℝ) (hw : ∀ n, w n ≠ 0) (n : ℕ) :
    w n * hfix w n - (1 - w n) * hprev w n = 1 := by
  have h1 : w n * hfix w n = 1 + (1 - w n) * hprev w n := by
    rw [hfix_eq, mul_comm (w n)]
    exact div_mul_cancel₀ _ (hw n)
  rw [h1]
  ring

/-- `h^w(x) >= 1` for `1/2 <= w <= 1`  ("By (hrec), we have h^w(x) >= 1"). -/
theorem one_le_hfix (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) :
    ∀ n, 1 ≤ hfix w n
  | 0 => by
      rw [hfix_eq, hprev_zero, le_div_iff₀ (hw 0)]
      have h0 := hw1 0
      nlinarith
  | (n + 1) => by
      have ih := one_le_hfix w hw hw1 n
      rw [hfix_eq, hprev_succ, le_div_iff₀ (hw (n + 1))]
      have h1 := hw1 (n + 1)
      nlinarith

/-- One step of the comparison `w <= w' => h^{w'} <= h^{w}`. -/
lemma step_mono {w w' h : ℝ} (hw : 0 < w) (hww' : w ≤ w') (hh : 1 ≤ h) :
    (1 + (1 - w') * h) / w' ≤ (1 + (1 - w) * h) / w := by
  have hw' : 0 < w' := lt_of_lt_of_le hw hww'
  rw [← sub_nonneg]
  have key : (1 + (1 - w) * h) / w - (1 + (1 - w') * h) / w'
      = ((w' - w) * (1 + h)) / (w * w') := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · nlinarith
  · positivity

/-- The map `h |-> (1 + (1-w) h)/w` is nondecreasing for `0 < w <= 1`. -/
lemma step_mono_h {w h h' : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hh : h ≤ h') :
    (1 + (1 - w) * h) / w ≤ (1 + (1 - w) * h') / w := by
  rw [← sub_nonneg]
  have key : (1 + (1 - w) * h') / w - (1 + (1 - w) * h) / w = (1 - w) * (h' - h) / w := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · nlinarith
  · linarith

/-- **Comparison of potentials**: `w <= w'` pointwise implies `h^{w'} <= h^{w}`. -/
theorem hfix_mono (w w' : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hpos : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) :
    ∀ n, hfix w' n ≤ hfix w n
  | 0 => by
      rw [hfix_eq, hfix_eq, hprev_zero, hprev_zero]
      exact step_mono (hw 0) (hle 0) le_rfl
  | (n + 1) => by
      have ih := hfix_mono w w' hw hw1 hpos hw1' hle n
      have h1 := one_le_hfix w hw hw1 n
      rw [hfix_eq, hfix_eq, hprev_succ, hprev_succ]
      calc (1 + (1 - w' (n + 1)) * hfix w' n) / w' (n + 1)
          ≤ (1 + (1 - w' (n + 1)) * hfix w n) / w' (n + 1) :=
            step_mono_h (hpos (n + 1)) (hw1' (n + 1)) ih
        _ ≤ (1 + (1 - w (n + 1)) * hfix w n) / w (n + 1) :=
            step_mono (hw (n + 1)) (hle (n + 1)) h1

/-- The potential `H^w(x) = sum_{u<x} h^w(u)`  (eq. (Hdef), on `x >= 0`). -/
noncomputable def Hfix (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ u ∈ range n, hfix w u

lemma Hfix_succ (w : ℕ → ℝ) (n : ℕ) : Hfix w (n + 1) = Hfix w n + hfix w n := by
  simp [Hfix, sum_range_succ]

lemma Hfix_mono (w w' : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hpos : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) (n : ℕ) :
    Hfix w' n ≤ Hfix w n := by
  refine sum_le_sum fun u _ => ?_
  exact hfix_mono w w' hw hw1 hpos hw1' hle u

/-- **(hmono)**: `H^w - H^{w'}` is nonnegative and nondecreasing in `x`. -/
theorem Hfix_diff_monotone (w w' : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hpos : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) :
    Monotone fun n => Hfix w n - Hfix w' n := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Hfix_succ, Hfix_succ]
  have h := hfix_mono w w' hw hw1 hpos hw1' hle n
  linarith

/-- `H^w(x) >= x`: used for (Wpos) in the proof of Proposition (group) and for the
lower comparison `H^w(x) >= x` inside the proof of (spav). -/
theorem Hfix_ge (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) (n : ℕ) :
    (n : ℝ) ≤ Hfix w n := by
  induction n with
  | zero => simp [Hfix]
  | succ k ih =>
      rw [Hfix_succ]
      have h := one_le_hfix w hw hw1 k
      push_cast
      linarith

/-- The drift identity used in the proof of Proposition (group) and in (Zdrift):
for a `±1` increment with right probability `alpha`,
`alpha h(x) - (1-alpha) h(x-1) = 1 + (alpha - w(x)) (h(x) + h(x-1))`. -/
theorem drift_identity (w : ℕ → ℝ) (hw : ∀ n, w n ≠ 0) (n : ℕ) (alpha : ℝ) :
    alpha * hfix w n - (1 - alpha) * hprev w n
      = 1 + (alpha - w n) * (hfix w n + hprev w n) := by
  have h' := unit w hw n
  have key : alpha * hfix w n - (1 - alpha) * hprev w n
      = (1 + (alpha - w n) * (hfix w n + hprev w n))
        + (w n * hfix w n - (1 - w n) * hprev w n) - 1 := by ring
  rw [key, h']
  ring

/-- Closed form of the affine recursion (eq. (projh)). -/
theorem geom_closed (c a : ℝ) (ha : a ≠ 1) (y : ℕ → ℝ) (hy : ∀ n, y (n + 1) = c + a * y n) :
    ∀ n, y n = c / (1 - a) + a ^ n * (y 0 - c / (1 - a)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [hy, ih, pow_succ]
      field_simp
      ring

/-- Closed form of the partial sums (eq. (projH)). -/
theorem geom_partial_sum (c a : ℝ) (ha : a ≠ 1) (y : ℕ → ℝ) (hy : ∀ n, y (n + 1) = c + a * y n)
    (g : ℕ) :
    ∑ k ∈ range g, y k
      = g * (c / (1 - a)) + (y 0 - c / (1 - a)) * ((1 - a ^ g) / (1 - a)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction g with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih, geom_closed c a ha y hy k, pow_succ]
      field_simp
      push_cast
      ring

end Cookie

-- machine check of what the kernel actually used


namespace Swarming

open Finset

/-- Capping every summand at `m` does not change whether a sum reaches `m`.
This is the finite-index form of the local-time truncation used in the record-state Markov chain. -/
theorem capped_sum_ge_iff {ι : Type*} [Fintype ι] (m : ℕ) (a : ι → ℕ) :
    m ≤ ∑ i, a i ↔ m ≤ ∑ i, min (a i) m := by
  classical
  constructor <;> intro h
  · by_cases hex : ∃ i, m ≤ a i
    · obtain ⟨i, hi⟩ := hex
      have hcap : m ≤ min (a i) m := le_min hi le_rfl
      exact hcap.trans (single_le_sum (f := fun j => min (a j) m) (fun j _ => Nat.zero_le _) (mem_univ i))
    · simp only [not_exists, not_le] at hex
      have heq : ∀ i, min (a i) m = a i := fun i => min_eq_left (Nat.le_of_lt (hex i))
      simpa [heq] using h
  · by_cases hex : ∃ i, m ≤ a i
    · obtain ⟨i, hi⟩ := hex
      exact hi.trans (single_le_sum (fun j _ => Nat.zero_le (a j)) (mem_univ i))
    · simp only [not_exists, not_le] at hex
      have heq : ∀ i, min (a i) m = a i := fun i => min_eq_left (Nat.le_of_lt (hex i))
      simpa [heq] using h

/-- The unbiased jump driven by the same uniform variable. -/
noncomputable def symmetricStep (u : ℝ) : ℤ := if 2 * u ≤ 1 then 1 else -1

/-- The driven jump with right probability `α`. -/
noncomputable def drivenStep (u α : ℝ) : ℤ := if u ≤ α then 1 else -1

/-- On one common driving uniform, the driven jump is always at least the unbiased jump. -/
theorem symmetricStep_le_drivenStep {u α : ℝ} (hα : 1 / 2 ≤ α) :
    symmetricStep u ≤ drivenStep u α := by
  by_cases hu : 2 * u ≤ 1
  · have hua : u ≤ α := by linarith
    simp [symmetricStep, drivenStep, hu, hua]
  · by_cases hua : u ≤ α
    · simp [symmetricStep, drivenStep, hu, hua]
    · simp [symmetricStep, drivenStep, hu, hua]

end Swarming


namespace Swarming.Update

open Finset
open Cookie

/-- The backward ratio appearing in the Poisson-update product. -/
noncomputable def ratio (w : ℕ → ℝ) (n : ℕ) : ℝ := (1 - w n) / w n

variable (w w' : ℕ → ℝ) (k : ℕ)
lemma hfix_congr_before (hne : ∀ n, n ≠ k → w' n = w n) {n : ℕ} (hn : n < k) : hfix w' n = hfix w n := by
  induction n with
  | zero =>
      have h0 : 0 ≠ k := Nat.ne_of_lt hn
      simp [hfix_eq, hprev, hne 0 h0]
  | succ n ih =>
      have hnk : n < k := (Nat.lt_succ_self n).trans hn
      have hs : n + 1 ≠ k := Nat.ne_of_lt hn
      rw [hfix_eq, hfix_eq, hprev_succ, hprev_succ, hne (n + 1) hs, ih hnk]

lemma hprev_congr_before (hne : ∀ n, n ≠ k → w' n = w n) {n : ℕ} (hn : n ≤ k) : hprev w' n = hprev w n := by
  cases n with
  | zero => simp
  | succ n =>
      have hnk : n < k := Nat.succ_le_iff.mp hn
      rw [hprev_succ, hprev_succ, hfix_congr_before w w' k hne hnk]

lemma hfix_single_site (hne : ∀ n, n ≠ k → w' n = w n) (p : ℝ) (hp : p ≠ 0) (hwk : w k = 1 / 2) (hw'k : w' k = p) :
    hfix w k - hfix w' k = (2 * p - 1) / p * (1 + hprev w k) := by
  rw [hfix_eq, hfix_eq, hprev_congr_before w w' k hne le_rfl, hwk, hw'k]
  field_simp
  ring

lemma hfix_single_site_after (hne : ∀ n, n ≠ k → w' n = w n) (p : ℝ) (hp : p ≠ 0)
    (hwk : w k = 1 / 2) (hw'k : w' k = p) {n : ℕ} (hn : k ≤ n) :
    hfix w n - hfix w' n =
      ((2 * p - 1) / p * (1 + hprev w k)) *
        ∏ u ∈ Ico (k + 1) (n + 1), ratio w u := by
  induction n, hn using Nat.le_induction with
  | base => simpa using hfix_single_site w w' k hne p hp hwk hw'k
  | succ n hn ih =>
      have hnext : n + 1 ≠ k := Nat.ne_of_gt (Nat.lt_succ_of_le hn)
      calc
        hfix w (n + 1) - hfix w' (n + 1) =
            ratio w (n + 1) * (hfix w n - hfix w' n) := by
              rw [hfix_eq, hfix_eq, hprev_succ, hprev_succ, hne (n + 1) hnext]
              dsimp [ratio]
              ring
        _ = ((2 * p - 1) / p * (1 + hprev w k)) *
              (∏ u ∈ Ico (k + 1) (n + 1), ratio w u) * ratio w (n + 1) := by rw [ih]; ring
        _ = ((2 * p - 1) / p * (1 + hprev w k)) *
              ∏ u ∈ Ico (k + 1) (n + 2), ratio w u := by
                rw [prod_Ico_succ_top (Nat.add_le_add_right hn 1)]
                ring

/-- The single-site update equation `upd` from the paper, expressed with finite products. -/
theorem Hfix_single_site (hne : ∀ n, n ≠ k → w' n = w n) (p : ℝ) (hp : p ≠ 0)
    (hwk : w k = 1 / 2) (hw'k : w' k = p) {n : ℕ} (hn : k ≤ n) :
    Hfix w n - Hfix w' n =
      ((2 * p - 1) / p * (1 + hprev w k)) *
        ∑ z ∈ Ico k n, ∏ u ∈ Ico (k + 1) (z + 1), ratio w u := by
  induction n, hn using Nat.le_induction with
  | base =>
      have heq : Hfix w k = Hfix w' k := by
        apply sum_congr rfl
        intro u hu
        exact (hfix_congr_before w w' k hne (mem_range.mp hu)).symm
      simp [heq]
  | succ n hn ih =>
      calc
        Hfix w (n + 1) - Hfix w' (n + 1) =
            (Hfix w n - Hfix w' n) + (hfix w n - hfix w' n) := by
              rw [Hfix_succ, Hfix_succ]
              ring
        _ = ((2 * p - 1) / p * (1 + hprev w k)) *
              (∑ z ∈ Ico k n, ∏ u ∈ Ico (k + 1) (z + 1), ratio w u) +
            ((2 * p - 1) / p * (1 + hprev w k)) *
              (∏ u ∈ Ico (k + 1) (n + 1), ratio w u) := by
                rw [ih, hfix_single_site_after w w' k hne p hp hwk hw'k hn]
        _ = ((2 * p - 1) / p * (1 + hprev w k)) *
              ∑ z ∈ Ico k (n + 1), ∏ u ∈ Ico (k + 1) (z + 1), ratio w u := by
                rw [sum_Ico_succ_top hn]
                ring

/-- Before the updated site, the two potentials agree. -/
theorem Hfix_single_site_before (hne : ∀ n, n ≠ k → w' n = w n) {n : ℕ} (hn : n ≤ k) :
    Hfix w n = Hfix w' n := by
  apply sum_congr rfl
  intro u hu
  exact (hfix_congr_before w w' k hne ((mem_range.mp hu).trans_le hn)).symm

end Swarming.Update


namespace Swarming.Constants

open Cookie

/-- The interval estimate used in `Wpos`: potential increments dominate spatial increments. -/
theorem Hfix_sub_ge (w : ℕ → ℝ) (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    {x y : ℕ} (hxy : x ≤ y) :
    (y - x : ℝ) ≤ Hfix w y - Hfix w x := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
      rw [Hfix_succ]
      have hy := one_le_hfix w hw0 hw1 y
      push_cast
      linarith

/-- The pointwise two-sided bound used at a running record. -/
theorem hfix_le_hprev_add_two (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) (hwHalf : ∀ n, 1 / 2 ≤ w n) (n : ℕ) :
    hfix w n ≤ hprev w n + 2 := by
  have hprev_ge : 1 ≤ hprev w n := by
    cases n with
    | zero => simp
    | succ k =>
        rw [hprev_succ]
        exact one_le_hfix w hw0 hw1 k
  rw [hfix_eq, div_le_iff₀ (hw0 n)]
  have hw2 : 0 ≤ 2 * w n - 1 := by linarith [hwHalf n]
  have hh : 0 ≤ hprev w n + 1 := by linarith
  have hprod : 0 ≤ (2 * w n - 1) * (hprev w n + 1) := mul_nonneg hw2 hh
  nlinarith

/-- The expected ratio parameter of the two-valued mark environment. -/
noncomputable def ratioMean (p q : ℝ) : ℝ := (1 - q) + q * (1 - p) / p

/-- The expected inverse right probability of the two-valued mark environment. -/
noncomputable def inverseMean (p q : ℝ) : ℝ := 2 * (1 - q) + q / p

/-- A compact name for the paper's constant `a`. -/
noncomputable def a (p q : ℝ) : ℝ := 1 - (2 * p - 1) * q / p

theorem ratioMean_eq_a (p q : ℝ) (hp : p ≠ 0) : ratioMean p q = a p q := by
  dsimp [ratioMean, a]
  field_simp
  ring

theorem inverseMean_eq_one_add_a (p q : ℝ) (hp : p ≠ 0) :
    inverseMean p q = 1 + a p q := by
  dsimp [inverseMean, a]
  field_simp
  ring

end Swarming.Constants


namespace Swarming.Group

open Finset

noncomputable def average {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / s.card

noncomputable def maximumOn {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ℝ :=
  s.sup' hs f

variable {ι : Type*} {s t : Finset ι} {x : ι → ℤ} {H D : ℤ → ℝ}

lemma maximum_old_le_maximum_new_add_maximum_difference
    (ht : t.Nonempty) :
    maximumOn t ht (fun j => H (x j)) ≤
      maximumOn t ht (fun j => H (x j) - D (x j)) + maximumOn t ht (fun j => D (x j)) := by
  refine sup'_le ht (fun j => H (x j)) ?_
  intro j hj
  have hnew : H (x j) - D (x j) ≤ maximumOn t ht (fun y => H (x y) - D (x y)) :=
    le_sup' (fun y => H (x y) - D (x y)) hj
  have hdiff : D (x j) ≤ maximumOn t ht (fun y => D (x y)) :=
    le_sup' (fun y => D (x y)) hj
  dsimp [maximumOn] at *
  linarith

lemma maximum_difference_le_average (hd : Monotone D)
    (hsep : ∀ i ∈ s, ∀ j ∈ t, x j ≤ x i) (hs : s.Nonempty) (ht : t.Nonempty) :
    maximumOn t ht (fun j => D (x j)) ≤ average s (fun i => D (x i)) := by
  have hpoint : ∀ i ∈ s, maximumOn t ht (fun j => D (x j)) ≤ D (x i) := by
    intro i hi
    refine sup'_le ht (fun j => D (x j)) ?_
    intro j hj
    exact hd (hsep i hi j hj)
  have hsumNat : s.card • maximumOn t ht (fun j => D (x j)) ≤
      ∑ i ∈ s, D (x i) :=
    card_nsmul_le_sum s (fun i => D (x i)) (maximumOn t ht (fun j => D (x j))) hpoint
  have hsum : (s.card : ℝ) * maximumOn t ht (fun j => D (x j)) ≤
      ∑ i ∈ s, D (x i) := by simpa [nsmul_eq_mul] using hsumNat
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Nat.cast_pos.mpr (card_pos.mpr hs))
  change maximumOn t ht (fun j => D (x j)) ≤ (∑ i ∈ s, D (x i)) / s.card
  exact (le_div_iff₀ hcard).2 (by nlinarith)

/-- The finite-maximum/average inequality behind the separated-group comparison in the paper. -/
theorem updated_average_le_original_average (hd : Monotone D)
    (hsep : ∀ i ∈ s, ∀ j ∈ t, x j ≤ x i) (hs : s.Nonempty) (ht : t.Nonempty) :
    average s (fun i => H (x i) - D (x i)) - maximumOn t ht (fun j => H (x j) - D (x j)) ≤
      average s (fun i => H (x i)) - maximumOn t ht (fun j => H (x j)) := by
  have hmax := maximum_old_le_maximum_new_add_maximum_difference (H := H) (D := D)
    (x := x) ht
  have havg := maximum_difference_le_average (x := x) hd hsep hs ht
  have hsum : average s (fun i => H (x i) - D (x i)) =
      average s (fun i => H (x i)) - average s (fun i => D (x i)) := by
    dsimp [average]
    rw [sum_sub_distrib]
    ring
  rw [hsum]
  dsimp [maximumOn] at *
  linarith

end Swarming.Group


namespace Swarming.Model

open Finset

/-- Visit counts for finitely many walkers on the integer lattice. -/
abbrev LocalTimes (N : ℕ) := Fin N → ℤ → ℕ

/-- Total previous visits to `x` by walkers other than `i`. -/
def otherVisits {N : ℕ} (ell : LocalTimes N) (i : Fin N) (x : ℤ) : ℕ :=
  ∑ j, if j = i then 0 else ell j x

/-- Excitation at `x` for walker `i` under threshold `m`. -/
def Excited {N : ℕ} (m : ℕ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) : Prop :=
  m ≤ otherVisits ell i x

/-- Probability of a right jump for one walker at the current local-time configuration. -/
noncomputable def rightProbability {N : ℕ} (p : ℝ) (m : ℕ) (ell : LocalTimes N)
    (i : Fin N) (x : ℤ) : ℝ := by
  classical
  exact if Excited m ell i x then p else 1 / 2

/-- Capping every walker's local time at `m` leaves every excitation indicator unchanged. -/
theorem excited_capped_iff {N : ℕ} (m : ℕ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) :
    Excited m ell i x ↔ Excited m (fun j y => min (ell j y) m) i x := by
  change m ≤ (∑ j, if j = i then 0 else ell j x) ↔
    m ≤ ∑ j, if j = i then 0 else min (ell j x) m
  rw [Swarming.capped_sum_ge_iff]
  have heq : (∑ j, min (if j = i then 0 else ell j x) m) =
      ∑ j, if j = i then 0 else min (ell j x) m := by
    apply sum_congr rfl
    intro j hj
    by_cases hji : j = i <;> simp [hji]
  rw [heq]

theorem otherVisits_mono {N : ℕ} {ell ell' : LocalTimes N}
    (h : ∀ j x, ell j x ≤ ell' j x) (i : Fin N) (x : ℤ) :
    otherVisits ell i x ≤ otherVisits ell' i x := by
  apply sum_le_sum
  intro j hj
  by_cases hji : j = i <;> simp [hji, h j x]

theorem excited_mono {N : ℕ} {m : ℕ} {ell ell' : LocalTimes N}
    (h : ∀ j x, ell j x ≤ ell' j x) {i : Fin N} {x : ℤ} :
    Excited m ell i x → Excited m ell' i x := by
  intro hi
  exact (otherVisits_mono h i x).trans' hi

theorem one_half_le_rightProbability {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p)
    (m : ℕ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) :
    1 / 2 ≤ rightProbability p m ell i x := by
  by_cases hi : Excited m ell i x
  · simp only [rightProbability, hi, if_true]
    nlinarith
  · simp [rightProbability, hi]

theorem rightProbability_le_p {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p)
    (m : ℕ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) :
    rightProbability p m ell i x ≤ p := by
  by_cases hi : Excited m ell i x
  · simp [rightProbability, hi]
  · simp only [rightProbability, hi, if_false]
    nlinarith

theorem symmetricStep_le_model_step {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p)
    (m : ℕ) (ell : LocalTimes N) (i : Fin N) (x : ℤ) (u : ℝ) :
    symmetricStep u ≤ drivenStep u (rightProbability p m ell i x) :=
  symmetricStep_le_drivenStep (one_half_le_rightProbability hp m ell i x)

end Swarming.Model


namespace Swarming.Paths

open Finset

/-- Number of visits to `x` among the times `0, ..., n`. -/
def localTime (gamma : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  ((range (n + 1)).filter (fun k => gamma k = x)).card

/-- Index of the copied visit in the shared-endpoint path construction. -/
def copyTime (t s : ℕ) : ℕ := if s = 0 then t + 1 else t + 1 + s

/-- The uphill segment followed by the translated finite path `gamma`. -/
noncomputable def prescribed (gamma : ℕ → ℤ) (t n : ℕ) : ℤ :=
  if n ≤ t + 1 then (n : ℤ) else (t + 1 : ℤ) + gamma (n - (t + 1))

lemma copyTime_injective (t : ℕ) : Function.Injective (copyTime t) := by
  intro a b hab
  simp only [copyTime] at hab
  split_ifs at hab with ha hb hbc <;> omega

lemma prescribed_copy (gamma : ℕ → ℤ) (hgamma : gamma 0 = 0)
    {t s : ℕ} (hs : s ≤ t) :
    prescribed gamma t (copyTime t s) = (t + 1 : ℤ) + gamma s := by
  by_cases hs0 : s = 0
  · subst s
    simp [copyTime, prescribed, hgamma]
  · have hle : ¬t + 1 + s ≤ t + 1 := by omega
    simp [copyTime, prescribed, hs0, hle]

lemma prescribed_final (gamma : ℕ → ℤ) (hgamma : gamma 0 = 0) (t : ℕ) :
    prescribed gamma t (2 * t + 1) = (t + 1 : ℤ) + gamma t := by
  have hb : 2 * t + 1 = copyTime t t := by
    simp only [copyTime]
    split_ifs with ht
    · subst t
      rfl
    · omega
  rw [hb, prescribed_copy gamma hgamma le_rfl]

/-- The shared-endpoint local-time identity, with no double count at `s = 0`. -/
theorem localTime_prescribed (gamma : ℕ → ℤ) (hgamma : gamma 0 = 0)
    {t : ℕ} {x : ℤ} (hx : 0 ≤ x) :
    localTime gamma t x = localTime (prescribed gamma t) (2 * t + 1) ((t + 1 : ℤ) + x) := by
  unfold localTime
  apply card_bij (fun s _ => copyTime t s)
  · intro s hs
    rcases mem_filter.mp hs with ⟨hsrange, hsvisit⟩
    apply mem_filter.mpr
    have hst : s ≤ t := Nat.le_of_lt_succ (mem_range.mp hsrange)
    constructor
    · apply mem_range.mpr
      simp only [copyTime]
      split_ifs with hs0 <;> omega
    · rw [prescribed_copy gamma hgamma hst, hsvisit]
  · intro a ha b hb hab
    exact copyTime_injective t hab
  · intro b hb
    rcases mem_filter.mp hb with ⟨hbrange, hbvisit⟩
    have hbt : b ≤ 2 * t + 1 := by
      have : b < 2 * t + 2 := mem_range.mp hbrange
      omega
    by_cases hlow : b ≤ t + 1
    · have hx0 : x = 0 := by
        simp only [prescribed, hlow, if_true] at hbvisit
        omega
      have hb0 : b = t + 1 := by
        simp only [prescribed, hlow, if_true] at hbvisit
        omega
      refine ⟨0, ?_, ?_⟩
      · apply mem_filter.mpr
        exact ⟨mem_range.mpr (Nat.zero_lt_succ t), by simp [hgamma, hx0]⟩
      · simp [copyTime, hb0]
    · let s := b - (t + 1)
      have hspos : 0 < s := by
        dsimp [s]
        omega
      have hst : s ≤ t := by
        dsimp [s]
        omega
      have hs0 : s ≠ 0 := Nat.ne_of_gt hspos
      have hbdef : b = copyTime t s := by
        simp [copyTime, hs0]
        dsimp [s]
        omega
      refine ⟨s, ?_, ?_⟩
      · apply mem_filter.mpr
        have hsvisit : gamma s = x := by
          rw [hbdef, prescribed_copy gamma hgamma hst] at hbvisit
          exact add_left_cancel hbvisit
        exact ⟨mem_range.mpr (Nat.lt_succ_of_le hst), hsvisit⟩
      · exact hbdef.symm

end Swarming.Paths


