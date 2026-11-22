import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Swarm.MarkMoments

open Finset SwarmMarks

set_option autoImplicit false

namespace Swarming.Diameter

private theorem affine_pow_le {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    (a * x + b * y) ^ k ≤ a * x ^ k + b * y ^ k := by
  simpa only [smul_eq_mul] using
    (convexOn_pow (𝕜 := ℝ) k).2 (x := x) (y := y) hx hy ha hb hab

/-- The sum of powers along a nonnegative sequence with an affine upper
recurrence is bounded by the initial power and the sum of the forcing powers. -/
private theorem sum_pow_le_of_affine_recurrence {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h ℓ : ℕ → ℝ) (n : ℕ), (∀ j, 0 ≤ h j) → (∀ j, 0 ≤ ℓ j) →
        (∀ j < n, h (j + 1) ≤ ρ * h j + 2 * ℓ j) →
        (∑ j ∈ range n, h j ^ k) ≤ C * (h 0 ^ k + ∑ j ∈ range n, ℓ j ^ k) := by
  let a := (1 + ρ) / 2
  let b := 1 - a
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [a, b]; linarith
  have hρa : ρ ≤ a := by dsimp [a]; linarith
  let K := max 1 (b * (2 / b) ^ k)
  have hK : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  refine ⟨K / b, div_nonneg hK hb.le, ?_⟩
  intro h ℓ n hh hℓ hrec
  have hstep (j : ℕ) (hj : j ∈ range n) :
      h (j + 1) ^ k ≤ a * h j ^ k + (b * (2 / b) ^ k) * ℓ j ^ k := by
    have he : b * ((2 / b) * ℓ j) = 2 * ℓ j := by field_simp
    have hxy : h (j + 1) ≤ a * h j + b * ((2 / b) * ℓ j) := by
      rw [he]
      exact (hrec j (mem_range.mp hj)).trans
        (add_le_add (mul_le_mul_of_nonneg_right hρa (hh j)) le_rfl)
    calc
      _ ≤ (a * h j + b * ((2 / b) * ℓ j)) ^ k := pow_le_pow_left₀ (hh _) hxy _
      _ ≤ a * h j ^ k + b * ((2 / b) * ℓ j) ^ k :=
        affine_pow_le ha hb.le (by dsimp [b]; ring) (hh _) (mul_nonneg (by positivity) (hℓ j)) k
      _ = _ := by rw [mul_pow, ← mul_assoc]
  have hsum := sum_le_sum hstep
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have htel : (∑ j ∈ range n, h (j + 1) ^ k) + h 0 ^ k =
      (∑ j ∈ range n, h j ^ k) + h n ^ k := by
    calc
      _ = ∑ j ∈ range (n + 1), h j ^ k := (sum_range_succ' (fun j => h j ^ k) n).symm
      _ = _ := sum_range_succ (fun j => h j ^ k) n
  have hp : 0 ≤ h n ^ k := pow_nonneg (hh n) _
  have hmain : b * (∑ j ∈ range n, h j ^ k) ≤ h 0 ^ k +
      (b * (2 / b) ^ k) * (∑ j ∈ range n, ℓ j ^ k) := by
    dsimp only [b] at ⊢
    linarith
  have hle : h 0 ^ k + (b * (2 / b) ^ k) * (∑ j ∈ range n, ℓ j ^ k) ≤
      K * (h 0 ^ k + ∑ j ∈ range n, ℓ j ^ k) := by
    rw [mul_add]
    have hzero : h 0 ^ k ≤ K * h 0 ^ k := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show 1 ≤ K from le_max_left _ _) (pow_nonneg (hh 0) k)
    exact add_le_add hzero
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sum_nonneg fun j _ => pow_nonneg (hℓ j) _))
  rw [div_mul_eq_mul_div, le_div_iff₀ hb, mul_comm]
  exact hmain.trans hle

/-- For intervals between marked sites, bound the sum of the contributions
`ℓ j * (h j + 2 * ℓ j)^q` by the initial potential and the gap lengths to power
`q + 1`. The potential at the next marked site satisfies the affine recurrence. -/
theorem sum_gap_mul_pow_le {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h ℓ : ℕ → ℝ) (n : ℕ), (∀ j, 0 ≤ h j) → (∀ j, 0 ≤ ℓ j) →
        (∀ j < n, h (j + 1) ≤ ρ * h j + 2 * ℓ j) →
        (∑ j ∈ range n, ℓ j * (h j + 2 * ℓ j) ^ q) ≤
          C * (h 0 ^ (q + 1) + ∑ j ∈ range n, ℓ j ^ (q + 1)) := by
  obtain ⟨K, hK, hsum⟩ := sum_pow_le_of_affine_recurrence hρ₀ hρ₁ (q + 1)
  let c : ℝ := 2 ^ (q + 1)
  have hcpos : 0 < c := pow_pos (by norm_num) _
  refine ⟨c * (K + c), mul_pos hcpos (add_pos_of_nonneg_of_pos hK hcpos), ?_⟩
  intro h ℓ n hh hℓ hrec
  have hs := hsum h ℓ n hh hℓ hrec
  have hcost (j : ℕ) (hj : j ∈ range n) :
      ℓ j * (h j + 2 * ℓ j) ^ q ≤ c * (h j ^ (q + 1) + c * ℓ j ^ (q + 1)) := by
    let x := h j
    let y := 2 * ℓ j
    have hx : 0 ≤ x := hh j
    have hy : 0 ≤ y := by exact mul_nonneg (by norm_num) (hℓ j)
    have hℓ' : ℓ j ≤ x + y := by dsimp [y]; linarith [hℓ j]
    have he : 2 * ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) = x + y := by ring
    calc
      _ ≤ (x + y) ^ (q + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right hℓ' (pow_nonneg (add_nonneg hx hy) _)
      _ ≤ c * (x ^ (q + 1) + y ^ (q + 1)) := by
        rw [← he, mul_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (affine_pow_le (by norm_num) (by norm_num) (by norm_num) hx hy (q + 1)).trans
          (by nlinarith [pow_nonneg hx (q + 1), pow_nonneg hy (q + 1)])
      _ = _ := by rw [show y ^ (q + 1) = c * ℓ j ^ (q + 1) by exact mul_pow _ _ _]
  have hc := sum_le_sum hcost
  rw [← mul_sum, sum_add_distrib, ← mul_sum] at hc
  refine hc.trans ?_
  rw [mul_assoc c (K + c)]
  apply mul_le_mul_of_nonneg_left _ hcpos.le
  rw [add_mul]
  exact add_le_add hs (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (pow_nonneg (hh 0) _)) hcpos.le)

/-- The potential just before the site indexed by `s`. At site zero this is
the prescribed initial value one. -/
private noncomputable def beforeSite (p : ℝ) (ω : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | s + 1 => hof p ω s

private theorem beforeSite_succ (p : ℝ) (ω : ℕ → Bool) (s : ℕ) :
    beforeSite p ω (s + 1) = hstep p (ω s) (beforeSite p ω s) := by
  cases s <;> rfl

private theorem one_le_beforeSite {p : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1)
    (ω : ℕ → Bool) (s : ℕ) : 1 ≤ beforeSite p ω s := by
  cases s with
  | zero => exact le_rfl
  | succ s => exact one_le_hof hp₀ hp₁ ω s

private theorem beforeSite_add_le {p : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1)
    (ω : ℕ → Bool) (s k : ℕ) :
    beforeSite p ω (s + k) ≤ beforeSite p ω s + 2 * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, beforeSite_succ, Nat.cast_succ]
    have h := hstep_le_add_two hp₀ hp₁ (one_le_beforeSite hp₀ hp₁ ω (s + k))
      (b := ω (s + k))
    linarith

private theorem sum_Ico_eq_sum_intervals {f : ℕ → ℝ} {s : ℕ → ℕ} {n : ℕ}
    (h : ∀ j < n, s j ≤ s (j + 1)) :
    (∑ x ∈ Ico (s 0) (s n), f x) =
      ∑ j ∈ range n, ∑ x ∈ Ico (s j) (s (j + 1)), f x := by
  have h₀ (j : ℕ) (hj : j ≤ n) : s 0 ≤ s j := by
    induction j with
    | zero => rfl
    | succ j ih => exact (ih (by omega)).trans (h j (by omega))
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih (fun j hj => h j (by omega)) (fun j hj => h₀ j (by omega))]
    exact (sum_Ico_consecutive _ (h₀ n (Nat.le_succ n)) (h n (Nat.lt_succ_self n))).symm

/-- A spatial sum of powers of the potential is bounded by the initial
potential and the marked-site gaps to power `q + 1`. The indices `s j`
start at the left endpoint, and each interval ends at a marked site
`s (j + 1) - 1`. The proof also applies when an interval contains other marks. -/
theorem sum_hof_pow_le_marked_gaps {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ω : ℕ → Bool) (s : ℕ → ℕ) (L : ℕ),
        (∀ j < L, s j < s (j + 1)) →
        (∀ j < L, ω (s (j + 1) - 1) = true) →
        (∑ x ∈ Ico (s 0) (s 0 + L), hof p ω x ^ q) ≤
          C * ((if s 0 = 0 then 1 else hof p ω (s 0 - 1)) ^ (q + 1) +
            ∑ j ∈ range L, ((s (j + 1) - s j : ℕ) : ℝ) ^ (q + 1)) := by
  obtain ⟨C, hC, hb⟩ := sum_gap_mul_pow_le (rho_nonneg hp₀ hp₁) (rho_lt_one hp₀ hp₁) q
  refine ⟨C, hC, ?_⟩
  intro ω s L hs hmark
  let h (j : ℕ) := beforeSite p ω (s j)
  let ℓ (j : ℕ) := ((s (j + 1) - s j : ℕ) : ℝ)
  have hh (j : ℕ) : 0 ≤ h j := zero_le_one.trans (one_le_beforeSite hp₀.le hp₁ ω _)
  have hℓ (j : ℕ) : 0 ≤ ℓ j := Nat.cast_nonneg _
  have hrec (j : ℕ) (hj : j < L) :
      h (j + 1) ≤ (1 - p) / p * h j + 2 * ℓ j := by
    have hlt := hs j hj
    let k := s (j + 1) - 1 - s j
    have hend : s j + k + 1 = s (j + 1) := by dsimp [k]; omega
    have hindex : s j + k = s (j + 1) - 1 := by omega
    have hle := beforeSite_add_le hp₀.le hp₁ ω (s j) k
    have hmark' : ω (s j + k) = true := hindex ▸ hmark j hj
    have hρ0 := rho_nonneg hp₀ hp₁
    have hρ1 := (rho_lt_one hp₀ hp₁).le
    have hk : (k : ℝ) + 1 = ℓ j := by
      dsimp only [ℓ]
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact_mod_cast (show k + 1 = s (j + 1) - s j by omega)
    change beforeSite p ω (s (j + 1)) ≤ _
    rw [← hend, beforeSite_succ, hmark', hstep_true]
    have hd := one_div_p_le_three hp₀.le
    have hmul := mul_le_mul_of_nonneg_left hle hρ0
    have hmul' := mul_le_mul_of_nonneg_right hρ1 (show 0 ≤ 2 * (k : ℝ) by positivity)
    change _ ≤ (1 - p) / p * beforeSite p ω (s j) + 2 * ℓ j
    linarith
  have hcover : s 0 + L ≤ s L := by
    have hm (j : ℕ) (hj : j ≤ L) : s 0 + j ≤ s j := by
      induction j with
      | zero => simp
      | succ j ih => have h := ih (by omega : j ≤ L); have ht := hs j (by omega); omega
    exact hm L le_rfl
  have hstart : h 0 = if s 0 = 0 then 1 else hof p ω (s 0 - 1) := by
    dsimp only [h]
    cases s 0 <;> simp [beforeSite]
  rw [← hstart]
  calc
    _ ≤ ∑ x ∈ Ico (s 0) (s L), hof p ω x ^ q := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨ha, hb⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨ha, hb.trans_le hcover⟩
      · intro x _ _
        exact pow_nonneg (zero_le_one.trans (one_le_hof hp₀.le hp₁ ω x)) _
    _ = ∑ j ∈ range L, ∑ x ∈ Ico (s j) (s (j + 1)), hof p ω x ^ q :=
      sum_Ico_eq_sum_intervals (fun j hj => (hs j hj).le)
    _ ≤ ∑ j ∈ range L, ℓ j * (h j + 2 * ℓ j) ^ q := by
      apply sum_le_sum
      intro j hj
      have hsite (x : ℕ) (hx : x ∈ Ico (s j) (s (j + 1))) :
          hof p ω x ^ q ≤ (h j + 2 * ℓ j) ^ q := by
        obtain ⟨hsx, hxe⟩ := mem_Ico.mp hx
        have hbound := beforeSite_add_le hp₀.le hp₁ ω (s j) (x + 1 - s j)
        rw [Nat.add_sub_of_le (by omega : s j ≤ x + 1)] at hbound
        have hdist : ((x + 1 - s j : ℕ) : ℝ) ≤ ℓ j := by
          dsimp only [ℓ]
          exact_mod_cast (show x + 1 - s j ≤ s (j + 1) - s j by omega)
        apply pow_le_pow_left₀ (zero_le_one.trans (one_le_hof hp₀.le hp₁ ω x))
        change hof p ω x ≤ beforeSite p ω (s j) + 2 * ℓ j
        change hof p ω x ≤ beforeSite p ω (s j) + _ at hbound
        linarith
      calc
        _ ≤ ∑ _ ∈ Ico (s j) (s (j + 1)), (h j + 2 * ℓ j) ^ q := sum_le_sum hsite
        _ = _ := by simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, ℓ]
    _ ≤ _ := hb h ℓ L hh hℓ hrec

end Swarming.Diameter
