import Swarm.SepGroup

open Finset

namespace Swarming.Diameter

set_option autoImplicit false

/-- Slope of the bounded comparison function at site `n - 1`.
Its value at site `-1` is one. -/
noncomputable def boundedSlope (K : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => min K ((1 + (1 - w n) * boundedSlope K w n) / w n)

theorem boundedSlope_bounds {K : ℝ} (hK : 1 ≤ K) {w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (n : ℕ) :
    1 ≤ boundedSlope K w n ∧ boundedSlope K w n ≤ K := by
  induction n with
  | zero => exact ⟨le_rfl, hK⟩
  | succ n ih =>
    rw [boundedSlope]
    refine ⟨le_min hK ((le_div_iff₀ (hw n)).2 ?_), min_le_left _ _⟩
    simpa only [one_mul] using (hw₁ n).trans
      (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (hw₁ n)) (zero_le_one.trans ih.1)))

theorem boundedSlope_le_of_le_prefix {K : ℝ} (hK : 1 ≤ K) {w v : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (hv₁ : ∀ n, v n ≤ 1) (n : ℕ)
    (hle : ∀ i < n, w i ≤ v i) : boundedSlope K v n ≤ boundedSlope K w n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hwv := hle n (Nat.lt_succ_self n)
    rw [boundedSlope, boundedSlope]
    apply min_le_min le_rfl
    exact (Cookie.step_mono_h ((hw n).trans_le hwv) (hv₁ n)
      (ih (fun i hi => hle i (Nat.lt_succ_of_lt hi)))).trans
        (Cookie.step_mono (hw n) hwv (boundedSlope_bounds hK hw hw₁ n).1)

theorem boundedSlope_eq_of_eq_prefix (K : ℝ) {w v : ℕ → ℝ} (n : ℕ)
    (heq : ∀ i < n, w i = v i) : boundedSlope K w n = boundedSlope K v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boundedSlope, boundedSlope, ih (fun i hi => heq i (Nat.lt_succ_of_lt hi)),
      heq n (Nat.lt_succ_self n)]

/-- The expected increment at right-jump probability `w n` is the smaller
of one and the increment computed with the upper bound on the right slope. -/
theorem boundedSlope_increment_eq_min (K : ℝ) {w : ℕ → ℝ} {n : ℕ} (hw : 0 < w n) :
    w n * boundedSlope K w (n + 1) - (1 - w n) * boundedSlope K w n =
      min (w n * K - (1 - w n) * boundedSlope K w n) 1 := by
  let b := (1 - w n) * boundedSlope K w n
  have hdiv : w n * ((1 + b) / w n) = 1 + b := by
    rw [mul_comm, div_mul_cancel₀ _ hw.ne']
  change w n * min K ((1 + b) / w n) - b = min (w n * K - b) 1
  by_cases h : K ≤ (1 + b) / w n
  · have hn := (le_div_iff₀ hw).mp h
    rw [min_eq_left h, min_eq_left (by linarith only [hn])]
  · have hn := (div_le_iff₀ hw).mp (le_of_lt (lt_of_not_ge h))
    rw [min_eq_right (le_of_lt (lt_of_not_ge h)), hdiv, min_eq_right (by linarith only [hn])]
    ring

theorem boundedSlope_increment_bounds {K : ℝ} (hK : 1 ≤ K) {w : ℕ → ℝ}
    (hw : ∀ n, 1 / 2 ≤ w n) (hw₁ : ∀ n, w n ≤ 1) (n : ℕ) :
    0 ≤ w n * boundedSlope K w (n + 1) - (1 - w n) * boundedSlope K w n ∧
      w n * boundedSlope K w (n + 1) - (1 - w n) * boundedSlope K w n ≤ 1 := by
  have hw₀ (j : ℕ) : 0 < w j := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hw j)
  rw [boundedSlope_increment_eq_min K (hw₀ n)]
  refine ⟨le_min ?_ zero_le_one, min_le_right _ _⟩
  have h := mul_le_mul_of_nonneg_left (boundedSlope_bounds hK hw₀ hw₁ n).2
    (sub_nonneg.mpr (hw₁ n))
  have hp := mul_nonneg (show 0 ≤ 2 * w n - 1 by linarith only [hw n]) (zero_le_one.trans hK)
  nlinarith only [hp, h]

theorem boundedSlope_increment_eq_one {K : ℝ} (hK : 1 ≤ K) {w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (n : ℕ)
    (hn : 1 ≤ (2 * w n - 1) * K ∨ w n = 1 / 2 ∧ boundedSlope K w n ≤ K - 2) :
    w n * boundedSlope K w (n + 1) - (1 - w n) * boundedSlope K w n = 1 := by
  rw [boundedSlope_increment_eq_min K (hw n)]
  apply min_eq_right
  rcases hn with hn | ⟨hne, hn⟩
  · have h := mul_le_mul_of_nonneg_left (boundedSlope_bounds hK hw hw₁ n).2
      (sub_nonneg.mpr (hw₁ n))
    linarith only [h, hn]
  · rw [hne]
    linarith only [hn]

/-- A capped slope can be bounded by restarting the affine recursion a
fixed number of sites earlier with initial value `K`. -/
theorem boundedSlope_le_window {K : ℝ} (hK : 1 ≤ K) {w v : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (hv : ∀ n, 0 < v n) (hv₁ : ∀ n, v n ≤ 1)
    (a k : ℕ) (h : ∀ i < k, w (a + i) ≤ v (a + i)) :
    boundedSlope K v (a + k) ≤ Cookie.hprev (fun i => w (a + i)) k +
      (K - 1) * ∏ i ∈ Finset.range k, (1 - w (a + i)) / w (a + i) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Cookie.hprev_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    linarith only [(boundedSlope_bounds hK hv hv₁ a).2]
  | succ k ih =>
    let b := boundedSlope K v (a + k)
    let H := Cookie.hprev (fun i => w (a + i)) k
    let Q := ∏ i ∈ Finset.range k, (1 - w (a + i)) / w (a + i)
    have hwa := h k (Nat.lt_succ_self k)
    have he : Cookie.hprev (fun i => w (a + i)) (k + 1) =
        (1 + (1 - w (a + k)) * H) / w (a + k) := by
      rw [Cookie.hprev_succ, Cookie.hfix_eq]
    rw [← Nat.add_assoc, boundedSlope, he, Finset.prod_range_succ]
    calc
      _ ≤ (1 + (1 - v (a + k)) * b) / v (a + k) := min_le_right _ _
      _ ≤ (1 + (1 - w (a + k)) * b) / w (a + k) :=
        Cookie.step_mono (hw (a + k)) hwa (boundedSlope_bounds hK hv hv₁ (a + k)).1
      _ ≤ (1 + (1 - w (a + k)) * (H + (K - 1) * Q)) / w (a + k) :=
        Cookie.step_mono_h (hw (a + k)) (hw₁ (a + k)) (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      _ = _ := by dsimp only [Q]; ring

/-- Bounded-slope comparison function, extended by the identity on negative sites. -/
noncomputable def boundedPotential (K : ℝ) (w : ℕ → ℝ) (x : ℤ) : ℝ :=
  if x < 0 then (x : ℝ) else ∑ n ∈ Finset.range x.toNat, boundedSlope K w (n + 1)

theorem boundedPotential_nat (K : ℝ) (w : ℕ → ℝ) (a : ℕ) :
    boundedPotential K w (a : ℤ) = ∑ n ∈ Finset.range a, boundedSlope K w (n + 1) := by
  simp [boundedPotential]

theorem boundedPotential_sub_nat (K : ℝ) (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    boundedPotential K w (b : ℤ) - boundedPotential K w (a : ℤ) =
      ∑ n ∈ Finset.Ico a b, boundedSlope K w (n + 1) := by
  rw [boundedPotential_nat, boundedPotential_nat, Finset.sum_Ico_eq_sub _ hab]

theorem boundedPotential_add_one (K : ℝ) (w : ℕ → ℝ) (x : ℤ) :
    boundedPotential K w (x + 1) - boundedPotential K w x =
      if 0 ≤ x then boundedSlope K w (x.toNat + 1) else 1 := by
  by_cases hx : 0 ≤ x
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    rw [← Int.natCast_succ, boundedPotential_nat, boundedPotential_nat, Finset.sum_range_succ]
    simp
  · rw [if_neg hx]
    by_cases hx' : x + 1 < 0
    · simp [boundedPotential, hx', lt_of_not_ge hx]
    · have he : x = -1 := by omega
      norm_num [he, boundedPotential]

theorem boundedPotential_sub_one (K : ℝ) (w : ℕ → ℝ) {x : ℤ} (hx : 0 ≤ x) :
    boundedPotential K w x - boundedPotential K w (x - 1) = boundedSlope K w x.toNat := by
  have h := boundedPotential_add_one K w (x - 1)
  rw [sub_add_cancel] at h
  by_cases hpos : 0 ≤ x - 1
  · have hc : (x - 1).toNat + 1 = x.toNat := by omega
    rwa [if_pos hpos, hc] at h
  · have he : x = 0 := by omega
    rw [if_neg hpos] at h
    simpa only [he, Int.toNat_zero, boundedSlope] using h

theorem boundedPotential_add_one_bounds {K : ℝ} (hK : 1 ≤ K) {w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (x : ℤ) :
    1 ≤ boundedPotential K w (x + 1) - boundedPotential K w x ∧
      boundedPotential K w (x + 1) - boundedPotential K w x ≤ K := by
  rw [boundedPotential_add_one]
  split
  · exact boundedSlope_bounds hK hw hw₁ _
  · exact ⟨le_rfl, hK⟩

theorem boundedPotential_sub_bounds {K : ℝ} (hK : 1 ≤ K) {w : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) {x y : ℤ} (hxy : x ≤ y) :
    (y : ℝ) - x ≤ boundedPotential K w y - boundedPotential K w x ∧
      boundedPotential K w y - boundedPotential K w x ≤ K * ((y : ℝ) - x) := by
  have hlo : Monotone (fun z : ℤ => boundedPotential K w z - (z : ℝ)) := by
    apply monotone_int_of_le_succ
    intro z
    have h := (boundedPotential_add_one_bounds hK hw hw₁ z).1
    push_cast
    linarith only [h]
  have hhi : Monotone (fun z : ℤ => K * (z : ℝ) - boundedPotential K w z) := by
    apply monotone_int_of_le_succ
    intro z
    have h := (boundedPotential_add_one_bounds hK hw hw₁ z).2
    push_cast
    linarith only [h]
  constructor
  · linarith only [hlo hxy]
  · linarith only [hhi hxy]

theorem monotone_boundedPotential_sub {K : ℝ} (hK : 1 ≤ K) {w v : ℕ → ℝ}
    (hw : ∀ n, 0 < w n) (hw₁ : ∀ n, w n ≤ 1) (hv₁ : ∀ n, v n ≤ 1)
    (hle : ∀ n, w n ≤ v n) :
    Monotone (fun x : ℤ => boundedPotential K w x - boundedPotential K v x) := by
  apply monotone_int_of_le_succ
  intro x
  have h₁ := boundedPotential_add_one K w x
  have h₂ := boundedPotential_add_one K v x
  by_cases hx : 0 ≤ x
  · rw [if_pos hx] at h₁ h₂
    have h₃ := boundedSlope_le_of_le_prefix hK hw hw₁ hv₁ (x.toNat + 1) (fun i _ => hle i)
    linarith only [h₁, h₂, h₃]
  · rw [if_neg hx] at h₁ h₂
    linarith only [h₁, h₂]

theorem boundedPotential_eq_of_eq_prefix (K : ℝ) {w v : ℕ → ℝ} (x : ℤ)
    (heq : ∀ n < x.toNat, w n = v n) : boundedPotential K w x = boundedPotential K v x := by
  unfold boundedPotential
  split
  · rfl
  · exact Finset.sum_congr rfl fun n hn =>
      boundedSlope_eq_of_eq_prefix K (n + 1) (fun i hi => heq i
        ((Nat.lt_succ_iff.mp hi).trans_lt (Finset.mem_range.mp hn)))

/-- The drift at a nonnegative site with right-jump probability `α`
equals the comparison drift plus the correction for replacing `w` by `α`. -/
theorem boundedPotential_mean_increment (K : ℝ) {w : ℕ → ℝ} {x : ℤ}
    (hx : 0 ≤ x) (α : ℝ) :
    α * (boundedPotential K w (x + 1) - boundedPotential K w x) +
        (1 - α) * (boundedPotential K w (x - 1) - boundedPotential K w x) =
      w x.toNat * boundedSlope K w (x.toNat + 1) - (1 - w x.toNat) * boundedSlope K w x.toNat +
        (α - w x.toNat) * (boundedSlope K w (x.toNat + 1) + boundedSlope K w x.toNat) := by
  have hr := boundedPotential_add_one K w x
  rw [if_pos hx] at hr
  have hl := boundedPotential_sub_one K w hx
  rw [hr, show boundedPotential K w (x - 1) - boundedPotential K w x =
      -boundedSlope K w x.toNat by linarith only [hl]]
  ring

end Swarming.Diameter
