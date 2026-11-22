import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace Swarming.Diameter

set_option autoImplicit false

variable {ι : Type*}

private noncomputable def expSum (θ : ℝ) (s : Finset ι) (z : ι → ℝ) : ℝ :=
  ∑ i ∈ s, Real.exp (-θ * z i)

/-- Logarithmic approximation of the minimum of finitely many values. -/
noncomputable def softMinimum (θ : ℝ) (s : Finset ι) (z : ι → ℝ) : ℝ :=
  -Real.log (expSum θ s z) / θ

/-- The weights of the first-order approximation of the soft minimum. -/
noncomputable def softMinimumWeight (θ : ℝ) (s : Finset ι) (z : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-θ * z i) / expSum θ s z

private theorem expSum_pos (θ : ℝ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) :
    0 < expSum θ s z :=
  Finset.sum_pos (fun i _ => Real.exp_pos (-θ * z i)) hs

theorem softMinimumWeight_nonneg (θ : ℝ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) (i : ι) :
    0 ≤ softMinimumWeight θ s z i :=
  div_nonneg (Real.exp_pos _).le (expSum_pos θ hs z).le

theorem sum_softMinimumWeight (θ : ℝ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) :
    ∑ i ∈ s, softMinimumWeight θ s z i = 1 := by
  simp only [softMinimumWeight, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (expSum_pos θ hs z).ne'

private theorem expSum_le_card_mul {θ : ℝ} (hθ : 0 ≤ θ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) :
    expSum θ s z ≤ (s.card : ℝ) * Real.exp (-θ * s.inf' hs z) := by
  calc
    _ ≤ ∑ _ ∈ s, Real.exp (-θ * s.inf' hs z) :=
      Finset.sum_le_sum fun i hi => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Finset.inf'_le z hi) (neg_nonpos.mpr hθ))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

private theorem exp_le_expSum (θ : ℝ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) :
    Real.exp (-θ * s.inf' hs z) ≤ expSum θ s z := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hs z
  rw [he]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (-θ * z j)).le) hi

theorem softMinimum_bounds {θ : ℝ} (hθ : 0 < θ) {s : Finset ι} (hs : s.Nonempty) (z : ι → ℝ) :
    s.inf' hs z - Real.log (s.card : ℝ) / θ ≤ softMinimum θ s z ∧
      softMinimum θ s z ≤ s.inf' hs z := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hlo := Real.log_le_log (Real.exp_pos _) (exp_le_expSum θ hs z)
  have hhi := Real.log_le_log (expSum_pos θ hs z) (expSum_le_card_mul hθ.le hs z)
  rw [Real.log_exp] at hlo
  rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hhi
  unfold softMinimum
  constructor
  · apply (le_div_iff₀ hθ).mpr
    rw [sub_mul, div_mul_cancel₀ _ hθ.ne']
    linarith only [hhi]
  · apply (div_le_iff₀ hθ).mpr
    linarith only [hlo]

theorem softMinimumWeight_le_exp (θ : ℝ) {s : Finset ι} (hs : s.Nonempty)
    (z : ι → ℝ) (i : ι) :
    softMinimumWeight θ s z i ≤ Real.exp (-θ * (z i - s.inf' hs z)) := by
  unfold softMinimumWeight
  calc
    _ ≤ Real.exp (-θ * z i) / Real.exp (-θ * s.inf' hs z) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) (exp_le_expSum θ hs z)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem one_div_card_le_softMinimumWeight {θ : ℝ} (hθ : 0 < θ) {s : Finset ι}
    (hs : s.Nonempty) {z : ι → ℝ} {i : ι} (hi : z i = s.inf' hs z) :
    1 / (s.card : ℝ) ≤ softMinimumWeight θ s z i := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  unfold softMinimumWeight
  rw [hi, div_le_div_iff₀ hcard (expSum_pos θ hs z), one_mul]
  exact (expSum_le_card_mul hθ.le hs z).trans_eq (mul_comm _ _)

theorem softMinimum_mono {θ : ℝ} (hθ : 0 < θ) {s : Finset ι} (hs : s.Nonempty) {z w : ι → ℝ}
    (hle : ∀ i ∈ s, z i ≤ w i) : softMinimum θ s z ≤ softMinimum θ s w := by
  have h : expSum θ s w ≤ expSum θ s z := Finset.sum_le_sum (fun i hi =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hle i hi) (neg_nonpos.mpr hθ.le)))
  exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log (expSum_pos θ hs w) h)) hθ.le

theorem softMinimum_add_const {θ : ℝ} (hθ : 0 < θ) {s : Finset ι} (hs : s.Nonempty)
    (z : ι → ℝ) (b : ℝ) :
    softMinimum θ s (fun i => z i + b) = softMinimum θ s z + b := by
  have he : expSum θ s (fun i => z i + b) = expSum θ s z * Real.exp (-θ * b) := by
    unfold expSum
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.exp_add]; congr 1; ring
  rw [softMinimum, he, Real.log_mul (expSum_pos θ hs z).ne' (Real.exp_ne_zero _), Real.log_exp, softMinimum]
  field_simp
  ring

theorem abs_softMinimum_sub_le {θ : ℝ} (hθ : 0 < θ) {s : Finset ι} (hs : s.Nonempty)
    {z u : ι → ℝ} {K : ℝ} (hu : ∀ i ∈ s, |u i| ≤ K) :
    |softMinimum θ s (fun i => z i + u i) - softMinimum θ s z| ≤ K := by
  have hlo := softMinimum_mono hθ hs
    (z := fun i => z i + (-K)) (w := fun i => z i + u i)
    (fun i hi => add_le_add le_rfl (abs_le.mp (hu i hi)).1)
  have hhi := softMinimum_mono hθ hs
    (z := fun i => z i + u i) (w := fun i => z i + K)
    (fun i hi => add_le_add le_rfl (abs_le.mp (hu i hi)).2)
  rw [softMinimum_add_const hθ hs] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- First-order lower bound with a uniform quadratic remainder for bounded
jumps. -/
theorem softMinimum_sub_ge_weighted_sum {θ K : ℝ} (hθ : 0 < θ) (hK : θ * K ≤ 1)
    {s : Finset ι} (hs : s.Nonempty) {z u : ι → ℝ} (hu : ∀ i ∈ s, |u i| ≤ K) :
    (∑ i ∈ s, softMinimumWeight θ s z i * u i) - θ * K ^ 2 ≤
      softMinimum θ s (fun i => z i + u i) - softMinimum θ s z := by
  let w := softMinimumWeight θ s z
  let U := ∑ i ∈ s, w i * Real.exp (-θ * u i)
  have hU : 0 < U := Finset.sum_pos
    (fun i _ => mul_pos (div_pos (Real.exp_pos _) (expSum_pos θ hs z)) (Real.exp_pos _)) hs
  have hmul : expSum θ s (fun i => z i + u i) = expSum θ s z * U := by
    rw [Finset.mul_sum]
    unfold expSum
    apply Finset.sum_congr rfl
    intro i _
    change Real.exp (-θ * (z i + u i)) = expSum θ s z * (w i * Real.exp (-θ * u i))
    rw [show -θ * (z i + u i) = -θ * z i + -θ * u i by ring, Real.exp_add]
    have h : expSum θ s z * w i = Real.exp (-θ * z i) := by
      dsimp only [w, softMinimumWeight]
      field_simp [(expSum_pos θ hs z).ne']
    rw [← h, mul_assoc]
  have hexp (i : ι) (hi : i ∈ s) : Real.exp (-θ * u i) ≤ 1 - θ * u i + θ ^ 2 * K ^ 2 := by
    have h : |-θ * u i| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_of_pos hθ]
      exact (mul_le_mul_of_nonneg_left (hu i hi) hθ.le).trans hK
    have h₁ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h)).2
    have h₂ := pow_le_pow_left₀ (abs_nonneg (u i)) (hu i hi) 2
    rw [sq_abs] at h₂
    nlinarith only [h₁, mul_le_mul_of_nonneg_left h₂ (sq_nonneg θ)]
  have hlin : U ≤ 1 - θ * (∑ i ∈ s, w i * u i) + θ ^ 2 * K ^ 2 := by
    calc
      _ ≤ ∑ i ∈ s, w i * (1 - θ * u i + θ ^ 2 * K ^ 2) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hexp i hi) (softMinimumWeight_nonneg θ hs z i))
      _ = ∑ i ∈ s, (w i - θ * (w i * u i) + w i * (θ ^ 2 * K ^ 2)) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [show ∑ i ∈ s, w i = 1 from sum_softMinimumWeight θ hs z]
        ring
  have he : softMinimum θ s (fun i => z i + u i) - softMinimum θ s z = -Real.log U / θ := by
    simp only [softMinimum, hmul, Real.log_mul (expSum_pos θ hs z).ne' hU.ne']
    ring
  rw [he, le_div_iff₀ hθ]
  linarith only [Real.log_le_sub_one_of_pos hU, hlin]

/-- Nonnegative drifts near the minimum need only be controlled within
distance `d` of the minimum to bound their weighted average. -/
theorem softMinimum_weighted_drift_lower {θ d b : ℝ} (hθ : 0 < θ) (hb : 0 ≤ b)
    {s : Finset ι} (hs : s.Nonempty) {z a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hnear : ∀ i ∈ s, z i - s.inf' hs z ≤ d → 1 - b ≤ a i) :
    1 - b - (s.card : ℝ) * Real.exp (-θ * d) ≤
      ∑ i ∈ s, softMinimumWeight θ s z i * a i := by
  let w := softMinimumWeight θ s z
  have hterm (i : ι) (hi : i ∈ s) : w i * (1 - b) - Real.exp (-θ * d) ≤ w i * a i := by
    have hw := softMinimumWeight_nonneg θ hs z i
    by_cases h : z i - s.inf' hs z ≤ d
    · exact (sub_le_self _ (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left (hnear i hi h) hw)
    · have hiw : w i ≤ Real.exp (-θ * d) :=
        (softMinimumWeight_le_exp θ hs z i).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (le_of_not_ge h) (neg_nonpos.mpr hθ.le)))
      have hle : w i * (1 - b) ≤ w i := by
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left (sub_le_self 1 hb) hw)
      exact (sub_nonpos.mpr (hle.trans hiw)).trans (mul_nonneg hw (ha i hi))
  calc
    _ = ∑ i ∈ s, (w i * (1 - b) - Real.exp (-θ * d)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      change _ = (∑ i ∈ s, w i) * (1 - b) - _
      rw [show ∑ i ∈ s, w i = 1 from sum_softMinimumWeight θ hs z, one_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

end Swarming.Diameter
