/-
  Scale function / Poisson-equation algebra for the crossing estimate of
  *Swarming of interacting excited random walks* (main_1d_revised.tex),
  Section 2.2, proof of Lemma `transience` (eq. (cross)).

  Everything here is deterministic: it is a statement about a fixed weight sequence
  `ω : ℕ → ℝ` with values in `[1/2, p] ⊂ (0,1)`.  The stochastic content of the crossing
  estimate -- that the conditional right-jump probability of walker `i` dominates
  `ω_j(X^i_t)` on `{0 ≤ X^i_t < M^j_t}` (eq. (dominate)), and that the exit time of
  `[b0, b1+1]` is almost surely finite -- is isolated separately and is not assumed here.

  Notation (paper, with sites indexed by `ℕ`, which is all the crossing estimate needs
  since `b0 ≥ 0`):
    r(x)   = (1 - w(x))/w(x)                        `rat`
    R(y)   = prod_{x=b0+1}^{y} r(x)                 `R`      (R(b0) = 1, R nonincreasing)
    Z      = sum_{y=b0}^{b1} R(y)                   `Z`      (Z >= 1)
    f(z)   = (sum_{y=b0}^{z-1} R(y)) / Z            `sc`     (scale function of [b0,b1+1])

  The paper's identities:
    f(b0) = 0, f(b1+1) = 1, 0 <= f <= 1, f nondecreasing,
    w(x)(f(x+1) - f(x)) = (1 - w(x))(f(x) - f(x-1))                (harmonic identity)
    a f(x+1) + (1-a) f(x-1) - f(x) = (a - w(x))(f(x+1) - f(x-1))   (drift computation)
    1 - f(b1) = R(b1)/Z <= R(b1)                                   (eq. (cross) right side)
-/
import Swarm.Imports

open Finset
open scoped BigOperators

namespace SwarmSpeed

/-! ### The ratio sequence and the potential `R` -/

/-- `r(x) = (1 - w(x))/w(x)`, the paper's local ratio (identical to `ExcitedEnv.rOf`). -/
noncomputable def rat (w : ℕ → ℝ) (x : ℕ) : ℝ := (1 - w x) / w x

/-- `R(y) = prod_{x=b0+1}^{y} r(x)`; the empty product `R(b0) = 1` is the paper's boundary
condition `h(-1) = 1` transported to the interval. -/
noncomputable def R (w : ℕ → ℝ) (b0 : ℕ) (y : ℕ) : ℝ := ∏ x ∈ Icc (b0 + 1) y, rat w x

/-- The normalising constant `Z = sum_{y=b0}^{b1} R(y)`. -/
noncomputable def Z (w : ℕ → ℝ) (b0 b1 : ℕ) : ℝ := ∑ y ∈ Icc b0 b1, R w b0 y

/-- The numerator `sum_{y=b0}^{z-1} R(y)` of the scale function (`Ico b0 z` has `z - b0`
elements when `z >= b0`, and is empty otherwise). -/
noncomputable def num (w : ℕ → ℝ) (b0 : ℕ) (z : ℕ) : ℝ := ∑ y ∈ Ico b0 z, R w b0 y

/-- The scale function `f(z) = (sum_{y=b0}^{z-1} R(y))/Z` of the interval `[b0, b1+1]`. -/
noncomputable def sc (w : ℕ → ℝ) (b0 b1 : ℕ) (z : ℕ) : ℝ := num w b0 z / Z w b0 b1

/-! ### Elementary bounds on the ratios -/

lemma rat_pos {w : ℕ → ℝ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (x : ℕ) :
    0 < rat w x := by
  have h1 : 0 < w x := by linarith [hlo x]
  have h2 : 0 < 1 - w x := by linarith [hhi x]
  exact div_pos h2 h1

lemma rat_nonneg {w : ℕ → ℝ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (x : ℕ) :
    0 ≤ rat w x := (rat_pos hlo hhi x).le

lemma rat_le_one {w : ℕ → ℝ} (hlo : ∀ x, 1 / 2 ≤ w x) (x : ℕ) : rat w x ≤ 1 := by
  have h1 : 0 < w x := by linarith [hlo x]
  rw [rat, div_le_one h1]
  linarith [hlo x]

/-- `w(x) * r(x) = 1 - w(x)`: the identity that makes the scale function harmonic. -/
lemma rat_mul {w : ℕ → ℝ} (hlo : ∀ x, 1 / 2 ≤ w x) (x : ℕ) : w x * rat w x = 1 - w x := by
  have h1 : w x ≠ 0 := by linarith [hlo x]
  rw [rat]
  field_simp

/-- The two-valued case `w in {1/2, p}`: a ratio is `1` or `rho = (1-p)/p`. -/
lemma rat_two_valued {w : ℕ → ℝ} {p : ℝ} (h2 : ∀ x, w x = 1 / 2 ∨ w x = p) (x : ℕ) :
    rat w x = 1 ∨ rat w x = (1 - p) / p := by
  rcases h2 x with h | h
  · left; rw [rat, h]; norm_num
  · right; rw [rat, h]

/-! ### The potential `R` -/

lemma R_b0 {w : ℕ → ℝ} {b0 : ℕ} : R w b0 b0 = 1 := by
  have h : Icc (b0 + 1) b0 = (∅ : Finset ℕ) := by
    rw [Icc_eq_empty_iff]; omega
  simp [R, h]

lemma R_succ {w : ℕ → ℝ} {b0 y : ℕ} (hy : b0 ≤ y) :
    R w b0 (y + 1) = R w b0 y * rat w (y + 1) :=
  prod_Icc_succ_top (by omega) _

lemma R_pos {w : ℕ → ℝ} {b0 : ℕ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (y : ℕ) :
    0 < R w b0 y := prod_pos fun x _ => rat_pos hlo hhi x

lemma R_nonneg {w : ℕ → ℝ} {b0 : ℕ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (y : ℕ) :
    0 ≤ R w b0 y := (R_pos hlo hhi y).le

lemma R_eq_one_of_le {y : ℕ} (hy : y ≤ b0) : R w b0 y = 1 := by
  have h : Icc (b0 + 1) y = (∅ : Finset ℕ) := by
    rw [Icc_eq_empty_iff]; omega
  simp [R, h]

/-- `R <= 1`: every factor of the defining product is at most `1`. -/
lemma R_le_one {w : ℕ → ℝ} {b0 : ℕ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (y : ℕ) :
    R w b0 y ≤ 1 := by
  unfold R
  exact prod_le_one (fun x _ => rat_nonneg hlo hhi x) (fun x _ => rat_le_one hlo x)

/-- `R` is nonincreasing in `y`: this is exactly `r <= 1` (i.e. `w >= 1/2`). -/
lemma R_antitone {w : ℕ → ℝ} {b0 : ℕ} (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) :
    Antitone (R w b0) := by
  have step : ∀ y, b0 ≤ y → R w b0 (y + 1) ≤ R w b0 y := by
    intro y hy
    rw [R_succ hy]
    calc R w b0 y * rat w (y + 1) ≤ R w b0 y * 1 :=
          mul_le_mul_of_nonneg_left (rat_le_one hlo _) (R_nonneg hlo hhi y)
      _ = R w b0 y := mul_one _
  intro a b hab
  by_cases hb : b ≤ b0
  · rw [R_eq_one_of_le (le_trans hab hb), R_eq_one_of_le hb]
  · push_neg at hb
    by_cases ha : a ≤ b0
    · rw [R_eq_one_of_le ha]; exact R_le_one hlo hhi b
    · push_neg at ha
      obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
      have key : ∀ k, R w b0 (a + k) ≤ R w b0 a := by
        intro k
        induction k with
        | zero => exact le_rfl
        | succ k ih =>
            have h1 : R w b0 (a + k + 1) ≤ R w b0 (a + k) := step _ (by omega)
            have h2 : a + (k + 1) = a + k + 1 := by omega
            rw [h2]; exact le_trans h1 ih
      exact key k

/-! ### The scale function `f` and its boundary values -/

section Scale

variable {w : ℕ → ℝ} {b0 b1 : ℕ}

lemma num_eq_zero {z : ℕ} (hz : z ≤ b0) : num w b0 z = 0 := by
  unfold num
  have h : Ico b0 z = (∅ : Finset ℕ) := by rw [Ico_eq_empty_iff]; omega
  simp [h]

lemma Z_pos (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) : 0 < Z w b0 b1 :=
  sum_pos (fun y _ => R_pos hlo hhi y) (nonempty_Icc.mpr hb)

lemma Z_ge_one (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) :
    1 ≤ Z w b0 b1 := by
  unfold Z
  have h := single_le_sum (f := R w b0) (fun y _ => R_nonneg hlo hhi y)
      (mem_Icc.mpr ⟨le_rfl, hb⟩ : b0 ∈ Icc b0 b1)
  rwa [R_b0] at h

lemma num_nonneg (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (z : ℕ) : 0 ≤ num w b0 z := by
  unfold num
  exact sum_nonneg fun y _ => R_nonneg hlo hhi y

lemma num_le_Z (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) {z : ℕ} (hz : z ≤ b1 + 1) :
    num w b0 z ≤ Z w b0 b1 := by
  unfold num Z
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [mem_Ico] at hy
    exact mem_Icc.mpr ⟨hy.1, by omega⟩
  · intro y _ _; exact R_nonneg hlo hhi y

lemma sc_b0 : sc w b0 b1 b0 = 0 := by
  unfold sc
  rw [num_eq_zero le_rfl, zero_div]

lemma Ico_succ_eq_Icc : Ico b0 (b1 + 1) = Icc b0 b1 := by
  ext y
  simp only [mem_Ico, mem_Icc]
  omega

lemma num_succ : num w b0 (b1 + 1) = Z w b0 b1 := by
  unfold num Z
  rw [Ico_succ_eq_Icc]

lemma sc_top (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) :
    sc w b0 b1 (b1 + 1) = 1 := by
  have hZ : Z w b0 b1 ≠ 0 := ne_of_gt (Z_pos hlo hhi hb)
  unfold sc
  rw [num_succ, div_self hZ]

lemma sc_nonneg (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) (z : ℕ) :
    0 ≤ sc w b0 b1 z :=
  div_nonneg (num_nonneg hlo hhi z) (Z_pos hlo hhi hb).le

lemma sc_le_one (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) {z : ℕ}
    (hz : z ≤ b1 + 1) : sc w b0 b1 z ≤ 1 := by
  unfold sc
  rw [div_le_one (Z_pos hlo hhi hb)]
  exact num_le_Z hlo hhi hz

/-- The one-step increment: `f(z+1) - f(z) = R(z)/Z`. -/
lemma sc_succ_sub {z : ℕ} (hz : b0 ≤ z) :
    sc w b0 b1 (z + 1) - sc w b0 b1 z = R w b0 z / Z w b0 b1 := by
  unfold sc num
  rw [sum_Ico_succ_top hz]
  ring

/-- The backwards increment: `f(z) - f(z-1) = R(z-1)/Z`. -/
lemma sc_sub_pred {z : ℕ} (hz : b0 + 1 ≤ z) :
    sc w b0 b1 z - sc w b0 b1 (z - 1) = R w b0 (z - 1) / Z w b0 b1 := by
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact sc_succ_sub (b1 := b1) (by omega)

lemma sc_monotone (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) :
    Monotone (sc w b0 b1) := by
  have step : ∀ z, b0 ≤ z → sc w b0 b1 z ≤ sc w b0 b1 (z + 1) := by
    intro z hz
    have h := sc_succ_sub (w := w) (b0 := b0) (b1 := b1) hz
    have h2 : 0 ≤ R w b0 z / Z w b0 b1 :=
      div_nonneg (R_nonneg hlo hhi _) (Z_pos hlo hhi hb).le
    linarith
  intro a b hab
  by_cases ha : a ≤ b0
  · rw [show sc w b0 b1 a = 0 from by rw [sc, num_eq_zero ha, zero_div]]
    exact sc_nonneg hlo hhi hb b
  · push_neg at ha
    obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    have key : ∀ k, sc w b0 b1 a ≤ sc w b0 b1 (a + k) := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
          have h1 : sc w b0 b1 (a + k) ≤ sc w b0 b1 (a + k + 1) := step _ (by omega)
          have h2 : a + (k + 1) = a + k + 1 := by omega
          rw [h2]; exact le_trans ih h1
    exact key k

/-- **The harmonic identity** behind eq. (cross): for `b0 < x <= b1`,
`w(x)(f(x+1) - f(x)) = (1 - w(x))(f(x) - f(x-1))`. -/
theorem sc_harmonic (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) {x : ℕ}
    (hx0 : b0 < x) (hx1 : x ≤ b1) :
    w x * (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      = (1 - w x) * (sc w b0 b1 x - sc w b0 b1 (x - 1)) := by
  have h1 := sc_succ_sub (w := w) (b0 := b0) (b1 := b1) (z := x) (le_of_lt hx0)
  have h2 := sc_sub_pred (w := w) (b0 := b0) (b1 := b1) (z := x) (by omega)
  have hRs : R w b0 x = R w b0 (x - 1) * rat w x := by
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact R_succ (by omega)
  have hkey : w x * R w b0 x = (1 - w x) * R w b0 (x - 1) := by
    rw [hRs]
    calc w x * (R w b0 (x - 1) * rat w x) = R w b0 (x - 1) * (w x * rat w x) := by ring
      _ = R w b0 (x - 1) * (1 - w x) := by rw [rat_mul hlo]
      _ = (1 - w x) * R w b0 (x - 1) := by ring
  have hZ : Z w b0 b1 ≠ 0 := ne_of_gt (Z_pos hlo hhi hb)
  rw [h1, h2]
  field_simp
  exact hkey

/-- **The drift computation** of the proof of (cross): for any `a : ℝ` and `b0 < x <= b1`,
`a f(x+1) + (1-a) f(x-1) - f(x) = (a - w(x)) (f(x+1) - f(x-1))`. -/
theorem sc_drift (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) {x : ℕ}
    (hx0 : b0 < x) (hx1 : x ≤ b1) (a : ℝ) :
    a * sc w b0 b1 (x + 1) + (1 - a) * sc w b0 b1 (x - 1) - sc w b0 b1 x
      = (a - w x) * (sc w b0 b1 (x + 1) - sc w b0 b1 (x - 1)) := by
  have h1 := sc_succ_sub (w := w) (b0 := b0) (b1 := b1) (z := x) (le_of_lt hx0)
  have h2 := sc_sub_pred (w := w) (b0 := b0) (b1 := b1) (z := x) (by omega)
  have hRs : R w b0 x = R w b0 (x - 1) * rat w x := by
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact R_succ (by omega)
  have hkey : w x * R w b0 x = (1 - w x) * R w b0 (x - 1) := by
    rw [hRs]
    calc w x * (R w b0 (x - 1) * rat w x) = R w b0 (x - 1) * (w x * rat w x) := by ring
      _ = R w b0 (x - 1) * (1 - w x) := by rw [rat_mul hlo]
      _ = (1 - w x) * R w b0 (x - 1) := by ring
  have hZ : Z w b0 b1 ≠ 0 := ne_of_gt (Z_pos hlo hhi hb)
  have e1 : sc w b0 b1 (x + 1) = sc w b0 b1 x + R w b0 x / Z w b0 b1 := by linarith
  have e2 : sc w b0 b1 (x - 1) = sc w b0 b1 x - R w b0 (x - 1) / Z w b0 b1 := by linarith
  rw [e1, e2]
  field_simp
  linear_combination hkey

/-- The drift is nonnegative when the walker's conditional right-jump probability `a`
dominates the local weight `w(x)` (eq. (dominate) in the paper). -/
theorem sc_drift_nonneg (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) {x : ℕ}
    (hx0 : b0 < x) (hx1 : x ≤ b1) {a : ℝ} (ha : w x ≤ a) :
    0 ≤ a * sc w b0 b1 (x + 1) + (1 - a) * sc w b0 b1 (x - 1) - sc w b0 b1 x := by
  rw [sc_drift hlo hhi hb hx0 hx1 a]
  exact mul_nonneg (by linarith) (sub_nonneg.mpr (sc_monotone hlo hhi hb (by omega)))

/-- The probability of crossing down that the paper bounds in (cross), evaluated at the
starting point `b1`: `1 - f(b1) = R(b1)/Z <= R(b1) = prod_{x=b0+1}^{b1} r(x)`. -/
theorem one_sub_sc_le (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) :
    1 - sc w b0 b1 b1 ≤ R w b0 b1 := by
  have hZ := Z_pos hlo hhi hb
  have hZ1 := Z_ge_one hlo hhi hb
  have hstep : sc w b0 b1 (b1 + 1) - sc w b0 b1 b1 = R w b0 b1 / Z w b0 b1 :=
    sc_succ_sub (w := w) (b0 := b0) (b1 := b1) (z := b1) hb
  rw [sc_top hlo hhi hb] at hstep
  have : 1 - sc w b0 b1 b1 = R w b0 b1 / Z w b0 b1 := by linarith
  rw [this]
  calc R w b0 b1 / Z w b0 b1 ≤ R w b0 b1 / 1 := by
        apply div_le_div_of_nonneg_left (R_nonneg hlo hhi _) (by norm_num) hZ1
    _ = R w b0 b1 := div_one _

end Scale

end SwarmSpeed
