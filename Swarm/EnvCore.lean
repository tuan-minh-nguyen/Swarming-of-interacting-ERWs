/-
  Environment ("site-mark") layer of §2.1 of
  *Swarming of interacting excited random walks* (main_1d_revised.tex).

  The paper's driving randomness is an i.i.d. Uniform(0,1) array `U^i(x,k)`; from it one
  builds the site marks

      B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p},          (marks)
      omega_j(x) = 1/2 + (p - 1/2) B_j(x),                 (omega)

  and then `h_j = h^{omega_j}`, the solution of the one-dimensional Poisson equation
  (hrec)/(unit) whose deterministic skeleton was certified in the baseline `PoissonCore.lean`.

  This file certifies the *deterministic* content of the marks: the two-valued structure of
  `omega_j`, the exact two-case form of the recursion for `h_j` (the paper's display in the
  proof of Proposition (spatial)), the bounds `1 <= h_j(x) <= h_j(x-1) + 2` used at
  line 603 of the paper, the ratio bounds for `r(x) = (1 - omega x)/omega x`, the exact
  product formula for products of ratios (each factor is `1` or `rho = (1-p)/p`), and the
  arithmetic of the paper's constant

      a = E[(1 - omega_j(0))/omega_j(0)] = 1 - (2p-1)(1-p)^{m-1}/p,
      1/2 < 1 - (1-p)^{m-1} <= a < 1.

  Nothing here is probabilistic: every statement is a statement about a fixed weight
  function `omega` (or a fixed `0/1` mark function `B`).
-/
import Swarm.Imports

open Finset
open scoped BigOperators

namespace ExcitedEnv

variable {ι : Type*}

/-! ### The site marks and the weights -/

/-- The paper's site weight `omega_j(x) = 1/2 + (p - 1/2) B_j(x)` (eq. (marks)-(omega)),
for a `0/1`-valued mark function `B`. -/
noncomputable def omegaMark (p : ℝ) (B : ι → ℝ) (x : ι) : ℝ := 1/2 + (p - 1/2) * B x

lemma omegaMark_eq_half {p : ℝ} {B : ι → ℝ} {x : ι} (h : B x = 0) :
    omegaMark p B x = 1/2 := by
  simp [omegaMark, h]

lemma omegaMark_eq_p {p : ℝ} {B : ι → ℝ} {x : ι} (h : B x = 1) :
    omegaMark p B x = p := by
  simp [omegaMark, h]

/-- Every site weight is `1/2` or `p`: the two-valued structure the whole argument uses. -/
lemma omegaMark_two_valued {p : ℝ} {B : ι → ℝ} (hB : ∀ x, B x = 0 ∨ B x = 1) (x : ι) :
    omegaMark p B x = 1/2 ∨ omegaMark p B x = p := by
  rcases hB x with h | h
  · exact Or.inl (omegaMark_eq_half h)
  · exact Or.inr (omegaMark_eq_p h)

/-- The ratio `r(x) = (1 - omega_j(x))/omega_j(x)` whose products occur in `h^*_j`, `G_j`
and in the local-coefficient estimates of the paper. -/
noncomputable def rOf (ω : ι → ℝ) (x : ι) : ℝ := (1 - ω x) / ω x

/-- `1 + r = 1/omega`: the identity converting the paper's two forms of (hrec). -/
lemma one_add_rOf {ω : ι → ℝ} {x : ι} (h : ω x ≠ 0) : 1 + rOf ω x = 1 / ω x := by
  unfold rOf
  field_simp
  ring

lemma rOf_eq_one_of_half {ω : ι → ℝ} {x : ι} (h : ω x = 1/2) : rOf ω x = 1 := by
  rw [rOf, h]
  norm_num

lemma rOf_eq_rho {ω : ι → ℝ} {x : ι} {p : ℝ} (h : ω x = p) :
    rOf ω x = (1 - p) / p := by
  simp only [rOf, h]

/-! ### Bounds on the ratios -/

lemma rOf_pos {ω : ι → ℝ} {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {x : ι}
    (hx : ω x = 1 / 2 ∨ ω x = p) : 0 < rOf ω x := by
  rcases hx with h | h
  · rw [rOf_eq_one_of_half h]; norm_num
  · rw [rOf_eq_rho h]; positivity

lemma rOf_le_one {ω : ι → ℝ} {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {x : ι}
    (hx : ω x = 1 / 2 ∨ ω x = p) : rOf ω x ≤ 1 := by
  rcases hx with h | h
  · rw [rOf_eq_one_of_half h]
  · rw [rOf_eq_rho h, div_le_one (by linarith)]
    linarith

/-- The lower bound `rho = (1-p)/p > 0` for every ratio. -/
lemma rho_le_rOf {ω : ι → ℝ} {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {x : ι}
    (hx : ω x = 1 / 2 ∨ ω x = p) : (1 - p) / p ≤ rOf ω x := by
  rcases hx with h | h
  · rw [rOf_eq_one_of_half h, div_le_one (by linarith)]
    linarith
  · rw [rOf_eq_rho h]

lemma rho_pos {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) : 0 < (1 - p) / p := by
  positivity

lemma rho_lt_one {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) : (1 - p) / p < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- **Exact product formula.** A product of ratios over a finite set of sites is `rho` to the
power of the number of *marked* sites (`omega u = p`), because each factor is `1` or `rho`. -/
lemma prod_rOf_eq_pow {ω : ℕ → ℝ} {p : ℝ} (hp1 : 1 / 2 < p)
    {s : Finset ℕ} (hω : ∀ u ∈ s, ω u = 1 / 2 ∨ ω u = p) :
    ∏ u ∈ s, rOf ω u = ((1 - p) / p) ^ (s.filter (fun u => ω u = p)).card := by
  classical
  have h1 : ∀ u ∈ s, rOf ω u = if ω u = p then (1 - p) / p else 1 := by
    intro u hu
    rcases hω u hu with h | h
    · have hne : ω u ≠ p := by rw [h]; linarith
      simp [hne, rOf_eq_one_of_half h]
    · simp [h, rOf_eq_rho h]
  rw [Finset.prod_congr rfl h1, Finset.prod_ite, div_pow]
  simp

/-! ### The potential `h^omega` and its two-case recursion -/

/-- `h^omega(x)` on `x >= 0`, with the boundary convention `h(-1) = 1` (eq. (hrec)). -/
noncomputable def hw (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 + (1 - ω 0) * 1) / ω 0
  | n + 1 => (1 + (1 - ω (n + 1)) * hw ω n) / ω (n + 1)

/-- `h^omega(x-1)`, i.e. `hprev 0 = h(-1) = 1` and `hprev (n+1) = h(n)`. -/
noncomputable def hprev (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => hw ω n

@[simp] lemma hprev_zero (ω : ℕ → ℝ) : hprev ω 0 = 1 := rfl

@[simp] lemma hprev_succ (ω : ℕ → ℝ) (n : ℕ) : hprev ω (n + 1) = hw ω n := rfl

lemma hw_eq (ω : ℕ → ℝ) (n : ℕ) :
    hw ω n = (1 + (1 - ω n) * hprev ω n) / ω n := by
  cases n with
  | zero => simp [hw, hprev]
  | succ k => simp [hw, hprev]

/-- `h^omega(x) = 1/omega(x) + r(x) h^omega(x-1)`: the form of (hrec) used in the paper's
display at line 335/603. -/
lemma hw_eq_one_div_add (ω : ℕ → ℝ) {n : ℕ} (h : ω n ≠ 0) :
    hw ω n = 1 / ω n + rOf ω n * hprev ω n := by
  rw [hw_eq]
  unfold rOf
  field_simp

/-- The recursion in the shape `h(x) = 1 + r(x) (1 + h(x-1))` used by the stationary
comparison: both `h_j` and `h^*_j` satisfy it. -/
lemma hw_rec (ω : ℕ → ℝ) (h : ∀ n, ω n ≠ 0) (n : ℕ) :
    hw ω (n + 1) = 1 + rOf ω (n + 1) * (1 + hprev ω (n + 1)) := by
  rw [hw_eq_one_div_add ω (h (n + 1)), ← one_add_rOf (h (n + 1))]
  ring

/-- The recursion at a single site, for every `n` (including `n = 0`). -/
lemma hw_rec' (ω : ℕ → ℝ) (h : ∀ n, ω n ≠ 0) (n : ℕ) :
    hw ω n = 1 + rOf ω n * (1 + hprev ω n) := by
  rw [hw_eq_one_div_add ω (h n), ← one_add_rOf (h n)]
  ring

/-- The unmarked branch `B_j(x) = 0` of the paper's display in the proof of (spatial). -/
lemma hw_of_half (ω : ℕ → ℝ) {n : ℕ} (h : ω n = 1 / 2) : hw ω n = hprev ω n + 2 := by
  rw [hw_eq, h]
  field_simp
  ring

/-- The marked branch `B_j(x) = 1` of the paper's display in the proof of (spatial). -/
lemma hw_of_p (ω : ℕ → ℝ) {n : ℕ} {p : ℝ} (hp0 : p ≠ 0) (h : ω n = p) :
    hw ω n = 1 / p + ((1 - p) / p) * hprev ω n := by
  rw [hw_eq, h]
  field_simp

/-- **The paper's two-case recursion** (display in the proof of Proposition (spatial)):
`h_j(x) = h_j(x-1) + 2` if `B_j(x) = 0`, and `h_j(x) = 1/p + ((1-p)/p) h_j(x-1)` if
`B_j(x) = 1`. -/
theorem hw_two_case {p : ℝ} (hp0 : p ≠ 0) (ω : ℕ → ℝ) (n : ℕ) :
    (ω n = 1 / 2 → hw ω n = hprev ω n + 2) ∧
      (ω n = p → hw ω n = 1 / p + ((1 - p) / p) * hprev ω n) :=
  ⟨fun hh => hw_of_half ω hh, fun hh => hw_of_p ω hp0 hh⟩

/-- `h^omega(x) >= 1` ("By (hrec), we have h^w(x) >= 1"). -/
theorem one_le_hw {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n = 1 / 2 ∨ ω n = p) : ∀ n, 1 ≤ hw ω n := by
  intro n
  induction n with
  | zero =>
      rcases hω 0 with h | h
      · rw [hw_of_half ω h]; simp
      · rw [hw_eq, h, hprev_zero]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
  | succ k ih =>
      have hk : 1 ≤ hprev ω (k + 1) := by
        rw [hprev_succ]; exact ih
      rcases hω (k + 1) with h | h
      · rw [hw_of_half ω h]; linarith
      · rw [hw_eq, h]
        rw [le_div_iff₀ (by linarith)]
        nlinarith

lemma one_le_hprev {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n = 1 / 2 ∨ ω n = p) (n : ℕ) : 1 ≤ hprev ω n := by
  cases n with
  | zero => simp
  | succ k => rw [hprev_succ]; exact one_le_hw hp1 hp2 hω k

/-- **`h_j(x) <= h_j(x-1) + 2`** (line 603: "Both branches of (hrec) give
`1 <= h_j(x) <= h_j(x-1) + 2`"). -/
theorem hw_le_hprev_add_two {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n = 1 / 2 ∨ ω n = p) (n : ℕ) : hw ω n ≤ hprev ω n + 2 := by
  have h1 := one_le_hprev hp1 hp2 hω n
  rcases hω n with h | h
  · rw [hw_of_half ω h]
  · rw [hw_eq, h]
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- The same two-sided bound in the form used in the paper: `1 <= h_j(x) <= h_j(x-1)+2`. -/
theorem hw_bounds {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n = 1 / 2 ∨ ω n = p) (n : ℕ) :
    1 ≤ hw ω n ∧ hw ω n ≤ hprev ω n + 2 :=
  ⟨one_le_hw hp1 hp2 hω n, hw_le_hprev_add_two hp1 hp2 hω n⟩

/-! ### The constant `a` of the paper -/

/-- The paper's constant `a = 1 - (2p-1)(1-p)^{m-1}/p`, written with `q = (1-p)^{m-1}`. -/
noncomputable def aConst (p q : ℝ) : ℝ := 1 - (2 * p - 1) * q / p

/-- `(1-p)^{m-1} <= 1/2` for `m >= 2` and `p > 1/2`. -/
lemma q_le_half {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    (1 - p) ^ (m - 1) ≤ 1 / 2 := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hle : 1 - p ≤ 1 / 2 := by linarith
  obtain ⟨k, hk⟩ : ∃ k, m - 1 = k + 1 := ⟨m - 2, by omega⟩
  rw [hk, pow_succ]
  have h2 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h5 : (1 - p) ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ h0 hle k
  have h6 : (1 - p) ^ k * (1 - p) ≤ (1 / 2) ^ k * (1 - p) :=
    mul_le_mul_of_nonneg_right h5 h0
  have h4 : (1 / 2 : ℝ) ^ k * (1 - p) ≤ 1 * (1 / 2) :=
    mul_le_mul h2 hle h0 (by positivity)
  linarith [h6, h4]

/-- **`1/2 < 1 - q <= a < 1`** (the paper: "For `m >= 2` and `p in (1/2,1)`, we note that
`1/2 < 1 - (1-p)^{m-1} <= a < 1`"). -/
theorem aConst_bounds {p q : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) (hq0 : 0 < q)
    (hq1 : q ≤ 1 / 2) :
    1 / 2 < aConst p q ∧ aConst p q < 1 ∧ 1 - q ≤ aConst p q := by
  have hp0 : 0 < p := by linarith
  have hratio_lt : (2 * p - 1) / p < 1 := by
    rw [div_lt_one hp0]; linarith
  have hratio_pos : 0 < (2 * p - 1) / p := by
    apply div_pos (by linarith) hp0
  have key : (2 * p - 1) * q / p = q * ((2 * p - 1) / p) := by field_simp
  have hlt : q * ((2 * p - 1) / p) < q := by
    nth_rewrite 2 [← mul_one q]
    exact mul_lt_mul_of_pos_left hratio_lt hq0
  have hle : q * ((2 * p - 1) / p) ≤ q := hlt.le
  have hpos : 0 < q * ((2 * p - 1) / p) := mul_pos hq0 hratio_pos
  rw [aConst, key]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The paper's `a` in the `(1-p)^{m-1}` form. -/
theorem aConst_q {p : ℝ} {m : ℕ} (hp1 : 1 / 2 < p) (hp2 : p < 1) (hm : 2 ≤ m) :
    1 / 2 < aConst p ((1 - p) ^ (m - 1)) := by
  have hq0 : 0 < (1 - p) ^ (m - 1) := by
    apply pow_pos; linarith
  exact (aConst_bounds hp1 hp2 hq0 (q_le_half hp1 hp2 hm)).1

/-! ### Geometric sums with ratio `a` -/

/-- `sum_{k<N} a^k = (1 - a^N)/(1 - a)`. -/
lemma geom_partial_sum (a : ℝ) (ha : a ≠ 1) (N : ℕ) :
    ∑ k ∈ range N, a ^ k = (1 - a ^ N) / (1 - a) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      field_simp
      ring

/-- `sum_{k>=0} a^k = (1-a)^{-1}` for `0 <= a < 1`. -/
lemma geom_tsum (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∑' k : ℕ, a ^ k = (1 - a)⁻¹ := by
  have h : ‖a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ha0]; exact ha1
  exact tsum_geometric_of_norm_lt_one h

/-- **The mean identity behind (spav)**: `1 + 2 sum_{l>=1} a^l = (1+a)/(1-a)`.
(This is the value `(1+a)/(1-a)` to which `H_j(r)/r` converges; the expectation interpretation
`a^l = E prod_{u<l} r(x-u)` requires independence and is *not* proved here.) -/
theorem mean_hstar (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    1 + 2 * (∑' l : ℕ, a ^ (l + 1)) = (1 + a) / (1 - a) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hsplit : (∑' l : ℕ, a ^ (l + 1)) = a * (∑' k : ℕ, a ^ k) := by
    have : (fun l : ℕ => a ^ (l + 1)) = fun l : ℕ => a * a ^ l := by
      funext l; rw [pow_succ]; ring
    rw [this, tsum_mul_left]
  rw [hsplit, geom_tsum a ha0 ha1]
  field_simp
  ring

end ExcitedEnv
