/-
  Equation `(Zloss)` of the occupation-time estimate (Proposition `ball` of
  *Swarming of interacting excited random walks*, `main_1d_revised.tex`):

      E[ H_{j,n+1}(X^i_{n+1}) - H_{j,n}(X^i_n) | F_n ]
        >= 1{0 <= X^i_n <= r_n} - b_n a^{X^i_n - r_n} 1{X^i_n >= r_n},
      r_n = M^j_n,   b_n = h_j(r_n - 1) + 2.

  The paper derives it by a four-case analysis of the position `X^i_n` relative to the record
  `r_n`.  Each case below is a *deterministic* real-arithmetic lemma with its premises listed
  explicitly.  The premises are exactly the quantities that the stochastic layer must supply:

  * `zdrift_interior` : `(dominate)` alpha_n^i >= omega_j(x) together with `(unit)` and the
    fact that `h_j(x)`, `h_j(x-1)` are `F_n`-measurable for `x <= r_n`
    (`Swarm/Reveal.lean` supplies `(dominate)` pointwise; the measurability is the filtration part);
  * `zdrift_neg`      : `h_j(x) = h_j(x-1) = 1` for `x < 0` and `alpha >= 1/2`;
  * `zdrift_at`       : `E[h_j(r_n) | F_n] >= 1`, `alpha >= 1/2`, `b = h_j(r_n-1) + 2`;
  * `zdrift_above`    : the projected recursion `(projh)` at the sites above the record, and
    `1 <= e_0 <= b_n`.

  `Zloss` is the combination: it turns the four case bounds into the paper's single pointwise
  inequality, with the indicator and loss term on the left.

  **What is *not* claimed here.**  These are not conditional-expectation statements.  The
  passage from "the drift of `H_{j,n}` computed pointwise on each `F_n`-atom" to the
  `condExp` inequality `(Zloss)` is the stochastic layer (nested filtration + regular
  conditional expectation), and is *not* discharged in this file; `Zloss` states plainly
  which four bounds it consumes.
-/
import Swarm.Imports
import Swarm.EnvCore
import Swarm.ProjRec

open Finset
open scoped BigOperators

namespace SwarmOcc

/-! ### The four cases of `(Zloss)` -/

/-- **Interior case `0 <= x < r_n`**: with `(dominate)` `w = omega_j(x) <= alpha` and `(unit)`
`w h(x) - (1-w) h(x-1) = 1`, the drift is at least `1`.

The two conditional means are `e = E[h_j(x)|F_n]`, `e' = E[h_j(x-1)|F_n]`; on the event
`{X^i_n = x}` with `x < r_n` both sites are revealed, so `e = h(x)`, `e' = h(x-1)`.  The lemma
only needs the resulting one-sided bounds `h(x) <= e`, `e' <= h(x-1)` (both equalities in the
actual model) and `e + e' >= 0`. -/
theorem zdrift_interior {α w e e' hx hx1 : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hαw : w ≤ α)
    (he : hx ≤ e) (he' : e' ≤ hx1) (hene : 0 ≤ e + e')
    (hunit : w * hx - (1 - w) * hx1 = 1) :
    1 ≤ α * e - (1 - α) * e' := by
  have h1 : w * hx - (1 - w) * hx1 ≤ w * e - (1 - w) * e' := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr he), mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr he')]
  have h2 : w * e - (1 - w) * e' ≤ α * e - (1 - α) * e' := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hαw) hene]
  linarith

/-- **Case `x < 0`**: both `h_j` values are `1`, so the drift is `2 alpha - 1 >= 0`. -/
theorem zdrift_neg {α : ℝ} (hα : 1 / 2 ≤ α) : 0 ≤ α * 1 - (1 - α) * 1 := by
  linarith

/-- **Case `x = r_n`**: with `E[h_j(r_n)|F_n] >= 1`, `alpha >= 1/2` and
`b_n = h_j(r_n - 1) + 2`, the drift is at least `1 - b_n`. -/
theorem zdrift_at {α e hprev b : ℝ} (hα : 1 / 2 ≤ α) (he : 1 ≤ e) (hsum : 0 ≤ e + hprev)
    (hhprev : 0 ≤ hprev) (hb : b = hprev + 2) :
    1 - b ≤ α * e - (1 - α) * hprev := by
  have h1 : (1 / 2) * e - (1 / 2) * hprev ≤ α * e - (1 - α) * hprev := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) hsum]
  have h2 : (1 / 2) * (1 - hprev) ≤ (1 / 2) * e - (1 / 2) * hprev := by linarith
  have h3 : 1 - b ≤ (1 / 2) * (1 - hprev) := by
    rw [hb]; linarith
  linarith

/-- **Case `x = r_n + g`, `g >= 1`**: using `(projh)` and `alpha >= 1/2`, the drift is at
least `-b_n a^g`.  (Stated with the increment index `k` for the pair `(e_{k+1}, e_k)`, i.e.
`g = k+1`.) -/
theorem zdrift_above {a b α : ℝ} (_ha0 : 0 ≤ a) (ha1 : a < 1) (ha13 : 1 / 3 ≤ a)
    (_hb : 0 ≤ b) (hα : 1 / 2 ≤ α) (e : ℕ → ℝ)
    (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (he0 : e 0 ≤ b)
    (hene : ∀ g, 0 ≤ e g) (k : ℕ) :
    -b * a ^ (k + 1) ≤ α * e (k + 1) - (1 - α) * e k := by
  have ha1' : a ≠ 1 := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hstep := proj_step_sub ha1' e he k
  have hL : (0 : ℝ) ≤ (1 + a) / (1 - a) := by positivity
  -- the increment is at least `-(1-a) a^k b`
  have hinc : -((1 - a) * a ^ k * b) ≤ e (k + 1) - e k := by
    rw [hstep]
    have hbnd : -((1 - a) * a ^ k * b) = (1 - a) * a ^ k * (-b) := by ring
    rw [hbnd]
    have hcoef : (0 : ℝ) ≤ (1 - a) * a ^ k := by positivity
    have hlast : -b ≤ (1 + a) / (1 - a) - e 0 := by linarith
    exact mul_le_mul_of_nonneg_left hlast hcoef
  -- drop the positive `(alpha - 1/2)(e_{k+1}+e_k)` term
  have hdrop : (1 / 2 : ℝ) * (e (k + 1) - e k)
      ≤ α * e (k + 1) - (1 - α) * e k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) (by linarith [hene (k + 1), hene k] :
      (0 : ℝ) ≤ e (k + 1) + e k)]
  have hcoef2 : (1 / 2 : ℝ) * ((1 - a) * a ^ k * b) ≤ b * a ^ (k + 1) := by
    have hpow : a ^ (k + 1) = a ^ k * a := by rw [pow_succ]
    rw [hpow]
    have hcoef : (0 : ℝ) ≤ b * a ^ k := by positivity
    nlinarith [hcoef, mul_nonneg hcoef (by linarith : (0:ℝ) ≤ a - 1/3)]
  nlinarith

/-! ### The combination: `(Zloss)` -/

/-- **`(Zloss)`**: the paper's pointwise drift lower bound, assembled from the four case
bounds.  `E` is `x |-> E[h_j(x) | F_n]` and `Env` is `x |-> E[h_j(x-1) | F_n]`; `r` is the
record `r_n >= 0`, `b` is `b_n`, `α` is `α^i_n`.  The conclusion is

    1{0 <= x <= r} - b a^{x-r} 1{r <= x}  <=  α E x - (1-α) Env x .

The four hypotheses are *exactly* the four case estimates `zdrift_interior`, `zdrift_neg`,
`zdrift_at`, `zdrift_above`; no conditional expectation is asserted here. -/
theorem Zloss {a b α : ℝ} (r : ℤ) (hr : 0 ≤ r) (E Env : ℤ → ℝ)
    (hbelow : ∀ x : ℤ, 0 ≤ x → x < r → 1 ≤ α * E x - (1 - α) * Env x)
    (hneg : ∀ x : ℤ, x < 0 → 0 ≤ α * E x - (1 - α) * Env x)
    (hat : 1 - b ≤ α * E r - (1 - α) * Env r)
    (habove : ∀ x : ℤ, r < x → -b * a ^ (x - r).toNat ≤ α * E x - (1 - α) * Env x) :
    ∀ x : ℤ, (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0)
        - b * (if r ≤ x then a ^ (x - r).toNat else 0)
      ≤ α * E x - (1 - α) * Env x := by
  intro x
  rcases lt_trichotomy x r with hlt | heq | hgt
  · -- `x < r`
    rcases lt_or_ge x 0 with hxneg | hx0
    · rw [if_neg (by omega : ¬ (0 ≤ x ∧ x ≤ r)), if_neg (by omega : ¬ r ≤ x)]
      simpa using hneg x hxneg
    · rw [if_pos ⟨hx0, hlt.le⟩, if_neg (by omega : ¬ r ≤ x)]
      simpa using hbelow x hx0 hlt
  · rw [heq, if_pos ⟨hr, le_rfl⟩, if_pos le_rfl,
      show ((r : ℤ) - r).toNat = 0 from by simp, pow_zero, mul_one]
    exact hat
  · rw [if_neg (by omega : ¬ (0 ≤ x ∧ x ≤ r)), if_pos hgt.le]
    simpa using habove x hgt

end SwarmOcc
