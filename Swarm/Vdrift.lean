/-
  The two remaining deterministic steps of the occupation-time estimate of Proposition
  `ball` of *Swarming of interacting excited random walks*:

  * **`(Vdrift)`**: the cancellation of the loss term `b_n a^{X^i_n - r_n}` between
    `(Zloss)` (the projected Poisson drift) and `(Fdrift)` (the correction potential).
    The paper: "The two terms involving `b_n a^{X^i_n-r_n}` cancel because
    `{g >= 0} = {X^i_n >= r_n}`."  Here `Vdrift_combine` is that cancellation and
    `Vdrift_Fcorr` instantiates the correction side with the verified `Fcorr_coin_drift`.

  * **`(Jbound)`/`(Vbound)`, pointwise part**: the record-cost increment
    `J_{t+1} = F_{b_{t+1}}(X^i_{t+1} - r_{t+1}) - F_{b_t}(X^i_{t+1} - r_t)` is bounded by
    `C_eps (b_{t+1}^2 + b_t^2)`, vanishes when the record does not advance, and the
    potential part of `Z_n` is bounded by `g L + b/(1-a) + C_eps b^2`.
    The *summation* `sum_{t<n} |J_{t+1}| <= C_eps sum_{x<M^i_n} h_j(x-1)^2` uses the
    spatial average `(spav)` and is left to the caller (`(spav)` is available on the actual
    array as `RawSpatial.spatial_G_array`); it is not asserted here.

  No conditional expectation, no environment and no walker count occurs in this file.
-/
import Swarm.Imports
import Swarm.EnvCore
import Swarm.Fcorr
import Swarm.ProjRec
import Swarm.Zdrift

open Finset
open scoped BigOperators

namespace SwarmOcc

/-! ### The loss term and the cancellation of `(Vdrift)` -/

/-- `FbRHS` at the gap `x - r`, written with the record indicator: this is the correction
drift in the form in which it meets `(Zloss)`. -/
lemma FbRHS_sub {a b ε : ℝ} {x r : ℤ} :
    FbRHS a b ε (x - r) = (if r ≤ x then -b * a ^ (x - r).toNat else 0) + ε := by
  unfold FbRHS
  by_cases h : 0 ≤ x - r
  · rw [if_pos h, if_pos (by omega : r ≤ x)]
  · rw [if_neg h, if_neg (by omega : ¬ r ≤ x)]
    ring

/-- **`(Vdrift)`: the cancellation.**  If the projected Poisson drift dominates the loss term
up to `Dh` (this is exactly `(Zloss)`), and the correction drift is at most the paper's
`FbRHS` (this is exactly `(Fdrift)`), then their difference, i.e. the drift of
`Z_n = H_{j,n}(X^i_n) - F_{b_n}(X^i_n - r_n)` before the `J` terms, is at least
`1{0 <= x <= r} - eps`.

The two loss terms cancel: `(Zloss)` carries `-b a^{x-r} 1{x >= r}` and `(Fdrift)` carries the
same quantity with the opposite sign. -/
theorem Vdrift_combine {a b ε Dh Df : ℝ} {x r : ℤ}
    (hDh : (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0)
        - b * (if r ≤ x then a ^ (x - r).toNat else 0) ≤ Dh)
    (hDf : Df ≤ FbRHS a b ε (x - r)) :
    (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0) - ε ≤ Dh - Df := by
  rw [FbRHS_sub] at hDf
  by_cases hrx : r ≤ x
  · simp only [if_pos hrx] at hDh hDf
    linarith
  · simp only [if_neg hrx] at hDh hDf
    linarith

/-- **`(Vdrift)` with the verified correction.**  `Fdrift` is supplied by
`Fcorr_coin_drift` at `g = x - r` with the actual `alpha >= 1/2`; the only remaining input is
`(Zloss)` in the form `Dh`. -/
theorem Vdrift_Fcorr {a b ε α : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (hα : 1 / 2 ≤ α) (r x : ℤ) (Dh : ℝ)
    (hDh : (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0)
        - b * (if r ≤ x then a ^ (x - r).toNat else 0) ≤ Dh) :
    (if 0 ≤ x ∧ x ≤ r then (1 : ℝ) else 0) - ε
      ≤ Dh - (α * Fcorr a ε b (x - r + 1) + (1 - α) * Fcorr a ε b (x - r - 1)
          - Fcorr a ε b (x - r)) :=
  Vdrift_combine hDh (Fcorr_coin_drift ha0 ha1 hb hε hα (x - r))

/-! ### The record-cost increment `J` -/

/-- **`(Jbound)`, pointwise.**  The record-cost increment is bounded by the sum of the two
absolute correction values, `C_eps (b_{t+1}^2 + b_t^2)`. -/
theorem J_abs_le {a ε b0 b1 : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hε : 0 < ε) (g0 g1 : ℤ) :
    |Fcorr a ε b1 g1 - Fcorr a ε b0 g0| ≤ (b1 ^ 2 + b0 ^ 2) / (ε * (1 - a) ^ 2) := by
  have h1 := Fcorr_abs_le ha0 ha1 hb1 hε g1
  have h2 := Fcorr_abs_le ha0 ha1 hb0 hε g0
  have h3 : |Fcorr a ε b1 g1 - Fcorr a ε b0 g0|
      ≤ |Fcorr a ε b1 g1| + |Fcorr a ε b0 g0| := abs_sub _ _
  have h5 : |Fcorr a ε b1 g1| + |Fcorr a ε b0 g0|
      ≤ (b1 ^ 2 + b0 ^ 2) / (ε * (1 - a) ^ 2) := by
    rw [add_div]
    linarith
  linarith

/-- **`J` vanishes when the record does not advance**: `J_{t+1} = 0` on `{r_{t+1} = r_t,
b_{t+1} = b_t}`. -/
theorem J_eq_zero_of {a ε b0 b1 : ℝ} {x r0 r1 : ℤ} (hr : r1 = r0) (hb : b1 = b0) :
    Fcorr a ε b1 (x - r1) - Fcorr a ε b0 (x - r0) = 0 := by
  rw [hr, hb]; ring

/-! ### `(Vbound)`, pointwise -/

/-- **`(Vbound)`, pointwise**: the potential part of `Z_n`,
`H_{j,n}(X^i_n) - F_{b_n}(X^i_n - r_n)`, is at most
`g L + b/(1-a) + b^2/(eps (1-a)^2)` with `g = X^i_n - r_n >= 0`, `b = b_n`.
The `H` part is identified with `sum_{j<g} e_j` by `projH`; the `F` part is bounded by
`Fcorr_abs_le`.  The `M^i_n`-proportional bound of the paper follows by taking `g <= M^i_n`. -/
theorem Z_bound {a b ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    {e : ℕ → ℝ} (he : ∀ g, e (g + 1) = a * e g + (1 + a)) (he0 : 1 ≤ e 0) (heb : e 0 ≤ b)
    (g : ℕ) (gf : ℤ) :
    (∑ j ∈ Finset.range g, e j) - Fcorr a ε b gf
      ≤ g * ((1 + a) / (1 - a)) + b / (1 - a) + b ^ 2 / (ε * (1 - a) ^ 2) := by
  have h1 := proj_partial_sum_upper ha0 ha1 hb he he0 heb g
  have h2 := Fcorr_abs_le ha0 ha1 hb hε gf
  have h3 : -Fcorr a ε b gf ≤ b ^ 2 / (ε * (1 - a) ^ 2) := by
    have hpos := Fcorr_nonpos a ε b gf
    rw [abs_of_nonpos hpos] at h2
    linarith
  linarith

end SwarmOcc
