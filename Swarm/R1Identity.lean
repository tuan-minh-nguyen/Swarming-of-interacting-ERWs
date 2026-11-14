/-
  **`locsum` residual R1: the harmonic function `h_j` and its truncations.**

  The paper's `h_j(x)` is `SwarmMarks.hof p (siteMarks .. j) x`, the two-branch recursion
  `h(x) = 1 + rho(x) (1 + h(x-1))`, `h(-1) = 1`.  The truncated stationary potential of
  `LocSumAct` is `LocSum.Q p k x` with `Q (k+1) x = 1 + rho(x) (1 + Q k (x-1))` and
  `Q 1 x = 1`.  The two recursions are the same, so `h_j` *is* one of the truncations:

      hof p ω x = Q p (x+2) x ω          (`hof_eq_Q`)

  and the paper's display (hstat) takes the following exact, hypothesis-free form on the
  one-sided mark row:

      hof p ω x - Q p ℓ x ω = Pz p x ℓ ω * (1 + hof p ω (x-ℓ))     (ℓ ≤ x)

  This file proves those two identities and the square comparison that consumes them.  No
  probability is involved.

  IMPORTANT: the *supremum* `hstarN` of `B1Potential.lean` is **not** the right object on a
  one-sided row: because `LocSum.rat` truncates `x - u` at `0`, the product `Pz x j` repeats
  the factor `rat 0` for every `j > x`, so `hstarN` is infinite as soon as site `0` is
  unmarked (see `R1Obstruction.lean`).  The correct "full potential" on a one-sided row is
  `hof` itself, which is what the identities of this file use.
-/
import Swarm.A4Assembly
import Swarm.MarkTails

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumR1

noncomputable section

/-- `LocSum.rat` is `SwarmMarks.rhoOf` composed with the mark evaluation. -/
lemma rat_eq_rhoOf (p : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    LocSum.rat p ω n = SwarmMarks.rhoOf p (ω n) := by
  unfold LocSum.rat SwarmMarks.rhoOf
  cases ω n <;> rfl

/-- **The harmonic function is a truncation of the potential**: `h_j(x) = Q_{x+2}(x)`.
The boundary value `h(-1) = 1` is exactly `Q 1 x = 1`. -/
theorem hof_eq_Q {p : ℝ} (hp0 : p ≠ 0) (ω : ℕ → Bool) (x : ℕ) :
    SwarmMarks.hof p ω x = LocSum.Q p (x + 2) x ω := by
  induction x with
  | zero =>
      rw [SwarmMarks.hof_zero, SwarmMarks.hstep_eq_rho hp0]
      have hQ : LocSum.Q p 2 0 ω = 1 + LocSum.rat p ω 0 * 2 := by
        have h1 := LocSum.Q_succ (p := p) 1 0 ω
        rw [LocSum.Q_one] at h1
        rw [h1]; norm_num
      rw [hQ, rat_eq_rhoOf]
      ring
  | succ k ih =>
      rw [SwarmMarks.hof_succ, SwarmMarks.hstep_eq_rho hp0, ih]
      have hQ : LocSum.Q p (k + 3) (k + 1) ω = 1 + LocSum.rat p ω (k + 1) * (1 + LocSum.Q p (k + 2) k ω) := by
        have h1 := LocSum.Q_succ (p := p) (k + 2) (k + 1) ω
        rwa [show k + 2 + 1 = k + 3 from rfl, Nat.succ_sub_one] at h1
      rw [hQ, rat_eq_rhoOf]

/-- **The exact `(hstat)` comparison on a one-sided row.**  For `ℓ ≤ x` the difference between
the harmonic function at `x` and the `ℓ`-truncation is the product of the ratios over the last
`ℓ` sites times `1 + h_j(x-ℓ)`. -/
theorem hof_sub_Q {p : ℝ} (hp0 : p ≠ 0) (ω : ℕ → Bool) {ℓ x : ℕ} (hℓx : ℓ ≤ x) :
    SwarmMarks.hof p ω x - LocSum.Q p ℓ x ω
      = LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ)) := by
  have hQ : LocSum.Q p (x + 2 - ℓ) (x - ℓ) ω = SwarmMarks.hof p ω (x - ℓ) := by
    rw [hof_eq_Q (p := p) hp0, show x - ℓ + 2 = x + 2 - ℓ from by omega]
  have h1 := LocSum.Q_telescope (p := p) (x + 2 - ℓ) ℓ x ω
  rw [show ℓ + (x + 2 - ℓ) = x + 2 from by omega, hQ] at h1
  rw [show SwarmMarks.hof p ω x = LocSum.Q p (x + 2) x ω from hof_eq_Q hp0 ω x]
  exact h1

/-- The one-sided upper comparison: `h_j(x) ≤ Q_ℓ(x) + Pz(x,ℓ) (1 + M)` whenever `h_j(x-ℓ) ≤ M`. -/
theorem hof_le_Q_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) {ℓ x : ℕ}
    (hℓx : ℓ ≤ x) {M : ℝ} (hM : SwarmMarks.hof p ω (x - ℓ) ≤ M) :
    SwarmMarks.hof p ω x ≤ LocSum.Q p ℓ x ω + LocSum.Pz p x ℓ ω * (1 + M) := by
  have hp0 : p ≠ 0 := by linarith
  have hid := hof_sub_Q (p := p) hp0 ω hℓx
  have hPz : 0 ≤ LocSum.Pz p x ℓ ω := LocSum.Pz_nonneg hp1 hp2 x ℓ ω
  have hle : LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ))
      ≤ LocSum.Pz p x ℓ ω * (1 + M) := by
    refine mul_le_mul_of_nonneg_left ?_ hPz
    linarith
  linarith

/-- `(|a| + b)^2 ≤ 2a^2 + 2b^2` for `b ≥ 0`. -/
lemma sq_abs_add_sq_le (a b : ℝ) (hb : 0 ≤ b) : (|a| + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
  have h2 : 0 ≤ (|a| - b) ^ 2 := sq_nonneg _
  nlinarith [h1, h2]

/-- **The square comparison.**  `h_j(x)² ≤ 2 Q_ℓ(x)² + 2 Pz(x,ℓ)² (1+M)²`. -/
theorem hof_sq_le_Q_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) {ℓ x : ℕ}
    (hℓx : ℓ ≤ x) {M : ℝ} (hM : SwarmMarks.hof p ω (x - ℓ) ≤ M) :
    (SwarmMarks.hof p ω x) ^ 2
      ≤ 2 * (LocSum.Q p ℓ x ω) ^ 2 + 2 * (LocSum.Pz p x ℓ ω) ^ 2 * (1 + M) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hid := hof_sub_Q (p := p) hp0 ω hℓx
  have hPz : 0 ≤ LocSum.Pz p x ℓ ω := LocSum.Pz_nonneg hp1 hp2 x ℓ ω
  have hr : 1 ≤ SwarmMarks.hof p ω (x - ℓ) := SwarmMarks.one_le_hof hp1.le hp2 ω (x - ℓ)
  have hP : 0 ≤ LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ)) := by positivity
  have hPle : LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ))
      ≤ LocSum.Pz p x ℓ ω * (1 + M) := by
    refine mul_le_mul_of_nonneg_left ?_ hPz
    linarith
  have hgoal : SwarmMarks.hof p ω x
      = LocSum.Q p ℓ x ω + LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ)) := by
    linarith
  have hBnn : 0 ≤ LocSum.Pz p x ℓ ω * (1 + M) := by
    refine mul_nonneg hPz ?_
    linarith
  -- step 1: the absolute value is bounded
  have h1 : |SwarmMarks.hof p ω x| ≤ |LocSum.Q p ℓ x ω| + LocSum.Pz p x ℓ ω * (1 + M) := by
    rw [hgoal]
    refine (abs_add_le _ _).trans ?_
    have hPabs : |LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ))|
        = LocSum.Pz p x ℓ ω * (1 + SwarmMarks.hof p ω (x - ℓ)) :=
      abs_of_nonneg hP
    rw [hPabs]
    linarith
  have h2 : (SwarmMarks.hof p ω x) ^ 2
      ≤ (|LocSum.Q p ℓ x ω| + LocSum.Pz p x ℓ ω * (1 + M)) ^ 2 := by
    calc (SwarmMarks.hof p ω x) ^ 2 = |SwarmMarks.hof p ω x| ^ 2 := (sq_abs _).symm
      _ ≤ (|LocSum.Q p ℓ x ω| + LocSum.Pz p x ℓ ω * (1 + M)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine h2.trans ?_
  have := sq_abs_add_sq_le (LocSum.Q p ℓ x ω) (LocSum.Pz p x ℓ ω * (1 + M)) hBnn
  calc (|LocSum.Q p ℓ x ω| + LocSum.Pz p x ℓ ω * (1 + M)) ^ 2
      ≤ 2 * (LocSum.Q p ℓ x ω) ^ 2
        + 2 * (LocSum.Pz p x ℓ ω * (1 + M)) ^ 2 := this
    _ = 2 * (LocSum.Q p ℓ x ω) ^ 2 + 2 * (LocSum.Pz p x ℓ ω) ^ 2 * (1 + M) ^ 2 := by ring

end

end LocSumR1
