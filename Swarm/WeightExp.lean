/-
# The certificate series is finite for the paper's exponential profile

`Tightness.lean`'s `ProbCtx.tightness` needs one analytic input,
`∑' ℓ, (4Bℓ+1) p ℓ ≠ ⊤`: the total probability of a certificate, summed over all levels.
The paper's block estimate `(blkprob)` gives `p ℓ = C_T exp (-c_T ℓ^(1/16))`, and this file
discharges the input for that profile.

The profile hypothesis is a *pointwise domination*
`∀ ℓ, p ℓ ≤ ofReal (C exp (-c ℓ^(1/16)))`, not an equality `p = fun ℓ => …`: the block estimate
produces *some* bound `p` for the certificate probabilities, and a proof of tightness must accept
any `p` below the paper's profile.

The analytic ingredient is the elementary estimate "`exp` beats every polynomial": for `x ≥ 0`
and any `n`, `x^n / n! ≤ exp x`.  With `n = 48` and `x = c ℓ^(1/16)`,

  `exp (-c ℓ^(1/16)) ≤ 48! / (c^48 ℓ^3)`,

so `(4Bℓ+1) exp (-c ℓ^(1/16)) ≤ K / ℓ^2`, and `∑ 1/ℓ^2` converges.

All powers of a real base are annotated with `ℕ` exponents: `x ^ 48` at `x : ℝ` defaults to the
`rpow` instance, which would make the identities `(ℓ^(1/16))^48 = ℓ^3` and
`(c ℓ^(1/16))^48 = c^48 ℓ^3` non-definitional.
-/
import Swarm.Tightness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace RecordTight

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The certificate weight profile of the covering argument, as a real function. -/
noncomputable def expW (B : ℕ) (C cc : ℝ) (ℓ : ℕ) : ℝ :=
  (4 * (B : ℝ) * ℓ + 1) * (C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))))

lemma expW_nonneg (B : ℕ) {C cc : ℝ} (hC : 0 ≤ C) (ℓ : ℕ) : 0 ≤ expW B C cc ℓ := by
  have hexp : (0 : ℝ) ≤ Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))) := (Real.exp_pos _).le
  have hlin : (0 : ℝ) ≤ 4 * (B : ℝ) * ℓ + 1 := by positivity
  exact mul_nonneg hlin (mul_nonneg hC hexp)

/-- The exponent identity `(ℓ^(1/16))^48 = ℓ^3`. -/
lemma rpow_sixteenth_pow (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) :
    ((ℓ ^ ((1 : ℝ) / 16)) ^ (48 : ℕ)) = ℓ ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast (ℓ ^ ((1 : ℝ) / 16)) 48, ← Real.rpow_mul hℓ0]
  rw [show (1 : ℝ) / 16 * (((48 : ℕ)) : ℝ) = (((3 : ℕ)) : ℝ) by norm_num]
  rw [Real.rpow_natCast]

/-- `exp` beats the polynomial of degree `48` at the scale `ℓ^(1/16)`. -/
lemma exp_neg_rpow_le_fact {cc : ℝ} (hc : 0 < cc) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))) ≤
      ((48 : ℕ).factorial : ℝ) / (cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ)) := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  set t : ℝ := cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16) with ht
  have ht0 : 0 ≤ t := by positivity
  have hpow : t ^ (48 : ℕ) / ((48 : ℕ).factorial : ℝ) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t ht0 48
  have h48 : ((ℓ : ℝ) ^ ((1 : ℝ) / 16)) ^ (48 : ℕ) = (ℓ : ℝ) ^ (3 : ℕ) :=
    rpow_sixteenth_pow (ℓ : ℝ) (le_of_lt hℓ0)
  have ht48 : t ^ (48 : ℕ) = cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ) := by
    rw [ht, mul_pow, h48]
  rw [ht48] at hpow
  have h1 : 1 / Real.exp t ≤ 1 / ((cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ)) /
      ((48 : ℕ).factorial : ℝ)) := one_div_le_one_div_of_le (by positivity) hpow
  have h2 : 1 / ((cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ)) / ((48 : ℕ).factorial : ℝ)) =
      ((48 : ℕ).factorial : ℝ) / (cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ)) := by
    field_simp
  rw [h2] at h1
  rw [Real.exp_neg]
  simpa only [one_div] using h1

/-- Pointwise `ℓ^{-2}` bound for the profile. -/
lemma expW_le_invSq (B : ℕ) {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    expW B C cc ℓ ≤
      ((4 * (B : ℝ) + 1) * C * ((48 : ℕ).factorial : ℝ) / cc ^ (48 : ℕ)) *
        (1 / (ℓ : ℝ) ^ (2 : ℕ)) := by
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hexp := exp_neg_rpow_le_fact hc hℓ
  have hlin : 4 * (B : ℝ) * (ℓ : ℝ) + 1 ≤ (4 * (B : ℝ) + 1) * (ℓ : ℝ) := by nlinarith
  have hstep : expW B C cc ℓ ≤
      ((4 * (B : ℝ) + 1) * (ℓ : ℝ)) *
        (C * (((48 : ℕ).factorial : ℝ) / (cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ)))) := by
    refine mul_le_mul hlin (mul_le_mul_of_nonneg_left hexp hC) (by positivity) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- **The profile is stable under enlarging the level.**  If the level actually used by the block
estimate is `a ℓ` with `a ≥ 1` (for instance because the cover argument's levels are measured in
lattice units while the estimate is stated in half-units), the profile is only smaller, so the
pointwise domination hypothesis `hprof` still applies with the same constants. -/
lemma profile_le_of_one_le_mul {C cc a : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ cc) (ha : 1 ≤ a) (ℓ : ℕ) :
    C * Real.exp (-(cc * ((a * (ℓ : ℝ)) ^ ((1 : ℝ) / 16)))) ≤
      C * Real.exp (-(cc * ((ℓ : ℝ) ^ ((1 : ℝ) / 16)))) := by
  have hbase : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  have hmono : (ℓ : ℝ) ^ ((1 : ℝ) / 16) ≤ (a * (ℓ : ℝ)) ^ ((1 : ℝ) / 16) := by
    refine Real.rpow_le_rpow hbase (by nlinarith) (by norm_num)
  have hcc : -(cc * ((a * (ℓ : ℝ)) ^ ((1 : ℝ) / 16))) ≤
      -(cc * ((ℓ : ℝ) ^ ((1 : ℝ) / 16))) := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hcc) hC

/-- **The profile is stable under halving the level.**  This is the constant rescaling that the
half-distance convention of `RecState` (`dist2 y i = d_i / 2`) costs: the level `ℓ` in half-units
is the level `2ℓ` in the paper's lattice units, and `exp (-c (2ℓ)^(1/16))` is again of the form
`exp (-c' ℓ^(1/16))` with `c' = c * 2^(1/16)`. -/
lemma profile_two_mul {C cc : ℝ} (ℓ : ℕ) :
    C * Real.exp (-((cc * (2 : ℝ) ^ ((1 : ℝ) / 16)) * ((ℓ : ℝ) ^ ((1 : ℝ) / 16)))) =
      C * Real.exp (-(cc * (((2 : ℝ) * (ℓ : ℝ)) ^ ((1 : ℝ) / 16)))) := by
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  rw [Real.mul_rpow h2 hℓ]
  ring_nf

/-- **The certificate series is summable** for the paper's exponential profile. -/
theorem summable_expW (B : ℕ) {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc) :
    Summable (expW B C cc) := by
  have hbase : Summable (fun ℓ : ℕ =>
      ((4 * (B : ℝ) + 1) * C * ((48 : ℕ).factorial : ℝ) / cc ^ (48 : ℕ)) *
        (1 / (ℓ : ℝ) ^ (2 : ℕ))) := by
    have h : Summable (fun ℓ : ℕ => 1 / (ℓ : ℝ) ^ (2 : ℕ)) :=
      Real.summable_one_div_nat_pow.2 (by norm_num)
    exact h.mul_left _
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => expW_nonneg B hC (n + 1))
    (fun n => expW_le_invSq B hC hc (by omega)) ?_
  exact hbase.comp_injective (fun a b hab => by omega)

namespace ProbCtx

variable (c : ProbCtx Ω)

/-- **Finiteness of the certificate series for the paper's block estimate**, from a pointwise
domination of the certificate profile. -/
theorem weight_tsum_ne_top {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc)
    (hp : ∀ ℓ : ℕ, c.p ℓ ≤ ENNReal.ofReal (C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))))) :
    (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤ := by
  have hsum : Summable (expW c.B C cc) := summable_expW c.B hC hc
  have hw : ∀ ℓ : ℕ, c.w ℓ ≤ ENNReal.ofReal (expW c.B C cc ℓ) := by
    intro ℓ
    have hcast : ((4 * c.B * ℓ + 1 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((4 : ℝ) * (c.B : ℝ) * (ℓ : ℝ) + 1) := by
      rw [← ENNReal.ofReal_natCast (4 * c.B * ℓ + 1)]
      congr 1
      push_cast
      ring
    have h1 : c.w ℓ ≤ ENNReal.ofReal ((4 : ℝ) * (c.B : ℝ) * (ℓ : ℝ) + 1) *
        ENNReal.ofReal (C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16)))) := by
      rw [ProbCtx.w, hcast]
      gcongr
      exact hp ℓ
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    simp only [expW]
  have htail : ∑' ℓ : ℕ, ENNReal.ofReal (expW c.B C cc ℓ) =
      ENNReal.ofReal (∑' ℓ : ℕ, expW c.B C cc ℓ) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun ℓ => expW_nonneg c.B hC ℓ) hsum).symm
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hw)
  rw [htail]
  exact ENNReal.ofReal_ne_top

/-- **Tightness of the record distances for the paper's exponential block estimate.**  Only the
shape of the certificate profile is used; the block estimate itself enters through `hblk` of
`ProbCtx`, and `(recordo)` through `hterm` and `hR`. -/
theorem tightness_exp {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc)
    (hp : ∀ ℓ : ℕ, c.p ℓ ≤ ENNReal.ofReal (C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K' : ℕ, ∀ u : ℕ, c.μ {ω | K' < c.d ω u} ≤ ε :=
  fun ε hε => c.tightness (c.weight_tsum_ne_top hC hc hp) ε hε

end ProbCtx

end RecordTight


