/-
  **Chernoff form of the Gamma residue-class count tail.**

  Combining `TrialTail.count_tail` with the Bernoulli Hoeffding bound
  `(1-c) + c e^{-λ} ≤ e^{-cλ + λ²/4}` (valid for `0 ≤ c ≤ 1`, `|λ| ≤ 1`, proved here from
  Mathlib's `Real.abs_exp_sub_one_sub_id_le`) gives the exponential count tail with the
  exponent `-(Kc - j)²/K`.
-/
import Swarm.Imports
import Swarm.GammaTail

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace TrialTail

/-- Pointwise second-order bound: for `|x| ≤ 1`, `exp x ≤ 1 + x + x^2`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have h1 : Real.exp x - 1 - x ≤ x ^ 2 := (abs_le.1 h).2
  linarith

/-- **Bernoulli Hoeffding bound**: `(1-c) + c e^{-λ} ≤ e^{-cλ + λ²/4}` for `0 ≤ c ≤ 1`,
`|λ| ≤ 1`. -/
theorem scalar_bound {c lam : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hlam : |lam| ≤ 1) :
    (1 - c) + c * Real.exp (-lam) ≤ Real.exp (-(c * lam) + lam ^ 2 / 4) := by
  have habs1 : |lam * c| ≤ 1 := by
    rw [abs_mul]
    have h1 : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
    nlinarith [abs_nonneg lam, hlam, h1]
  have habs2 : |-(lam * (1 - c))| ≤ 1 := by
    rw [abs_neg, abs_mul]
    have h2 : |1 - c| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg lam, hlam, h2]
  have h1 : Real.exp (lam * c) ≤ 1 + (lam * c) + (lam * c) ^ 2 := exp_le_one_add_add_sq habs1
  have h2 : Real.exp (-(lam * (1 - c))) ≤ 1 + (-(lam * (1 - c))) + (-(lam * (1 - c))) ^ 2 :=
    exp_le_one_add_add_sq habs2
  have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - c)
  have e2 := mul_le_mul_of_nonneg_left h2 hc0
  have key : (1 - c) * Real.exp (lam * c) + c * Real.exp (-(lam * (1 - c)))
      ≤ 1 + lam ^ 2 * (c * (1 - c)) := by nlinarith [e1, e2]
  have hc4 : c * (1 - c) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * c - 1)]
  have key2 : (1 : ℝ) + lam ^ 2 * (c * (1 - c)) ≤ Real.exp (lam ^ 2 / 4) := by
    have hexp := Real.add_one_le_exp (lam ^ 2 / 4)
    have h4 : lam ^ 2 * (c * (1 - c)) ≤ lam ^ 2 / 4 := by nlinarith [sq_nonneg lam, hc4]
    linarith
  have hstep1 : Real.exp (-(lam * c)) * ((1 - c) * Real.exp (lam * c) + c * Real.exp (-(lam * (1 - c))))
      = (1 - c) + c * Real.exp (-lam) := by
    rw [mul_add]
    have h3 : Real.exp (-(lam * c)) * ((1 - c) * Real.exp (lam * c)) = (1 - c) := by
      rw [mul_comm (Real.exp (-(lam * c))) ((1 - c) * Real.exp (lam * c)), mul_assoc,
        ← Real.exp_add, show lam * c + -(lam * c) = 0 by ring, Real.exp_zero, mul_one]
    have h4 : Real.exp (-(lam * c)) * (c * Real.exp (-(lam * (1 - c)))) = c * Real.exp (-lam) := by
      rw [mul_comm (Real.exp (-(lam * c))) (c * Real.exp (-(lam * (1 - c)))), mul_assoc,
        ← Real.exp_add, show -(lam * (1 - c)) + -(lam * c) = -lam by ring]
    rw [h3, h4]
  have hstep2 : Real.exp (-(lam * c)) * Real.exp (lam ^ 2 / 4) = Real.exp (-(c * lam) + lam ^ 2 / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 - c) + c * Real.exp (-lam)
      = Real.exp (-(lam * c)) * ((1 - c) * Real.exp (lam * c) + c * Real.exp (-(lam * (1 - c)))) :=
        hstep1.symm
    _ ≤ Real.exp (-(lam * c)) * Real.exp (lam ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (key.trans key2) (Real.exp_pos _).le
    _ = Real.exp (-(c * lam) + lam ^ 2 / 4) := hstep2

end TrialTail

namespace Swarming.Enl

/-- **Exponential count tail on one residue class of the group record.**  With `t = K c - j ≥ 0`
and `t ≤ K/2`, the number of successful trials among the first `K` levels of the class is at
least `j = K c - t` except on a set of mass at most
`exp (-t²/K) + P(σ_{y_0} = ⊤) + P(σ_{y_K} = ⊤)`. -/
theorem gamma_count_tail_exp (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y0 : ℤ} (hy0 : 0 ≤ y0)
    (K j : ℕ) (hK : 0 < K) (hjc : (j : ℝ) ≤ (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card))
    (hthalf : (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) - j ≤ (K : ℝ) / 2) :
    arrayMeasure N {U : Array N | ((Finset.range K).filter
        (fun i => U ∈ GammaSet p m hA (lvl y0 m i))).card ≤ j}
      ≤ arrayMeasure N {U : Array N | sigmaA p m U hA (lvl y0 m 0) = ⊤}
        + ENNReal.ofReal (Real.exp (-((((K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) - j) ^ 2)
            / (K : ℝ))))
        + arrayMeasure N {U : Array N | sigmaA p m U hA (lvl y0 m K) = ⊤} := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set cr : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hcr
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcr0 : 0 ≤ cr := pow_nonneg h1mp _
  have hcr1 : cr ≤ 1 := pow_le_one₀ h1mp (by linarith)
  set t : ℝ := (K : ℝ) * cr - j with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [hjc]
  have htK : t ≤ (K : ℝ) / 2 := by rw [ht]; exact hthalf
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set lam : ℝ := 2 * t / K with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hKpos]
    linarith
  have hlamabs : |lam| ≤ 1 := abs_le.mpr ⟨by linarith, hlam1⟩
  -- the main numerical estimate
  have hmain : ((Real.exp (-lam)) ^ j)⁻¹ *
      (1 - cr + cr * Real.exp (-lam)) ^ K ≤ Real.exp (-(t ^ 2 / (K : ℝ))) := by
    have hρpos : 0 < Real.exp (-lam) := Real.exp_pos _
    have hR0 : 0 ≤ 1 - cr + cr * Real.exp (-lam) := by
      have := Real.exp_pos (-lam)
      nlinarith
    have hstep1 : ((Real.exp (-lam)) ^ j)⁻¹ = Real.exp ((j : ℝ) * lam) := by
      rw [Real.exp_nat_mul]
      have : Real.exp (-lam) = (Real.exp lam)⁻¹ := by rw [Real.exp_neg]
      rw [this, inv_pow, inv_inv]
    have hstep2 : (1 - cr + cr * Real.exp (-lam)) ^ K
        ≤ Real.exp ((K : ℝ) * (-(cr * lam) + lam ^ 2 / 4)) := by
      have hbase := TrialTail.scalar_bound hcr0 hcr1 hlamabs
      calc (1 - cr + cr * Real.exp (-lam)) ^ K
          ≤ (Real.exp (-(cr * lam) + lam ^ 2 / 4)) ^ K :=
            pow_le_pow_left₀ hR0 hbase K
        _ = Real.exp ((K : ℝ) * (-(cr * lam) + lam ^ 2 / 4)) := (Real.exp_nat_mul _ _).symm
    have hexp : ((j : ℝ) * lam) + (K : ℝ) * (-(cr * lam) + lam ^ 2 / 4) = -(t ^ 2 / (K : ℝ)) := by
      rw [hlam, ht]
      field_simp
      ring
    calc ((Real.exp (-lam)) ^ j)⁻¹ * (1 - cr + cr * Real.exp (-lam)) ^ K
        ≤ Real.exp ((j : ℝ) * lam) * Real.exp ((K : ℝ) * (-(cr * lam) + lam ^ 2 / 4)) := by
          rw [hstep1]
          exact mul_le_mul_of_nonneg_left hstep2 (Real.exp_pos _).le
      _ = Real.exp (-(t ^ 2 / (K : ℝ))) := by
          rw [← Real.exp_add, hexp]
  -- apply the algebraic count tail
  have hbase := gamma_count_tail p hp0 hp1 m A hA hy0 (Real.exp (-lam))
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) K j
  refine hbase.trans ?_
  have hle : (Real.exp (-lam) ^ j)⁻¹ * (1 - cr + cr * Real.exp (-lam)) ^ K
      ≤ Real.exp (-(t ^ 2 / (K : ℝ))) := hmain
  have : ENNReal.ofReal ((Real.exp (-lam) ^ j)⁻¹ *
      (1 - (1 - p) ^ ((2 * m - 1) * A.card)
        + (1 - p) ^ ((2 * m - 1) * A.card) * Real.exp (-lam)) ^ K)
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (K : ℝ)))) := ENNReal.ofReal_le_ofReal hle
  exact add_le_add (add_le_add (le_refl _) this) (le_refl _)

end Swarming.Enl
