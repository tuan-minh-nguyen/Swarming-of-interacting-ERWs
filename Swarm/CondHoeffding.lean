/-
Conditional Hoeffding lemma (Mathlib gap).

`results/lean/areas/martingale/README.md` records, as *the* missing ingredient of the paper's
maximal Azuma--Hoeffding step (Proposition `local`, display `(locmart)`):

> (i) a **conditional Hoeffding lemma** — `HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (ΔQ_n) (c_n²) μ`
> from `|ΔQ_n| ≤ c_n` and `E[ΔQ_n | ℱ_n] = 0` (Mathlib only has the unconditional
> `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`).

This file supplies that lemma in the form actually needed downstream: an explicit almost-sure
bound on the conditional moment generating function of a bounded random variable with vanishing
conditional mean.  The constant is the crude but dimensionally correct `exp (t^2 c^2)`
(sharp Hoeffding would give `exp (t^2 c^2 / 2)`); the crude constant only costs an absolute
factor in the exponent, which the paper's `C_T e^{-c_T L^{1/16}}` bounds absorb.

Proof: for `|y| ≤ c` and `|t| c ≤ 1` the second-order Taylor bound
`exp (t*y) ≤ 1 + t*y + t^2*c^2` holds; taking conditional expectations, the linear term
vanishes by the vanishing conditional mean and `1 + t^2*c^2 ≤ exp (t^2*c^2)`.
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LocMart

/-- Pointwise second-order Taylor bound: for `|x| ≤ 1`, `exp x ≤ 1 + x + x^2`. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have h1 : Real.exp x - 1 - x ≤ x ^ 2 := (abs_le.1 h).2
  linarith

/-- **Conditional Hoeffding lemma.**  Let `Y` be almost surely bounded by `c ≥ 0` and have
vanishing conditional mean given a σ-algebra `m`.  Then for every real `t` with `|t| * c ≤ 1`
the conditional moment generating function of `Y` is bounded by `exp (t^2 * c^2)`. -/
theorem condExp_exp_mul_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {Y : Ω → ℝ} {c t : ℝ} (hc : 0 ≤ c) (htc : |t| * c ≤ 1)
    (hY : AEMeasurable Y μ) (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ c)
    (hmean : μ[Y | m] =ᵐ[μ] 0) :
    μ[fun ω => Real.exp (t * Y ω) | m] ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c ^ 2) := by
  letI : MeasurableSpace Ω := m0
  have hYm : AEStronglyMeasurable Y μ := hY.aestronglyMeasurable
  have hYint : Integrable Y μ := by
    refine Integrable.of_bound hYm c ?_
    filter_upwards [hb] with ω hω using hω
  have hsq_le : ∀ᵐ ω ∂μ, |Y ω| ^ 2 ≤ c ^ 2 := by
    filter_upwards [hb] with ω hω
    simpa using pow_le_pow_left₀ (abs_nonneg _) hω 2
  -- pointwise second-order bound
  have hbd : ∀ᵐ ω ∂μ, Real.exp (t * Y ω) ≤ 1 + t * Y ω + t ^ 2 * c ^ 2 := by
    filter_upwards [hb, hsq_le] with ω hω hω2
    have h1 : |t * Y ω| ≤ 1 := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hω (abs_nonneg t)) htc
    have h2 : (t * Y ω) ^ 2 ≤ t ^ 2 * c ^ 2 := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
      simpa [sq_abs] using hω2
    have h3 := exp_le_one_add_add_sq h1
    linarith
  have hbnd_exp : ∀ᵐ ω ∂μ, |Real.exp (t * Y ω)| ≤ Real.exp 1 := by
    filter_upwards [hb] with ω hω
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc t * Y ω ≤ |t * Y ω| := le_abs_self _
      _ = |t| * |Y ω| := abs_mul t _
      _ ≤ |t| * c := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
      _ ≤ 1 := htc
  have hexpint : Integrable (fun ω => Real.exp (t * Y ω)) μ := by
    refine Integrable.of_bound ?_ (Real.exp 1) hbnd_exp
    exact Real.continuous_exp.comp_aestronglyMeasurable (hYm.const_mul t)
  have haffint : Integrable (fun ω => 1 + t * Y ω + t ^ 2 * c ^ 2) μ := by
    have h1 : Integrable (fun ω => t * Y ω) μ := hYint.const_mul t
    have h2 : Integrable (fun ω => t * Y ω + (1 + t ^ 2 * c ^ 2)) μ :=
      h1.add (integrable_const _)
    have h3 : (fun ω => t * Y ω + (1 + t ^ 2 * c ^ 2))
        = fun ω => 1 + t * Y ω + t ^ 2 * c ^ 2 := by
      funext ω; ring
    rw [h3] at h2
    exact h2
  have hmono : μ[fun ω => Real.exp (t * Y ω) | m]
      ≤ᵐ[μ] μ[fun ω => 1 + t * Y ω + t ^ 2 * c ^ 2 | m] :=
    condExp_mono hexpint haffint hbd
  -- conditional expectation of the affine function
  have hpull : μ[(fun _ => t) * Y | m] =ᵐ[μ] (fun _ => t) * μ[Y | m] :=
    condExp_mul_of_aestronglyMeasurable_left aestronglyMeasurable_const
      (by
        have hmul : ((fun _ => t) * Y) = fun ω => t * Y ω := rfl
        rw [hmul]
        exact hYint.const_mul t) hYint
  have hce : μ[fun ω => 1 + t ^ 2 * c ^ 2 + t * Y ω | m]
      =ᵐ[μ] fun _ => 1 + t ^ 2 * c ^ 2 := by
    have hsplit : (fun ω => 1 + t ^ 2 * c ^ 2 + t * Y ω)
        = (fun _ => 1 + t ^ 2 * c ^ 2) + ((fun _ => t) * Y) := by
      funext ω; simp
    rw [hsplit]
    refine (condExp_add (integrable_const (1 + t ^ 2 * c ^ 2))
      (by
        have hmul : ((fun _ => t) * Y) = fun ω => t * Y ω := rfl
        rw [hmul]
        exact hYint.const_mul t) (m : MeasurableSpace Ω)).trans ?_
    rw [condExp_const (μ := μ) hm (1 + t ^ 2 * c ^ 2)]
    filter_upwards [hpull, hmean] with ω h1 h2
    simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2]
    ring
  have hsq : μ[fun ω => 1 + t * Y ω + t ^ 2 * c ^ 2 | m]
      =ᵐ[μ] fun _ => 1 + t ^ 2 * c ^ 2 := by
    have heq : (fun ω => 1 + t * Y ω + t ^ 2 * c ^ 2)
        = fun ω => 1 + t ^ 2 * c ^ 2 + t * Y ω := by
      funext ω; ring
    rw [heq]
    exact hce
  have hstep : (fun _ : Ω => 1 + t ^ 2 * c ^ 2) ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c ^ 2) :=
    Filter.Eventually.of_forall fun _ => by
      simpa [add_comm] using Real.add_one_le_exp (t ^ 2 * c ^ 2)
  exact hmono.trans (Filter.EventuallyEq.le hsq |>.trans hstep)

end LocMart
