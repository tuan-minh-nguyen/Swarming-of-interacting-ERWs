import SwarmDiameter.RecordTailFromBlock
import SwarmDiameter.RecordLinearBlock
import SwarmDiameter.SwarmDiameterBounds

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- Theorem 1.2 when the threshold is strictly smaller than the population,
with logarithmic growth and exponential tails. -/
theorem swarm_diameter_linear {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hmN : m < N) :
    ∃ (c C : ℝ) (ν : ProbabilityMeasure ℝ), 0 < c ∧ 1 ≤ C ∧
      (∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
        C⁻¹ * (Real.log (n : ℝ)) ^ (1 : ℕ) ≤ runningDiameter n (posPath p m U) ∧
          runningDiameter n (posPath p m U) ≤ C * (Real.log (n : ℝ)) ^ (1 : ℕ)) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution (fun n (U : Array N) => pathDiameter n (posPath p m U))
        atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / ((1 : ℕ) : ℝ) : ℝ)) ≤ ν.toMeasure.real (Ici x) ∧
        ν.toMeasure.real (Ici x) ≤ Real.exp (-c * x ^ (1 / ((1 : ℕ) : ℝ) : ℝ)) := by
  have hN₂ : 2 ≤ N := hm.trans hmN.le
  obtain ⟨B, T, C₀, L₀, hB, hT, _, _, K, c, hK, hc, hblock⟩ :=
    record_linear_block_failure_le (N := N) hp₀ hp₁ hm hmN
  obtain ⟨K', c', hK', hc', hE, hW⟩ := record_interval_tails_le_of_block hp₀ hp₁ hm hN₂
    hB hT hK.le hc (γ := 1) (by norm_num) (by simpa only [Real.rpow_one] using hblock)
  exact exists_diameter_bounds_of_record_tails hp₀ hp₁ hm hN₂ (β := 1) (by decide)
    (by rw [if_neg (by omega : N ≠ 2), if_pos hmN]) hc' hc' hK' hK' (by simpa only [Nat.cast_one, div_one] using hE)
    (by
      filter_upwards [hW, eventually_ge_atTop (1 : ℕ)] with u hu h₁
      exact hu.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast h₁) (by norm_num : (1 / 3 : ℝ) ≤ 1)) (neg_nonpos.mpr hc'.le))) hK'))

end Swarming.Diameter
