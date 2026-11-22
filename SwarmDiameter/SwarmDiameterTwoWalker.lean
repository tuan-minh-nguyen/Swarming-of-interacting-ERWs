import SwarmDiameter.TwoWalkerTail
import SwarmDiameter.SwarmDiameterBounds

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- Theorem 1.2 for two walkers, with quadratic logarithmic growth and
square-root exponential tails. -/
theorem swarm_diameter_two_walker {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ (c C : ℝ) (ν : ProbabilityMeasure ℝ), 0 < c ∧ 1 ≤ C ∧
      (∀ᵐ U ∂arrayMeasure 2, ∀ᶠ n : ℕ in atTop,
        C⁻¹ * (Real.log (n : ℝ)) ^ (2 : ℕ) ≤ runningDiameter n (posPath p m U) ∧
          runningDiameter n (posPath p m U) ≤ C * (Real.log (n : ℝ)) ^ (2 : ℕ)) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution (fun n (U : Array 2) => pathDiameter n (posPath p m U))
        atTop (id : ℝ → ℝ) (fun _ => arrayMeasure 2) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / 2 : ℝ)) ≤ ν.toMeasure.real (Ici x) ∧
        ν.toMeasure.real (Ici x) ≤ Real.exp (-c * x ^ (1 / 2 : ℝ)) := by
  obtain ⟨B, T, C₀, L₀, hB, hT, _, _, K, a, hK, ha, hblock⟩ :=
    record_cubic_block_failure_le (N := 2) hp₀ hp₁ hm le_rfl
  obtain ⟨H, d, hH, hd, _, hW⟩ := record_interval_tails_le_of_block hp₀ hp₁ hm le_rfl
    hB hT hK.le ha (by norm_num : (0 : ℝ) < 1 / 3) hblock
  obtain ⟨c, hc, hE⟩ := record_two_walker_exceedance_limsup_le hp₀ hp₁ hm hH hd hW
  exact exists_diameter_bounds_of_record_tails hp₀ hp₁ hm le_rfl (β := 2)
    (by decide) (by simp) hc hd zero_le_one hH
    (by simpa only [Real.sqrt_eq_rpow, Nat.cast_ofNat, one_mul] using hE) hW

end Swarming.Diameter
