import SwarmDiameter.RecordTailFromBlock
import SwarmDiameter.SwarmDiameterBounds

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- Theorem 1.2 for at least three walkers and a threshold at least the number
of walkers, with cubic logarithmic growth and cube-root exponential tails. -/
theorem swarm_diameter_cubic {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hN : 3 ≤ N) (hmN : N ≤ m) :
    ∃ (c C : ℝ) (ν : ProbabilityMeasure ℝ), 0 < c ∧ 1 ≤ C ∧
      (∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
        C⁻¹ * (Real.log (n : ℝ)) ^ (3 : ℕ) ≤ runningDiameter n (posPath p m U) ∧
          runningDiameter n (posPath p m U) ≤ C * (Real.log (n : ℝ)) ^ (3 : ℕ)) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution (fun n (U : Array N) => pathDiameter n (posPath p m U))
        atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / 3 : ℝ)) ≤ ν.toMeasure.real (Ici x) ∧
        ν.toMeasure.real (Ici x) ≤ Real.exp (-c * x ^ (1 / 3 : ℝ)) := by
  have hN₂ : 2 ≤ N := by omega
  have hm : 2 ≤ m := hN₂.trans hmN
  obtain ⟨B, T, C₀, L₀, hB, hT, _, _, K, c, hK, hc, hblock⟩ :=
    record_cubic_block_failure_le (N := N) hp₀ hp₁ hm hN₂
  obtain ⟨K', c', hK', hc', hE, hW⟩ := record_interval_tails_le_of_block hp₀ hp₁ hm hN₂
    hB hT hK.le hc (by norm_num : (0 : ℝ) < 1 / 3) hblock
  exact exists_diameter_bounds_of_record_tails hp₀ hp₁ hm hN₂ (β := 3) (by decide)
    (by rw [if_neg (by omega : N ≠ 2), if_neg (not_lt_of_ge hmN)]) hc' hc' hK' hK' hE hW

end Swarming.Diameter
