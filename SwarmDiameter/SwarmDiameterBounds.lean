import SwarmDiameter.OccupationTail
import SwarmDiameter.SwarmLowerBounds
import SwarmDiameter.SwarmUpperGrowth

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- The bounds of Theorem 1.2 follow from the corresponding record-interval
exceedance bound and a cube-root bound on record-interval durations. -/
theorem exists_diameter_bounds_of_record_tails
    {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {β : ℕ} (hβ : 0 < β) (hβeq : (if N = 2 then 2 else if m < N then 1 else 3) = β)
    {a d K H : ℝ} (ha : 0 < a) (hd : 0 < d) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hE : ∀ᶠ x : ℝ in atTop, limsup (fun r => (arrayMeasure N).real
      {U | recordIntervalExceeds (posPath p m U) r x}) atTop ≤
        K * Real.exp (-a * x ^ (1 / (β : ℝ))))
    (hW : ∀ᶠ u : ℕ in atTop, limsup (fun r => (arrayMeasure N).real
      {U | (u : ℕ∞) < recordDuration (posPath p m U) r}) atTop ≤
        H * Real.exp (-d * (u : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ (c C : ℝ) (ν : ProbabilityMeasure ℝ), 0 < c ∧ 1 ≤ C ∧
      (∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
        C⁻¹ * (Real.log (n : ℝ)) ^ β ≤ runningDiameter n (posPath p m U) ∧
          runningDiameter n (posPath p m U) ≤ C * (Real.log (n : ℝ)) ^ β) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution (fun n (U : Array N) => pathDiameter n (posPath p m U))
        atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / (β : ℝ))) ≤ ν.toMeasure.real (Ici x) ∧
        ν.toMeasure.real (Ici x) ≤ Real.exp (-c * x ^ (1 / (β : ℝ))) := by
  obtain ⟨c, hc, hocc⟩ := eventually_regeneration_occupation_le_of_record_tails hp₀ hp₁ hm hN hβ
    ha hd hK hH hE hW
  obtain ⟨C₂, _, hupper⟩ := ae_log_pow_upper_of_regeneration_occupation hp₀ hp₁ hm hN hβ hc hocc
  obtain ⟨ν₂, _, hweak₂, htail₂⟩ :=
    exists_diameter_limit_with_upper_tail_of_regeneration_occupation hp₀ hp₁ hm hN hβ hc hocc
  have hlo := exists_diameter_lower_bounds (N := N) hp₀ hp₁ hm hN
  dsimp only at hlo
  rw [hβeq] at hlo
  obtain ⟨C₁, ν, hC₁, hlower, hnonneg, hweak, htail₁⟩ := hlo
  have hν : ν.toMeasure = ν₂.toMeasure := by
    simpa only [Measure.map_id] using tendstoInDistribution_unique _ hweak hweak₂
  let C := max C₁ C₂
  have h₁ : C₁ ≤ C := le_max_left _ _
  have h₂ : C₂ ≤ C := le_max_right _ _
  refine ⟨c / 2, C, ν, half_pos hc, hC₁.trans h₁, ?_, hnonneg, hweak, ?_⟩
  · filter_upwards [hlower, hupper] with U hU₁ hU₂
    filter_upwards [hU₁, hU₂, eventually_ge_atTop (1 : ℕ)] with n hn₁ hn₂ hn
    have hpow : 0 ≤ (Real.log (n : ℝ)) ^ β :=
      pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _
    have hi : C⁻¹ ≤ C₁⁻¹ := inv_anti₀ (zero_lt_one.trans_le hC₁) h₁
    exact ⟨(mul_le_mul_of_nonneg_right hi hpow).trans hn₁,
      hn₂.trans (mul_le_mul_of_nonneg_right h₂ hpow)⟩
  · filter_upwards [htail₁, htail₂, eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂ hx
    rw [← hν] at hx₂
    have hg := mul_le_mul_of_nonneg_right (neg_le_neg h₁) (Real.rpow_nonneg hx (1 / (β : ℝ)))
    exact ⟨(Real.exp_le_exp.mpr hg).trans hx₁, hx₂⟩

end Swarming.Diameter
