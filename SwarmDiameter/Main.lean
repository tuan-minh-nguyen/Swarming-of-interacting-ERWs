import SwarmDiameter.SwarmDiameterTwoWalker
import SwarmDiameter.SwarmDiameterLinear
import SwarmDiameter.SwarmDiameterCubic

open Filter MeasureTheory
open scoped Topology

theorem Swarming.swarm_diameter (N m : ℕ) (p : ℝ)
    (hN : 2 ≤ N) (hm : 2 ≤ m) (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) :
    letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    let β : ℕ := if N = 2 then 2 else if m < N then 1 else 3
    let Δ : ℕ → Swarming.Uniform.Array N → ℝ := fun n U =>
      (LeaderDescent.spreadZ
        (fun i j => (Swarming.Trajectory.trajectory p m U j).pos i) n : ℝ)
    ∃ (c C : ℝ) (ν : ProbabilityMeasure ℝ), 0 < c ∧ 1 ≤ C ∧
      (∀ᵐ U ∂Swarming.Uniform.arrayMeasure N, ∀ᶠ n in atTop,
        let M := (Finset.range (n + 1)).sup' (by simp) (fun j => Δ j U)
        C⁻¹ * (Real.log (n : ℝ)) ^ β ≤ M ∧ M ≤ C * (Real.log (n : ℝ)) ^ β) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution Δ atTop (id : ℝ → ℝ)
        (fun _ => Swarming.Uniform.arrayMeasure N) ν.toMeasure ∧
      (∀ᶠ x : ℝ in atTop,
        Real.exp (-C * x ^ (1 / (β : ℝ))) ≤ ν.toMeasure.real (Set.Ici x) ∧
          ν.toMeasure.real (Set.Ici x) ≤ Real.exp (-c * x ^ (1 / (β : ℝ)))) := by
  dsimp only
  by_cases h₂ : N = 2
  · subst N
    simpa only [if_true, Nat.cast_ofNat, Diameter.runningDiameter, Diameter.pathDiameter, SwarmRestart.posPath]
      using Swarming.Diameter.swarm_diameter_two_walker hp₀ hp₁ hm
  · let hn : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    by_cases hlt : m < N
    · simpa only [if_neg h₂, if_pos hlt, Diameter.runningDiameter, Diameter.pathDiameter, SwarmRestart.posPath]
        using @Swarming.Diameter.swarm_diameter_linear p m N hn hp₀ hp₁ hm hlt
    · simpa only [if_neg h₂, if_neg hlt, Nat.cast_ofNat, Diameter.runningDiameter, Diameter.pathDiameter,
        SwarmRestart.posPath] using @Swarming.Diameter.swarm_diameter_cubic p m N hn hp₀ hp₁
        (by omega : 3 ≤ N) (le_of_not_gt hlt)
