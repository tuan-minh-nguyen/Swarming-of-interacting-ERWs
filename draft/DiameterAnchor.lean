import Swarm.LeaderDescent
import Swarm.Trajectory
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

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
  sorry
