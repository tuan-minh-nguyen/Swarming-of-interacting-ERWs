/-
The local Azuma--Hoeffding estimate instantiated at the actual interacting law and at
its concrete uniform-array model.  This is a fixed-horizon estimate from time zero;
random record starts, the shifted-window version and the local profile are separate.
-/
import Swarm.LocMartRate
import Swarm.SwarmMart
import Swarm.ActualInstance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace LocMart

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0} {N : ℕ} {X : ℕ → Ω → Fin N → ℤ} {m : ℕ} {p : ℝ}

/-- Maximal local deviation of any martingale whose increments are bounded by two. -/
theorem measure_max_abs_psum_of_bounded_martingale {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (hbdd : ∀ k ω, |MartingaleLimit.inc Q k ω| ≤ 2)
    {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    μ.real {ω | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |psum (MartingaleLimit.inc Q) k ω|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) := by
  refine measure_max_abs_psum_locmart (μ := μ) (ℱ := ℱ)
    (ξ := MartingaleLimit.inc Q) (T := T) (L := L) ?_ hbdd
    (fun k => MartingaleLimit.condExp_inc_eq_zero hQ k) hT hL
  intro k
  exact (hQ.stronglyAdapted (k + 1)).sub
    ((hQ.stronglyAdapted k).mono (ℱ.mono (Nat.le_succ k)))

/-- The partial sum of `mart` increments is the centred position itself. -/
theorem measure_max_abs_mart_of_interactingLaw
    (hlaw : Swarm.IsInteractingLaw ℱ μ X m p) (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (i : Fin N) {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    μ.real {ω | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |Swarm.mart p X m k ω i|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) := by
  have hbound := measure_max_abs_psum_of_bounded_martingale
    (μ := μ) (ℱ := ℱ) (Q := fun k ω => Swarm.mart p X m k ω i)
    (SwarmHosc.mart_martingale hlaw i) (fun k ω => SwarmHosc.abs_mart_inc_le hlaw hp0 hp1 k i ω)
    hT hL
  have heq : {ω | ∃ k ≤ T * L,
      (L : ℝ) ^ (3 / 4 : ℝ) ≤ |psum (MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i)) k ω|} =
      {ω | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |Swarm.mart p X m k ω i|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    congr! 3 with k hk
    rw [show psum (MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i)) k ω =
      Swarm.mart p X m k ω i - Swarm.mart p X m 0 ω i by
        exact MartingaleLimit.sum_inc (fun k ω => Swarm.mart p X m k ω i) k ω,
      SwarmHosc.mart_zero hlaw i ω, sub_zero]
  rw [← heq]
  exact hbound

/-- The actual uniform-array trajectory has the local drift-martingale estimate,
unconditionally in the paper's parameter range. -/
theorem trajectory_measure_max_abs_mart {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m N : ℕ) (i : Fin N) {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    (Swarming.Uniform.arrayMeasure N).real {U | ∃ k ≤ T * L,
      (L : ℝ) ^ (3 / 4 : ℝ) ≤ |Swarm.mart p
        (fun t (U : Swarming.Uniform.Array N) =>
          (Swarming.Trajectory.trajectory p m U t).pos) m k U i|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) := by
  exact measure_max_abs_mart_of_interactingLaw
    (SwarmCross.Actual.actual_isInteractingLaw hp0 hp1 m) hp0.le hp1.le i hT hL

end LocMart


