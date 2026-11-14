import Swarm.SymmPattern
import Swarm.SymmTransport
import Swarm.MeasurableInc

/-!
Unconditional transport of the actual interacting auxiliary walk's finite sign law into the
finite-path reflection module.  These theorems concern only the auxiliary nearest-neighbour walk,
not the interacting speeds or regeneration itself.
-/

open MeasureTheory ProbabilityTheory Set Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

namespace Swarming.SymmTransport

/-- The integrated arbitrary-horizon sign law supplies `PathLawPattern`. -/
theorem pathLawPattern_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) :
    PathLawPattern p m i := by
  intro r σ hσ
  have h := Swarming.FairWalk.measure_symmInc_pattern p m r i σ
  rw [if_pos hσ] at h
  have hset : {U : Array N | ∀ k : Fin r, symmInc p m U i (k : ℕ) = σ k} =
      {U : Array N | ∀ k : Fin r, Swarming.FairWalk.symmInc p m U i (k : ℕ) = σ k} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hh k <;> exact hh k
  rw [hset]
  simpa [MeasureTheory.measureReal_def] using congrArg ENNReal.toReal h

/-- Measurability of the actual increment, supplied by finite countable pieces of its
trajectory recursion. -/
theorem incMeasurable_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : IncMeasurable p m i := by
  intro k
  change Measurable (fun U : Array N => Swarming.Fair.symmInc p m U i k)
  exact Swarming.Fair.measurable_symmInc p m i k

/-- The exact law for every finite set of Boolean sign paths. -/
theorem pathLawFinset_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) : PathLawFinset p m i :=
  pathLawFinset_of_pattern (pathLawPattern_actual p m i) (incMeasurable_actual p m i)

/-- **Non-hitting probability bound for the actual auxiliary walk**, with no stochastic
hypothesis left: almost every sign path places its running maximum in the same finite
reflection class as the unbiased nearest-neighbour walk. -/
theorem prob_nonhit_le_sqrt_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N)
    (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) :=
  prob_nonhit_le_sqrt_of_pattern (pathLawPattern_actual p m i) n hb

/-- Exact running-maximum mass of the actual auxiliary walk. -/
theorem prob_nonhit_eq_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) (b : ℤ) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, symmetricWalk p m U i k < b}
      = ((Finset.univ.filter (fun ω : Fin n → Bool => SwarmReflect.rmax ω n < b)).card : ℝ)
          / 2 ^ n :=
  prob_nonhit_eq (pathLawFinset_actual p m i) n b

/-- Exact first-hit mass, using the actual finite-path law and the finite-path reflection
bijection. -/
theorem prob_hit_eq_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) {b : ℤ} (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∃ k ≤ n, b ≤ symmetricWalk p m U i k}
      = (((Finset.univ.filter (fun ω : Fin n → Bool => b ≤ SwarmReflect.psum ω n)).card : ℝ)
          + ((Finset.univ.filter (fun ω : Fin n → Bool => b < SwarmReflect.psum ω n)).card : ℝ))
        / 2 ^ n :=
  prob_hit_eq (pathLawFinset_actual p m i) n hb

/-- Exact binomial endpoint law of the actual auxiliary walk. -/
theorem prob_endpoint_eq_choose_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N) (n j : ℕ) :
    (arrayMeasure N).real {U : Array N |
        symmetricWalk p m U i n = 2 * (j : ℤ) - (n : ℤ)}
      = (n.choose j : ℝ) / 2 ^ n :=
  prob_endpoint_eq_choose (pathLawFinset_actual p m i) n j

/-- Complementary probability of reaching the threshold, from the running-maximum bound. -/
theorem prob_hit_ge_one_sub_sqrt_actual {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N)
    (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    1 - (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1)
      ≤ (arrayMeasure N).real {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ symmetricWalk p m U i k} :=
  prob_hit_ge_one_sub_sqrt (pathLawFinset_actual p m i) n hb

end Swarming.SymmTransport


