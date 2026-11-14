import Swarm.SymmLetters
import Swarm.SymmCells

open MeasureTheory ProbabilityTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

namespace Swarming.FairWalk


/-- A letter is precisely a driving-sign pair at the two thresholds. -/
lemma letterSet_eq_cell (p : ℝ) (a b : Bool) :
    letterSet p (a, b) = cell p b a := by
  ext u
  simp only [letterSet, letter, Set.mem_setOf_eq, cell, Set.mem_inter_iff,
    mem_drvSet_iff, mem_sgnSet_iff, sv, Prod.mk.injEq]
  by_cases hu : 2 * u ≤ 1 <;> by_cases hp : u ≤ p <;> cases a <;> cases b <;>
    simp [hu, hp, drivenStep, symmetricStep] <;> linarith

/-- The four letter probabilities sum to one. -/
lemma letterLaw_sum (p : ℝ) : ∑ l : Bool × Bool, letterLaw p l = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [letterLaw, letterSet_eq_cell, Fintype.sum_bool]
  rw [cell_add, cell_add]
  simpa only [one_div] using ENNReal.inv_two_add_inv_two

end Swarming.FairWalk

--# both Bool with combined Shortcuts anyway.
