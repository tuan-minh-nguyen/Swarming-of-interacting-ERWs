/-
  **The actual frozen crossing bound on the bad-position event.**

  This instantiates `frozen_cross_prob_le_R` with the verified enlarged-filtration revelation
  measurability and the bad-event domination of `Xtil`.  The conclusion concerns the modified
  process `Xtil` and the event `badPos`; it does not identify that event with the paper's full
  `BadTime`, whose `hitBefore` conjunct is handled separately.
-/
import Swarm.FrozenHdom

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

/-- **Crossing estimate for the actual modified frozen walk on `badPos`.**
No one-step law or revelation measurability remains a hypothesis: both are proved at the actual
uniform-array model. -/
theorem badPos_frozen_cross_prob_le_R (p : ℝ) (m : ℕ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (i j : Fin N) {b0 b1 s : ℕ} (hb : b0 < b1) (hij : i ≠ j) :
    (arrayMeasure N).real
      (exitBottomShift
        (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s}) b0 b1 s ∩
        {U : Array N | badPos p m U i j (b1 : ℤ) s}) ≤
      ∫ U in {U : Array N | badPos p m U i j (b1 : ℤ) s},
        R (revealedWF p m j s U) b0 b1 ∂(arrayMeasure N) := by
  have hA : MeasurableSet[enlFilt p m s] {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    measurableSet_badPos (N := N) p m s le_rfl i j (b1 : ℤ)
  have hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} →
      (trajectory p m U s).pos i = b1 :=
    Filter.Eventually.of_forall (fun _ hU => hU.1)
  refine frozen_cross_prob_le_R p m i j hp0 hp1 hb hA hstartA ?_ ?_
  · intro x
    exact measurable_revealedWeight_enlFilt p m s j (x : ℤ)
  · intro n hsn
    exact hdom_Xtil_bad p m hp0 hp1 i j hb hij hsn

end SwarmSpeed.Frozen

