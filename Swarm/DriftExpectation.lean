--
-- Signed-jump expectations under the simultaneous product law, and the
-- zero-mean centred increment used for the drift martingale.
import Swarm.TransitionLaw
import Swarm.SimJumpCore

namespace Swarming.DriftExpectation

open Finset
open Swarming.Transition

variable {N m : ℕ}

noncomputable def jointRightMean (p : ℝ) (s : SimJump.State N m) (i : Fin N) : ℝ :=
  ∑ v : SimJump.JumpVec N, (if v i = true then (1 : ℝ) else 0) * SimJump.stepW p m s v

noncomputable def jointLeftMean (p : ℝ) (s : SimJump.State N m) (i : Fin N) : ℝ :=
  ∑ v : SimJump.JumpVec N, (if v i = false then (1 : ℝ) else 0) * SimJump.stepW p m s v

lemma jointRightMean_eq (p : ℝ) (s : SimJump.State N m) (i : Fin N) :
    jointRightMean p s i = SimJump.qRight p m s i := by
  exact SimJump.stepW_marginal p m s i

lemma jointLeftMean_eq_one_sub (p : ℝ) (s : SimJump.State N m) (i : Fin N) :
    jointLeftMean p s i = 1 - SimJump.qRight p m s i := by
  have hsum : jointLeftMean p s i + jointRightMean p s i = 1 := by
    rw [← SimJump.stepW_sum_one p m s]
    unfold jointLeftMean jointRightMean
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    cases hvi : v i <;> simp [hvi]
  have hright := jointRightMean_eq p s i
  calc
    jointLeftMean p s i = (jointLeftMean p s i + jointRightMean p s i) - jointRightMean p s i := by ring
    _ = 1 - SimJump.qRight p m s i := by rw [hsum, hright]

-- The mean of the signed jump `+1/-1` under the product law.
noncomputable def jointSignedMean (p : ℝ) (s : SimJump.State N m) (i : Fin N) : ℝ :=
  ∑ v : SimJump.JumpVec N, SimJump.stepW p m s v * (jumpShift (v i) : ℝ)

lemma jointSignedMean_eq (p : ℝ) (s : SimJump.State N m) (i : Fin N) :
    jointSignedMean p s i = 2 * SimJump.qRight p m s i - 1 := by
  calc
    jointSignedMean p s i = jointRightMean p s i - jointLeftMean p s i := by
      unfold jointSignedMean jointRightMean jointLeftMean
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      cases hvi : v i <;> simp [jumpShift, hvi]
    _ = SimJump.qRight p m s i - (1 - SimJump.qRight p m s i) := by
      rw [jointRightMean_eq, jointLeftMean_eq_one_sub]
    _ = 2 * SimJump.qRight p m s i - 1 := by ring

-- Subtracting the conditional drift gives a zero-mean centred increment.
theorem centered_joint_increment_mean_zero (p : ℝ) (s : SimJump.State N m) (i : Fin N) :
    ∑ v : SimJump.JumpVec N, SimJump.stepW p m s v *
      ((jumpShift (v i) : ℝ) - (2 * SimJump.qRight p m s i - 1)) = 0 := by
  have hdecomp :
      (∑ v : SimJump.JumpVec N, SimJump.stepW p m s v *
        ((jumpShift (v i) : ℝ) - (2 * SimJump.qRight p m s i - 1))) =
      jointSignedMean p s i - (2 * SimJump.qRight p m s i - 1) *
        ∑ v : SimJump.JumpVec N, SimJump.stepW p m s v := by
    rw [Finset.mul_sum]
    unfold jointSignedMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hdecomp, jointSignedMean_eq, SimJump.stepW_sum_one p m s]
  ring

end Swarming.DriftExpectation


