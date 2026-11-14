/-
The capped record state associated with a recursive trajectory state.
-/
import Swarm.DriftExpectation

namespace Swarming.CurrentState

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Transition

variable {N : ℕ}

/-- The capped state corresponding to the current trajectory state. -/
noncomputable def currentRecordState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    SimJump.State N m where
  pos := (trajectory p m U n).pos
  eta i x := min ((trajectory p m U n).ell i x) m
  hcap _ _ := min_le_right _ _

lemma otherVisits_erase_eq {N m : ℕ} (s : SimJump.State N m) (i : Fin N) :
    SimJump.otherVisits s i = Model.otherVisits (fun j x => s.eta j x) i (s.pos i) := by
  classical
  unfold SimJump.otherVisits Model.otherVisits
  simp only [Finset.sum_ite]
  have hset : Finset.univ.erase i = Finset.univ.filter (fun j => ¬j = i) := by
    ext j
    simp
  rw [hset]
  simp only [Finset.sum_const_zero, zero_add]

lemma qRight_currentRecordState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    SimJump.qRight p m (currentRecordState p m U n) i = currentAlpha p m U n i := by
  classical
  unfold SimJump.qRight currentAlpha rightProbability currentRecordState
  rw [otherVisits_erase_eq]
  change (if m ≤ Model.otherVisits (fun j y => min ((trajectory p m U n).ell j y) m)
      i ((trajectory p m U n).pos i) then p else 1 / 2) =
    (if Model.Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i)
      then p else 1 / 2)
  by_cases hc : m ≤ Model.otherVisits (fun j y => min ((trajectory p m U n).ell j y) m)
      i ((trajectory p m U n).pos i)
  · have he : Model.Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i) :=
      (Model.excited_capped_iff m (trajectory p m U n).ell i
        ((trajectory p m U n).pos i)).mpr hc
    simp only [hc, he, if_true]
  · have he : ¬Model.Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i) :=
      fun h => hc ((Model.excited_capped_iff m (trajectory p m U n).ell i
        ((trajectory p m U n).pos i)).mp h)
    simp only [hc, he, if_false]


lemma stepW_currentRecordState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (v : Fin N → Bool) :
    SimJump.stepW p m (currentRecordState p m U n) v =
      ∏ i, jumpWeight (v i) (currentAlpha p m U n i) := by
  unfold SimJump.stepW
  apply Finset.prod_congr rfl
  intro i hi
  cases hvi : v i <;> simp [jumpWeight, qRight_currentRecordState]

/-- The Boolean vector of jumps actually taken from the uniform array. -/
noncomputable def nextJumpVec {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    SimJump.JumpVec N := fun i =>
  if U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i then true else false

lemma nextJumpVec_true_iff {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    nextJumpVec p m U n i = true ↔
      U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i := by
  by_cases h : U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i
  · simp [nextJumpVec, h]
  · simp [nextJumpVec, h]

lemma nextPos_eq_nextJumpVec {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    Trajectory.nextPos p m U (trajectory p m U n) i =
      (trajectory p m U n).pos i + jumpShift (nextJumpVec p m U n i) := by
  by_cases hv : nextJumpVec p m U n i = true
  · rw [hv]
    have h := (nextJumpVec_true_iff p m U n i).mp hv
    simp only [jumpShift, if_true]
    unfold Trajectory.nextPos
    change (trajectory p m U n).pos i +
      (if U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i then (1 : ℤ) else -1) =
        (trajectory p m U n).pos i + 1
    rw [if_pos h]
  · have hv' : nextJumpVec p m U n i = false := by
      cases hval : nextJumpVec p m U n i <;> simp_all
    rw [hv']
    have h : ¬U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i :=
      fun h => hv ((nextJumpVec_true_iff p m U n i).mpr h)
    simp only [jumpShift, Bool.false_eq_true, if_false]
    unfold Trajectory.nextPos
    change (trajectory p m U n).pos i +
      (if U (Trajectory.departureCoord p m U n i) ≤ currentAlpha p m U n i then (1 : ℤ) else -1) =
        (trajectory p m U n).pos i + -1
    rw [if_neg h]

lemma jumpEvent_iff_nextJumpVec {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (v : Fin N → Bool) :
    U ∈ jumpEvent p m n v ↔ nextJumpVec p m U n = v := by
  constructor
  · intro h
    funext i
    have hi : (trajectory p m U n).pos i + jumpShift (nextJumpVec p m U n i) =
        (trajectory p m U n).pos i + jumpShift (v i) := by
      rw [← nextPos_eq_nextJumpVec]
      simpa only [trajectory_succ, Trajectory.nextWalkState_pos] using h i
    cases hvi : v i <;> cases hni : nextJumpVec p m U n i <;>
      simp [hvi, hni, jumpShift] at hi ⊢
  · intro h
    subst v
    intro i
    rw [trajectory_succ, Trajectory.nextWalkState_pos, nextPos_eq_nextJumpVec]

lemma recordState_ext {N m : ℕ} {s t : SimJump.State N m}
    (hp : s.pos = t.pos) (he : s.eta = t.eta) : s = t := by
  cases s
  cases t
  simp_all

lemma stepPos_nextJumpVec {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    SimJump.stepPos (currentRecordState p m U n) (nextJumpVec p m U n) i =
      Trajectory.nextPos p m U (trajectory p m U n) i := by
  rw [nextPos_eq_nextJumpVec]
  cases hv : nextJumpVec p m U n i <;>
    simp [SimJump.stepPos, jumpShift, hv, currentRecordState]

/-- The next capped record state is the simultaneous-jump update of the current one. -/
theorem step_currentRecordState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    SimJump.step m (currentRecordState p m U n) (nextJumpVec p m U n) =
      currentRecordState p m U (n + 1) := by
  apply recordState_ext
  · funext i
    exact stepPos_nextJumpVec p m U n i
  · funext i x
    change (if x = SimJump.stepPos (currentRecordState p m U n) (nextJumpVec p m U n) i then
        min (min ((trajectory p m U n).ell i x) m + 1) m
      else min ((trajectory p m U n).ell i x) m) =
      min ((trajectory p m U n).ell i x +
        if x = Trajectory.nextPos p m U (trajectory p m U n) i then 1 else 0) m
    rw [← stepPos_nextJumpVec]
    by_cases hx : x = SimJump.stepPos (currentRecordState p m U n) (nextJumpVec p m U n) i
    · simp only [hx, if_true]
      omega
    · simp [hx]

/-- The signed conditional mean on the current trajectory state is its current drift. -/
theorem jointSignedMean_currentRecordState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N)
    (n : ℕ) (i : Fin N) :
    DriftExpectation.jointSignedMean p (currentRecordState p m U n) i =
      2 * currentAlpha p m U n i - 1 := by
  rw [DriftExpectation.jointSignedMean_eq, qRight_currentRecordState]

/-- Centring by the current drift gives zero mean for the actual trajectory state. -/
theorem centered_currentRecordState_mean_zero {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N)
    (n : ℕ) (i : Fin N) :
    ∑ v : SimJump.JumpVec N, SimJump.stepW p m (currentRecordState p m U n) v *
      ((jumpShift (v i) : ℝ) - (2 * currentAlpha p m U n i - 1)) = 0 := by
  simpa only [qRight_currentRecordState] using
    DriftExpectation.centered_joint_increment_mean_zero p (currentRecordState p m U n) i

end Swarming.CurrentState


