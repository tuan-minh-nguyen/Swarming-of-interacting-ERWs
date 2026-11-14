/-
Product identities for the next jump vector on exact finite coordinate histories.
-/
import Swarm.CurrentState

namespace Swarming.CurrentState

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Transition
open Swarming.History

variable {N : ℕ}

/-- The complete finite-coordinate history is a measurable cylinder. -/
lemma measurableSet_historyEvent {N : ℕ} (hs : List (Record N)) :
    MeasurableSet (historyEvent hs) := by
  rw [← preimage_compatible]
  exact (compatible_measurable hs).preimage
    (measurable_pi_iff.mpr fun j => measurable_pi_apply (j : Fin N × ℤ × ℕ))

/-- The prescribed next-jump event is the corresponding value of `nextJumpVec`. -/
lemma history_and_jumpEvent_eq {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (v : Fin N → Bool) :
    historyEvent (actualHistory p m U n) ∩ jumpEvent p m n v =
      historyEvent (actualHistory p m U n) ∩ {ω | nextJumpVec p m ω n = v} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_congr_right fun _ => jumpEvent_iff_nextJumpVec p m ω n v

/-- The complete-history law of the actual next jump vector, with capped-record weights. -/
theorem measure_history_nextJumpVec {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ {ω | nextJumpVec p m ω n = v}) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (SimJump.stepFactor p m (currentRecordState p m U n) i (v i)) := by
  rw [← history_and_jumpEvent_eq, conditional_jumpLaw hp0 hp1]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  cases hv : v i <;> simp [SimJump.stepFactor, jumpWeight, qRight_currentRecordState, hv]

/-- The same law in real-valued probability, without division by the history mass. -/
theorem measureReal_history_nextJumpVec {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    (arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω | nextJumpVec p m ω n = v})).toReal =
      (arrayMeasure N (historyEvent (actualHistory p m U n))).toReal *
        SimJump.stepW p m (currentRecordState p m U n) v := by
  rw [measure_history_nextJumpVec hp0 hp1, ENNReal.toReal_mul, ENNReal.toReal_prod,
    stepW_currentRecordState]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn := (SimJump.stepFactor_bounds p m (currentRecordState p m U n) i (v i)
    hp0.le hp1.le).1
  rw [ENNReal.toReal_ofReal hn]
  cases hv : v i <;> simp [SimJump.stepFactor, jumpWeight, qRight_currentRecordState, hv]

/-- Finite weighted sum normalized by the mass of an exact history event.
At a zero-mass history the value is zero. This expression alone is not a
conditional expectation with respect to the revealed sigma-algebra. -/
noncomputable def historyConditionalJumpMean {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (F : SimJump.JumpVec N → ℝ) : ℝ :=
  (arrayMeasure N (historyEvent (actualHistory p m U n))).toReal⁻¹ *
    ∑ v : SimJump.JumpVec N,
      (arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω | nextJumpVec p m ω n = v})).toReal * F v

/-- The finite normalized weighted sum of centred signed jumps is zero. -/
theorem history_conditional_centered_mean_zero {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    historyConditionalJumpMean p m U n (fun v =>
      (jumpShift (v i) : ℝ) - (2 * currentAlpha p m U n i - 1)) = 0 := by
  unfold historyConditionalJumpMean
  simp_rw [measureReal_history_nextJumpVec hp0 hp1]
  calc
    _ = (arrayMeasure N (historyEvent (actualHistory p m U n))).toReal⁻¹ *
        ((arrayMeasure N (historyEvent (actualHistory p m U n))).toReal *
          ∑ v : SimJump.JumpVec N, SimJump.stepW p m (currentRecordState p m U n) v *
            ((jumpShift (v i) : ℝ) - (2 * currentAlpha p m U n i - 1))) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = 0 := by
      rw [centered_currentRecordState_mean_zero]
      ring

/-- On a fibre of the next jump vector, the actual position increment is its prescribed
signed displacement and the current drift agrees with that of the conditioning history. -/
lemma centered_increment_on_history_fibre {N : ℕ} (p : ℝ) (m : ℕ) (U ω : Array N)
    (n : ℕ) (v : Fin N → Bool) (i : Fin N)
    (hω : ω ∈ historyEvent (actualHistory p m U n)) (hv : nextJumpVec p m ω n = v) :
    (((trajectory p m ω (n + 1)).pos i - (trajectory p m ω n).pos i : ℤ) : ℝ) -
        (2 * currentAlpha p m ω n i - 1) =
      (jumpShift (v i) : ℝ) - (2 * currentAlpha p m U n i - 1) := by
  have hα : currentAlpha p m ω n i = currentAlpha p m U n i := by
    unfold currentAlpha
    rw [HistoryDeterminism.trajectory_eq_of_history p m U n hω]
  rw [trajectory_succ, Trajectory.nextWalkState_pos, nextPos_eq_nextJumpVec, congrFun hv i, hα]
  push_cast
  ring

end Swarming.CurrentState


