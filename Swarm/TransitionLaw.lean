/-
Product identities on fixed finite coordinate histories of the interacting walks.
-/
import Swarm.HistoryCylinder
import Swarm.HistoryDeterminism

namespace Swarming.Transition

open MeasureTheory Set Swarming Swarming.Model Swarming.Uniform Swarming.History

variable {N : ℕ}

/-- Current right probability of walker `i` at its current position. -/
noncomputable def currentAlpha {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) : ℝ :=
  rightProbability p m (Trajectory.trajectory p m U n).ell i ((Trajectory.trajectory p m U n).pos i)

/-- The event decided by one jump: right iff `U ≤ α`, left iff `U > α`. -/
noncomputable def jumpSet (b : Bool) (α : ℝ) : Set ℝ := if b = true then Iic α else Ioi α

/-- Its probability: `α` for a right jump and `1-α` for a left jump. -/
noncomputable def jumpWeight (b : Bool) (α : ℝ) : ℝ := if b = true then α else 1 - α

lemma currentAlpha_pos {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (_hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) : 0 < currentAlpha p m U n i := by
  unfold currentAlpha rightProbability
  split
  · exact lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hp0
  · norm_num

lemma currentAlpha_lt_one {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) : currentAlpha p m U n i < 1 := by
  unfold currentAlpha rightProbability
  split
  · exact hp1
  · norm_num

lemma jumpSet_measurable (b : Bool) (α : ℝ) : MeasurableSet (jumpSet b α) := by
  cases b <;> simp [jumpSet, measurableSet_Iic, measurableSet_Ioi]

lemma uniform01_jumpSet {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (b : Bool) :
    uniform01 (jumpSet b α) = ENNReal.ofReal (jumpWeight b α) := by
  cases b <;> simp [jumpSet, jumpWeight, uniform01_Iic hα0 hα1, uniform01_Ioi hα0 hα1]

/-- One-unit displacement of a Boolean jump. -/
def jumpShift (b : Bool) : ℤ := if b = true then 1 else -1

/-- Simultaneous event of a prescribed jump vector, evaluated on the random array. -/
noncomputable def jumpEvent {N : ℕ} (p : ℝ) (m : ℕ) (n : ℕ) (v : Fin N → Bool) :
    Set (Array N) :=
  {ω | ∀ i, (Trajectory.trajectory p m ω (n + 1)).pos i =
    (Trajectory.trajectory p m ω n).pos i + jumpShift (v i)}

lemma nextPos_eq_iff {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (v : Fin N → Bool) (i : Fin N) :
    Trajectory.nextPos p m U (Trajectory.trajectory p m U n) i =
      (Trajectory.trajectory p m U n).pos i + jumpShift (v i) ↔
      U (Trajectory.departureCoord p m U n i) ∈ jumpSet (v i) (currentAlpha p m U n i) := by
  cases hvi : v i
  · simp [Trajectory.nextPos, jumpSet, currentAlpha, drivenStep, jumpShift, Trajectory.departureCoord]
  · simp [Trajectory.nextPos, jumpSet, currentAlpha, drivenStep, jumpShift, Trajectory.departureCoord]

lemma jumpEvent_history_eq_inter {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (v : Fin N → Bool) {ω : Array N} :
    ω ∈ historyEvent (actualHistory p m U n) ∩ jumpEvent p m n v ↔
      ω ∈ historyEvent (actualHistory p m U n) ∩ ⋂ i,
        (fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹'
          jumpSet (v i) (currentAlpha p m U n i) := by
  constructor
  · rintro ⟨hHist, hJ⟩
    refine ⟨hHist, Set.mem_iInter.mpr (fun i => ?_)⟩
    have hα : currentAlpha p m ω n i = currentAlpha p m U n i := by
      simpa only [currentAlpha] using HistoryDeterminism.currentAlpha_eq_of_history p m U n hHist i
    have hi : Trajectory.nextPos p m ω (Trajectory.trajectory p m ω n) i =
        (Trajectory.trajectory p m ω n).pos i + jumpShift (v i) := by
      simpa only [Trajectory.trajectory_succ, Trajectory.nextWalkState_pos] using hJ i
    have hi' := (nextPos_eq_iff p m ω n v i).mp hi
    rw [hα] at hi'
    have hc : Trajectory.departureCoord p m ω n i = Trajectory.departureCoord p m U n i := by
      unfold Trajectory.departureCoord
      rw [HistoryDeterminism.trajectory_eq_of_history p m U n hHist]
    rw [hc] at hi'
    simpa only [Set.mem_preimage] using hi'
  · rintro ⟨hHist, hJ⟩
    refine ⟨hHist, fun i => ?_⟩
    have hα : currentAlpha p m ω n i = currentAlpha p m U n i := by
      simpa only [currentAlpha] using HistoryDeterminism.currentAlpha_eq_of_history p m U n hHist i
    have hi' := nextPos_eq_iff p m ω n v i
    have hJi := Set.mem_iInter.mp hJ i
    rw [← hα] at hJi
    have hc : Trajectory.departureCoord p m ω n i = Trajectory.departureCoord p m U n i := by
      unfold Trajectory.departureCoord
      rw [HistoryDeterminism.trajectory_eq_of_history p m U n hHist]
    rw [← hc] at hJi
    simpa only [Trajectory.trajectory_succ, Trajectory.nextWalkState_pos, Set.mem_preimage] using hi'.mpr hJi

/-- Product identity on the event of one exact coordinate/value history.
For a nonempty history this event has probability zero. For conditional laws
with respect to the revealed sigma-algebra, see `Swarming.Enl.enl_fresh_law`
and `Swarming.Enl.condExp_pattern_enl`. -/
theorem conditional_jumpLaw {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ jumpEvent p m n v) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
  rw [Set.ext fun _ => jumpEvent_history_eq_inter p m U n v]
  calc
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ ⋂ i,
        (fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹'
          jumpSet (v i) (currentAlpha p m U n i)) =
        arrayMeasure N (historyEvent (actualHistory p m U n)) *
          ∏ i, arrayMeasure N ((fun ω : Array N => ω (Trajectory.departureCoord p m U n i)) ⁻¹'
            jumpSet (v i) (currentAlpha p m U n i)) := by
              exact measure_actualHistory_and_next_sets p m U n _ (fun i => jumpSet_measurable _ _)
    _ = arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hmap := arrayMeasure_preimage_set N (Trajectory.departureCoord p m U n i)
        (jumpSet (v i) (currentAlpha p m U n i)) (jumpSet_measurable _ _)
      exact hmap.trans (uniform01_jumpSet (currentAlpha_pos hp0 hp1 m U n i)
        (currentAlpha_lt_one hp0 hp1 m U n i) (v i))

end Swarming.Transition

