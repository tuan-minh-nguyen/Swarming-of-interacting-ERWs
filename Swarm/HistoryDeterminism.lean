/-
The used-coordinate history determines the recursive trajectory, its local times,
and its current right probabilities.
-/
import Swarm.HistoryCylinder

namespace Swarming.HistoryDeterminism

open Swarming Swarming.Model Swarming.Uniform Swarming.History

variable {N : ℕ}

lemma actualHistory_succ {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    actualHistory p m U (n + 1) = actualHistory p m U n ++
      List.ofFn (fun i : Fin N =>
        let c := Trajectory.departureCoord p m U n i
        (c, U c)) := by
  unfold actualHistory
  rw [List.range_succ, List.flatMap_append]
  simp

lemma history_event_old {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    {ω : Array N} (hω : ω ∈ historyEvent (actualHistory p m U (n + 1)))
    {r : Record N} (hr : r ∈ actualHistory p m U n) : ω r.1 = r.2 := by
  apply hω
  rw [actualHistory_succ]
  exact List.mem_append_left _ hr

lemma history_event_next {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    {ω : Array N} (hω : ω ∈ historyEvent (actualHistory p m U (n + 1))) (i : Fin N) :
    ω (Trajectory.departureCoord p m U n i) = U (Trajectory.departureCoord p m U n i) := by
  let c := Trajectory.departureCoord p m U n i
  let r : Record N := (c, U c)
  have hr : r ∈ actualHistory p m U (n + 1) := by
    rw [actualHistory_succ]
    apply List.mem_append_right
    apply List.mem_ofFn.mpr
    exact ⟨i, rfl⟩
  exact hω r hr

lemma state_ext {N : ℕ} {a b : Trajectory.WalkState N} (hp : a.pos = b.pos) (he : a.ell = b.ell) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Compatibility with the used-coordinate history at time `n` determines the full state there. -/
theorem trajectory_eq_of_history {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    ∀ (n : ℕ) {ω : Array N}, ω ∈ historyEvent (actualHistory p m U n) →
      Trajectory.trajectory p m ω n = Trajectory.trajectory p m U n := by
  intro n
  induction n with
  | zero => intro ω hω; rfl
  | succ n ih =>
      intro ω hω
      have hprev : Trajectory.trajectory p m ω n = Trajectory.trajectory p m U n :=
        ih (fun r hr => history_event_old p m U n hω hr)
      rw [Trajectory.trajectory_succ, Trajectory.trajectory_succ, hprev]
      unfold Trajectory.nextWalkState Trajectory.nextPos
      apply state_ext
      · funext i
        have hu := history_event_next p m U n hω i
        unfold Trajectory.departureCoord at hu
        exact congrArg (fun z => (Trajectory.trajectory p m U n).pos i +
          drivenStep z (rightProbability p m (Trajectory.trajectory p m U n).ell i
            ((Trajectory.trajectory p m U n).pos i))) hu
      · funext i x
        have hu := history_event_next p m U n hω i
        unfold Trajectory.departureCoord at hu
        have hpos_eq : Trajectory.nextPos p m ω (Trajectory.trajectory p m U n) i =
            Trajectory.nextPos p m U (Trajectory.trajectory p m U n) i := by
          unfold Trajectory.nextPos
          rw [hu]
        exact congrArg (fun z => (Trajectory.trajectory p m U n).ell i x +
          if x = z then 1 else 0) hpos_eq

lemma currentAlpha_eq_of_history {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    {ω : Array N} (hω : ω ∈ historyEvent (actualHistory p m U n)) (i : Fin N) :
    rightProbability p m (Trajectory.trajectory p m ω n).ell i ((Trajectory.trajectory p m ω n).pos i) =
      rightProbability p m (Trajectory.trajectory p m U n).ell i ((Trajectory.trajectory p m U n).pos i) := by
  rw [trajectory_eq_of_history p m U n hω]

end Swarming.HistoryDeterminism


