/-
The recursive interacting-walk trajectory driven by a countable uniform array,
and the freshness of the coordinate used at each departure.
-/
import Swarm.UniformArray
import Swarm.Swarming
import Swarm.LocalTime

namespace Swarming.Trajectory

open Swarming Swarming.Model Swarming.Uniform
open Finset

structure WalkState (N : ℕ) where
  pos : Fin N → ℤ
  ell : LocalTimes N

noncomputable def nextPos {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) : Fin N → ℤ :=
  fun i => s.pos i + drivenStep (U (i, s.pos i, s.ell i (s.pos i)))
    (rightProbability p m s.ell i (s.pos i))

noncomputable def nextWalkState {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) :
    WalkState N where
  pos := nextPos p m U s
  ell i x := s.ell i x + if x = nextPos p m U s i then 1 else 0

def initialWalkState {N : ℕ} : WalkState N where
  pos _ := 0
  ell _ x := if x = 0 then 1 else 0

noncomputable def trajectory {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) : ℕ → WalkState N
  | 0 => initialWalkState
  | n + 1 => nextWalkState p m U (trajectory p m U n)

@[simp] lemma initial_pos {N : ℕ} (i : Fin N) : (initialWalkState : WalkState N).pos i = 0 := rfl
@[simp] lemma trajectory_zero {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    trajectory p m U 0 = initialWalkState := rfl
@[simp] lemma trajectory_succ {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    trajectory p m U (n + 1) = nextWalkState p m U (trajectory p m U n) := rfl

lemma nextWalkState_pos {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (i : Fin N) :
    (nextWalkState p m U s).pos i = nextPos p m U s i := rfl

lemma nextWalkState_ell {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N)
    (i : Fin N) (x : ℤ) :
    (nextWalkState p m U s).ell i x = s.ell i x + if x = nextPos p m U s i then 1 else 0 := rfl

/-- The local times stored by the recursive state are exactly the path local times. -/
theorem ell_eq_localTime {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    ∀ (n : ℕ) (i : Fin N) (x : ℤ),
      (trajectory p m U n).ell i x = localTime (fun k => (trajectory p m U k).pos i) n x := by
  intro n
  induction n with
  | zero =>
      intro i x
      simp [initialWalkState, localTime_zero, eq_comm]
  | succ n ih =>
      intro i x
      rw [localTime_succ, trajectory_succ, nextWalkState_ell, nextWalkState_pos, ih]
      simp only [eq_comm]

/-- A visit at a strictly later time makes the local time strictly larger. -/
lemma localTime_lt_of_visit {σ : Type*} [DecidableEq σ] {X : ℕ → σ} {a b : ℕ}
    (hab : a < b) {x : σ} (hx : X b = x) : localTime X a x < localTime X b x := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2⟩
  · intro heq
    have hbmem : b ∈ (range (b + 1)).filter (fun k => X k = x) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self b), hx⟩
    have hnot : b ∉ (range (a + 1)).filter (fun k => X k = x) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro hba
      omega
    rw [← heq] at hbmem
    exact hnot hbmem

/-- The array coordinate governing departure `n` of walker `i`. -/
noncomputable def departureCoord {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    Fin N × ℤ × ℕ :=
  (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i))

/-- Every walker consumes a fresh coordinate at every departure. -/
theorem departureCoord_injective {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    Function.Injective (fun n => departureCoord p m U n i) := by
  intro a b hab
  have hpos := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) hab
  have hell := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
  change (trajectory p m U a).pos i = (trajectory p m U b).pos i at hpos
  change (trajectory p m U a).ell i ((trajectory p m U a).pos i) =
    (trajectory p m U b).ell i ((trajectory p m U b).pos i) at hell
  have hell_local : localTime (fun k => (trajectory p m U k).pos i) a ((trajectory p m U a).pos i) =
      localTime (fun k => (trajectory p m U k).pos i) b ((trajectory p m U b).pos i) := by
    rw [← ell_eq_localTime p m U a, ← ell_eq_localTime p m U b]
    exact hell
  rcases lt_trichotomy a b with hab' | rfl | hba
  · exfalso
    have hlt := localTime_lt_of_visit (X := fun k => (trajectory p m U k).pos i)
      (x := (trajectory p m U b).pos i) hab' rfl
    have heq : localTime (fun k => (trajectory p m U k).pos i) a ((trajectory p m U b).pos i) =
        localTime (fun k => (trajectory p m U k).pos i) b ((trajectory p m U b).pos i) := by
      simpa only [hpos] using hell_local
    exact (ne_of_lt hlt) heq
  · rfl
  · exfalso
    have hlt := localTime_lt_of_visit (X := fun k => (trajectory p m U k).pos i)
      (x := (trajectory p m U a).pos i) hba rfl
    have heq : localTime (fun k => (trajectory p m U k).pos i) a ((trajectory p m U a).pos i) =
        localTime (fun k => (trajectory p m U k).pos i) b ((trajectory p m U a).pos i) := by
      simpa only [← hpos] using hell_local
    exact (ne_of_gt hlt) heq

/-- Across all walkers and all departure times, no array coordinate is consumed twice. -/
theorem allDepartures_injective {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) :
    Function.Injective (fun q : Fin N × ℕ => departureCoord p m U q.2 q.1) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have hi : i = j := congrArg Prod.fst hab
  subst j
  have hab' : a = b := departureCoord_injective p m U i hab
  subst b
  rfl


/-- The auxiliary unbiased walk using exactly the same departure uniforms as the interacting walk. -/
noncomputable def symmetricWalk {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) : ℕ → ℤ
  | 0 => 0
  | n + 1 => symmetricWalk p m U i n + symmetricStep
      (U (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i)))

@[simp] lemma symmetricWalk_zero {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    symmetricWalk p m U i 0 = 0 := rfl

/-- The pointwise coupling used in the transience proof: the unbiased walk is always below
its interacting counterpart. -/
theorem symmetricWalk_le_trajectory {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N)
    (i : Fin N) : ∀ n, symmetricWalk p m U i n ≤ (trajectory p m U n).pos i := by
  intro n
  induction n with
  | zero => simp [symmetricWalk, trajectory, initialWalkState]
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_pos, nextPos]
      change symmetricWalk p m U i n + symmetricStep
        (U (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i))) ≤
        (trajectory p m U n).pos i + drivenStep
        (U (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i))
      have hstep := symmetricStep_le_model_step hp m (trajectory p m U n).ell i
        ((trajectory p m U n).pos i)
        (U (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i ((trajectory p m U n).pos i)))
      exact add_le_add ih hstep


end Swarming.Trajectory


namespace Swarming.Trajectory

open Swarming Swarming.Model Swarming.Uniform
open Finset
open scoped BigOperators

/-- Excitation of walker `i` at the current position of the interacting trajectory. -/
noncomputable def currentExcited {N : ℕ} (m : ℕ) {U : Array N} {p : ℝ} (n : ℕ) (i : Fin N) : ℕ := by
  classical
  exact if Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i) then 1 else 0

/-- Number of excited steps before time `n`. -/
noncomputable def excitedSteps {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) : ℕ :=
  ∑ t ∈ range n, currentExcited m (U := U) (p := p) t i

@[simp] lemma currentExcited_le_one {N : ℕ} (m : ℕ) {U : Array N} {p : ℝ} (n : ℕ) (i : Fin N) :
    currentExcited m (U := U) (p := p) n i ≤ 1 := by
  unfold currentExcited
  split <;> simp

lemma excitedSteps_le_time {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    excitedSteps p m U n i ≤ n := by
  have h := Finset.sum_le_card_nsmul (range n) (fun t => currentExcited m (U := U) (p := p) t i) 1
    (fun t _ => currentExcited_le_one m t i)
  simpa [excitedSteps] using h

/-- The drift-martingale centred position. -/
noncomputable def driftMartingale {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) : ℝ :=
  (trajectory p m U n).pos i - (2 * p - 1) * (excitedSteps p m U n i : ℝ)

/-- Elementary upper-speed decomposition: position = drift martingale + excited drift,
and the accumulated excited drift is at most `(2p-1)n`. -/
theorem pos_le_driftMartingale_add_time {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (U : Array N) (n : ℕ) (i : Fin N) :
    ((trajectory p m U n).pos i : ℝ) ≤ driftMartingale p m U n i + (2 * p - 1) * n := by
  have hc : (excitedSteps p m U n i : ℝ) ≤ n := by
    exact_mod_cast excitedSteps_le_time p m U n i
  have hcoef : 0 ≤ 2 * p - 1 := by linarith
  change (trajectory p m U n).pos i ≤
    driftMartingale p m U n i + (2 * p - 1) * n
  dsimp [driftMartingale]
  nlinarith

end Swarming.Trajectory


