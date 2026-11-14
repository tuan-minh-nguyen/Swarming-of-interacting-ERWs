/-
# Law of the future from a translated state

`SwarmRestart.restart_agreement_aux` says: two states that agree above a level `d`
(`ShiftAgree d s s'`), the first one at or above `d`, keep agreeing above `d` as long as the
first trajectory stays at or above `d` — the second trajectory being driven by the
level-shifted array.

This file turns that deterministic coupling into the *law* statement needed for the
regeneration seed probability: the probability that the future of `s` stays at or above `d`
equals the probability that the future of `s'` stays at or above `0`.  (The seed-positivity
argument transplants a state whose future is known to stay nonnegative with positive
probability up by the record level, where a prescribed strictly-positive prefix can reach it.)

The two ingredients are:
* measurability in the array of the iteration from an *arbitrary* starting state
  (`measurable_trajFrom`, by the same countable-piece induction as
  `Swarming.Fair.measurable_trajectory`);
* the level shift is measure preserving (`SwarmRestart.measurePreserving_levelShift`).
-/
import Swarm.RestartRecord
import Swarm.MeasurableInc

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart

namespace SwarmSeed

variable {N : ℕ}

/-! ### The departure coordinate of the iteration from a state -/

/-- The array coordinate read by walker `i` at step `n` of the iteration started from `s`. -/
noncomputable def depFrom (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ)
    (i : Fin N) : Fin N × ℤ × ℕ :=
  (i, (trajFrom p m U s n).pos i, (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i))

@[simp] theorem depFrom_fst (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ)
    (i : Fin N) : (depFrom p m U s n i).1 = i := rfl

/-! ### Measurability of the iteration from an arbitrary state -/

theorem measurable_ellFrom_at_pos {p : ℝ} {m : ℕ} {s : WalkState N} {n : ℕ} {i : Fin N}
    (hpos : Measurable fun U : Array N => (trajFrom p m U s n).pos i)
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell j x) :
    Measurable fun U : Array N => (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i) :=
  SwarmIID.measurable_of_countable_pieces
    (fun (x : ℤ) (U : Array N) => (trajFrom p m U s n).ell i x)
    (fun x => hell i x) (fun U => (trajFrom p m U s n).pos i)
    (fun x => hpos (measurableSet_singleton x))

theorem measurable_otherVisitsFrom {p : ℝ} {m : ℕ} {s : WalkState N} {n : ℕ} {i : Fin N}
    (hpos : Measurable fun U : Array N => (trajFrom p m U s n).pos i)
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell j x) :
    Measurable fun U : Array N =>
      otherVisits (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i) := by
  have hterm : ∀ j : Fin N, Measurable fun U : Array N =>
      if j = i then (0 : ℕ) else (trajFrom p m U s n).ell j ((trajFrom p m U s n).pos i) := by
    intro j
    by_cases hji : j = i
    · simp only [hji, if_pos]
      exact measurable_const
    · simp only [hji, if_false]
      exact SwarmIID.measurable_of_countable_pieces
        (fun (x : ℤ) (U : Array N) => (trajFrom p m U s n).ell j x)
        (fun x => hell j x) (fun U => (trajFrom p m U s n).pos i)
        (fun x => hpos (measurableSet_singleton x))
  unfold otherVisits
  exact Finset.measurable_sum _ (fun j _ => hterm j)

theorem measurable_rightProbabilityFrom {p : ℝ} {m : ℕ} {s : WalkState N} {n : ℕ} {i : Fin N}
    (hpos : Measurable fun U : Array N => (trajFrom p m U s n).pos i)
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell j x) :
    Measurable fun U : Array N =>
      rightProbability p m (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i) := by
  have hov := measurable_otherVisitsFrom (p := p) (m := m) hpos hell
  have hfun : (fun U : Array N =>
      rightProbability p m (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i)) =
      fun U => (fun (k : ℕ) => if m ≤ k then p else 1 / 2)
        (otherVisits (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i)) := by
    funext U
    simp [rightProbability, Excited]
  rw [hfun]
  exact (measurable_of_countable (fun k : ℕ => if m ≤ k then p else 1 / 2)).comp hov

theorem measurableSet_depFrom {p : ℝ} {m : ℕ} {s : WalkState N} {n : ℕ} {i : Fin N}
    (hpos : Measurable fun U : Array N => (trajFrom p m U s n).pos i)
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell j x)
    (c : Fin N × ℤ × ℕ) :
    MeasurableSet {U : Array N | depFrom p m U s n i = c} := by
  by_cases hc : c.1 = i
  · have hset : {U : Array N | depFrom p m U s n i = c} =
        {U : Array N | (trajFrom p m U s n).pos i = c.2.1} ∩
          {U : Array N | (trajFrom p m U s n).ell i c.2.1 = c.2.2} := by
      ext U
      simp only [depFrom, mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro h
        have h1 : (trajFrom p m U s n).pos i = c.2.1 := by
          have := congrArg (fun q : Fin N × ℤ × ℕ => q.2.1) h
          simpa using this
        have h2 : (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i) = c.2.2 := by
          have := congrArg (fun q : Fin N × ℤ × ℕ => q.2.2) h
          simpa using this
        exact ⟨h1, by rw [← h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        have key : ((trajFrom p m U s n).pos i,
            (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i)) = (c.2.1, c.2.2) := by
          rw [Prod.mk.injEq]
          exact ⟨h1, by rw [h1]; exact h2⟩
        exact Prod.ext hc.symm key
    rw [hset]
    exact (hpos (measurableSet_singleton c.2.1)).inter (hell i c.2.1 (measurableSet_singleton c.2.2))
  · have hset : {U : Array N | depFrom p m U s n i = c} = ∅ := by
      ext U
      constructor
      · intro h
        apply hc
        have := congrArg (fun q : Fin N × ℤ × ℕ => q.1) h
        simpa using this.symm
      · intro h
        exact absurd h (Set.notMem_empty U)
    rw [hset]
    exact MeasurableSet.empty

theorem measurable_value_at_depFrom {p : ℝ} {m : ℕ} {s : WalkState N} {n : ℕ} {i : Fin N}
    (hpos : Measurable fun U : Array N => (trajFrom p m U s n).pos i)
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell j x) :
    Measurable fun U : Array N => U (depFrom p m U s n i) :=
  SwarmIID.measurable_of_countable_pieces (fun c (U : Array N) => U c)
    (fun c => measurable_pi_apply c) (fun U => depFrom p m U s n i)
    (fun c => measurableSet_depFrom hpos hell c)

/-- **Measurability of the iteration started from an arbitrary state.** -/
theorem measurable_trajFrom (p : ℝ) (m : ℕ) (s : WalkState N) (n : ℕ) :
    (∀ i : Fin N, Measurable fun U : Array N => (trajFrom p m U s n).pos i) ∧
      (∀ (i : Fin N) (x : ℤ), Measurable fun U : Array N => (trajFrom p m U s n).ell i x) := by
  induction n with
  | zero =>
      refine ⟨fun i => ?_, fun i x => ?_⟩
      · have h : (fun U : Array N => (trajFrom p m U s 0).pos i) = fun _ => s.pos i := by
          funext U; rw [trajFrom_zero]
        rw [h]; exact measurable_const
      · have h : (fun U : Array N => (trajFrom p m U s 0).ell i x) = fun _ => s.ell i x := by
          funext U; rw [trajFrom_zero]
        rw [h]; exact measurable_const
  | succ n ih =>
      obtain ⟨hpos, hell⟩ := ih
      have hstepPos : ∀ i : Fin N, (fun U : Array N => (trajFrom p m U s (n + 1)).pos i) =
          fun U => (trajFrom p m U s n).pos i +
            drivenStep (U (depFrom p m U s n i))
              (rightProbability p m (trajFrom p m U s n).ell i
                ((trajFrom p m U s n).pos i)) := by
        intro i
        funext U
        rw [trajFrom_succ, nextWalkState_pos, nextPos]
        rfl
      have hP : ∀ i : Fin N, Measurable fun U : Array N => (trajFrom p m U s (n + 1)).pos i := by
        intro i
        rw [hstepPos i]
        exact (hpos i).add (Swarming.Fair.measurable_drivenStep.comp
          ((measurable_value_at_depFrom (hpos i) hell).prodMk
            (measurable_rightProbabilityFrom (hpos i) hell)))
      refine ⟨hP, fun i x => ?_⟩
      · have hstepEll : (fun U : Array N => (trajFrom p m U s (n + 1)).ell i x) =
            fun U => (trajFrom p m U s n).ell i x +
              (if (trajFrom p m U s (n + 1)).pos i = x then 1 else 0) := by
          funext U
          rw [trajFrom_succ, nextWalkState_ell, nextWalkState_pos]
          simp only [eq_comm]
        rw [hstepEll]
        exact (hell i x).add (Measurable.ite
          ((measurableSet_singleton x).preimage (hP i)) measurable_const measurable_const)

end SwarmSeed

namespace SwarmSeed

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart

variable {N : ℕ}

/-! ### The future of a state stays at or above a level -/

/-- `FutureGe p m s d`: every walker is at or above level `d` at every future time, for the
iteration started from the state `s`. -/
def FutureGe (p : ℝ) (m : ℕ) (s : WalkState N) (d : ℤ) : Set (Array N) :=
  {U | ∀ (n : ℕ) (i : Fin N), d ≤ (trajFrom p m U s n).pos i}

theorem measurableSet_FutureGe (p : ℝ) (m : ℕ) (s : WalkState N) (d : ℤ) :
    MeasurableSet (FutureGe p m s d) := by
  have h : FutureGe p m s d =
      ⋂ (n : ℕ), ⋂ (i : Fin N), {U : Array N | d ≤ (trajFrom p m U s n).pos i} := by
    ext U
    simp only [FutureGe, mem_ofPred_eq, mem_iInter]
  rw [h]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
  exact (measurableSet_Ici (a := d)).preimage ((measurable_trajFrom p m s n).1 i)

/-- The symmetric form of `SwarmRestart.restart_agreement_aux`: it is the *translated* state
that stays at or above zero, and the array of the translated system is the level shift of the
array of the reference system. -/
theorem restart_agreement_symm (p : ℝ) (m : ℕ) {V : Array N} {d : ℤ} {a b : WalkState N}
    (h : ShiftAgree d a b) (hstay : ∀ (k : ℕ) (i : Fin N), 0 ≤ (trajFrom p m V b k).pos i) :
    ∀ n, ShiftAgree d (trajFrom p m (levelShift (-d) V) a n) (trajFrom p m V b n) := by
  have hV : levelShift d (levelShift (-d) V) = V := by
    funext c
    obtain ⟨i, x, k⟩ := c
    simp [levelShift]
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have hge : ∀ i, d ≤ (trajFrom p m (levelShift (-d) V) a n).pos i := by
        intro i
        have h1 := ih.1 i
        have h2 := hstay n i
        omega
      have hstep := nextWalkState_shiftAgree (p := p) (m := m) (U := levelShift (-d) V) (d := d)
        ih hge
      rw [hV] at hstep
      rw [trajFrom_succ, trajFrom_succ]
      exact hstep

theorem levelShift_neg_levelShift (d : ℤ) (U : Array N) :
    levelShift (-d) (levelShift d U) = U := by
  funext c
  obtain ⟨i, x, k⟩ := c
  simp [levelShift]

theorem levelShift_pos_levelShift (d : ℤ) (U : Array N) :
    levelShift d (levelShift (-d) U) = U := by
  funext c
  obtain ⟨i, x, k⟩ := c
  simp [levelShift]

/-- **The future law is invariant under translating the state.**  If `a` is the state `b`
translated up by the level `d` (at all sites at or above `d`), then the probability that the
future of `a` stays at or above `d` equals the probability that the future of `b` stays at or
above `0`. -/
theorem future_ge_transfer (p : ℝ) (m : ℕ) {d : ℤ} {a b : WalkState N} (h : ShiftAgree d a b) :
    (arrayMeasure N) (FutureGe p m b 0) = (arrayMeasure N) (FutureGe p m a d) := by
  have hset : FutureGe p m a d = (levelShift (N := N) d) ⁻¹' (FutureGe p m b 0) := by
    ext U
    simp only [FutureGe, mem_ofPred_eq, mem_preimage]
    constructor
    · intro hU n i
      have hshift := (restart_agreement_aux (p := p) (m := m) (U := U) h hU n).1 i
      have h2 : d ≤ (trajFrom p m U a n).pos i := hU n i
      rw [hshift] at h2
      omega
    · intro hU n i
      have hb : ∀ (k : ℕ) (j : Fin N), 0 ≤ (trajFrom p m (levelShift d U) b k).pos j := hU
      have hshift := restart_agreement_symm (p := p) (m := m) (V := levelShift d U) h hb n
      rw [levelShift_neg_levelShift] at hshift
      have h1 := hshift.1 i
      have h2 := hU n i
      omega
  rw [hset]
  exact ((measurePreserving_levelShift (N := N) d).measure_preimage
    (measurableSet_FutureGe p m b 0).nullMeasurableSet).symm

end SwarmSeed
