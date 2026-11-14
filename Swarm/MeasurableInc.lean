/-
Measurability of the actual auxiliary symmetric-walk increments
`Swarming.Fair.symmInc p m · i n`.

The departure coordinate is itself a function of the array, so this is exactly the
"measurable selection from countably many pieces" situation: the value read is
`ω ↦ ω (departureCoord p m ω n i)`, handled by
`SwarmIID.measurable_of_countable_pieces` once the trajectory is known measurable.
The trajectory is proved measurable componentwise by induction on time, using the same
countable-piece lemma to evaluate the local-time field at the random current position.
-/
import Swarm.FairSlice

namespace Swarming.Fair

open MeasureTheory ProbabilityTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

variable {N : ℕ}

lemma trajectory_succ_ell_apply (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    (trajectory p m U (n + 1)).ell i x =
      (trajectory p m U n).ell i x + (if x = (trajectory p m U (n + 1)).pos i then 1 else 0) := rfl

lemma measurable_drivenStep : Measurable (fun q : ℝ × ℝ => drivenStep q.1 q.2) := by
  unfold drivenStep
  exact Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
    measurable_const

/-! ### Evaluating the local-time field at the current position -/

/-- `ω ↦ (ell at time n of walker j) (position at time n of walker i)`. -/
lemma measurable_ell_at_pos {p : ℝ} {m : ℕ} {n : ℕ} {i j : Fin N}
    (hpos : Measurable (fun ω : Array N => (trajectory p m ω n).pos i))
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell j x)) :
    Measurable (fun ω : Array N => (trajectory p m ω n).ell j ((trajectory p m ω n).pos i)) :=
  SwarmIID.measurable_of_countable_pieces (fun (x : ℤ) (ω : Array N) => (trajectory p m ω n).ell j x)
    (fun x => hell j x) (fun ω => (trajectory p m ω n).pos i)
    (fun x => hpos (measurableSet_singleton x))

/-- The visits of the *other* walkers to the current position of walker `i`, at time `n`. -/
lemma measurable_otherVisits {p : ℝ} {m : ℕ} {n : ℕ} {i : Fin N}
    (hpos : Measurable (fun ω : Array N => (trajectory p m ω n).pos i))
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell j x)) :
    Measurable (fun ω : Array N =>
      otherVisits (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) := by
  have hterm : ∀ j : Fin N, Measurable (fun ω : Array N =>
      if j = i then (0 : ℕ) else (trajectory p m ω n).ell j ((trajectory p m ω n).pos i)) := by
    intro j
    by_cases hji : j = i
    · simp only [hji, if_pos]
      exact measurable_const
    · simp only [hji, if_false]
      exact measurable_ell_at_pos (i := i) (j := j) hpos hell
  unfold otherVisits
  exact Finset.measurable_sum _ (fun j _ => hterm j)

/-- The right-jump probability of walker `i` at time `n`, as a function of the array. -/
lemma measurable_rightProbability {p : ℝ} {m : ℕ} {n : ℕ} {i : Fin N}
    (hpos : Measurable (fun ω : Array N => (trajectory p m ω n).pos i))
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell j x)) :
    Measurable (fun ω : Array N =>
      rightProbability p m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) := by
  have hov := measurable_otherVisits (p := p) (m := m) (n := n) (i := i) hpos hell
  have hfun : (fun ω : Array N =>
      rightProbability p m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) =
      fun ω => (fun (k : ℕ) => if m ≤ k then p else 1 / 2)
        (otherVisits (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) := by
    funext ω
    simp [rightProbability, Excited]
  rw [hfun]
  exact (measurable_of_countable (fun k : ℕ => if m ≤ k then p else 1 / 2)).comp hov

/-! ### Measurability of the departure coordinate -/

lemma measurableSet_departureCoord {p : ℝ} {m : ℕ} {n : ℕ} {i : Fin N}
    (hpos : Measurable (fun ω : Array N => (trajectory p m ω n).pos i))
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell j x))
    (c : Fin N × ℤ × ℕ) :
    MeasurableSet {ω : Array N | departureCoord p m ω n i = c} := by
  by_cases hc : c.1 = i
  · have hset : {ω : Array N | departureCoord p m ω n i = c} =
        {ω : Array N | (trajectory p m ω n).pos i = c.2.1} ∩
          {ω : Array N | (trajectory p m ω n).ell i c.2.1 = c.2.2} := by
      ext ω
      simp only [departureCoord, mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro h
        have hsnd : ((trajectory p m ω n).pos i,
            (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) = c.2 := congrArg Prod.snd h
        rw [Prod.mk.injEq] at hsnd
        exact ⟨hsnd.1, hsnd.1 ▸ hsnd.2⟩
      · rintro ⟨h1, h2⟩
        have hsnd : ((trajectory p m ω n).pos i,
            (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) = c.2 := by
          rw [Prod.mk.injEq]
          exact ⟨h1, by rw [h1]; exact h2⟩
        exact Prod.ext hc.symm hsnd
    rw [hset]
    exact (hpos (measurableSet_singleton c.2.1)).inter (hell i c.2.1 (measurableSet_singleton c.2.2))
  · have hset : {ω : Array N | departureCoord p m ω n i = c} = ∅ := by
      ext ω
      simp only [departureCoord, mem_ofPred_eq, mem_empty_iff_false]
      rw [iff_false]
      exact fun h => hc (congrArg Prod.fst h).symm
    rw [hset]
    exact MeasurableSet.empty

lemma measurable_value_at_departure {p : ℝ} {m : ℕ} {n : ℕ} {i : Fin N}
    (hpos : Measurable (fun ω : Array N => (trajectory p m ω n).pos i))
    (hell : ∀ (j : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell j x)) :
    Measurable (fun ω : Array N => ω (departureCoord p m ω n i)) :=
  SwarmIID.measurable_of_countable_pieces (fun c (ω : Array N) => ω c)
    (fun c => measurable_pi_apply c) (fun ω => departureCoord p m ω n i)
    (fun c => measurableSet_departureCoord hpos hell c)

/-! ### The trajectory is measurable in the array -/

theorem measurable_trajectory (p : ℝ) (m : ℕ) (n : ℕ) :
    (∀ i : Fin N, Measurable (fun ω : Array N => (trajectory p m ω n).pos i)) ∧
      (∀ (i : Fin N) (x : ℤ), Measurable (fun ω : Array N => (trajectory p m ω n).ell i x)) := by
  induction n with
  | zero =>
      refine ⟨fun i => ?_, fun i x => ?_⟩
      · have h : (fun ω : Array N => (trajectory p m ω 0).pos i) = fun _ => (0 : ℤ) := rfl
        rw [h]; exact measurable_const
      · have h : (fun ω : Array N => (trajectory p m ω 0).ell i x) =
          fun _ => (if x = 0 then 1 else 0 : ℕ) := rfl
        rw [h]; exact measurable_const
  | succ n ih =>
      obtain ⟨hpos, hell⟩ := ih
      refine ⟨fun i => ?_, fun i x => ?_⟩
      · have hval := measurable_value_at_departure (p := p) (m := m) (n := n) (i := i) (hpos i) hell
        have hα := measurable_rightProbability (p := p) (m := m) (n := n) (i := i) (hpos i) hell
        have hnext : (fun ω : Array N => (trajectory p m ω (n + 1)).pos i) =
            fun ω => (trajectory p m ω n).pos i +
              drivenStep (ω (departureCoord p m ω n i))
                (rightProbability p m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) :=
          rfl
        rw [hnext]
        exact (hpos i).add (measurable_drivenStep.comp (hval.prodMk hα))
      · have hposNext : Measurable (fun ω : Array N => (trajectory p m ω (n + 1)).pos i) := by
          have hval := measurable_value_at_departure (p := p) (m := m) (n := n) (i := i) (hpos i) hell
          have hα := measurable_rightProbability (p := p) (m := m) (n := n) (i := i) (hpos i) hell
          have hnext : (fun ω : Array N => (trajectory p m ω (n + 1)).pos i) =
              fun ω => (trajectory p m ω n).pos i +
                drivenStep (ω (departureCoord p m ω n i))
                  (rightProbability p m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)) :=
            rfl
          rw [hnext]
          exact (hpos i).add (measurable_drivenStep.comp (hval.prodMk hα))
        have hstep : (fun ω : Array N => (trajectory p m ω (n + 1)).ell i x) =
            fun ω => (trajectory p m ω n).ell i x +
              (if (trajectory p m ω (n + 1)).pos i ∈ ({x} : Set ℤ) then 1 else 0) := by
          funext ω
          rw [trajectory_succ_ell_apply]
          simp only [mem_singleton_iff, eq_comm]
        rw [hstep]
        exact (hell i x).add (Measurable.ite
          ((measurableSet_singleton x).preimage hposNext) measurable_const measurable_const)

/-- The departure coordinate of walker `i` at time `n`, as a measurable map into the
countable coordinate type. -/
lemma measurable_departureCoord (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Measurable (fun ω : Array N => departureCoord p m ω n i) :=
  measurable_to_countable' (fun c =>
    measurableSet_departureCoord (i := i) ((measurable_trajectory p m n).1 i)
      (measurable_trajectory p m n).2 c)

/-- **Measurability of the actual increment of `symmetricWalk`.** -/
theorem measurable_symmInc (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) :
    Measurable (fun ω : Array N => symmInc p m ω i n) :=
  measurable_symmetricStep.comp
    (measurable_value_at_departure (i := i) ((measurable_trajectory p m n).1 i)
      (measurable_trajectory p m n).2)

/-- **Measurability of the actual auxiliary walk itself.** -/
theorem measurable_symmetricWalk (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) :
    Measurable (fun ω : Array N => symmetricWalk p m ω i n) := by
  have h : (fun ω : Array N => symmetricWalk p m ω i n) =
      fun ω => ∑ k ∈ Finset.range n, symmInc p m ω i k := by
    funext ω
    exact symmetricWalk_eq_sum_range p m ω i n
  rw [h]
  exact Finset.measurable_sum _ (fun k _ => measurable_symmInc p m i k)

/-- The joint increment vector of the whole swarm at time `n` is measurable. -/
theorem measurable_symmIncVec (p : ℝ) (m : ℕ) (n : ℕ) :
    Measurable (fun ω : Array N => fun i : Fin N => symmInc p m ω i n) := by
  rw [measurable_pi_iff]
  exact fun i => measurable_symmInc p m i n

/-- The event that a given time-`n` increment pattern is realised is measurable. -/
theorem measurableSet_incEq (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) (s : ℤ) :
    MeasurableSet {ω : Array N | symmInc p m ω i n = s} :=
  (measurable_symmInc p m i n) (measurableSet_singleton s)

end Swarming.Fair
