/-
# Measurability of the stopped record map of the capped-step chain

This file proves that the record state produced at the first record time of the capped-step
chain (`SimJump.Record.FirstRecord`) depends *measurably* on the starting compact record state
`y : RecState N m`, with the driving jump sequence held fixed.  This is the measurability input
for the stopped record kernel `hitK` of `StoppedKernel.lean`.

The proof is a simultaneous induction on the number of steps over the position and capped
local-time coordinates of `SimJump.evolveFun`, followed by finite sums/products for the
one-step weight `SimJump.stepW` and the path weight `SimJump.pathW`.  No continuity argument is
used and no measurability is transported through an almost-sure equality.

Main results:

* `measurable_pos_eta` : every position and capped local-time coordinate after `n` steps is a
  measurable function of the initial compact record state;
* `measurable_pos_eta_diag` : the diagonal combination `η_j(X_i)` (needed for the excitation
  count `otherVisits`) is measurable;
* `measurable_pathW` : the path weight `q ↦ pathW p k q (ofRecState y)` is measurable in `y`;
* `measurable_firstRecord_set` : the first-record event is measurable in `y`;
* `measurable_out` : the stopped record state map is measurable in `y`.
-/
import Swarm.StoppedState

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SimJump.RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### A countable-codomain measurability criterion -/

/-- A function into a countable space with measurable point fibres is measurable. -/
theorem measurable_of_countable_codomain {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] (f : α → β) (h : ∀ b, MeasurableSet (f ⁻¹' {b})) : Measurable f := by
  intro s _
  have hEq : f ⁻¹' s = ⋃ b ∈ s, f ⁻¹' ({b} : Set β) := by
    ext a
    simp
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable s) fun b _ => h b

/-! ### The position and local-time coordinates -/

/-- **Every coordinate of the capped-step chain is measurable in the starting record state.**
Simultaneous induction on the time `n` over the positions and the capped local times. -/
theorem measurable_pos_eta (u : ℕ → JumpVec N) (n : ℕ) :
    (∀ i : Fin N, Measurable fun y : RecState N m =>
        (evolveFun (m := m) u n (Record.ofRecState y)).pos i) ∧
      (∀ (i : Fin N) (x : ℤ), Measurable fun y : RecState N m =>
        (evolveFun (m := m) u n (Record.ofRecState y)).eta i x) := by
  induction n with
  | zero =>
      constructor
      · intro i
        have hzero : (fun y : RecState N m =>
            (evolveFun (m := m) u 0 (Record.ofRecState y)).pos i) =
            (fun y => -(2 * ((y.val.1 i : ℕ) : ℤ))) := by
          funext y
          simp [evolveFun, evolve, Record.ofRecState]
        rw [hzero]
        have hd0 : Measurable fun y : RecState N m => y.val.1 :=
          measurable_fst.comp measurable_subtype_coe
        have hd : Measurable fun y : RecState N m => ((y.val.1 i : ℕ) : ℤ) :=
          (measurable_of_countable (fun n : ℕ => ((n : ℤ)))).comp
            ((measurable_pi_apply i).comp hd0)
        exact (measurable_of_countable (fun z : ℤ => -(2 * z))).comp hd
      · intro i x
        have hzero : (fun y : RecState N m =>
            (evolveFun (m := m) u 0 (Record.ofRecState y)).eta i x) =
            (fun y => (y.val.2 i x).val) := by
          funext y
          simp [evolveFun, evolve, Record.ofRecState]
        rw [hzero]
        have hd0 : Measurable fun y : RecState N m => y.val.2 :=
          measurable_snd.comp measurable_subtype_coe
        have hd : Measurable fun y : RecState N m => y.val.2 i x :=
          (measurable_pi_apply x).comp ((measurable_pi_apply i).comp hd0)
        exact (measurable_of_countable (fun c : Fin (m + 1) => c.val)).comp hd
  | succ n ih =>
      obtain ⟨hpos, heta⟩ := ih
      constructor
      · intro i
        have hstep : (fun y : RecState N m =>
            (evolveFun (m := m) u (n + 1) (Record.ofRecState y)).pos i) =
            (fun y => (evolveFun (m := m) u n (Record.ofRecState y)).pos i +
              (if u n i = true then (1 : ℤ) else -1)) := by
          funext y
          rw [evolveFun_succ, step_pos, stepPos]
        rw [hstep]
        exact (measurable_of_countable
          (fun z : ℤ => z + (if u n i = true then (1 : ℤ) else -1))).comp (hpos i)
      · intro i x
        have hstep : (fun y : RecState N m =>
            (evolveFun (m := m) u (n + 1) (Record.ofRecState y)).eta i x) =
            (fun y => if x = stepPos (evolveFun (m := m) u n (Record.ofRecState y)) (u n) i then
              cap m ((evolveFun (m := m) u n (Record.ofRecState y)).eta i x + 1)
              else (evolveFun (m := m) u n (Record.ofRecState y)).eta i x) := by
          funext y
          rw [evolveFun_succ]
          simp only [step]
        rw [hstep]
        have hGm : Measurable fun y : RecState N m =>
            (evolveFun (m := m) u n (Record.ofRecState y)).eta i x := heta i x
        have hstepPos : Measurable fun y : RecState N m =>
            stepPos (evolveFun (m := m) u n (Record.ofRecState y)) (u n) i := by
          have hEq : (fun y : RecState N m =>
              stepPos (evolveFun (m := m) u n (Record.ofRecState y)) (u n) i) =
              (fun y => (evolveFun (m := m) u n (Record.ofRecState y)).pos i +
                (if u n i = true then (1 : ℤ) else -1)) := rfl
          rw [hEq]
          exact (hpos i).add measurable_const
        exact Measurable.ite (measurableSet_eq_fun measurable_const hstepPos)
          ((measurable_of_countable (fun a : ℕ => cap m (a + 1))).comp hGm) hGm

/-! ### The diagonal combination `η_j(X_i)` -/

/-- The excitation count of `SimJumpCore` evaluates walker `j`'s capped local time at walker
`i`'s current position, i.e. along a *diagonal* of the state.  Measurability survives because
the position takes countably many values. -/
theorem measurable_pos_eta_diag (u : ℕ → JumpVec N) (n : ℕ) (i j : Fin N) :
    Measurable fun y : RecState N m =>
      (evolveFun (m := m) u n (Record.ofRecState y)).eta j
        ((evolveFun (m := m) u n (Record.ofRecState y)).pos i) := by
  obtain ⟨hpos, heta⟩ := measurable_pos_eta (m := m) u n
  refine measurable_of_countable_codomain _ fun c => ?_
  have hEq : (fun y : RecState N m =>
      (evolveFun (m := m) u n (Record.ofRecState y)).eta j
        ((evolveFun (m := m) u n (Record.ofRecState y)).pos i)) ⁻¹' {c} =
      ⋃ x : ℤ, ({y : RecState N m |
          (evolveFun (m := m) u n (Record.ofRecState y)).pos i = x} ∩
        {y : RecState N m |
          (evolveFun (m := m) u n (Record.ofRecState y)).eta j x = c}) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨_, rfl, h⟩
      exact h
  rw [hEq]
  refine MeasurableSet.iUnion fun x => ?_
  exact ((hpos i) (measurableSet_singleton x)).inter ((heta j x) (measurableSet_singleton c))

end SimJump.RecKernel


namespace SimJump.RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### The one-step weight and the path weight -/

theorem measurable_otherVisits (u : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    Measurable fun y : RecState N m =>
      otherVisits (evolveFun (m := m) u n (Record.ofRecState y)) i := by
  unfold otherVisits
  exact Finset.measurable_sum _ fun j _ => measurable_pos_eta_diag u n i j

theorem measurable_qRight (p : ℝ) (u : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    Measurable fun y : RecState N m =>
      qRight p m (evolveFun (m := m) u n (Record.ofRecState y)) i := by
  have h : (fun y : RecState N m =>
        qRight p m (evolveFun (m := m) u n (Record.ofRecState y)) i) =
      (fun a : ℕ => if m ≤ a then p else (1 / 2 : ℝ)) ∘
        (fun y => otherVisits (evolveFun (m := m) u n (Record.ofRecState y)) i) := rfl
  rw [h]
  exact (measurable_of_countable (fun a : ℕ => if m ≤ a then p else (1 / 2 : ℝ))).comp
    (measurable_otherVisits u n i)

theorem measurable_stepW (p : ℝ) (u : ℕ → JumpVec N) (n : ℕ) (v : JumpVec N) :
    Measurable fun y : RecState N m =>
      stepW p m (evolveFun (m := m) u n (Record.ofRecState y)) v := by
  have h : (fun y : RecState N m =>
        stepW p m (evolveFun (m := m) u n (Record.ofRecState y)) v) =
      (fun y => ∏ i : Fin N,
        stepFactor p m (evolveFun (m := m) u n (Record.ofRecState y)) i (v i)) := rfl
  rw [h]
  refine Finset.measurable_prod _ fun i _ => ?_
  by_cases hv : v i = true
  · have h1 : (fun y : RecState N m =>
        stepFactor p m (evolveFun (m := m) u n (Record.ofRecState y)) i (v i)) =
        (fun y => qRight p m (evolveFun (m := m) u n (Record.ofRecState y)) i) := by
      funext y
      simp [stepFactor, hv]
    rw [h1]
    exact measurable_qRight p u n i
  · have h1 : (fun y : RecState N m =>
        stepFactor p m (evolveFun (m := m) u n (Record.ofRecState y)) i (v i)) =
        (fun y => 1 - qRight p m (evolveFun (m := m) u n (Record.ofRecState y)) i) := by
      funext y
      simp [stepFactor, hv]
    rw [h1]
    exact measurable_const.sub (measurable_qRight p u n i)

/-- The path weight `pathWFun` of the capped-step chain is a measurable function of the
starting compact record state. -/
theorem measurable_pathWFun (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) :
    Measurable fun y : RecState N m => pathWFun p u k (Record.ofRecState y) := by
  induction k with
  | zero => simp [pathWFun, pathW]
  | succ k ih =>
      have h : (fun y : RecState N m => pathWFun p u (k + 1) (Record.ofRecState y)) =
          (fun y => pathWFun p u k (Record.ofRecState y) *
            stepW p m (evolveFun (m := m) u k (Record.ofRecState y)) (u k)) := by
        funext y
        rw [pathWFun_succ]
      rw [h]
      exact ih.mul (measurable_stepW p u k (u k))

/-- The finite path weight of a fixed jump path is a measurable function of the starting
compact record state. -/
theorem measurable_pathW (p : ℝ) (k : ℕ) (q : Fin k → JumpVec N) :
    Measurable fun y : RecState N m => pathW p k q (Record.ofRecState y) := by
  classical
  let u : ℕ → JumpVec N := fun n => if h : n < k then q ⟨n, h⟩ else fun _ => true
  have hqi : (fun i : Fin k => u i) = q := by
    funext i
    have hi : u (i : ℕ) = q ⟨(i : ℕ), i.isLt⟩ := by
      simp only [u, dif_pos i.isLt]
    rw [hi]
  have h : (fun y : RecState N m => pathW p k q (Record.ofRecState y)) =
      (fun y => pathWFun p u k (Record.ofRecState y)) := by
    funext y
    rw [← hqi, pathW_eq_pathWFun]
  rw [h]
  exact measurable_pathWFun p u k

/-! ### The first-record event -/

theorem measurableSet_Iic_int (c : ℤ) : MeasurableSet (Set.Iic c) := by
  have hEq : Set.Iic c = ⋃ n : ℕ, ({(c - (n : ℤ))} : Set ℤ) := by
    ext z
    simp only [Set.mem_Iic, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨(c - z).toNat, by omega⟩
    · rintro ⟨n, rfl⟩
      omega
  rw [hEq]
  exact MeasurableSet.iUnion fun n => measurableSet_singleton _

/-- **The first-record event is measurable in the starting record state.** -/
theorem measurableSet_firstRecord (k : ℕ) (q : Fin k → JumpVec N) :
    MeasurableSet {y : RecState N m |
      Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)} := by
  obtain ⟨hpos, _⟩ := measurable_pos_eta (m := m) (Record.extendPath q) k
  have hEq : {y : RecState N m |
        Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)} =
      {y | ∃ i : Fin N,
          (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i = 1} ∩
        {y | ∀ t : Fin k, ∀ i : Fin N,
          (evolveFun (m := m) (Record.extendPath q) (t : ℕ) (Record.ofRecState y)).pos i ≤ 0} := by
    ext y
    constructor
    · rintro ⟨⟨i, hi⟩, hprev⟩
      exact ⟨⟨i, hi⟩, fun t i => hprev t t.isLt i⟩
    · rintro ⟨⟨i, hi⟩, hprev⟩
      exact ⟨⟨i, hi⟩, fun t ht i => hprev ⟨t, ht⟩ i⟩
  rw [hEq]
  refine MeasurableSet.inter ?_ ?_
  · rw [show {y : RecState N m | ∃ i : Fin N,
        (evolveFun (m := m) (Record.extendPath q) k (Record.ofRecState y)).pos i = 1} =
        ⋃ i : Fin N, {y | (evolveFun (m := m) (Record.extendPath q) k
          (Record.ofRecState y)).pos i = 1} from by
      ext y
      simp]
    exact MeasurableSet.iUnion fun i => hpos i (measurableSet_singleton 1)
  · rw [show {y : RecState N m | ∀ t : Fin k, ∀ i : Fin N,
        (evolveFun (m := m) (Record.extendPath q) (t : ℕ) (Record.ofRecState y)).pos i ≤ 0} =
        ⋂ t : Fin k, ⋂ i : Fin N, {y |
          (evolveFun (m := m) (Record.extendPath q) (t : ℕ) (Record.ofRecState y)).pos i ≤ 0} from by
      ext y
      simp]
    refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun i => ?_
    exact (measurable_pos_eta (m := m) (Record.extendPath q) (t : ℕ)).1 i
      (measurableSet_Iic_int 0)

/-! ### The stopped record state map -/

/-- The ambient coordinates of the state reached by the path `u` at time `k` from `y`, i.e. the
`Record.toRecordAmb` construction of `Swarm/Bridge.lean`. -/
noncomputable def recEta (u : ℕ → JumpVec N) (k : ℕ) (i : Fin N) (x : ℤ) :
    RecState N m → Fin (m + 1) :=
  fun y => ⟨(evolveFun (m := m) u k (Record.ofRecState y)).eta i (x + 1), by
    have h := (evolveFun (m := m) u k (Record.ofRecState y)).hcap i (x + 1)
    omega⟩

theorem measurable_recEta (u : ℕ → JumpVec N) (k : ℕ) (i : Fin N) (x : ℤ) :
    Measurable (recEta (m := m) u k i x) := by
  refine measurable_of_countable_codomain _ fun c => ?_
  have hset : recEta (m := m) u k i x ⁻¹' {c} =
      {y : RecState N m | (evolveFun (m := m) u k (Record.ofRecState y)).eta i (x + 1) = c.val} := by
    ext y
    simp [recEta, Fin.ext_iff]
  rw [hset]
  exact (measurable_pos_eta (m := m) u k).2 i (x + 1) (measurableSet_singleton c.val)

noncomputable def recAmb (u : ℕ → JumpVec N) (k : ℕ) : RecState N m → Amb N m :=
  fun y =>
    (fun i => Record.halfDist ((evolveFun (m := m) u k (Record.ofRecState y)).pos i),
     fun i x => recEta (m := m) u k i x y)

lemma recAmb_eq_toRecordAmb (u : ℕ → JumpVec N) (k : ℕ) (y : RecState N m) :
    recAmb (m := m) u k y =
      Record.toRecordAmb (evolveFun (m := m) u k (Record.ofRecState y)) := by
  simp [recAmb, recEta, Record.toRecordAmb, Record.normalize]

theorem measurable_recAmb (u : ℕ → JumpVec N) (k : ℕ) :
    Measurable (recAmb (m := m) u k) := by
  obtain ⟨hpos, -⟩ := measurable_pos_eta (m := m) u k
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun i => ?_
    exact (measurable_of_countable (fun z : ℤ => Record.halfDist z)).comp (hpos i)
  · refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_iff.mpr fun x => measurable_recEta u k i x

/-- Measurability of a function into a subtype is measurability of its ambient part. -/
theorem measurable_subtype_iff {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {p : β → Prop} (f : α → Subtype p) : Measurable f ↔ Measurable fun a => (f a : β) := by
  rw [measurable_iff_comap_le, measurable_iff_comap_le, Subtype.instMeasurableSpace,
    MeasurableSpace.comap_comp]
  rfl

/-- **The stopped record state depends measurably on the starting record state.** -/
theorem measurable_out (hm : 1 ≤ m) (k : ℕ) (q : Fin k → JumpVec N) :
    Measurable fun y : RecState N m => out hm q y := by
  classical
  rw [measurable_subtype_iff]
  have hEq : (fun y : RecState N m => (out hm q y).val) =
      (fun y => if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
        then recAmb (m := m) (Record.extendPath q) k y else y.val) := by
    funext y
    by_cases h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
    · rw [out_of_firstRecord hm q y h, if_pos h]
      rw [recState_val (Record.extendPath q) k (Record.ofRecState y) hm h
        (Record.ofRecState_recordStart y hm)]
      exact recAmb_eq_toRecordAmb _ _ _
    · rw [out_of_not_firstRecord hm q y h, if_neg h]
  rw [hEq]
  exact Measurable.ite (measurableSet_firstRecord k q) (measurable_recAmb _ k)
    measurable_subtype_coe

end SimJump.RecKernel


