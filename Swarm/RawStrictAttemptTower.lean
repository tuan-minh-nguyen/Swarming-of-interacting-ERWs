/-
Actual repeated strict-record attempts on the raw WCJF array.

The attempt at `r` uses the canonical record time of level `r+1` and the
integrated `RegenAtStrict` event.  The first-success selector is total: its zero
fallback is retained on the infinite-failure event and is not confused with an
immediate success.  No existence of a successful attempt or invariant law is
assumed by the selector and measurability declarations.
-/
import Swarm.RecordMeas
import Swarm.SeedConditional
import Swarm.StarRegen
import Swarm.Trials

open MeasureTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming.Uniform Swarming.Trajectory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Swarm.Trials

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {S : Type*} [MeasurableSpace S]

/-- A positive value of the totalized selector is exactly the corresponding
first-success cell; the zero fallback cannot occur at a positive value. -/
theorem firstSuccess_eq_succ_iff {Z : ℕ → Ω → S} {C : Set S} {ω : Ω} {k : ℕ} :
    firstSuccess Z C ω = k + 1 ↔
      Z (k + 1) ω ∈ C ∧ ∀ j < k + 1, Z j ω ∉ C := by
  by_cases hex : ∃ k, Z k ω ∈ C
  · simp only [firstSuccess, dif_pos hex]
    constructor
    · intro hk
      have hs := Nat.find_spec hex
      rw [hk] at hs
      refine ⟨hs, fun j hj => ?_⟩
      exact Nat.find_min hex (by omega)
    · rintro ⟨hs, hmin⟩
      apply le_antisymm
      · exact Nat.find_min' hex hs
      · by_contra hlt
        have hlt' : Nat.find hex < k + 1 := by omega
        exact hmin (Nat.find hex) hlt' (Nat.find_spec hex)
  · have hz : firstSuccess Z C ω = 0 := by simp [firstSuccess, hex]
    rw [hz]
    constructor
    · intro hfalse
      omega
    · intro h
      exact (hex ⟨k + 1, h.1⟩).elim

/-- The totalized first-success index is measurable whenever every trial and
its target are measurable.  The zero fibre must also include the event on
which no trial succeeds. -/
theorem measurable_firstSuccess {Z : ℕ → Ω → S} {C : Set S}
    (hZ : ∀ k, MeasurableSet (Z k ⁻¹' C)) :
    Measurable (firstSuccess Z C) := by
  refine measurable_to_countable' fun k => ?_
  cases k with
  | zero =>
      have hset : firstSuccess Z C ⁻¹' {0} =
          (Z 0 ⁻¹' C) ∪ ⋂ j, (Z j ⁻¹' C)ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_iInter, Set.mem_compl_iff]
        by_cases hex : ∃ k, Z k ω ∈ C
        · simp only [firstSuccess, dif_pos hex]
          constructor
          · intro hk
            left
            have hs := Nat.find_spec hex
            rwa [hk] at hs
          · intro h
            rcases h with h0 | hall
            · exact le_antisymm (Nat.find_min' hex h0) (Nat.zero_le _)
            · exact False.elim (hall (Nat.find hex) (Nat.find_spec hex))
        · have hz : firstSuccess Z C ω = 0 := by simp [firstSuccess, hex]
          simp only [hz, true_iff]
          exact Or.inr fun j hj => hex ⟨j, hj⟩
      rw [hset]
      exact (hZ 0).union (MeasurableSet.iInter fun j => (hZ j).compl)
  | succ k =>
      have hset : firstSuccess Z C ⁻¹' {k + 1} =
          (Z (k + 1) ⁻¹' C) ∩ ⋂ j ∈ Finset.range (k + 1), (Z j ⁻¹' C)ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
        exact firstSuccess_eq_succ_iff
      rw [hset]
      exact (hZ (k + 1)).inter
        (MeasurableSet.biInter (Finset.countable_toSet _) fun j _ => (hZ j).compl)

end Swarm.Trials

namespace RawStrictAttemptTower

open RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open SwarmFresh SwarmSeed

attribute [local instance] Classical.propDecidable

variable {N : ℕ} [Nonempty (Fin N)]

/-- The level of attempt `r`. -/
def attemptLevel (r : ℕ) : ℕ := r + 1

/-- The canonical time of attempt `r`. -/
noncomputable def attemptTime (p : ℝ) (m : ℕ) (U : Array N) (r : ℕ) : ℕ :=
  recTimeA p m U (r + 1)

/-- Strict record attempt `r`, at positive level `r+1` and the actual
canonical record time of that level. -/
noncomputable def StrictAttempt (p : ℝ) (m : ℕ) (U : Array N) (r : ℕ) : Prop :=
  RegenAtStrict p m U (attemptTime p m U r) ((attemptLevel r : ℕ) : ℤ)

/-- Boolean success signal, used only to instantiate the existing generic
`Trials.firstSuccess`; `StrictAttempt` remains the mathematical event. -/
noncomputable def attemptSignal (p : ℝ) (m : ℕ) (U : Array N) (r : ℕ) : Bool :=
  decide (StrictAttempt p m U r)

/-- Total first successful strict-record attempt, with zero fallback on the
infinite-failure event. -/
noncomputable def firstStrictAttempt (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  Swarm.Trials.firstSuccess (fun r U => attemptSignal p m U r) {true} U

/-- Level of the selected attempt. -/
noncomputable def selectedLevel (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  attemptLevel (firstStrictAttempt p m U)

/-- Absolute actual-array time of the selected attempt. -/
noncomputable def selectedTime (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  attemptTime p m U (firstStrictAttempt p m U)

/-- Literal real translated path after the selected attempt. -/
noncomputable def selectedFutureR (p : ℝ) (m : ℕ) (U : Array N) :
    ℕ → Fin N → ℝ :=
  fun n i => Swarm.pos (Swarm.actualX (N := N) p m) (n + selectedTime p m U) i U -
    (selectedLevel p m U : ℝ)

/-- Integer relative future after the selected attempt. -/
noncomputable def selectedFutureZ (p : ℝ) (m : ℕ) (U : Array N) :
    ℕ → Fin N → ℤ :=
  relFuture p m U (selectedTime p m U) ((selectedLevel p m U : ℕ) : ℤ)

/-- Exact disjoint cell on which attempt `k` is the first successful attempt. -/
def FirstSuccessCell (p : ℝ) (m : ℕ) (k : ℕ) : Set (Array N) :=
  {U | StrictAttempt p m U k ∧ ∀ j < k, ¬ StrictAttempt p m U j}

/-- The event that infinitely many attempts fail. -/
def InfiniteFailure (p : ℝ) (m : ℕ) : Set (Array N) :=
  {U | ¬ ∃ k, StrictAttempt p m U k}

/-- Fixed-attempt measurability by countable patching of the genuine
fixed-time `RegenAtStrict` event along `recTimeA`. -/
theorem measurableSet_strictAttempt (p : ℝ) (m : ℕ) (r : ℕ) :
    MeasurableSet {U : Array N | StrictAttempt p m U r} := by
  have hset : {U : Array N | StrictAttempt p m U r} =
      ⋃ t : ℕ, {U : Array N | recTimeA p m U (r + 1) = t} ∩
        {U : Array N | RegenAtStrict p m U t ((r + 1 : ℕ) : ℤ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨recTimeA p m U (r + 1), rfl, h⟩
    · rintro ⟨t, ht, hreg⟩
      change RegenAtStrict p m U (recTimeA p m U (r + 1)) ((r + 1 : ℕ) : ℤ)
      rwa [ht]
  rw [hset]
  exact MeasurableSet.iUnion fun t =>
    ((measurable_recTimeA p m (r + 1)) (measurableSet_singleton t)).inter
      (measurableSet_regenAtStrict t ((r + 1 : ℕ) : ℤ))

theorem measurable_attemptSignal (p : ℝ) (m : ℕ) (r : ℕ) :
    Measurable (fun U : Array N => attemptSignal p m U r) := by
  apply measurable_to_bool
  have hset : (fun U : Array N => attemptSignal p m U r) ⁻¹' {true} =
      {U | StrictAttempt p m U r} := by
    ext U
    simp only [Set.mem_preimage, Set.mem_singleton_iff, attemptSignal,
      decide_eq_true_eq, Set.mem_ofPred_eq]
  rw [hset]
  exact measurableSet_strictAttempt (N := N) p m r

theorem measurable_firstStrictAttempt (p : ℝ) (m : ℕ) :
    Measurable (firstStrictAttempt (N := N) p m) := by
  change Measurable (Swarm.Trials.firstSuccess
    (fun r U => attemptSignal p m U r) {true})
  apply Swarm.Trials.measurable_firstSuccess
  intro k
  exact (measurable_attemptSignal (N := N) p m k) (measurableSet_singleton true)

theorem measurable_selectedLevel (p : ℝ) (m : ℕ) :
    Measurable (selectedLevel (N := N) p m) :=
  (measurable_firstStrictAttempt p m).add_const 1

theorem measurable_selectedTime (p : ℝ) (m : ℕ) :
    Measurable (selectedTime (N := N) p m) := by
  exact SwarmRecordMeas.measurable_comp_nat (measurable_selectedLevel p m)
    (fun k => measurable_recTimeA p m k)

theorem measurable_selectedLevel_real (p : ℝ) (m : ℕ) :
    Measurable (fun U : Array N => (selectedLevel p m U : ℝ)) := by
  exact (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_selectedLevel p m)

theorem measurable_selectedFutureR (p : ℝ) (m : ℕ) :
    Measurable (selectedFutureR (N := N) p m) := by
  exact M6Star.measurable_shiftPath p m (selectedTime p m)
    (fun U => (selectedLevel p m U : ℝ)) (measurable_selectedTime p m)
    (measurable_selectedLevel_real p m)

/-- The integer relative future is measurable by the same countable patching,
retaining the exact level cast and absolute record time. -/
theorem measurable_selectedFutureZ (p : ℝ) (m : ℕ) :
    Measurable (selectedFutureZ (N := N) p m) := by
  have hlevelZ : Measurable (fun U : Array N => ((selectedLevel p m U : ℕ) : ℤ)) := by
    have hc : Measurable (fun d : ℕ => (d : ℤ)) := measurable_of_countable _
    exact hc.comp (measurable_selectedLevel p m)
  have hF : Measurable (fun q : (ℕ × ℤ) × Array N =>
      relFuture p m q.2 q.1.1 q.1.2) := by
    refine measurable_pi_lambda _ fun n => measurable_pi_lambda _ fun i => ?_
    refine M6Star.measurable_uncurry_of_forall
      (f := fun (q : ℕ × ℤ) (U : Array N) =>
        (trajectory p m U (q.1 + n)).pos i - q.2) ?_
    intro q
    exact (measurable_posPath_apply p m N (q.1 + n) i).sub_const q.2
  have hpair : Measurable (fun U : Array N =>
      ((selectedTime p m U, ((selectedLevel p m U : ℕ) : ℤ)), U)) :=
    ((measurable_selectedTime p m).prodMk hlevelZ).prodMk measurable_id
  change Measurable (fun U : Array N =>
    relFuture p m U (selectedTime p m U) ((selectedLevel p m U : ℕ) : ℤ))
  exact hF.comp hpair

/-- The literal real future is the coordinatewise cast of the integer future. -/
theorem selectedFutureR_apply_eq_cast (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    selectedFutureR p m U n i = (selectedFutureZ p m U n i : ℝ) := by
  simp [selectedFutureR, selectedFutureZ, relFuture, Swarm.pos, Swarm.actualX, Nat.add_comm]

/-- Pointwise minimality, independent of all stochastic inputs. -/
theorem firstStrictAttempt_le_of_strictAttempt {p : ℝ} {m : ℕ} {U : Array N}
    {r : ℕ} (hr : StrictAttempt p m U r) : firstStrictAttempt p m U ≤ r := by
  change Swarm.Trials.firstSuccess (fun r U => attemptSignal p m U r) {true} U ≤ r
  apply Swarm.Trials.firstSuccess_le_of_mem
  simpa only [attemptSignal, Set.mem_singleton_iff, decide_eq_true_eq] using hr

/-- On the infinite-failure event the index is exactly the declared zero
fallback; no success conclusion is made there. -/
theorem firstStrictAttempt_eq_zero_of_infiniteFailure {p : ℝ} {m : ℕ} {U : Array N}
    (hU : U ∈ InfiniteFailure (N := N) p m) : firstStrictAttempt p m U = 0 := by
  change ¬ ∃ k, StrictAttempt p m U k at hU
  simp only [firstStrictAttempt, Swarm.Trials.firstSuccess]
  split_ifs with hex
  · exfalso
    apply hU
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simpa only [attemptSignal, Set.mem_singleton_iff,
      decide_eq_true_eq] using hk⟩
  · rfl

/-- Positive selected indices characterize the exact first-success cells. -/
theorem firstStrictAttempt_eq_succ_iff {p : ℝ} {m : ℕ} {U : Array N} {k : ℕ} :
    firstStrictAttempt p m U = k + 1 ↔ U ∈ FirstSuccessCell p m (k + 1) := by
  change Swarm.Trials.firstSuccess (fun r U => attemptSignal p m U r) {true} U = k + 1 ↔ _
  rw [Swarm.Trials.firstSuccess_eq_succ_iff]
  simp only [FirstSuccessCell, Set.mem_ofPred_eq, attemptSignal,
    Set.mem_singleton_iff, decide_eq_true_eq]

theorem measurableSet_firstSuccessCell (p : ℝ) (m : ℕ) (k : ℕ) :
    MeasurableSet (FirstSuccessCell (N := N) p m k) := by
  have hset : FirstSuccessCell (N := N) p m k =
      {U : Array N | StrictAttempt p m U k} ∩
        ⋂ j ∈ Finset.range k, {U : Array N | ¬ StrictAttempt p m U j} := by
    ext U
    simp only [FirstSuccessCell, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range, Set.mem_ofPred_eq]
  rw [hset]
  exact (measurableSet_strictAttempt (N := N) p m k).inter
    (MeasurableSet.biInter (Finset.countable_toSet (Finset.range k))
      fun j _ => (measurableSet_strictAttempt (N := N) p m j).compl)

theorem pairwise_disjoint_firstSuccessCell (p : ℝ) (m : ℕ) :
    Pairwise (fun a b => Disjoint (FirstSuccessCell (N := N) p m a)
      (FirstSuccessCell (N := N) p m b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  intro U ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact hb.2 a h ha.1
  · exact ha.2 b h hb.1

theorem iUnion_firstSuccessCell (p : ℝ) (m : ℕ) :
    (⋃ k, FirstSuccessCell (N := N) p m k) = {U | ∃ k, StrictAttempt p m U k} := by
  ext U
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    let r := Nat.find (show ∃ k, StrictAttempt p m U k from ⟨k, hk⟩)
    refine ⟨r, Nat.find_spec (show ∃ k, StrictAttempt p m U k from ⟨k, hk⟩), ?_⟩
    intro j hj
    exact Nat.find_min (show ∃ k, StrictAttempt p m U k from ⟨k, hk⟩) hj

theorem measurableSet_infiniteFailure (p : ℝ) (m : ℕ) :
    MeasurableSet (InfiniteFailure (N := N) p m) := by
  have hset : InfiniteFailure (N := N) p m =
      (⋃ k, {U : Array N | StrictAttempt p m U k})ᶜ := by
    ext U
    simp only [InfiniteFailure, Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_iUnion]
  rw [hset]
  exact (MeasurableSet.iUnion fun k => measurableSet_strictAttempt p m k).compl

/-- Null infinite failure is exactly the almost-sure finite-success input;
nothing stronger about record recurrence is hidden in this equivalence. -/
theorem ae_exists_strictAttempt_of_infiniteFailure_null {p : ℝ} {m : ℕ}
    (hnull : (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r := by
  rw [MeasureTheory.ae_iff]
  exact hnull

/-- A supplied almost-sure successful-attempt premise makes the selected
window a genuine strict regeneration almost surely. -/
theorem ae_regenAtStrict_selected {p : ℝ} {m : ℕ}
    (h : ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r) :
    ∀ᵐ U ∂(arrayMeasure N), RegenAtStrict p m U (selectedTime p m U)
      ((selectedLevel p m U : ℕ) : ℤ) := by
  have hb : ∀ᵐ U ∂(arrayMeasure N), ∃ r,
      attemptSignal p m U r ∈ ({true} : Set Bool) := by
    filter_upwards [h] with U hU
    obtain ⟨r, hr⟩ := hU
    exact ⟨r, by simpa only [attemptSignal, Set.mem_singleton_iff,
      decide_eq_true_eq] using hr⟩
  have hs := Swarm.Trials.firstSuccess_mem
    (Z := fun r U => attemptSignal p m U r) (C := {true}) (μ := arrayMeasure N) hb
  filter_upwards [hs] with U hU
  have hr : StrictAttempt p m U (firstStrictAttempt p m U) := by
    have hb : attemptSignal p m U (firstStrictAttempt p m U) = true := by
      simpa only [Set.mem_singleton_iff, firstStrictAttempt] using hU
    change decide (StrictAttempt p m U (firstStrictAttempt p m U)) = true at hb
    exact of_decide_eq_true hb
  exact hr

/-- Under the same named existence premise, the selected integer future lies
in the actual strict seed event almost surely. -/
theorem ae_selectedFutureZ_mem_strictPos {p : ℝ} {m : ℕ}
    (h : ∀ᵐ U ∂(arrayMeasure N), ∃ r, StrictAttempt p m U r) :
    ∀ᵐ U ∂(arrayMeasure N), selectedFutureZ p m U ∈ strictPos (N := N) := by
  filter_upwards [ae_regenAtStrict_selected (N := N) h] with U hU
  exact ((regenAtStrict_iff p m U (selectedTime p m U)
    ((selectedLevel p m U : ℕ) : ℤ)).mp hU).2

/-- Null-failure form of the selected genuine strict regeneration. -/
theorem ae_regenAtStrict_selected_of_infiniteFailure_null {p : ℝ} {m : ℕ}
    (hnull : (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0) :
    ∀ᵐ U ∂(arrayMeasure N), RegenAtStrict p m U (selectedTime p m U)
      ((selectedLevel p m U : ℕ) : ℤ) :=
  ae_regenAtStrict_selected (ae_exists_strictAttempt_of_infiniteFailure_null hnull)

/-- Null-failure form of the selected strict-future conclusion. -/
theorem ae_selectedFutureZ_mem_strictPos_of_infiniteFailure_null {p : ℝ} {m : ℕ}
    (hnull : (arrayMeasure N) (InfiniteFailure (N := N) p m) = 0) :
    ∀ᵐ U ∂(arrayMeasure N), selectedFutureZ p m U ∈ strictPos (N := N) :=
  ae_selectedFutureZ_mem_strictPos (ae_exists_strictAttempt_of_infiniteFailure_null hnull)

end RawStrictAttemptTower
