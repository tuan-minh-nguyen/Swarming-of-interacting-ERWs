/-
Conditional centred-increment expectation of the actual interacting trajectory
given the complete used-coordinate history.

The interacting walk is the recursive trajectory of `Swarm/Trajectory.lean` driven by the
product array of `Swarm/UniformArray.lean`.  The one-step conditional law of the *actual*
trajectory, given every array coordinate it has already consumed, is
`Transition.conditional_jumpLaw`.  Here we convert that law into a statement about
the increments of the trajectory: the centred increment
`inc - (2 p - 1) * excited indicator` has zero integral over any event of the
used-coordinate history, i.e. its conditional expectation given the complete
used-coordinate history vanishes.

The bridge to the finite jump vectors is `CurrentState.stepW_currentRecordState`,
and the finite zero-mean computation is
`DriftExpectation.centered_joint_increment_mean_zero`.
-/
import Swarm.CurrentState
import Swarm.DriftExpectation
import Swarm.HistoryDeterminism

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.History
  Swarming.Trajectory Swarming.Transition

namespace Swarming.Increment

variable {N : ℕ}

/-! ### The increment of the actual trajectory -/

/-- Signed increment of walker `i` over step `n`, as a real function of the array. -/
noncomputable def inc (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) : ℝ :=
  ((trajectory p m ω (n + 1)).pos i : ℝ) - ((trajectory p m ω n).pos i : ℝ)

@[simp] lemma inc_apply (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) :
    inc p m n i ω = ((trajectory p m ω (n + 1)).pos i : ℝ) -
      ((trajectory p m ω n).pos i : ℝ) := rfl

/-- Excitation indicator of walker `i` at time `n`, as a real number. -/
noncomputable def excitedAt (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) : ℝ :=
  (currentExcited m (U := ω) (p := p) n i : ℝ)

lemma excitedAt_eq_currentExcited (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) :
    excitedAt p m n i ω = (currentExcited m (U := ω) (p := p) n i : ℝ) := rfl

/-- The centred increment: the increment minus the conditional drift at the current state. -/
noncomputable def centredInc (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) : ℝ :=
  inc p m n i ω - (2 * currentAlpha p m ω n i - 1)

/-- The conditional drift of a single step equals `(2p-1)` times the excitation indicator. -/
lemma two_mul_currentAlpha_sub_one (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) :
    2 * currentAlpha p m ω n i - 1 = (2 * p - 1) * excitedAt p m n i ω := by
  classical
  unfold excitedAt currentExcited currentAlpha rightProbability
  by_cases h : Excited m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i) <;> simp [h]

/-! ### The Boolean jump-index partition of the array space -/

/-- For every threshold and value exactly one of the two jump sets contains the value. -/
lemma jumpSet_existsUnique (α x : ℝ) : ∃! b : Bool, x ∈ jumpSet b α := by
  rcases le_or_gt x α with h | h
  · refine ⟨true, by simp [jumpSet, h], fun b hb => ?_⟩
    cases b with
    | false =>
        simp only [jumpSet, Bool.false_eq_true, if_false, mem_Ioi] at hb
        exact absurd hb (not_lt.mpr h)
    | true => rfl
  · refine ⟨false, by simpa [jumpSet] using h, fun b hb => ?_⟩
    cases b with
    | false => rfl
    | true =>
        simp only [jumpSet, if_true, mem_Iic] at hb
        exact absurd hb (not_le.mpr h)

/-- Coordinatewise uniqueness assembles to a unique jump vector. -/
lemma forall_mem_jumpSet_existsUnique {ι : Type*} [Fintype ι] (x α : ι → ℝ) :
    ∃! v : ι → Bool, ∀ i, x i ∈ jumpSet (v i) (α i) := by
  classical
  have key : ∀ i, ∃ b, x i ∈ jumpSet b (α i) :=
    fun i => (jumpSet_existsUnique (α i) (x i)).exists
  refine ⟨fun i => Classical.choose (key i), fun i => Classical.choose_spec (key i), ?_⟩
  intro w hw
  funext i
  exact (jumpSet_existsUnique (α i) (x i)).unique (hw i) (Classical.choose_spec (key i))

/-- The cylinder of arrays whose departure uniform for walker `i` produces the jump `v i`. -/
noncomputable def jumpCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    Set (Array N) :=
  ⋂ i, (fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
    jumpSet (v i) (currentAlpha p m U n i)

@[simp] lemma mem_jumpCyl_iff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool)
    (ω : Array N) :
    ω ∈ jumpCyl p m U n v ↔
      ∀ i, ω (departureCoord p m U n i) ∈ jumpSet (v i) (currentAlpha p m U n i) :=
  Set.mem_iInter

lemma jumpCyl_measurable (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    MeasurableSet (jumpCyl p m U n v) :=
  MeasurableSet.iInter fun i =>
    (jumpSet_measurable (v i) (currentAlpha p m U n i)).preimage (measurable_pi_apply _)

/-- The unique jump vector realised by the departure uniforms of the array `ω`. -/
noncomputable def jumpIndexOf (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (ω : Array N) :
    Fin N → Bool :=
  Classical.choose (forall_mem_jumpSet_existsUnique
    (fun i => ω (departureCoord p m U n i)) (fun i => currentAlpha p m U n i))

lemma mem_jumpCyl_jumpIndexOf (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (ω : Array N) :
    ω ∈ jumpCyl p m U n (jumpIndexOf p m U n ω) :=
  (mem_jumpCyl_iff p m U n _ ω).mpr (Classical.choose_spec (forall_mem_jumpSet_existsUnique
    (fun i => ω (departureCoord p m U n i)) (fun i => currentAlpha p m U n i))).1

lemma eq_jumpIndexOf_of_mem (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {v : Fin N → Bool}
    {ω : Array N} (hv : ω ∈ jumpCyl p m U n v) : v = jumpIndexOf p m U n ω :=
  (forall_mem_jumpSet_existsUnique (fun i => ω (departureCoord p m U n i))
    (fun i => currentAlpha p m U n i)).unique ((mem_jumpCyl_iff p m U n v ω).mp hv)
    ((mem_jumpCyl_iff p m U n _ ω).mp (mem_jumpCyl_jumpIndexOf p m U n ω))

lemma exists_mem_jumpCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (ω : Array N) :
    ∃ v, ω ∈ jumpCyl p m U n v :=
  ⟨jumpIndexOf p m U n ω, mem_jumpCyl_jumpIndexOf p m U n ω⟩

/-! ### The history event decides the state at time `n` -/

lemma trajectory_eq_of_mem_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) :
    trajectory p m ω n = trajectory p m U n :=
  HistoryDeterminism.trajectory_eq_of_history p m U n hω

/-- On the history event the departure coordinate of `ω` is the recorded one. -/
lemma departureCoord_of_mem_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) (i : Fin N) :
    departureCoord p m ω n i = departureCoord p m U n i := by
  unfold departureCoord
  rw [trajectory_eq_of_mem_history p m U n hω]

/-- The current right probability is decided by the history. -/
lemma currentAlpha_of_mem_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) (i : Fin N) :
    currentAlpha p m ω n i = currentAlpha p m U n i :=
  HistoryDeterminism.currentAlpha_eq_of_history p m U n hω i

/-- The excitation indicator is decided by the history. -/
lemma excitedAt_of_mem_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) (i : Fin N) :
    excitedAt p m n i ω = excitedAt p m n i U := by
  classical
  have htr := trajectory_eq_of_mem_history p m U n hω
  by_cases h : Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i)
  · have h' : Excited m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i) := by
      simpa only [htr] using h
    unfold excitedAt currentExcited
    simp [h, h']
  · have h' : ¬ Excited m (trajectory p m ω n).ell i ((trajectory p m ω n).pos i) := by
      simpa only [htr] using h
    unfold excitedAt currentExcited
    simp [h, h']

/-! ### The history event forces the realised jump -/

/-- The jump cylinder event is the jump event of `Transition` intersected with the history. -/
theorem history_inter_jumpCyl_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    historyEvent (actualHistory p m U n) ∩ jumpCyl p m U n v =
      historyEvent (actualHistory p m U n) ∩ jumpEvent p m n v := by
  ext ω
  exact (jumpEvent_history_eq_inter p m U n v (ω := ω)).symm

/-- The realised jump of `ω` at step `n` is prescribed by its jump cylinder. -/
lemma nextPos_eq_of_mem_history_jumpCyl (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) {v : Fin N → Bool} (hv : ω ∈ jumpCyl p m U n v)
    (i : Fin N) :
    (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i + jumpShift (v i) := by
  have hmem : ω (departureCoord p m ω n i) ∈ jumpSet (v i) (currentAlpha p m ω n i) := by
    have h := (mem_jumpCyl_iff p m U n v ω).mp hv i
    rw [departureCoord_of_mem_history p m U n hω i,
      currentAlpha_of_mem_history p m U n hω i]
    exact h
  have hstep := (nextPos_eq_iff p m ω n v i).mpr hmem
  simpa only [trajectory_succ, nextWalkState_pos] using hstep

/-- Consequently the increment of `ω` on its jump cylinder is the signed jump. -/
lemma inc_eq_jumpShift (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) {v : Fin N → Bool} (hv : ω ∈ jumpCyl p m U n v)
    (i : Fin N) : inc p m n i ω = (jumpShift (v i) : ℝ) := by
  have h := nextPos_eq_of_mem_history_jumpCyl p m U n hω hv i
  simp only [inc, h, Int.cast_add]
  ring

/-! ### The used-coordinate projection and the conditional jump law -/

/-- The signed jump coefficient multiplying the indicator of a jump cylinder. -/
noncomputable def jumpCoeff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    (v : Fin N → Bool) : ℝ :=
  (jumpShift (v i) : ℝ) - (2 * currentAlpha p m U n i - 1)

lemma jumpWeight_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (b : Bool) : 0 < jumpWeight b α := by
  cases b <;> simp [jumpWeight] <;> linarith

lemma jumpWeight_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (b : Bool) : 0 ≤ jumpWeight b α :=
  (jumpWeight_pos h0 h1 b).le

/-- The signed-increment part of `centredInc` on the jump cylinder of `v`. -/
lemma centredInc_eq_jumpCoeff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) {v : Fin N → Bool} (hv : ω ∈ jumpCyl p m U n v)
    (i : Fin N) : centredInc p m n i ω = jumpCoeff p m U n i v := by
  unfold centredInc jumpCoeff
  rw [inc_eq_jumpShift p m U n hω hv i, currentAlpha_of_mem_history p m U n hω i]

/-- On the history event the centred increment is the finite sum over jump cylinders. -/
theorem indicator_centredInc_eq_sum (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (historyEvent (actualHistory p m U n)).indicator (fun ω => centredInc p m n i ω) =
      fun ω => ∑ v : Fin N → Bool,
        ((historyEvent (actualHistory p m U n) ∩ jumpCyl p m U n v).indicator
          (fun _ => jumpCoeff p m U n i v)) ω := by
  classical
  funext ω
  by_cases hω : ω ∈ historyEvent (actualHistory p m U n)
  · rw [Set.indicator_of_mem hω, Finset.sum_eq_single (jumpIndexOf p m U n ω)]
    · rw [Set.indicator_of_mem (Set.mem_inter hω (mem_jumpCyl_jumpIndexOf p m U n ω))]
      exact centredInc_eq_jumpCoeff p m U n hω (mem_jumpCyl_jumpIndexOf p m U n ω) i
    · intro v _ hv
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hv (eq_jumpIndexOf_of_mem p m U n hmem.2)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Set.indicator_of_notMem hω]
    symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hω hmem.1

/-- Projection of an array onto the coordinates used before time `n`. -/
noncomputable def pastProj (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Array N → (used (actualHistory p m U n) → ℝ) :=
  fun ω j => ω j

lemma measurable_pastProj (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    Measurable (pastProj p m U n : Array N → (used (actualHistory p m U n) → ℝ)) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j : Fin N × ℤ × ℕ)

lemma pastProj_preimage_compatible (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    pastProj p m U n ⁻¹' compatible (actualHistory p m U n) =
      historyEvent (actualHistory p m U n) :=
  preimage_compatible _

lemma measurableSet_historyEvent (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    MeasurableSet (historyEvent (actualHistory p m U n)) := by
  rw [← pastProj_preimage_compatible p m U n]
  exact (compatible_measurable _).preimage (measurable_pastProj p m U n)

lemma pastProj_inter_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Set (used (actualHistory p m U n) → ℝ)) :
    pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) =
      pastProj p m U n ⁻¹' (A ∩ compatible (actualHistory p m U n)) := by
  rw [← pastProj_preimage_compatible p m U n, Set.preimage_inter]

/-- **The conditional jump law given the complete used-coordinate history.** For a jump
vector `v`, the event that every walker takes the jump prescribed by `v` is independent of
any event determined by the used coordinates, with the product of the current left/right
probabilities. -/
theorem measure_pastProj_inter_jumpCyl {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {A : Set (used (actualHistory p m U n) → ℝ)}
    (hA : MeasurableSet A) (v : Fin N → Bool) :
    arrayMeasure N (pastProj p m U n ⁻¹' A ∩ jumpCyl p m U n v) =
      arrayMeasure N (pastProj p m U n ⁻¹' A) *
        ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
  have hind := SwarmIID.indep_fresh_finset (array_independent N) (fun c => measurable_pi_apply c)
    (nextCoords_injective p m U n) (fun i => next_not_mem_used_actualHistory p m U n i)
    A hA (fun i => jumpSet (v i) (currentAlpha p m U n i)) (fun i => jumpSet_measurable _ _)
  change arrayMeasure N (pastProj p m U n ⁻¹' A ∩ jumpCyl p m U n v) = _ at hind
  rw [hind]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [arrayMeasure_preimage_set N _ _ (jumpSet_measurable _ _),
    uniform01_jumpSet (currentAlpha_pos hp0 hp1 m U n i) (currentAlpha_lt_one hp0 hp1 m U n i) (v i)]

/-- The same law with the history event itself. -/
theorem measure_history_inter_jumpCyl {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ jumpCyl p m U n v) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
  rw [history_inter_jumpCyl_eq]
  exact conditional_jumpLaw hp0 hp1 m U n v

/-- The same law for an arbitrary past-determined event inside the history. -/
theorem measure_pastProj_inter_history_inter_jumpCyl {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {A : Set (used (actualHistory p m U n) → ℝ)}
    (hA : MeasurableSet A) (v : Fin N → Bool) :
    arrayMeasure N ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩
        jumpCyl p m U n v) =
      arrayMeasure N (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) *
        ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
  rw [pastProj_inter_history p m U n A]
  exact measure_pastProj_inter_jumpCyl hp0 hp1 m U n (hA.inter (compatible_measurable _)) v


/-! ### The conditional mean of the centred increment vanishes -/

/-- The weight product is the finite jump-vector weight of the capped record state. -/
lemma toReal_prod_jumpWeight {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (v : Fin N → Bool) :
    (∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i))).toReal =
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v := by
  rw [CurrentState.stepW_currentRecordState, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ =>
    ENNReal.toReal_ofReal (jumpWeight_nonneg (currentAlpha_pos hp0 hp1 m U n i)
      (currentAlpha_lt_one hp0 hp1 m U n i) (v i))

/-- The finite signed mean of the jump vector is the conditional drift. -/
lemma sum_stepW_jumpCoeff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    ∑ v : Fin N → Bool, SimJump.stepW p m (CurrentState.currentRecordState p m U n) v *
      jumpCoeff p m U n i v = 0 := by
  have h := DriftExpectation.centered_joint_increment_mean_zero p
    (CurrentState.currentRecordState p m U n) i
  simp only [CurrentState.qRight_currentRecordState, jumpCoeff] at h ⊢
  exact h

/-- The finite signed mean of the jump vector is the conditional drift (uncentred form). -/
lemma sum_stepW_jumpShift (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    ∑ v : Fin N → Bool, SimJump.stepW p m (CurrentState.currentRecordState p m U n) v *
      (jumpShift (v i) : ℝ) = 2 * currentAlpha p m U n i - 1 := by
  have h := DriftExpectation.jointSignedMean_eq p (CurrentState.currentRecordState p m U n) i
  simp only [CurrentState.qRight_currentRecordState, DriftExpectation.jointSignedMean] at h ⊢
  exact h

/-- On the history event the centred increment decomposes over the jump cylinders. -/
theorem indicator_centredInc_eq_sum_pastProj {p : ℝ} (m : ℕ) (U : Array N) (n : ℕ)
    {A : Set (used (actualHistory p m U n) → ℝ)} (i : Fin N) :
    (fun ω => (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω) ω) =
      fun ω => ∑ v : Fin N → Bool,
        (((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩ jumpCyl p m U n v).indicator
          (fun _ => jumpCoeff p m U n i v)) ω := by
  classical
  funext ω
  by_cases hω : ω ∈ pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)
  · have hH : ω ∈ historyEvent (actualHistory p m U n) := hω.2
    rw [Set.indicator_of_mem hω, Finset.sum_eq_single (jumpIndexOf p m U n ω)]
    · rw [Set.indicator_of_mem (Set.mem_inter hω (mem_jumpCyl_jumpIndexOf p m U n ω))]
      exact centredInc_eq_jumpCoeff p m U n hH (mem_jumpCyl_jumpIndexOf p m U n ω) i
    · intro v _ hv
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hv (eq_jumpIndexOf_of_mem p m U n hmem.2)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Set.indicator_of_notMem hω]
    symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hω hmem.1

/-- **The conditional expectation of the centred increment given the complete
used-coordinate history is zero.** For every event determined by the array coordinates
used before time `n`, restricted to the realised history, the integral of the centred
increment of walker `i` over step `n` vanishes. -/
theorem integral_indicator_centredInc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {A : Set (used (actualHistory p m U n) → ℝ)}
    (hA : MeasurableSet A) (i : Fin N) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω)) ω ∂(arrayMeasure N) = 0 := by
  classical
  set Hs : Set (Array N) := pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) with hHs
  have hmeasA : MeasurableSet (pastProj p m U n ⁻¹' A) :=
    hA.preimage (measurable_pastProj p m U n)
  have hmeasH : MeasurableSet (historyEvent (actualHistory p m U n)) :=
    measurableSet_historyEvent p m U n
  have hmeas_s : ∀ v : Fin N → Bool, MeasurableSet (Hs ∩ jumpCyl p m U n v) := fun v =>
    (hmeasA.inter hmeasH).inter (jumpCyl_measurable p m U n v)
  rw [indicator_centredInc_eq_sum_pastProj (p := p) m U n (A := A) i]
  have hint : ∀ v : Fin N → Bool, Integrable
      (fun ω => ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => jumpCoeff p m U n i v)) ω)
      (arrayMeasure N) := fun v => (integrable_const _).indicator (hmeas_s v)
  rw [integral_finsetSum Finset.univ (fun v _ => hint v)]
  have hval : ∀ v : Fin N → Bool,
      ∫ ω, ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => jumpCoeff p m U n i v)) ω
        ∂(arrayMeasure N) =
        (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) * jumpCoeff p m U n i v := by
    intro v
    rw [integral_indicator_const _ (hmeas_s v), smul_eq_mul]
  simp only [hval]
  have hreal : ∀ v : Fin N → Bool, (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) =
      (arrayMeasure N).real Hs * SimJump.stepW p m (CurrentState.currentRecordState p m U n) v := by
    intro v
    have hlaw : (arrayMeasure N) (Hs ∩ jumpCyl p m U n v) =
        (arrayMeasure N) Hs *
          ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
      rw [hHs]
      exact measure_pastProj_inter_history_inter_jumpCyl hp0 hp1 m U n hA v
    rw [measureReal_def, measureReal_def, hlaw, ENNReal.toReal_mul,
      toReal_prod_jumpWeight hp0 hp1 m U n v]
  simp only [hreal]
  have hfac : ∑ v : Fin N → Bool, (arrayMeasure N).real Hs *
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v =
      (arrayMeasure N).real Hs * ∑ v : Fin N → Bool,
        SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hfac, sum_stepW_jumpCoeff p m U n i, mul_zero]

/-- **The conditional drift of the actual trajectory.** Over any event determined by the
used coordinates and compatible with the realised history, the mean increment of walker `i`
over step `n` is `(2p-1)` times its current excitation indicator. -/
theorem integral_indicator_inc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {A : Set (used (actualHistory p m U n) → ℝ)}
    (hA : MeasurableSet A) (i : Fin N) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => inc p m n i ω)) ω ∂(arrayMeasure N) =
      (2 * p - 1) * excitedAt p m n i U *
        (arrayMeasure N).real (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) := by
  classical
  set Hs : Set (Array N) := pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) with hHs
  have hmeasA : MeasurableSet (pastProj p m U n ⁻¹' A) :=
    hA.preimage (measurable_pastProj p m U n)
  have hmeasH : MeasurableSet (historyEvent (actualHistory p m U n)) :=
    measurableSet_historyEvent p m U n
  have hmeas : MeasurableSet Hs := hmeasA.inter hmeasH
  have hpoint : (fun ω => Hs.indicator (fun ω => inc p m n i ω) ω) =
      fun ω => Hs.indicator (fun ω => centredInc p m n i ω) ω +
        (2 * p - 1) * excitedAt p m n i U * Hs.indicator (1 : Array N → ℝ) ω := by
    funext ω
    by_cases hω : ω ∈ Hs
    · have hH : ω ∈ historyEvent (actualHistory p m U n) := hω.2
      have he : excitedAt p m n i ω = excitedAt p m n i U := excitedAt_of_mem_history p m U n hH i
      have h2 := two_mul_currentAlpha_sub_one p m n i ω
      simp only [Set.indicator_of_mem hω, Pi.one_apply, centredInc, he] at h2 ⊢
      rw [h2]
      ring
    · simp only [Set.indicator_of_notMem hω]
      ring
  have hInt1 : Integrable (fun ω => Hs.indicator (fun ω => centredInc p m n i ω) ω)
      (arrayMeasure N) := by
    rw [indicator_centredInc_eq_sum_pastProj (p := p) m U n (A := A) i]
    exact integrable_finsetSum _ fun v _ =>
      (integrable_const _).indicator ((hmeasA.inter hmeasH).inter (jumpCyl_measurable p m U n v))
  have hInt2 : Integrable (fun ω => (2 * p - 1) * excitedAt p m n i U *
      Hs.indicator (1 : Array N → ℝ) ω) (arrayMeasure N) :=
    ((integrable_const (1 : ℝ)).indicator hmeas).const_mul _
  rw [hpoint, integral_add hInt1 hInt2]
  rw [integral_indicator_centredInc hp0 hp1 m U n hA i, zero_add,
    integral_const_mul, integral_indicator_one hmeas]

/-- The drift martingale increment of the actual trajectory. -/
lemma driftMartingale_increment (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) :
    driftMartingale p m ω (n + 1) i - driftMartingale p m ω n i = centredInc p m n i ω := by
  have hexc : ((excitedSteps p m ω (n + 1) i : ℕ) : ℝ) =
      (excitedSteps p m ω n i : ℝ) + excitedAt p m n i ω := by
    simp [excitedSteps, Finset.sum_range_succ, excitedAt]
  have h2 := two_mul_currentAlpha_sub_one p m n i ω
  simp only [driftMartingale, centredInc, inc, hexc]
  rw [h2]
  ring

/-- **The drift martingale has conditionally zero increments.** The increment of
`driftMartingale` over step `n`, integrated over any event determined by the used
coordinates and compatible with the realised history, vanishes. -/
theorem integral_indicator_driftMartingale_increment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {A : Set (used (actualHistory p m U n) → ℝ)}
    (hA : MeasurableSet A) (i : Fin N) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => driftMartingale p m ω (n + 1) i - driftMartingale p m ω n i)) ω
        ∂(arrayMeasure N) = 0 := by
  simp only [driftMartingale_increment]
  exact integral_indicator_centredInc hp0 hp1 m U n hA i

/-- The centred increment with the drifted mean `(2p-1)` times the excitation indicator. -/
lemma centredInc_eq_inc_sub (p : ℝ) (m n : ℕ) (i : Fin N) (ω : Array N) :
    centredInc p m n i ω = inc p m n i ω - (2 * p - 1) * excitedAt p m n i ω := by
  simp only [centredInc, two_mul_currentAlpha_sub_one]


/-! ### The used-coordinate history σ-algebra -/

/-- The σ-algebra generated by the array coordinates used before time `n`. -/
noncomputable abbrev usedSigma (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : MeasurableSpace (Array N) :=
  MeasurableSpace.comap (pastProj p m U n) inferInstance

lemma measurableSet_usedSigma_iff (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {G : Set (Array N)} :
    MeasurableSet[usedSigma p m U n] G ↔
      ∃ A : Set (used (actualHistory p m U n) → ℝ), MeasurableSet A ∧ pastProj p m U n ⁻¹' A = G :=
  MeasurableSpace.measurableSet_comap

/-- Every used-coordinate event is (in particular) an event of the ambient σ-algebra. -/
lemma measurableSet_of_usedSigma (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {s : Set (Array N)}
    (hs : MeasurableSet[usedSigma p m U n] s) : MeasurableSet s := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hs
  exact hA.preimage (measurable_pastProj p m U n)

lemma usedSigma_le_pi (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    usedSigma p m U n ≤ MeasurableSpace.pi := fun _ hs => measurableSet_of_usedSigma p m U n hs

lemma historyEvent_mem_usedSigma (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    MeasurableSet[usedSigma p m U n] (historyEvent (actualHistory p m U n)) :=
  (measurableSet_usedSigma_iff p m U n).mpr
    ⟨compatible (actualHistory p m U n), compatible_measurable _,
      pastProj_preimage_compatible p m U n⟩

/-- The conditional jump law holds for every event of the used-coordinate σ-algebra. -/
theorem measure_usedSigma_inter_jumpCyl {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) (v : Fin N → Bool) :
    arrayMeasure N (G ∩ jumpCyl p m U n v) =
      arrayMeasure N G * ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  exact measure_pastProj_inter_jumpCyl hp0 hp1 m U n hA v

/-- **The conditional expectation of the centred increment vanishes on the whole
used-coordinate history σ-algebra.** -/
theorem integral_indicator_centredInc_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) (i : Fin N) :
    ∫ ω, ((G ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω)) ω ∂(arrayMeasure N) = 0 := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  exact integral_indicator_centredInc hp0 hp1 m U n hA i

/-- **The conditional drift on the whole used-coordinate history σ-algebra.** -/
theorem integral_indicator_inc_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) (i : Fin N) :
    ∫ ω, ((G ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => inc p m n i ω)) ω ∂(arrayMeasure N) =
      (2 * p - 1) * excitedAt p m n i U *
        (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  exact integral_indicator_inc hp0 hp1 m U n hA i

/-! ### The conditional second moment -/

/-- The exact conditional second moment of a single jump. -/
lemma sum_stepW_jumpCoeff_sq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    ∑ v : Fin N → Bool, SimJump.stepW p m (CurrentState.currentRecordState p m U n) v *
      jumpCoeff p m U n i v ^ 2 =
      4 * currentAlpha p m U n i * (1 - currentAlpha p m U n i) := by
  classical
  set d : ℝ := 2 * currentAlpha p m U n i - 1 with hd
  have h1 : ∑ v : Fin N → Bool,
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v = 1 :=
    SimJump.stepW_sum_one p m _
  have h2 : ∑ v : Fin N → Bool,
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * (jumpShift (v i) : ℝ) = d := by
    rw [hd]
    exact sum_stepW_jumpShift p m U n i
  have hpt : ∀ v : Fin N → Bool,
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v ^ 2 =
        (1 + d ^ 2) * SimJump.stepW p m (CurrentState.currentRecordState p m U n) v -
          2 * d * (SimJump.stepW p m (CurrentState.currentRecordState p m U n) v *
            (jumpShift (v i) : ℝ)) := by
    intro v
    have hd' : jumpCoeff p m U n i v = (jumpShift (v i) : ℝ) - d := by
      simp only [jumpCoeff, hd]
    have hsq : (jumpShift (v i) : ℝ) ^ 2 = 1 := by
      cases hv : v i <;> simp [jumpShift]
    have hexp : ((jumpShift (v i) : ℝ) - d) ^ 2 =
        1 - 2 * (jumpShift (v i) : ℝ) * d + d ^ 2 := by
      linear_combination hsq
    rw [hd', hexp]
    ring
  simp only [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, hd]
  ring

/-- The conditional second moment of the centred increment is at most one. -/
lemma sum_stepW_jumpCoeff_sq_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    ∑ v : Fin N → Bool, SimJump.stepW p m (CurrentState.currentRecordState p m U n) v *
      jumpCoeff p m U n i v ^ 2 ≤ 1 := by
  rw [sum_stepW_jumpCoeff_sq]
  nlinarith [sq_nonneg (2 * currentAlpha p m U n i - 1)]

/-- Squaring and restricting to the history gives the sum over the jump cylinders. -/
theorem indicator_centredInc_sq_eq_sum_pastProj (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    {A : Set (used (actualHistory p m U n) → ℝ)} (i : Fin N) :
    (fun ω => (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω ^ 2) ω) =
      fun ω => ∑ v : Fin N → Bool,
        (((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩ jumpCyl p m U n v).indicator
          (fun _ => jumpCoeff p m U n i v ^ 2)) ω := by
  classical
  funext ω
  by_cases hω : ω ∈ pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)
  · have hH : ω ∈ historyEvent (actualHistory p m U n) := hω.2
    rw [Set.indicator_of_mem hω, Finset.sum_eq_single (jumpIndexOf p m U n ω)]
    · rw [Set.indicator_of_mem (Set.mem_inter hω (mem_jumpCyl_jumpIndexOf p m U n ω)),
        centredInc_eq_jumpCoeff p m U n hH (mem_jumpCyl_jumpIndexOf p m U n ω) i]
    · intro v _ hv
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hv (eq_jumpIndexOf_of_mem p m U n hmem.2)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Set.indicator_of_notMem hω]
    symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hω hmem.1

/-- The conditional second moment of the centred increment over a used-coordinate event. -/
theorem integral_indicator_centredInc_sq {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ)
    {A : Set (used (actualHistory p m U n) → ℝ)} (hA : MeasurableSet A) (i : Fin N) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω ^ 2)) ω ∂(arrayMeasure N) =
      (arrayMeasure N).real (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) *
        ∑ v : Fin N → Bool,
          SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v ^ 2 := by
  classical
  set Hs : Set (Array N) := pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) with hHs
  have hmeasA : MeasurableSet (pastProj p m U n ⁻¹' A) :=
    hA.preimage (measurable_pastProj p m U n)
  have hmeasH : MeasurableSet (historyEvent (actualHistory p m U n)) :=
    measurableSet_historyEvent p m U n
  have hmeas_s : ∀ v : Fin N → Bool, MeasurableSet (Hs ∩ jumpCyl p m U n v) := fun v =>
    (hmeasA.inter hmeasH).inter (jumpCyl_measurable p m U n v)
  rw [indicator_centredInc_sq_eq_sum_pastProj (p := p) m U n (A := A) i]
  have hint : ∀ v : Fin N → Bool, Integrable
      (fun ω => ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => jumpCoeff p m U n i v ^ 2)) ω)
      (arrayMeasure N) := fun v => (integrable_const _).indicator (hmeas_s v)
  rw [integral_finsetSum Finset.univ (fun v _ => hint v)]
  have hval : ∀ v : Fin N → Bool,
      ∫ ω, ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => jumpCoeff p m U n i v ^ 2)) ω
        ∂(arrayMeasure N) =
        (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) * jumpCoeff p m U n i v ^ 2 := by
    intro v
    rw [integral_indicator_const _ (hmeas_s v), smul_eq_mul]
  simp only [hval]
  have hreal : ∀ v : Fin N → Bool, (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) =
      (arrayMeasure N).real Hs * SimJump.stepW p m (CurrentState.currentRecordState p m U n) v := by
    intro v
    have hlaw : (arrayMeasure N) (Hs ∩ jumpCyl p m U n v) =
        (arrayMeasure N) Hs *
          ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
      rw [hHs]
      exact measure_pastProj_inter_history_inter_jumpCyl hp0 hp1 m U n hA v
    rw [measureReal_def, measureReal_def, hlaw, ENNReal.toReal_mul,
      toReal_prod_jumpWeight hp0 hp1 m U n v]
  simp only [hreal]
  have hfac : ∑ v : Fin N → Bool, (arrayMeasure N).real Hs *
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v ^ 2 =
      (arrayMeasure N).real Hs * ∑ v : Fin N → Bool,
        SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * jumpCoeff p m U n i v ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hfac]

/-- **The conditional second moment bound used for the martingale strong law.** Over any
event of the used-coordinate history, the mean square of the centred increment of walker
`i` over step `n` is at most the probability of the event. -/
theorem integral_indicator_centredInc_sq_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ)
    {A : Set (used (actualHistory p m U n) → ℝ)} (hA : MeasurableSet A) (i : Fin N) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω ^ 2)) ω ∂(arrayMeasure N) ≤
      (arrayMeasure N).real (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) := by
  rw [integral_indicator_centredInc_sq hp0 hp1 m U n hA i]
  have h0 : (0 : ℝ) ≤ (arrayMeasure N).real
      (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) :=
    ENNReal.toReal_nonneg
  nlinarith [sum_stepW_jumpCoeff_sq_le p m U n i]

/-- **The conditional expectation of the centred increment given the complete
used-coordinate history vanishes almost surely.** For every event `G` of the
used-coordinate σ-algebra, the conditional expectation of the history-restricted centred
increment w.r.t. that σ-algebra is zero. -/
theorem condExp_indicator_centredInc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) (i : Fin N) :
    (MeasureTheory.condExp (usedSigma p m U n) (arrayMeasure N)
        (fun ω => (G ∩ historyEvent (actualHistory p m U n)).indicator
          (fun ω => centredInc p m n i ω) ω)) =ᵐ[arrayMeasure N] 0 := by
  classical
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  have hmeasA : MeasurableSet (pastProj p m U n ⁻¹' A) :=
    hA.preimage (measurable_pastProj p m U n)
  have hmeasH : MeasurableSet (historyEvent (actualHistory p m U n)) :=
    measurableSet_historyEvent p m U n
  have hInt : Integrable (fun ω =>
      (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω) ω) (arrayMeasure N) := by
    rw [indicator_centredInc_eq_sum_pastProj (p := p) m U n (A := A) i]
    exact integrable_finsetSum _ fun v _ =>
      (integrable_const _).indicator ((hmeasA.inter hmeasH).inter (jumpCyl_measurable p m U n v))
  have hkey : ∀ s : Set (Array N), MeasurableSet[usedSigma p m U n] s →
      ∫ x in s, (fun ω => (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω) ω) x ∂(arrayMeasure N) = 0 := by
    intro s hs
    have hs' : MeasurableSet s := measurableSet_of_usedSigma p m U n hs
    rw [← integral_indicator hs']
    have heq : s.indicator (fun ω => (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => centredInc p m n i ω) ω) =
        fun ω => ((s ∩ pastProj p m U n ⁻¹' A) ∩ historyEvent (actualHistory p m U n)).indicator
          (fun ω => centredInc p m n i ω) ω := by
      funext ω
      by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ pastProj p m U n ⁻¹' A <;>
        by_cases h3 : ω ∈ historyEvent (actualHistory p m U n) <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, h3]
    rw [heq]
    exact integral_indicator_centredInc_usedSigma hp0 hp1 m U n (hs.inter hG) i
  have hgf : ∀ s : Set (Array N), MeasurableSet[usedSigma p m U n] s → (arrayMeasure N) s < ⊤ →
      IntegrableOn (fun _ => (0 : ℝ)) s (arrayMeasure N) := fun s _ _ => integrableOn_zero
  have hge : ∀ s : Set (Array N), MeasurableSet[usedSigma p m U n] s → (arrayMeasure N) s < ⊤ →
      ∫ x in s, (fun _ => (0 : ℝ)) x ∂(arrayMeasure N) =
        ∫ x in s, (fun ω =>
          (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
            (fun ω => centredInc p m n i ω) ω) x ∂(arrayMeasure N) := by
    intro s hs _
    rw [hkey s hs]
    simp
  exact (ae_eq_condExp_of_forall_setIntegral_eq (m := usedSigma p m U n) (m₀ := MeasurableSpace.pi)
    (μ := arrayMeasure N)
    (f := fun ω => (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
      (fun ω => centredInc p m n i ω) ω)
    (g := fun _ => (0 : ℝ)) (usedSigma_le_pi p m U n) hInt hgf hge
    aestronglyMeasurable_zero).symm

/-! ### The conditional law of the next jump vector -/

/-- **The conditional law of the next jump vector given the complete used-coordinate
history.** For any observable `F` of the next jump vector and any event determined by the
used coordinates and compatible with the realised history, the mean of `F` is the value of
`F` under the product jump law of the capped record state. -/
theorem integral_indicator_jumpObservable {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ)
    {A : Set (used (actualHistory p m U n) → ℝ)} (hA : MeasurableSet A)
    (F : (Fin N → Bool) → ℝ) :
    ∫ ω, ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)).indicator
        (fun ω => F (jumpIndexOf p m U n ω))) ω ∂(arrayMeasure N) =
      (arrayMeasure N).real (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) *
        ∑ v : Fin N → Bool, SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * F v := by
  classical
  set Hs : Set (Array N) := pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) with hHs
  have hmeasA : MeasurableSet (pastProj p m U n ⁻¹' A) :=
    hA.preimage (measurable_pastProj p m U n)
  have hmeasH : MeasurableSet (historyEvent (actualHistory p m U n)) :=
    measurableSet_historyEvent p m U n
  have hmeas_s : ∀ v : Fin N → Bool, MeasurableSet (Hs ∩ jumpCyl p m U n v) := fun v =>
    (hmeasA.inter hmeasH).inter (jumpCyl_measurable p m U n v)
  have hpoint : (fun ω => Hs.indicator (fun ω => F (jumpIndexOf p m U n ω)) ω) =
      fun ω => ∑ v : Fin N → Bool,
        ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => F v)) ω := by
    funext ω
    by_cases hω : ω ∈ Hs
    · rw [Set.indicator_of_mem hω, Finset.sum_eq_single (jumpIndexOf p m U n ω)]
      · rw [Set.indicator_of_mem (Set.mem_inter hω (mem_jumpCyl_jumpIndexOf p m U n ω))]
      · intro v _ hv
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hv (eq_jumpIndexOf_of_mem p m U n hmem.2)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Set.indicator_of_notMem hω]
      symm
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hω hmem.1
  rw [hpoint]
  have hint : ∀ v : Fin N → Bool, Integrable
      (fun ω => ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => F v)) ω) (arrayMeasure N) :=
    fun v => (integrable_const _).indicator (hmeas_s v)
  rw [integral_finsetSum Finset.univ (fun v _ => hint v)]
  have hval : ∀ v : Fin N → Bool,
      ∫ ω, ((Hs ∩ jumpCyl p m U n v).indicator (fun _ => F v)) ω ∂(arrayMeasure N) =
        (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) * F v := by
    intro v
    rw [integral_indicator_const _ (hmeas_s v), smul_eq_mul]
  simp only [hval]
  have hreal : ∀ v : Fin N → Bool, (arrayMeasure N).real (Hs ∩ jumpCyl p m U n v) =
      (arrayMeasure N).real Hs * SimJump.stepW p m (CurrentState.currentRecordState p m U n) v := by
    intro v
    have hlaw : (arrayMeasure N) (Hs ∩ jumpCyl p m U n v) =
        (arrayMeasure N) Hs *
          ∏ i, ENNReal.ofReal (jumpWeight (v i) (currentAlpha p m U n i)) := by
      rw [hHs]
      exact measure_pastProj_inter_history_inter_jumpCyl hp0 hp1 m U n hA v
    rw [measureReal_def, measureReal_def, hlaw, ENNReal.toReal_mul,
      toReal_prod_jumpWeight hp0 hp1 m U n v]
  simp only [hreal]
  have hfac : ∑ v : Fin N → Bool, (arrayMeasure N).real Hs *
      SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * F v =
      (arrayMeasure N).real Hs * ∑ v : Fin N → Bool,
        SimJump.stepW p m (CurrentState.currentRecordState p m U n) v * F v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hfac]

end Swarming.Increment


