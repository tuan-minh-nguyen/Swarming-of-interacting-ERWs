/-
Predictive (history-conditional) fairness of the increments of the *actual* auxiliary
symmetric walk `Swarming.Trajectory.symmetricWalk` under `Swarming.Uniform.arrayMeasure`,
together with the unconditional joint first-step law of the whole swarm.

Mathematical point: the coordinate consumed at departure `n` of walker `i` depends on the
array `U` itself, so the sign increments are *not* a fixed-index composition of independent
coordinates.  What is true is that the complete used-coordinate history determines the
trajectory (`HistoryDeterminism.trajectory_eq_of_history`), while the next coordinates are
fresh (`History.next_not_mem_used_actualHistory`) and therefore carry the product
Uniform(0,1) law conditionally on the history
(`History.measure_actualHistory_and_next_sets`).  Feeding the two threshold cells
`{u | 2u ≤ 1}` and `{u | 2u > 1}` (both of uniform mass `1/2`; the boundary `u = 1/2` is a
null singleton) into that conditional law gives the exact fair two-point predictive law of
the actual increment.
-/
import Swarm.HistoryDeterminism
import Swarm.HistoryLaw

namespace Swarming.Fair

open MeasureTheory ProbabilityTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.History
  Swarming.CurrentState
open scoped ENNReal BigOperators

variable {N : ℕ}

/-! ### The increment and the path recursion -/

/-- The increment of the auxiliary symmetric walk at departure `n` of walker `i`. -/
noncomputable def symmInc (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) : ℤ :=
  symmetricStep (U (departureCoord p m U n i))

lemma symmInc_eq_walkSucc (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmetricWalk p m U i (n + 1) = symmetricWalk p m U i n + symmInc p m U i n := rfl

/-- Exact path recursion: the actual auxiliary walk is the sum of its increments. -/
theorem symmetricWalk_eq_sum_range (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmetricWalk p m U i n = ∑ k ∈ Finset.range n, symmInc p m U i k := by
  induction n with
  | zero => simp [symmetricWalk]
  | succ n ih => rw [symmInc_eq_walkSucc, ih, Finset.sum_range_succ]

lemma symmInc_val (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    symmInc p m U i n = 1 ∨ symmInc p m U i n = -1 := by
  unfold symmInc symmetricStep
  split_ifs <;> simp

/-! ### The two sign cells of the asymmetric threshold `2u ≤ 1` -/

/-- The set of uniforms producing the sign `s`. -/
def signCell (s : ℤ) : Set ℝ := {u | symmetricStep u = s}

lemma signCell_one : signCell 1 = Iic (1 / 2 : ℝ) := by
  ext u
  simp only [signCell, mem_ofPred_eq, mem_Iic, symmetricStep]
  by_cases h : 2 * u ≤ 1
  · rw [if_pos h]
    exact ⟨fun _ => by linarith, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd h (by linarith)⟩

lemma signCell_neg_one : signCell (-1) = Ioi (1 / 2 : ℝ) := by
  ext u
  simp only [signCell, mem_ofPred_eq, mem_Ioi, symmetricStep]
  by_cases h : 2 * u ≤ 1
  · rw [if_pos h]
    exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd h (by linarith)⟩
  · rw [if_neg h]
    exact ⟨fun _ => by linarith, fun _ => rfl⟩

lemma measurable_symmetricStep : Measurable (fun u : ℝ => symmetricStep u) := by
  unfold symmetricStep
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
    measurable_const

lemma measurableSet_signCell (s : ℤ) : MeasurableSet (signCell s) := by
  have h : signCell s = (fun u : ℝ => symmetricStep u) ⁻¹' {s} := rfl
  rw [h]
  exact measurable_symmetricStep (measurableSet_singleton s)

/-- Both sign cells carry exact uniform mass `1/2`.  The boundary case `2u = 1` is counted in
`signCell 1` and has zero mass, so the asymmetric `≤` threshold is harmless. -/
lemma uniform01_signCell {s : ℤ} (hs : s = 1 ∨ s = -1) :
    uniform01 (signCell s) = ENNReal.ofReal (1 / 2) := by
  rcases hs with rfl | rfl
  · rw [signCell_one, uniform01_Iic (by norm_num) (by norm_num)]
  · rw [signCell_neg_one, uniform01_Ioi (by norm_num) (by norm_num)]
    norm_num

/-! ### The history determines the consumed coordinates -/

/-- On the complete used-coordinate history of the reference array, the array's own next
departure coordinate is the reference one: the history determines the recursive state. -/
lemma departureCoord_eq_of_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {ω : Array N} (hω : ω ∈ historyEvent (actualHistory p m U n)) :
    departureCoord p m ω n i = departureCoord p m U n i := by
  unfold departureCoord
  rw [HistoryDeterminism.trajectory_eq_of_history p m U n hω]

/-- On the history event, the actual next increment of the process is the value at the
reference departure coordinate. -/
lemma symmInc_eq_on_history (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {ω : Array N} (hω : ω ∈ historyEvent (actualHistory p m U n)) :
    symmInc p m ω i n = symmetricStep (ω (departureCoord p m U n i)) := by
  unfold symmInc
  rw [departureCoord_eq_of_history p m U n i hω]

/-! ### The predictive fair slice -/

/-- **Predictive fair-slice law.**  Conditionally on the complete used-coordinate history of
the actual trajectory at time `n`, the value read by the process at the (fresh) next
departure coordinate of walker `i` falls in a prescribed measurable set with exactly its
Uniform(0,1) probability. -/
theorem measure_history_and_freshCoordinate (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | ω (departureCoord p m U n i) ∈ J}) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) * uniform01 J := by
  have hI : ∀ j : Fin N, MeasurableSet (if j = i then J else univ) := by
    intro j
    by_cases h : j = i
    · subst h
      simpa using hJ
    · simp [h]
  have hkey := measure_actualHistory_and_next_sets (N := N) p m U n
    (fun j => if j = i then J else univ) hI
  have hset : (⋂ j, (fun ω : Array N => ω (departureCoord p m U n j)) ⁻¹'
      (if j = i then J else univ)) =
      {ω : Array N | ω (departureCoord p m U n i) ∈ J} := by
    ext ω
    simp only [mem_iInter, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h => by
        have := h i
        rwa [if_pos rfl] at this,
      fun h j => by
        by_cases hji : j = i
        · subst hji
          rwa [if_pos rfl]
        · rw [if_neg hji]
          exact mem_univ _⟩
  rw [hset] at hkey
  rw [hkey]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp only [if_true]
    exact arrayMeasure_preimage_set N (departureCoord p m U n i) J hJ
  · intro j _ hji
    simp [hji]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- **Predictive fair-slice law for the signs.**  Conditionally on the complete history at
time `n`, the value read by the actual process at its next departure coordinate lies in the
sign cell `signCell s` with exact probability `1/2`. -/
theorem measure_history_and_signValue (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | symmetricStep (ω (departureCoord p m U n i)) = s}) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) * ENNReal.ofReal (1 / 2) := by
  rw [← uniform01_signCell hs]
  exact measure_history_and_freshCoordinate p m U n i (signCell s) (measurableSet_signCell s)

/-- **Predictive fair-slice law for the actual increments of `symmetricWalk`.**  Conditionally
on the complete used-coordinate history at time `n`, the next increment of the actual
auxiliary symmetric walk of walker `i` equals `s` with exact probability `1/2`. -/
theorem measure_history_and_inc (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | symmInc p m ω i n = s}) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) * ENNReal.ofReal (1 / 2) := by
  have hset : historyEvent (actualHistory p m U n) ∩ {ω : Array N | symmInc p m ω i n = s} =
      historyEvent (actualHistory p m U n) ∩
        {ω : Array N | symmetricStep (ω (departureCoord p m U n i)) = s} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (symmInc_eq_on_history p m U n i h1).symm ▸ h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (symmInc_eq_on_history p m U n i h1).symm ▸ h2⟩
  rw [hset]
  exact measure_history_and_signValue p m U n i hs

/-- The predictive law in its most symmetric form: on the complete history event the two
possible increments have equal mass.  This is the exact "no drift at the next departure"
statement for the actual auxiliary walk. -/
theorem measure_history_inc_one_eq_neg_one (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | symmInc p m ω i n = 1}) =
      arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | symmInc p m ω i n = -1}) := by
  rw [measure_history_and_inc p m U n i (s := 1) (Or.inl rfl),
    measure_history_and_inc p m U n i (s := -1) (Or.inr rfl)]

/-- **Joint predictive fair-slice law for the whole swarm.**  Conditionally on the complete
used-coordinate history at time `n`, the vector of next increments of *all* walkers is exactly
uniform on `{±1}^N`. -/
theorem measure_history_and_incVec (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (σ : Fin N → ℤ)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        {ω : Array N | ∀ i, symmInc p m ω i n = σ i}) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) * (ENNReal.ofReal (1 / 2)) ^ N := by
  have hset : historyEvent (actualHistory p m U n) ∩ {ω : Array N | ∀ i, symmInc p m ω i n = σ i} =
      historyEvent (actualHistory p m U n) ∩
        ⋂ i, (fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' signCell (σ i) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_preimage, signCell]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j => (symmInc_eq_on_history p m U n j h1).symm ▸ h2 j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j => (symmInc_eq_on_history p m U n j h1) ▸ h2 j⟩
  rw [hset, measure_actualHistory_and_next_sets p m U n (fun i => signCell (σ i))
    (fun i => measurableSet_signCell (σ i))]
  congr 1
  have hfac : ∀ i : Fin N,
      arrayMeasure N ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' signCell (σ i))
        = ENNReal.ofReal (1 / 2) := fun i =>
    (arrayMeasure_preimage_set N (departureCoord p m U n i) (signCell (σ i))
      (measurableSet_signCell (σ i))).trans (uniform01_signCell (hσ i))
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ### The unconditional first-step law -/

/-- At time `0` the departure coordinate is the constant `(i, 0, 1)`. -/
@[simp] lemma departureCoord_zero (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    departureCoord p m U 0 i = (i, 0, 1) := by
  simp only [departureCoord, trajectory_zero, initialWalkState]
  rfl

/-- The joint law of the very first increments of the whole swarm: they are independent and
exactly fair.  This is unconditional, because the time-`0` coordinates are constant. -/
theorem measure_firstStep (p : ℝ) (m : ℕ) (σ : Fin N → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    arrayMeasure N {ω : Array N | ∀ i, symmInc p m ω i 0 = σ i} =
      (ENNReal.ofReal (1 / 2)) ^ N := by
  set g : Fin N → (Fin N × ℤ × ℕ) := fun i => ((i : Fin N), (0 : ℤ), (1 : ℕ)) with hg
  have hfun : ∀ (i : Fin N) (ω : Array N), symmInc p m ω i 0 = symmetricStep (ω (g i)) := by
    intro i ω
    simp [symmInc, hg]
  have hinj : Function.Injective g := by
    intro i j hij
    have h1 : (i : Fin N) = (j : Fin N) := (Prod.ext_iff.mp hij).1
    exact h1
  have hInd : iIndepFun (fun i (ω : Array N) => ω (g i)) (arrayMeasure N) :=
    (array_independent N).precomp hinj
  have hset : {ω : Array N | ∀ i, symmInc p m ω i 0 = σ i} =
      ⋂ i, (fun ω : Array N => ω (g i)) ⁻¹' signCell (σ i) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, signCell, hfun]
  rw [hset]
  have h := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd
    (Finset.univ : Finset (Fin N)) (sets := fun i => signCell (σ i))
    (fun i _ => measurableSet_signCell (σ i))
  have h' : arrayMeasure N (⋂ i, (fun ω : Array N => ω (g i)) ⁻¹' signCell (σ i)) =
      ∏ i, arrayMeasure N ((fun ω : Array N => ω (g i)) ⁻¹' signCell (σ i)) := by
    simpa using h
  rw [h']
  have hfac : ∀ i : Fin N,
      arrayMeasure N ((fun ω : Array N => ω (g i)) ⁻¹' signCell (σ i))
        = ENNReal.ofReal (1 / 2) := fun i =>
    (arrayMeasure_preimage_set N (g i) (signCell (σ i))
      (measurableSet_signCell (σ i))).trans (uniform01_signCell (hσ i))
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Swarming.Fair
