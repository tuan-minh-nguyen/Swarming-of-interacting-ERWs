/-
Countable first-block decomposition for the actual strict array path.

This extends `RawTimeStrict.array_firstBlock_future_mass` from one concrete
`(d,t)` to the countable disjoint union over `1 ≤ d` and `t : ℕ`.  The
no-regeneration event is kept as a separate measurable remainder.  No assertion
that regeneration occurs almost surely, stationarity, or independence of
increments is made.
-/
import Swarm.RawTimeStrict

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators Function

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmRawTimeStrictSum

variable {N : ℕ}

/-- Positive regeneration levels paired with their first-hitting times. -/
abbrev LevelTime := {q : ℕ × ℕ // 1 ≤ q.1}

/-- The concrete strict first-block event, with a condition on its relative future. -/
def FirstBlockFuture (p : ℝ) (m : ℕ) (q : LevelTime)
    (B : Set (ℕ → Fin N → ℤ)) : Set (Swarming.Uniform.Array N) :=
  {U : Swarming.Uniform.Array N |
    SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
      RegenPath.D (SwarmRestart.posPath p m U) = (q.1.1 : ℕ∞) ∧
      RegenPath.tau (SwarmRestart.posPath p m U) (q.1.1 : ℤ) = (q.1.2 : ℕ∞) ∧
      SwarmFresh.relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ B}

/-- The mass of the concrete low event `C_{d,t}`. -/
noncomputable def firstBlockLowMass (p : ℝ) (m : ℕ) (q : LevelTime) : ℝ≥0∞ :=
  (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
    RegenPath.Cdt (SwarmRestart.posPath p m U) q.1.1 q.1.2}

/-- All completed strict first blocks whose relative future lies in `B`. -/
def CompletedFirstBlockFuture (p : ℝ) (m : ℕ)
    (B : Set (ℕ → Fin N → ℤ)) : Set (Swarming.Uniform.Array N) :=
  ⋃ q : LevelTime, FirstBlockFuture p m q B

/-- The strict paths having no positive regeneration level. -/
def NoFirstBlock (p : ℝ) (m : ℕ) : Set (Swarming.Uniform.Array N) :=
  {U : Swarming.Uniform.Array N |
    SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
      RegenPath.D (SwarmRestart.posPath p m U) = ⊤}

/-- The strict fresh law, normalized by the actual strict-path mass. -/
noncomputable def normalizedStrictLaw (p : ℝ) (m N : ℕ) :
    Measure (ℕ → Fin N → ℤ) :=
  ((Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})⁻¹ •
    (((Swarming.Uniform.arrayMeasure N).map (SwarmRestart.posPath p m)).restrict
      (SwarmFresh.strictPos (N := N)))

/-- Every concrete completed first-block/future event is measurable. -/
theorem measurableSet_FirstBlockFuture (p : ℝ) (m : ℕ) (q : LevelTime)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (FirstBlockFuture p m q B) := by
  exact SwarmRawTimeStrict.measurableSet_arrayFirstBlock_future
    p m q.1.1 q.1.2 q.2 hB

/-- Distinct concrete first blocks are disjoint, even after intersecting them with
an arbitrary common future event. -/
theorem pairwise_disjoint_FirstBlockFuture (p : ℝ) (m : ℕ)
    (B : Set (ℕ → Fin N → ℤ)) :
    Pairwise (Disjoint on fun q : LevelTime => FirstBlockFuture (N := N) p m q B) := by
  intro q r hqr
  change Disjoint (FirstBlockFuture p m q B) (FirstBlockFuture p m r B)
  rw [Set.disjoint_left]
  intro U hq hr
  apply hqr
  have hde : q.1.1 = r.1.1 := by
    have h : (q.1.1 : ℕ∞) = (r.1.1 : ℕ∞) := hq.2.1.symm.trans hr.2.1
    exact_mod_cast h
  have hts : q.1.2 = r.1.2 := by
    have h : (q.1.2 : ℕ∞) = (r.1.2 : ℕ∞) := by
      have hqq := hq.2.2.1
      have hrr := hr.2.2.1
      rw [hde] at hqq
      exact hqq.symm.trans hrr
    exact_mod_cast h
  exact Subtype.ext (Prod.ext hde hts)

/-- The completed first-block/future union is measurable. -/
theorem measurableSet_CompletedFirstBlockFuture (p : ℝ) (m : ℕ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (CompletedFirstBlockFuture p m B) := by
  exact MeasurableSet.iUnion fun q => measurableSet_FirstBlockFuture p m q hB

/-- Exact countable summation of the strict first-block/future mass.  Only the
completed `C_{d,t}` pieces are summed; no disjointness of unrestricted `Cdt`
events is used. -/
theorem array_completedFirstBlock_future_mass (p : ℝ) (m : ℕ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m B) =
      (∑' q : LevelTime, firstBlockLowMass (N := N) p m q) *
        (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
          SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  calc
    (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m B) =
        ∑' q : LevelTime,
          (Swarming.Uniform.arrayMeasure N) (FirstBlockFuture p m q B) :=
      measure_iUnion (pairwise_disjoint_FirstBlockFuture p m B)
        (fun q => measurableSet_FirstBlockFuture p m q hB)
    _ = ∑' q : LevelTime, firstBlockLowMass (N := N) p m q *
        (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
          SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
      apply tsum_congr
      intro q
      exact SwarmRawTimeStrict.array_firstBlock_future_mass
        p m q.1.1 q.1.2 q.2 hB
    _ = _ := ENNReal.tsum_mul_right

/-- Finiteness of `D` is exactly the existence of a concrete first block and a
finite hitting time.  This is a pathwise equivalence, not an almost-sure claim. -/
theorem D_ne_top_iff_exists_firstBlock (X : RegenPath.Path N) :
    RegenPath.D X ≠ ⊤ ↔ ∃ d t : ℕ, 1 ≤ d ∧ RegenPath.D X = (d : ℕ∞) ∧
      RegenPath.tau X (d : ℤ) = (t : ℕ∞) := by
  classical
  constructor
  · intro hD
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := by
      by_contra hcon
      apply hD
      unfold RegenPath.D
      rw [dif_neg hcon]
    have hfind : RegenPath.D X = (Nat.find hex : ℕ∞) := by
      unfold RegenPath.D
      rw [dif_pos hex]
    obtain ⟨t, htau, -, -⟩ := (Nat.find_spec hex).2
    exact ⟨Nat.find hex, t, (Nat.find_spec hex).1, hfind, htau⟩
  · rintro ⟨d, t, hd, hD, htau⟩
    rw [hD]
    simp

/-- On strict paths, the union over all first blocks with unrestricted future is
exactly the event `D ≠ ∞`. -/
theorem CompletedFirstBlockFuture_univ (p : ℝ) (m : ℕ) :
    CompletedFirstBlockFuture (N := N) p m Set.univ =
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
          RegenPath.D (SwarmRestart.posPath p m U) ≠ ⊤} := by
  ext U
  constructor
  · intro hU
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
    refine ⟨hq.1, ?_⟩
    rw [hq.2.1]
    simp
  · rintro ⟨hS, hD⟩
    obtain ⟨d, t, hd, hDeq, htau⟩ := (D_ne_top_iff_exists_firstBlock _).mp hD
    apply Set.mem_iUnion.mpr
    refine ⟨ ⟨(d, t), hd⟩, ?_⟩
    exact ⟨hS, hDeq, htau, Set.mem_univ _⟩

/-- The no-regeneration strict event is measurable. -/
theorem measurableSet_NoFirstBlock (p : ℝ) (m : ℕ) :
    MeasurableSet (NoFirstBlock (N := N) p m) := by
  have hS : MeasurableSet {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} :=
    (SwarmRestart.measurable_posPath p m N) SwarmFresh.measurableSet_strictPos
  have hset : NoFirstBlock (N := N) p m =
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} \
        CompletedFirstBlockFuture p m Set.univ := by
    rw [CompletedFirstBlockFuture_univ]
    ext U
    constructor
    · rintro ⟨hpos, htop⟩
      exact ⟨hpos, fun h => h.2 htop⟩
    · rintro ⟨hpos, hrest⟩
      refine ⟨hpos, ?_⟩
      by_contra hne
      exact hrest ⟨hpos, hne⟩
  rw [hset]
  exact hS.diff (measurableSet_CompletedFirstBlockFuture p m MeasurableSet.univ)

/-- The no-regeneration and completed-first-block events are disjoint. -/
theorem NoFirstBlock_disjoint_Completed (p : ℝ) (m : ℕ) :
    Disjoint (NoFirstBlock (N := N) p m)
      (CompletedFirstBlockFuture p m Set.univ) := by
  rw [Set.disjoint_left, CompletedFirstBlockFuture_univ]
  intro U hno hcompleted
  exact hcompleted.2 hno.2

/-- Every strict path is either in the no-regeneration remainder or in a unique
completed first block. -/
theorem strictPath_eq_NoFirstBlock_union_Completed (p : ℝ) (m : ℕ) :
    {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} =
      NoFirstBlock p m ∪ CompletedFirstBlockFuture p m Set.univ := by
  rw [CompletedFirstBlockFuture_univ]
  ext U
  constructor
  · intro hS
    by_cases hD : RegenPath.D (SwarmRestart.posPath p m U) = ⊤
    · exact Or.inl ⟨hS, hD⟩
    · exact Or.inr ⟨hS, hD⟩
  · rintro (⟨hS, hD⟩ | ⟨hS, hD⟩) <;> exact hS

/-- Exact mass decomposition preserving the `D = ∞` remainder. -/
theorem array_strictPath_mass_eq_NoFirstBlock_add_Completed (p : ℝ) (m : ℕ) :
    (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} =
      (Swarming.Uniform.arrayMeasure N) (NoFirstBlock p m) +
      (Swarming.Uniform.arrayMeasure N)
        (CompletedFirstBlockFuture p m Set.univ) := by
  rw [strictPath_eq_NoFirstBlock_union_Completed,
    measure_union (NoFirstBlock_disjoint_Completed p m)
      (measurableSet_CompletedFirstBlockFuture p m MeasurableSet.univ)]

/-- Evaluation of the normalized strict fresh law on a measurable future event. -/
theorem normalizedStrictLaw_apply (p : ℝ) (m N : ℕ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    normalizedStrictLaw p m N B =
      ((Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)})⁻¹ *
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  have hset : (SwarmRestart.posPath p m) ⁻¹'
      (B ∩ SwarmFresh.strictPos (N := N)) =
      {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
    ext U
    simp [and_comm]
  rw [normalizedStrictLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hB,
    Measure.map_apply (SwarmRestart.measurable_posPath p m N)
      (hB.inter SwarmFresh.measurableSet_strictPos), hset]

/-- Joint law of the completed first block and its translated future, using the
normalized strict fresh law.  Positivity of the strict-path mass is an explicit
premise; no positivity or finiteness of `D` is inferred. -/
theorem array_completedFirstBlock_normalized_joint (p : ℝ) (m N : ℕ)
    (hpos : (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m B) =
      (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m Set.univ) *
        normalizedStrictLaw p m N B := by
  let V : ℝ≥0∞ := (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
    SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)}
  let A : ℝ≥0∞ := ∑' q : LevelTime, firstBlockLowMass (N := N) p m q
  let X : ℝ≥0∞ := (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
    SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B}
  have hVtop : V ≠ ⊤ := measure_ne_top _ _
  have htotal : (Swarming.Uniform.arrayMeasure N)
      (CompletedFirstBlockFuture (N := N) p m Set.univ) = A * V := by
    simpa [A, V] using
      (array_completedFirstBlock_future_mass (N := N) p m MeasurableSet.univ)
  have hfactor : (A * V) * (V⁻¹ * X) = A * X := by
    calc
      (A * V) * (V⁻¹ * X) = A * ((V * V⁻¹) * X) := by simp only [mul_assoc]
      _ = A * (1 * X) := by rw [ENNReal.mul_inv_cancel hpos hVtop]
      _ = A * X := by rw [one_mul]
  calc
    (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m B) = A * X := by
      simpa [A, X] using array_completedFirstBlock_future_mass (N := N) p m hB
    _ = (A * V) * (V⁻¹ * X) := hfactor.symm
    _ = (Swarming.Uniform.arrayMeasure N) (CompletedFirstBlockFuture p m Set.univ) *
        normalizedStrictLaw p m N B := by
      rw [← htotal, normalizedStrictLaw_apply p m N hB]

end SwarmRawTimeStrictSum
