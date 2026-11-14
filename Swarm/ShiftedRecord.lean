import Swarm.Tightness.S1

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace ShiftedAdvance

open RecordDefect SlowBlock

variable {N : ℕ} [Nonempty (Fin N)]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The per-walker small-increment event with the record start frozen at the deterministic time
`s`.  Unlike `SlowBlock.SmallInc`, this event contains no record-time lookup. -/
def SmallIncAt (X : Ω → Fin N → ℕ → ℤ) (B T s L : ℕ) : Set Ω :=
  {ω | ∃ j : Fin N, X ω j (s + T * L) - X ω j s ≤ ((B * L + L : ℕ) : ℤ) - 1}

/-- One deterministic record-start cell.  The first two conjuncts retain the actual record-prefix
information (`τr = s` and the defect band); only the small-increment clause is shifted to `s`.
Consequently a later estimate may condition on this cell rather than pretend that the post-`s`
increments are independent of it. -/
def StartCell (X : Ω → Fin N → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (B T r L s : ℕ) : Set Ω :=
  {ω | τ ω r = s ∧ (defect (X ω) (τ ω) r).toNat ≤ L ∧ ω ∈ SmallIncAt X B T s L}

/-- The ordinary slow-block event, with `X`, `τ` explicit as in the light `S1` interface. -/
def SlowEvent (X : Ω → Fin N → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (B T r L : ℕ) : Set Ω :=
  {ω | SlowBlock.SlowBlock (X ω) (τ ω) B T r L}

/-- The late-start residual; no bound for it is manufactured from an absolute-time window. -/
def LateStart (X : Ω → Fin N → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (B T r L S : ℕ) : Set Ω :=
  {ω | ω ∈ SlowEvent X τ B T r L ∧ S < τ ω r}

omit [MeasurableSpace Ω] in
/-- On the bounded-start part, a slow block is covered by deterministic start cells.  The proof
uses the actual nearest-neighbour/first-record geometry through `S1.increment_le_of_slow`. -/
theorem bounded_slow_subset_startUnion
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L S : ℕ) :
    {ω | ω ∈ SlowEvent X τ B T r L ∧ τ ω r ≤ S} ⊆
      ⋃ s ∈ Finset.range (S + 1), StartCell X τ B T r L s := by
  intro ω hω
  have hslow : SlowBlock.SlowBlock (X ω) (τ ω) B T r L := hω.1
  obtain ⟨j, hj⟩ := SlowBlock.slowBlock_subset_smallInc (hrec ω) hslow
  have hτ : τ ω r ≤ S := hω.2
  have hcell : ω ∈ StartCell X τ B T r L (τ ω r) := by
    refine ⟨rfl, hslow.1, j, ?_⟩
    exact hj
  exact Set.mem_iUnion.2 ⟨τ ω r,
    Set.mem_iUnion.2 ⟨Finset.mem_range.2 (by omega), hcell⟩⟩

omit [MeasurableSpace Ω] in
/-- The countable start-cell cover.  It loses neither the defect band nor the record-prefix event;
in particular it does not condition away the dependence between the start and the future. -/
theorem slow_subset_iUnion_startCell
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L : ℕ) :
    SlowEvent X τ B T r L ⊆ ⋃ s : ℕ, StartCell X τ B T r L s := by
  intro ω hω
  have hslow : SlowBlock.SlowBlock (X ω) (τ ω) B T r L := hω
  obtain ⟨j, hj⟩ := SlowBlock.slowBlock_subset_smallInc (hrec ω) hslow
  refine Set.mem_iUnion.2 ⟨τ ω r, rfl, hslow.1, j, hj⟩

/-- Countable `ℝ≥0∞`-measure form.  A summable estimate for the weighted start cells bounds the
whole shifted event, with no extra late tail; otherwise the finite version below exposes that
late tail explicitly. -/
theorem measure_slow_le_tsum_startCell
    {μ : Measure Ω}
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L : ℕ) :
    μ (SlowEvent X τ B T r L) ≤ ∑' s : ℕ, μ (StartCell X τ B T r L s) := by
  calc
    μ (SlowEvent X τ B T r L) ≤ μ (⋃ s : ℕ, StartCell X τ B T r L s) :=
      measure_mono (slow_subset_iUnion_startCell hrec B T r L)
    _ ≤ ∑' s : ℕ, μ (StartCell X τ B T r L s) := measure_iUnion_le _

omit [MeasurableSpace Ω] in
/-- Exact pathwise split of a slow block into the finite collection of start cells and the genuine
late-start event. -/
theorem slow_subset_startUnion_union_late
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L S : ℕ) :
    SlowEvent X τ B T r L ⊆
      (⋃ s ∈ Finset.range (S + 1), StartCell X τ B T r L s) ∪
        LateStart X τ B T r L S := by
  intro ω hω
  by_cases hS : τ ω r ≤ S
  · exact Or.inl (bounded_slow_subset_startUnion hrec B T r L S ⟨hω, hS⟩)
  · exact Or.inr ⟨hω, by omega⟩

/-- The exact real-measure reduction at a random record start.  The sum is over at most `S+1`
start cells, each retaining its record-prefix band; the final term is the uncontrolled late-start
mass.  No stationarity, independence or absolute-horizon estimate is used. -/
theorem measureReal_slow_le_startSum_add_late
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L S : ℕ) :
    μ.real (SlowEvent X τ B T r L) ≤
      (∑ s ∈ Finset.range (S + 1), μ.real (StartCell X τ B T r L s)) +
        μ.real (LateStart X τ B T r L S) := by
  calc
    μ.real (SlowEvent X τ B T r L) ≤
        μ.real ((⋃ s ∈ Finset.range (S + 1), StartCell X τ B T r L s) ∪
          LateStart X τ B T r L S) :=
      measureReal_mono (slow_subset_startUnion_union_late hrec B T r L S)
        (measure_ne_top _ _)
    _ ≤ μ.real (⋃ s ∈ Finset.range (S + 1), StartCell X τ B T r L s) +
          μ.real (LateStart X τ B T r L S) := measureReal_union_le _ _
    _ ≤ (∑ s ∈ Finset.range (S + 1), μ.real (StartCell X τ B T r L s)) +
          μ.real (LateStart X τ B T r L S) :=
      add_le_add (measureReal_biUnion_finset_le _ _) le_rfl

/-- Scalar form of the same reduction.  A bound `a` for each *weighted start cell*, plus a bound
`b` for the late residual, yields `(S+1)a+b`.  This is the precise remaining analytic obligation;
it is not an assumption that the whole slow-block event has such a profile. -/
theorem measureReal_slow_le_of_cell_and_late_bounds
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → Fin N → ℕ → ℤ} {τ : Ω → ℕ → ℕ}
    (hrec : ∀ ω, IsRecord (X ω) (τ ω)) (B T r L S : ℕ) {a b : ℝ}
    (hcell : ∀ s ∈ Finset.range (S + 1), μ.real (StartCell X τ B T r L s) ≤ a)
    (hlate : μ.real (LateStart X τ B T r L S) ≤ b) :
    μ.real (SlowEvent X τ B T r L) ≤ ((S + 1 : ℕ) : ℝ) * a + b := by
  refine le_trans (measureReal_slow_le_startSum_add_late hrec B T r L S) ?_
  have hsum : (∑ s ∈ Finset.range (S + 1), μ.real (StartCell X τ B T r L s)) ≤
      ∑ _s ∈ Finset.range (S + 1), a :=
    Finset.sum_le_sum hcell
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact add_le_add hsum hlate

/-- The centred/baseline split forced by the literal uncentred shifted oscillation
`δ ≤ |Q(τ+k)|`.  A centred estimate sees the second alternative; the first remains an additional
baseline obligation.  Both thresholds are `δ/2`, by the triangle inequality. -/
theorem abs_at_shift_split {a b δ : ℝ} (h : δ ≤ |a|) :
    δ / 2 ≤ |b| ∨ δ / 2 ≤ |a - b| := by
  by_cases hb : δ / 2 ≤ |b|
  · exact Or.inl hb
  · right
    have htri : |a| - |b| ≤ |a - b| := abs_sub_abs_le_abs_sub a b
    simp only [not_le] at hb
    linarith

end ShiftedAdvance
