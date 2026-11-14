import Swarm.ShiftedRecord

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace ShiftedAdvance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Literal uncentred oscillation at a random start, for any real-valued process `Q`. -/
def OscShift (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) : Set Ω :=
  {ω | ∃ k ≤ n, δ ≤ |Q (τ ω + k) ω|}

/-- The baseline term which an uncentred random-start oscillation necessarily carries. -/
def OscBase (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (δ : ℝ) : Set Ω :=
  {ω | δ ≤ |Q (τ ω) ω|}

/-- One deterministic-start cell for the centred oscillation.  The equality `τ = s` is retained,
so the subsequent future bound is against this weighted prefix cell, not an unconditional future
law. -/
def OscStartCell (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) (s : ℕ) : Set Ω :=
  {ω | τ ω = s ∧ ∃ k ≤ n, δ ≤ |Q (s + k) ω - Q s ω|}

/-- The part of the literal shifted oscillation whose start exceeds the chosen finite cutoff. -/
def OscLate (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) (S : ℕ) : Set Ω :=
  {ω | ω ∈ OscShift Q τ n δ ∧ S < τ ω}

omit [MeasurableSpace Ω] in
/-- The literal uncentred event is contained in the baseline at threshold `δ/2`, centred
start cells at threshold `δ/2`, and its own late residual.  This is the exact decomposition needed
before invoking the deterministic-start shifted Azuma interface. -/
theorem oscShift_subset_base_startUnion_late
    (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) (S : ℕ) :
    OscShift Q τ n δ ⊆ OscBase Q τ (δ / 2) ∪
      ((⋃ s ∈ Finset.range (S + 1), OscStartCell Q τ n (δ / 2) s) ∪
        OscLate Q τ n δ S) := by
  intro ω hω
  obtain ⟨k, hk, hδ⟩ := hω
  rcases abs_at_shift_split (a := Q (τ ω + k) ω) (b := Q (τ ω) ω) hδ with hb | hi
  · exact Or.inl hb
  · by_cases hS : τ ω ≤ S
    · refine Or.inr (Or.inl (Set.mem_iUnion.2 ⟨τ ω, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩))
      · exact Finset.mem_range.2 (by omega)
      · exact ⟨rfl, k, hk, hi⟩
    · exact Or.inr (Or.inr ⟨⟨k, hk, hδ⟩, by omega⟩)

/-- Measured form of the centred/baseline decomposition.  The three explicit residual inputs are:
the uncentred baseline mass, the sum of weighted deterministic-start centred-oscillation masses,
and the genuinely late shifted mass.  Nothing here substitutes an absolute-time estimate for the
second or third terms. -/
theorem measureReal_oscShift_le_base_add_startSum_add_late
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) (S : ℕ) :
    μ.real (OscShift Q τ n δ) ≤
      (μ.real (OscBase Q τ (δ / 2)) +
        ∑ s ∈ Finset.range (S + 1), μ.real (OscStartCell Q τ n (δ / 2) s)) +
        μ.real (OscLate Q τ n δ S) := by
  calc
    μ.real (OscShift Q τ n δ) ≤
        μ.real (OscBase Q τ (δ / 2) ∪
          ((⋃ s ∈ Finset.range (S + 1), OscStartCell Q τ n (δ / 2) s) ∪
            OscLate Q τ n δ S)) :=
      measureReal_mono (oscShift_subset_base_startUnion_late Q τ n δ S)
        (measure_ne_top _ _)
    _ ≤ μ.real (OscBase Q τ (δ / 2)) +
          μ.real ((⋃ s ∈ Finset.range (S + 1), OscStartCell Q τ n (δ / 2) s) ∪
            OscLate Q τ n δ S) := measureReal_union_le _ _
    _ ≤ μ.real (OscBase Q τ (δ / 2)) +
          (μ.real (⋃ s ∈ Finset.range (S + 1), OscStartCell Q τ n (δ / 2) s) +
            μ.real (OscLate Q τ n δ S)) :=
      add_le_add le_rfl (measureReal_union_le _ _)
    _ ≤ μ.real (OscBase Q τ (δ / 2)) +
          ((∑ s ∈ Finset.range (S + 1), μ.real (OscStartCell Q τ n (δ / 2) s)) +
            μ.real (OscLate Q τ n δ S)) :=
      add_le_add le_rfl (add_le_add (measureReal_biUnion_finset_le _ _) le_rfl)
    _ = (μ.real (OscBase Q τ (δ / 2)) +
          ∑ s ∈ Finset.range (S + 1), μ.real (OscStartCell Q τ n (δ / 2) s)) +
        μ.real (OscLate Q τ n δ S) := by ring

/-- If another bad event is proved to lie in the literal shifted oscillation, the same three terms
bound it.  The inclusion remains an explicit argument input; in particular this theorem does not
assert the open `BadTime`/oscillation comparison. -/
theorem measureReal_bad_le_osc_decomposition
    {μ : Measure Ω} [IsFiniteMeasure μ] {Bad : Set Ω}
    (Q : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (δ : ℝ) (S : ℕ)
    (hsub : Bad ⊆ OscShift Q τ n δ) :
    μ.real Bad ≤
      (μ.real (OscBase Q τ (δ / 2)) +
        ∑ s ∈ Finset.range (S + 1), μ.real (OscStartCell Q τ n (δ / 2) s)) +
        μ.real (OscLate Q τ n δ S) := by
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _))
    (measureReal_oscShift_le_base_add_startSum_add_late Q τ n δ S)

end ShiftedAdvance
