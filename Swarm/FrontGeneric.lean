/-
# Proposition `front`, generic form, with the positive mass factors retained

`Swarm/KrylovBogoliubov.lean` proves (Proposition `front`, abstract form)

  `(hF : Feller κ) → TightIterates κ μ → (∀ K, ∃ c ≠ 0, ∀ y ∈ Kset K, c ≤ κ y F) →
     ∃ π, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧ 0 < π F`,

discarding the two positive factors of the paper's display
`π(F) ≥ c_K · π(Kset K) > 0` (Hairer/Krylov–Bogoliubov step + force estimate).  The Kac step
downstream needs those factors: `π(F) > 0` enters as a *strict* inequality `0 < pf`, and
`π(F) ≠ 0` must be derived rather than assumed.

This module supplies the generic quantitative form, with an explicit constant family, and
exposes `0 < π (Kset K)` and `c K · π (Kset K) ≤ π F`.  It reproves no Feller and no
tightness content: both stay hypotheses, exactly as upstream.  The record-kernel instance (a thin instantiation of this theorem) is
`SwarmFront.exists_invariant_measure_srSet_quantitative` (`FrontThin.lean`), where
`c K = ofReal ((1-p)^(N*(2K+1)))`.

Main result: `exists_invariant_measure_pos_exhaustion_quantitative`.
-/
import Swarm.KrylovBogoliubov

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [OpensMeasurableSpace X] [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
variable [TopologicalSpace.SeparableSpace X] [BorelSpace X]

/-- **Proposition `front`, quantitative form.**  Let `κ` be a Feller Markov kernel whose
iterates from `μ` are tight on the exhaustion `Kset`, and suppose the paper's force estimate
holds with explicit constants `c K ≠ 0`: `c K ≤ κ y F` for every `y ∈ Kset K`.  Then there are
an invariant probability `π` and a level `K` with

  `0 < π (Kset K)`,  `c K * π (Kset K) ≤ π F`,  and hence `0 < π F`.

The two positive factors of the paper's display are therefore available for the Kac step. -/
theorem exists_invariant_measure_pos_exhaustion_quantitative {κ : Kernel X X} [IsMarkovKernel κ]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hF : Feller κ) (Kset : ℕ → Set X) (hcomp : ∀ K : ℕ, IsCompact (Kset K))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, (step κ)^[n] μ (Kset K)ᶜ ≤ ε)
    {F : Set X} (hFm : MeasurableSet F) (c : ℕ → ℝ≥0∞) (hc : ∀ K, c K ≠ 0)
    (hforce : ∀ (K : ℕ) (y : X), y ∈ Kset K → c K ≤ κ y F) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      ∃ K : ℕ, 0 < π (Kset K) ∧ c K * π (Kset K) ≤ π F ∧ 0 < π F := by
  have hT' : TightIterates κ μ := fun ε hε => by
    obtain ⟨K, hK⟩ := htight ε hε
    exact ⟨Kset K, hcomp K, hK⟩
  obtain ⟨a, hinv, hopen⟩ := exists_invariant_cluster_point hF (tightAverages_of_tightIterates hT')
  obtain ⟨K₀, hK₀⟩ := htight (1 / 2) (by norm_num)
  have hKopen : IsOpen (Kset K₀)ᶜ := (hcomp K₀).isClosed.isOpen_compl
  have hlim : (a : Measure X) (Kset K₀)ᶜ ≤ 1 / 2 :=
    hopen _ hKopen (1 / 2) (fun n => avg_compl_le_of_forall_iterate_compl_le hK₀ n)
  have hKm : MeasurableSet (Kset K₀) := (hcomp K₀).isClosed.measurableSet
  have hsum : (a : Measure X) (Kset K₀) + (a : Measure X) (Kset K₀)ᶜ = 1 := by
    rw [measure_add_measure_compl hKm, measure_univ]
  have hposK : 0 < (a : Measure X) (Kset K₀) := by
    rw [pos_iff_ne_zero]
    intro h0
    have h1 : (a : Measure X) (Kset K₀)ᶜ = 1 := by
      have h := hsum
      rw [h0, zero_add] at h
      simpa using h
    rw [h1] at hlim
    exact absurd hlim (by norm_num)
  have hbound := invariant_density_lower_bound hinv hKm hFm (c := c K₀) (hforce K₀)
  have hposF : 0 < (a : Measure X) F :=
    lt_of_lt_of_le (ENNReal.mul_pos (hc K₀) hposK.ne') hbound
  exact ⟨(a : Measure X), inferInstance, hinv, K₀, hposK, hbound, hposF⟩

end SwarmKB
