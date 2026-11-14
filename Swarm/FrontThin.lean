/-
# Proposition `front` for the stopped record kernel: a thin instantiation

The generic quantitative form of Proposition `front` is proved and audited in
`FrontGeneric.lean`:

  `SwarmKB.exists_invariant_measure_pos_exhaustion_quantitative`:
  for a Feller Markov kernel with tight iterates and force constants `c K ≠ 0` on the
  exhaustion `Kset K`, there are an invariant probability `π` and a level `K` with
  `0 < π (Kset K)`, `c K * π (Kset K) ≤ π F`, hence `0 < π F`.

This module **instantiates** it at the genuine horizon-free stopped record kernel
`SimJump.RecKernel.hitKKernel`, with the paper's explicit force constant
`c K = ofReal ((1-p)^{N(2K+1)})` supplied by `hitKInf_srSet_ge` and Feller by
`feller_hitKKernel`.  There is **no duplicated Krylov–Bogoliubov argument here**: every
proof in this file is a short application of an upstream declaration.  Iterate tightness
remains the only premise; the seed and factorisation premises are untouched.

Declarations:

* `exists_invariant_measure_srSet_quantitative` — the quantitative `front`;
* `srSet_mass_pos`, `srSet_mass_ne_zero`, `srSet_mass_ne_top`, `srSet_kac_side_conditions`
  — the corollaries the Kac step consumes.
-/
import Swarm.FrontGeneric
import Swarm.FellerInf

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFront

open SimJump SimJump.RecKernel SwarmRec SwarmKB

variable {N m : ℕ}

/-- **Proposition `front` with both positive mass factors**, for the stopped record kernel,
obtained as a thin instantiation of the verified generic form. -/
theorem exists_invariant_measure_srSet_quantitative (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧
      ∃ K : ℕ, 0 < π (exh N m K) ∧
        ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) * π (exh N m K) ≤ π (srSet N m) ∧
        0 < π (srSet N m) := by
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine exists_invariant_measure_pos_exhaustion_quantitative
    (κ := hitKKernel (N := N) (m := m) p hm)
    (feller_hitKKernel p hp hp1 hm) (fun K => exh N m K)
    (fun K => isCompact_dist2_le N m K) htight (measurableSet_srSet N m)
    (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))) ?_ ?_
  · intro K
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · intro K y hy
    have h := hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy
    simpa only [hitKKernel_apply] using h

/-- The bare positivity statement `0 < π (srSet)`, with tightness the only premise. -/
theorem srSet_mass_pos (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧ 0 < π (srSet N m) := by
  obtain ⟨π, hprob, hinv, K, hK, hbound, hpos⟩ :=
    exists_invariant_measure_srSet_quantitative p hp hp1 hp_lt hm hN μ htight
  exact ⟨π, hprob, hinv, hpos⟩

/-- The invariant mass of the record set is nonzero — the `pf ≠ 0` side condition of the Kac
transfer, derived from the invariant law. -/
theorem srSet_mass_ne_zero (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧ π (srSet N m) ≠ 0 := by
  obtain ⟨π, hprob, hinv, hpos⟩ := srSet_mass_pos p hp hp1 hp_lt hm hN μ htight
  exact ⟨π, hprob, hinv, hpos.ne'⟩

/-- The invariant mass of the record set is finite — the `pf ≠ ⊤` side condition. -/
theorem srSet_mass_ne_top (π : Measure (RecState N m)) [IsProbabilityMeasure π] :
    π (srSet N m) ≠ ⊤ :=
  measure_ne_top π _

/-- **The two side conditions of the Kac step, discharged by the invariant law**: for the
record state `π` produced by `front`, `π (srSet)` is neither `0` nor `⊤`, so
`E^*D ≤ 1/(π(F)P(V))` is a finite number as soon as the seed mass `P(V)` is positive. -/
theorem srSet_kac_side_conditions (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (srSet N m) ∧ π (srSet N m) ≠ ⊤ := by
  obtain ⟨π, hprob, hinv, hpos⟩ := srSet_mass_pos p hp hp1 hp_lt hm hN μ htight
  exact ⟨π, hprob, hinv, hpos, srSet_mass_ne_top π⟩

end SwarmFront
