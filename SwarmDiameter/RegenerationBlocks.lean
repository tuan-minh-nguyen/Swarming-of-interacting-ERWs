import Swarm.RegenIid

/-!
# Independence of the existing regeneration blocks

The finite product identities for `FreshBlocks` establish mutual independence
in Mathlib's sense.
-/

open MeasureTheory ProbabilityTheory Set

namespace KacFormula

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

theorem iIndepFun_of_fresh {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) : iIndepFun Z μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  classical
  let t (i : ℕ) := if i ∈ s then sets i else univ
  have ht (i : ℕ) : MeasurableSet (t i) := by
    by_cases hi : i ∈ s
    · simpa only [t, if_pos hi] using hs i hi
    · simp [t, hi]
  have he : (⋂ i ∈ s, Z i ⁻¹' sets i) = ⋂ i ∈ s, Z i ⁻¹' t i := by
    refine iInter_congr (fun i => iInter_congr (fun hi => ?_))
    simp [t, hi]
  rw [he, prod_finset h s t ht]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  change Q (if i ∈ s then sets i else univ) = _
  rw [if_pos hi, ← iid_marginal h i, Measure.map_apply (h.1 i) (hs i hi)]

end KacFormula
