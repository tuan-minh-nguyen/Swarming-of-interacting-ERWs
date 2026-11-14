/-
# The strict `V`: `P^*` for the paper's strict regeneration event

`FreshLaw.lean` proves the factorisation for the paper's strict set
`V = strictPos` (`X^i_n > 0` for `n ≥ 1`) at a fixed point, and `SegmentLaw.lean` /
`FirstRegen.lean` develop the full-past and first-hit forms for `V = nonnegPath`.
This file records the strict counterparts of the segment-law statements, so that the
paper's own (strict) regeneration event has the same `P^*` interface.

`RegenAtStrict p m U t d ↔ RecordAt p m U t d ∧ relFuture ∈ strictPos`
(`FreshLaw.regenAtStrict_iff`), so the strict statements are the `S = strictPos` case of
`freshlaw_past_of_subset`.
-/
import Swarm.FirstRegen

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

namespace SwarmSeg

variable {N : ℕ}

/-- The array event "the fresh path stays strictly positive after time `0`". -/
def strictSeedSet (p : ℝ) (m : ℕ) (N : ℕ) : Set (Array N) :=
  {U | posPath p m U ∈ strictPos (N := N)}

theorem measurableSet_strictSeedSet (p : ℝ) (m : ℕ) (N : ℕ) :
    MeasurableSet (strictSeedSet p m N) :=
  (measurable_posPath p m N) measurableSet_strictPos

theorem strictSeedSet_ne_top (p : ℝ) (m : ℕ) (N : ℕ) :
    (arrayMeasure N) (strictSeedSet p m N) ≠ ⊤ :=
  measure_ne_top _ _

/-- **The paper's `P^*` for the strict regeneration set `V`.** -/
noncomputable def PstarStrict (p : ℝ) (m : ℕ) (N : ℕ) : Measure (ℕ → Fin N → ℤ) :=
  ((arrayMeasure N) (strictSeedSet p m N))⁻¹ •
    (Measure.restrict (arrayMeasure N) (strictSeedSet p m N)).map (fun U => posPath p m U)

/-- **`P^*` is concentrated on the strict set `V`.** -/
theorem PstarStrict_self (p : ℝ) (m : ℕ) (N : ℕ)
    (hV : (arrayMeasure N) (strictSeedSet p m N) ≠ 0) :
    PstarStrict p m N (strictPos (N := N)) = 1 := by
  have htop := strictSeedSet_ne_top p m N
  have hmap : ((Measure.restrict (arrayMeasure N) (strictSeedSet p m N)).map
      (fun U => posPath p m U)) (strictPos (N := N)) = (arrayMeasure N) (strictSeedSet p m N) := by
    rw [Measure.map_apply (measurable_posPath p m N) measurableSet_strictPos,
      Measure.restrict_apply ((measurable_posPath p m N) measurableSet_strictPos)]
    congr 1
    ext U
    simp only [strictSeedSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨h, h⟩⟩
  rw [PstarStrict, Measure.smul_apply, hmap, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hV htop

/-- **`P^*` (strict) is a probability measure** given strict seed positivity. -/
theorem PstarStrict_isProbabilityMeasure (p : ℝ) (m : ℕ) (N : ℕ)
    (hV : (arrayMeasure N) (strictSeedSet p m N) ≠ 0) :
    IsProbabilityMeasure (PstarStrict p m N) := by
  refine ⟨?_⟩
  have htop := strictSeedSet_ne_top p m N
  have huniv : ((Measure.restrict (arrayMeasure N) (strictSeedSet p m N)).map
      (fun U => posPath p m U)) univ = (arrayMeasure N) (strictSeedSet p m N) := by
    rw [Measure.map_apply (measurable_posPath p m N) MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [PstarStrict, Measure.smul_apply, huniv, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hV htop

/-- Measurability of the strict regeneration event. -/
theorem measurableSet_regenAtStrict (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet {U : Array N | RegenAtStrict p m U t d} := by
  have hset : {U : Array N | RegenAtStrict p m U t d}
      = {U : Array N | RecordAt p m U t d} ∩
        (fun U => relFuture p m U t d) ⁻¹' strictPos (N := N) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [regenAtStrict_iff]
  rw [hset]
  exact (measurableSet_recordSet p m t d).inter
    ((measurable_relFuture p m t d N) measurableSet_strictPos)

end SwarmSeg
