/-
# Discharging the seed-positivity hypothesis of `(freshlaw)`

`SwarmFresh.freshlaw_hfac` / `freshlawStrict_hfac` (in `Swarm/FreshLaw.lean`) prove the
paper's `(factor)` for a single record time *given* the seed probability
`P(posPath ∈ nonnegPath) ≠ 0` respectively `P(posPath ∈ strictPos) ≠ 0`.

`SwarmSeed.strictPos_measure_ne_zero` (this directory) proves the strict seed positivity for the
actual i.i.d. array law from transience, with no hypothesis beyond the paper's parameter range.
This file therefore supplies the paper's `(factor)` with *no* residual hypothesis:

* `nonnegPath_measure_ne_zero` — `P(posPath ∈ nonnegPath) > 0` (weaker event, easier to use);
* `freshlaw_hfac_discharged` — `(factor)` for the non-strict regeneration event;
* `freshlawStrict_hfac_discharged` — `(factor)` for the paper's strict event `V`.
-/
import Swarm.SeedPos
import Swarm.FreshLaw

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh

namespace SwarmSeed

variable {N : ℕ}

/-- **`P(posPath ∈ nonnegPath) > 0`** for the actual array law, from the strict version. -/
theorem nonnegPath_measure_ne_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} ≠ 0 := by
  intro h0
  refine strictPos_measure_ne_zero hp0 hp1 hm hN (le_antisymm ?_ bot_le)
  rw [← h0]
  exact measure_mono (fun U hU => strictPos_subset_nonnegPath hU)

/-- **The paper's `(factor)` for the strict regeneration event `V`, with no residual
hypothesis.** -/
theorem freshlawStrict_hfac_discharged {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
          * ((Measure.restrict (arrayMeasure N)
              {U : Array N | posPath p m U ∈ strictPos (N := N)}).map
              (fun U => posPath p m U)) B) :=
  freshlawStrict_hfac p m t d (strictPos_measure_ne_zero hp0 hp1 hm hN) (measure_ne_top _ _) hB

/-- **The paper's `(factor)` for the non-strict regeneration event**, with no residual
hypothesis. -/
theorem freshlaw_hfac_discharged {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | RegenAt p m U t d}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹
          * ((Measure.restrict (arrayMeasure N)
              {U : Array N | posPath p m U ∈ nonnegPath (N := N)}).map
              (fun U => posPath p m U)) B) :=
  freshlaw_hfac p m t d (nonnegPath_measure_ne_zero hp0 hp1 hm hN) (measure_ne_top _ _) hB

end SwarmSeed
