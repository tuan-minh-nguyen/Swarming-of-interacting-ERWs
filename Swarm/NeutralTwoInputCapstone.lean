/-
Two-input neutral assembly for the actual WCJF array model.

`BlockLevelKac` derives selected-block level integrability from the same genuine
stopped-record invariant law used by `HfullBridge`.  Consequently the neutral
regeneration law needs no separate level-moment premise.  The raw source capstone
still requires the literal initial translated-path-law identity; this file neither
constructs that identity nor asserts invariant existence or tightness.
-/
import Swarm.ActualNeutralCapstone
import Swarm.ActualNeutralDuration
import Swarm.BlockLevelKac

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming.Uniform Swarming.Trajectory

namespace ActualNeutralCapstone

/-- The actual neutral `RegenLaw`, including the derived duration moment, from
one genuine invariant stopped-record probability law.  `hintD` is discharged by
`BlockLevelKac` rather than assumed again. -/
theorem actual_neutral_regenLaw_of_invariant_derived_level {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π) :
    ((arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N))) ∧
    KacFormula.FreshBlocks (SwarmSelectedBlockLaw.seedLaw p m N)
      (fun k U => SwarmSelectedBlockInfinite.positiveSeq
        (p := p) (m := m) (N := N) k U)
      (SwarmSelectedBlockLaw.blockLaw p m N) ∧
    Swarm.RegenLaw (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
  refine SwarmActualNeutral.actual_neutral_regenLaw_of_invariant
    hp0 hp1 hm hN π hinv ?_
  exact BlockLevelKac.integrable_blkLevelR_of_invariant hm hN hp0 hp1 π hinv

/-- Source Theorem 1.1 from exactly two actual stochastic inputs: a genuine
invariant stopped-record law and the literal finite initial path-law transport.
The common neutral speed is transported to the source raw-array trajectory;
`κ` is chosen once before all `N`. -/
theorem main_claim_actual_of_invariant_neutral_derived_level {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hπ : ∀ (N : ℕ), 2 ≤ N → ∃ (π : Measure (SwarmRec.RecState N m)),
      IsProbabilityMeasure π ∧
        Kernel.Invariant
          (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π)
    (hpath : ∀ (N : ℕ), 2 ≤ N →
      ∃ (S : Array N → ℕ) (c : Array N → ℝ),
        Measurable S ∧ Measurable c ∧
          Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
            Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U)
              (arrayMeasure N) =
            Measure.map (M6Star.actPath (N := N) p m)
              (SwarmFB.seedCond (p := p) (m := m) (N := N))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) := by
  refine main_claim_actual_of_invariant_neutral hp0 hp1 hm hπ ?_ hpath
  intro N hN
  obtain ⟨π, hπprob, hinv⟩ := hπ N hN
  letI : IsProbabilityMeasure π := hπprob
  exact BlockLevelKac.integrable_blkLevelR_of_invariant hm hN hp0 hp1 π hinv

end ActualNeutralCapstone
