/-
The actual neutral regeneration package from one genuine invariant record law.

No raw-array stationarity is assumed.  The strict-seed conditional measure is
used only for the neutral increments.  The conclusion retains the literal
one-stage fullness identity and the coherent positive-index block sequence,
so none of the intermediate actual-array commitments is hidden.
-/
import Swarm.HfullBridge
import Swarm.SelectedBlockInfinite
import Swarm.NeutralRegenLaw
import Swarm.ActualMain

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmChain
open SimJump
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SwarmActualNeutral

variable {N : ℕ}

/-- The neutral path is definitionally the source trajectory's actual position
path, not a generic interacting system or a canonical replacement model. -/
theorem selectedPath_eq_actualX (p : ℝ) (m N : ℕ) :
    NeutralRegen.selectedPath p m N = Swarm.actualX (N := N) p m := by
  rfl

/-- One genuine invariant probability for the stopped-record hit kernel and a
finite one-block distance moment give the complete actual neutral package.
The first conjunct is the literal `hfull`; the second is the coherent infinite
positive-index sequence from `SelectedBlockInfinite`; the last two use exactly
`selectedD` and `selectedT` on the actual trajectory. -/
theorem actual_neutral_regeneration_of_invariant {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π)
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    ((arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N))) ∧
    KacFormula.FreshBlocks (SwarmSelectedBlockLaw.seedLaw p m N)
      (fun k U => SwarmSelectedBlockInfinite.positiveSeq
        (p := p) (m := m) (N := N) k U)
      (SwarmSelectedBlockLaw.blockLaw p m N) ∧
    Swarm.RegenLawWeak (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
  have hfullPos : (arrayMeasure N) (⋃ i : ℕ × ℕ,
      SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N |
        SwarmRestart.posPath p m U ∈ SwarmSelInd.seed} :=
    SwarmActualHfull.full_selection_actual_of_invariant hp0 hp1 hm hN π hinv
  have hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
      SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) := by
    simpa only [SwarmFB.seedSet] using hfullPos
  have hfresh : KacFormula.FreshBlocks (SwarmSelectedBlockLaw.seedLaw p m N)
      (fun k U => SwarmSelectedBlockInfinite.positiveSeq
        (p := p) (m := m) (N := N) k U)
      (SwarmSelectedBlockLaw.blockLaw p m N) :=
    SwarmSelectedBlockInfinite.freshBlocks_positiveSeq_actual
      hp0 hp1 hm hN hfullPos
  have hreg : Swarm.RegenLawWeak
        (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
      Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (NeutralRegen.selectedPath p m N)
        (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) :=
    NeutralRegen.neutral_regen_bridge_actual hp0 hp1 hm hN hfull hintD
  refine ⟨hfull, hfresh, hreg.1, ?_⟩
  simpa only [selectedPath_eq_actualX] using hreg.2

/-- Exact stopped-record iterate tightness can replace the invariant premise.
The tightness hypothesis is the standard one on `hitKKernel` iterates; there
is still no premise of stationarity or invariance for `arrayMeasure N`. -/
theorem actual_neutral_regeneration_of_tight {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (μ₀ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ₀]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (RecKernel.hitKKernel (N := N) (m := m) p
        (by omega : 1 ≤ m)))^[r] μ₀ (SwarmRec.exh N m K)ᶜ ≤ ε)
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    ((arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N))) ∧
    KacFormula.FreshBlocks (SwarmSelectedBlockLaw.seedLaw p m N)
      (fun k U => SwarmSelectedBlockInfinite.positiveSeq
        (p := p) (m := m) (N := N) k U)
      (SwarmSelectedBlockLaw.blockLaw p m N) ∧
    Swarm.RegenLawWeak (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
  obtain ⟨π, hprob, hinv, -⟩ :=
    RecKernel.exists_invariant_measure_pos_hitKInf_feller
      (N := N) (m := m) p hp0.le hp1.le hp1 (by omega : 1 ≤ m)
      (by omega : 0 < N) μ₀ htight
  letI : IsProbabilityMeasure π := hprob
  exact actual_neutral_regeneration_of_invariant hp0 hp1 hm hN π hinv hintD

end SwarmActualNeutral
