/-
Finite selected-block duration on the actual neutral law.

The strict-seed conditional law is absolutely continuous with respect to the
actual array law.  Thus the actual projected ballistic lower bound and the
unit normalization bound transfer to it.  The existing regeneration duration
argument then proves a genuine finite mean for `selectedT`; this is not a
distance/time identification and does not use the initial path-law identity.
-/
import Swarm.ActualNeutralBridge

open MeasureTheory Set ProbabilityTheory Filter Topology
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmChain
open SimJump
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace SwarmActualNeutral

variable {N : ℕ}

/-- The neutral selected duration is integrable from the same actual `hfull`
and one-block distance moment used by `NeutralRegenLaw`.  No duration moment
is assumed, and `selectedT` remains the time coordinate (totalised only on the
null no-chain fallback). -/
theorem integrable_selectedT_zero_of_hfull {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    Integrable (fun U => (NeutralRegen.selectedT p m N 0 U : ℝ))
      (SwarmFB.seedCond (p := p) (m := m) (N := N)) := by
  have h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold SwarmFB.seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨hreg, hsand⟩ :=
    NeutralRegen.neutral_regen_bridge_actual hp0 hp1 hm hN hfull hintD
  have hsandActual : Swarm.Sandwich
      (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
    simpa only [selectedPath_eq_actualX] using hsand
  obtain ⟨κ, hκpos, hκlim⟩ := Swarm.actualProjectedBallistic hp0 hp1 hm
  obtain ⟨𝓕, hlaw⟩ : ∃ 𝓕 : Filtration ℕ
      (inferInstanceAs (MeasurableSpace (Array N))),
      Swarm.IsInteractingLaw 𝓕 (arrayMeasure N) (Swarm.actualX (N := N) p m) m p :=
    ⟨_, SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m⟩
  have hballRaw : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ =>
        Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop := by
    simpa only [Swarm.pos, Swarm.actualX] using hκlim N hN
  have hbdRaw : ∀ᵐ U ∂(arrayMeasure N), ∀ (i : Fin N) (n : ℕ),
      -(1 : ℝ) ≤ Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ) := by
    exact Eventually.of_forall fun U i n =>
      (abs_le.mp (SwarmDens.abs_pos_div_le_one hlaw n U i)).1
  have hac : SwarmFB.seedCond (p := p) (m := m) (N := N) ≪ arrayMeasure N := by
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hballν : ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      ∀ i : Fin N, κ ≤ liminf (fun n : ℕ =>
        Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ)) atTop :=
    hac.ae_le hballRaw
  have hbdν : ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      ∀ (i : Fin N) (n : ℕ),
        -(1 : ℝ) ≤ Swarm.pos (Swarm.actualX (N := N) p m) n i U / (n : ℝ) :=
    hac.ae_le hbdRaw
  exact Swarm.integrable_duration_of_regenLawWeak
    (X := Swarm.actualX (N := N) p m) hκpos (by omega) hreg hsandActual hballν hbdν

/-- The full neutral regeneration law (including duration integrability) from
one genuine stopped-record invariant probability and one-block distance mean. -/
theorem actual_neutral_regenLaw_of_invariant {p : ℝ}
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
    Swarm.RegenLaw (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
  obtain ⟨hfull, hfresh, hreg, hsand⟩ :=
    actual_neutral_regeneration_of_invariant hp0 hp1 hm hN π hinv hintD
  have hintT := integrable_selectedT_zero_of_hfull hp0 hp1 hm hN hfull hintD
  have h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold SwarmFB.seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact ⟨hfull, hfresh, Swarm.regenLaw_of_regenLawWeak hreg hintT, hsand⟩

/-- Exact stopped-record iterate tightness gives the same full neutral
regeneration package, now with the duration moment derived rather than added. -/
theorem actual_neutral_regenLaw_of_tight {p : ℝ}
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
    Swarm.RegenLaw (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) ∧
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
  obtain ⟨hfull, hfresh, hreg, hsand⟩ :=
    actual_neutral_regeneration_of_tight hp0 hp1 hm hN μ₀ htight hintD
  have hintT := integrable_selectedT_zero_of_hfull hp0 hp1 hm hN hfull hintD
  have h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold SwarmFB.seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact ⟨hfull, hfresh, Swarm.regenLaw_of_regenLawWeak hreg hintT, hsand⟩

end SwarmActualNeutral
