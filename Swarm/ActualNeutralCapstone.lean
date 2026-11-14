/-
Final neutral capstone for the actual WCJF array model.

This file composes, without weakening any of them,
* `SwarmActualHfull.full_selection_actual_of_invariant`,
* `NeutralRegen.neutral_regen_bridge_actual`, and
* `M7Neutral.actual_common_speed_of_neutral_map`.

The conclusion is the source theorem on the literal `Swarming.Trajectory.trajectory`:
one `κ(m,p)>0` before all `N`, then a common speed in `[κ,2p-1]` for every walker.
The three remaining stochastic inputs are explicit: a genuine invariant stopped-record
probability law for each `N`, integrability of the selected block level (not duration),
and a finite raw-array time/space translation whose future path law is exactly `seedCond`.
-/
import Swarm.NeutralTransport
import Swarm.NeutralRegenLaw
import Swarm.HfullBridge

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming.Uniform Swarming.Trajectory

namespace ActualNeutralCapstone

/-- **Source Theorem 1.1 from the three actual neutral inputs.**

The invariant kernel is exactly `RecKernel.hitKKernel`.  The integrable observable is
`SwarmFB.blkLevelR`, not walk time.  The maps `S,c` take ordinary finite values on every
array, so the initial temporal and spatial translations are genuinely finite; `hpath`
is the required identity between the translated raw-array path law and the actual neutral
path law.  No independence or invariance is asserted under `arrayMeasure N` itself. -/
theorem main_claim_actual_of_invariant_neutral {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hπ : ∀ (N : ℕ), 2 ≤ N → ∃ (π : Measure (SwarmRec.RecState N m)),
      IsProbabilityMeasure π ∧
        Kernel.Invariant
          (SimJump.RecKernel.hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π)
    (hintD : ∀ (N : ℕ), 2 ≤ N →
      Integrable SwarmFB.blkLevelR (SwarmFB.Q (p := p) (m := m) (N := N)))
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
  classical
  obtain ⟨κ, hκpos, hκlim⟩ := Swarm.actualProjectedBallistic hp0 hp1 hm
  refine ⟨κ, hκpos, fun N hN => ?_⟩
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  obtain ⟨π, hπprob, hinv⟩ := hπ N hN
  letI : IsProbabilityMeasure π := hπprob
  have hfull := SwarmActualHfull.full_selection_actual_of_invariant
    (p := p) hp0 hp1 hm hN π hinv
  have h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold SwarmFB.seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure h0
  obtain ⟨hreg, hsand₀⟩ := NeutralRegen.neutral_regen_bridge_actual
    hp0 hp1 hm hN hfull (hintD N hN)
  have hprocess : NeutralRegen.selectedPath p m N = Swarm.actualX (N := N) p m := by
    funext n U i
    rfl
  have hsand : Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (Swarm.actualX (N := N) p m)
      (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N) := by
    rw [← hprocess]
    exact hsand₀
  obtain ⟨S, c, hS, hc, hmap⟩ := hpath N hN
  obtain ⟨_, _, _, hvup, hlim⟩ := M7Neutral.actual_common_speed_of_neutral_map
    (N := N) hp0 hp1 hm hN
    (SwarmFB.seedCond (p := p) (m := m) (N := N))
    (NeutralRegen.selectedD p m N) (NeutralRegen.selectedT p m N)
    hreg hsand S c hS hc hmap
  let v : ℝ :=
    (∫ U, (NeutralRegen.selectedD p m N 0 U : ℝ)
      ∂(SwarmFB.seedCond (p := p) (m := m) (N := N))) /
    (∫ U, (NeutralRegen.selectedT p m N 0 U : ℝ)
      ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)))
  have hlim' : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / (n : ℝ))
        atTop (𝓝 v) := by
    simpa only [v, Swarm.pos, Swarm.actualX] using hlim
  have hvup' : v ≤ 2 * p - 1 := by simpa only [v] using hvup
  have hvlow : κ ≤ v := by
    by_cases hcase : κ ≤ v
    · exact hcase
    · exfalso
      have hall : ∀ᵐ U ∂(arrayMeasure N), κ ≤ v := by
        have i₀ : Fin N := ⟨0, by omega⟩
        filter_upwards [hκlim N hN, hlim'] with U hb hcl
        exact Swarm.le_of_le_liminf_of_tendsto (hcl i₀) (by simpa using hb i₀)
      exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])
  exact ⟨v, hvlow, hvup', hlim'⟩

end ActualNeutralCapstone
