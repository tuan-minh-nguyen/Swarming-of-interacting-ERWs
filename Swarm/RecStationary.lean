/-
# The stationary two-sided record law from an invariant record measure

This file supplies the residual `(R)` of `areas/kac/KOL_RETRACT.md` §4 **given an invariant
probability** of the stopped-record kernel, and then discharges that input from the existing
Feller/tightness package:

* `SwarmChain.winLaw π κ` is the chain window law `(x i)_{i ∈ I}` of the Markov chain with
  transition kernel `κ` started in the invariant law `π` (ChainWindow.lean);
* it is a probability measure on every window, projective, and shift-stationary
  (`winLaw_projective`, `winLaw_shift`);
* hence `SwarmKolNC.exists_stationary_isProjectiveLimit_recState` produces a shift-invariant
  probability on `ℤ → RecState N m` with exactly those window laws;
* by `SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_feller`, the only remaining
  hypothesis is tightness of the iterates of the stopped-record kernel on the compact
  exhaustion `exh N m K` (the paper's Proposition "tight").
-/
import Swarm.ChainWindow
import Swarm.KolRecState
import Swarm.FellerInf

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace SwarmChain

open SimJump SwarmRec

variable {N m : ℕ}

/-- The local reindexing of window laws coincides with `SwarmKol.winReindex`. -/
theorem winReindex_eq_swarmKol (k : ℤ) (I : Finset ℤ) :
    (winReindex (β := RecState N m) k I) = SwarmKol.winReindex k I := rfl

/-- **The window-law residual `(R)` given an invariant probability.**

For any invariant probability `π` of a Markov kernel `κ` on the record states, the chain window
laws are a shift-stationary projective family of probability measures. -/
theorem winLaw_isProjective_stationary (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (κ : Kernel (RecState N m) (RecState N m)) [IsMarkovKernel κ]
    (hinv : π.bind κ = π) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => RecState N m) (winLaw π κ) ∧
      (∀ I : Finset ℤ, IsProbabilityMeasure (winLaw π κ I)) ∧
      (∀ (k : ℤ) (I : Finset ℤ),
        winLaw π κ (I.image (fun i => i + k))
          = (winLaw π κ I).map (SwarmKol.winReindex (β := RecState N m) k I)) := by
  refine ⟨winLaw_projective π κ hinv, fun I => inferInstance, fun k I => ?_⟩
  rw [← winReindex_eq_swarmKol (N := N) (m := m) k I]
  exact winLaw_shift π κ hinv k I

/-- **(R): the actual stationary record window laws have a shift-invariant projective limit.**

Given an invariant probability of the stopped-record kernel, there is a probability on the
two-sided record path space whose finite-window marginals are exactly the chain laws of the
record kernel and which is invariant under every time shift `pathShift k`. -/
theorem exists_stationary_recordLaw_of_invariant (hN : 0 < N) (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    ∃ ν : Measure (ℤ → RecState N m),
      IsProjectiveLimit (α := fun _ : ℤ => RecState N m) ν
          (winLaw π (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm)) ∧
        IsProbabilityMeasure ν ∧
          ∀ k : ℤ, ν.map (SwarmKol.pathShift (β := RecState N m) k) = ν := by
  haveI := SimJump.RecKernel.isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  obtain ⟨hproj, hprob, hstat⟩ :=
    winLaw_isProjective_stationary (N := N) (m := m) π
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) (Kernel.Invariant.def hinv)
  exact SwarmKolNC.exists_stationary_isProjectiveLimit_recState N m hN hproj hprob hstat

/-- **The stationary two-sided record law, with the tightness of the record iterates as the only
remaining stochastic hypothesis.** -/
theorem exists_stationary_recordLaw (hN : 0 < N) (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm))^[r] μ
        (exh N m K)ᶜ ≤ ε) :
    ∃ (π : Measure (RecState N m)) (ν : Measure (ℤ → RecState N m)),
      IsProbabilityMeasure π ∧ 0 < π (srSet N m) ∧
        IsProjectiveLimit (α := fun _ : ℤ => RecState N m) ν
          (winLaw π (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm)) ∧
        IsProbabilityMeasure ν ∧
          ∀ k : ℤ, ν.map (SwarmKol.pathShift (β := RecState N m) k) = ν := by
  obtain ⟨π, hprob, hinv, hpos⟩ :=
    SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_feller (N := N) (m := m)
      p hp hp1 hp_lt hm hN μ htight
  obtain ⟨ν, hνproj, hνprob, hνstat⟩ :=
    exists_stationary_recordLaw_of_invariant (N := N) (m := m) hN p hp hp1 hm π hinv
  exact ⟨π, ν, hprob, hpos, hνproj, hνprob, hνstat⟩

end SwarmChain
