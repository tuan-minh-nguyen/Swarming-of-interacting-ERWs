/-
Neutral regeneration increments and path sandwich from actual selected blocks.

The source measure is `SwarmFB.seedCond` on the literal actual array.  `hfull`
is retained exactly; no assertion is made here that it has been proved.
-/
import Swarm.NeutralRegenGeometry
import Swarm.DurationIntegrable
import Swarm.SandwichBridge

open MeasureTheory Set ProbabilityTheory Filter Topology
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NeutralRegen

open SwarmFB SwarmSelInd

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- The literal actual position process.  `Swarm.actualX` unfolds to this same
function; keeping this local form avoids importing the occupation stack. -/
noncomputable def selectedPath (p : ℝ) (m N : ℕ) : ℕ → Array N → Fin N → ℤ :=
  fun n U => SwarmRestart.posPath p m U n

/-- Distance increment carried by the actual selected block. -/
noncomputable def selectedD (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) : ℕ :=
  (SwarmFB.Z (p := p) (m := m) (N := N) k U).2 + 1

/-- Positive totalisation of the selected duration.  It differs from the raw
block time only where that time is zero; on genuine selected chains it is the
block time itself. -/
noncomputable def selectedT (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) : ℕ :=
  max 1 (SwarmFB.Z (p := p) (m := m) (N := N) k U).1

/-- Cumulative regeneration time. -/
noncomputable def selectedSigma (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) : ℕ :=
  Swarm.blockSum (fun j => selectedT p m N j U) k

/-- Cumulative regeneration level. -/
noncomputable def selectedLevel (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) : ℕ :=
  Swarm.blockSum (fun j => selectedD p m N j U) k

/-- The real-valued positive duration functional on one block index. -/
def posTimeReal (q : ℕ × ℕ) : ℝ := (max 1 q.1 : ℕ)

theorem measurable_posTimeReal : Measurable posTimeReal := measurable_of_countable _

/-- A completed genuine chain identifies the totalised and raw durations. -/
theorem selectedT_eq_raw (hN : 0 < N) (p : ℝ) (m : ℕ) (k : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N (k + 1) Set.univ) :
    selectedT p m N k U = (SwarmFB.Z (p := p) (m := m) (N := N) k U).1 := by
  exact max_eq_right (one_le_time_Z hN p m k hU)

/-- Full mass of every finite selected chain under the neutral law. -/
theorem ae_all_chain (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      ∀ n : ℕ, U ∈ SwarmSelInd.Achain p m N n Set.univ := by
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  rw [MeasureTheory.ae_all_iff]
  intro n
  rw [MeasureTheory.ae_iff]
  change (SwarmFB.seedCond (p := p) (m := m) (N := N))
    (SwarmSelInd.Achain p m N n Set.univ)ᶜ = 0
  rw [measure_compl (SwarmSelInd.measurableSet_Achain n MeasurableSet.univ)
    (measure_ne_top _ _), SwarmFB.seedCond_chain hN hfull h0 n, measure_univ, tsub_self]

/-- The neutral `RegenLawWeak`.  The only integrability premise is the genuine
one-block distance mean.  No duration mean is assumed. -/
theorem regenLawWeak_selected (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    Swarm.RegenLawWeak (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (selectedD p m N) (selectedT p m N) := by
  letI : IsProbabilityMeasure (SwarmFB.Q (p := p) (m := m) (N := N)) :=
    SwarmFB.Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  have hfresh := SwarmFB.freshBlocks (p := p) (m := m) hN hfull h0
  have hd := KacFormula.renewal_block_hypotheses hfresh
    SwarmFB.blkLevelR SwarmFB.measurable_blkLevelR hintD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := (hd.2.1 i).integrable_iff.mpr hd.2.2
    simpa only [selectedD, SwarmFB.blkLevelR, Nat.cast_add, Nat.cast_one] using hi
  · intro i U
    exact le_max_left _ _
  · intro i j hij
    simpa only [selectedD, SwarmFB.blkLevelR, Nat.cast_add, Nat.cast_one] using hd.1 hij
  · intro i
    simpa only [selectedD, SwarmFB.blkLevelR, Nat.cast_add, Nat.cast_one] using hd.2.1 i
  · intro i j hij
    have h := (KacFormula.indep_of_fresh hfresh hij).comp
      measurable_posTimeReal measurable_posTimeReal
    simpa only [Function.comp_def, posTimeReal, selectedT] using h
  · intro i
    have h := (KacFormula.ident_distrib_of_fresh hfresh i 0).comp measurable_posTimeReal
    simpa only [Function.comp_def, posTimeReal, selectedT] using h

/-- On all completed chains the cumulative time is the genuine sum of selected
block times. -/
theorem selectedSigma_eq_sum_Z (hN : 0 < N) (p : ℝ) (m : ℕ)
    {U : Array N} (hU : ∀ n : ℕ, U ∈ SwarmSelInd.Achain p m N n Set.univ) (k : ℕ) :
    selectedSigma p m N k U =
      ∑ i : Fin k, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1 := by
  unfold selectedSigma Swarm.blockSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  exact selectedT_eq_raw hN p m j (hU (j + 1))

/-- The cast cumulative level is the genuine sum of selected levels. -/
theorem selectedLevel_cast (p : ℝ) (m : ℕ) (k : ℕ) (U : Array N) :
    (selectedLevel p m N k U : ℤ) =
      ∑ i : Fin k, SwarmFB.blkLevel (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U) := by
  simp only [selectedLevel, selectedD, Swarm.blockSum, Nat.cast_sum,
    Nat.cast_add, Nat.cast_one]
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- The neutral regeneration sequence has the paper's `Sandwich` path structure. -/
theorem sandwich_selected (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
      (selectedPath p m N)
      (fun k U => selectedLevel p m N (k + 1) U - selectedLevel p m N k U)
      (fun k U => selectedSigma p m N (k + 1) U - selectedSigma p m N k U) := by
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) h0
  filter_upwards [ae_all_chain (p := p) (m := m) hN hfull h0] with U hU
  have hσraw : ∀ k : ℕ, selectedSigma p m N k U =
      ∑ i : Fin k, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1 :=
    selectedSigma_eq_sum_Z hN p m hU
  have hzraw : ∀ k : ℕ, (selectedLevel p m N k U : ℤ) =
      ∑ i : Fin k, SwarmFB.blkLevel (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U) :=
    fun k => selectedLevel_cast p m k U
  have hσmono : Monotone (fun k => selectedSigma p m N k U) := by
    apply monotone_nat_of_le_succ
    intro k
    simp [selectedSigma, Swarm.blockSum, Finset.sum_range_succ]
  have hzmono : Monotone (fun k => selectedLevel p m N k U) := by
    apply monotone_nat_of_le_succ
    intro k
    simp [selectedLevel, Swarm.blockSum, Finset.sum_range_succ]
  have hrec : ∀ k : ℕ, SwarmChain.pathRec
      (∑ i : Fin k, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1)
      (∑ i : Fin k, SwarmFB.blkLevel (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U))
      (SwarmRestart.posPath p m U) := fun k => cumulative_record_Z hN p m k (hU k)
  have hlevel : ∀ (k : ℕ) (i : Fin N),
      selectedPath p m N (selectedSigma p m N k U) U i =
        (selectedLevel p m N k U : ℤ) := by
    intro k i
    rw [hσraw k, hzraw k]
    exact (hrec k).2 i
  have hfirst : ∀ (k n : ℕ) (i : Fin N), n < selectedSigma p m N (k + 1) U →
      selectedPath p m N n U i < (selectedLevel p m N (k + 1) U : ℤ) := by
    intro k n i hn
    rw [hσraw (k + 1)] at hn
    rw [hzraw (k + 1)]
    exact (hrec (k + 1)).1 n hn i
  have hnoReturn : ∀ (k : ℕ), 1 ≤ k → ∀ n : ℕ, selectedSigma p m N k U < n →
      ∀ i : Fin N, (selectedLevel p m N k U : ℤ) < selectedPath p m N n U i := by
    intro k _ n hn i
    rw [hσraw k] at hn
    rw [hzraw k]
    let σ : ℕ := ∑ i : Fin k, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1
    let z : ℤ := ∑ i : Fin k, SwarmFB.blkLevel
      (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U)
    have ht := cumulative_tail_Z hN p m k (hU k)
    have hpos := (SwarmFresh.mem_strictPos.mp ht).2
    let j := n - σ
    have hj : 0 < j := by dsimp [j, σ]; omega
    have hp := hpos j hj i
    change 0 < SwarmRestart.posPath p m U (σ + j) i - z at hp
    have heq : σ + j = n := by dsimp [j, σ]; omega
    rw [heq] at hp
    change z < SwarmRestart.posPath p m U n i
    exact sub_pos.mp hp
  have hs := M6Star.sandwich_of_regenSequence
    (x := fun n i => selectedPath p m N n U i)
    (σ := fun k => selectedSigma p m N k U) (z := fun k => selectedLevel p m N k U)
    (by simp [selectedSigma, Swarm.blockSum]) (by simp [selectedLevel, Swarm.blockSum])
    hσmono hzmono hlevel hnoReturn hfirst
  simpa [selectedSigma, selectedLevel, Swarm.blockSum, Finset.sum_range_succ] using hs

/-- The successive level difference is exactly the selected distance. -/
theorem selectedLevel_succ_sub (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) :
    selectedLevel p m N (k + 1) U - selectedLevel p m N k U = selectedD p m N k U := by
  simp [selectedLevel, Swarm.blockSum, Finset.sum_range_succ]

/-- The successive time difference is exactly the totalised selected duration. -/
theorem selectedSigma_succ_sub (p : ℝ) (m N : ℕ) (k : ℕ) (U : Array N) :
    selectedSigma p m N (k + 1) U - selectedSigma p m N k U = selectedT p m N k U := by
  simp [selectedSigma, Swarm.blockSum, Finset.sum_range_succ]

/-- Neutral regeneration increments and their path structure, for the same
`selectedD` and `selectedT`. -/
theorem neutral_regen_bridge (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    Swarm.RegenLawWeak (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (selectedD p m N) (selectedT p m N) ∧
      Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (selectedPath p m N) (selectedD p m N) (selectedT p m N) := by
  refine ⟨regenLawWeak_selected hN hfull h0 hintD, ?_⟩
  simpa only [selectedLevel_succ_sub, selectedSigma_succ_sub] using
    sandwich_selected (p := p) (m := m) hN hfull h0

/-- Model-parameter form: seed positivity is proved.  The exact remaining
stochastic premises are the one-stage full-selection identity and the mean
one-block distance. -/
theorem neutral_regen_bridge_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {N : ℕ} (hN2 : 2 ≤ N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)))
    (hintD : Integrable SwarmFB.blkLevelR
      (SwarmFB.Q (p := p) (m := m) (N := N))) :
    Swarm.RegenLawWeak (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (selectedD p m N) (selectedT p m N) ∧
      Swarm.Sandwich (SwarmFB.seedCond (p := p) (m := m) (N := N))
        (selectedPath p m N) (selectedD p m N) (selectedT p m N) := by
  apply neutral_regen_bridge (by omega) hfull _ hintD
  unfold SwarmFB.seedSet
  exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN2

end NeutralRegen
