import Swarm.FrozenCrossMain
import Swarm.EnlReveal
import Swarm.EnlRight

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- Right-jump indicators of `Xtil` and the frozen walk agree on the bad event. -/
lemma stepRight_Xtil_restrict_bad (p : ℝ) (m : ℕ) (i j : Fin N) {b0 b1 s n : ℕ}
    (hb : b0 < b1) (hsn : s ≤ n) :
    MeasureTheory.condExp (enlFilt p m n)
      ((arrayMeasure N).restrict {U : Array N | badPos p m U i j (b1 : ℤ) s})
        (stepRight (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s}) n) =ᵐ[(arrayMeasure N).restrict
          {U : Array N | badPos p m U i j (b1 : ℤ) s}]
      MeasureTheory.condExp (enlFilt p m n)
      ((arrayMeasure N).restrict {U : Array N | badPos p m U i j (b1 : ℤ) s})
        (stepRight (nWalkF p m i b0 b1 s) n) := by
  have hAn : MeasurableSet[enlFilt p m n] {U : Array N | badPos p m U i j (b1 : ℤ) s} := by
    exact measurableSet_badPos (N := N) p m n hsn i j (b1 : ℤ)
  apply condExp_congr_ae
  have hmem : ∀ᵐ U ∂((arrayMeasure N).restrict
      {U : Array N | badPos p m U i j (b1 : ℤ) s}), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    ae_restrict_mem ((enlFilt p m).le n _ hAn)
  filter_upwards [hmem] with U hU
  unfold stepRight
  rw [Xtil_of_mem hsn hU, Xtil_of_mem (by omega) hU]

/-- The bridge between bad-event conditional expectations of `Xtil` and `nWalk`. -/
lemma condExp_Xtil_restrict_bad (p : ℝ) (m : ℕ) (i j : Fin N) {b0 b1 s n : ℕ}
    (hb : b0 < b1) (hsn : s ≤ n) :
    MeasureTheory.condExp (enlFilt p m n)
      ((arrayMeasure N).restrict {U : Array N | badPos p m U i j (b1 : ℤ) s})
        (stepRight (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s}) n)
      =ᵐ[(arrayMeasure N).restrict
          {U : Array N | badPos p m U i j (b1 : ℤ) s}]
      {U : Array N | badPos p m U i j (b1 : ℤ) s}.indicator
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s
          {U : Array N | badPos p m U i j (b1 : ℤ) s}) n | enlFilt p m n]) := by
  have hAn : MeasurableSet[enlFilt p m n] {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    measurableSet_badPos (N := N) p m n hsn i j (b1 : ℤ)
  have hXm : ∀ k, Measurable[enlFilt p m k]
      (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} k) :=
    fun k => Xtil_measurable p m i b0 b1 s
      (measurableSet_badPos (N := N) p m s le_rfl i j (b1 : ℤ)) k
  have hRmeas : Measurable (stepRight (Xtil p m i b0 b1 s
      {U : Array N | badPos p m U i j (b1 : ℤ) s}) n) := by
    exact Measurable.ite
      (measurableSet_eq_fun ((hXm (n + 1)).mono ((enlFilt p m).le (n + 1)) le_rfl)
        (((hXm n).mono ((enlFilt p m).le n) le_rfl).add measurable_const))
      measurable_const measurable_const
  have hI : Integrable (stepRight (Xtil p m i b0 b1 s
      {U : Array N | badPos p m U i j (b1 : ℤ) s}) n) (arrayMeasure N) :=
    Integrable.of_bound hRmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun U => norm_stepRight_le n U))
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  exact condExp_restrict_of_measurableSet ((enlFilt p m).le n) hAn
    (f := stepRight (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s}) n) hI

/-- **The assembled process has the required revealed-weight domination on the bad event.**
Only the verified enlarged one-step law is used; no global start-at-`b1` or other stochastic
input is required. -/
theorem hdom_Xtil_bad (p : ℝ) (m : ℕ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (i j : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1) (hij : i ≠ j) (hsn : s ≤ n) :
    ∀ᵐ U ∂(arrayMeasure N),
      b0 < Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U →
      Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U ≤ b1 →
      revealedWF p m j s U
          (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U) ≤
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s
          {U : Array N | badPos p m U i j (b1 : ℤ) s}) n | enlFilt p m n]) U := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hA : MeasurableSet[enlFilt p m s] {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    measurableSet_badPos (N := N) p m s le_rfl i j (b1 : ℤ)
  have hAn : MeasurableSet[enlFilt p m n] {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    measurableSet_badPos (N := N) p m n hsn i j (b1 : ℤ)
  have hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} →
      (trajectory p m U s).pos i = b1 := Filter.Eventually.of_forall (fun U h => h.1)
  have hbadA : ∀ᵐ U ∂(arrayMeasure N), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} →
      badPos p m U i j (b1 : ℤ) s := Filter.Eventually.of_forall (fun U h => h)
  have hdom := frozen_hdom_local p m i j hp0.le hb hij hsn hA hstartA hbadA
    (condExp_stepUp_enl p hp0 hp1 i)
  have hbridge := condExp_Xtil_restrict_bad p m i j hb hsn
  have hrestrict := condExp_restrict_of_measurableSet ((enlFilt p m).le n)
    (measurableSet_badPos (N := N) p m n hsn i j (b1 : ℤ))
    (f := stepRight (nWalkF p m i b0 b1 s) n)
    (show Integrable (stepRight (nWalkF p m i b0 b1 s) n) (arrayMeasure N) from by
      change Integrable (fun U : Array N =>
        if nWalkF p m i b0 b1 s (n + 1) U = nWalkF p m i b0 b1 s n U + 1
        then (1 : ℝ) else 0) (arrayMeasure N)
      apply Integrable.of_bound (C := 1)
      · exact (Measurable.ite
          (measurableSet_eq_fun ((nWalkF_measurable p m i b0 b1 s (n + 1)).mono
            ((enlFilt p m).le (n + 1)) le_rfl)
            (((nWalkF_measurable p m i b0 b1 s n).mono
              ((enlFilt p m).le n) le_rfl).add measurable_const))
          measurable_const measurable_const).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun U => norm_stepRight_le n U))
  have hdomR := hdom.filter_mono (ae_mono (Measure.restrict_le_self
    (μ := arrayMeasure N) (s := {U : Array N | badPos p m U i j (b1 : ℤ) s})))
  suffices houter : ∀ᵐ U ∂(arrayMeasure N), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} →
      b0 < Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U →
      Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U ≤ b1 →
      revealedWF p m j s U
        (Xtil p m i b0 b1 s {U : Array N | badPos p m U i j (b1 : ℤ) s} n U) ≤
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s
          {U : Array N | badPos p m U i j (b1 : ℤ) s}) n | enlFilt p m n]) U by
    filter_upwards [houter] with U hU
    by_cases hmem : U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s}
    · exact hU hmem
    · rw [Xtil_of_not_mem hsn hmem]
      intro hlo hhi
      omega
  apply (ae_restrict_iff' ((enlFilt p m).le n _ hAn)).mp
  have hmem : ∀ᵐ U ∂((arrayMeasure N).restrict
      {U : Array N | badPos p m U i j (b1 : ℤ) s}), U ∈ {U : Array N | badPos p m U i j (b1 : ℤ) s} :=
    ae_restrict_mem ((enlFilt p m).le n _ hAn)
  have hreq := stepRight_Xtil_restrict_bad p m i j hb hsn
  filter_upwards [hmem, hdomR, hbridge, hrestrict, hreq] with U hU hd hbri hrestri hreqi
  intro hlo hhi
  have hNlo : b0 < nWalk p m i b0 b1 s n U := by
    rw [← Xtil_of_mem (A := {U : Array N | badPos p m U i j (b1 : ℤ) s}) hsn hU]
    exact hlo
  have hNhi : nWalk p m i b0 b1 s n U ≤ b1 := by
    rw [← Xtil_of_mem (A := {U : Array N | badPos p m U i j (b1 : ℤ) s}) hsn hU]
    exact hhi
  have hbase := hd hU hNlo hNhi
  rw [Xtil_of_mem (A := {U : Array N | badPos p m U i j (b1 : ℤ) s}) hsn hU]
  calc
    revealedWF p m j s U (nWalk p m i b0 b1 s n U) ≤
        ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n |
          enlFilt p m n]) U := hbase
    _ = {U : Array N | badPos p m U i j (b1 : ℤ) s}.indicator
        ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n | enlFilt p m n]) U :=
      (Set.indicator_of_mem (s := {U : Array N | badPos p m U i j (b1 : ℤ) s}) hU _).symm
    _ = MeasureTheory.condExp (enlFilt p m n)
          ((arrayMeasure N).restrict {U : Array N | badPos p m U i j (b1 : ℤ) s})
          (stepRight (nWalkF p m i b0 b1 s) n) U := hrestri.symm
    _ = MeasureTheory.condExp (enlFilt p m n)
          ((arrayMeasure N).restrict {U : Array N | badPos p m U i j (b1 : ℤ) s})
          (stepRight (Xtil p m i b0 b1 s
            {U : Array N | badPos p m U i j (b1 : ℤ) s}) n) U := hreqi.symm
    _ = {U : Array N | badPos p m U i j (b1 : ℤ) s}.indicator
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s
          {U : Array N | badPos p m U i j (b1 : ℤ) s}) n | enlFilt p m n]) U := hbri
    _ = ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s
          {U : Array N | badPos p m U i j (b1 : ℤ) s}) n | enlFilt p m n]) U :=
      Set.indicator_of_mem (s := {U : Array N | badPos p m U i j (b1 : ℤ) s}) hU _

end SwarmSpeed.Frozen


