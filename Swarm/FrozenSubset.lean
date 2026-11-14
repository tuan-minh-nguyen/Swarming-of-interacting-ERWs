/-
  **Frozen crossing on measurable subsets of the bad-position event.**

  `FrozenHdom.lean` treats the whole `badPos` event.  The paper's exponential estimate is on
  the smaller event `badPos ∩ ActualExtra`, so the domination and the crossing estimate are
  localized here to an arbitrary `enlFilt s`-measurable `A ⊆ badPos`.  The shifted `hitsBefore`
  conclusion is the one consumed by the actual `BadTime` bridge.
-/
import Swarm.FrozenActualCross

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- Right-jump indicators of `Xtil` and the frozen walk agree on any modification event. -/
lemma stepRight_Xtil_restrict (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A) (hsn : s ≤ n) :
    MeasureTheory.condExp (enlFilt p m n) ((arrayMeasure N).restrict A)
        (stepRight (Xtil p m i b0 b1 s A) n) =ᵐ[(arrayMeasure N).restrict A]
      MeasureTheory.condExp (enlFilt p m n) ((arrayMeasure N).restrict A)
        (stepRight (nWalkF p m i b0 b1 s) n) := by
  apply condExp_congr_ae
  have hmem : ∀ᵐ U ∂((arrayMeasure N).restrict A), U ∈ A :=
    ae_restrict_mem ((enlFilt p m).le n _ hA)
  filter_upwards [hmem] with U hU
  unfold stepRight
  rw [Xtil_of_mem hsn hU, Xtil_of_mem (by omega) hU]

/-- Restriction formula for the conditional expectation of a modified frozen step. -/
lemma condExp_Xtil_restrict (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A) (hsn : s ≤ n) :
    MeasureTheory.condExp (enlFilt p m n) ((arrayMeasure N).restrict A)
        (stepRight (Xtil p m i b0 b1 s A) n) =ᵐ[(arrayMeasure N).restrict A]
      A.indicator ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n | enlFilt p m n]) := by
  have hAn : MeasurableSet[enlFilt p m n] A := (enlFilt p m).mono hsn A hA
  have hXm : ∀ k, Measurable[enlFilt p m k] (Xtil p m i b0 b1 s A k) :=
    fun k => Xtil_measurable p m i b0 b1 s hA k
  have hRmeas : Measurable (stepRight (Xtil p m i b0 b1 s A) n) := by
    exact Measurable.ite
      (measurableSet_eq_fun ((hXm (n + 1)).mono ((enlFilt p m).le (n + 1)) le_rfl)
        (((hXm n).mono ((enlFilt p m).le n) le_rfl).add measurable_const))
      measurable_const measurable_const
  have hI : Integrable (stepRight (Xtil p m i b0 b1 s A) n) (arrayMeasure N) :=
    Integrable.of_bound hRmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun U => norm_stepRight_le n U))
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  exact condExp_restrict_of_measurableSet ((enlFilt p m).le n) hAn
    (f := stepRight (Xtil p m i b0 b1 s A) n) hI

/-- **The modified process has the required domination on every measurable subset of `badPos`.** -/
theorem hdom_Xtil_of_subset_badPos (p : ℝ) (m : ℕ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (i j : Fin N) {b0 b1 s n : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hsub : A ⊆ {U : Array N | badPos p m U i j (b1 : ℤ) s})
    (hb : b0 < b1) (hij : i ≠ j) (hsn : s ≤ n) :
    ∀ᵐ U ∂(arrayMeasure N),
      b0 < Xtil p m i b0 b1 s A n U → Xtil p m i b0 b1 s A n U ≤ b1 →
      revealedWF p m j s U (Xtil p m i b0 b1 s A n U) ≤
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n | enlFilt p m n]) U := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hAn : MeasurableSet[enlFilt p m n] A := (enlFilt p m).mono hsn A hA
  have hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → (trajectory p m U s).pos i = b1 :=
    Filter.Eventually.of_forall (fun U hU => (hsub hU).1)
  have hbadA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → badPos p m U i j (b1 : ℤ) s :=
    Filter.Eventually.of_forall (fun U hU => hsub hU)
  have hdom := frozen_hdom_local p m i j hp0.le hb hij hsn hA hstartA hbadA
    (condExp_stepUp_enl p hp0 hp1 i)
  have hbridge := condExp_Xtil_restrict p m i (b0 := b0) (b1 := b1) hA hsn
  have hrestrict := condExp_restrict_of_measurableSet ((enlFilt p m).le n) hAn
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
    (μ := arrayMeasure N) (s := A)))
  suffices houter : ∀ᵐ U ∂(arrayMeasure N), U ∈ A →
      b0 < Xtil p m i b0 b1 s A n U → Xtil p m i b0 b1 s A n U ≤ b1 →
      revealedWF p m j s U (Xtil p m i b0 b1 s A n U) ≤
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n | enlFilt p m n]) U by
    filter_upwards [houter] with U hU
    by_cases hmem : U ∈ A
    · exact hU hmem
    · rw [Xtil_of_not_mem hsn hmem]
      intro hlo hhi
      omega
  apply (ae_restrict_iff' ((enlFilt p m).le n _ hAn)).mp
  have hmem : ∀ᵐ U ∂((arrayMeasure N).restrict A), U ∈ A :=
    ae_restrict_mem ((enlFilt p m).le n _ hAn)
  have hreq := stepRight_Xtil_restrict p m i (b0 := b0) (b1 := b1) hAn hsn
  filter_upwards [hmem, hdomR, hbridge, hrestrict, hreq] with U hU hd hbri hrestri hreqi
  intro hlo hhi
  have hNlo : b0 < nWalk p m i b0 b1 s n U := by
    rw [← Xtil_of_mem (A := A) hsn hU]
    exact hlo
  have hNhi : nWalk p m i b0 b1 s n U ≤ b1 := by
    rw [← Xtil_of_mem (A := A) hsn hU]
    exact hhi
  have hbase := hd hU hNlo hNhi
  rw [Xtil_of_mem (A := A) hsn hU]
  calc
    revealedWF p m j s U (nWalk p m i b0 b1 s n U) ≤
        ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n |
          enlFilt p m n]) U := hbase
    _ = A.indicator ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n |
          enlFilt p m n]) U := (Set.indicator_of_mem hU _).symm
    _ = MeasureTheory.condExp (enlFilt p m n) ((arrayMeasure N).restrict A)
          (stepRight (nWalkF p m i b0 b1 s) n) U := hrestri.symm
    _ = MeasureTheory.condExp (enlFilt p m n) ((arrayMeasure N).restrict A)
          (stepRight (Xtil p m i b0 b1 s A) n) U := hreqi.symm
    _ = A.indicator ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n |
          enlFilt p m n]) U := hbri
    _ = ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n | enlFilt p m n]) U :=
      Set.indicator_of_mem hU _

/-- **The shifted frozen `hitsBefore` crossing estimate on a subset of `badPos`.** -/
theorem subset_frozen_cross_prob_hitsBefore_le_R
    (p : ℝ) (m : ℕ) (hp0 : 1 / 2 < p) (hp1 : p < 1) (i j : Fin N)
    {b0 b1 s : ℕ} {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    (hsub : A ⊆ {U : Array N | badPos p m U i j (b1 : ℤ) s})
    (hb : b0 < b1) (hij : i ≠ j) :
    (arrayMeasure N).real (hitsBefore (shiftX (Xtil p m i b0 b1 s A) s) b0 (b1 + 1) ∩ A) ≤
      ∫ U in A, R (revealedWF p m j s U) b0 b1 ∂(arrayMeasure N) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → (trajectory p m U s).pos i = b1 :=
    Filter.Eventually.of_forall (fun U hU => (hsub hU).1)
  refine SwarmSpeedLoc.cross_prob_shift_hitsBefore (μ := arrayMeasure N)
    (ℱ := enlFilt p m) (wf := revealedWF p m j s) (X := Xtil p m i b0 b1 s A)
    (hb := hb.le) (hX := ?_) (hw := ?_) (hloh := ?_) (hhih := ?_)
    (hrange := ?_) (hstep := ?_) (hdom := ?_) (hX0b := ?_) (hstartA := ?_) (hA := hA)
  · exact Xtil_measurable p m i b0 b1 s hA
  · exact fun x => measurable_revealedWeight_enlFilt p m s j (x : ℤ)
  · filter_upwards with U x
    exact one_half_le_revealedWeight hp0.le m U j s x
  · filter_upwards with U x
    exact lt_of_le_of_lt (revealedWeight_le_p hp0.le m U j s x) hp1
  · refine hstartA.mono ?_
    intro U hU n hsn
    exact Xtil_range p m i hb hsn hU
  · intro n hsn
    refine hstartA.mono ?_
    intro U hU
    exact Xtil_stepAt p m i hb hsn hU
  · intro n hsn
    exact hdom_Xtil_of_subset_badPos p m hp0 hp1 i j hA hsub hb hij hsn
  · refine hstartA.mono ?_
    intro U hU
    by_cases hmem : U ∈ A
    · rw [Xtil_start_mem p m i hmem (hU hmem)]
      exact hb.le
    · rw [Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s)
        (n := s) (A := A) le_rfl hmem]
      exact hb.le.trans (Nat.le_succ b1)
  · refine hstartA.mono ?_
    intro U hU hmem
    exact Xtil_start_mem p m i hmem (hU hmem)

end SwarmSpeed.Frozen


