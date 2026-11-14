/-
  **Restricting a conditional expectation to a measurable set.**

  The generic crossing layer `Swarm/Cross.lean` states its hypotheses almost
  everywhere for the *global* measure, in particular `hstart : X s = b1` a.e.  At the actual
  model the walker's position at the reveal time `s` is only known on the bad-time event, so
  the estimate has to be applied to the restricted measure `μ.restrict A`.  This file supplies
  the only measure-theoretic input that transfer needs: conditioning commutes with restriction
  to an `m`-measurable set in the form

      (μ.restrict A)[f | m] =ᵐ[μ.restrict A] 1_A · μ[f | m].
-/
import Swarm.Imports

open MeasureTheory Filter

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A set integral for a restricted measure, written as a set integral over the intersection. -/
theorem setIntegral_restrict_restrict {A B : Set Ω} (hB : MeasurableSet B) (f : Ω → ℝ) :
    ∫ x in B, f x ∂(μ.restrict A) = ∫ x in B ∩ A, f x ∂μ :=
  congrArg (fun ν : Measure Ω => ∫ x, f x ∂ν) (Measure.restrict_restrict hB)

/-- **Conditioning commutes with restriction.**  For `A` measurable for the sub-σ-algebra `m`
and `f` integrable, the `m`-conditional expectation under `μ.restrict A` is the `m`-conditional
expectation under `μ` multiplied by the indicator of `A`. -/
theorem condExp_restrict_of_measurableSet [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet[m] A) {f : Ω → ℝ} (hf : Integrable f μ) :
    (μ.restrict A)[f | m] =ᵐ[μ.restrict A] A.indicator (μ[f | m]) := by
  classical
  have hA0 : @MeasurableSet Ω m0 A := hm A hA
  have hfA : Integrable f (μ.restrict A) :=
    hf.mono_measure Measure.restrict_le_self
  have hcf : Integrable (μ[f | m]) μ := integrable_condExp
  have hgint : Integrable (A.indicator (μ[f | m])) μ := hcf.indicator hA0
  have hgm : AEStronglyMeasurable[m] (A.indicator (μ[f | m])) (μ.restrict A) :=
    (stronglyMeasurable_condExp.measurable.indicator hA).aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ.restrict A) (m := m) hm hfA
    (fun s _ _ => (hgint.mono_measure Measure.restrict_le_self).integrableOn) ?_ hgm).symm
  intro s hs _
  have hs0 : @MeasurableSet Ω m0 s := hm s hs
  have hsA : MeasurableSet[m] (s ∩ A) := hs.inter hA
  have hsA0 : @MeasurableSet Ω m0 (s ∩ A) := hm (s ∩ A) hsA
  have h1 : ∫ x in s, A.indicator (μ[f | m]) x ∂(μ.restrict A)
      = ∫ x in s ∩ A, (μ[f | m]) x ∂μ := by
    rw [setIntegral_restrict_restrict hs0]
    refine setIntegral_congr_fun hsA0 (fun x hx => ?_)
    exact Set.indicator_of_mem hx.2 _
  have h2 : ∫ x in s, f x ∂(μ.restrict A) = ∫ x in s ∩ A, f x ∂μ :=
    setIntegral_restrict_restrict hs0 f
  rw [h1, h2, setIntegral_condExp hm hf hsA]

end SwarmSpeed
