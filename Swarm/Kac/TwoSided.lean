/-
# The two-sided i.i.d. environment: an invertible measure-preserving shift

The Kac bound of `KacDisjoint.lean` is stated for an invertible measure-preserving
map `θ : Ω ≃ᵐ Ω` of a probability space.  In `main_1d_revised.tex` §3.2 the space
is the two-sided sequence of record states and path segments, whose law `P_π` is
built by Kolmogorov extension precisely so that the left shift `θ` is invertible
and preserves `P_π`:

> "By the Kolmogorov extension theorem we construct a two-sided sequence of states
> and segments with these distributions.  Since these distributions do not depend
> on the absolute record indices, we obtain a stationary sequence.  …  The map
> `θ` is invertible and preserves `P_π`."

This file verifies the corresponding statement for the concrete **i.i.d.
environment**: the two-sided product law on `ℤ → α`, on which the shift is an
invertible measure-preserving map.  It is the model case of the stationarity
hypothesis `MeasurePreserving θ P_π P_π` used by the Kac argument, and it
instantiates the Kac bound and the conditioned-mean bound on a genuine
infinite-dimensional stationary system.

Every declaration is checked by `verify.sh` and `Audit.lean` (`#print axioms`).
-/
import Swarm.Imports
import Swarm.KacDisjoint
import Swarm.KacTransfer

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace KacFormula

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]

/-- The left shift of a two-sided environment. -/
def shift (x : ℤ → α) : ℤ → α := fun i => x (i + 1)

lemma measurable_shift : Measurable (shift (α := α)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (i + 1)

/-- The left shift as a measurable equivalence, with inverse `x ↦ x (· - 1)`. -/
def shiftEquiv (α : Type*) [MeasurableSpace α] : (ℤ → α) ≃ᵐ (ℤ → α) where
  toEquiv :=
    { toFun := fun x i => x (i + 1)
      invFun := fun x i => x (i - 1)
      left_inv := by
        intro x
        funext i
        show x ((i - 1) + 1) = x i
        rw [Int.sub_add_cancel]
      right_inv := by
        intro x
        funext i
        show x ((i + 1) - 1) = x i
        rw [Int.add_sub_cancel] }
  measurable_toFun := measurable_shift
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (i - 1)

lemma shiftEquiv_apply (x : ℤ → α) : shiftEquiv α x = shift x := rfl

/-- **The two-sided i.i.d. environment is shift-invariant**: the shift preserves the
product law.  This is the concrete instance of `θ` preserving `P_π`. -/
theorem measurePreserving_shift :
    MeasurePreserving (shiftEquiv α) (Measure.infinitePi fun _ : ℤ => ν)
      (Measure.infinitePi fun _ : ℤ => ν) where
  measurable := (shiftEquiv α).measurable
  map_eq := by
    convert Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℤ => ν) (f := fun i : ℤ => i + 1) (fun a b hab => add_right_cancel hab) using 2
    ext x i
    rfl

/-- **Kac's inequality on the two-sided i.i.d. environment**: for any measurable set
`A` of environments, the mean of the first positive return time to `A`, measured
along the shift orbit, satisfies `Σ_k μ (A ∩ {D > k}) ≤ 1`. -/
theorem twoSided_kac_tsum_le_one (A : Set (ℤ → α)) (hA : MeasurableSet A) :
    ∑' k : ℕ,
        (Measure.infinitePi fun _ : ℤ => ν)
          (A ∩ noReturn (shiftEquiv α : (ℤ → α) → (ℤ → α)) A k) ≤ 1 :=
  kac_tsum_le_one (shiftEquiv α) measurePreserving_shift A hA

/-- **Kac's bound on the conditioned mean return time on the two-sided i.i.d.
environment**: `E_{μ(·|A)}[D] ≤ 1/μ(A)`. -/
theorem twoSided_kac_cond_mean_le (A : Set (ℤ → α)) (hA : MeasurableSet A) :
    ∫⁻ x, (retTime (shiftEquiv α : (ℤ → α) → (ℤ → α)) A x : ℝ≥0∞)
        ∂(((Measure.infinitePi fun _ : ℤ => ν) A)⁻¹ •
          ((Measure.infinitePi fun _ : ℤ => ν).restrict A))
      ≤ ((Measure.infinitePi fun _ : ℤ => ν) A)⁻¹ :=
  kac_cond_mean_le (shiftEquiv α) measurePreserving_shift A hA

end KacFormula
