import Swarm.PullOut

open MeasureTheory

namespace Swarming.Enl

/-- Coordinatewise measurability for a map into a countable product, in the `Measurable[m]` form
(with the domain σ-algebra an explicit argument), which `measurable_pi_iff` does not provide. -/
theorem measurable_pi_iff_enl {α : Type*} {m : MeasurableSpace α} {X : ℕ → Type*}
    [∀ a, MeasurableSpace (X a)] {F : α → ∀ a, X a} :
    Measurable[m] F ↔ ∀ a, Measurable[m] (fun x => F x a) := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

end Swarming.Enl
