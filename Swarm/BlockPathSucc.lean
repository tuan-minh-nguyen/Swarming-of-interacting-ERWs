/-
# The one-step recursion stated directly for `M6Aggr.blockPathLaw`

`OneStep.blockPathLawIic_succ` is stated for the `Iic r`-shaped block path law, the shape in
which it matches `M6Aggr.homTraj_window_succ`.  This file re-expresses it in terms of
`M6Aggr.blockPathLaw` itself, using the two re-indexings `toIicPath` (`Fin (r+1)` → `Iic r`) and
`toFinPath` (`Iic r` → `Fin (r+1)`), so that the recursion is a statement about the object
`M6Aggr.blockPathLaw` and one step of `hitKKernelT` alone.

No `sorry`, no new axioms.
-/
import Swarm.WindowLaw

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M6Step

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec M5FirstBlock M6Aggr

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### The reverse re-indexing -/

/-- A `Fin (r+1)`-shaped path, regarded as an `Iic r`-shaped path (the inverse re-indexing). -/
def toIicPath {X : Type*} (r : ℕ) (f : (i : Fin (r + 1)) → X) : (i : ↥(Finset.Iic r)) → X :=
  fun i => f ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

@[simp] theorem toIicPath_apply {X : Type*} (r : ℕ) (f : (i : Fin (r + 1)) → X)
    (i : ↥(Finset.Iic r)) :
    toIicPath r f i = f ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩ := rfl

theorem measurable_toIicPath {X : Type*} [MeasurableSpace X] (r : ℕ) :
    Measurable (toIicPath (X := X) r) := by
  refine measurable_pi_lambda (fun (f : (i : Fin (r + 1)) → X) (i : ↥(Finset.Iic r)) =>
    f ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩) (fun i => ?_)
  exact measurable_pi_apply _

/-- The two re-indexings are inverse to each other. -/
theorem toIicPath_toFinPath {X : Type*} (r : ℕ) (g : (i : ↥(Finset.Iic r)) → X) :
    toIicPath r (toFinPath r g) = g := by
  funext i
  rw [toIicPath_apply, toFinPath_apply]

/-- **`blockPathLawIic` is `blockPathLaw` re-indexed.** -/
theorem blockPathLawIic_eq_map_toIicPath (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m)
    (t r : ℕ) :
    blockPathLawIic (N := N) p hm y t r
      = (blockPathLaw (N := N) p hm y t r).map (toIicPath (X := RecState N m × ℕ) r) := by
  rw [blockPathLaw_eq_map_blockPathLawIic p hm y t r,
    Measure.map_map (measurable_toIicPath (X := RecState N m × ℕ) r)
      (measurable_toFinPath (X := RecState N m × ℕ) r),
    show toIicPath (X := RecState N m × ℕ) r ∘ toFinPath (X := RecState N m × ℕ) r = id from
      funext (toIicPath_toFinPath r),
    Measure.map_id]

/-! ### The recursion for `blockPathLaw` -/

/-- **The narrow one-step recursion of `M6Aggr.blockPathLaw`.**

The `(r+1)`-block block path law is the `r`-block block path law, re-indexed to the `Iic r` shape,
tensored with one step of the time-extended stopped record kernel at the prefix's last coordinate,
and appended as a new last coordinate; then re-indexed back to the `Fin (r+2)` shape of
`M6Aggr.blockPathLaw`.  Both the prefix law and the result are literally `M6Aggr.blockPathLaw`. -/
theorem blockPathLaw_succ (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) :
    blockPathLaw (N := N) p hm y t (r + 1)
      = (((blockPathLaw (N := N) p hm y t r).map
            (toIicPath (X := RecState N m × ℕ) r) ⊗ₘ homFam (hitKKernelT p hm) r).map
          (fun q : ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) × (RecState N m × ℕ) =>
            toFinPath (X := RecState N m × ℕ) (r + 1) (appendFun q.1 q.2))) := by
  rw [blockPathLaw_eq_map_blockPathLawIic p hm y t (r + 1),
    blockPathLawIic_succ p hp0 hp1 hm y t r,
    ← blockPathLawIic_eq_map_toIicPath p hm y t r,
    Measure.map_map (measurable_toFinPath (X := RecState N m × ℕ) (r + 1))
      (measurable_appendFun (X := RecState N m × ℕ) (r := r))]
  rfl

end M6Step
