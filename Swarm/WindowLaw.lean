/-
# The finite path-window identity for `M6Aggr.blockPathLaw`

`M6Step.blockPathLawIic_succ` is the one-step recursion of the block path law in the `Iic r`
shape.  This file

* identifies the `Iic r`-shaped block law with the `Fin (r+1)`-shaped `M6Aggr.blockPathLaw`
  (`blockPathLaw_eq_map_blockPathLawIic`),
* proves the base case `r = 0` (`blockPathLawIic_zero`, both sides are the Dirac at the constant
  path) and runs the induction against `M6Aggr.homTraj_window_succ`, giving
  `blockPathLawIic_eq_trajWindow`:  the `Iic r` window of the stopped-record Ionescu–Tulcea path
  law `recordTrajT p hp0 hp1 hm (δ_{(y,t)})`,
* transports that to the exact `Fin (r+1)` statement
  `blockPathLaw_eq_recordTrajT_window`.

Together with `M2RecordFinite.jointLawIdentity_of_finiteRecLaw`, this supplies the finite
window identity `M2RecordFinite.FiniteRecLaw` at the start law `δ_{(zeroState, 0)}`; the array
side is `M7Block.actual_blockPath_law`.  Nothing here asserts `Bridge.JointLawIdentity` itself.

No `sorry`, no new axioms.
-/
import Swarm.OneStep

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

/-! ### Re-indexing `Finset.Iic r` paths by `Fin (r+1)` -/

/-- The canonical re-indexing of an `Iic r`-shaped path as a `Fin (r+1)`-shaped path. -/
def toFinPath {X : Type*} (r : ℕ) (g : (i : ↥(Finset.Iic r)) → X) : (i : Fin (r + 1)) → X :=
  fun i => g ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩

@[simp] theorem toFinPath_apply {X : Type*} (r : ℕ) (g : (i : ↥(Finset.Iic r)) → X) (i : Fin (r + 1)) :
    toFinPath r g i = g ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩ := rfl

theorem measurable_toFinPath {X : Type*} [MeasurableSpace X] (r : ℕ) :
    Measurable (toFinPath (X := X) r) := by
  refine measurable_pi_lambda (fun (g : (i : ↥(Finset.Iic r)) → X) (i : Fin (r + 1)) =>
    g ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)⟩) (fun i => ?_)
  exact measurable_pi_apply _

/-- The re-indexed restriction of a sequence is its `Fin (r+1)` window. -/
theorem toFinPath_frestrictLe {X : Type*} (r : ℕ) (ω : ℕ → X) :
    toFinPath r (Preorder.frestrictLe (π := fun _ => X) r ω) = fun i : Fin (r + 1) => ω i := by
  funext i
  rw [toFinPath_apply, Preorder.frestrictLe_apply]

/-! ### The block path law in the `Iic` shape -/

/-- **`blockPathLaw` is the `Iic r`-shaped block path law re-indexed.** -/
theorem blockPathLaw_eq_map_blockPathLawIic (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m)
    (t r : ℕ) :
    blockPathLaw (N := N) p hm y t r
      = (blockPathLawIic (N := N) p hm y t r).map (toFinPath (X := RecState N m × ℕ) r) := by
  have hpt : ∀ w : Fin r → Word N,
      toFinPath (X := RecState N m × ℕ) r (pathIic hm y t r w) = pathOf hm y t r w := by
    intro w
    funext i
    rw [toFinPath_apply, pathIic_apply]
  rw [blockPathLaw, blockPathLawIic,
    Measure.map_sum (measurable_toFinPath (X := RecState N m × ℕ) r).aemeasurable]
  refine Eq.symm (sum_measure_congr (fun w => ?_))
  rw [Measure.map_smul, Measure.map_dirac, hpt w]

/-! ### The base case -/

/-- At `r = 0` the `Iic 0`-shaped block path law is the Dirac at the constant path. -/
theorem blockPathLawIic_zero (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) :
    blockPathLawIic (N := N) p hm y t 0
      = Measure.dirac (fun _ : ↥(Finset.Iic 0) => (y, t)) := by
  have hsingle : ∀ (μ : (Fin 0 → Word N) →
      Measure ((i : ↥(Finset.Iic 0)) → RecState N m × ℕ)),
      Measure.sum μ = μ (fun i => i.elim0) := by
    intro μ
    ext s hs
    rw [Measure.sum_apply _ hs]
    exact tsum_eq_single _ (fun b hb => absurd (Subsingleton.elim b _) hb)
  rw [blockPathLawIic, hsingle, blockProdF_zero, ENNReal.ofReal_one, one_smul, pathIic_zero]

/-- The `r = 0` window of the stopped-record path law. -/
theorem homTraj_frestrictLe_zero (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) :
    (recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))).map
        (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) 0)
      = Measure.dirac (fun _ : ↥(Finset.Iic 0) => (y, t)) := by
  haveI hK : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT (N := N) (m := m) p hp0 hp1 hm
  have hdef : recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))
      = homTraj (hitKKernelT p hm) (Measure.dirac (y, t)) := rfl
  rw [hdef]
  have hcomp : (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) 0)
      = (fun z : RecState N m × ℕ => fun _ : ↥(Finset.Iic 0) => z) ∘
          (fun ω : ℕ → RecState N m × ℕ => ω 0) := by
    funext ω i
    rw [Function.comp_apply, Preorder.frestrictLe_apply]
    have hi : (i : ℕ) = 0 := by
      have := i.2
      simp only [Finset.mem_Iic] at this
      omega
    rw [hi]
  rw [hcomp, ← Measure.map_map (by fun_prop : Measurable (fun z : RecState N m × ℕ =>
      fun _ : ↥(Finset.Iic 0) => z)) (measurable_pi_apply 0),
    homTraj_map_zero, Measure.map_dirac]

/-! ### The induction -/

/-- **The `Iic r` window of the block path law is the stopped-record path window.** -/
theorem blockPathLawIic_eq_trajWindow (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) :
    blockPathLawIic (N := N) p hm y t r
      = (recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))).map
          (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) r) := by
  haveI hK : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT (N := N) (m := m) p hp0 hp1 hm
  have hdef : recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))
      = homTraj (hitKKernelT p hm) (Measure.dirac (y, t)) := rfl
  rw [hdef]
  induction r with
  | zero =>
      rw [blockPathLawIic_zero]
      exact (homTraj_frestrictLe_zero p hp0 hp1 hm y t).symm
  | succ r ih =>
      rw [blockPathLawIic_succ p hp0 hp1 hm y t r, ih,
        ← homTraj_window_succ (hitKKernelT p hm) (Measure.dirac (y, t)) r]

/-! ### The exact finite path-window identity -/

/-- **The finite path-window identity**: the `r`-block block path law is the `Fin (r+1)` window of
the time-extended stopped-record Ionescu–Tulcea path law started at `δ_{(y,t)}`. -/
theorem blockPathLaw_eq_recordTrajT_window (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) :
    blockPathLaw (N := N) p hm y t r
      = (recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))).map
          (fun ω : ℕ → RecState N m × ℕ => fun i : Fin (r + 1) => ω i) := by
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) r) := by fun_prop
  have hwin : ∀ ω : ℕ → RecState N m × ℕ,
      toFinPath (X := RecState N m × ℕ) r
          (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) r ω)
        = fun i : Fin (r + 1) => ω i := toFinPath_frestrictLe r
  calc blockPathLaw (N := N) p hm y t r
      = (blockPathLawIic (N := N) p hm y t r).map (toFinPath (X := RecState N m × ℕ) r) :=
        blockPathLaw_eq_map_blockPathLawIic p hm y t r
    _ = ((recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))).map
            (Preorder.frestrictLe (π := fun _ => RecState N m × ℕ) r)).map
            (toFinPath (X := RecState N m × ℕ) r) := by
        rw [blockPathLawIic_eq_trajWindow p hp0 hp1 hm y t r]
    _ = (recordTrajT (N := N) (m := m) p hp0 hp1 hm (Measure.dirac (y, t))).map
          (fun ω : ℕ → RecState N m × ℕ => fun i : Fin (r + 1) => ω i) := by
        rw [Measure.map_map (measurable_toFinPath (X := RecState N m × ℕ) r) hfr]
        exact Measure.map_congr (ae_of_all _ hwin)

end M6Step
