/-
# Downstream diameter assembly (direction 4): the actual-array bridge

This module is the bridge between the *deterministic* nested-leader reduction
(`Swarm/LeaderDescent.lean`, `NestedLeader.lean`, `NestedLeaderPot.lean`) and the
*actual* array measure `arrayMeasure N` of the interacting excited random walk.

It contains no probabilistic assumption other than those spelled out in the hypotheses of its
theorems; `WdriftJoint` supplies the *proved* conditional drift, the proved telescoping and the
`Q^{I,J}` martingale together with its strong law conditional on the paper's log-fourth variance
estimate.
-/
import Swarm.WdriftJoint
import Swarm.NestedLeader
import Swarm.NestedLeaderPot

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssembly

variable {N : ℕ}

/-! ## 0. The actual configuration as an integer path array -/

/-- The actual array read as the integer path array `Fin N → ℕ → ℤ` that the deterministic
leader-descent modules are stated for. -/
noncomputable def XA (p : ℝ) (m : ℕ) (U : Array N) : Fin N → ℕ → ℤ :=
  fun i n => SepGroup.Model.X p m U n i

@[simp] lemma XA_apply (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    XA p m U i n = SepGroup.Model.X p m U n i := rfl

/-- The running maximum of `LeaderDescent` at the actual configuration is the paper's `M_n^j`. -/
lemma runMax_XA (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    LeaderDescent.runMax (XA p m U) j n = Swarming.Trajectory.runMax p m U j n := rfl

/-- **`(sep)` is the leader-descent `SepMax` for the pair `(A, Aᶜ)`.** -/
theorem sepMax_iff_sep (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (n : ℕ) :
    LeaderDescent.SepMax (XA p m U) A n ↔ SepGroup.Model.Sep p m U n A Aᶜ := by
  simp only [LeaderDescent.SepMax, SepGroup.Model.Sep, XA_apply, runMax_XA, mem_compl]

/-- The set-level form of `(sep)` is the pair `(A, Aᶜ)`. -/
theorem sepSet_iff_sepMax (p : ℝ) (m : ℕ) (U : Array N) (A : Finset (Fin N)) (n : ℕ) :
    SwarmJointDrift.SepSet p m n A Aᶜ U ↔ LeaderDescent.SepMax (XA p m U) A n :=
  (sepMax_iff_sep p m U A n).symm

/-- Every actual walker moves by exactly one lattice step. -/
theorem unitStep_XA (p : ℝ) (m : ℕ) (U : Array N) : LeaderDescent.UnitStep (XA p m U) := by
  intro i n
  have hstep : XA p m U i (n + 1) = XA p m U i n +
      Swarming.drivenStep
        (U (i, (trajectory p m U n).pos i, (trajectory p m U n).ell i
          ((trajectory p m U n).pos i)))
        (rightProbability p m (trajectory p m U n).ell i
          ((trajectory p m U n).pos i)) := by
    rw [XA_apply, XA_apply, SepGroup.Model.X_apply, SepGroup.Model.X_apply,
      Swarming.Trajectory.trajectory_succ,
      Swarming.Trajectory.nextWalkState_pos, Swarming.Trajectory.nextPos]
  rw [hstep]
  unfold Swarming.drivenStep
  split <;> simp

/-- Every actual walker starts at `0`. -/
theorem zero_XA (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) : XA p m U i 0 = 0 := by
  rw [XA_apply, SepGroup.Model.X_apply, Swarming.Trajectory.trajectory_zero]
  rfl

/-! ## 1. The total block potential `Wtot`

`SepGroup.Model.WA` needs `A.Nonempty` and `Aᶜ.Nonempty` as arguments (it is the paper's observable
`W^{I,J}`).  To quantify over *all* blocks without dependent proof arguments we use the total
version, which is `0` on the two degenerate blocks `∅` and `univ`. -/

/-- The actual group potential, totalised in the block. -/
noncomputable def Wtot (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) : ℝ :=
  if h : A.Nonempty ∧ Aᶜ.Nonempty then SepGroup.Model.WA p m U n A Aᶜ h.1 h.2 else 0

theorem Wtot_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {A : Finset (Fin N)}
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    Wtot p m U n A = SepGroup.Model.WA p m U n A Aᶜ hA hAc := by
  have h : A.Nonempty ∧ Aᶜ.Nonempty := ⟨hA, hAc⟩
  simp only [Wtot, dif_pos h]

theorem Wtot_eq_zero (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) {A : Finset (Fin N)}
    (h : ¬ (A.Nonempty ∧ Aᶜ.Nonempty)) : Wtot p m U n A = 0 := by
  simp only [Wtot, dif_neg h]

/-! ## 2. `W ≥ gap`: the block gap is dominated by the actual potential

This is `(Wpos)` of the paper already proved as `SepGroup.Model.gap_le_WA`; here it is transported to the
leader-descent `gapAt` and to the totalised potential. -/

theorem gapAt_le_Wtot {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (U : Array N)
    (n : ℕ) {A : Finset (Fin N)} (hsep : LeaderDescent.SepMax (XA p m U) A n) :
    ((LeaderDescent.gapAt (fun i => XA p m U i n) A : ℤ) : ℝ) ≤ Wtot p m U n A := by
  classical
  by_cases h : A.Nonempty ∧ Aᶜ.Nonempty
  · have h' : A.Nonempty ∧ (univ \ A).Nonempty := h
    have hg := SepGroup.Model.gap_le_WA (p := p) (m := m) (U := U) (n := n) (I := A) (J := Aᶜ)
      hp hp1 h.1 h.2 ((sepMax_iff_sep p m U A n).mp hsep)
    rw [Wtot_eq p m U n h.1 h.2, LeaderDescent.gapAt, dif_pos h']
    have e1 : A.inf' h'.1 (fun i => XA p m U i n)
        = A.inf' h.1 (fun i => SepGroup.Model.X p m U n i) := rfl
    have e2 : (univ \ A).sup' h'.2 (fun i => XA p m U i n)
        = Aᶜ.sup' h.2 (fun j => SepGroup.Model.X p m U n j) := rfl
    rw [e1, e2, Int.cast_sub]
    exact hg
  · rw [Wtot_eq_zero p m U n h, LeaderDescent.gapAt_eq_zero _ h]
    simp

end DiamAssembly
