/-
# A compatible start law for the stopped-record chain


`RecordLawBridge.startLaw_constraint_of_jointLawIdentity` shows that the joint
`(defect, record time)` law identity forces the start law `ν` of the stopped-record path law to be
carried by `{dmax = 0, time = 0}`.  This file shows that the constraint is **satisfiable**: the
record state with every walker at the record level and local time one at the origin is a genuine
element of `SwarmRec.RecState`, its `dmax` is `0`, and its Dirac law (together with record time
`0`) satisfies the constraint.

What this does *not* do: it does not prove the law identity for that `ν`, and it does not identify
the iterates of the record kernel with the actual array's record process.  It only rules out the
possibility that the constraint is vacuous.
-/
import Swarm.RecordLawBridge

open MeasureTheory Set
open scoped ENNReal

namespace SwarmRecordMeas

namespace StartLaw

open SimJump.RecKernel SwarmRec

variable {N m : ℕ} [Nonempty (Fin N)]

/-- Local times of the all-at-the-record state: one visit at the origin, none elsewhere. -/
def zeta (m : ℕ) (hm : 1 ≤ m) : Fin N → ℤ → Fin (m + 1) :=
  fun _ x => if x = 0 then ⟨1, Nat.lt_succ_of_le hm⟩ else 0

theorem zeta_above (hm : 1 ≤ m) (i : Fin N) {x : ℤ} (hx : 0 < x) : zeta (N := N) m hm i x = 0 := by
  have hx0 : x ≠ 0 := by omega
  simp only [zeta, hx0, if_false]

theorem zeta_at_zero (hm : 1 ≤ m) (i : Fin N) :
    zeta (N := N) m hm i 0 = ⟨1, Nat.lt_succ_of_le hm⟩ := by
  simp [zeta]

/-- The local-time field of the all-at-the-record state satisfies the record-state constraints
with every half-distance `0`. -/
theorem zeta_mem_secSet (hm : 1 ≤ m) : zeta (N := N) m hm ∈ secSet N m (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i x hx
    exact zeta_above hm i hx
  · intro i
    have h0 : -(2 * ((fun _ => (0 : ℕ)) i : ℤ)) = 0 := by simp
    rw [h0, zeta_at_zero hm i]
    apply Fin.le_def.2
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
  · intro i
    rw [zeta_at_zero hm i]
    apply Fin.ext
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m + 1)]

/-- **The all-at-the-record state**: all half-distances zero, local time one at the origin. -/
def zeroState (hm : 1 ≤ m) : RecState N m :=
  ⟨(fun _ => 0, zeta (N := N) m hm), ⟨Classical.arbitrary (Fin N), rfl⟩, zeta_mem_secSet hm⟩

theorem dist2_zeroState (hm : 1 ≤ m) (i : Fin N) : dist2 (zeroState (N := N) (m := m) hm) i = 0 :=
  rfl

/-- The diameter coordinate of the all-at-the-record state is `0`. -/
theorem dmax_zeroState (hm : 1 ≤ m) : dmax (zeroState (N := N) (m := m) hm) = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine Finset.sup_le (fun i _ => ?_)
  rw [dist2_zeroState]

/-- **The forced start-law constraint is satisfiable.**  The Dirac law at the all-at-the-record
state, with record time `0`, is a probability measure carried by `{dmax = 0, time = 0}`. -/
theorem exists_startLaw_constraint (hm : 1 ≤ m) :
    ∃ ν : Measure (RecState N m × ℕ), IsProbabilityMeasure ν ∧
      ν {z : RecState N m × ℕ | dmax z.1 = 0 ∧ z.2 = 0} = 1 := by
  refine ⟨Measure.dirac (zeroState (N := N) (m := m) hm, (0 : ℕ)), inferInstance, ?_⟩
  have hmem : (zeroState (N := N) (m := m) hm, (0 : ℕ))
      ∈ {z : RecState N m × ℕ | dmax z.1 = 0 ∧ z.2 = 0} :=
    ⟨dmax_zeroState hm, rfl⟩
  exact Measure.dirac_apply_of_mem hmem

end StartLaw

end SwarmRecordMeas


