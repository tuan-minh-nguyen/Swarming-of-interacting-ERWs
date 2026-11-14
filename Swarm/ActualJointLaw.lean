/-
# The actual canonical joint record law

The record block decomposition identifies every actual finite record-state/time path with the
weighted stopped-record block path law.  The one-step kernel recursion identifies that path law
with the finite window of the genuine Ionescu–Tulcea trajectory.  Finite-window uniqueness then
yields the full canonical joint record law at the compatible Dirac start.
-/
import Swarm.BlockPathSucc
import Swarm.ActualBlockPath
import Swarm.M2RecordFinite

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M7Block

open Swarming Swarming.Uniform SwarmRec SimJump SimJump.RecKernel
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw

variable {N : ℕ} [Nonempty (Fin N)]

/-- The actual finite record-state/time path as a measure on partial endpoint paths. -/
theorem actual_blockPath_map {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : 2 ≤ m) (hN : 2 ≤ N) (r : ℕ) :
    (arrayMeasure N).map (fun U : Array N => fun i : Fin (r + 1) =>
      (M2RecordFinite.actRecStateA p m hm1 U i, recTimeA p m U i))
      = M6Aggr.blockPathLaw p hm1 (zeroState (N := N) (m := m) hm1) 0 r := by
  ext A hA
  rw [Measure.map_apply (M2RecordFinite.measurable_actRecStatA (N := N) p m hm1 (r + 1)) hA]
  exact actual_blockPath_law hp0 hp1 hm1 hm hN r hA

/-- Every record-state/time window of length at least two agrees between the actual array and the
canonical stopped-record trajectory. -/
theorem finiteRecLaw_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ n, 2 ≤ n → M2RecordFinite.FiniteRecLaw (N := N) (m := m) p hp0.le hp1.le
      (by omega : 1 ≤ m) (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))) n := by
  intro n _hn
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ n)
  rw [hr, Nat.add_comm 1 r]
  let hm1 : 1 ≤ m := by omega
  have hblock : M6Aggr.blockPathLaw p hm1 (zeroState (N := N) (m := m) hm1) 0 r
      = (recordTrajT p hp0.le hp1.le hm1
          (Measure.dirac (zeroState (N := N) (m := m) hm1, (0 : ℕ)))).map
          (fun ω : ℕ → RecState N m × ℕ => fun i : Fin (r + 1) => ω i) :=
    M6Step.blockPathLaw_eq_recordTrajT_window p hp0.le hp1.le hm1
      (zeroState (N := N) (m := m) hm1) 0 r
  unfold M2RecordFinite.FiniteRecLaw
  rw [← hblock]
  exact (actual_blockPath_map hp0 hp1 hm1 hm hN r).symm

/-- The actual array's full canonical record-state/time sequence has the law of the stopped-record
trajectory at the compatible Dirac start. -/
theorem jointLawIdentity_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    SwarmRecordMeas.Bridge.JointLawIdentity (N := N) (m := m) p hp0.le hp1.le
      (by omega : 1 ≤ m) (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))) :=
  M2RecordFinite.jointLawIdentity_of_finiteRecLaw_ge_two (N := N) (m := m) hp0 hp1 hm hN
    (by omega : 1 ≤ m) (fun n hn => finiteRecLaw_actual (N := N) hp0 hp1 hm hN n hn)

end M7Block
