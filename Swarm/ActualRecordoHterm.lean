import Swarm.ActualJointLaw
import Swarm.DiamActual

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M7Block

open Swarming Swarming.Uniform SwarmRec RecordDefect RecordoSupply SimJump SimJump.RecKernel
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw SwarmRecordMeas.Bridge

variable {N : ℕ} [Nonempty (Fin N)]

/-- The actual diameter in the form consumed by the canonical record-time transfer. -/
theorem diam_actual_recordo {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) := by
  simpa [LeaderDescent.spreadZ, RecordDefect.spread, RecordoSupply.actX,
    RecordDefect.runMax, RecordDefect.runMin, DiamAssembly.XA] using
    DiamAssemblyHcomp.diam_actual (N := N) hp0 hp1 hm hN

/-- The canonical stopped-record block statement follows from the proved joint record law and
actual diameter. -/
theorem hterm_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))), ∃ j : ℕ,
        GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
          (2 ^ j * L) :=
  SwarmRecordMeas.Bridge.hterm_pathlaw_of_array_canonical_exists hp0 hp1 hm hN B hB
    (diam_actual_recordo hp0 hp1 hm hN) _
    (jointLawIdentity_actual hp0 hp1 hm hN)

/-- The same fixed block statement, retaining the actual array's lower-speed witness for
later assembly.  Keeping the same `κ` avoids silently changing the block constants when the
scale and tightness inputs are packaged into an invariant-law reduction. -/
theorem hterm_actual_with_speed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
        (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ)) ∧
      ∀ r L : ℕ, 1 ≤ L →
        ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))), ∃ j : ℕ,
          GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r
            (2 ^ j * L) := by
  obtain ⟨κ, hκ, hspeed⟩ := RecordoSupply.speed_actual hp0 hp1 hm
  exact ⟨κ, hκ, hspeed N hN,
    SwarmRecordMeas.Bridge.hterm_pathlaw_of_array_canonical hp0 hp1 hm hN B hB hκ
      (hspeed N hN) (diam_actual_recordo hp0 hp1 hm hN) _
      (jointLawIdentity_actual hp0 hp1 hm hN)⟩


end M7Block
