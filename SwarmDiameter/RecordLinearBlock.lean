import SwarmDiameter.RecordLinearConcentration
import SwarmDiameter.LinearRecordHalving
import SwarmDiameter.RecordCubicBlock

open Filter MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRecordMeas.Actual SwarmRestart RecordDefect PaperBlock

set_option autoImplicit false

namespace Swarming.Diameter

private theorem exists_linear_record_schedule (N : ℕ) {C v : ℝ} (hv : 0 < v) :
    ∃ B T : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ (B : ℝ) + 2 ≤ v * (T : ℝ) ∧
      (1 + 2 / v) * (1 + (C + 1)) ^ (N - 1) - 1 < (B : ℝ) := by
  let D := (1 + 2 / v) * (1 + (C + 1)) ^ (N - 1)
  let B := ⌈D⌉₊ + 1
  let T := ⌈((B : ℝ) + 2) / v⌉₊ + 1
  refine ⟨B, T, Nat.le_add_left _ _, Nat.le_add_left _ _, ?_, ?_⟩
  · rw [mul_comm, ← div_le_iff₀ hv]
    exact (Nat.le_ceil _).trans (by
      dsimp only [T]
      push_cast
      linarith only)
  · have hD := Nat.le_ceil D
    change D - 1 < (B : ℝ)
    dsimp only [B]
    push_cast
    linarith only [hD]

/-- The record-block failure probability is exponentially small in the
initial scale when the threshold is strictly smaller than the population. -/
theorem record_linear_block_failure_le {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hmN : m < N) :
    ∃ B T C₀ L₀ : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ 1 ≤ C₀ ∧ 1 ≤ L₀ ∧ ∃ K c : ℝ,
      0 < K ∧ 0 < c ∧ ∀ L ≥ L₀, ∀ r ≥ C₀ * L,
        (arrayMeasure N).real (recordBlockFailure p m B T L r) ≤ K * Real.exp (-c * (L : ℝ)) := by
  have hN : 2 ≤ N := hm.trans hmN.le
  have hN₀ : 0 < N := by omega
  let v := linearMinimumSpeed p N
  let C := linearPositionConstant p m N
  have hv : 0 < v := linearMinimumSpeed_pos hp₀ hN₀
  have hC : 1 ≤ C := one_le_linearPositionConstant hp₀ hp₁ m hN₀
  obtain ⟨B, T, hB, hT, htime, hBT⟩ := exists_linear_record_schedule N (C := C) hv
  obtain ⟨ε, hε, hε₁, L₁, hhalf⟩ := record_defect_halves_of_linear_clauses (ι := Fin N)
    B T hC hv htime (by simpa only [Fintype.card_fin] using hBT)
  obtain ⟨K, c, hK, hc, hprob⟩ := record_linear_clauses_failure_le_exp hp₀ hp₁ hm hmN T hT hε
  obtain ⟨L₂, hprob⟩ := eventually_atTop.mp hprob
  refine ⟨B, T, T + 3, max 1 (max L₁ L₂), hB, hT, by omega, le_max_left _ _, K, c, hK, hc, ?_⟩
  intro L hL r hr
  have hL₁ : L₁ ≤ L := by omega
  have hL₂ : L₂ ≤ L := by omega
  let E := RecClockLG.recordCarrier (N := N) p m r L ∩ {U |
    ¬ LinearBlockClauses (Xa p m U) (tauA p m U) r T L C v (ε * (L : ℝ))}
  have hcover : ∀ᵐ U ∂arrayMeasure N, U ∈ recordBlockFailure p m B T L r → U ∈ E := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN] with U hU hbad
    have hdiam : pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) ≤ (L : ℝ) :=
      hbad.1
    rw [pathDiameter_record_eq_defect hU r] at hdiam
    have hd : defect (Xa p m U) (tauA p m U) r ≤ (L : ℤ) := by exact_mod_cast hdiam
    have hcarrier : U ∈ RecClockLG.recordCarrier p m r L :=
      ⟨hU, Int.toNat_le.mpr (by simpa only [defect, M4D.Xa_eq_actX, M4D.tauA_eq] using hd)⟩
    refine ⟨hcarrier, fun hcl => ?_⟩
    have hrec := M1D.isRecord_Xa hcarrier
    have htime' := hcl.advance hrec hd hε₁ htime
    have hhalf' := hhalf L hL₁ r hr (Xa p m U) (tauA p m U) hrec (Xa_step p m U) hd hcl
    rcases hbad.2 with hb | hb
    · rw [recordTime_posPath_eq_of_mem_reachAll hU (r + B * L), recordTime_posPath_eq_of_mem_reachAll hU r,
        ← ENat.natCast_sub, ENat.natCast_lt_natCast] at hb
      exact (not_lt_of_ge htime') hb
    · rw [pathDiameter_record_eq_defect hU (r + B * L)] at hb
      have hcast : (2 : ℝ) * (defect (Xa p m U) (tauA p m U) (r + B * L) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hhalf'
      linarith only [hcast, hb]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)).trans (hprob L hL₂ r hr)

end Swarming.Diameter
