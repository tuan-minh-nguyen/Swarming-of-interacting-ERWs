import SwarmDiameter.RecordLocalClauses
import SwarmDiameter.RecordHalving
import SwarmDiameter.RecordExceedance
import Swarm.HalfNumerics

open Filter MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRecordMeas.Actual SwarmRestart RecordDefect PaperBlock

set_option autoImplicit false

namespace Swarming.Diameter

/-- The record block fails to halve an initial diameter of at most \(L\) within
the prescribed time. -/
def recordBlockFailure {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m B T L r : ℕ) :
    Set (Array N) :=
  let X := posPath (N := N) p m
  {U | pathDiameter (recordTime (X U) r).toNat (X U) ≤ (L : ℝ) ∧
    (((T * L : ℕ) : ℕ∞) < recordTime (X U) (r + B * L) - recordTime (X U) r ∨
      (L : ℝ) / 2 < pathDiameter (recordTime (X U) (r + B * L)).toNat (X U))}

/-- The trajectory diameter at a record equals the record defect. -/
theorem pathDiameter_record_eq_defect {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    {U : Array N} (hU : U ∈ ReachAll p m) (r : ℕ) :
    pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) =
      (defect (Xa p m U) (tauA p m U) r : ℝ) := by
  rw [recordTime_posPath_eq_of_mem_reachAll hU r, ENat.toNat_natCast]
  have hrec := M4RecordGeom.isRecord_recTimeA_of_reach hU
  unfold pathDiameter LeaderDescent.spreadZ defect
  congr 1
  exact congrArg (fun z : ℤ => z - _) (hrec r).2

private theorem exists_record_schedule (C : ℝ) (N : ℕ) :
    ∃ B T C₀ : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ T + 3 ≤ C₀ ∧ 64 * Nat.ceil C ≤ T ∧
      (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ) := by
  let G := (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (N - 1)
  let B := ⌈G⌉₊ + 2
  let T := max (64 * Nat.ceil C) (⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ + 1)
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hT : 1 ≤ T := (Nat.le_add_left 1 _).trans (le_max_right _ _)
  refine ⟨B, T, T + 3, hB, hT, le_rfl, le_max_left _ _, ?_, ?_⟩
  · have hG := Nat.le_ceil G
    change G - 1 < (B : ℝ) - 2
    dsimp only [B]
    push_cast
    linarith
  · have h := Nat.le_ceil (8 * C * ((B : ℝ) + 5) / 3)
    have h' : (⌈8 * C * ((B : ℝ) + 5) / 3⌉₊ + 1 : ℕ) ≤ T := le_max_right _ _
    exact h.trans_lt (by exact_mod_cast h')

private theorem advance_numerics {C CT ε : ℝ} {B T L : ℕ} (hC : 1 ≤ C) (hε : ε ≤ 1)
    (hL : 1 ≤ L) (hT : 8 * C * ((B : ℝ) + 5) / 3 < (T : ℝ))
    (herr : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε * (L : ℝ)) :
    CT / C ≤ (3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ)) * (L : ℝ) ^ (1 / 4 : ℝ) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : 0 < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hCT : CT ≤ (L : ℝ) ^ (1 / 4 : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hpow).mp
    rw [M1DNum.rpow_quarter_mul_rpow_three_quarters hL]
    exact herr.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hε hLpos.le)
  have hdiv : CT / C ≤ (L : ℝ) ^ (1 / 4 : ℝ) :=
    (div_le_iff₀ hCpos).mpr (hCT.trans (le_mul_of_one_le_right (by positivity) hC))
  have hcoef : (B : ℝ) + 5 < 3 * (T : ℝ) / (8 * C) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8 * C)).mpr
    linarith only [hT]
  exact hdiv.trans (le_mul_of_one_le_left (by positivity) (by linarith only [hcoef]))

/-- The block estimate at rate \(\exp(-c L^{1/3})\) for the actual walks. -/
theorem record_cubic_block_failure_le {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∃ B T C₀ L₀ : ℕ, 1 ≤ B ∧ 1 ≤ T ∧ 1 ≤ C₀ ∧ 1 ≤ L₀ ∧ ∃ K c : ℝ,
      0 < K ∧ 0 < c ∧ ∀ L ≥ L₀, ∀ r ≥ C₀ * L,
        (arrayMeasure N).real (recordBlockFailure p m B T L r) ≤
          K * Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  obtain ⟨C, hC, hprob⟩ := record_local_clauses_failure_le_cube_root hp₀ hp₁ hm N hN
  obtain ⟨B, T, C₀, hB, hT, hC₀, hT64, hBnum, hTnum⟩ := exists_record_schedule C N
  have hcard : 2 ≤ Fintype.card (Fin N) := by simpa only [Fintype.card_fin] using hN
  have hBnum' : (1 + 64 * (Nat.ceil C : ℝ)) *
      (1 + 2 * C ^ 2) ^ (Fintype.card (Fin N) - 1) - 1 < (B : ℝ) - 2 := by
    simpa only [Fintype.card_fin] using hBnum
  obtain ⟨ε, hε, hε₁, L₁, hhalf⟩ :=
    record_defect_halves_of_local_clauses C₀ B T hC hT64 hC₀ hBnum' hcard (2 * p - 1)
  obtain ⟨K, c, hK, hc, hprob⟩ := hprob T hT hε
  obtain ⟨L₂, hprob⟩ := eventually_atTop.mp hprob
  have hC₀₁ : 1 ≤ C₀ := (by omega : 1 ≤ T + 3).trans hC₀
  refine ⟨B, T, C₀, max 1 (max L₁ L₂), hB, hT, hC₀₁, le_max_left _ _, K + 1, c,
    by linarith, hc, ?_⟩
  intro L hL r hr
  have hL₀ : 1 ≤ L := (le_max_left _ _).trans hL
  have hL₁ : L₁ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL₂ : L₂ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hr' : (T + 3) * L ≤ r := (Nat.mul_le_mul_right L hC₀).trans hr
  let CT := ε * (L : ℝ) / (L : ℝ) ^ (3 / 4 : ℝ)
  have hCT : 0 ≤ CT := by dsimp only [CT]; positivity
  have hCTeq : CT * (L : ℝ) ^ (3 / 4 : ℝ) = ε * (L : ℝ) := by
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (by exact_mod_cast hL₀) _).ne'
  let E := RecClockLG.recordCarrier (N := N) p m r L ∩ {U |
    ¬ (BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U) C CT T L r ∧
      JoinStep.MartClause (Xa p m U) (tauA p m U) (fun i n => excitedSteps p m U n i)
        (2 * p - 1) CT T L r)}
  have hcover : ∀ᵐ U ∂arrayMeasure N, U ∈ recordBlockFailure p m B T L r → U ∈ E := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN] with U hU hbad
    have hdiam : pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) ≤ (L : ℝ) :=
      hbad.1
    rw [pathDiameter_record_eq_defect hU r] at hdiam
    have hd : defect (Xa p m U) (tauA p m U) r ≤ (L : ℤ) := by exact_mod_cast hdiam
    have hcarrier : U ∈ RecClockLG.recordCarrier p m r L :=
      ⟨hU, Int.toNat_le.mpr (by simpa only [defect, M4D.Xa_eq_actX, M4D.tauA_eq] using hd)⟩
    refine ⟨hcarrier, ?_⟩
    rintro ⟨hBC, hM⟩
    have hrec := M1D.isRecord_Xa hcarrier
    obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : Fin N, i₀ ≠ j₀ := by
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin N))
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card (Fin N)) i
      exact ⟨j, i, hj⟩
    have htime := LocalFluid.tau_advance_of_locOcc (Xa p m U) hrec (Xa_step p m U)
      (fun _ => rfl) (zero_lt_one.trans_le hC) hBC.base.occ hd hL₀ hij
      (B := B) (advance_numerics hC hε₁ hL₀ hTnum hCTeq.le)
    have htime' : tauA p m U (r + B * L) - tauA p m U r ≤ T * L := by omega
    have hhalf' := hhalf L hL₁ r hr (Xa p m U) (tauA p m U) (Hc p m U) (fun i n => excitedSteps p m U n i)
      CT hrec (Xa_step p m U) hd htime' hBC hM hCT hCTeq.le
    rcases hbad.2 with hbad | hbad
    · rw [recordTime_posPath_eq_of_mem_reachAll hU (r + B * L), recordTime_posPath_eq_of_mem_reachAll hU r,
        ← ENat.natCast_sub, ENat.natCast_lt_natCast] at hbad
      exact (not_lt_of_ge htime') hbad
    · rw [pathDiameter_record_eq_defect hU (r + B * L)] at hbad
      have hcast : (2 : ℝ) * (defect (Xa p m U) (tauA p m U) (r + B * L) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hhalf'
      linarith only [hcast, hbad]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)).trans
    ((hprob L hL₂ r hr').trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))

end Swarming.Diameter
