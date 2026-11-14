/-
  # canonical site-rate instantiation for the single-window occupation event

  ## What this file does

  `LocOccSingleWindow.exists_singleWindow_complement_paper` proves the paper-shaped bound

      mu.real (carrier(r,s0,L) ∩ (GoodWin i j C r T L s0)^c) <= C_T exp (-c_T L^{1/16})

  **given** the one remaining free input of that file, the `LsBad`-rate hypothesis

      mu (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) <= ofReal (exp (-c * xOf (Lw T L)))

  (an input rate `c > 0`), and given a free constant `C` with `1 <= C`.

  This file *discharges* that hypothesis from the verified `(locsum)` machinery and pins the
  constant to the paper's canonical `C = |Mb| + 1`.  The two facts used are

  * `LocSumR1.array_locsum_h_start` (`LocStartRange`): for `C >= 1`, `C > Mb` there are `c > 0`
    and `L₀` such that for every window length `L >= L₀` and every window start `A` with
    `2 * ceil (xOf L)^{1/16} <= A`, the set `LocSumR1.LsBad N p m C L A` has measure at most
    `exp (-c * xOf L)`, **and** off it the `(locsum)` inequality holds for every walker and every
    subinterval of `[A, A+L)`;
  * `LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le`: that start condition is automatic for
    `L` large, at the paper's window `L := Lw T L`, `A := A0 r T L`.

  The resulting `c` and `L₀` do not depend on `r`, and `LocSumR1.LsBad` mentions nothing that
  depends on the display anchor `s0`, so the single-window composition goes through with no rate
  hypothesis at all, at the **original** paper range `(T+3)*L <= r` (no `(T+4)*L`).
  `exists_lsBad_rate_single_window_via_carrierAssembly` re-derives the same rate from
  `LocOccCarrierAssembly.exists_lococc_recordCarrier_TL'`, i.e. from the declaration whose rate the
  `RecCarrierPaper` paper-scale chain consumes, so the instantiated rate is traceable rather than a
  look-alike.

  ## What is *not* proved here

  * No statement about `⋃_{s0}` (clock-fibre summation) — that is a different direction.
  * No finite all-pair intersection / joint all-pair good event — fixed ordered pair `(i, j)`.
  * No non-vacuity of `GoodWin`, no lower bound, no defect tightness, no Kac / invariant measure,
    no speed statement, no all-pairs-unconditional `G`.
  * The `(locmax)` harmonic defect mass `QplWindow.harmDefect` is *retained* in the raw bound
    (`measureReal_recordCarrier_singleWindow_le_paper`); it is estimated away
    (`exp (-c' xOf Lw)`, `CarrierQplResidual`) only in the normalized bound.  It is the only mass
    beyond the two carrier-weighted prices that survives the paper's single window.
  * `C_T` stays existential: the statements guarantee `C_T >= 0`, `c_T > 0`, with
    `c_T, C_T` functions of `N, m, p, T` only — no explicit numeric value is produced.
  * The `i ≠ j` hypothesis of Sections 4-5 is carried for scope fidelity with the paper's ordered
    distinct pair; it is not consumed by the two probability estimates themselves (`GoodWin` and
    `LsBad` are defined for every pair of sites), and Section 5 does consume it.
-/
import Swarm.LocOccSingleWindow
import Swarm.LocStartRange
import Swarm.LocOccCarrierAssembly
import Swarm.RecordCarrierPaperScale

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open SummedSlope.Model

namespace LocOccSiteRate

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The canonical constant -/

/-- **The paper's canonical constant.**  `LocSumR1.array_locsum_h_start` only asks `C >= 1` and
`C > Mb`; `C := |Mb| + 1` is the concrete choice, a function of `p` and `m` alone. -/
noncomputable def Ccan (p : ℝ) (m : ℕ) : ℝ := |LocSum.Mb p (LocSumAct.qOf p m)| + 1

theorem one_le_Ccan (p : ℝ) (m : ℕ) : 1 ≤ Ccan p m := by
  unfold Ccan
  have h := abs_nonneg (LocSum.Mb p (LocSumAct.qOf p m))
  linarith

theorem Mb_lt_Ccan (p : ℝ) (m : ℕ) : LocSum.Mb p (LocSumAct.qOf p m) < Ccan p m := by
  unfold Ccan
  have h := le_abs_self (LocSum.Mb p (LocSumAct.qOf p m))
  linarith

/-! ### 2. The `LsBad` rate at the paper's record window, uniform in `r` -/

/-- **The `(locsum)`/`(locmax)` rate at the record window `[A0 r T L, A0 r T L + Lw T L)`.**

`LocSumR1.array_locsum_h_start` at `A := A0 r T L`, window length `L := Lw T L`: the start
condition `2 ceil (xOf Lw)^{1/16} <= A0 r T L` is the arithmetic side condition discharged through
`LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le` and `le_A0`.

The point of the statement is the quantifier order: `c` and `L₀` do not depend on `r`, and
`LocSumR1.LsBad` does not mention the display anchor `s0` at all — this is exactly the `hLsBad`
input of `LocOccSingleWindow.exists_singleWindow_complement_paper`. -/
theorem exists_lsBad_rate_single_window
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) (T : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) := by
  obtain ⟨c, hc, L₀, hL₀⟩ := LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  obtain ⟨L₁, hL₁⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le (T := T)
  refine ⟨c, hc, max L₀ L₁, ?_⟩
  intro L hL r hr
  have hA : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hB : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hLw : L₀ ≤ Lw T L := le_trans hA (le_Lw T L)
  have hbig : 2 * ellT (xOf (Lw T L)) ≤ A0 r T L := hbig_of_le_L hr (hL₁ L hB)
  exact (hL₀ (Lw T L) hLw (A0 r T L) hbig).1

/-- **Cross-check: the same rate that feeds `RecCarrierPaper`'s joint bound.**

`LocOccCarrierAssembly.exists_lococc_recordCarrier_TL'` is the declaration whose `LsBad` rate
`RecCarrierPaper.exists_recordCarrier_joint_complement_paper` (and its `_canonical` form) consumes,
and it is exactly the statement of `RecCarrierPaper.exists_recordCarrier_joint_complement_paper`
minus that rate hypothesis.  There the rate is bundled inside a `∀ s ≤ t ≤ s + T*L` statement, so
extracting it uses the dummy pair `(s, t) = (0, 0)`; `LocSumR1.array_locsum_h_start` (used in
`exists_lsBad_rate_single_window`) is the primitive behind it, and the two rates therefore agree.
This declaration exists only to make that trace machine-checkable; it is not used below. -/
theorem exists_lsBad_rate_single_window_via_carrierAssembly
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) := by
  obtain ⟨c, hc, L₀, hL₀⟩ :=
    LocOccCarrierAssembly.exists_lococc_recordCarrier_TL' (N := N) hp1 hp2 hm hij hC1 hCM hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL r hr
  exact (hL₀ L hL (r := r) (s := 0) (t := 0) hr (Nat.le_refl 0) (Nat.zero_le _)).1

/-! ### 3. The raw carrier-fixed bound with the rate discharged -/

/-- **The single-window carrier bound with no `LsBad`-rate hypothesis.**

`LocOccSingleWindow.measureReal_recordCarrier_singleWindow_le` with its `hLsBad` input replaced by
the concrete rate of `exists_lsBad_rate_single_window`, at `V = xOf (Lw T L)`.  The three masses are
visible exactly as there: the s0-independent `2 exp (-c xOf Lw)`, the carrier-mass-weighted maximal
Azuma price for the single-window `Qpl` drop, the harmonic `(locmax)` defect
`harmDefect p m j (xOf Lw) (cA r T L) (cM T L)` (a function of `r, T, L, j`, not of `s0`), and the
`Lw`-weighted projected-oscillation price.  No `shiftedContDefect` term appears. -/
theorem measureReal_recordCarrier_singleWindow_le_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
        2 * Real.exp (-c * xOf (Lw T L)) +
          ((arrayMeasure N).real
                (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((T * L : ℕ) : ℝ) + 1) *
                Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
                  (4 * ((T * L : ℕ) : ℝ) *
                    (QplPredEnv.envB p m (xOf (Lw T L))
                      (QplWindow.envC p m (xOf (Lw T L)))) ^ 2))) +
            (arrayMeasure N).real
              (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                QplWindow.harmDefect p m j (xOf (Lw T L))
                  (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L))) +
          (Lw T L : ℝ) *
            ((arrayMeasure N).real
                (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((T * L : ℕ) : ℝ) + 1) *
                Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                  (16 * ((T * L : ℕ) : ℝ) *
                    (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))) := by
  obtain ⟨c, hc, L₁, hL₁⟩ :=
    exists_lsBad_rate_single_window (N := N) hp1 hp2 (m := m) hm hC1 hCM T
  refine ⟨c, hc, max L₁ 1, ?_⟩
  intro L hL r s0 hr
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  exact LocOccSingleWindow.measureReal_recordCarrier_singleWindow_le (N := N) hp1 hp2
    (m := m) (i := i) (j := j) (C := C) hL1 hT (r := r) (s0 := s0) hr
    (V := xOf (Lw T L)) (RecCarrierPaper.one_le_xOf_Lw T L) hc.le
    (hL₁ L (le_trans (le_max_left _ _) hL) hr)

/-- **The raw three-mass bound at the canonical `C = |Mb| + 1`.**

Same masses as `measureReal_recordCarrier_singleWindow_le_paper`; both the constant and the rate
are now fixed by `p, m`.  The `LsBad` charge and underlying `harmDefect` event do not depend
on the anchor `s0`.  The carrier mass and the intersection with that defect event still do depend
on `s0`, as the statement shows.  A countable-fibre summation must charge the fixed underlying bad
events once and sum the carrier-weighted terms over the disjoint fibres; the raw RHS itself is not
s0-free. -/
theorem measureReal_recordCarrier_singleWindow_le_paper_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0)ᶜ) ≤
        2 * Real.exp (-c * xOf (Lw T L)) +
          ((arrayMeasure N).real
                (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((T * L : ℕ) : ℝ) + 1) *
                Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
                  (4 * ((T * L : ℕ) : ℝ) *
                    (QplPredEnv.envB p m (xOf (Lw T L))
                      (QplWindow.envC p m (xOf (Lw T L)))) ^ 2))) +
            (arrayMeasure N).real
              (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                QplWindow.harmDefect p m j (xOf (Lw T L))
                  (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L))) +
          (Lw T L : ℝ) *
            ((arrayMeasure N).real
                (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((T * L : ℕ) : ℝ) + 1) *
                Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                  (16 * ((T * L : ℕ) : ℝ) *
                    (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))) :=
  measureReal_recordCarrier_singleWindow_le_paper (N := N) hp1 hp2 hm
    (i := i) (j := j) (C := Ccan p m) (one_le_Ccan p m) (Mb_lt_Ccan p m) hT

/-! ### 4. The normalized single-window bound: no free rate, canonical constant -/

/-- **The paper-shaped single-window bound, with the rate supplied by the `(locsum)` machinery.**

`LocOccSingleWindow.exists_singleWindow_complement_paper` composed with
`exists_lsBad_rate_single_window`: no `hLsBad` hypothesis remains.  `C` is still a parameter, with
exactly the hypotheses `array_locsum_h_start` needs (`C >= 1`, `C > Mb`). -/
theorem exists_singleWindow_complement_paper_of_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
          C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  obtain ⟨c, hc, L₁, hL₁⟩ :=
    exists_lsBad_rate_single_window (N := N) hp1 hp2 (m := m) hm hC1 hCM T
  obtain ⟨c_T, hc_T, C_T, hC_T, L₂, hL₂⟩ :=
    LocOccSingleWindow.exists_singleWindow_complement_paper (N := N) hp1 hp2 hm (i := i) (j := j)
      (C := C) (c := c) hC1 hc hT
  refine ⟨c_T, hc_T, C_T, hC_T, max L₁ L₂, ?_⟩
  intro L hL r s0 hr
  exact hL₂ L (le_trans (le_max_right _ _) hL) hr (hL₁ L (le_trans (le_max_left _ _) hL) hr)

/-- **Canonical form: `C = |Mb| + 1`.**

The inputs left are the paper's own: `1/2 < p < 1`, `2 <= m`, `i ≠ j`, `T >= 1`, `L` large, and
the original range `(T+3) L <= r`.  In particular: no rate hypothesis, no `C` parameter, no
`(T+4)L` range, and no carrier-mass hypothesis. -/
theorem exists_singleWindow_complement_paper_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              (LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0)ᶜ) ≤
          C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) :=
  exists_singleWindow_complement_paper_of_paper (N := N) hp1 hp2 hm hij
    (C := Ccan p m) (one_le_Ccan p m) (Mb_lt_Ccan p m) hT

/-! ### 5. The display at the fixed ordered pair, with no `(locsum)` hypothesis -/

/-- **The paper's `(lococc)` on the record carrier, single window, no `(locsum)` hypothesis.**

`LocOccSingleWindow.lococc_recordCarrier_TL_of_singleWindow` carries the `(locsum)` input
`hLsum : ∀ U, U ∉ LsBad → ∀ a b, ...` as a hypothesis.  That is not an extra hypothesis of the
model: the second conjunct of `LocSumR1.array_locsum_h_start` states it verbatim for every walker
`j : Fin N` and every subinterval of `[A0, A0+Lw)`, so it can be discharged — here it is.

The conclusion is the paper's collapsed form at the *fixed ordered pair* `(i,j)`: on the carrier,
inside `GoodWin`, for every `s0 <= t <= s0 + T*L`,

  `sum_{u in [s0,t)} 1{(X^i_u) <= (M^j_u)}`
      `<= (2C+Lc+2 CJ (2C)+1) (T L + 3 L) + (t-s0)/8 + K L^{3/4}`

with `C = |Mb| + 1` and `K = 2C+1+2KF+4 CJ (2C)+5+4/(1-aRec)`.

Residual: a statement about one ordered pair and the record anchor `s0` only; nothing is summed
over the record levels `s0`, and no intersection over pairs is taken. -/
theorem ae_lococc_recordCarrier_singleWindow_TL_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {T : ℕ} (hT : 1 ≤ T) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 t : ℕ}, (T + 3) * L ≤ r → s0 ≤ t → t ≤ s0 + T * L →
      ∀ᵐ U ∂(arrayMeasure N),
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
        U ∈ LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0 →
        ∑ u ∈ Finset.Ico s0 t,
            (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
          ≤ ((2 * Ccan p m + Lc p m) + 2 * CJc p m * (2 * Ccan p m) + 1) *
              ((((T * L : ℕ)) : ℝ) + 3 * (L : ℝ))
            + ((t : ℝ) - (s0 : ℝ)) / 8
            + (2 * Ccan p m + 1 + 2 * KFc p m + 4 * CJc p m * (2 * Ccan p m) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  have hC1 : (1 : ℝ) ≤ Ccan p m := one_le_Ccan p m
  have hCM : LocSum.Mb p (LocSumAct.qOf p m) < Ccan p m := Mb_lt_Ccan p m
  obtain ⟨c₂, -, L₂, hL₂⟩ := LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  obtain ⟨L₃, hL₃⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le (T := T)
  refine ⟨max (max L₂ L₃) 1, ?_⟩
  intro L hL r s0 t hr hst htT
  have hL2 : L₂ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL)
  have hL3 : L₃ ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hL)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLw : L₂ ≤ Lw T L := le_trans hL2 (le_Lw T L)
  have hbig : 2 * ellT (xOf (Lw T L)) ≤ A0 r T L := hbig_of_le_L hr (hL₃ L hL3)
  have hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m (Ccan p m) (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * Ccan p m * ((b : ℝ) - (a : ℝ)) +
            6 * Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ) :=
    fun U hU a b ha hb hab => (hL₂ (Lw T L) hLw (A0 r T L) hbig).2 U hU j a b ha hb hab
  exact LocOccSingleWindow.lococc_recordCarrier_TL_of_singleWindow (N := N) hp1 hp2 hm hij
    (C := Ccan p m) hC1 hL1 hT (r := r) (s0 := s0) (t := t) hr hst htT hLsum

/-! ### 6. The good event carries almost all of the carrier mass -/

/-- **Lower bound for the carrier ∩ good event.**

The complement bound `exists_singleWindow_complement_paper_canonical` says the display fails on the
carrier with mass at most `C_T exp (-c_T L^{1/16})`; hence, on the same carrier and at the same
original range, the display holds on a set of mass at least `carrier mass - C_T exp (-c_T
L^{1/16})`.  No measurability of `GoodWin` is needed: the decomposition
`carrier = (carrier ∩ Good) ∪ (carrier ∩ Goodᶜ)` is set algebra and `measureReal_union_le` is
subadditivity of a measure.  The carrier mass itself is *not* claimed to be `1`. -/
theorem measureReal_carrier_inter_goodWin_ge_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) -
          C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) ≤
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hL₀⟩ :=
    exists_singleWindow_complement_paper_canonical (N := N) hp1 hp2 hm hij hT
  refine ⟨c_T, hc_T, C_T, hC_T, L₀, ?_⟩
  intro L hL r s0 hr
  have hbad := hL₀ L hL (r := r) (s0 := s0) hr
  have hsplit : (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0) ∪
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0)ᶜ)
      = ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L := by
    ext U
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hsub := measureReal_union_le (μ := arrayMeasure N)
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0)
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      (LocOccSingleWindow.GoodWin p m i j (Ccan p m) r T L s0)ᶜ)
  rw [hsplit] at hsub
  linarith

end LocOccSiteRate
