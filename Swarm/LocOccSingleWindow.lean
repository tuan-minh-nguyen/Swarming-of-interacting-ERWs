/-
  # fidelity and hypothesis minimality of the compiled local-good event

  The paper's Proposition `local` states `(lococc)` for *all* integers
  `tau_r <= s <= t <= tau_r + floor (T L)` — a single window of length `T L` starting at the
  record time, for both endpoints.  The compiled `LocOccAllStarts.GoodAllStarts` instead excludes
  the adapted `Qpl` drop over the **doubled** window `[s0, s0 + 2 T L]`, because its core
  re-derives the display with the drop exclusion anchored at the *display* start `s`, whose window
  `[s, s + T L]` can stick out of `[s0, s0 + T L]` by another `T L`.

  This file proves that this doubling is not necessary: the display at every pair `(s,t)` of the
  paper's window only needs `Q_t - Q_s`, i.e. the *pair* range, and the paper's own single window
  `[s0, s0 + T L]` covers every such pair.  `lococc_core_singleWindow` is
  `LocOccAllStarts.lococc_recordCarrier_core_laterStart` with the drop exclusion re-anchored at
  `s0` over `T * L`; the proof is the same (the only use of the `Qpl` hypothesis is the single
  pair bound `-(Q_t - Q_s) <= 2 L34`), so nothing else in the display changes.

  Consequence used below: at the single window the geometric `Qpl` residual
  `ShiftedQplResidual.shiftedContDefect` is *provably empty* on the carrier
  (`CarrierQplResidual.carrier_inter_shiftedContDefect_eq_empty`, which needs `n <= T * L`),
  whereas at the doubled window the residual term remains in the bound: the zero-mass lemma just
  cited requires the condition `n <= T * L`, which the doubled window does not satisfy. This file
  proves no residual-nonemptiness statement and no non-vacuity witness for the new good event.  So the doubling is not
  a harmless constant loss: it costs a residual mass that the paper's statement does not have.
-/
import Swarm.LocOccAllStarts
import Swarm.CarrierQplResidual
import Swarm.LocOccAllPairs
import Swarm.RecordCarrierPaperScale

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccSingleWindow

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The pair form of the `Qpl` drop exclusion -/

/-- **A drop is a *pair* event.**  `qplDrop Q sigma n delta` is unfolded: it is exactly the set of
points where some pair `sigma <= a <= b <= sigma + n` rises by more than `delta`. -/
theorem mem_qplDrop_iff {Q : ℕ → Array N → ℝ} {σ n : ℕ} {δ : ℝ} {U : Array N} :
    U ∈ LocOccQ.qplDrop Q σ n δ ↔
      ∃ a b : ℕ, σ ≤ a ∧ a ≤ b ∧ b ≤ σ + n ∧ δ < Q a U - Q b U := Iff.rfl

/-- **The single `hQ` field, isolated.**  Off the drop set the one-sided pair bound
`Q a - Q b <= delta` (the decrease of `Qpl`, which is what the display consumes) holds for every
pair of the window. -/
theorem notMem_qplDrop_pair {Q : ℕ → Array N → ℝ} {σ n : ℕ} {δ : ℝ} {U : Array N}
    (h : U ∉ LocOccQ.qplDrop Q σ n δ) :
    ∀ a b : ℕ, σ ≤ a → a ≤ b → b ≤ σ + n → Q a U - Q b U ≤ δ := by
  intro a b h1 h2 h3
  have h' := LocOccQ.notMem_qplDrop h h1 h2 h3
  linarith

/-- **One window covers every pair of the paper's time range.**

The paper's range is `tau_r <= s <= t <= tau_r + floor (T L)`; both endpoints move inside the
*same* window `[s0, s0 + T L]`.  Hence the record-anchored drop exclusion over `T L` (and not
`2 T L`) already gives the `hQ` field at every display pair. -/
theorem notMem_qplDrop_window_pair {Q : ℕ → Array N → ℝ} {s0 n : ℕ} {δ : ℝ} {U : Array N}
    (h : U ∉ LocOccQ.qplDrop Q s0 n δ) :
    ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + n → Q s U - Q t U ≤ δ := by
  intro s t h1 h2 h3
  exact notMem_qplDrop_pair h s t h1 h2 h3

/-- A drop over a shorter window is a drop over any longer window at the same anchor. -/
theorem qplDrop_mono_len {Q : ℕ → Array N → ℝ} {σ n n' : ℕ} {δ : ℝ} (h : n ≤ n') :
    LocOccQ.qplDrop Q σ n δ ⊆ LocOccQ.qplDrop Q σ n' δ := by
  rintro U ⟨a, b, ha, hb, hc, hdev⟩
  exact ⟨a, b, ha, hb, by omega, hdev⟩

/-- The doubled window contains the display-anchored window: this is the only place where the
factor `2` of `LocOccAllStarts.GoodAllStarts` enters.  Recorded here so that the cost of the
doubling is visible; Section 2 removes it. -/
theorem qplDrop_laterStart_subset' {Q : ℕ → Array N → ℝ} {s0 s n : ℕ} {δ : ℝ}
    (h1 : s0 ≤ s) (h2 : s ≤ s0 + n) :
    LocOccQ.qplDrop Q s n δ ⊆ LocOccQ.qplDrop Q s0 (2 * n) δ :=
  LocOccAllStarts.qplDrop_laterStart_subset h1 h2

/-! ### 2. The display at every start, from the *paper* window -/

/-- `LocOccAllStarts.lococc_recordCarrier_core_laterStart` with the `Qpl` drop exclusion anchored
at the record time `s0` over the paper's single window `T * L` instead of at the display start `s`
over `T * L` (the compiled all-starts version then doubles the window to `2 * T * L` to cover the
`s`-anchored one).  Same conclusion, with the shorter hypothesis on the dropped window. -/
theorem lococc_core_singleWindow
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hs0s : s0 ≤ s) (hst : s ≤ t) (htT : t ≤ s0 + T * L) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      -- `(locsum)` on the window `[A0, A0+Lw)`
      (∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) →
      -- `(locmax)` on `[A0-1, A0+Lw)`: the left boundary site `A0-1` is what bounds `b_n`
      (∀ y ∈ Finset.Ico (A0 r T L - 1) (A0 r T L + Lw T L),
        hof p (siteMarks p m U j) y ≤ xOf (Lw T L)) →
      -- the one-sided adapted projected `Qpl` window
      U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L) (2 * L34 L (Lw T L)) →
      -- the projected oscillation pair at the carrier's start site
      OscPair p m i j s t L U →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hA1 : 1 ≤ A0 r T L := one_le_A0 hL hr
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (N := N) (p := p) hp1 hp2
      (by linarith : p ≠ 0) m t j,
    ae_forall_projH_closed_form (N := N) (p := p) hp1 hp2 m (n := t) j,
    eRec_zero_bounds_ae (N := N) (p := p) hp1 hp2 m (n := t) j,
    LocOcc.ae_step_ledger_actual (N := N) hp1 hp2 hm hij (ε := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) s i j
      (eps := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) t i j
      (eps := 1 / 8) (by norm_num)]
    with U hbelow hcl hbnd hledger hbrS hbrT
  intro hU hlsq hloc hqpl hoscPair
  -- ### the cell fields, from adapted record-carrier membership
  have hcell : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + T * L →
      (A0 r T L : ℤ) ≤ (trajectory p m U u).pos i ∧
      (trajectory p m U u).pos i < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
      (A0 r T L : ℤ) ≤ runMax p m U j u ∧
      runMax p m U j u < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
      (A0 r T L : ℤ) ≤ runMax p m U i u ∧
      runMax p m U i u + 1 ≤ (A0 r T L : ℤ) + (Lw T L : ℤ) :=
    fun u h1 h2 => carrier_cell_window hU hr i j h1 h2
  have hA0nn : (0 : ℤ) ≤ (A0 r T L : ℤ) := by
    have : (1 : ℤ) ≤ (A0 r T L : ℤ) := by exact_mod_cast hA1
    linarith
  have hcellX : ∀ u : ℕ, s ≤ u → u ≤ t →
      A0 r T L ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨h1', h2', -, -, -, -⟩ := hcell u (by omega) (by omega)
    have hcastu : ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) = (trajectory p m U u).pos i :=
      Int.toNat_of_nonneg (by linarith)
    have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
      push_cast; ring
    constructor
    · have h' : (A0 r T L : ℤ) ≤ ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) := by
        rw [hcastu]; exact h1'
      exact_mod_cast h'
    · have h'' : ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ)
          < (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
        rw [hcast2, hcastu]; exact h2'
      exact_mod_cast h''
  have hcellMj : ∀ u : ℕ, s ≤ u → u ≤ t →
      A0 r T L ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨-, -, h1', h2', -, -⟩ := hcell u (by omega) (by omega)
    have hcastu : ((((runMax p m U j u).toNat : ℕ) : ℤ) = runMax p m U j u) :=
      Int.toNat_of_nonneg (zero_le_runMax p m U j u)
    have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
      push_cast; ring
    constructor
    · have h' : (A0 r T L : ℤ) ≤ ((((runMax p m U j u).toNat : ℕ) : ℤ)) := by
        rw [hcastu]; exact h1'
      exact_mod_cast h'
    · have h'' : ((((runMax p m U j u).toNat : ℕ) : ℤ))
          < (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
        rw [hcast2, hcastu]; exact h2'
      exact_mod_cast h''
  have hcellMi : A0 r T L ≤ (runMax p m U i t).toNat ∧
      (runMax p m U i t).toNat + 1 ≤ A0 r T L + Lw T L := by
    obtain ⟨-, -, -, -, h1', h2'⟩ := hcell t (by omega) (by omega)
    have hcastu : ((((runMax p m U i t).toNat : ℕ) : ℤ) = runMax p m U i t) :=
      Int.toNat_of_nonneg (zero_le_runMax p m U i t)
    have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
      push_cast; ring
    constructor
    · have h' : (A0 r T L : ℤ) ≤ ((((runMax p m U i t).toNat : ℕ) : ℤ)) := by
        rw [hcastu]; exact h1'
      exact_mod_cast h'
    · have h4 : ((((runMax p m U i t).toNat + 1 : ℕ)) : ℤ) ≤
          (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
        rw [hcast2]
        push_cast
        rw [hcastu]
        exact h2'
      exact_mod_cast h4
  -- ### nonnegativity and casts on the window
  have hnonneg : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    have hc := (hcell u (by omega) (by omega)).1
    linarith
  have hnonneg' : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i :=
    fun u h1 h2 => hnonneg u h1 (by omega)
  have hcast : ∀ u : ℕ, s ≤ u → u ≤ t →
      ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) = (trajectory p m U u).pos i :=
    fun u h1 h2 => Int.toNat_of_nonneg (hnonneg u h1 h2)
  have hrecCast : (((runMax p m U j t).toNat : ℕ) : ℤ) = recVal j (prefOf p m t U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j t)
  -- ### the summed above-record slope fields, from the closed form
  have he1 : 0 ≤ eRec p m t j 0 U := le_trans zero_le_one hbnd.1
  have hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ)
        = hof p (siteMarks p m U j) x := by
    intro x hx
    have hx' : (x : ℤ) < recVal j (prefOf p m t U) := by
      rw [← hrecCast]
      exact_mod_cast hx
    have h := SummedSlope.Model.projH_step_below_eq (p := p) (m := m) hp1 hp2 (t := t) (U := U) hbelow hx'
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hslopeHi0 : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ) := by
    intro x hx
    set g := x - (runMax p m U j t).toNat with hg
    have hxe : (runMax p m U j t).toNat + g = x := by omega
    have h1 : ((x : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g : ℤ) := by
      conv_lhs => rw [← hxe]
      push_cast
      rw [hrecCast]
    have h2 : ((x + 1 : ℕ) : ℤ) = recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ) := by
      push_cast
      rw [h1]
      ring
    rw [h2, h1]
    exact SummedSlope.Model.projH_step_above_nonneg (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 g
  have hsumHi : ∀ u w : ℕ, (runMax p m U j t).toNat ≤ u → u ≤ w →
      projH p m j t U ((w : ℕ) : ℤ) - projH p m j t U ((u : ℕ) : ℤ)
        ≤ Lc p m * ((w : ℝ) - (u : ℝ)) + bRec p m t j U / (1 - aRec p m) := by
    intro u w hu huw
    set g1 := u - (runMax p m U j t).toNat with hg1
    set g2 := w - (runMax p m U j t).toNat with hg2
    have hue : (runMax p m U j t).toNat + g1 = u := by omega
    have hwe : (runMax p m U j t).toNat + g2 = w := by omega
    have hg12 : g1 ≤ g2 := by omega
    have h1 : ((u : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g1 : ℤ) := by
      conv_lhs => rw [← hue]
      push_cast
      rw [hrecCast]
    have h2 : ((w : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g2 : ℤ) := by
      conv_lhs => rw [← hwe]
      push_cast
      rw [hrecCast]
    have hR : ((w : ℝ) - (u : ℝ)) = ((g2 : ℝ) - (g1 : ℝ)) := by
      conv_lhs => rw [← hwe, ← hue]
      push_cast
      ring
    have hmain := SummedSlope.Model.projH_sum_above_le (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 hg12
    have hdef : eRec p m t j 0 U / (1 - aRec p m) ≤ bRec p m t j U / (1 - aRec p m) :=
      div_le_div_of_nonneg_right hbnd.2 (le_of_lt (one_sub_aRec_pos hp1 hp2 m))
    rw [hR, h1, h2]
    linarith [hmain, hdef]
  -- ### the additive defect from `b_n` and the `(locmax)` cap
  have hbrec : bRec p m t j U ≤ xOf (Lw T L) + 2 := by
    refine SummedSlope.Model.bRec_le_succ_cap (p := p) (m := m) hp1 hp2 (j := j) (t := t) (U := U)
      (A := A0 r T L) (Mv := Lw T L) (V := xOf (Lw T L)) hA1 ?_ ?_ hloc
    · rw [xOf]
      exact Real.one_le_rpow (by exact_mod_cast hLw1) (by norm_num)
    · rw [← runMax_eq_recVal]
      exact hcellMj t hst le_rfl
  have hCaddL : bRec p m t j U / (1 - aRec p m)
      ≤ (4 / (1 - aRec p m)) * L34 L (Lw T L) :=
    SummedSlope.Model.bRec_div_le_L34 (p := p) (m := m) (L := L) (Lw := Lw T L) hp1 hp2 hLw1 hbrec
  have hCa : (0 : ℝ) ≤ bRec p m t j U / (1 - aRec p m) := by
    have hden : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
    have h3 : (0 : ℝ) < bRec p m t j U := by linarith [Swarming.Enl.three_le_bRec hp1 hp2 m t j U]
    positivity
  -- ### the remaining fields
  have hCJ0 : (0 : ℝ) ≤ CJc p m := CJc_nonneg hp1 hp2 m
  have hKF0 : (0 : ℝ) ≤ KFc p m := KFc_nonneg hp1 hp2 m
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hoccP : ∀ u : ℕ, s ≤ u → u < t →
      SwarmOcc.occInd (fun r => (trajectory p m U r).pos i) (fun r => runMax p m U j r) u
        = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
    fun u h1 h2 => LocOccEnd.occInd_eq_toNat_toNat (p := p) m U (hnonneg' u h1 (le_of_lt h2))
  have hcap : ∀ u : ℕ, s ≤ u → u ≤ t →
      (hof p (siteMarks p m U j) ((runMax p m U j u).toNat)) ^ 2 ≤ (xOf (Lw T L)) ^ 2 := by
    intro u h1 h2
    have hm := hcellMj u h1 h2
    have hloc' : ∀ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
        hof p (siteMarks p m U j) y ≤ xOf (Lw T L) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
      exact hloc y (Finset.mem_Ico.mpr ⟨by omega, hy2⟩)
    exact hof_sq_record_le (N := N) hp1 hp2 (m := m) (U := U) (j := j) u
      (A := A0 r T L) (Mv := Lw T L) (V := xOf (Lw T L)) (Real.rpow_nonneg (by positivity) _) hloc'
      (Finset.mem_Ico.mpr ⟨hm.1, hm.2⟩)
  -- ### the two endpoint decompositions
  have hZs : Zproj p m (1 / 8) i j s U
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s) := by
    rw [← hbrS]
    show Swarming.Enl.Zproj p m (1 / 8) i j U s
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s)
    rw [hcast s le_rfl (by omega)]
    rfl
  have hZt : Zproj p m (1 / 8) i j t U
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    rw [← hbrT]
    show Swarming.Enl.Zproj p m (1 / 8) i j U t
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t)
    rw [hcast t hst le_rfl]
    rfl
  -- ### the summed `(lococc)` bound on the `occInd` carrier
  have hcore : ∑ u ∈ Finset.Ico s t,
        SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u
      ≤ (2 * C + Lc p m + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + 1 / 8 * ((t : ℝ) - (s : ℝ))
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) :=
    SummedSlope.lococc_summed
      (X := fun u => ((trajectory p m U u).pos i).toNat)
      (Mi := fun u => (runMax p m U i u).toNat)
      (Mj := fun u => (runMax p m U j u).toNat)
      (occ := fun u => SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
        (fun r => runMax p m U j r) u)
      (J := fun u => Jcorr p m (1 / 8) i j U u)
      (Z := fun u => Zproj p m (1 / 8) i j u U)
      (Q := fun u => Qpl p m (1 / 8) i j u U)
      (H := fun t y => projH p m j t U (y : ℤ))
      (Fs := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s))
      (Ft := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t))
      (h := fun x => hof p (siteMarks p m U j) x)
      (wt := fun x => (hof p (siteMarks p m U j) x) ^ 2)
      (A := A0 r T L) (Lw := Lw T L) (K := 2 * C) (β := 3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
      (Kp := Lc p m) (CH := 1) (KQ := 2) (KF := KFc p m) (CJ := CJc p m)
      (ε := 1 / 8) (L34 := L34 L (Lw T L)) (Cadd := bRec p m t j U / (1 - aRec p m))
      (CaddK := 4 / (1 - aRec p m))
      hst hoccP hledger hZs hZt
      (fun x => LocOccEnd.hof_nonneg hp1 hp2 (siteMarks p m U j) x)
      (fun x => le_refl ((hof p (siteMarks p m U j) x) ^ 2))
      hslopeLo hslopeHi0 hsumHi
      (locsum_hint_wt (p := p) (m := m) (U := U) (j := j) (A := A0 r T L) (Lw := Lw T L)
        (C := C) (β := ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) hC0 hlsq)
      (by
        have h1 : projH p m j t U (((trajectory p m U s).pos i).toNat)
            - projH p m j s U (((trajectory p m U s).pos i).toNat) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by
          rw [hcast s le_rfl (by omega)]
          exact hoscPair
        have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
        have h4 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L (Lw T L) := L34_lower_rpow L (Lw T L)
        linarith)
      (by
        have h := LocOccQ.notMem_qplDrop (Q := fun n (V : Array N) => ProjLedger.Qpl p m (1 / 8) i j n V)
          hqpl hs0s hst htT
        simpa using h)
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U s
        (hcap s le_rfl (by omega)))
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U t
        (hcap t hst le_rfl))
      (fun nx => Jstruct_all (N := N) hp1 hp2 (m := m) (i := i) (j := j) U nx)
      (fun nx => runMax_toNat_mono (le_of_lt (Nat.lt_succ_self nx)))
      (fun nx => runMax_toNat_step nx)
      (fun nx h1 h2 =>
        calc ((trajectory p m U (nx + 1)).pos i).toNat
            ≤ (runMax p m U i (nx + 1)).toNat :=
              pos_toNat_le_runMax (hnonneg' (nx + 1) (by omega) (by omega))
          _ ≤ (runMax p m U i t).toNat := runMax_toNat_mono (by omega))
      (runMax_toNat_mono hst)
      (pos_toNat_le_runMax (hnonneg' s (le_refl s) hst))
      (pos_toNat_le_runMax (hnonneg' t hst (le_refl t)))
      (hcellX s le_rfl (by omega)).1
      (hcellMj s le_rfl (by omega)).1
      (le_of_lt (hcellX t hst le_rfl).2)
      hcellMi.2
      (le_of_lt (hcellMj t hst le_rfl).2)
      (by linarith) (by positivity) (Lc_nonneg hp1 hp2 m) hCJ0 (by norm_num) hKF0 (by norm_num)
      (L34_nonneg L (Lw T L)) (one_le_L34 hL) (three_betaT_le_L34 L (Lw T L)) hCa hCaddL
  -- ### back to the paper's literal indicator `1{X_u^i <= M_u^j}`
  have hsum : (∑ u ∈ Finset.Ico s t,
        (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0))
      = ∑ u ∈ Finset.Ico s t,
          SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
            (fun r => runMax p m U j r) u := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hu
    have hnn := hnonneg' u h1 (le_of_lt h2)
    have hiff := LocOccEnd.toNat_le_toNat_iff hnn (zero_le_runMax p m U j u)
    by_cases h : ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat
    · have hA1 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 1 :=
        if_pos (hiff.mp h)
      have hB1 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 1 := by rw [hoccP u h1 h2, if_pos h]
      rw [hA1, hB1]
    · have hA0 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 0 :=
        if_neg (fun hc => h (hiff.mpr hc))
      have hB0 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 0 := by rw [hoccP u h1 h2, if_neg h]
      rw [hA0, hB0]
  rw [hsum]
  have hcoef : (1 / 8 : ℝ) * ((t : ℝ) - (s : ℝ)) = ((t : ℝ) - (s : ℝ)) / 8 := by ring
  rw [hcoef] at hcore
  exact hcore

/-! ### 3. The paper's event with the paper's window -/

/-- **The paper's `(lococc)` good event, on the paper's own window.**  `(locsum)`/`(locmax)` via
`LocSumR1.LsBad`, the adapted `Qpl` drop exclusion over the single window `[s0, s0 + T L]`, and the
start-independent projected oscillation sup.  Compared with `LocOccAllStarts.GoodAllStarts` the
`Qpl` window is `T L` instead of `2 T L`; by `notMem_qplDrop_window_pair` the single window already
covers `Q_s - Q_t` for every display pair `s0 <= s <= t <= s0 + T L`. -/
def GoodWin (p : ℝ) (m : ℕ) {N : ℕ} (i j : Fin N) (C : ℝ) (r T L s0 : ℕ) : Set (Array N) :=
  {U | U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
    U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L) (2 * L34 L (Lw T L)) ∧
    U ∉ OscSup p m j r T L s0}

theorem goodWin_iff {p : ℝ} {m : ℕ} {i j : Fin N} {C : ℝ} {r T L s0 : ℕ}
    {U : Array N} :
    U ∈ GoodWin p m i j C r T L s0 ↔
      (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
        U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
          (2 * L34 L (Lw T L)) ∧
        U ∉ OscSup p m j r T L s0) := Iff.rfl

/-- **The compiled doubled-window event implies the single-window event.**

`GoodAllStarts` excludes the `Qpl` drop over `[s0, s0 + 2 T L]`; `GoodWin` only over the paper's
`[s0, s0 + T L]`.  Since a drop over the shorter window is a drop over the longer one, excluding the
longer-window drops gives the shorter-window exclusion, i.e. `GoodAllStarts ⊆ GoodWin`.  The single-
window good event is therefore *larger*, and its complement bound is the stronger statement; the
The reverse inclusion and non-vacuity of either event are not proved by this theorem. The route was
registered as a strictness/non-vacuity direction, but this declaration is only the displayed inclusion. -/
theorem goodAllStarts_subset_goodWin {p : ℝ} {m : ℕ} {i j : Fin N} {C : ℝ}
    {r T L s0 : ℕ} :
    GoodAllStarts p m i j C r T L s0 ⊆ GoodWin p m i j C r T L s0 := by
  rintro U ⟨hls, hq, hosc⟩
  refine ⟨hls, ?_, hosc⟩
  intro hmem
  exact hq (qplDrop_mono_len (Q := ProjLedger.Qpl p m (1 / 8) i j) (σ := s0) (n := T * L)
    (n' := 2 * (T * L)) (δ := 2 * L34 L (Lw T L))
    (Nat.le_mul_of_pos_left (T * L) (by norm_num : 0 < 2)) hmem)

/-- **The paper's `(lococc)` at every start of the window, on the paper's single-window event.**

Same conclusion as `LocOccAllStarts.lococc_recordCarrier_allStarts` (the record-dependent
right-hand side at the *display* start `s`, with `C` independent of `T`), from the drop exclusion
over the paper's window `[tau_r, tau_r + T L]` only. -/
theorem lococc_recordCarrier_allStarts_singleWindow
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ} (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ,
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodWin p m i j C r T L s0 →
      s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
          ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
              ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
                + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
                + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
            + ((t : ℝ) - (s : ℝ)) / 8
            + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro t
  by_cases hrange : s0 ≤ s ∧ s ≤ t ∧ t ≤ s0 + T * L
  · obtain ⟨h1, h2, h3⟩ := hrange
    filter_upwards [lococc_core_singleWindow (N := N) hp1 hp2 hm hij hC1
      (L := L) (T := T) (r := r) (s0 := s0) (s := s) (t := t) hL hT hr h1 h2 h3]
      with U hcore
    intro hU hgood hs' hst' htb'
    obtain ⟨hls, hqpl, hosc⟩ := (goodWin_iff).1 hgood
    exact hcore hU (hLsum U hls)
      (hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s0) (C := C) (T := T) (L := L)
        j hL hls) hqpl
      (notMem_OscSup_imp_OscPair (p := p) (m := m) (r := r) (s0 := s0) (L := L) (T := T)
        (i := i) (j := j) hU hr hosc hs' hst' htb')
  · filter_upwards with U hU hgood h1 h2 h3
    exact absurd ⟨h1, h2, h3⟩ hrange

/-- The record-start specialization: the paper's collapsed `T L + 3 L` bound, from `GoodWin`. -/
theorem lococc_recordCarrier_TL_of_singleWindow
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s0 ≤ t) (htT : t ≤ s0 + T * L)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodWin p m i j C r T L s0 →
      ∑ u ∈ Finset.Ico s0 t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s0 : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  filter_upwards [lococc_recordCarrier_allStarts_singleWindow (N := N) hp1 hp2 hm hij hC1 hL hT
    (r := r) (s0 := s0) hr hLsum] with U hall
  intro hU hgood
  have h1 := hall s0 t hU hgood (le_refl s0) hst htT
  have h2 := record_geometry hU hr i j hst htT
  have hcoef : (0 : ℝ) ≤ (2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1 := by
    have := Lc_nonneg hp1 hp2 m
    have := CJc_nonneg hp1 hp2 m
    have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
    nlinarith
  have h3 : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
      ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s0).toNat : ℝ))
        + (((runMax p m U i s0).toNat : ℝ) - (((trajectory p m U s0).pos i).toNat : ℝ))
        + max 0 (((runMax p m U i s0).toNat : ℝ) - ((runMax p m U j s0).toNat : ℝ)))
      ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hcoef
  linarith

/-! ### 4. The complement, with the geometric `Qpl` residual *proved empty* -/

/-- **The bad set of the single-window display is the paper's three masses.**

`GoodWin` fails on the carrier only if `(locsum)`/`(locmax)` fails (`LsBad`), if the adapted `Qpl`
drops over the paper's window, or if the projected oscillation sup fires. -/
theorem carrier_fail_subset_singleWindow {p : ℝ} {m r s0 L T : ℕ} {C : ℝ} {i j : Fin N} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWin p m i j C r T L s0)ᶜ ⊆
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ∪
        ((ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
              (2 * L34 L (Lw T L))) ∪
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            OscSup p m j r T L s0)) := by
  rintro U ⟨hU, hbad⟩
  by_cases hLsBad : U ∈ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)
  · exact Or.inl ⟨hU, hLsBad⟩
  by_cases hQ : U ∈ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
      (2 * L34 L (Lw T L))
  · exact Or.inr (Or.inl ⟨hU, hQ⟩)
  by_cases hO : U ∈ OscSup p m j r T L s0
  · exact Or.inr (Or.inr ⟨hU, hO⟩)
  · exact absurd ((goodWin_iff).2 ⟨hLsBad, hQ, hO⟩) hbad

/-- **The complement of the single-window event in the paper's three masses, with the geometric
`Qpl` residual *discharged*.**

Compared with `LocOccAllStarts.measureReal_recordCarrier_allStarts_le` the residual list loses the
whole `shiftedContDefect` mass (two free parameters `w`, `M` disappear with it): at the paper's
single window `n = T L <= T L` that event is *empty* on the carrier
(`CarrierQplResidual.carrier_inter_shiftedContDefect_eq_empty`), while at the doubled window it is
not.  The harmonic residual is retained and is exactly the `(locmax)` defect. -/
theorem measureReal_recordCarrier_singleWindow_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodWin p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
      ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((T * L : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            QplWindow.harmDefect p m j V (CarrierQplResidual.cA r T L)
              (CarrierQplResidual.cM T L))) +
      (Lw T L : ℝ) *
        ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))) := by
  have hTL1 : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hL34pos : 0 < L34 L (Lw T L) := by
    linarith [one_le_L34 (L := L) (Lw := Lw T L) hL]
  have hmono : (T + 2) * L ≤ (T + 3) * L :=
    Nat.mul_le_mul_right L (by omega)
  have hA0 : (T + 2) * L ≤ r := le_trans hmono hr
  have hcross : (T + 3) * L = (T + 2) * L + L := by ring
  have hA1 : 1 ≤ CarrierQplResidual.cA r T L := by
    unfold CarrierQplResidual.cA
    omega
  -- the `Qpl` window: single window, geometric residual proved empty by `CarrierQplResidual`
  have hq := CarrierQplResidual.measureReal_recordCarrier_qplDrop_singleResidual (N := N)
    hp1 hp2 m (1 / 8) i j (by norm_num) (r := r) (s := s0) (T := T) (L := L) (n := T * L)
    hTL1 le_rfl hA0 hA1 hV1 (KQ := 2) (by norm_num) hL34pos
  have hls : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  have hosc := LocOccAllStarts.measureReal_oscSup_le (N := N) hp1 hp2 (m := m) (i := i) (j := j)
    (C := C) hL hT (r := r) (s0 := s0) hr
  have hstep : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWin p m i j C r T L s0)ᶜ)
      ≤ (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) +
        ((arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
                (2 * L34 L (Lw T L))) +
          (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              OscSup p m j r T L s0)) := by
    refine le_trans (measureReal_mono_array carrier_fail_subset_singleWindow
      (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_union_le _ _) ?_
    linarith [measureReal_union_le (μ := arrayMeasure N)
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
          (2 * L34 L (Lw T L)))
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        OscSup p m j r T L s0)]
  linarith [hstep, hls, hq, hosc]

/-! ### 5. Paper scale: `C_T exp (-c_T L^{1/16})` for the single-window event

The whole point of Section 4 is cashed in here.  `RecordCarrierPaperScale` had to carry two free
residual parameters (`w`, `M`) and their `shiftedContDefect` mass; with the paper's single window
that mass is *absent*, so the envelope contains no residual at all beyond the harmonic `(locmax)`
defect, which `CarrierQplResidual` estimates at `exp (-c' xOf Lw)`.

The exponent bookkeeping is the one already verified in `RecordCarrierPaperScale`
(`azuma_exp_arg_ge`, `osc_exp_arg_ge`, `pow_mul_exp_neg_absorb`); only the missing `2` in the
`Qpl` window changes, which *strengthens* the Azuma exponent. -/

theorem exists_singleWindow_complement_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} {C c : ℝ} (hC1 : 1 ≤ C) (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (GoodWin p m i j C r T L s0)ᶜ) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  -- the harmonic rate of `CarrierQplResidual`
  obtain ⟨c', hc', L₀', hb'⟩ :=
    CarrierQplResidual.measureReal_carrier_harmDefect_le_exp (N := N) hp1 hp2 hm T hT
  -- the two envelope constants
  set K1 : ℝ := RecCarrierPaper.Kb p m * (((2 * T + 3 : ℕ)) : ℝ) with hK1def
  set K2 : ℝ := 9 * SiteHMax.Cproj p m * (((2 * T + 3 : ℕ)) : ℝ) with hK2def
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT3pos : (0 : ℝ) < (((2 * T + 3 : ℕ)) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * T + 3 := by omega
    exact_mod_cast this
  have hK1 : 0 < K1 := mul_pos (RecCarrierPaper.Kb_pos (p := p) (m := m) hp1 hp2) hT3pos
  have hK2 : 0 < K2 := by
    have := RecCarrierPaper.Cproj_pos (p := p) (m := m) hp1 hp2
    rw [hK2def]; positivity
  set b : ℝ := min (min c c') (min (1 / (4 * (T : ℝ) * K1 ^ 2)) (1 / (16 * (T : ℝ) * K2 ^ 2)))
    with hbdef
  have hb1 : 0 < 1 / (4 * (T : ℝ) * K1 ^ 2) := by positivity
  have hb2 : 0 < 1 / (16 * (T : ℝ) * K2 ^ 2) := by positivity
  have hbpos : 0 < b := by
    rw [hbdef]
    exact lt_min (lt_min hc hc') (lt_min hb1 hb2)
  have hblec : b ≤ c := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hblec' : b ≤ c' := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hbleK1 : b ≤ 1 / (4 * (T : ℝ) * K1 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hbleK2 : b ≤ 1 / (16 * (T : ℝ) * K2 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  set K3 : ℝ := 3 + 2 * ((T : ℝ) + 1) + 2 * ((T : ℝ) + 1) * (2 * (T : ℝ) + 4) with hK3def
  have hK3 : 0 ≤ K3 := by rw [hK3def]; positivity
  refine ⟨b / 2, by linarith, K3 * (((48).factorial : ℝ) / (b / 2) ^ 48), ?_, max L₀' 1, ?_⟩
  · have hfac : (0 : ℝ) < (((48).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos 48
    have hb2' : (0 : ℝ) < (b / 2) ^ 48 := pow_pos (by linarith) 48
    positivity
  intro L hLbound r s0 hr hLsBad
  have hL : 1 ≤ L := le_trans (le_max_right L₀' 1) hLbound
  have hL₀' : L₀' ≤ L := le_trans (le_max_left L₀' 1) hLbound
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper hT hL hr
  -- the single-window union bound with `V = xOf Lw`
  have hmain := measureReal_recordCarrier_singleWindow_le (N := N) hp1 hp2 (m := m) (i := i)
    (j := j) (C := C) hL hT (r := r) (s0 := s0) hr (V := xOf (Lw T L))
    (RecCarrierPaper.one_le_xOf_Lw T L) hc.le hLsBad
  -- the harmonic residual, at the paper window
  have hharmraw := hb' (r := r) (s := s0) (L := L) (j := j) hL₀' hA1
  have hharmdefeq : QplWindow.harmDefect p m j (xOf (CarrierQplResidual.cLw T L))
      (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L)
      = QplWindow.harmDefect p m j (xOf (Lw T L))
        (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L) := by
    rw [show CarrierQplResidual.cLw T L = Lw T L from rfl]
  rw [hharmdefeq] at hharmraw
  -- abbreviations
  set Lr : ℝ := (L : ℝ) ^ (1 / 16 : ℝ) with hLrdef
  set E : ℝ := QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
    with hEdef
  set B : ℝ := SiteHMax.capB p m (xOf (Lw T L)) with hBdef
  set A : ℝ := (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
    with hAdef
  set harm : ℝ := (arrayMeasure N).real
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      QplWindow.harmDefect p m j (xOf (Lw T L)) (CarrierQplResidual.cA r T L)
        (CarrierQplResidual.cM T L)) with hharmdef
  have hharm : harm ≤ Real.exp (-c' * xOf (Lw T L)) := by
    rw [hharmdef]; exact hharmraw
  have hA0' : 0 ≤ A := by rw [hAdef]; exact measureReal_nonneg
  have hA1' : A ≤ 1 := by rw [hAdef]; exact measureReal_le_one
  have hLr_le : Lr ≤ xOf (Lw T L) := by
    have := RecCarrierPaper.xOf_le_of_le (L := L) (M := Lw T L) (le_Lw (T := T) L)
    simpa [hLrdef, LocSumAct.xOf] using this
  have hLr0 : 0 ≤ Lr := by rw [hLrdef]; positivity
  have hharm2 : Real.exp (-c' * xOf (Lw T L)) ≤ Real.exp (-b * Lr) := by
    have harg : -c' * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c' * Lr := mul_le_mul_of_nonneg_right hblec' hLr0
      have h2 : c' * Lr ≤ c' * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc'.le
      linarith
    exact Real.exp_le_exp.mpr harg
  have hharm' : harm ≤ Real.exp (-b * Lr) := le_trans hharm hharm2
  have hterm1 : 2 * Real.exp (-c * xOf (Lw T L)) ≤ 2 * Real.exp (-b * Lr) := by
    have harg : -c * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c * Lr := mul_le_mul_of_nonneg_right hblec hLr0
      have h2 : c * Lr ≤ c * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc.le
      linarith
    have := Real.exp_le_exp.mpr harg
    linarith
  -- the Azuma exponent
  have hV1x : (1 : ℝ) ≤ xOf (Lw T L) := RecCarrierPaper.one_le_xOf_Lw T L
  have hV0x : (0 : ℝ) ≤ xOf (Lw T L) := by linarith
  have hEpos : 0 < E := by
    rw [hEdef]
    exact QplPredEnv.envB_pos hp1 hp2 m hV0x (QplWindow.envC_nonneg hp1 hp2 m hV0x)
  have hEK : E ≤ K1 * Lr := by
    rw [hEdef, hK1def, hLrdef]
    exact RecCarrierPaper.envB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hTLcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hL34 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L (Lw T L) := L34_lower_rpow L (Lw T L)
  have hAzarg : Lr / (4 * (T : ℝ) * K1 ^ 2) ≤ L34 L (Lw T L) ^ 2 /
      (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
    have h := RecCarrierPaper.azuma_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K1) (E := E)
      (L34 := L34 L (Lw T L)) (by exact_mod_cast hL) hTpos hK1 hEpos hEK hL34
    simpa [hLrdef, hTLcast] using h
  have hAz : Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
        have h2 : b * Lr ≤ Lr / (4 * (T : ℝ) * K1 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK1 hLr0
          calc b * Lr ≤ (1 / (4 * (T : ℝ) * K1 ^ 2)) * Lr := h3
            _ = Lr / (4 * (T : ℝ) * K1 ^ 2) := by ring
        linarith
      have heq : ((2 * L34 L (Lw T L) / 2) ^ 2) = L34 L (Lw T L) ^ 2 := by ring
      have hneg : -(L34 L (Lw T L) ^ 2) / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)
          = -(L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the oscillation exponent
  have hBpos : 0 < B := by
    rw [hBdef]
    exact SiteHMax.capB_pos hp1 hp2 m hV0x
  have hBK : B ≤ K2 * Lr := by
    rw [hBdef, hK2def, hLrdef]
    exact RecCarrierPaper.capB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hOsc : Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
        have h2 : b * Lr ≤ Lr / (16 * (T : ℝ) * K2 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK2 hLr0
          calc b * Lr ≤ (1 / (16 * (T : ℝ) * K2 ^ 2)) * Lr := h3
            _ = Lr / (16 * (T : ℝ) * K2 ^ 2) := by ring
        have h4 := RecCarrierPaper.osc_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K2) (B := B)
          (by exact_mod_cast hL) hTpos hK2 hBpos hBK
        have h4' : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
          rw [hTLcast]
          linarith
        linarith
      have heq : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (L : ℝ) ^ (3 / 2 : ℝ) :=
        RecCarrierPaper.sq_three_quarters (by linarith)
      have hneg : -((L : ℝ) ^ (3 / 2 : ℝ)) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)
          = -((L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the two products with the carrier mass
  have hcoef : (0 : ℝ) ≤ 2 * ((((T * L : ℕ)) : ℝ) + 1) := by positivity
  have hprodA : A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) ≤
      (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hAz (Real.exp_pos _).le (by norm_num)
    calc A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)))
        = (2 * ((((T * L : ℕ)) : ℝ) + 1)) *
            (A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
              (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) := by ring
      _ ≤ (2 * ((((T * L : ℕ)) : ℝ) + 1)) * (1 * Real.exp (-b * Lr)) :=
          mul_le_mul_of_nonneg_left h1 hcoef
      _ = (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by ring
  have hprodO : (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
        Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)))) ≤
      ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
          (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hOsc (Real.exp_pos _).le (by norm_num)
    calc (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
          Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))))
        = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
            (A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
              (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))) := by ring
      _ ≤ ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * (1 * Real.exp (-b * Lr)) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by ring
  have hsum : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWin p m i j C r T L s0)ᶜ) ≤
      (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
          (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    nlinarith [hmain, hterm1, hharm', hprodA, hprodO]
  -- the polynomial prefactor is at most `K3 * L^2`
  have hTL1 : (((T * L : ℕ)) : ℝ) + 1 ≤ ((T : ℝ) + 1) * (L : ℝ) := by
    have h1 : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    rw [h1]; nlinarith
  have hLwle : (Lw T L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
    have h1 : Lw T L ≤ (2 * T + 3) * L := RecCarrierPaper.Lw_le_paper (T := T) hL
    have h1' : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 3) * L : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (((2 * T + 3) * L : ℕ) : ℝ) = (2 * (T : ℝ) + 3) * (L : ℝ) := by push_cast; ring
    have h3 : (2 * (T : ℝ) + 3) * (L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith
      nlinarith
    linarith
  have hpoly : 3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
      (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1)) ≤ K3 * (L : ℝ) ^ 2 := by
    have h2 : 2 * ((((T * L : ℕ)) : ℝ) + 1) ≤ 2 * (((T : ℝ) + 1) * (L : ℝ)) := by linarith
    have h3 : (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))
        ≤ ((2 * (T : ℝ) + 4) * (L : ℝ)) * (2 * (((T : ℝ) + 1) * (L : ℝ))) := by
      apply mul_le_mul hLwle h2
      · positivity
      · positivity
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [hK3def]
    nlinarith
  -- absorb the polynomial into the stretched exponential
  have habs := RecCarrierPaper.pow_mul_exp_neg_absorb hbpos 2 (L := (L : ℝ))
    (by exact_mod_cast hL)
  have hfinal : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
        (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) ≤
      (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by
    have h1 : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
          (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) ≤
        (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    have h2 : (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr)
        = K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) := by ring
    have h3 : K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) ≤
        K3 * ((((16 * (2 + 1)).factorial : ℝ) / (b / 2) ^ (16 * (2 + 1))) *
          Real.exp (-(b / 2) * Lr)) := by
      apply mul_le_mul_of_nonneg_left _ hK3
      simpa [hLrdef] using habs
    have h4 : (16 * (2 + 1)) = 48 := by norm_num
    rw [h4] at h3
    have h5 : K3 * ((((48).factorial : ℝ) / (b / 2) ^ 48) * Real.exp (-(b / 2) * Lr))
        = (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by ring
    linarith [h1, h2, h3, h5]
  linarith [hsum, hfinal]
