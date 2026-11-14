/-
  # `(lococc)` for *every* start time of the paper's window, on one start-independent event

  ## What the compiled package proves, and what the paper asks

  `LocOccCarrierAssembly.lococc_recordCarrier_TL` proves the paper's display

  ```
  sum_{u=s}^{t-1} 1{X^i_u <= M^j_u} <= C (M^i_t - M^i_s + M^i_s - X^i_s + (M^i_s - M^j_s)_+)
                                     + (t-s)/8 + C_T L^{3/4}
  ```

  only at the record time `s = tau_r`, where `recordPrefixBand p m r s L` happens to hold.  The paper
  (`Proposition local`, display `(lococc)`) needs it for *all* integers
  `tau_r <= s <= t <= tau_r + floor(T L)` on one event `G_{r,L,T}`, and the coefficient `C` there
  is the one multiplying the *record-dependent* combination `M_t^i - M_s^i + M_s^i - X_s^i +
  (M_s^i - M_s^j)_+` — the `T L + 3 L` collapse is a specialization valid only at `s = tau_r` with
  `d_r <= L`, because it uses `M_s^i - X_s^i <= L`.

  This module closes exactly that gap.

  ## The three load-bearing points

  1. **Geometry propagates, the display does not re-anchor for free.**  `carrier_cell_window`
     already gives the cell fields at every `s <= u <= s + T L`, so the whole proof of the display
     can be re-run with the display start `s` separated from the record time `s0`.  The generalized
     core `lococc_recordCarrier_core_laterStart` does that and keeps the record-dependent right-hand
     side at the *new* start `s`, with carrier membership still asserted only at `s0`
     (`{tau_r = s0} ∩ {d_r <= L}`).  This is not a monotonicity argument: the occupation prefix
     `[s0, s)` cannot be subtracted from the record-start display, so the proof is genuinely redone.

  2. **The `Qpl` window is already a window event.**  `LocOccQ.qplDrop Q sigma n delta` is
     `exists sigma <= s <= t <= sigma+n, delta < Q s - Q t`, so one exclusion at `sigma = s0` covers
     every pair of the paper's window — but the pairs needed for a display started at `s` reach
     `t <= s + T L <= s0 + 2 T L`.  The honest event is therefore the drop exclusion over the
     *doubled* window `2 T L`, at the same threshold `2 L34`.  That factor `2` is the only cost of
     the upgrade, and it is carried explicitly below (in the Azuma exponent and in `(n + 1)`).

  3. **The oscillation event is already start-independent.**  The compiled estimate
     `M3Hosc.measureReal_cell_supSiteOsc_pair_le` bounds the *supremum over every site of the site
     window and every pair* `s0 <= u <= v <= s0 + T L` — the single pair `OscPair` at the record
     start site is a subevent of it.  So replacing `OscPair` by the sup event `OscSup` costs nothing
     in the union bound, and makes the event independent of the display start.

  ## Result

  `lococc_recordCarrier_allStarts`: on one event, for every `s0 <= s <= t <= s0 + T L`, the paper's
  display holds at `(s,t)` with the record-dependent right-hand side.  `carrier_fail_subset_allStarts`
  and `measureReal_recordCarrier_allStarts_le` give the complement as the same three named masses as
  the record-start version: `LsBad`, the adapted Azuma term with both residual masses, and the
  site-window oscillation term.
-/
import Swarm.LocOccCarrierAssembly
import Swarm.M3Hosc

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccAllStarts

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier
open SummedSlope.Model
open LocOccCarrierAssembly

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The start-independent projected-oscillation event -/

/-- The shifted two-sided oscillation of `projH_{j,.}` over the carrier's site window
`[A0, A0+Lw)` and the whole time window `s0 <= u <= v <= s0 + T L`, at threshold `L^{3/4}`.
This is precisely the event whose measure `M3Hosc.measureReal_cell_supSiteOsc_pair_le`
estimates; `LocOccCarrierAssembly.OscPair` at a fixed start time is a subevent of it. -/
def OscSup (p : ℝ) (m : ℕ) {N : ℕ} (j : Fin N) (r T L s0 : ℕ) : Set (Array N) :=
  {U | ∃ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L), ∃ u v : ℕ,
    s0 ≤ u ∧ u ≤ v ∧ v ≤ s0 + T * L ∧
      (L : ℝ) ^ (3 / 4 : ℝ) ≤
        |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|}

/-- **`OscSup` at the record carrier implies `OscPair` at every later start.**

The display started at `s` needs the *one-sided* rise of `projH_{j,.}` at the site `X^i_s` between
`s` and `t`.  Both `s` and `t` lie in the paper's window and `X^i_s` lies in the site window, so
the single start-independent `OscSup` exclusion covers all of them at once. -/
theorem notMem_OscSup_imp_OscPair {p : ℝ} {m r s0 L T : ℕ} {i j : Fin N} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
    (hr : (T + 3) * L ≤ r)
    (h : U ∉ OscSup p m j r T L s0) {s t : ℕ} (h1 : s0 ≤ s) (h2 : s ≤ t)
    (h3 : t ≤ s0 + T * L) :
    OscPair p m i j s t L U := by
  have hcell := carrier_cell_window (N := N) hU hr i j h1 (le_trans h2 h3)
  obtain ⟨hlo, hhi, -, -, -, -⟩ := hcell
  have hcast : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) = (trajectory p m U s).pos i := by
    have h0 : (0 : ℤ) ≤ (trajectory p m U s).pos i := by
      have hA0 : (0 : ℤ) ≤ (A0 r T L : ℤ) := by exact_mod_cast Nat.zero_le _
      linarith
    exact Int.toNat_of_nonneg h0
  have hmem : (((trajectory p m U s).pos i).toNat)
      ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L) := by
    rw [Finset.mem_Ico]
    constructor
    · have : (A0 r T L : ℤ) ≤ ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) := by
        rw [hcast]; exact hlo
      exact_mod_cast this
    · have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
        push_cast; ring
      have : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
          < (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
        rw [hcast2, hcast]; exact hhi
      exact_mod_cast this
  by_contra hcon
  have hlt : (L : ℝ) ^ (3 / 4 : ℝ) <
      projH p m j t U ((trajectory p m U s).pos i)
        - projH p m j s U ((trajectory p m U s).pos i) := not_le.mp hcon
  have hle : projH p m j t U ((trajectory p m U s).pos i)
      - projH p m j s U ((trajectory p m U s).pos i)
      ≤ |projH p m j t U ((trajectory p m U s).pos i)
          - projH p m j s U ((trajectory p m U s).pos i)| := le_abs_self _
  exact h ⟨((trajectory p m U s).pos i).toNat, hmem, s, t, h1, h2, h3, by rw [hcast]; linarith⟩

theorem lococc_recordCarrier_core_laterStart
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
      U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) →
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
          hqpl (le_refl s) hst (by omega)
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

/-! ### 5. `(locsum)` and `(locmax)` from the single accepted event `LsBad` -/

/-! ### 3. The paper's event: one set, independent of the display start -/

/-- **The paper's `(lococc)` good event at the carrier.**  The `(locsum)`/`(locmax)` event
`LocSumR1.LsBad`, the one-sided adapted projected `Qpl` drop exclusion over the doubled window
`[s0, s0 + 2 T L]` (needed because a display started at `s <= s0 + T L` reaches `t <= s + T L`),
and the shifted site-window oscillation sup `OscSup`.  None of the three depends on the display
start `s`. -/
def GoodAllStarts (p : ℝ) (m : ℕ) {N : ℕ} (i j : Fin N) (C : ℝ) (r T L s0 : ℕ) :
    Set (Array N) :=
  {U | U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
    U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
      (2 * L34 L (Lw T L)) ∧
    U ∉ OscSup p m j r T L s0}

theorem goodAllStarts_iff {p : ℝ} {m : ℕ} {N : ℕ} {i j : Fin N} {C : ℝ} {r T L s0 : ℕ}
    {U : Array N} :
    U ∈ GoodAllStarts p m i j C r T L s0 ↔
      (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
        U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
          (2 * L34 L (Lw T L)) ∧
        U ∉ OscSup p m j r T L s0) := Iff.rfl

/-- The window `T L` drop set of a later start is contained in the doubled-window drop set of the
record start.  This is the only place where the factor `2` enters. -/
theorem qplDrop_laterStart_subset {Q : ℕ → Array N → ℝ} {s0 s n : ℕ} {δ : ℝ}
    (h1 : s0 ≤ s) (h2 : s ≤ s0 + n) :
    LocOccQ.qplDrop Q s n δ ⊆ LocOccQ.qplDrop Q s0 (2 * n) δ := by
  rintro U ⟨a, b, ha, hb, hc, hdev⟩
  exact ⟨a, b, le_trans h1 ha, hb, by omega, hdev⟩

/-- **The paper's `(lococc)` at every start of the window, on the paper's own event.**

On `GoodAllStarts` (which does not depend on `s` or `t`), for *every* pair of integers
`tau_r = s0 <= s <= t <= s0 + floor (T L)` the display holds with the record-dependent right-hand
side of the paper — no `T L + 3 L` collapse at a later start, since the collapse uses
`M_s^i - X_s^i <= L`, which is only available at `s = tau_r` on `{d_r <= L}`.

`hLsum` is the pointwise `(locsum)` consequence of `U ∉ LsBad`; it is supplied for every `U` by
`LocSumR1.array_locsum_h_start` (see `LocOccCarrierAssembly.exists_lococc_recordCarrier_TL`). -/
theorem lococc_recordCarrier_allStarts
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ} (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ,
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodAllStarts p m i j C r T L s0 →
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
    filter_upwards [lococc_recordCarrier_core_laterStart (N := N) hp1 hp2 hm hij hC1
      (L := L) (T := T) (r := r) (s0 := s0) (s := s) (t := t) hL hT hr h1 h2 h3]
      with U hcore
    intro hU hgood hs' hst' htb'
    obtain ⟨hls, hqpl, hosc⟩ := (goodAllStarts_iff).1 hgood
    have hsle : s ≤ s0 + T * L := le_trans hst' htb'
    exact hcore hU (hLsum U hls)
      (hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s0) (C := C) (T := T) (L := L)
        j hL hls)
      (fun hmem => hqpl (qplDrop_laterStart_subset (Q := ProjLedger.Qpl p m (1 / 8) i j)
        (s0 := s0) (s := s) (n := T * L) (δ := 2 * L34 L (Lw T L))
        hs' hsle hmem))
      (notMem_OscSup_imp_OscPair (p := p) (m := m) (r := r) (s0 := s0) (L := L) (T := T)
        (i := i) (j := j) hU hr hosc hs' hst' htb')
  · filter_upwards with U hU hgood h1 h2 h3
    exact absurd ⟨h1, h2, h3⟩ hrange

/-! ### 4. The complement of the start-independent event -/

/-- **The bad set of the all-starts display is a union of the three named events.**

The display is a.e. on `GoodAllStarts` (`lococc_recordCarrier_allStarts`), so the bad set whose
measure must be bounded is exactly the complement of the good event, intersected with the record
carrier.  The identity below is the set-level statement behind the union bound. -/
theorem carrier_fail_subset_allStarts {p : ℝ} {m r s0 L T : ℕ} {C : ℝ} {i j : Fin N} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodAllStarts p m i j C r T L s0)ᶜ ⊆
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ∪
        ((ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
              (2 * L34 L (Lw T L))) ∪
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            OscSup p m j r T L s0)) := by
  rintro U ⟨hU, hbad⟩
  by_cases hLsBad : U ∈ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)
  · exact Or.inl ⟨hU, hLsBad⟩
  by_cases hQ : U ∈ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
      (2 * L34 L (Lw T L))
  · exact Or.inr (Or.inl ⟨hU, hQ⟩)
  by_cases hO : U ∈ OscSup p m j r T L s0
  · exact Or.inr (Or.inr ⟨hU, hO⟩)
  · exact absurd ((goodAllStarts_iff).2 ⟨hLsBad, hQ, hO⟩) hbad

/-- **The site-window oscillation sup is estimated at the record carrier, with the truncation
residual charged through `LsBad`.**  This is the `OscSup`-form of
`LocOccCarrierAssembly.carrier_inter_osc_fail_le`; the sup over sites and time pairs is exactly the
event `M3Hosc.measureReal_cell_supSiteOsc_pair_le` bounds, so no subset step is needed. -/
theorem measureReal_oscSup_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m j r T L s0)
      ≤ (Lw T L : ℝ) *
          ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
            (2 * (((T * L : ℕ) : ℝ) + 1) *
              Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))))
        + (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) := by
  unfold OscSup
  have hA1 : 1 ≤ A0 r T L := one_le_A0 hL hr
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hV1 : (1 : ℝ) ≤ xOf (Lw T L) := one_le_xOf hLw1
  have hV0 : (0 : ℝ) ≤ xOf (Lw T L) := le_trans zero_le_one hV1
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hn : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hbase := M3Hosc.measureReal_cell_supSiteOsc_pair_le (N := N) hp1 hp2 m j
    (Finset.Ico (A0 r T L) (A0 r T L + Lw T L)) hn
    (ActualRecordFiltration.measurableSet_recordPrefixBand (N := N) p m r s0 L) hV0 hε
  have hcard : ((Finset.Ico (A0 r T L) (A0 r T L + Lw T L)).card : ℝ) = (Lw T L : ℝ) := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  rw [hcard] at hbase
  -- the truncation residual of `M3Hosc` is contained in `LsBad`
  have hres : ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      {U : Array N | ∃ k < T * L,
        U ∉ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)} ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) := by
    rintro U ⟨hU, k, hk, hbad⟩
    refine ⟨hU, ?_⟩
    by_contra hls
    have hloc := hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s0) (C := C) (T := T)
      (L := L) j hL hls
    have hku : s0 + k ≤ s0 + T * L := by omega
    have hrec := recVal_window hU hr j (u := s0 + k) (by omega) hku
    have := QplWindow.HprevAt_le_of_window (N := N) hp1 hp2 (m := m) j (A := A0 r T L)
      (M := Lw T L) (t := s0 + k) hA1 hV1 hrec hloc
    exact hbad this
  have hmono : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        {U : Array N | ∃ k < T * L,
          U ∉ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)})
      ≤ (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) :=
    measureReal_mono hres (measure_ne_top _ _)
  linarith [hbase, hmono]

/-- **The complement of the all-starts event, in the paper's three masses.**

`exp(-c Lw^{1/16})` for `(locsum)`+`(locmax)`, the adapted Azuma term over the doubled window with
both shifted residuals retained, and the site-window oscillation term.  The doubled window only
changes `T L` to `2 T L` inside the Azuma exponent and prefactor. -/
theorem measureReal_recordCarrier_allStarts_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodAllStarts p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
      ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
          (2 * (((2 * (T * L) : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((2 * (T * L) : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s0 w M (2 * (T * L))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            QplWindow.harmDefect p m j V w M)) +
      (Lw T L : ℝ) *
        ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))) := by
  have hTL1 : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have h2TL : 1 ≤ 2 * (T * L) := by omega
  have hL34pos : 0 < L34 L (Lw T L) := by
    linarith [one_le_L34 (L := L) (Lw := Lw T L) hL]
  -- the `Qpl` mass over the doubled window
  have hq := LocOccRecordCarrier.measureReal_recordCarrier_ledger_hQ_le (N := N) hp1 hp2 hm hij
    (r := r) (s := s0) (n := 2 * (T * L)) (L := L) h2TL hV1 (M := M) hw (KQ := 2)
    (L34 := L34 L (Lw T L)) (by norm_num) hL34pos
  have hq' : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
          (2 * L34 L (Lw T L))) ≤
      (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
          (2 * (((2 * (T * L) : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((2 * (T * L) : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s0 w M (2 * (T * L))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            QplWindow.harmDefect p m j V w M)) :=
    le_trans (measureReal_mono_array (Set.subset_union_right) (measure_ne_top _ _)) hq
  have hls : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  have hosc := measureReal_oscSup_le (N := N) hp1 hp2 (m := m) (i := i) (j := j) (C := C) hL hT
    (r := r) (s0 := s0) hr
  have hstep : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodAllStarts p m i j C r T L s0)ᶜ)
      ≤ (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) +
        ((arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
                (2 * L34 L (Lw T L))) +
          (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              OscSup p m j r T L s0)) := by
    refine le_trans (measureReal_mono_array carrier_fail_subset_allStarts
      (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_union_le _ _) ?_
    linarith [measureReal_union_le (μ := arrayMeasure N)
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (2 * (T * L))
          (2 * L34 L (Lw T L)))
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        OscSup p m j r T L s0)]
  linarith

/-! ### 5. No weakening: the new event is contained in the compiled record-start event

The record-start form `LocOccCarrierAssembly.lococc_recordCarrier_TL` of the compiled package is
obtained from the hypotheses `¬LsBad`, `¬qplDrop` over the *single* window `T L` and the *pair*
`OscPair` at the record start site.  The event `GoodAllStarts` implies all three, for every `t` of
the window, so the all-starts complement bound is a bound for a *larger* bad set: the record-start
package is not weakened, it is the `s = s0` special case. -/

/-- `GoodAllStarts` implies the three hypotheses of the compiled record-start display, at every
`t` of the window. -/
theorem goodAllStarts_imp_recordStart
    {p : ℝ} {m r s0 L T : ℕ} {i j : Fin N} {C : ℝ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
    (hr : (T + 3) * L ≤ r) (hgood : U ∈ GoodAllStarts p m i j C r T L s0)
    {t : ℕ} (hst : s0 ≤ t) (ht : t ≤ s0 + T * L) :
    U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
      U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L) (2 * L34 L (Lw T L)) ∧
      OscPair p m i j s0 t L U := by
  obtain ⟨hls, hqpl, hosc⟩ := (goodAllStarts_iff).1 hgood
  refine ⟨hls, fun hmem => hqpl (qplDrop_laterStart_subset
    (Q := ProjLedger.Qpl p m (1 / 8) i j) (s0 := s0) (s := s0) (n := T * L)
    (δ := 2 * L34 L (Lw T L)) (le_refl s0) (by omega) hmem), ?_⟩
  exact notMem_OscSup_imp_OscPair (p := p) (m := m) (r := r) (s0 := s0) (L := L) (T := T)
    (i := i) (j := j) hU hr hosc (le_refl s0) hst ht

/-- **The compiled record-start display, as the `s = s0` special case.**

Same conclusion as `LocOccCarrierAssembly.lococc_recordCarrier_TL` — the collapsed leading term
`T L + 3 L`, using `M_s^i - X_s^i <= L`, `M_s^i - M_s^j <= L` and `M_t^i - M_s^i <= T L + L` at the
record time — but obtained from the start-independent event `GoodAllStarts`. -/
theorem lococc_recordCarrier_TL_of_allStarts
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
      U ∈ GoodAllStarts p m i j C r T L s0 →
      ∑ u ∈ Finset.Ico s0 t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s0 : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  filter_upwards [lococc_recordCarrier_allStarts (N := N) hp1 hp2 hm hij hC1 hL hT hr hLsum]
    with U hall
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

/-! ### 6. The paper's "`L` sufficiently large" packaging

`LocSumR1.array_locsum_h_start` supplies both the exponential bound on `LsBad` and its pointwise
`(locsum)` content at the window `Lw T L`, provided the window start dominates
`2 ellT (xOf (Lw T L))`.  This removes `hLsum` and `hLsBad` from the statement, leaving exactly the
two side conditions the compiled record-start package also keeps. -/

theorem exists_lococc_recordCarrier_allStarts
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 : ℕ},
      (T + 3) * L ≤ r → 2 * ellT (xOf (Lw T L)) ≤ A0 r T L →
      ((arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
          ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) ∧
      (∀ᵐ U ∂(arrayMeasure N), ∀ s t : ℕ,
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
        U ∈ GoodAllStarts p m i j C r T L s0 →
        s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
          ∑ u ∈ Finset.Ico s t,
              (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
            ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
                ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
                  + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
                  + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
              + ((t : ℝ) - (s : ℝ)) / 8
              + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                  + 4 / (1 - aRec p m)) * L34 L (Lw T L)) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
  intro r s0 hr hbig
  have hLLw : L₀ ≤ Lw T L := le_trans hL₀ (le_Lw T L)
  have hres := hL0 (Lw T L) hLLw (A0 r T L) hbig
  exact ⟨hres.1, lococc_recordCarrier_allStarts (N := N) hp1 hp2 hm hij hC1 hL1 hT hr
    (fun U hU a b ha hb hab => hres.2 U hU j a b ha hb hab)⟩
