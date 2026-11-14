/-
  # `(lococc)` on the actual adapted record carrier, with the summed above-record slope-/
import Swarm.LocOccRecordCarrier
import Swarm.SummedSlope
import Swarm.M3Hosc

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccCarrierAssembly

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The paper's window parameters `A0 = r - (T+2)L`, `Lw = (2T+2)L + 1` -/

/-- The paper's left window boundary at level `r`: `A0 = r - (T+2)L`. -/
def A0 (r T L : ℕ) : ℕ := r - (T + 2) * L

/-- The paper's window length: `Lw = (2T+2)L + 1`. -/
def Lw (T L : ℕ) : ℕ := (2 * T + 2) * L + 1

theorem A0_cast {r T L : ℕ} (hr : (T + 2) * L ≤ r) :
    ((A0 r T L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) :=
  Nat.cast_sub hr

/-- The two parameters are exactly complementary: `A0 + Lw = r + TL + 1`.  This is the whole
reason for the `+1` in `Lw`: the window has to reach one level above the record of `i`. -/
theorem A0_add_Lw_cast {r T L : ℕ} (hr : (T + 2) * L ≤ r) :
    ((A0 r T L : ℕ) : ℤ) + ((Lw T L : ℕ) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by
  unfold A0 Lw
  rw [Nat.cast_sub hr]
  push_cast
  ring

/-- `A0 >= 1` on the paper's range `r >= (T+3)L`. -/
theorem one_le_A0 {r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) : 1 ≤ A0 r T L := by
  have hmul : (T + 3) * L = (T + 2) * L + L := by
    rw [show T + 3 = T + 2 + 1 by omega, add_mul, one_mul]
  unfold A0
  omega

theorem T2L_le_r {r T L : ℕ} (hr : (T + 3) * L ≤ r) : (T + 2) * L ≤ r := by
  have hmul : (T + 3) * L = (T + 2) * L + L := by
    rw [show T + 3 = T + 2 + 1 by omega, add_mul, one_mul]
  omega

/-- A `toNat`-cast of a nonnegative integer is the integer itself, in `ℝ`. -/
theorem toNat_cast_real {a : ℤ} (ha : 0 ≤ a) : (((a.toNat : ℕ)) : ℝ) = (a : ℝ) := by
  have h : (((a.toNat : ℕ)) : ℤ) = a := Int.toNat_of_nonneg ha
  exact_mod_cast h

/-! ### 2. The sharpened window containment on the adapted record carrier

`LocOccRecordCarrier.carrier_window_containment` gives, at every `s <= s' <= s + T L`,

`A0 <= X^i_{s'}`, `A0 <= M^j_{s'}`, `X^i_{s'} <= r + T L + 1`,
`M^i_{s'} + 1 <= r + T L + 1`, `M^j_{s'} <= r + T L + 1`.

The `+1` slack is only needed for the running maxima, which can rise one level above
`X^i_s <= r`.  The position `X^i_{s'}` itself obeys the sharper `X^i_{s'} <= r + T L`, and
`r + T L < A0 + Lw`.  The cell fields of the summed assembly are *strict* upper bounds, so this
sharpening is exactly what is needed; it is proved here rather than by changing the accepted
statement. -/
theorem carrier_cell_window {p : ℝ} {m r s L T : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hr : (T + 3) * L ≤ r) (i j : Fin N) {s' : ℕ} (h1 : s ≤ s') (h2 : s' ≤ s + T * L) :
    (A0 r T L : ℤ) ≤ (trajectory p m U s').pos i ∧
    (trajectory p m U s').pos i < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
    (A0 r T L : ℤ) ≤ runMax p m U j s' ∧
    runMax p m U j s' < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
    (A0 r T L : ℤ) ≤ runMax p m U i s' ∧
    runMax p m U i s' + 1 ≤ (A0 r T L : ℤ) + (Lw T L : ℤ) := by

  have hT2 := T2L_le_r hr
  have hcont := LocOccRecordCarrier.carrier_window_containment (N := N) hU i j h1 h2
  obtain ⟨hlo1, hlo2, -, -, -⟩ := hcont
  obtain ⟨-, -, -, -, hpos_ge, hpos_le⟩ :=
    LocOccRecordCarrier.recordPrefixBand_subset_recCell p m i j r s L hU
  have hel : ((s' - s : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have h : s' - s ≤ T * L := by omega
    exact_mod_cast h
  have hposup : (trajectory p m U s').pos i ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h := LocOccRecordCarrier.pos_le_add p m U i h1
    linarith
  have hrecj : runMax p m U j s' ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h := LocOccRecordCarrier.runMax_le_add (N := N) hU j h1
    linarith
  have hreci : runMax p m U i s' ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h := LocOccRecordCarrier.runMax_le_add (N := N) hU i h1
    linarith
  have hrec_i_low : (r : ℤ) - (L : ℤ) ≤ runMax p m U i s' := by
    have h1' : (trajectory p m U s).pos i ≤ runMax p m U i s := le_runMax p m U i s
    have h2' : runMax p m U i s ≤ runMax p m U i s' :=
      LocOccRecordCarrier.runMax_mono_own p m U i h1
    linarith
  have hsum := A0_add_Lw_cast hT2
  have hAc := A0_cast hT2
  have hTL : (L : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by
    have h1 : L ≤ (T + 2) * L := Nat.le_mul_of_pos_left L (by omega)
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The `(lococc)` right-hand side is `T L + 3 L` on the record carrier.**  The three record
terms satisfy `M_t^i - M_s^i <= T L + L`, `M_s^i - X_s^i <= L` and `(M_s^i - M_s^j)_+ <= L`. -/
theorem record_geometry {p : ℝ} {m r s L T : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hr : (T + 3) * L ≤ r) (i j : Fin N) {t : ℕ} (hst : s ≤ t) (htT : t ≤ s + T * L) :
    ((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ)
        + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
        + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ))
      ≤ ((T * L : ℕ) : ℝ) + 3 * (L : ℝ) := by

  obtain ⟨hj_low, hj_up, hi_low, hi_up, hpos_ge, hpos_le⟩ :=
    LocOccRecordCarrier.recordPrefixBand_subset_recCell p m i j r s L hU
  have hMt_nn : (0 : ℤ) ≤ runMax p m U i t := zero_le_runMax p m U i t
  have hMs_nn : (0 : ℤ) ≤ runMax p m U i s := zero_le_runMax p m U i s
  have hMj_nn : (0 : ℤ) ≤ runMax p m U j s := zero_le_runMax p m U j s
  have hLr : (L : ℤ) ≤ (r : ℤ) := by
    have h1 : L ≤ (T + 3) * L := Nat.le_mul_of_pos_left L (by omega)
    have h2 : (L : ℤ) ≤ (((T + 3) * L : ℕ) : ℤ) := by exact_mod_cast h1
    have h3 : (((T + 3) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    linarith
  have hXs_nn : (0 : ℤ) ≤ (trajectory p m U s).pos i := by linarith
  rw [toNat_cast_real hMt_nn, toNat_cast_real hMs_nn, toNat_cast_real hXs_nn,
    toNat_cast_real hMj_nn]
  have hMt_up : runMax p m U i t ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h := LocOccRecordCarrier.runMax_le_add (N := N) hU i hst
    have hel : ((t - s : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
      have h' : t - s ≤ T * L := by omega
      exact_mod_cast h'
    linarith
  have h1 : ((runMax p m U i t : ℤ) : ℝ) - ((runMax p m U i s : ℤ) : ℝ)
      ≤ ((T * L : ℕ) : ℝ) + (L : ℝ) := by
    have h : ((runMax p m U i t : ℤ) : ℝ) ≤ (r : ℝ) + ((T * L : ℕ) : ℝ) := by
      exact_mod_cast hMt_up
    have h' : (r : ℝ) - (L : ℝ) ≤ ((runMax p m U i s : ℤ) : ℝ) := by
      exact_mod_cast hi_low
    linarith
  have h2 : ((runMax p m U i s : ℤ) : ℝ) - ((trajectory p m U s).pos i : ℝ) ≤ (L : ℝ) := by
    have h : ((runMax p m U i s : ℤ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hi_up
    have h' : (r : ℝ) - (L : ℝ) ≤ ((trajectory p m U s).pos i : ℝ) := by
      exact_mod_cast hpos_ge
    linarith
  have h3 : max 0 (((runMax p m U i s : ℤ) : ℝ) - ((runMax p m U j s : ℤ) : ℝ)) ≤ (L : ℝ) := by
    refine max_le ?_ ?_
    · positivity
    · have h : ((runMax p m U i s : ℤ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hi_up
      have h' : (r : ℝ) - (L : ℝ) ≤ ((runMax p m U j s : ℤ) : ℝ) := by exact_mod_cast hj_low
      linarith
  linarith

/-- The paper's window length is at least one. -/
theorem one_le_Lw (T L : ℕ) : 1 ≤ Lw T L := by
  unfold Lw; omega

theorem le_Lw (T L : ℕ) : L ≤ Lw T L := by
  unfold Lw
  have h : L ≤ (2 * T + 2) * L := Nat.le_mul_of_pos_left L (by omega)
  omega

/-! ### 3. The residual probabilistic inputs

Everything in the display below is deterministic given three named events.  Two of them are
accepted events with proved measure bounds (`LocSumR1.LsBad`, `LocOccQ.qplDrop`); the third is the
projected-oscillation pair at the carrier's own start site, which no estimate in the public tree
produces. -/

/-- The projected-oscillation residual at the record carrier: the projected potential of walker
`j` at the carrier's start site `X_s^i` does not rise by more than `L^{3/4}` between `s` and `t`.
Only this single pair is used by the assembly; the full window oscillation is *not* claimed. -/
def OscPair (p : ℝ) (m : ℕ) {N : ℕ} (i j : Fin N) (s t L : ℕ) (U : Array N) : Prop :=
  projH p m j t U ((trajectory p m U s).pos i)
    - projH p m j s U ((trajectory p m U s).pos i) ≤ (L : ℝ) ^ (3 / 4 : ℝ)

/-! ### 4. The assembly: `(lococc)` on the adapted record carrier with the summed slope -/

/-- **`(lococc)` on the actual adapted record carrier, with the summed above-record slope.**

Carrier: the paper's own `{tau_r = s} ∩ {d_r <= L}` in adapted, lookahead-free form
(`ActualRecordFiltration.recordPrefixBand`, `N` finite and nonempty).  Windows: `A0 = r-(T+2)L`,
`Lw = (2T+2)L+1`, times `s <= t <= s + TL`.

Discharged inside, from adapted record-carrier membership alone: all cell/geometry fields of the
summed assembly (`X^i, M^i, M^j` inside `[A0, A0+Lw)` at every time of the window, with the
`M^i` lower bound from `X_s <= M_s^i <= M_{s'}^i`), nonnegativity of the integer sites, the
`Int.toNat` casts, and the literal indicator form.

Discharged inside, from the a.e. accepted fields: the adapted projected step ledger
(`LocOcc.ae_step_ledger_actual`), the `Zproj` bridges at `s` and `t`, the below-record slope
identity `projH = Hpot`, the closed form for `projH` above the record and the seed bounds
`0 <= e_0 <= b_n`.  Hence the below-record slope field, per-site nonnegativity above the record
and the *summed* above-record estimate with the single additive defect `e_0/(1-a) <= b_n/(1-a)`
are all conclusions, not hypotheses, and the per-site `Kp` premise is gone (`Kp = Lc p m`).

Retained, as the exact residual inputs: `(locsum)`, `(locmax)` on `[A0-1, A0+Lw)`, the one-sided
adapted `Qpl` window, and the projected-oscillation pair. -/
theorem lococc_recordCarrier_core
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
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
  have hcell : ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
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
  have hcellX : ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
      A0 r T L ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨h1', h2', -, -, -, -⟩ := hcell u h1 h2
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
  have hcellMj : ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
      A0 r T L ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨-, -, h1', h2', -, -⟩ := hcell u h1 h2
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
    obtain ⟨-, -, -, -, h1', h2'⟩ := hcell t hst htT
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
  have hnonneg : ∀ u : ℕ, s ≤ u → u ≤ s + T * L → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    have hc := (hcell u h1 h2).1
    linarith
  have hnonneg' : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i :=
    fun u h1 h2 => hnonneg u h1 (by omega)
  have hcast : ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
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
      exact hcellMj t hst htT
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
  have hcap : ∀ u : ℕ, s ≤ u → u ≤ s + T * L →
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
    rw [hcast t hst htT]
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
          hqpl (le_refl s) hst htT
        simpa using h)
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U s
        (hcap s le_rfl (by omega)))
      (abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U t
        (hcap t hst htT))
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
      (le_of_lt (hcellX t hst htT).2)
      hcellMi.2
      (le_of_lt (hcellMj t hst htT).2)
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

/-- The `(locmax)` cap on `[A0-1, A0+Lw)` from `U ∉ LsBad`: `LsBad` carries the cap on the wider
window `[A0 - ellT (xOf Lw), A0 + Lw)`, and `ellT (xOf Lw) >= 1`, so the left boundary site
`A0 - 1` is covered. -/
theorem hloc_of_not_LsBad {p : ℝ} {m r s : ℕ} {C : ℝ} {U : Array N} {T L : ℕ} (j : Fin N)
    (hL : 1 ≤ L)
    (hls : U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) :
    ∀ y ∈ Finset.Ico (A0 r T L - 1) (A0 r T L + Lw T L),
      hof p (siteMarks p m U j) y ≤ xOf (Lw T L) := by
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hx1 : (1 : ℝ) ≤ xOf (Lw T L) := one_le_xOf hLw1
  have hell : 1 ≤ ellT (xOf (Lw T L)) := by
    have h : xOf (Lw T L) ≤ ((⌈xOf (Lw T L)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (1 : ℝ) ≤ ((⌈xOf (Lw T L)⌉₊ : ℕ) : ℝ) := le_trans hx1 h
    exact_mod_cast h2
  have hsem : U ∉ ({U : Array N |
      ∃ j : Fin N, ∃ y ∈ Finset.Ico (A0 r T L - ellT (xOf (Lw T L))) (A0 r T L + Lw T L),
        xOf (Lw T L) ≤ hof p (siteMarks p m U j) y}) := by
    intro hmem
    exact hls (Or.inr (Or.inl hmem))
  intro y hy
  have hmem : y ∈ Finset.Ico (A0 r T L - ellT (xOf (Lw T L))) (A0 r T L + Lw T L) := by
    rw [Finset.mem_Ico] at hy ⊢
    exact ⟨by omega, hy.2⟩
  by_contra hcon
  exact hsem ⟨j, y, hmem, le_of_lt (not_le.mp hcon)⟩

/-- **`(lococc)` on the adapted record carrier with the summed slope, `LsBad` form.**  The
`(locsum)` premise of `lococc_recordCarrier_core` is replaced by its *pointwise consequence* of
the accepted event `LocSumR1.LsBad`, and `(locmax)` is derived from `U ∉ LsBad` outright. -/
theorem lococc_recordCarrier_summed
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) →
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
  filter_upwards [lococc_recordCarrier_core (N := N) hp1 hp2 hm hij hC1 hL hT hr hst htT] with U hcore
  intro hU hls hqpl hosc
  exact hcore hU (hLsum U hls) (hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s) j hL hls)
    hqpl hosc

/-! ### 6. The paper's shape: `T L + 3 L` in the leading term -/

/-- **The `(lococc)` display in the paper's shape on the record carrier.**  The record-dependent
right-hand side is bounded by `T L + 3 L`, so the occupation is `O(T L)` with the coefficient
`C` independent of `T`. -/
theorem lococc_recordCarrier_TL
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) →
      OscPair p m i j s t L U →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  filter_upwards [lococc_recordCarrier_summed (N := N) hp1 hp2 hm hij hC1 hL hT hr hst htT hLsum]
    with U hcore
  intro hU hls hqpl hosc
  have h1 := hcore hU hls hqpl hosc
  have h2 := record_geometry hU hr i j hst htT
  have hcoef : (0 : ℝ) ≤ (2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1 := by
    have := Lc_nonneg hp1 hp2 m
    have := CJc_nonneg hp1 hp2 m
    have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
    nlinarith
  have h3 : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
      ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
        + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
        + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
      ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hcoef
  linarith

/-! ### 7. The paper's "`L` sufficiently large" reduction and the `LsBad` probability

`array_locsum_h_start` needs the window start to dominate `2 ellT (xOf Lw)`.  Since `A0 >= L` on
the paper's range `r >= (T+3)L`, it is enough that `2 ellT (xOf Lw) <= L`. -/

theorem le_A0 {r T L : ℕ} (hr : (T + 3) * L ≤ r) : L ≤ A0 r T L := by
  have hmul : (T + 3) * L = (T + 2) * L + L := by
    rw [show T + 3 = T + 2 + 1 by omega, add_mul, one_mul]
  unfold A0
  omega

theorem hbig_of_le_L {r T L : ℕ} (hr : (T + 3) * L ≤ r)
    (h : 2 * ellT (xOf (Lw T L)) ≤ L) : 2 * ellT (xOf (Lw T L)) ≤ A0 r T L :=
  le_trans h (le_A0 hr)

/-- The start condition of `array_locsum_h_start` is automatic once `r` exceeds `(T+3)L` by the
depth `2 ellT (xOf Lw)`.  This is a pure arithmetic side condition on `(r, L)` — the paper's
regime `r >> L` at fixed `T` — and carries no probabilistic content. -/
theorem hbig_of_r {r T L : ℕ} (hr : (T + 3) * L + 2 * ellT (xOf (Lw T L)) ≤ r) :
    2 * ellT (xOf (Lw T L)) ≤ A0 r T L := by
  have hmul : (T + 3) * L = (T + 2) * L + L := by
    rw [show T + 3 = T + 2 + 1 by omega, add_mul, one_mul]
  unfold A0
  omega

/-- **The paper's `(lococc)` on the adapted record carrier, for all sufficiently large `L`.**

This is the exact form of the paper's Proposition `local` restricted to `(lococc)`: an explicit
`c > 0` and threshold `L₀` (both from `LocSumR1.array_locsum_h_start`), the accepted exponential
bound on the joint `(locsum)`/`(locmax)` event `LsBad`, and — on its complement and outside the
adapted `Qpl` drop set and given the projected-oscillation pair — the display with the *summed*
above-record slope, the additive seed defect absorbed into `C_T L^{3/4}`, and the leading term
`C (T L + 3 L)` with `C` independent of `T`. -/
theorem exists_lococc_recordCarrier_TL
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s t : ℕ},
      (T + 3) * L ≤ r → 2 * ellT (xOf (Lw T L)) ≤ A0 r T L →
      s ≤ t → t ≤ s + T * L →
      ((arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
          ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) ∧
      (∀ᵐ U ∂(arrayMeasure N),
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
        U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
        U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) →
        OscPair p m i j s t L U →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
          ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
              (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
            + ((t : ℝ) - (s : ℝ)) / 8
            + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L)) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
  intro r s t hr hbig hst htT
  have hLLw : L₀ ≤ Lw T L := le_trans hL₀ (le_Lw T L)
  have hres := hL0 (Lw T L) hLLw (A0 r T L) hbig
  refine ⟨hres.1, ?_⟩
  refine lococc_recordCarrier_TL (N := N) hp1 hp2 hm hij hC1 (L := L) (T := T) (r := r) (s := s)
    (t := t) hL1 hT hr hst htT ?_
  exact fun U hU a b ha hb hab => hres.2 U hU j a b ha hb hab

/-! ### 8. Joint probability bookkeeping: the failure set is a union of three named events -/

/-- `μ.real s ≤ μ.real t` for `s ⊆ t` in a finite measure space. -/
theorem measureReal_mono_array {s t : Set (Array N)}
    (h : s ⊆ t) (ht : (arrayMeasure N) t ≠ ∞) :
    (arrayMeasure N).real s ≤ (arrayMeasure N).real t :=
  MeasureTheory.measureReal_mono h ht

/-- From an `ENNReal` bound to a real bound. -/
theorem measureReal_le_of_measure_le_ofReal {s : Set (Array N)} {a : ℝ} (ha : 0 ≤ a)
    (h : (arrayMeasure N) s ≤ ENNReal.ofReal a) : (arrayMeasure N).real s ≤ a := by
  rw [MeasureTheory.measureReal_def]
  calc ((arrayMeasure N) s).toReal ≤ (ENNReal.ofReal a).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = a := ENNReal.toReal_ofReal ha

/-- **The joint failure set of the record-carrier display is a union of three named events.**

The display fails on the carrier only if one of `LsBad` (carrier `(locsum)` + `(locmax)`),
`qplDrop` (the adapted projected `Qpl` drop) or the projected-oscillation pair fails.  This is
stated as a set inclusion and *not* as a claim that the three field bounds compose into a joint
bound. -/
theorem carrier_fail_subset {p : ℝ} {m r s t L T : ℕ} {C : ℝ} {i j : Fin N} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
      {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
        U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
        OscPair p m i j s t L U)} ⊆
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ∪
      ((ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L))) ∪
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ OscPair p m i j s t L U})) := by
  rintro U ⟨h1, h2⟩
  by_cases hLb : U ∈ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)
  · exact Or.inl ⟨h1, hLb⟩
  · by_cases hQ : U ∈ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L)
        (2 * L34 L (Lw T L))
    · exact Or.inr (Or.inl ⟨h1, hQ⟩)
    · exact Or.inr (Or.inr ⟨h1, fun hOp => h2 ⟨hLb, hQ, hOp⟩⟩)

/-- **The three-term union bound for the record-carrier failure set.**  The `Qpl` term is replaced
by the accepted adapted Azuma estimate with *both* residual masses `shiftedContDefect` and
`harmDefect` retained; the `LsBad` and oscillation terms remain as named masses. -/
theorem measureReal_recordCarrier_fail_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s t : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
            U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
            OscPair p m i j s t L U)}) ≤
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) +
      ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((T * L : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s w M (T * L)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V w M)) +
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U : Array N | ¬ OscPair p m i j s t L U}) := by
  have hTL : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hL34pos : 0 < L34 L (Lw T L) := by linarith [one_le_L34 (L := L) (Lw := Lw T L) hL]
  have hq := LocOccRecordCarrier.measureReal_recordCarrier_ledger_hQ_le (N := N) hp1 hp2 hm hij
    (r := r) (s := s) (n := T * L) (L := L) hTL hV1 (M := M) hw (KQ := 2)
    (L34 := L34 L (Lw T L)) (by norm_num) hL34pos
  have hq' : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L))) ≤
      (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((T * L : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        ((arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s w M (T * L)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V w M)) :=
    le_trans (measureReal_mono_array (Set.subset_union_right) (measure_ne_top _ _)) hq
  have hstep : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
          U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
          OscPair p m i j s t L U)})
      ≤ (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) +
        ((arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L))) +
          (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              {U : Array N | ¬ OscPair p m i j s t L U})) := by
    refine le_trans (measureReal_mono_array carrier_fail_subset (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_union_le _ _) ?_
    linarith [measureReal_union_le (μ := arrayMeasure N)
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)))
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ¬ OscPair p m i j s t L U})]
  linarith

/-- **The joint failure bound with the accepted exponential `LsBad` estimate.**  The three terms
are the accepted `e^{-c Lw^{1/16}}` for `(locsum)`+`(locmax)`, the adapted Azuma term with both
residual masses, and the un-estimated projected-oscillation mass. -/
theorem measureReal_recordCarrier_fail_le_exp
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s t : ℕ} {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w) {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
            U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
            OscPair p m i j s t L U)}) ≤
      Real.exp (-c * xOf (Lw T L)) +
      ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((T * L : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s w M (T * L)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V w M)) +
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U : Array N | ¬ OscPair p m i j s t L U}) := by
  have h1 := measureReal_recordCarrier_fail_le (N := N) hp1 hp2 hm hij (C := C) hL hT
    (r := r) (s := s) (t := t) hV1 (M := M) hw
  have hexp : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  linarith

/-! ### 9. The one-sided drop input against a two-sided window -/

/-- **A two-sided window implies the one-sided drop exclusion.**  A deviation of `2delta` at some
pair `sigma <= s <= t <= sigma+n` is impossible if every single-time deviation is below `delta`.
Hence the `Qpl` input of `lococc_recordCarrier_TL`
(`U ∉ qplDrop ... (2 * L34)`) is *implied* by a two-sided window at threshold `L^{3/4}`, while the
converse does not hold: the one-sided form is the weaker hypothesis, and it is the one for which
the accepted adapted Azuma estimate gives a bound at the record carrier. -/
theorem notMem_qplDrop_of_window {Q : ℕ → Array N → ℝ} {σ n : ℕ} {δ δ' : ℝ}
    (hle : 2 * δ ≤ δ') {U : Array N}
    (h : ∀ k ≤ n, |Q (σ + k) U - Q σ U| < δ) : U ∉ LocOccQ.qplDrop Q σ n δ' := by
  rintro ⟨s, t, h1, h2, h3, hdev⟩
  have hs : σ + (s - σ) = s := Nat.add_sub_cancel' h1
  have ht : σ + (t - σ) = t := Nat.add_sub_cancel' (le_trans h1 h2)
  have hsn : s - σ ≤ n := by omega
  have htn : t - σ ≤ n := by omega
  have e1 := h (s - σ) hsn
  have e2 := h (t - σ) htn
  rw [hs] at e1
  rw [ht] at e2
  have h1' : Q s U - Q σ U < δ := (abs_lt.mp e1).2
  have h2' : -δ < Q t U - Q σ U := (abs_lt.mp e2).1
  linarith

/-- **The same-carrier display from a two-sided projected `Qpl` window.**  This is
`lococc_recordCarrier_TL` with the one-sided drop hypothesis replaced by the two-sided window at
threshold `L^{3/4}` that the accepted `SummedSlope` interface uses; the implication is
`notMem_qplDrop_of_window`, so nothing is assumed that the accepted interface does not assume. -/
theorem lococc_recordCarrier_TL_of_twoSided
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    (hLsum : ∀ U : Array N, U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      (∀ k ≤ T * L,
        |Qpl p m (1 / 8) i j (s + k) U - Qpl p m (1 / 8) i j s U| < (L : ℝ) ^ (3 / 4 : ℝ)) →
      OscPair p m i j s t L U →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  filter_upwards [lococc_recordCarrier_TL (N := N) hp1 hp2 hm hij hC1 hL hT hr hst htT hLsum]
    with U hcore
  intro hU hls hwin hosc
  refine hcore hU hls ?_ hosc
  refine notMem_qplDrop_of_window (Q := ProjLedger.Qpl p m (1 / 8) i j) (σ := s) (n := T * L)
    (δ := (L : ℝ) ^ (3 / 4 : ℝ)) (δ' := 2 * L34 L (Lw T L)) ?_ hwin
  have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h4 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L (Lw T L) := L34_lower_rpow L (Lw T L)
  linarith

/-- **Non-vacuity of the carrier at the paper's own level `r = s`.**  For `p >= 1/2`, `s >= 1`
and every `L`, the adapted record carrier at level `s` and time `s` has strictly positive
`arrayMeasure N`-mass, so the a.e. display above is not a statement about a null carrier. -/
theorem recordPrefixBand_pos_at_own_level (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (s L : ℕ)
    (hs : 1 ≤ s) :
    0 < arrayMeasure N (ActualRecordFiltration.recordPrefixBand (N := N) p m s s L) :=
  LocOccRecordCarrier.recordPrefixBand_pos p hp m s L hs

/-! ### 10. The projected oscillation pair is itself estimated at the record carrier

`M3Hosc.measureReal_cell_supSiteOsc_pair_le` bounds the shifted two-sided oscillation of
`H_{j,·}(y)` over all sites `y` of a window and all pairs `s <= u <= v <= s+n`, on a
`F_s`-measurable cell, with the predictable-truncation residual `{∃ k < n, ¬ siteGood (s+k)}`
charged once.  Two observations remove the residual here:

* the truncation failure `HprevAt p m (s+k) j U > V` forces the `(locmax)` condition to fail at the
  record site `M_{s+k}^j - 1`, which on the carrier lies in `[A0-1, A0+Lw)`; hence
  `carrier ∩ {∃ k < n, ¬ siteGood} ⊆ carrier ∩ LsBad`;
* the oscillation pair at the walker's own site `X_s^i` is a pair of the site-window event,
  because `X_s^i` lies in `[A0, A0+Lw)` on the carrier.

Hence the *last* residual of the display is a union-bound term with an explicit exponent, and the
whole joint failure set of the record-carrier display is estimated. -/
/-- The record of walker `j` in the `toNat` form of the summed assembly, from carrier membership. -/
theorem runMax_toNat_window {p : ℝ} {m r s L T : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hr : (T + 3) * L ≤ r) (j : Fin N) {u : ℕ} (h1 : s ≤ u) (h2 : u ≤ s + T * L) :
    A0 r T L ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A0 r T L + Lw T L := by
  obtain ⟨-, -, hlo, hhi, -, -⟩ := carrier_cell_window hU hr (Classical.arbitrary (Fin N)) j h1 h2
  have hcast : ((((runMax p m U j u).toNat : ℕ) : ℤ)) = runMax p m U j u :=
    Int.toNat_of_nonneg (zero_le_runMax p m U j u)
  have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
    push_cast; ring
  constructor
  · have h' : (A0 r T L : ℤ) ≤ (((runMax p m U j u).toNat : ℕ) : ℤ) := by
      rw [hcast]; exact hlo
    exact_mod_cast h'
  · have h'' : (((runMax p m U j u).toNat : ℕ) : ℤ) < (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
      rw [hcast2, hcast]; exact hhi
    exact_mod_cast h''

/-- The same in `recVal` form, as `QplWindow.HprevAt_le_of_window` consumes it. -/
theorem recVal_window {p : ℝ} {m r s L T : ℕ} {U : Array N}
    (hU : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    (hr : (T + 3) * L ≤ r) (j : Fin N) {u : ℕ} (h1 : s ≤ u) (h2 : u ≤ s + T * L) :
    A0 r T L ≤ (recVal j (prefOf p m u U)).toNat ∧
      (recVal j (prefOf p m u U)).toNat < A0 r T L + Lw T L := by
  rw [← runMax_eq_recVal]
  exact runMax_toNat_window hU hr j h1 h2

theorem carrier_inter_osc_fail_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s t : ℕ}
    (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ OscPair p m i j s t L U})
      ≤ (Lw T L : ℝ) *
          ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
            (2 * (((T * L : ℕ) : ℝ) + 1) *
              Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))))
        + (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
              LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) := by
  have hA1 : 1 ≤ A0 r T L := one_le_A0 hL hr
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hV1 : (1 : ℝ) ≤ xOf (Lw T L) := one_le_xOf hLw1
  have hV0 : (0 : ℝ) ≤ xOf (Lw T L) := le_trans zero_le_one hV1
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hn : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hbase := M3Hosc.measureReal_cell_supSiteOsc_pair_le (N := N) hp1 hp2 m j
    (Finset.Ico (A0 r T L) (A0 r T L + Lw T L)) hn
    (ActualRecordFiltration.measurableSet_recordPrefixBand (N := N) p m r s L) hV0 hε
  have hcard : ((Finset.Ico (A0 r T L) (A0 r T L + Lw T L)).card : ℝ) = (Lw T L : ℝ) := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  rw [hcard] at hbase
  -- the oscillation pair is one of the site-window pairs
  have hsub : ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
      {U : Array N | ¬ OscPair p m i j s t L U} ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ∃ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
          ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + T * L ∧
            (L : ℝ) ^ (3 / 4 : ℝ) ≤
              |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|} := by
    rintro U ⟨hU, hnot⟩
    obtain ⟨h1, h2, -, -, -, -⟩ := carrier_cell_window hU hr i j (le_refl s) (by omega)
    have hcast : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) = (trajectory p m U s).pos i :=
      Int.toNat_of_nonneg (by
        have h0 : (0 : ℤ) ≤ (A0 r T L : ℤ) := by exact_mod_cast Nat.zero_le _
        linarith)
    have hmem : (((trajectory p m U s).pos i).toNat)
        ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L) := by
      rw [Finset.mem_Ico]
      constructor
      · have hZ : (A0 r T L : ℤ) ≤ (trajectory p m U s).pos i := h1
        have : (A0 r T L : ℤ) ≤ ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) := by
          rw [hcast]; exact hZ
        exact_mod_cast this
      · have hZ : (trajectory p m U s).pos i < (A0 r T L : ℤ) + (Lw T L : ℤ) := h2
        have hcast2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (A0 r T L : ℤ) + (Lw T L : ℤ) := by
          push_cast; ring
        have : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
            < (((A0 r T L + Lw T L : ℕ)) : ℤ) := by
          rw [hcast2, hcast]; exact hZ
        exact_mod_cast this
    refine ⟨hU, _, hmem, s, t, le_rfl, hst, htT, ?_⟩
    have hdev : (L : ℝ) ^ (3 / 4 : ℝ) <
        projH p m j t U ((trajectory p m U s).pos i)
          - projH p m j s U ((trajectory p m U s).pos i) := by
      by_contra hc
      exact hnot (le_of_not_gt hc)
    have hle : projH p m j t U ((trajectory p m U s).pos i)
        - projH p m j s U ((trajectory p m U s).pos i)
        ≤ |projH p m j t U ((trajectory p m U s).pos i)
            - projH p m j s U ((trajectory p m U s).pos i)| := le_abs_self _
    rw [hcast]
    linarith
  -- the truncation residual is contained in `LsBad`
  have hres : ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
      {U : Array N | ∃ k < T * L,
        U ∉ SiteHMax.siteGood p m j (xOf (Lw T L)) (s + k)} ⊆
      ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) := by
    rintro U ⟨hU, k, hk, hbad⟩
    refine ⟨hU, ?_⟩
    by_contra hls
    have hloc := hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s) (C := C) (T := T)
      (L := L) j hL hls
    have hku : s + k ≤ s + T * L := by omega
    have hrec := recVal_window hU hr j (u := s + k) (by omega) hku
    have := QplWindow.HprevAt_le_of_window (N := N) hp1 hp2 (m := m) j (A := A0 r T L)
      (M := Lw T L) (t := s + k) hA1 hV1 hrec hloc
    exact hbad this
  have hmono1 : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ¬ OscPair p m i j s t L U})
      ≤ (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ∃ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
            ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + T * L ∧
              (L : ℝ) ^ (3 / 4 : ℝ) ≤
                |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|}) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hmono2 : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ∃ k < T * L,
          U ∉ SiteHMax.siteGood p m j (xOf (Lw T L)) (s + k)})
      ≤ (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) :=
    measureReal_mono hres (measure_ne_top _ _)
  linarith [hbase, hmono1, hmono2]

/-- **The complete joint probability bound for the record-carrier display.**

All four named good events of `lococc_recordCarrier_summed` are estimated at once, with the two
`(locsum)`/`(locmax)` failures and the truncation residual charged through the single accepted
event `LsBad` (hence the factor `2`), the adapted projected `Qpl` drop charged by the shifted
Azuma estimate with both residual masses `shiftedContDefect`, `harmDefect` retained, and the
projected-oscillation pair charged by the shifted record-window estimate.  This is a genuine
union bound: it does not identify the joint mass with the product or the sum of the field
estimates, it bounds it by their sum. -/
theorem measureReal_recordCarrier_joint_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s t : ℕ} (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w) {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
            U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
            OscPair p m i j s t L U)}) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
      ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
              (4 * ((T * L : ℕ) : ℝ) *
                (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s w M (T * L)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j V w M)) +
      (Lw T L : ℝ) *
        ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) *
          (2 * (((T * L : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))) := by
  have h1 := measureReal_recordCarrier_fail_le_exp (N := N) hp1 hp2 hm hij (C := C) hL hT
    (r := r) (s := s) (t := t) hV1 (M := M) hw hc hLsBad
  have h2 := carrier_inter_osc_fail_le (N := N) hp1 hp2 (m := m) (i := i) (j := j) (C := C)
    (T := T) (r := r) (s := s) (t := t) hL hT hr hst htT
  have hexp : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  linarith

/-- The `(locsum)` start condition `2 ellT (xOf Lw) <= L` holds for all sufficiently large `L`
(explicitly: `L >= (2T+4) * 4^16`), by `LocSumAct.two_mul_ellT_window_le`.  This removes the only
non-explicit arithmetic side condition of `exists_lococc_recordCarrier_TL`. -/
theorem exists_two_mul_ellT_xOf_Lw_le (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, 2 * ellT (xOf (Lw T L)) ≤ L := by
  refine ⟨(2 * T + 4) * 4 ^ 16, ?_⟩
  intro L hL
  have hM1 : 1 ≤ (2 * T + 4) * 4 ^ 16 := by
    have h1 : 1 ≤ 2 * T + 4 := by omega
    have h2 : 1 ≤ 4 ^ 16 := by norm_num
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (2 * T + 4) * 4 ^ 16 := Nat.mul_le_mul h1 h2
  have hL1 : 1 ≤ L := le_trans hM1 hL
  have hpow : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 := by
    have h1 : ((2 * T + 4) * 4 ^ 16) ^ 15 ≤ L ^ 15 := Nat.pow_le_pow_left hL 15
    have h2 : (2 * T + 4) * 4 ^ 16 ≤ ((2 * T + 4) * 4 ^ 16) ^ 15 := by
      calc (2 * T + 4) * 4 ^ 16 = ((2 * T + 4) * 4 ^ 16) ^ 1 := (pow_one _).symm
        _ ≤ ((2 * T + 4) * 4 ^ 16) ^ 15 := Nat.pow_le_pow_right hM1 (by norm_num)
    linarith
  have hbase := LocSumAct.two_mul_ellT_window_le (L := L) (T := T) hL1 hpow
  have hLwle : Lw T L ≤ (2 * T + 4) * L := by
    unfold Lw
    have h2 : (2 * T + 2) * L + 1 ≤ (2 * T + 2) * L + L := by omega
    have ha : (2 * T + 2) * L + 2 * L = (2 * T + 4) * L := by
      have h : 2 * T + 4 = (2 * T + 2) + 2 := by omega
      calc (2 * T + 2) * L + 2 * L = ((2 * T + 2) + 2) * L := (Nat.add_mul _ _ _).symm
        _ = (2 * T + 4) * L := by rw [← h]
    have hb : (2 * T + 2) * L + L ≤ (2 * T + 2) * L + 2 * L := by omega
    linarith
  have hmono : ellT (xOf (Lw T L)) ≤ ellT (xOf ((2 * T + 4) * L)) := by
    refine Nat.ceil_mono ?_
    unfold xOf
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLwle) (by norm_num)
  omega

/-- **The paper's `(lococc)` on the adapted record carrier, with no arithmetic side condition.**
Same as `exists_lococc_recordCarrier_TL`, but the `(locsum)` start condition is discharged from
`exists_two_mul_ellT_xOf_Lw_le`, so the only hypotheses are the paper's own
(`1/2 < p < 1`, `2 <= m`, `i ≠ j`, `C >= 1`, `C > Mb`, `T >= 1`, `r >= (T+3)L`,
`s <= t <= s + T L`). -/
theorem exists_lococc_recordCarrier_TL' 
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s t : ℕ},
      (T + 3) * L ≤ r → s ≤ t → t ≤ s + T * L →
      ((arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
          ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) ∧
      (∀ᵐ U ∂(arrayMeasure N),
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s L →
        U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
        U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) →
        OscPair p m i j s t L U →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
          ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
              (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
            + ((t : ℝ) - (s : ℝ)) / 8
            + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L)) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    exists_lococc_recordCarrier_TL (N := N) hp1 hp2 hm hij hC1 hCM hT
  obtain ⟨L₁, hL1⟩ := exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨c, hc, max L₀ L₁, fun L hL => ?_⟩
  intro r s t hr hst htT
  have hA : L₀ ≤ L := le_trans (le_max_left L₀ L₁) hL
  have hB : L₁ ≤ L := le_trans (le_max_right L₀ L₁) hL
  have hbig : 2 * ellT (xOf (Lw T L)) ≤ A0 r T L := hbig_of_le_L hr (hL1 L hB)
  exact hL0 L hA hr hbig hst htT

/-- **The joint bound in the form the paper quotes.**  Since `arrayMeasure N` is a probability
measure, `m(carrier) <= 1` and the two carrier-weighted exponential terms lose its prefactor. -/
theorem measureReal_recordCarrier_joint_le'
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s t : ℕ} (hr : (T + 3) * L ≤ r) (hst : s ≤ t) (htT : t ≤ s + T * L)
    {w M : ℕ} (hw : 1 ≤ w) {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
          {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
            U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L) (2 * L34 L (Lw T L)) ∧
            OscPair p m i j s t L U)}) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
      (2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
          (4 * ((T * L : ℕ) : ℝ) * (QplPredEnv.envB p m 1 (QplWindow.envC p m 1)) ^ 2)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            ShiftedQplResidual.shiftedContDefect p m i j s w M (T * L)) +
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            QplWindow.harmDefect p m j 1 w M)) +
      (Lw T L : ℝ) *
        (2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
            (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h1 := measureReal_recordCarrier_joint_le (N := N) hp1 hp2 hm hij (C := C) hL hT
    (r := r) (s := s) (t := t) hr hst htT (V := 1) le_rfl (M := M) hw hc hLsBad
  have hmu : (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) ≤ 1 :=
    measureReal_le_one
  have hmu0 : (0 : ℝ) ≤
      (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L) :=
    measureReal_nonneg
  have hE1 : (0 : ℝ) ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
      Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
        (4 * ((T * L : ℕ) : ℝ) * (QplPredEnv.envB p m 1 (QplWindow.envC p m 1)) ^ 2)) := by
    positivity
  have hE2 : (0 : ℝ) ≤ (Lw T L : ℝ) *
      (2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
          (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))) := by
    positivity
  nlinarith [h1, hmu, hmu0, hE1, hE2]

end LocOccCarrierAssembly
