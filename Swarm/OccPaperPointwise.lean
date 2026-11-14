/-
# `(lococc)` in the paper's literal shape, pointwise at the actual record fibre

## What this file is

`OccDisplayNull.occFace` states the paper's `(lococc)` display pointwise at a record fibre, but in
an *intermediate* shape: the record-dependent combination is written with `Int.toNat` casts
(`((runMax …).toNat : ℝ)`, `(((trajectory …).pos …).toNat : ℝ)`) and the additive remainder is the
abstract `L34 L (Lw T L)`.  The paper writes honest ℤ-differences and `C_T L^{3/4}`.

`LocOccPaperScale` converts `L34` into `CTocc · L^{3/4}` but keeps the `.toNat` casts and states the
result only almost surely, not off the named bad event at the literal record time.

This file performs the conversion at the pointwise level and composes it with the finite-family
event:

* `cast_toNat_of_nonneg`, `cast_runMax` — the cast identities.  `M_n^j >= 0` holds identically
  (`zero_le_runMax`), so `M_t^i - M_s^i` and `(M_s^i - M_s^j)_+` need no carrier hypothesis.
* `pos_nonneg_of_carrier` — the one place where a hypothesis is genuinely needed: `X_s^i >= 0`.
  It is *derived* from `recordCarrier` (`(locmax)`/`d_r <= L` plus unit steps), not assumed:
  on `[tau_r, tau_r + T*L]` every walker stands at least at `r - (T+1)L >= 2L >= 0`.
* `occDisplayAllStartsPaper`, `occDisplayTLPaper`, `occFacePaper` — the paper's display with honest
  `((· : ℤ) : ℝ)` casts, coefficient `Kocc p m C` and error `CTocc p m C T · L^{3/4}`.
* `occDisplayAllStartsPaper_of_pos`, `occDisplayTLPaper_of_toNat`, `occFacePaper_of_carrier` — the
  conversions.
* `familyGood_lococcPaper` — off `LocalGoodFamily.famBad`, on `recordCarrier`, the paper-shape
  display holds pointwise at `recTimeA p m U r`, with `C = Kocc p m (Ccan p m)` and
  `C_T = CTocc p m (Ccan p m) T`.
* `locMartGood_paper`, `familyGood_locmartPaper` — the `(locmart)` reindexing `s ↦ tau_r + s`,
  `t ↦ tau_r + s + k` to arbitrary `s <= t` in the window, at `C_T = 1`.
* `exists_famBad_and_lococcPaper` — the same inside the family headline: one bad event with one
  exponential bound, off which the paper-shape occupation and `(locmart)` displays hold.

## What is NOT claimed

* `GoodWinAllPairs` remains a *hypothesis* of the display (as in the source); this file proves no
  probability statement about it and no non-vacuity.
* `locmoveGood`, `locCoordGeom`, `SepSet`, the `(locsum)` range content and the geometric
  `recordCarrier` remain explicit carriers of the corresponding clauses.  Only the *nonnegativity*
  of the positions on the record window is discharged here.
* No `(loccoord)` single-time spatial conversion, no `(locmove)` paper-form conversion, no universal
  family instantiation, no blocks, tightness, invariant law, regeneration, speed or `MainClaim`.
-/
import Swarm.LocalGoodFamily
import Swarm.LocOccPaperScale
import Swarm.L34PaperScale
import Swarm.TopRowChain

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs

namespace OccPaperPointwise

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The cast identities -/

/-- `Int.toNat` is the identity in `ℝ` on nonnegative integers.  This is the only bridge between
the `.toNat` casts of the source displays and the paper's ℤ-differences. -/
theorem cast_toNat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = (n : ℤ) := ⟨z.toNat, (Int.toNat_of_nonneg hz).symm⟩
  simp

/-- The running record is nonnegative identically, so `M_n^j` may be read through `Int.toNat`
without a carrier hypothesis. -/
theorem cast_runMax (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    ((runMax p m U j n).toNat : ℝ) = ((runMax p m U j n : ℤ) : ℝ) :=
  cast_toNat_of_nonneg (zero_le_runMax p m U j n)

/-! ## 2. Nonnegativity of the positions on the record window

This is the one cast that is not free: `M_s^i - X_s^i` needs `X_s^i >= 0`.  On the paper's carrier
`{d_r <= L}` the record hypothesis `RecHyp` holds at `tau_r` and the unit-step geometry confines
every position in `[tau_r, tau_r + T*L]` to `[r - (T+1)L, r + T*L]`; since `r >= (T+3)L` this is at
least `2L >= 0`.  Nothing is assumed about the walkers beyond `recordCarrier`. -/

theorem pos_nonneg_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r) {s : ℕ} (hs : recTimeA p m U r ≤ s)
    (hst : s ≤ recTimeA p m U r + T * L) (i : Fin N) :
    (0 : ℤ) ≤ (trajectory p m U s).pos i := by
  have hrec : LocGroupSimul.RecHyp p m r (recTimeA p m U r) L U :=
    RecClockLG.recHyp_at_record (N := N) hcarr
  have hge := LocGroupSimul.RecHyp_pos_ge (p := p) (m := m) (T := T) hrec hs hst i
  -- `(T+1) * L <= (T+3) * L <= r`, so the lower bound `r - (T+1)L` is `>= 2L >= 0`.
  have hcast : (((T + 1) * L : ℕ) : ℤ) ≤ (r : ℤ) := by
    have : (T + 1) * L ≤ r := le_trans (Nat.mul_le_mul_right L (by omega)) hr
    exact_mod_cast this
  have hL : (0 : ℤ) ≤ (L : ℤ) := by positivity
  have hsplit : (((T + 1) * L : ℕ) : ℤ) = (L : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h : ((T + 1) * L : ℕ) = L + T * L := by ring
    rw [h]; push_cast; ring
  linarith

/-- The `X_s^i` cast identity on the record window. -/
theorem cast_pos_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r) {s : ℕ} (hs : recTimeA p m U r ≤ s)
    (hst : s ≤ recTimeA p m U r + T * L) (i : Fin N) :
    ((((trajectory p m U s).pos i).toNat : ℕ) : ℝ) = (((trajectory p m U s).pos i : ℤ) : ℝ) :=
  cast_toNat_of_nonneg (pos_nonneg_of_carrier hcarr hr hs hst i)

/-! ## 3. The paper's `(lococc)` display in its literal shape -/

/-- The paper's `(lococc)` display at an arbitrary pair of display times
`tau_r <= s <= t <= tau_r + TL`, with the record-dependent right-hand side written with the
paper's ℤ-differences, coefficient `Kocc p m C` and additive remainder `CTocc p m C T * L^{3/4}`. -/
def occDisplayAllStartsPaper (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
    U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
    U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0 →
    ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
        ≤ LocOccPaperScale.Kocc p m C *
            ((((runMax p m U q.1 t : ℤ) : ℝ) - ((runMax p m U q.1 s : ℤ) : ℝ))
              + (((runMax p m U q.1 s : ℤ) : ℝ) - (((trajectory p m U s).pos q.1 : ℤ) : ℝ))
              + max 0 (((runMax p m U q.1 s : ℤ) : ℝ) - ((runMax p m U q.2 s : ℤ) : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + LocOccPaperScale.CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ))

/-- The record-start collapsed form of the same display, in the paper's shape. -/
def occDisplayTLPaper (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
    U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
    U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0 →
    ∀ t : ℕ, s0 ≤ t → t ≤ s0 + T * L →
      ∑ u ∈ Finset.Ico s0 t,
          (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
        ≤ LocOccPaperScale.Kocc p m C * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s0 : ℝ)) / 8
          + LocOccPaperScale.CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ))

/-- Both display forms at the fibre `s0`, in the paper's shape. -/
def occFacePaper (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  occDisplayAllStartsPaper p m C r T L s0 U ∧ occDisplayTLPaper p m C r T L s0 U

/-! ## 4. The conversions -/

/-- The coefficient in front of `L34` is nonnegative. -/
theorem L34coef_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ}
    (hC1 : 1 ≤ C) :
    (0 : ℝ) ≤ 2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
      + 4 / (1 - aRec p m) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have h1 := KFc_nonneg hp1 hp2 m
  have h2 := CJc_nonneg hp1 hp2 m
  have h3 := one_sub_aRec_pos hp1 hp2 m
  have h4 : (0 : ℝ) ≤ 4 / (1 - aRec p m) := by positivity
  nlinarith

/-- `L34 L (Lw T L)` at the paper's scale, with exactly the coefficient that occurs in the display:
the additive remainder `coef * L34 L (Lw T L)` is at most `CTocc p m C T * L^{3/4}`. -/
theorem L34_le_CTocc {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ}
    (hC1 : 1 ≤ C) (T : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1 + 4 / (1 - aRec p m))
        * L34 L (Lw T L)
      ≤ LocOccPaperScale.CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ)) := by
  have h0 := L34coef_nonneg (m := m) hp1 hp2 hC1
  have hle := L34PaperScale.L34_Lw_le_rpow34 T hL
  have hmul := mul_le_mul_of_nonneg_left hle h0
  refine le_trans hmul (le_of_eq ?_)
  simp only [LocOccPaperScale.CTocc]
  ring

/-- **The arbitrary-start form in the paper's shape**, from the `.toNat` form plus nonnegativity of
the positions on the display window.  No carrier is used here: the window positivity is the
hypothesis, and `cast_runMax` handles the records unconditionally. -/
theorem occDisplayAllStartsPaper_of_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {C : ℝ} (hC1 : 1 ≤ C) {r T L s0 : ℕ} {U : Array N}
    (h : OccDisplayNull.occDisplayAllStarts p m C r T L s0 U)
    (hpos : ∀ (i : Fin N) (s : ℕ), s0 ≤ s → s ≤ s0 + T * L →
      (0 : ℤ) ≤ (trajectory p m U s).pos i)
    (hL : 1 ≤ L) :
    occDisplayAllStartsPaper (N := N) p m C r T L s0 U := by
  intro q hq hband hgood s t h1 h2 h3
  have hmain := h q hq hband hgood s t h1 h2 h3
  -- the record-dependent combination, in the two shapes
  have hkey :
      ((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ)
        + (((runMax p m U q.1 s).toNat : ℝ) - (((trajectory p m U s).pos q.1).toNat : ℝ))
        + max 0 (((runMax p m U q.1 s).toNat : ℝ) - ((runMax p m U q.2 s).toNat : ℝ))
      = (((runMax p m U q.1 t : ℤ) : ℝ) - ((runMax p m U q.1 s : ℤ) : ℝ))
        + (((runMax p m U q.1 s : ℤ) : ℝ) - (((trajectory p m U s).pos q.1 : ℤ) : ℝ))
        + max 0 (((runMax p m U q.1 s : ℤ) : ℝ) - ((runMax p m U q.2 s : ℤ) : ℝ)) := by
    rw [cast_runMax p m U q.1 t, cast_runMax p m U q.1 s, cast_runMax p m U q.2 s,
      cast_toNat_of_nonneg (hpos q.1 s h1 (le_trans h2 h3))]
  have hcoef : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) = LocOccPaperScale.Kocc p m C := rfl
  have hrem : (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1 + 4 / (1 - aRec p m))
      * L34 L (Lw T L) ≤ LocOccPaperScale.CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ)) :=
    L34_le_CTocc hp1 hp2 hC1 T hL
  rw [hkey, hcoef] at hmain
  linarith [hmain, hrem]

/-- **The paper's `(lococc)`, arbitrary-start form, on the record carrier** at the literal record
fibre: the positions on `[tau_r, tau_r + T*L]` are nonnegative by `pos_nonneg_of_carrier`. -/
theorem occDisplayAllStartsPaper_of_carrier {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {C : ℝ} (hC1 : 1 ≤ C) {r T L : ℕ} {U : Array N}
    (h : OccDisplayNull.occDisplayAllStarts p m C r T L (recTimeA p m U r) U)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r) (hL : 1 ≤ L) :
    occDisplayAllStartsPaper (N := N) p m C r T L (recTimeA p m U r) U :=
  occDisplayAllStartsPaper_of_pos hp1 hp2 hC1 h
    (fun i s hs hst => pos_nonneg_of_carrier hcarr hr hs hst i) hL

/-- **The record-start collapsed form in the paper's shape.**  This form contains no position cast,
so only the `L34` remainder has to be converted; no carrier hypothesis is needed. -/
theorem occDisplayTLPaper_of_toNat {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {C : ℝ} (hC1 : 1 ≤ C) {r T L s0 : ℕ} {U : Array N}
    (h : OccDisplayNull.occDisplayTL p m C r T L s0 U) (hL : 1 ≤ L) :
    occDisplayTLPaper (N := N) p m C r T L s0 U := by
  intro q hq hband hgood t h1 h2
  have hmain := h q hq hband hgood t h1 h2
  have hcoef : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) = LocOccPaperScale.Kocc p m C := rfl
  have hrem : (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1 + 4 / (1 - aRec p m))
      * L34 L (Lw T L) ≤ LocOccPaperScale.CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ)) :=
    L34_le_CTocc hp1 hp2 hC1 T hL
  rw [hcoef] at hmain
  linarith [hmain, hrem]

/-- The two-form conversion at the literal record fibre. -/
theorem occFacePaper_of_carrier {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {C : ℝ} (hC1 : 1 ≤ C) {r T L : ℕ} {U : Array N}
    (h : OccDisplayNull.occFace p m C r T L (recTimeA p m U r) U)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r) (hL : 1 ≤ L) :
    occFacePaper (N := N) p m C r T L (recTimeA p m U r) U :=
  ⟨occDisplayAllStartsPaper_of_carrier hp1 hp2 hC1 h.1 hcarr hr hL,
    occDisplayTLPaper_of_toNat hp1 hp2 hC1 h.2 hL⟩

/-! ## 5. The paper-shape display off the finite-family bad event -/

/-- **`(lococc)` in the paper's literal shape, off `famBad`, at `tau_r`.**  The occupation null event
is inside `LocalGoodFamily.famBad`, so the display is pointwise; `recordCarrier` supplies the
nonnegativity of the positions through `pos_nonneg_of_carrier`.  The coefficient of the
record-dependent combination is `Kocc p m (Ccan p m)` and the error `CTocc p m (Ccan p m) T`. -/
theorem familyGood_lococcPaper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    occFacePaper (N := N) p m (LocOccSiteRate.Ccan p m) r T L (recTimeA p m U r) U :=
  occFacePaper_of_carrier hp1 hp2 (LocOccSiteRate.one_le_Ccan p m)
    (LocalGoodFamily.familyGood_lococc (N := N) hcarr h) hcarr hr hL

/-- **The paper's `(lococc)` inequality itself on the family event**, with every fibre hypothesis
discharged.  For every ordered pair of distinct walkers and every
`tau_r <= s <= t <= tau_r + T*L`, on `recordCarrier` and off `famBad`, the occupation sum obeys the
paper's bound with `C = Kocc p m (Ccan p m)` and `C_T = CTocc p m (Ccan p m) T`.  The fibre
membership is `recordBand_self` and `familyGood_goodWin`, not a hypothesis. -/
theorem familyGood_lococcPaper_expanded {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (q : Fin N × Fin N), q ∈ offDiag (N := N) →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
          ≤ LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m) *
              ((((runMax p m U q.1 t : ℤ) : ℝ) - ((runMax p m U q.1 s : ℤ) : ℝ))
                + (((runMax p m U q.1 s : ℤ) : ℝ) - (((trajectory p m U s).pos q.1 : ℤ) : ℝ))
                + max 0 (((runMax p m U q.1 s : ℤ) : ℝ) - ((runMax p m U q.2 s : ℤ) : ℝ)))
            + ((t : ℝ) - (s : ℝ)) / 8
            + LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T * ((L : ℝ) ^ (3 / 4 : ℝ)) := by
  intro q hq s t h1 h2 h3
  have hband : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r (recTimeA p m U r) L :=
    OccDisplayNull.recordBand_self (N := N) hcarr
  have hgood : U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
      (LocOccSiteRate.Ccan p m) r T L (recTimeA p m U r) :=
    LocalGoodFamily.familyGood_goodWin (N := N) h (recTimeA p m U r) hband
  exact (familyGood_lococcPaper hp1 hp2 hL hr hcarr h).1 q hq hband hgood s t h1 h2 h3

/-- The record-start collapsed form of the same, with every fibre hypothesis discharged. -/
theorem familyGood_lococcPaperTL_expanded {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (q : Fin N × Fin N), q ∈ offDiag (N := N) →
      ∀ t : ℕ, recTimeA p m U r ≤ t → t ≤ recTimeA p m U r + T * L →
        ∑ u ∈ Finset.Ico (recTimeA p m U r) t,
            (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
          ≤ LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m)
              * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
            + ((t : ℝ) - ((recTimeA p m U r : ℕ) : ℝ)) / 8
            + LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T * ((L : ℝ) ^ (3 / 4 : ℝ)) := by
  intro q hq t h1 h2
  have hband : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r (recTimeA p m U r) L :=
    OccDisplayNull.recordBand_self (N := N) hcarr
  have hgood : U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
      (LocOccSiteRate.Ccan p m) r T L (recTimeA p m U r) :=
    LocalGoodFamily.familyGood_goodWin (N := N) h (recTimeA p m U r) hband
  exact (familyGood_lococcPaper hp1 hp2 hL hr hcarr h).2 q hq hband hgood t h1 h2

/-! ## 6. `(locmart)` reindexed to arbitrary `s <= t` in the record window (`C_T = 1`) -/

/-- **`(locmart)` at the actual record clock, arbitrary endpoints.**  `RecordClock.locMartGood_spec`
is stated with `s ↦ tau_r + s` and `t ↦ tau_r + s + k`; this is the reindexing to arbitrary
`tau_r <= s <= t <= tau_r + T*L`.  The constant is `C_T = 1`, as in `locMartGood_spec`. -/
theorem locMartGood_paper {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hU : U ∈ RecordClock.locMartGood (N := N) p m r T L) :
    ∀ (i : Fin N) (s t : ℕ), recTimeA p m U r ≤ s → s ≤ t →
      t ≤ recTimeA p m U r + T * L →
      |driftMartingale p m U t i - driftMartingale p m U s i| ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  intro i s t h1 h2 h3
  have hs : s - recTimeA p m U r ≤ T * L := by omega
  have hk : t - s ≤ T * L - (s - recTimeA p m U r) := by omega
  have h := RecordClock.locMartGood_spec hU i (s - recTimeA p m U r) (t - s) hs hk
  have e1 : recTimeA p m U r + (s - recTimeA p m U r) + (t - s) = t := by omega
  have e2 : recTimeA p m U r + (s - recTimeA p m U r) = s := by omega
  rw [e1, e2] at h
  exact h

/-- The same off the finite-family bad event. -/
theorem familyGood_locmartPaper {p : ℝ} {m : ℕ} {Cerr : ℝ}
    {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (i : Fin N) (s t : ℕ), recTimeA p m U r ≤ s → s ≤ t →
      t ≤ recTimeA p m U r + T * L →
      |driftMartingale p m U t i - driftMartingale p m U s i| ≤ (L : ℝ) ^ ((3 : ℝ) / 4) :=
  locMartGood_paper (LocalGoodFamily.familyGood_locmart (N := N) h)

/-! ## 7. Inside the family headline -/

/-- **The finite-family local-good event with the paper-shape occupation display.**  This is
`LocalGoodFamily.exists_famBad_and_good` with its `occFace` clause and its `(locmart)` clause
replaced by their paper-shape versions (`Kocc`/`CTocc`, honest ℤ casts, arbitrary `s <= t`).  The
bad-event bound is unchanged: the conversion is deterministic. -/
theorem exists_famBad_and_lococcPaper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧
      (∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
        ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
          (arrayMeasure N).real
              (LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
            ≤ CT * LocalGoodAll.exf cT L) ∧
      (∃ Lg : ℕ, ∀ L ≥ Lg, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
        occFacePaper (N := N) p m (LocOccSiteRate.Ccan p m) r T L (recTimeA p m U r) U ∧
          (∀ (q : Fin N × Fin N), q ∈ offDiag (N := N) →
            ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
              ∑ u ∈ Finset.Ico s t,
                  (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
                ≤ LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m) *
                    ((((runMax p m U q.1 t : ℤ) : ℝ) - ((runMax p m U q.1 s : ℤ) : ℝ))
                      + (((runMax p m U q.1 s : ℤ) : ℝ)
                          - (((trajectory p m U s).pos q.1 : ℤ) : ℝ))
                      + max 0 (((runMax p m U q.1 s : ℤ) : ℝ)
                          - ((runMax p m U q.2 s : ℤ) : ℝ)))
                + ((t : ℝ) - (s : ℝ)) / 8
                + LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T * ((L : ℝ) ^ (3 / 4 : ℝ))) ∧
          (∀ (i : Fin N) (s t : ℕ), recTimeA p m U r ≤ s → s ≤ t →
            t ≤ recTimeA p m U r + T * L →
            |driftMartingale p m U t i - driftMartingale p m U s i|
              ≤ (L : ℝ) ^ ((3 : ℝ) / 4))) := by
  obtain ⟨Cerr, hCerr, hbound, Lg, hgood⟩ :=
    LocalGoodFamily.exists_famBad_and_good (N := N) hp0 hp1 hm hT hN moveFam hne hco
      grpFam hI hJ hdisj
  refine ⟨Cerr, hCerr, hbound, max Lg 1, ?_⟩
  intro L hL r hr U hcarr hnot
  have hLg : Lg ≤ L := le_trans (le_max_left Lg 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right Lg 1) hL
  exact ⟨familyGood_lococcPaper hp0 hp1 hL1 hr hcarr hnot,
    familyGood_lococcPaper_expanded hp0 hp1 hL1 hr hcarr hnot,
    familyGood_locmartPaper hnot⟩

end OccPaperPointwise
