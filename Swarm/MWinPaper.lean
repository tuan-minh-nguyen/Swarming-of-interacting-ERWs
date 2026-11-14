/-
# Display `(locmove)` at the paper's constants from the windowed move carrier

`PaperBlock.wmove_clause` proves the paper's `(locmove)` inequality at the `T`-free coefficient
`paperC` and the single error coefficient `CTtot`, from the paper good window whose `W`-conjunct is
the *prefix* envelope `LocGroupQ.GoodW`.  `MWinMove`/`MWinClock` replace that conjunct by the
*windowed* one (`SiteWindow.GoodWWin` at level `Aw` together with positions `≥ Aw+1`), with the same
error constants.  This file records the resulting block/local clause at `CTtot` and the carrier
that produces it.

* `MoveCarrierWinStep` — `PaperBlock.MoveCarrier` with the prefix envelope replaced by
  (`GoodWWin` at level `Aw`, positions `≥ Aw+1`, `GoodStep`); it is strictly weaker than the
  refuted `PaperBlock.MoveCarrier`.
* `moveCarrierWinStep_of_win` — its producer: `Swarming.Enl.ambGoodAll`, the measured
  `GoodWWin` windows of `CarrierWin.MoveCarrierWin` and the record-geometry position bound.
* `winTrunc_of_goodWWin` — the carrier window *is* `LocGroupSimul.winTrunc`.
* `wmove_of_not_mem` — off the windowed `(locmove)` failure event of `MWinClock`, the display holds
  on every window on which the windowed good window is available.
* `wmove_clause_win` — the paper's `(locmove)` at `paperC` and `CTtot` from that windowed input.

Nothing probabilistic is added: the failure event's own measure bound is
`MWin.measureReal_locMoveFailAtClockWin_le`.  The `(loccoord)`/`(lococc)`/`(locsum)`/`(locgroup)`
inputs and the record-geometry position bound remain explicit, as in the prefix version.
-/
import Swarm.MWinClock
import Swarm.PaperBlock
import Swarm.LocCoordGeomCarrier
import Swarm.CarrierWindowRepair

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace MWin

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The windowed move carrier -/

/-- **The windowed move carrier.**  `PaperBlock.MoveCarrier` with the prefix envelope `GoodW`
replaced by the level-window event `SiteWindow.GoodWWin` at level `Aw`, the recorded position bound
`Aw + 1 ≤ X_n^k`, and the one-step bound `GoodStep`.  The prefix conjunct of `MoveCarrier` is
refuted on explicit trajectories (`MoveCarrierObstruction.not_moveCarrier`); this one is the shape
`CarrierWin.MoveCarrierWin` plus the position bound that `moveCarrierWin_of_win` keeps separate. -/
def MoveCarrierWinStep (p : ℝ) (m r T L Aw : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    U ∈ ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t, SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) ∧
      (∀ n ∈ Finset.Ico s t, ∀ k : Fin N, Aw + 1 ≤ (X p m U n k).toNat) ∧
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U)

/-- **Producer for the windowed move carrier.**  The residuals are exactly the measured ambient
event `ambGoodAll`, the measured `SiteWindow.GoodWWin` windows, the record-geometry position bound
and the one-step bound `GoodStep`; no below-window information is needed. -/
theorem moveCarrierWinStep_of_win {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L Aw : ℕ} (hAlo : 1 ≤ Aw) {U : Array N}
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hwin : ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
      ∀ n ∈ Finset.Ico s t,
        SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U)
    (hposAll : ∀ n : ℕ, recTimeA p m U r ≤ n → n ≤ recTimeA p m U r + T * L →
      ∀ k : Fin N, Aw + 1 ≤ (X p m U n k).toNat) :
    MoveCarrierWinStep (N := N) p m r T L Aw U := by
  intro A hA hne s t hs hst ht hsep
  have hAc : Aᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hnil
    exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
  refine ⟨MoveStep.ambGood_of_ambGoodAll hA hAc hamb,
    fun n hn => hwin A hA hne s t hs hst ht hsep n hn, ?_, ?_⟩
  · intro n hn
    exact hposAll n (le_trans hs (Finset.mem_Ico.mp hn).1)
      (le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht)
  · intro n hn
    have hn1 : recTimeA p m U r ≤ n := le_trans hs (Finset.mem_Ico.mp hn).1
    have hn2 : n ≤ recTimeA p m U r + T * L :=
      le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht
    exact CarrierWin.goodStep_of_goodWWin hp0.le hp1.le hA hAlo
      (hwin A hA hne s t hs hst ht hsep n hn)
      (fun j _ => by have := hposAll n hn1 hn2 j; omega)

/-- The carrier window is the windowed truncation event of `LocGroupSimul`. -/
theorem winTrunc_of_goodWWin {p : ℝ} {m n : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {B : ℝ} {Aw : ℕ} {U : Array N}
    (h : SiteWindow.GoodWWin p m n A Aᶜ hA B Aw U)
    (hpos : ∀ k : Fin N, Aw + 1 ≤ (X p m U n k).toNat) :
    winTrunc p m n A Aᶜ hA B Aw U := ⟨h, hpos⟩

/-! ## 2. The display off the windowed `(locmove)` failure event -/

/-- **Off the windowed `(locmove)` failure event the display holds**, on every window of the
`TL`-record window on which the windowed good window is available.  This is the windowed
counterpart of `LocalGoodFamily.not_mem_moveBadCommon`. -/
theorem wmove_of_not_mem {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hAc : Aᶜ.Nonempty} {r T L : ℕ} {B C β ε₁ ε₂ : ℝ} {Aw : ℕ}
    {geom : ℕ → ℕ → Set (Array N)} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hU : U ∉ {U : Array N |
      locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U})
    {s t : ℕ} (hclk : recTimeA p m U r ≤ s) (hst : s ≤ t)
    (ht : t ≤ recTimeA p m U r + T * L)
    (hgood : locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw (recTimeA p m U r) s t U)
    (hgeom : U ∈ geom s t) :
    WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
      ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U := by
  by_contra hcon
  refine hU ⟨hcarr, s, t, hclk, hst, ?_, hgood, hgeom, hcon⟩
  have hmul : T * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
  omega

/-! ## 3. The paper's `(locmove)` at `paperC` and `CTtot`, from the windowed window -/

/-- **The paper's `(locmove)`** at the `T`-free coefficient `paperC` and the single error
coefficient `CTtot`, in the shape of `JoinStep.LocalClauses.wmove` at the integer potential `Hc`,
with the paper's window `[τ_r, τ_r+TL]` and the source's half-open time set `[s,t)` — with the
**windowed** good window in place of `GoodW`.

This is `PaperBlock.wmove_clause` with the three good-window requirements
(`ambGood`, windowed envelope, `GoodStep`) instead of (`ambGood`, `GoodW`, `GoodStep`); the
conclusion and both constants are unchanged. -/
theorem wmove_clause_win {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Array N} (hL : 1 ≤ L) {Cerr : ℝ}
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {Aw : ℕ}
    (hmove : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m hA (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t,
        LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U)
    (s t : ℕ) (hs : tauA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ tauA p m U r + T * L)
    (hamb : U ∈ ambGood p m hA (r : ℤ) T L)
    (hW : ∀ n ∈ Finset.Ico s t,
      LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U)
    (hstep : ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) :
    Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
        - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
      ≤ LocMovePaper.paperC (N := N) p m
          * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
        - ((t - s : ℕ) : ℝ) / LocMovePaper.paperC (N := N) p m
        + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hs' : recTimeA p m U r ≤ s := hs
  have ht' : t ≤ recTimeA p m U r + T * L := ht
  have hmain := hmove s t hs' hst ht' hamb hW hstep
  have hpaper := LocMovePaper.locmoveRHS_le_paperMoveRHS (N := N) hp0 hp1 (m := m) (T := T)
    A hA hL (Cerr := Cerr) s t U
  have hAcA : (Aᶜ)ᶜ = A := by ext i; simp
  have hWt : Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
      ≤ WA p m U t A Aᶜ hA hAc + 1 := by
    rw [Wst_eq_Wpot]
    have h := Wpot_le_WA_add_one (N := N) p m U A Aᶜ hA hAc t
    rwa [hAcA] at h
  have hWs : WA p m U s A Aᶜ hA hAc - 1
      ≤ Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s := by
    rw [Wst_eq_Wpot]
    have h := WA_sub_one_le_Wpot (N := N) p m U A Aᶜ hA hAc s
    rwa [hAcA] at h
  have hmax : Glue.sMaxM (Xa p m U) A s = runMaxA p m U hA s := sMaxM_eq_runMaxA p m U A hA s
  have hmin : Glue.sMin (Xa p m U) A s = Xmin p m U A hA s := sMin_eq_Xmin p m U A hA s
  have hL34 : (1 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := one_le_L34 hL
  have hCT : LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) + 2
      ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h2 : LocMovePaper.paperCT m Cerr + 2 ≤ CTtot p m T Cerr :=
      paperCT_add_two_le_CTtot p m T Cerr
    have h0 : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) := lt_of_lt_of_le zero_lt_one hL34
    calc LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) + 2
        ≤ LocMovePaper.paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)
            + 2 * (L : ℝ) ^ ((3 : ℝ) / 4) := by linarith
      _ = (LocMovePaper.paperCT m Cerr + 2) * (L : ℝ) ^ ((3 : ℝ) / 4) := by ring
      _ ≤ CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right h2 h0.le
  rw [hmax, hmin]
  unfold LocMovePaper.paperMoveRHS at hpaper
  linarith


/-! ## 4. The pin, the assembled good window, and the common coefficient `Cfin` -/

/-- The level pin of the windowed good window is a consequence of the record carrier
(`LocCoordGeomCarrier.locmoveGood_pin`), so a consumer never has to prove it. -/
theorem pin_of_carrier {p : ℝ} {m r L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) {A : Finset (Fin N)}
    (hA : A.Nonempty) :
    (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hA (recTimeA p m U r) ∧
      runMaxA p m U hA (recTimeA p m U r) ≤ (r : ℤ) :=
  LocCoordGeomCarrier.locmoveGood_pin (N := N) hcarr hA

/-- The windowed good window, assembled from its four pieces. -/
theorem locmoveGoodWin_of {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {r : ℤ}
    {Th Lh : ℕ} {B : ℝ} {Aw n0 s t : ℕ} {U : Array N}
    (hamb : U ∈ ambGood p m hA r Th Lh)
    (hW : ∀ n ∈ Finset.Ico s t, winTrunc p m n A Aᶜ hA B Aw U)
    (hstep : ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U)
    (hpin : r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) :
    locmoveGoodWin (N := N) p m A hA r Th Lh B Aw n0 s t U :=
  ⟨hamb, hW, hstep, hpin⟩

/-- The `∀`-form windowed `(locmove)` input of `wmove_clause_win`, derived from the windowed
failure event and the record carrier.  The residual is the `(loccoord)` geometric window
membership, which is the carrier's own content. -/
theorem hmove_win_of_not_mem {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hAc : Aᶜ.Nonempty} {r T L : ℕ} {Cerr ε₁ ε₂ : ℝ} {Aw : ℕ}
    {geom : ℕ → ℕ → Set (Array N)} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hU : U ∉ {U : Array N | locMoveFailAtClockWin p m A hA hAc r T L
      (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr) ε₁ ε₂ geom Aw U})
    (hpin : (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hA (recTimeA p m U r) ∧
      runMaxA p m U hA (recTimeA p m U r) ≤ (r : ℤ))
    (hgeom : ∀ s t : ℕ, s ≤ t → U ∈ geom s t) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m hA (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t,
        LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr) ε₁ ε₂ s t U := by
  intro s t hs hst ht hamb hW hstep
  exact wmove_of_not_mem (p := p) (m := m) (A := A) (hA := hA) (hAc := hAc) hcarr hU hs hst ht
    (locmoveGoodWin_of (p := p) (m := m) (A := A) (hA := hA) (r := (r : ℤ)) (Th := T) (Lh := L)
      (B := RecClockLG.Bstar L) (Aw := Aw) (n0 := recTimeA p m U r) (s := s) (t := t)
      (U := U) hamb hW hstep hpin)
    (hgeom s t hst)

/-- **The paper's `(locmove)` at the common coefficient `Cfin`**, from the windowed good window.
The coefficient transfer `paperC → Cfin` is `PaperBlock.paper_local_clauses`'s, applied to the
`paperC` form `wmove_clause_win`. -/
theorem wmove_clause_win_fin {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Array N} (hL : 1 ≤ L) {Cerr : ℝ}
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {Aw : ℕ}
    (hmove : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m hA (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t,
        LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U)
    (s t : ℕ) (hs : tauA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ tauA p m U r + T * L)
    (hamb : U ∈ ambGood p m hA (r : ℤ) T L)
    (hW : ∀ n ∈ Finset.Ico s t,
      LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U)
    (hstep : ∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) :
    Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
        - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
      ≤ Cfin (N := N) p m
          * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
        - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
        + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hpc := wmove_clause_win (N := N) hp0 hp1 (m := m) (r := r) (T := T) (L := L)
    (U := U) hL (A := A) hA hAc (Aw := Aw) hmove s t hs hst ht hamb hW hstep
  obtain ⟨i0, hi0⟩ := hA
  have hspread : (0 : ℝ) ≤
      ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) := by
    have h5 : Glue.sMin (Xa p m U) A s ≤ Glue.sMaxM (Xa p m U) A s :=
      le_trans (Glue.sMin_le (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0)
        (le_trans (le_runMaxI p m U i0 s)
          (Glue.le_sMaxM (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0))
    have h6 : ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) ≤ ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) :=
      Int.cast_le.mpr h5
    linarith
  have hCpc : (0 : ℝ) < LocMovePaper.paperC (N := N) p m := LocMovePaper.paperC_pos (N := N) p m
  have hCmono := paperC_le_Cfin (N := N) p m
  have e1 : LocMovePaper.paperC (N := N) p m
        * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
      ≤ Cfin (N := N) p m
        * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hCmono hspread
  have e2 : ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
      ≤ ((t - s : ℕ) : ℝ) / LocMovePaper.paperC (N := N) p m :=
    div_le_div_of_nonneg_left (by positivity) hCpc hCmono
  linarith


end MWin
