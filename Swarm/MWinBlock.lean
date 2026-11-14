/-
# Proposition `local` as `BlkCoin.BlockClauses` at `Cfin`, on the windowed move carrier

`PaperBlock.paper_local_clauses` bundles the paper-local clauses `hmono`, `hunit`, `hcoord`,
`wmove`, `hocc` and `group` into `BlkCoin.BlockClauses` at the common coefficient
`Cfin = max paperC Cocc`, conditional on two explicit premises: the `(lococc)` clause `LocOcc`,
and the `(locmove)` good-window carrier `PaperBlock.MoveCarrier` (whose `W`-conjunct is the
*prefix* envelope `GoodW`, refuted on explicit trajectories).

This file replaces that premise by the windowed one:

* `MoveCarrierWinTrunc` — the windowed move carrier: `ambGood`, the windowed good event
  `LocGroupSimul.winTrunc` (`GoodWWin` at level `Aw` plus positions `≥ Aw+1`) and `GoodStep`;
* `moveCarrierWinTrunc_of_win` — its producer from `ambGoodAll`, the measured `GoodWWin`
  windows and the record-geometry position bound;
* `paper_local_clauses_win` — **`BlkCoin.BlockClauses` at `Cfin`**, with the same `univBad`
  exponential profile, the same `Cerr`, `CT`, `cT`, `L₀`, the same `(lococc)` input, and with
  the movement residual now split into (a) the windowed carrier and (b) the single measured
  statement `U ∉ locMoveFailAtClockWin` for every group, whose probability is exactly
  `MWin.measureReal_locMoveFailAtClockWin_le`.

`hmono`, `hunit`, `hcoord`, `group` are `PaperBlock`'s and do not involve the move carrier.
Nothing here estimates the good event, the carrier, `(loccoord)`, `(lococc)`, `(locsum)`,
`(locgroup)`, the block/half profiles, tightness, coalescence, regeneration or the speed.
-/
import Swarm.MWinPaper

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

/-- **The windowed move carrier in `winTrunc` form**: on every separated window of the record
window, `ambGood` holds, the windowed truncation event holds at every time, and `GoodStep` holds
at every time.  The `W`-conjunct is `LocGroupSimul.winTrunc`, i.e. the level-window envelope plus
the recorded position bound — not the prefix envelope `GoodW`. -/
def MoveCarrierWinTrunc (p : ℝ) (m r T L Aw : ℕ) (U : Array N) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ → ∀ s t : ℕ,
    recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (PaperBlock.Xa p m U) A Aᶜ u) →
    U ∈ ambGood p m hA (r : ℤ) T L ∧
      (∀ n ∈ Finset.Ico s t,
        LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) ∧
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U)

/-- Producer for the `winTrunc`-form carrier, from `MWin.MoveCarrierWinStep`. -/
theorem moveCarrierWinTrunc_of_win {p : ℝ} {m r T L Aw : ℕ} {U : Array N}
    (h : MoveCarrierWinStep (N := N) p m r T L Aw U) :
    MoveCarrierWinTrunc (N := N) p m r T L Aw U := by
  intro A hA hne s t hs hst ht hsep
  obtain ⟨hamb, hwin, hpos, hstep⟩ := h A hA hne s t hs hst ht hsep
  exact ⟨hamb, fun n hn => winTrunc_of_goodWWin (hwin n hn) (hpos n hn), hstep⟩

/-- **Proposition `local`, in the tightness lane's clause shapes, off the single universal bad
event — with the windowed move carrier.**

Same `Cerr`, `CT`, `cT`, `L₀`, same `univBad` profile, same `(lococc)` input and same common
coefficient `Cfin` as `PaperBlock.paper_local_clauses`; the `(locmove)` good-window premise is now

* `MoveCarrierWinTrunc` (the measured windowed carrier), and
* `U ∉ locMoveFailAtClockWin` for every group `A` — the windowed `(locmove)` failure event whose
  measure is bounded by `MWin.measureReal_locMoveFailAtClockWin_le`. -/
theorem paper_local_clauses_win {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        LocalFluid.LocOcc (Xa p m U) (tauA p m U)
            (Cfin (N := N) p m) (CTtot p m T Cerr) T L r →
        ∀ (Aw : ℕ) (geom : ℕ → ℕ → Set (Array N)),
          (∀ s t : ℕ, s ≤ t → U ∈ geom s t) →
          MoveCarrierWinTrunc (N := N) p m r T L Aw U →
          (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
            U ∉ {U' : Array N | locMoveFailAtClockWin p m A hA hAc r T L
              (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
              (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) geom Aw U'}) →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
            (Cfin (N := N) p m) (CTtot p m T Cerr) T L r) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max L₀ 1, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left L₀ 1) hL) r hr
  · intro L hL r hr U hcarr hnot hocc Aw geom hgeom hcarrW hnotbad
    have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
    have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
    obtain ⟨-, -, -, -, -, -, hlocgroup, hsum⟩ := hgood L hL₀ r hr U hcarr hnot
    -- `hmono`, `hunit`
    have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        Hc p m U A n x ≤ Hc p m U A n y :=
      fun A n _ _ hxy => Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        y - x ≤ Hc p m U A n y - Hc p m U A n x :=
      fun A n _ _ hxy => Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    -- `(loccoord)`
    have hcoord : ∀ (A : Finset (Fin N)) (n : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ n → n ≤ tauA p m U r + T * L → ∀ a0 b0 : ℤ,
        (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
        b0 ≤ Glue.sMaxM (Xa p m U) A n →
        ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
          ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
            + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A n hA _ h1 h2 a0 b0 ha hab hb
      exact hcoord_clause_fin (N := N) hp0 hp1 hL1 hr hcarr hsum hCerr1 A hA n h1 h2 a0 b0 ha hab hb
    -- `(locmove)`
    have hwmove : ∀ (A : Finset (Fin N)) (s t : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
        (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A (Finset.univ \ A) u) →
        Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
            - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
          ≤ Cfin (N := N) p m
              * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
            - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
            + CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A s t hAn hAn' hs hst ht hsep
      have hAc : Aᶜ.Nonempty := by
        rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hAn'
      have hmove := hmove_win_of_not_mem (p := p) (m := m) (A := A) (hA := hAn) (hAc := hAc)
        (r := r) (T := T) (L := L) (Cerr := Cerr) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
        (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (Aw := Aw) (geom := geom) hcarr
        (hnotbad A hAn hAc) (pin_of_carrier (N := N) hcarr hAn) hgeom
      exact wmove_clause_win_fin (N := N) hp0 hp1 hL1 (Cerr := Cerr) hAn hAc
        (Aw := Aw) hmove s t hs hst ht
        (hcarrW A hAn hAn' s t hs hst ht hsep).1
        (hcarrW A hAn hAn' s t hs hst ht hsep).2.1
        (hcarrW A hAn hAn' s t hs hst ht hsep).2.2
    exact ⟨⟨hmono, hunit, hcoord, hwmove, hocc⟩,
      fun I J hdisj hI hJ => group_clause hL1 hcarr hr hlocgroup I J hdisj hI hJ⟩

/-! ## Axiom audit -/


end MWin
