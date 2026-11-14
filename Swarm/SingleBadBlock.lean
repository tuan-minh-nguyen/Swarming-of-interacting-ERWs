/-
# The paper's local block clauses off **one** measured bad event

`MWin.paper_local_clauses_win` produces `BlkCoin.BlockClauses` at `Cfin` off
`UniversalFamily.univBad`, but keeps three premises besides the record carrier:

* the `(lococc)` display `LocalFluid.LocOcc …` at `CTtot`,
* the windowed move carrier `MWin.MoveCarrierWinTrunc …` (whose production needs the *separate*
  measured ambient event `Swarming.Enl.ambGoodAll`), and
* the per-group windowed `(locmove)` failure event.

This file removes the first two premises and keeps only measured objects:

* the bad event becomes the **single** `SingleBad.badAll = univBad ∪ ambBadAll`, with the one
  `exf` profile `SingleBad.exists_badAll_bound`;
* `LocOcc` is **derived** off `badAllᶜ` by `LocOccDerived.locOcc_of_not_univBad`, at the enlarged
  error coefficient `CTfin = max CTtot CTocc` (the same coefficient `LocOccDerived` uses);
* the windowed move carrier is **derived** off `badAllᶜ` by
  `SingleBad.moveCarrierWinTrunc_of_badAll`, from the record geometry plus the finite run event
  `RunsOK (siteMarks p m U i) (n+3) (AstarPos.Kc p L)` on the record window.

What remains explicit is exactly the *measured* windowed `(locmove)` failure event
`locMoveFailAtClockWin` of `MWinClock` (bounded by `MWin.measureReal_locMoveFailAtClockWin_le`)
and the finite run event.  Neither is assumed to have positive probability; no good event's
probability is used.
-/
import Swarm.SingleBadAll
import Swarm.LocOccDerived

set_option autoImplicit false
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

namespace SingleBadBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The paper's local clauses `(loccoord)`, `(locmove)`, `(lococc)`, `(locgroup)` and the
potential monotonicity/unit-step bounds, off the single measured bad event.**

One `Cerr ≥ 1`, one profile `CT, cT`, one scale `L₀`; off `badAll` the `(lococc)` display is
derived (`CTfin`), the windowed carrier is derived from the record carrier and the finite run
event, and the only remaining input is the measured windowed `(locmove)` failure event for each
nonempty proper group. -/
theorem exists_blockClauses_of_badAll {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (SingleBad.badAll (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ SingleBad.badAll (N := N) p m Cerr r T L →
        (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
          ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L)) →
        ∀ (geom : ℕ → ℕ → Set (Array N)),
          (∀ s t : ℕ, s ≤ t → U ∈ geom s t) →
          (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
            U ∉ {U' : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L
              (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
              (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) geom
              (RecClockLG.Astar r T L) U'}) →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
            (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r) := by
  obtain ⟨Cerr, hCerr1, CTu, cu, hCTu, hcu, Lu, hboundU, hgoodU⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  obtain ⟨CTa, ca, hCTa, hca, La, hboundA⟩ :=
    SingleBad.exists_measureReal_ambBadAll_le (N := N) (m := m) hp0.le hp1 (by omega) T
  obtain ⟨Lk, hLk⟩ := SingleBad.exists_Kc' hp0 hp1
  refine ⟨Cerr, hCerr1, CTu + CTa, min cu ca, by linarith, lt_min hcu hca,
    max (max Lu La) (max Lk 2), ?_, ?_⟩
  · -- the single profile
    intro L hL r hr
    have hLu : Lu ≤ L := le_trans (le_trans (le_max_left Lu La) (le_max_left _ _)) hL
    have hLa : La ≤ L := le_trans (le_trans (le_max_right Lu La) (le_max_left _ _)) hL
    refine le_trans (measureReal_union_le (μ := arrayMeasure N)
      (UniversalFamily.univBad (N := N) p m Cerr r T L)
      (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
    refine le_trans (add_le_add (hboundU L hLu r hr) (hboundA L hLa r hr)) ?_
    exact LocalGoodAll.exf_two hCTu.le hCTa.le hcu hca L
  · -- the clauses
    intro L hL r hr U hcarr hnot hrun geom hgeom hnotfail
    have hLk' : Lk ≤ L := le_trans (le_trans (le_max_left Lk 2) (le_max_right _ _)) hL
    have hL2 : 2 ≤ L := le_trans (le_trans (le_max_right Lk 2) (le_max_right _ _)) hL
    have hL1 : 1 ≤ L := by omega
    have hLu : Lu ≤ L := le_trans (le_trans (le_max_left Lu La) (le_max_left _ _)) hL
    have hnotu : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
      SingleBad.not_mem_univBad_of_not_mem_badAll hnot
    -- the universal-family clauses
    obtain ⟨-, -, -, -, -, -, hlocgroup, hsum⟩ := hgoodU L hLu r hr U hcarr hnotu
    -- `(lococc)` derived
    have hocc : LocalFluid.LocOcc (Xa p m U) (tauA p m U) (Cfin (N := N) p m)
        (LocOccDerived.CTfin p m T Cerr) T L r :=
      LocOccDerived.locOcc_of_not_univBad (N := N) hp0 hp1 hm hT hL1 hr hcarr hnotu
    -- the windowed carrier derived
    have hcarrW : MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U :=
      SingleBad.moveCarrierWinTrunc_of_badAll (N := N) hp0 hp1 (m := m) (L₀ := Lk) hLk
        hLk' hL2 (T := T) (Cerr := Cerr) (r := r) (U := U) hcarr hr hnot hrun
    have hCTle : CTtot p m T Cerr ≤ LocOccDerived.CTfin p m T Cerr :=
      LocOccDerived.CTtot_le_CTfin p m T Cerr
    have hL34 : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (Nat.cast_nonneg L) _
    -- `hmono`, `hunit`
    have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        Hc p m U A n x ≤ Hc p m U A n y :=
      fun A n _ _ hxy => Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        y - x ≤ Hc p m U A n y - Hc p m U A n x :=
      fun A n _ _ hxy => Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    -- `(loccoord)` at `CTfin`
    have hcoord : ∀ (A : Finset (Fin N)) (n : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ n → n ≤ tauA p m U r + T * L → ∀ a0 b0 : ℤ,
        (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
        b0 ≤ Glue.sMaxM (Xa p m U) A n →
        ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
          ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
            + LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A n hA _ h1 h2 a0 b0 ha hab hb
      have h := hcoord_clause_fin (N := N) hp0 hp1 hL1 hr hcarr hsum hCerr1
        A hA n h1 h2 a0 b0 ha hab hb
      have h2' := LocOccDerived.mul_CT_mono hCTle L
      linarith
    -- `(locmove)` at `Cfin`, `CTfin`
    have hwmove : ∀ (A : Finset (Fin N)) (s t : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
        (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A (Finset.univ \ A) u) →
        Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
            - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
          ≤ Cfin (N := N) p m
              * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
            - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
            + LocOccDerived.CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A s t hAn hAn' hs hst ht hsep
      have hAc : Aᶜ.Nonempty := by
        rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hAn'
      have hmove := MWin.hmove_win_of_not_mem (p := p) (m := m) (A := A) (hA := hAn) (hAc := hAc)
        (r := r) (T := T) (L := L) (Cerr := Cerr) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
        (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (Aw := RecClockLG.Astar r T L) (geom := geom) hcarr
        (hnotfail A hAn hAc) (MWin.pin_of_carrier (N := N) hcarr hAn) hgeom
      have hbase := MWin.wmove_clause_win_fin (N := N) hp0 hp1 hL1 (Cerr := Cerr) hAn hAc
        (Aw := RecClockLG.Astar r T L) hmove s t hs hst ht
        (hcarrW A hAn hAn' s t hs hst ht hsep).1
        (hcarrW A hAn hAn' s t hs hst ht hsep).2.1
        (hcarrW A hAn hAn' s t hs hst ht hsep).2.2
      have h2' := LocOccDerived.mul_CT_mono hCTle L
      linarith
    refine ⟨⟨hmono, hunit, hcoord, hwmove, hocc⟩, ?_⟩
    intro I J hdisj hI hJ
    have hbase := group_clause (N := N) (Cerr := Cerr) hL1 hcarr hr hlocgroup I J hdisj hI hJ
    have h2' := LocOccDerived.mul_CT_mono hCTle L
    intro s t hs hst ht hsep
    have := hbase s t hs hst ht hsep
    linarith

/-! ## Axiom audit -/


end SingleBadBlock
