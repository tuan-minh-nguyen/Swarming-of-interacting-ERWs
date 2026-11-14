/-
# `BlkCoin.BlockClauses` off the single measured bad event, for **every** `N ≥ 2`

This is `WindowMain.exists_badEvent_blockClauses` (`WindowFinal`) with the `2m < N` hypothesis
removed.  Everything is the same except that the finite-run component of the bad event is the
position-level event `WindowPos.runWindowPos` (level `r + T·L + 1`), whose measured complement
`N·(r + T·L + 1)·(1−q)^{Kc}` is available for every `N` (`WindowPosAllN.exists_badEventPos_le`).

* `blockClauses_of_not_bad_pos` — `WindowBlock.blockClauses_of_not_bad` with
  `SingleBad.moveCarrierWinTrunc_of_badAll` replaced by
  `WindowPos.moveCarrierWinTrunc_of_badAll_pos`, and the run hypothesis at the position level.
* `exists_badEventPos_blockClauses` — one event, one profile `CT · exf cT L`, and the paper's
  `BlockClauses` at `Cfin`/`CTfin` off it, for **every** `2 ≤ N`, `2 ≤ m`, `1/2 < p < 1`,
  `T ≥ 1`, with the retained scope conditions `(T+3)·L ≤ r` and `r ≤ L²` displayed.

`r ≤ L²` is retained: it is the degree-2 polynomial absorption of the run term
(`N·(r+TL+1) ≤ N·(T+3)·(L+1)²`) and is not touched here — the `2m < N` restriction is what this
file removes.  No good event's probability, no stationary law, no coalescence, no NoCoalescence,
no velocity statement, no change to the actual trajectory or to `arrayMeasure`.
-/
import Swarm.RunPosWindow
import Swarm.WindowFinal

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

namespace WindowPosAllN

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The block clauses off the position-level run event -/

/-- **The paper's local block clauses off the single bad event, at *proved* geometry, with the
finite-run component at the position level.**  Verbatim `WindowBlock.blockClauses_of_not_bad`
except `hrun : WindowPos.runWindowPos p m r T L (AstarPos.Kc p L) U` and the movement carrier taken
from `WindowPos.moveCarrierWinTrunc_of_badAll_pos`. -/
theorem blockClauses_of_not_bad_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) {Cerr : ℝ} (hCerr1 : 1 ≤ Cerr) {Lk : ℕ}
    (hLk : ∀ L : ℕ, Lk ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {L : ℕ} (hL : Lk ≤ L) (hL2 : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hnot : U ∉ SingleBad.badAll (N := N) p m Cerr r T L)
    (hrun : WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U)
    (hnotfail : U ∉ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
      (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
    (hlocgroup : ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4))
    (hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m
            * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ)) :
    BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
      (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r := by
  have hL1 : 1 ≤ L := by omega
  have hnotu : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
    SingleBad.not_mem_univBad_of_not_mem_badAll hnot
  -- the windowed move carrier, from the position-level run event
  have hcarrW : MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    WindowPos.moveCarrierWinTrunc_of_badAll_pos (N := N) hp0 hp1 (m := m) (L₀ := Lk) hLk
      hL hL2 (T := T) (Cerr := Cerr) (r := r) (U := U) hcarr hr hnot hrun
  -- `(lococc)` derived
  have hocc : LocalFluid.LocOcc (Xa p m U) (tauA p m U) (Cfin (N := N) p m)
      (LocOccDerived.CTfin p m T Cerr) T L r :=
    LocOccDerived.locOcc_of_not_univBad (N := N) hp0 hp1 hm hT hL1 hr hcarr hnotu
  have hCTle : CTtot p m T Cerr ≤ LocOccDerived.CTfin p m T Cerr :=
    LocOccDerived.CTtot_le_CTfin p m T Cerr
  have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
      Hc p m U A n x ≤ Hc p m U A n y :=
    fun A n _ _ hxy => Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
  have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
      y - x ≤ Hc p m U A n y - Hc p m U A n x :=
    fun A n _ _ hxy => Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
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
    have hgeom : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        U ∈ ClockLocMove.locCoordGeom p m A hAn r T L s t :=
      fun s t hs hst ht => mem_locCoordGeom_of_carrier (N := N) hcarr hr A hAn s t hs hst ht
    have hmove := WindowBlock.hmove_win_of_not_mem_win (p := p) (m := m) (A := A) (hA := hAn)
      (hAc := hAc)
      (r := r) (T := T) (L := L) (Cerr := Cerr) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
      (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (Aw := RecClockLG.Astar r T L)
      (geom := ClockLocMove.locCoordGeom p m A hAn r T L) hcarr
      (WindowMeas.not_mem_locMoveFailCanon_of_not_mem_moveFailCanonAll hnotfail A hAn hAc)
      (MWin.pin_of_carrier (N := N) hcarr hAn) hgeom
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

/-! ## 2. One event, one profile, block clauses off it — every `N ≥ 2` -/

theorem exists_badEventPos_blockClauses {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → (r : ℝ) ≤ (L : ℝ) ^ 2 →
        (arrayMeasure N).real (badEventPos (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ badEventPos (N := N) p m Cerr r T L →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
          (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r) := by
  classical
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hmeas⟩ :=
    exists_badEventPos_le (N := N) hp0 hp1 hm hN hT
  obtain ⟨Lk, hLk⟩ := SingleBad.exists_Kc' hp0 hp1
  obtain ⟨L₈, hL₈⟩ := LocalGoodFamily.familyGood_locgroup (N := N) hp0 hp1 hm hT
    (UniversalFamily.grpAllFam (N := N)) UniversalFamily.grpAllFam_I
    UniversalFamily.grpAllFam_J UniversalFamily.grpAllFam_disj
  obtain ⟨c₉, hc₉, L₉, h₉⟩ := LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
    (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
    (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀ + Lk + L₈ + L₉ + L₁₀ + 2, ?_, ?_⟩
  · intro L hL r hr hrL
    exact hmeas L (by omega) r hr hrL
  intro L hL r hr U hcarr hnot
  have hL8 : L₈ ≤ L := by omega
  have hL9 : L₉ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  have hLk' : Lk ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have hnotbad : U ∉ SingleBad.badAll (N := N) p m Cerr r T L :=
    fun hc => hnot (Or.inl (Or.inl hc))
  have hnotfail : U ∉ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
      (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L) :=
    fun hc => hnot (Or.inl (Or.inr hc))
  have hrun : WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U := by
    have hnotrun : ¬ ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U :=
      fun hc => hnot (Or.inr hc)
    exact Classical.not_not.mp hnotrun
  have hnotu : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
    SingleBad.not_mem_univBad_of_not_mem_badAll hnotbad
  have hfam : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr
      (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
      UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
      UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J r T L := hnotu
  obtain ⟨⟨hcom, hmv⟩, hpair⟩ := LocalGoodFamily.not_mem_famBad hfam
  obtain ⟨hsumOcc, hocc, hlsC, hlocMax, hlocMart, hpot, hoccNull⟩ :=
    LocalGoodFamily.not_mem_commonBad hcom
  have hlocgroup : ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro I J hI hJ hdisj s t hs hst ht hsep
    have hq : (I, J) ∈ UniversalFamily.grpAllFam (N := N) :=
      UniversalFamily.mem_grpAllFam.mpr ⟨hI, hJ, hdisj⟩
    have h := hL₈ L hL8 r hr U hcarr hlocMax (LocalGoodFamily.familyGood_pot hfam) hpair
      (I, J) hq s t hs hst ht hsep
    rwa [show UniversalFamily.grpAllFam_I (I, J) hq = hI from Subsingleton.elim _ _,
      show UniversalFamily.grpAllFam_J (I, J) hq = hJ from Subsingleton.elim _ _] at h
  have hsum : ∀ (j : Fin N) (a0 b0 : ℕ),
      LocOccCarrierAssembly.A0 r T L ≤ a0 →
      b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m
            * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ) := by
    intro j a0 b0 ha0 hb0 hab
    have hside : 2 * ellT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
        ≤ LocOccCarrierAssembly.A0 r T L := by
      have hArith : L + (T + 2) * L ≤ r := by
        have hEq : L + (T + 2) * L = (T + 3) * L := by ring
        rw [hEq]; exact hr
      have hLA0 : L ≤ LocOccCarrierAssembly.A0 r T L := by
        unfold LocOccCarrierAssembly.A0
        exact Nat.le_sub_of_add_le hArith
      exact le_trans (hL₁₀ L hL10) hLA0
    exact (h₉ (LocOccCarrierAssembly.Lw T L)
      (le_trans hL9 (LocOccCarrierAssembly.le_Lw T L))
      (LocOccCarrierAssembly.A0 r T L) hside).2 U hsumOcc j a0 b0 ha0 hb0 hab
  exact blockClauses_of_not_bad_pos (N := N) hp0 hp1 hm hT hCerr1 hLk hLk' hL2 hr
    hcarr hnotbad hrun hnotfail hlocgroup hsum

end WindowPosAllN
