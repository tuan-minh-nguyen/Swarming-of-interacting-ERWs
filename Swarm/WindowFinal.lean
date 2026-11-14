/-
# One measured bad event, exponentially small, off which the paper's block clauses hold

This file assembles the four measured lanes into **one** event with **one** `exf` profile, off
which the paper's local `BlkCoin.BlockClauses` hold:

    badEvent = SingleBad.badAll            (the deterministic universal family ∪ the ambient Γ-count)
             ∪ moveFailCanonAll            (the simultaneous windowed (locmove) failure, canonical geometry)
             ∪ {¬ runWindow …}             (the finite run event on the record window)

* `badAll` obeys `exf` by `exists_famBad_le_at` + `SingleBad.exists_measureReal_ambBadAll_le`;
* `moveFailCanonAll` obeys `2^N` times the per-group measured `(locmove)` bound
  (`WindowMeas.measureReal_moveFailCanonAll_le`), whose exponential windows are turned into the
  profile by `WindowLocal` and whose polynomial prefactor is absorbed by `WindowAbsorb`;
* `¬ runWindow` obeys `RunWindow.arrayMeasure_runWindow_compl_le_auto` (**no** clock-cutoff
  hypothesis), and its two terms are absorbed: the clock term because `r ≥ (T+3)L`, and the
  finite-run term because `Kc p L ≈ xOf L` from below and `(1-q)^{Kc p L} = exf c_Q L`.

Off `badEvent` and on the record carrier, `WindowBlock.blockClauses_of_not_bad` derives
`BlockClauses` at `Cfin`/`CTfin` from the *proved* canonical geometry.

## Exact scope (read this before quoting the result)

* `2m < N` is required — the record-clock tail and hence the run-window measurement are only
  available there (`RunWindow.recTimeA_tail_regime_empty` records the `N ≤ 2m` obstruction).  The
  result therefore **does not** cover `N ≤ 2m`, in particular not `N = m = 2`.
* The profile threshold has the explicit polynomial restriction `r ≤ L²` on the record level.
  It is needed **only** for the finite-run term: the union bound
  `N·(clockCut + TL + 3)·(1-q)^{Kc}` grows linearly in `r` (since `clockCut ~ r`), so no `exf`
  bound uniform in all `r` can be extracted from it.  The two run-window terms are kept verbatim
  inside the proof of `exists_badEvent_le` (the union bound is `h3` there); no separate
  unrestricted-`r` declaration is exposed, and this file makes no claim in that regime beyond
  the proved `RunWindow.arrayMeasure_runWindow_compl_le_auto`.
* Both sides are stated for a fixed `N`: `Cerr, CT, cT, L₀` may depend on `N, m, p, T`.  What is
  *not* assumed anywhere is a good event's probability, a stationary law, coalescence, or the
  velocity.  `RunWindow`, `MWin`, `SingleBad`, `LocOccDerived` and `LocalGoodFamily` remain the
  only probabilistic inputs, and every one of them is a proved measured statement.
-/
import Swarm.WindowLe

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

namespace WindowMain

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 3. The combined theorem: one measured event, one profile, block clauses off it -/

/-- **One measured bad event, one profile, and the paper's block clauses off it.**

`WindowLe.exists_badEvent_le` measures `badEvent = badAll ∪ moveFailCanonAll ∪ {¬runWindow}` by
`CT · exf cT L`; `WindowBlock.blockClauses_of_not_bad` derives the block clauses off that event
and the record carrier.  This theorem states both at the same `Cerr`, `CT`, `cT`, with one
threshold.  **Scope**: `2m < N` and `r ≤ L²` (see `WindowLe`). -/
theorem exists_badEvent_blockClauses {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) (hmN : 2 * m < N) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → (r : ℝ) ≤ (L : ℝ) ^ 2 →
        (arrayMeasure N).real (badEvent (N := N) p m Cerr r T L) ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ badEvent (N := N) p m Cerr r T L →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
          (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r) := by
  classical
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hmeas⟩ :=
    exists_badEvent_le (N := N) hp0 hp1 hm hN hT hmN
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
  · intro L hL r hr U hcarr hnot
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
    have hrun : ∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
        ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L) := by
      have hnotrun : ¬ ¬ RunWindow.runWindow (N := N) p m r T L (AstarPos.Kc p L) U :=
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
    exact WindowBlock.blockClauses_of_not_bad (N := N) hp0 hp1 hm hT hCerr1 hLk hLk' hL2 hr
      hcarr hnotbad hrun hnotfail hlocgroup hsum

end WindowMain
