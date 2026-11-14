/-
# `BlkCoin.BlockClauses` off the measured events, with the *canonical* record geometry

`SingleBadBlock.exists_blockClauses_of_badAll` derives the paper's local block clauses off the
single bad event, but it keeps a *free* window family `geom` together with the hypothesis
`∀ s t, s ≤ t, U ∈ geom s t`.  That hypothesis is not satisfiable by the canonical `(loccoord)`
window `locCoordGeom`, whose membership fails far beyond the record window; it can only be met by
a family that contains *every* window, which then makes the measured `(locmove)` bound
unavailable (its pointwise display cannot hold on all windows).

This file removes the free family: it uses the canonical `geom = locCoordGeom p m A hA` at each
group, and the membership hypothesis is restricted to the **record window**
`τ_r ≤ s ≤ t ≤ τ_r + T·L`, where it is *proved* from the record carrier
(`LocCoordGeomCarrier.mem_locCoordGeom_of_carrier`).  Correspondingly the `(locmove)` display is
derived from the windowed failure event at the canonical geometry
(`WindowMeas.moveFailCanonAll`), which is what the measured bound
`WindowMeas.measureReal_moveFailCanonAll_le` actually estimates.

The remaining inputs are exactly: the record carrier, the single bad event `SingleBad.badAll`, the
finite run event on the record window, the simultaneous canonical `(locmove)` failure event, and
the two clauses `(locgroup)`/`(locsum)` of the universal family (which are themselves functions of
`univBadᶜ`; they are kept as hypotheses so that this file has no probabilistic content).
-/
import Swarm.WindowMeas
import Swarm.SingleBadGroups

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

namespace WindowBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The windowed `(locmove)` input**, with the geometric membership hypothesis restricted to the
record window.  This is `MWin.hmove_win_of_not_mem` with `hgeom` used only at the window actually
under consideration, which is where `mem_locCoordGeom_of_carrier` supplies it. -/
theorem hmove_win_of_not_mem_win {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hAc : Aᶜ.Nonempty} {r T L : ℕ} {Cerr ε₁ ε₂ : ℝ} {Aw : ℕ}
    {geom : ℕ → ℕ → Set (Array N)} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hU : U ∉ {U : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L
      (RecClockLG.Bstar L) (LocalGoodFamily.Cmax (N := N) p m)
      (LocalGoodFamily.betaOf (N := N) p m T L Cerr) ε₁ ε₂ geom Aw U})
    (hpin : (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hA (recTimeA p m U r) ∧
      runMaxA p m U hA (recTimeA p m U r) ≤ (r : ℤ))
    (hgeom : ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ geom s t) :
    ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m hA (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t,
        LocGroupSimul.winTrunc p m n A Aᶜ hA (RecClockLG.Bstar L) Aw U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr) ε₁ ε₂ s t U := by
  intro s t hs hst ht hamb hW hstep
  exact MWin.wmove_of_not_mem (p := p) (m := m) (A := A) (hA := hA) (hAc := hAc) hcarr hU hs hst ht
    (MWin.locmoveGoodWin_of (p := p) (m := m) (A := A) (hA := hA) (r := (r : ℤ)) (Th := T)
      (Lh := L) (B := RecClockLG.Bstar L) (Aw := Aw) (n0 := recTimeA p m U r) (s := s) (t := t)
      (U := U) hamb hW hstep hpin)
    (hgeom s t hs hst ht)

/-- **The paper's local block clauses off the single measured bad event, at *proved* geometry.**

`Cfin`, `CTfin` and the error coefficient `Cerr` are the same as in `SingleBadBlock`; the
`(lococc)` display is derived from `univBadᶜ`, the windowed move carrier from `badAllᶜ` and the
finite run event, the geometry from the record carrier, and the `(locmove)` display from the
simultaneous canonical failure event `moveFailCanonAll`. -/
theorem blockClauses_of_not_bad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) {Cerr : ℝ} (hCerr1 : 1 ≤ Cerr) {Lk : ℕ}
    (hLk : ∀ L : ℕ, Lk ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {L : ℕ} (hL : Lk ≤ L) (hL2 : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hnot : U ∉ SingleBad.badAll (N := N) p m Cerr r T L)
    (hrun : ∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
      ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L))
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
  -- the windowed move carrier
  have hcarrW : MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    SingleBad.moveCarrierWinTrunc_of_badAll (N := N) hp0 hp1 (m := m) (L₀ := Lk) hLk
      hL hL2 (T := T) (Cerr := Cerr) (r := r) (U := U) hcarr hr hnot hrun
  -- `(lococc)` derived
  have hocc : LocalFluid.LocOcc (Xa p m U) (tauA p m U) (Cfin (N := N) p m)
      (LocOccDerived.CTfin p m T Cerr) T L r :=
    LocOccDerived.locOcc_of_not_univBad (N := N) hp0 hp1 hm hT hL1 hr hcarr hnotu
  have hCTle : CTtot p m T Cerr ≤ LocOccDerived.CTfin p m T Cerr :=
    LocOccDerived.CTtot_le_CTfin p m T Cerr
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
  -- `(locmove)` at `Cfin`, `CTfin`, with the *proved* canonical geometry
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
    have hmove := hmove_win_of_not_mem_win (p := p) (m := m) (A := A) (hA := hAn) (hAc := hAc)
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

end WindowBlock
