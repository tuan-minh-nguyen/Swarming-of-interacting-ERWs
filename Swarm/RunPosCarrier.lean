/-
# The windowed movement carrier from the finite-run event at a *position* level

`AstarPos.moveCarrierWin_of_carrier_hybrid` needs the finite-run event of the record window at
every *time* `n` of the window, at level `n + 3`:

    ∀ n ∈ Ico (τ_r) (τ_r + T·L), ∀ i, RunsOK (siteMarks p m U i) (n + 3) K .

This file replaces it by the **single** deterministic event

    ∀ i, RunsOK (siteMarks p m U i) (r + T·L + 1) K ,

at the *position* level `runLev r T L = r + T·L + 1`.  On the record carrier the leader's running
maximum at any window time is at most `r + T·L` (`runMax_toNat_le_of_carrier`, from
`LocCoordGeomCarrier.Rmax_le_nat_step`), so `Gtail` truncated at `runMax + 1` is controlled by the
run event at level `runLev` (`RunPos.Gtail_le_of_runs_target`), and the windowed good event
follows from `RunPos.goodWWin_of_locmax_pos`.

Everything else — `(sep)`, the `(locmax)` `hfix` half, `ambGoodAll`, the position bound
`Astar ≤ X` — is exactly as in `AstarPos.goodWWin_of_carrier_hybrid`.  No clock, no drift
constant, no `2m < N`.
-/
import Swarm.RunPos
import Swarm.AstarPosition
import Swarm.SingleBadAll

set_option maxHeartbeats 2000000
set_option autoImplicit false
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

namespace WindowPos

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The deterministic run level -/

/-- **The position-level finite-run event of a record window**: every walker's mark row has a
marked site in every block of `K` consecutive sites below `r + T·L + 1`.  This is *one* event, at
a level determined by `(r, T, L)` only — no record clock. -/
def runWindowPos (p : ℝ) (m r T L K : ℕ) (U : Array N) : Prop :=
  ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (r + T * L + 1) K

/-- On the record carrier, at every time of the record window, every walker's running maximum is
at most `r + T·L`.  (`Rmax_le_nat_step` at the record time `τ_r`, where the spatial record is
`r`.) -/
theorem runMax_toNat_le_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L) (i : Fin N) :
    (runMax p m U i n).toNat ≤ r + T * L := by
  have hτ := isRecord_recTimeA_of_carrier (N := N) hcarr
  have hK : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  have hR := Rmax_le_nat_step (N := N) (r := r) (τ := recTimeA p m U r)
    (B := Finset.univ) hK (hτ r).1 (hτ r).2 hn1
  have hle : runMax p m U i n ≤ Loccoord.Rmax p m U Finset.univ hK n :=
    Finset.le_sup' (s := (Finset.univ : Finset (Fin N))) (f := fun j => runMax p m U j n)
      (Finset.mem_univ i)
  have h2 : (runMax p m U i n).toNat
      ≤ (Loccoord.Rmax p m U Finset.univ hK n).toNat := Int.toNat_le_toNat hle
  have hsub : n - recTimeA p m U r ≤ T * L := by omega
  omega

/-! ## 2. The windowed good event from the position-level run event -/

/-- **`GoodWWin` at `Bstar L` from `(locmax)`, `(sep)` and the position-level run event.**

Same as `AstarPos.goodWWin_of_carrier_hybrid`, with the hypothesis `hrun` at the single
deterministic level `r + T·L + 1` instead of the per-time levels `n + 3`. -/
theorem goodWWin_of_carrier_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {n : ℕ} (hn1 : recTimeA p m U r ≤ n) (hn2 : n ≤ recTimeA p m U r + T * L)
    (hsep : Glue.Sep (PaperBlock.Xa p m U) A Aᶜ n)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : runWindowPos (N := N) p m r T L K U) :
    SiteWindow.GoodWWin p m n A Aᶜ hA (RecClockLG.Bstar L) (RecClockLG.Astar r T L) U := by
  have hpne : p ≠ 0 := by linarith
  have hr1 : (T + 2) * L + 1 ≤ r := by omega
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hρ : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hGle : (K : ℝ) / (1 - (1 - p) / p) ≤ LocSumAct.xOf L := by
    rw [div_le_iff₀ hρ]
    linarith
  have hK : (A ∪ Aᶜ).Nonempty := ⟨Classical.arbitrary (Fin N), by simp⟩
  have hA' : ∀ i ∈ A, RecClockLG.Astar r T L ≤ (runMax p m U i n).toNat :=
    fun i _ => AstarPos.Astar_le_runMax_of_carrier hcarr hr1 hn1 hn2 i
  have hH : ∀ i ∈ A, ∀ v : ℕ, RecClockLG.Astar r T L ≤ v + 1 →
      v ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U → hfix (omegaN p m U i) v ≤ LocSumAct.xOf L := by
    intro i _ v hv1 hv2
    rw [Loccoord.hfix_omegaN_eq_hof (p := p) hpne (m := m) (U := U) i v]
    exact AstarPos.hof_le_of_not_mem_locmax hnb
      (AstarPos.mem_locmax_window_of_carrier hcarr hr hn1 hn2 hK hv1 hv2)
  have hG : ∀ i ∈ A, ∀ u : ℕ, RecClockLG.Astar r T L ≤ u →
      u ≤ LocGroupQ.xTop p m n (A ∪ Aᶜ) hK U →
      Gtail p m U i u ((runMax p m U i n).toNat + 1) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
    intro i _ u _ _
    refine Gtail_le_of_runs_target (N := N) hp0 hp1 (U := U) (i := i) (R := (runMax p m U i n).toNat)
      (Lrun := r + T * L + 1) hK1 ?_ (hrun i) u
    have := runMax_toNat_le_of_carrier (N := N) hcarr hn1 hn2 i
    omega
  have hGnn : (0 : ℝ) ≤ 2 + (K : ℝ) / (1 - (1 - p) / p) := by
    have h1 : (0 : ℝ) ≤ (K : ℝ) / (1 - (1 - p) / p) := div_nonneg hKnn hρ.le
    linarith
  have hgood := goodWWin_of_locmax_pos (N := N) hp0 hp1.le A Aᶜ hA hAc
    disjoint_compl_right (AstarPos.sepSet_of_glueSep hcarr hr1 hn1 hn2 hsep) hx1 hGnn hA' hH hG
  refine CarrierWin.goodWWin_mono (N := N) hA ?_ hgood
  rw [AstarPos.Bstar_eq_add hL]
  refine max_le le_rfl ?_
  linarith

/-! ## 3. The movement carrier and its truncation -/

/-- **`MoveCarrierWin` with the position-level run event.**  Same as
`AstarPos.moveCarrierWin_of_carrier_hybrid` with `hrun` at the level `r + T·L + 1`. -/
theorem moveCarrierWin_of_carrier_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} (hL : 1 ≤ L) (hr : (T + 2) * L + 2 ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
    (hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L)
    {K : ℕ} (hK1 : 1 ≤ K) (hGnum : (K : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    (hrun : runWindowPos (N := N) p m r T L K U) :
    CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  refine CarrierWin.moveCarrierWin_of_win (N := N) hp0 hp1 (AstarPos.one_le_Astar hr) hamb ?_ ?_
  · intro A hA hne s t hs hst ht hsepwin n hn
    have hAc : Aᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hnil
      exact hne ((Finset.compl_eq_empty_iff A).mp hnil)
    have hs1 : s ≤ n := (Finset.mem_Ico.mp hn).1
    have hs2 : n < t := (Finset.mem_Ico.mp hn).2
    have hn1 : recTimeA p m U r ≤ n := le_trans hs hs1
    have hn2 : n ≤ recTimeA p m U r + T * L := le_trans (le_of_lt hs2) ht
    exact goodWWin_of_carrier_pos (n := n) hp0 hp1 hL hr hcarr hA hAc hn1 hn2
      (hsepwin n hs1 hs2) hnb hK1 hGnum hrun
  · intro n hn1 hn2 j
    exact AstarPos.Astar_le_X_of_carrier hcarr (by omega) hn1 hn2 j

/-- **The truncated movement carrier off `badAll`, with the position-level run event.**

`SingleBad.moveCarrierWinTrunc_of_badAll` with `AstarPos.moveCarrierWin_of_carrier_hybrid`
replaced by `moveCarrierWin_of_carrier_pos`: the run event is the single deterministic event
`runWindowPos p m r T L (Kc p L)`. -/
theorem moveCarrierWinTrunc_of_badAll_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {L₀ : ℕ}
    (hL₀ : ∀ L : ℕ, L₀ ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {L : ℕ} (hL : L₀ ≤ L) (hL2 : 2 ≤ L)
    {T : ℕ} {Cerr : ℝ} {r : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (hnot : U ∉ SingleBad.badAll (N := N) p m Cerr r T L)
    (hrun : runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U) :
    MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  have hr2 : (T + 2) * L + 2 ≤ r := by
    refine le_trans ?_ hr
    calc (T + 2) * L + 2 ≤ (T + 2) * L + L := Nat.add_le_add_left (by omega : 2 ≤ L) _
      _ = (T + 3) * L := by ring
  have hwin : CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    moveCarrierWin_of_carrier_pos (N := N) hp0 hp1 (by omega : 1 ≤ L) hr2 hcarr
      (SingleBad.ambGoodAll_of_not_mem_badAll hnot)
      (AstarPos.not_mem_LocMaxBad_of_not_mem_univBad
        (SingleBad.not_mem_univBad_of_not_mem_badAll hnot))
      (hL₀ L hL).1 (hL₀ L hL).2 hrun
  intro A hA hne s t hs hst ht hsep
  obtain ⟨hamb, hgW, hstep⟩ := hwin A hA hne s t hs hst ht hsep
  exact ⟨hamb, fun n hn => MWin.winTrunc_of_goodWWin (hgW n hn) (fun k => by
    exact SingleBad.Astar_succ_le_X_of_carrier (N := N) hcarr (by omega) (by omega)
      (le_trans hs (Finset.mem_Ico.mp hn).1)
      (le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht) k), hstep⟩

end WindowPos
