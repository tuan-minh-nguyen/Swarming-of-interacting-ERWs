/-
# The record-window run event, measured at the *position* level — every `N ≥ 2`

`RunWindow.arrayMeasure_runWindow_compl_le_auto` is the measured bound on the failure of the
finite-run event of the record window *at every time of the window*:

    P(¬ runWindow) ≤ 2N exp(−rμ/(64N)) + N·(⌈2Nr/μ⌉₊ + T·L + 4)·(1−q)^{Kc},   μ = (2p−1)(N−2m).

Its clock term is a record-clock *upper* tail, and that tail is exactly what fails for `N ≤ 2m`:
the drift constant `μ` is non-positive there (`RunWindow.recTimeA_tail_regime_empty`), so the
bound provably cannot be instantiated.

The bound proved here has **no clock term at all**:

    P(¬ runWindowPos) ≤ N·(r + T·L + 1)·(1−q)^K ,      q = (1−p)^{m−1},

for every `N` with `Nonempty (Fin N)` (in particular every `2 ≤ N`), every `m ≥ 2` and every
`1/2 < p < 1`.  It is the direct image of `SwarmCarrier.arrayMeasure_carrier_compl_le` under the
deterministic level `r + T·L + 1`; no drift, no excitation, no stopping time, no stationarity.

`exists_measureReal_not_moveCarrierWin_le_allN` composes this with the movement carrier of
`RunPosCarrier`: off `univBad`, on `ambGoodAll` and on the record carrier, failure of
`CarrierWin.MoveCarrierWin` is measured by exactly that expression — for every `N ≥ 2`, with no
`2m < N`.  The `2m < N` hypothesis of the earlier route was needed *only* to pay for the record
clock; the position level makes the payment unnecessary.
-/
import Swarm.RunPosCarrier
import Swarm.CarrierModel

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

/-! ## 1. Measurability-free complement bound of the position-level run event -/

/-- **The position-level run event measured, every `N`.**  For `2 ≤ m`, `1 ≤ K`, any `r, T, L`:

    P{¬ runWindowPos} ≤ N·((r + T·L + 1) : ℝ)·(1 − (1−p)^{m−1})^K .

No record clock, no drift constant, no `2m < N`. -/
theorem arrayMeasure_runWindowPos_compl_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (r T L K : ℕ) (hK : 1 ≤ K) :
    (arrayMeasure N).real {U : Array N | ¬ runWindowPos (N := N) p m r T L K U}
      ≤ (N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
  have hsub : {U : Array N | ¬ runWindowPos (N := N) p m r T L K U}
      ⊆ {U : Array N | ∃ j : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U j) (r + T * L + 1) K} := by
    rintro U hU
    by_contra hcon
    apply hU
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  have hRHSnn : (0 : ℝ) ≤ (N : ℝ) *
      (((r + T * L + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
    have hq : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      have h2 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
      linarith
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hRHSnn
    (SwarmCarrier.arrayMeasure_carrier_compl_le (N := N) hp0 hp1 hm (r + T * L + 1) K hK)

/-! ## 2. The movement carrier off the position-level run event -/

/-- **The windowed movement carrier measured off the position-level run event, every `N ≥ 2`.**

For `2 ≤ m` there is a scale `L₀` such that for every `L ≥ L₀`, every block `(T, Cerr, r)` with
`(T+3)·L ≤ r`,

    P{ U ∈ recordCarrier ∩ univBadᶜ ∩ ambGoodAll  and  ¬ MoveCarrierWin at Astar r T L }
      ≤ N·(r + T·L + 1)·(1−q)^{Kc p L} .

`univBad` and `ambGoodAll` occur only as *conditions inside* the measured set; their own
probabilities are never assumed.  Compare `RunWindow.exists_measureReal_not_moveCarrierWin_le`,
which has the same shape but needs `2m < N` and carries a record-clock term
`2N exp(−rμ/(64N))` and the clock-cutoff prefactor `⌈2Nr/μ⌉₊ + T·L + 4` in place of `r + T·L + 1`.
-/
theorem exists_measureReal_not_moveCarrierWin_le_allN {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (T : ℕ) (Cerr : ℝ) (r : ℕ), (T + 3) * L ≤ r →
      (arrayMeasure N).real
          {U : Array N |
            U ∈ RecClockLG.recordCarrier (N := N) p m r L ∧
            U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L ∧
            U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L ∧
            ¬ CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U}
        ≤ (N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ)
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)) := by
  obtain ⟨Lk, hLk⟩ := AstarPos.exists_Kc (p := p) hp0 hp1
  refine ⟨max Lk 2, fun L hL T Cerr r hr => ?_⟩
  have hLk' : Lk ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
  have hr2 : (T + 2) * L + 2 ≤ r := by
    refine le_trans ?_ hr
    calc (T + 2) * L + 2 ≤ (T + 2) * L + L := Nat.add_le_add_left (by omega : 2 ≤ L) _
      _ = (T + 3) * L := by ring
  have hsub : {U : Array N |
        U ∈ RecClockLG.recordCarrier (N := N) p m r L ∧
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L ∧
        U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L ∧
        ¬ CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U}
      ⊆ {U : Array N | ¬ runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U} := by
    rintro U ⟨hcarr, huniv, hamb, hnot⟩ hrun
    exact hnot (moveCarrierWin_of_carrier_pos (N := N) hp0 hp1 (by omega : 1 ≤ L) hr2 hcarr
      hamb (AstarPos.not_mem_LocMaxBad_of_not_mem_univBad huniv)
      hK (hLk L hLk').2 hrun)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _))
    (arrayMeasure_runWindowPos_compl_le (N := N) hp0 hp1 hm r T L (AstarPos.Kc p L) hK)

end WindowPos
