/-
# The literal `(lococc)` display off a *named* null event

## What this file is

`LocOccSingleWindowAllPairs.lococc_recordCarrier_allPairs_singleWindow` and its collapsed
`T L + 3 L` form are stated `∀ᵐ U`.  Their null set is not a named set of that module, so the
`(lococc)` display cannot be folded into a measured bad event (`LocalGoodAll.LocalBad`): the
existing good-event result only delivers membership in `GoodWinAllPairs` at the record fibre.

This file names the failure event and proves it is `arrayMeasure`-null, so that a *pointwise*
display can be asserted off one explicit set of trajectories.

* `occDisplay AllStarts` : the paper's display at every pair of display times
  `s0 ≤ s ≤ t ≤ s0 + T L`, with the record-dependent right-hand side.
* `occDisplayTL` : the record-start (`s = s0`) collapsed `T L + 3 L` form.
* `occFace` : the conjunction, at a fixed fibre `s0`.
* `occNull` : the set of trajectories on which the display fails at *some* fibre `s0`.
* `ae_forall_occFace` / `measure_occNull` / `measureReal_occNull` : it is null.
* `recordBand_self` : on the paper's carrier `recordCarrier` (which contains `ReachAll`), the
  actual record fibre `recTimeA p m U r` is a `recordPrefixBand` fibre, so the display is a
  statement about the actual record time, not about a freely chosen `s0`.
* `occDisplay_recordCarrier_of_not_mem` : off `occNull`, on `recordCarrier`, the display holds at
  the literal record fibre.

## What is NOT claimed

* No probability statement about `GoodWinAllPairs`, no `GoodW`/`GoodStep`/pin/geometry content:
  `hLsum` (the `(locsum)` content) stays an explicit hypothesis, exactly as in the source.
* No non-vacuity of `GoodWinAllPairs`, no covering of the clock fibres by bands, no `(locsum)`
  probability, no separation survival, nothing about blocks, tightness or speed.
-/
import Swarm.LocOccSingleWindowAllPairs
import Swarm.LocalGoodAll

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

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

namespace OccDisplayNull

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The two display forms of Proposition `local` -/

/-- The paper's `(lococc)` display at an arbitrary pair of display times
`τ_r ≤ s ≤ t ≤ τ_r + ⌊TL⌋`, with the record-dependent right-hand side (the record `s0` is the
first-passage time, `q = (i,j)` an ordered pair of distinct walkers, and the sum runs over
`[s, t)`). -/
def occDisplayAllStarts (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
    U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
    U ∈ GoodWinAllPairs (N := N) p m C r T L s0 →
    ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ))
              + (((runMax p m U q.1 s).toNat : ℝ) - (((trajectory p m U s).pos q.1).toNat : ℝ))
              + max 0 (((runMax p m U q.1 s).toNat : ℝ) - ((runMax p m U q.2 s).toNat : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L)

/-- The record-start collapsed form of the display: the sum starts at the record fibre `s0` and
the record-dependent factor is bounded by `T L + 3 L`. -/
def occDisplayTL (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
    U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
    U ∈ GoodWinAllPairs (N := N) p m C r T L s0 →
    ∀ t : ℕ, s0 ≤ t → t ≤ s0 + T * L →
      ∑ u ∈ Finset.Ico s0 t,
          (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
          + ((t : ℝ) - (s0 : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
              + 4 / (1 - aRec p m)) * L34 L (Lw T L)

/-- Both display forms at the fibre `s0`. -/
def occFace (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) (U : Array N) : Prop :=
  occDisplayAllStarts p m C r T L s0 U ∧ occDisplayTL p m C r T L s0 U

/-! ## 2. The named null event -/

/-- The failure event: at some fibre `s0` the `(lococc)` display fails.  This is the *named*
null set of `lococc_recordCarrier_allPairs_singleWindow`; its nullity is `measure_occNull`. -/
def occNull (p : ℝ) (m : ℕ) (C : ℝ) (r T L : ℕ) : Set (Array N) :=
  {U : Array N | ¬ ∀ s0 : ℕ, occFace p m C r T L s0 U}

/-- **The `(lococc)` display at every record fibre, almost surely.**  This is the two source
a.e. statements, conjoined and quantified over the fibre index; the only input is the `(locsum)`
content `hLsum`, exactly as in the source. -/
theorem ae_forall_occFace {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s0 : ℕ, occFace p m C r T L s0 U := by
  rw [ae_all_iff]
  intro s0
  have h1 := lococc_recordCarrier_allPairs_singleWindow (N := N) hp1 hp2 hm hC1 hL hT
    (r := r) (s0 := s0) hr hLsum
  have h2 := lococc_recordCarrier_TL_allPairs_singleWindow (N := N) hp1 hp2 hm hC1 hL hT
    (r := r) (s0 := s0) hr hLsum
  filter_upwards [h1, h2] with U hU1 hU2
  exact ⟨hU1, hU2⟩

/-- **The named null event is null.** -/
theorem measure_occNull {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    (arrayMeasure N) (occNull (N := N) p m C r T L) = 0 := by
  unfold occNull
  exact ae_iff.mp (ae_forall_occFace (N := N) hp1 hp2 hm hC1 hL hT hr hLsum)

/-- The same, in the real-valued form used by the measured bad events. -/
theorem measureReal_occNull {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    (arrayMeasure N).real (occNull (N := N) p m C r T L) = 0 := by
  rw [measureReal_def, measure_occNull (N := N) hp1 hp2 hm hC1 hL hT hr hLsum,
    ENNReal.toReal_zero]

/-- Off the named null event the display holds at every fibre. -/
theorem occFace_of_not_mem {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ} {U : Array N}
    (h : U ∉ occNull (N := N) p m C r T L) : occFace (N := N) p m C r T L s0 U := by
  by_contra hcon
  exact h (fun hall => hcon (hall s0))

/-! ## 3. The actual record fibre of the paper's carrier -/

/-- On the paper's carrier (`ReachAll` and `d_r ≤ L`), the actual record time is a
`recordPrefixBand` fibre: the running maximum at `recTimeA p m U r` is exactly `r`, and no earlier
time has it. -/
theorem recordBand_self {p : ℝ} {m : ℕ} {r L : ℕ}
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier (N := N) p m r L) :
    U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r (recTimeA p m U r) L := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (RecClockLG.subset_iUnion_recordBand (N := N) p m r L hU)
  have hτ : recTimeA p m U r = a :=
    RecClockLG.recTimeA_eq_of_mem_band (N := N) hU.1 ha
  rw [hτ, ← RecClockLG.recordBand_eq_recordPrefixBand (N := N) p m r L a]
  exact ha

/-- **The `(lococc)` display at the literal record fibre, off the named null event.**  On the
paper's carrier, the pointwise display of Proposition `local` holds at `recTimeA p m U r`. -/
theorem occDisplay_recordCarrier_of_not_mem {p : ℝ} {m : ℕ}
    {C : ℝ} {r T L : ℕ} {U : Array N}
    (hU : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ occNull (N := N) p m C r T L) :
    occDisplayTL p m C r T L (recTimeA p m U r) U :=
  (occFace_of_not_mem (N := N) h).2

/-- The arbitrary-start form of the same conclusion. -/
theorem occDisplayAllStarts_recordCarrier_of_not_mem {p : ℝ}
    {m : ℕ} {C : ℝ} {r T L : ℕ} {U : Array N}
    (hU : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ occNull (N := N) p m C r T L) :
    occDisplayAllStarts p m C r T L (recTimeA p m U r) U :=
  (occFace_of_not_mem (N := N) h).1

end OccDisplayNull
