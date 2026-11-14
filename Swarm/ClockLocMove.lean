/-
# The `(locmove)` display at the literal actual record clock `tau_r`

`LOCAL_GOOD_PARTIAL.md` records the gap that stops `(locgroup)`/`(locmove)` from being displays at
the paper's random clock `n0 = tau_r`: they are proved at a **deterministic** clock, and the union
over the clock values is not summable because `tau_r` is unbounded and the failure events carry no
carrier disjoint in the clock.  `RecClockLocgroup.lean` closed this for the one-sided `(locgroup)`
advance with the count-free band estimate.  This file does the same for the two martingale halves
of `(locmove)`:

* `measureReal_recordClock_QTpair_le` — the two-endpoint `Gamma`-half (`dQT`) deviation over
  **every** window `[tau_r+s, tau_r+s+k]` with `s ≤ K`, `k ≤ K - s`, measured at the literal
  `recTimeA p m U r`, with the count-free prefactor `2 (K+1)^2` and envelope `2 * stepEnv p B`;
* `measureReal_recordClock_LGpair_le` — the same for the max-growth half (`Lcum`), envelope `2B`;
* `measureReal_locMoveFailAtClock_le` — **the measured `(locmove)` clause at the actual clock**:
  the paper's failure event (defect carrier + a window inside `[tau_r, tau_r + (T+3)L]` on which
  `locmoveGood` holds at the record clock and the display `WA_t - WA_s ≤ locmoveRHS` fails) has
  measure at most the two clock-anchored two-endpoint bounds plus the `(loccoord)` carrier error
  `e_b`.  No union over clock values, no truncation of the clock, no record-time tail.

The path is the one `LOCAL_GOOD_PARTIAL.md` names as the fix: the pointwise `(locmove)` implication
`locmove_ae` is conull for **each** deterministic triple `(n0,s,t)`, hence by countable
intersection conull simultaneously for *all* triples; the clock is then substituted into that
almost-sure statement and only the two deviation events remain, each of which the band estimate
charges once per record band.

What is **not** claimed: no `(lococc)`, no `(loccoord)` carrier estimate (it is carried as the
explicit `hbad`/`hcc` premise, exactly as the deterministic statement carries it), no merged
single-event `LocalBad`, no `GoodW`/`GoodStep` probability, no halving, tightness, invariant law,
regeneration, common speed or `MainClaim`.
-/
import Swarm.LocMoveAllWindows
import Swarm.RecClockLocgroup

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl

namespace ClockLocMove

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The `Gamma`-half increment, truncated at its a.e. envelope -/

/-- The `(locmove)` `Gamma`-increment `dQT`, truncated at its almost-sure envelope
`2 * stepEnv p B`.  For each `t` the truncated and untruncated increments agree almost surely, so
the martingale-difference property survives (`condExp_dQTtr`) while the envelope holds pointwise
(`abs_dQTtr_le`), which is what the band estimate needs. -/
noncomputable def dQTtr (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) (U : Array N) : ℝ :=
  if |dQT p m A Aᶜ hA hAc B t U| ≤ 2 * stepEnv (N := N) p B
    then dQT p m A Aᶜ hA hAc B t U else 0

/-- The truncated increment is adapted one step ahead, in the position filtration. -/
theorem stronglyMeasurable_dQTtr (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m (t + 1)] (dQTtr p m A hA hAc B t) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (t + 1)
  have hmeas : Measurable (dQT p m A Aᶜ hA hAc B t) :=
    (stronglyMeasurable_dQT p m t A Aᶜ hA hAc B).measurable
  have hset : MeasurableSet
      {U : Array N | |dQT p m A Aᶜ hA hAc B t U| ≤ 2 * stepEnv (N := N) p B} :=
    measurableSet_le hmeas.abs measurable_const
  exact (Measurable.ite hset hmeas measurable_const).stronglyMeasurable

/-- **The truncated increment is bounded pointwise**, everywhere, by the envelope. -/
theorem abs_dQTtr_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (t : ℕ) (U : Array N) :
    |dQTtr p m A hA hAc B t U| ≤ 2 * stepEnv (N := N) p B := by
  have hE0 : 0 ≤ stepEnv (N := N) p B := stepEnv_nonneg (N := N) hp0 hp1 hB
  unfold dQTtr
  split_ifs with h
  · exact h
  · rw [abs_zero]; linarith

/-- The truncated increment agrees almost surely with the `(locmove)` martingale difference. -/
theorem ae_dQTtr_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    dQTtr p m A hA hAc B t =ᵐ[arrayMeasure N] dQT p m A Aᶜ hA hAc B t := by
  filter_upwards [ae_abs_dQT_le (N := N) hp0 hp1 A Aᶜ hA hAc hid hB (n := t)] with U hU
  unfold dQTtr
  rw [if_pos hU]

/-- The truncated increment is integrable. -/
theorem integrable_dQTtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    Integrable (dQTtr p m A hA hAc B t) (arrayMeasure N) :=
  (integrable_dQT (N := N) hp0.le hp1 m t A Aᶜ hA hAc B).congr
    (ae_dQTtr_eq hp0 hp1 A hA hAc hid hB t).symm

/-- **The truncated increment is a `posFilt`-martingale difference.** -/
theorem condExp_dQTtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    (arrayMeasure N)[dQTtr p m A hA hAc B t | posFilt N p m t] =ᵐ[arrayMeasure N] 0 :=
  (condExp_congr_ae (ae_dQTtr_eq hp0 hp1 A hA hAc hid hB t)).trans
    (condExp_dQT hp0.le hp1 m t A Aᶜ hA hAc B)

/-- The global `Gamma`-half martingale: partial sums of the truncated increments. -/
noncomputable def QG (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) (U : Array N) : ℝ :=
  LocMart.psum (fun j => dQTtr p m A hA hAc B j) t U

theorem QG_succ (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) (U : Array N) :
    QG p m A hA hAc B (t + 1) U = QG p m A hA hAc B t U + dQTtr p m A hA hAc B t U :=
  LocMart.psum_succ _ t U

/-- `QG` is adapted to the position filtration. -/
theorem stronglyMeasurable_QG (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m t] (QG p m A hA hAc B t) :=
  LocMart.stronglyMeasurable_psum (ℱ := posFilt N p m)
    (fun k => stronglyMeasurable_dQTtr p m A hA hAc B k) t

/-- `QG` is integrable at every time. -/
theorem integrable_QG {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    Integrable (QG p m A hA hAc B t) (arrayMeasure N) := by
  induction t with
  | zero =>
      have h0 : QG p m A hA hAc B 0 = fun _ => (0 : ℝ) := LocMart.psum_zero _
      rw [h0]
      exact integrable_const 0
  | succ t ih =>
      have hgoal : QG p m A hA hAc B (t + 1)
          = fun U => QG p m A hA hAc B t U + dQTtr p m A hA hAc B t U := by
        funext U
        exact QG_succ p m A hA hAc B t U
      rw [hgoal]
      exact ih.add (integrable_dQTtr hp0 hp1 A hA hAc hid hB t)

/-- The increments of `QG` are the truncated increments. -/
theorem increments_QG (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (t : ℕ) :
    StoppedWindow.increments (QG p m A hA hAc B) t = dQTtr p m A hA hAc B t := by
  funext U
  rw [StoppedWindow.increments, QG_succ]
  ring

/-- **The increments of `QG` obey the envelope pointwise**, everywhere. -/
theorem abs_increments_QG {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (t : ℕ) (U : Array N) :
    |QG p m A hA hAc B (t + 1) U - QG p m A hA hAc B t U|
      ≤ 2 * stepEnv (N := N) p B := by
  have hdiff : QG p m A hA hAc B (t + 1) U - QG p m A hA hAc B t U
      = dQTtr p m A hA hAc B t U := by
    rw [QG_succ]; ring
  rw [hdiff]
  exact abs_dQTtr_le hp0 hp1 A hA hAc hB t U

/-- The conditional means of the increments of `QG` vanish. -/
theorem condExp_increments_QG {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    (arrayMeasure N)[StoppedWindow.increments (QG p m A hA hAc B) t
      | posFilt N p m t] =ᵐ[arrayMeasure N] 0 := by
  rw [increments_QG]
  exact condExp_dQTtr hp0 hp1 A hA hAc hid hB t

/-! ## 2. The max-growth increment, truncated at `2B` -/

/-- The `(locmove)` max-growth increment `LdM`, truncated at its almost-sure envelope `2B`. -/
noncomputable def lTr (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (t : ℕ) (U : Array N) : ℝ :=
  if |LdM p m t J hJ B U| ≤ 2 * B then LdM p m t J hJ B U else 0

/-- The truncated max-growth increment is adapted one step ahead. -/
theorem stronglyMeasurable_lTr (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m (t + 1)] (lTr p m J hJ B t) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (t + 1)
  have hmeas : Measurable (LdM p m t J hJ B) :=
    (stronglyMeasurable_LdM p m t J hJ B).measurable
  have hset : MeasurableSet {U : Array N | |LdM p m t J hJ B U| ≤ 2 * B} :=
    measurableSet_le hmeas.abs measurable_const
  exact (Measurable.ite hset hmeas measurable_const).stronglyMeasurable

/-- The truncated max-growth increment is bounded pointwise by `2B`. -/
theorem abs_lTr_le {p : ℝ} {m : ℕ} {J : Finset (Fin N)} {hJ : J.Nonempty} {B : ℝ}
    (hB : 0 ≤ B) (t : ℕ) (U : Array N) : |lTr p m J hJ B t U| ≤ 2 * B := by
  unfold lTr
  split_ifs with h
  · exact h
  · rw [abs_zero]; linarith

/-- The truncated max-growth increment agrees almost surely with `LdM`. -/
theorem ae_lTr_eq {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    lTr p m J hJ B t =ᵐ[arrayMeasure N] LdM p m t J hJ B := by
  filter_upwards [abs_LdM_le (p := p) (m := m) (n := t) hp hp1 hJ hB] with U hU
  unfold lTr
  rw [if_pos hU]

/-- The truncated max-growth increment is integrable. -/
theorem integrable_lTr {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    Integrable (lTr p m J hJ B t) (arrayMeasure N) :=
  (integrable_LdM hp hp1 m t J hJ B).congr (ae_lTr_eq hp hp1 J hJ hB t).symm

/-- The truncated max-growth increment is a `posFilt`-martingale difference. -/
theorem condExp_lTr {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    (arrayMeasure N)[lTr p m J hJ B t | posFilt N p m t] =ᵐ[arrayMeasure N] 0 :=
  (condExp_congr_ae (ae_lTr_eq hp hp1 J hJ hB t)).trans
    (condExp_LdM hp hp1 m t J hJ B)

/-- The global max-growth martingale: partial sums of the truncated increments. -/
noncomputable def LG (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (t : ℕ) (U : Array N) : ℝ :=
  LocMart.psum (fun j => lTr p m J hJ B j) t U

theorem LG_succ (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ)
    (t : ℕ) (U : Array N) :
    LG p m J hJ B (t + 1) U = LG p m J hJ B t U + lTr p m J hJ B t U :=
  LocMart.psum_succ _ t U

theorem stronglyMeasurable_LG (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m t] (LG p m J hJ B t) :=
  LocMart.stronglyMeasurable_psum (ℱ := posFilt N p m)
    (fun k => stronglyMeasurable_lTr p m J hJ B k) t

theorem integrable_LG {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    Integrable (LG p m J hJ B t) (arrayMeasure N) := by
  induction t with
  | zero =>
      have h0 : LG p m J hJ B 0 = fun _ => (0 : ℝ) := LocMart.psum_zero _
      rw [h0]
      exact integrable_const 0
  | succ t ih =>
      have hgoal : LG p m J hJ B (t + 1)
          = fun U => LG p m J hJ B t U + lTr p m J hJ B t U := by
        funext U
        exact LG_succ p m J hJ B t U
      rw [hgoal]
      exact ih.add (integrable_lTr hp hp1 J hJ hB t)

theorem increments_LG (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ)
    (t : ℕ) :
    StoppedWindow.increments (LG p m J hJ B) t = lTr p m J hJ B t := by
  funext U
  rw [StoppedWindow.increments, LG_succ]
  ring

theorem abs_increments_LG {p : ℝ} {m : ℕ} (J : Finset (Fin N)) (hJ : J.Nonempty)
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) (U : Array N) :
    |LG p m J hJ B (t + 1) U - LG p m J hJ B t U| ≤ 2 * B := by
  have hdiff : LG p m J hJ B (t + 1) U - LG p m J hJ B t U = lTr p m J hJ B t U := by
    rw [LG_succ]; ring
  rw [hdiff]
  exact abs_lTr_le hB t U

theorem condExp_increments_LG {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    (arrayMeasure N)[StoppedWindow.increments (LG p m J hJ B) t
      | posFilt N p m t] =ᵐ[arrayMeasure N] 0 := by
  rw [increments_LG]
  exact condExp_lTr hp hp1 J hJ hB t

/-! ## 3. The count-free two-endpoint bounds at the literal record clock -/

/-- **The `Gamma`-half two-endpoint deviation at the actual record clock.**  Over every window
`[tau_r + s, tau_r + s + k]` with `s ≤ K` and `k ≤ K - s`, a deviation of the truncated
`(locmove)` `Gamma`-martingale of size `ε` has measure at most
`2 (K+1)^2 exp (-ε^2 / (4 K (2 stepEnv)^2))`.  The record clock enters only through the adapted
disjoint bands `recordBand`; every band's mass is charged once, so there is no union over the
clock values. -/
theorem measureReal_recordClock_QTpair_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {B : ℝ} (hB : 0 < B) (r L K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (RecClockLG.recordCarrier (N := N) p m r L ∩
          StoppedWindow.stoppedWindow (QG p m A hA hAc B)
            (fun U : Array N => recTimeA p m U r) K ε)
      ≤ 2 * ((K : ℝ) + 1) ^ 2 *
          Real.exp (-(ε ^ 2) /
            (4 * (K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hEpos : 0 < stepEnv (N := N) p B := stepEnv_pos (N := N) hp0 hp1.le hB
  have hC : (0 : ℝ) < 2 * stepEnv (N := N) p B := by linarith
  exact StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := arrayMeasure N) (ℱ := posFilt N p m)
    (Q := QG p m A hA hAc B) (σ := fun U : Array N => recTimeA p m U r)
    (B := fun a => RecClockLG.recordBand (N := N) p m r L a)
    (G := RecClockLG.recordCarrier (N := N) p m r L)
    (fun t => stronglyMeasurable_QG p m A hA hAc B t)
    (fun t => integrable_QG hp0 hp1.le A hA hAc disjoint_compl_right hB.le t)
    (fun t => condExp_increments_QG hp0 hp1.le A hA hAc disjoint_compl_right hB.le t)
    hC (fun t U => abs_increments_QG hp0 hp1.le A hA hAc hB.le t U)
    (fun a => RecClockLG.measurableSet_recordBand p m r L a)
    (fun a b hab => RecClockLG.disjoint_recordBand hab)
    (RecClockLG.subset_iUnion_recordBand p m r L)
    (fun a => RecClockLG.carrier_inter_band_subset_clock_eq p m r L a) hK hε

/-- **The max-growth two-endpoint deviation at the actual record clock.**  Same count-free form
with the envelope `2B` of the truncated max-growth martingale. -/
theorem measureReal_recordClock_LGpair_le {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 < B)
    (r L K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        (RecClockLG.recordCarrier (N := N) p m r L ∩
          StoppedWindow.stoppedWindow (LG p m J hJ B)
            (fun U : Array N => recTimeA p m U r) K ε)
      ≤ 2 * ((K : ℝ) + 1) ^ 2 *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (2 * B) ^ 2)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hC : (0 : ℝ) < 2 * B := by linarith
  exact StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := arrayMeasure N) (ℱ := posFilt N p m)
    (Q := LG p m J hJ B) (σ := fun U : Array N => recTimeA p m U r)
    (B := fun a => RecClockLG.recordBand (N := N) p m r L a)
    (G := RecClockLG.recordCarrier (N := N) p m r L)
    (fun t => stronglyMeasurable_LG p m J hJ B t)
    (fun t => integrable_LG hp hp1 J hJ hB.le t)
    (fun t => condExp_increments_LG hp hp1 J hJ hB.le t)
    hC (fun t U => abs_increments_LG J hJ hB.le t U)
    (fun a => RecClockLG.measurableSet_recordBand p m r L a)
    (fun a b hab => RecClockLG.disjoint_recordBand hab)
    (RecClockLG.subset_iUnion_recordBand p m r L)
    (fun a => RecClockLG.carrier_inter_band_subset_clock_eq p m r L a) hK hε

/-! ## 4. A pair deviation at the clock is a stopped-window event -/

/-- Every two-endpoint deviation `|Q t - Q s|` over a window `[s,t]` inside
`[σ, σ + K]` is a member of the stopped-window event `stoppedWindow Q σ K ε`. -/
theorem mem_stoppedWindow_of_pair {Q : ℕ → Array N → ℝ} {σ : Array N → ℕ} {K : ℕ} {ε : ℝ}
    {U : Array N} {s t : ℕ} (h1 : σ U ≤ s) (hst : s ≤ t) (h2 : t ≤ σ U + K)
    (hdev : ε ≤ |Q t U - Q s U|) :
    U ∈ StoppedWindow.stoppedWindow Q σ K ε := by
  refine ⟨s - σ U, by omega, t - s, by omega, ?_⟩
  have h3 : σ U + (s - σ U) = s := Nat.add_sub_cancel' h1
  have h4 : σ U + (s - σ U) + (t - s) = t := by omega
  rw [h4, h3]
  exact hdev

/-! ## 5. The `(locmove)` failure event at the literal actual record clock -/

/-- The actual-clock `(locmove)` failure event: the defect carrier `{d_r ≤ L}`, and a window
`[s,t]` inside `[tau_r, tau_r + (T+3)L]` on which the paper's good window `locmoveGood` holds *at
the record clock*, the `(loccoord)` geometric window `geom s t` holds, and the display fails. -/
def locMoveFailAtClock (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ)
    (geom : ℕ → ℕ → Set (Array N)) (U : Array N) : Prop :=
  RecClockLG.recordCarrier (N := N) p m r L U ∧
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + (T + 3) * L ∧
      locmoveGood p m A hA (r : ℤ) T L B (recTimeA p m U r) s t U ∧ U ∈ geom s t ∧
      ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
          ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U)

/-- **The measured `(locmove)` clause at the literal actual record clock.**

For every truncation level `B > 0`, every `ε₁, ε₂ > 0`, every `(loccoord)` constant `C ≥ 1` with
`1 ≤ gammaRate p m A * C` and error `β ≥ 0`, if the `(loccoord)` budget `bad` has measure at most
`e_b` and the pointwise `(loccoord)` window inequality holds for every window of the record window
(the role of `Loccoord.loccoord_full_window`, carried here as an explicit premise `hcc`), then the
event "on `{d_r ≤ L}`, some `tau_r ≤ s ≤ t ≤ tau_r + (T+3)L` on which `(sep)`, `GoodW`, `GoodStep`
and the pinned record hold, and `W_t - W_s > locmoveRHS`" has measure at most the two clock-anchored
two-endpoint deviation bounds plus `e_b`.

The clock `tau_r = recTimeA p m U r` is the paper's own; there is no union over clock values, no
`tau_r ∧ A` truncation and no record-time tail. -/
theorem measureReal_locMoveFailAtClock_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {T : ℕ} {L : ℕ} (hL : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    {bad : Set (Array N)} {eb : ℝ} {geom : ℕ → ℕ → Set (Array N)}
    (hcc : ∀ s t : ℕ, s ≤ t → ∀ U : Array N, U ∉ bad → U ∈ geom s t →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β)
    (hbad : (arrayMeasure N).real bad ≤ eb) :
    (arrayMeasure N).real
        {U : Array N | locMoveFailAtClock p m A hA hAc r T L B C β ε₁ ε₂ geom U}
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₁ ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))
        + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₂ ^ 2) / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * B) ^ 2))
        + eb := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  have hK1 : 1 ≤ (T + 3) * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- (A) the conull master statement, simultaneously for every deterministic triple
  have hkey : ∀ n0 s t : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGood p m A hA (r : ℤ) T L B n0 s t U ∧ U ∉ bad ∧ U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U := by
    intro n0 s t
    by_cases h1 : n0 ≤ s
    · by_cases h2 : s ≤ t
      · by_cases h3 : t ≤ n0 + (T + 3) * L
        · have h := locmove_ae (N := N) hp0 hp1 hm A hA hAc (Th := T) (Lh := L)
            (by omega : 1 ≤ L) (r := (r : ℤ)) (by exact_mod_cast hr) h1 h2 h3
            (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := C) (β := β) hC1 hγC
            (bad := bad) (geom := geom s t) (hcc s t h2)
          filter_upwards [h] with U hU
          exact fun _ _ _ hconj => hU (by simpa only [locmoveGood, and_assoc] using hconj)
        · filter_upwards with U
          exact fun _ _ h3' => absurd h3' h3
      · filter_upwards with U
        exact fun _ h2' => absurd h2' h2
    · filter_upwards with U
      exact fun h1' => absurd h1' h1
  have hae : ∀ᵐ U ∂(arrayMeasure N), ∀ n0 s t : ℕ,
      n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGood p m A hA (r : ℤ) T L B n0 s t U ∧ U ∉ bad ∧ U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U :=
    MeasureTheory.ae_all_iff.2 fun n0 =>
      MeasureTheory.ae_all_iff.2 fun s =>
        MeasureTheory.ae_all_iff.2 fun t => hkey n0 s t
  -- (B) the three conull sets
  have hG₁ae : ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      dQTtr p m A hA hAc B t U = dQT p m A Aᶜ hA hAc B t U :=
    MeasureTheory.ae_all_iff.2 fun t => ae_dQTtr_eq hp0 hp1.le A hA hAc hid hB.le t
  have hG₂ae : ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U :=
    MeasureTheory.ae_all_iff.2 fun t => ae_lTr_eq hp0.le hp1.le Aᶜ hAc hB.le t
  have hG₁ : (arrayMeasure N)
      {U : Array N | ¬ ∀ t : ℕ, dQTtr p m A hA hAc B t U = dQT p m A Aᶜ hA hAc B t U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hG₁ae
  have hG₂ : (arrayMeasure N)
      {U : Array N | ¬ ∀ t : ℕ, lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hG₂ae
  have haeNull : (arrayMeasure N)
      {U : Array N | ¬ ∀ n0 s t : ℕ, n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
        (locmoveGood p m A hA (r : ℤ) T L B n0 s t U ∧ U ∉ bad ∧ U ∈ geom s t ∧
          (∀ k ≤ t - s,
            |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
          (∀ k ≤ t - s,
            |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
        WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
          ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae
  -- (C) the pointwise reduction
  set S₁ : Set (Array N) :=
    RecClockLG.recordCarrier (N := N) p m r L ∩
      StoppedWindow.stoppedWindow (QG p m A hA hAc B)
        (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₁ with hS₁
  set S₂ : Set (Array N) :=
    RecClockLG.recordCarrier (N := N) p m r L ∩
      StoppedWindow.stoppedWindow (LG p m Aᶜ hAc B)
        (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₂ with hS₂
  set Null : Set (Array N) :=
    {U : Array N | ¬ ∀ n0 s t : ℕ, n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGood p m A hA (r : ℤ) T L B n0 s t U ∧ U ∉ bad ∧ U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U} ∪
    {U : Array N | ¬ ∀ t : ℕ, dQTtr p m A hA hAc B t U = dQT p m A Aᶜ hA hAc B t U} ∪
    {U : Array N | ¬ ∀ t : ℕ, lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U} with hNull
  have hNull0 : (arrayMeasure N).real Null = 0 := by
    have h0 : (arrayMeasure N) Null = 0 := by
      rw [hNull]
      exact measure_union_null (measure_union_null haeNull hG₁) hG₂
    calc (arrayMeasure N).real Null = ((0 : ℝ≥0∞)).toReal := by rw [measureReal_def, h0]
      _ = 0 := ENNReal.toReal_zero
  have hsub : {U : Array N | locMoveFailAtClock p m A hA hAc r T L B C β ε₁ ε₂ geom U}
      ⊆ S₁ ∪ S₂ ∪ (bad ∪ Null) := by
    intro U hU
    obtain ⟨hcarr, s, t, hclk, hst, hwin, hgood, hgeom, hfail⟩ := hU
    by_cases hA1 : U ∈ S₁
    · exact Or.inl (Or.inl hA1)
    by_cases hA2 : U ∈ S₂
    · exact Or.inl (Or.inr hA2)
    by_cases hbadU : U ∈ bad
    · exact Or.inr (Or.inl hbadU)
    by_cases hM : U ∈ Null
    · exact Or.inr (Or.inr hM)
    classical
    simp only [hNull, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, and_assoc] at hM
    obtain ⟨hMaster, htr1, htr2⟩ := hM
    exfalso
    have hdev : (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂) := by
      constructor
      · intro k hk
        by_contra hc
        push Not at hc
        have hmem : U ∈ S₁ := by
          refine ⟨hcarr, mem_stoppedWindow_of_pair hclk (Nat.le_add_right s k) ?_ ?_⟩
          · omega
          · have h1 : LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U
                = QG p m A hA hAc B (s + k) U - QG p m A hA hAc B s U := by
              have h2 := congrFun (LocGroupSimul.psum_sub_eq
                (ξ := fun j => dQT p m A Aᶜ hA hAc B j) s k) U
              have h4t : LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B j) (s + k) U
                  = LocMart.psum (fun j => dQTtr p m A hA hAc B j) (s + k) U := by
                simp only [LocMart.psum]
                exact Finset.sum_congr rfl fun j _ => (htr1 j).symm
              have h4s : LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B j) s U
                  = LocMart.psum (fun j => dQTtr p m A hA hAc B j) s U := by
                simp only [LocMart.psum]
                exact Finset.sum_congr rfl fun j _ => (htr1 j).symm
              rw [h2, h4t, h4s]
              rfl
            rw [← h1]
            exact hc
        exact hA1 hmem
      · intro k hk
        by_contra hc
        push Not at hc
        have hmem : U ∈ S₂ := by
          refine ⟨hcarr, mem_stoppedWindow_of_pair hclk (Nat.le_add_right s k) ?_ ?_⟩
          · omega
          · have h1 : Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U
                = LG p m Aᶜ hAc B (s + k) U - LG p m Aᶜ hAc B s U := by
              have h2 := congrFun (LocMoveLocal.psum_winLInc p m s Aᶜ hAc B k) U
              have h4 : LocMart.psum (LocMoveLocal.winLInc p m s Aᶜ hAc B) k U
                  = LocMart.psum (fun j => lTr p m Aᶜ hAc B (s + j)) k U := by
                simp only [LocMart.psum, LocMoveLocal.winLInc]
                exact Finset.sum_congr rfl fun j _ => (htr2 (s + j)).symm
              have h6 : LocMart.psum (fun j => lTr p m Aᶜ hAc B (s + j)) k U
                  = LG p m Aᶜ hAc B (s + k) U - LG p m Aᶜ hAc B s U :=
                congrFun (LocGroupSimul.psum_sub_eq (ξ := fun j => lTr p m Aᶜ hAc B j) s k) U
              rw [← h2, h4, h6]
            rw [← h1]
            exact hc
        exact hA2 hmem
    have hdisp := hMaster (recTimeA p m U r) s t hclk hst hwin
      ⟨hgood, hbadU, hgeom, hdev.1, hdev.2⟩
    exact hfail hdisp
  -- (D) the union bound
  have hbd₁ := measureReal_recordClock_QTpair_le (N := N) (m := m) hp0 hp1 A hA hAc hB r L
    ((T + 3) * L) hK1 hε₁
  have hbd₂ := measureReal_recordClock_LGpair_le (N := N) (m := m) hp0.le hp1.le Aᶜ hAc hB r L
    ((T + 3) * L) hK1 hε₂
  calc (arrayMeasure N).real
        {U : Array N | locMoveFailAtClock p m A hA hAc r T L B C β ε₁ ε₂ geom U}
      ≤ (arrayMeasure N).real (S₁ ∪ S₂ ∪ (bad ∪ Null)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real (S₁ ∪ S₂) + (arrayMeasure N).real (bad ∪ Null) :=
        measureReal_union_le _ _
    _ ≤ ((arrayMeasure N).real S₁ + (arrayMeasure N).real S₂)
          + ((arrayMeasure N).real bad + (arrayMeasure N).real Null) := by
        have h1 := measureReal_union_le (μ := arrayMeasure N) S₁ S₂
        have h2 := measureReal_union_le (μ := arrayMeasure N) bad Null
        linarith
    _ ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₁ ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))
        + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₂ ^ 2) / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * B) ^ 2))
        + eb := by
        have h1 : (arrayMeasure N).real S₁
            = (arrayMeasure N).real (RecClockLG.recordCarrier (N := N) p m r L ∩
                StoppedWindow.stoppedWindow (QG p m A hA hAc B)
                  (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₁) := by rw [hS₁]
        have h2 : (arrayMeasure N).real S₂
            = (arrayMeasure N).real (RecClockLG.recordCarrier (N := N) p m r L ∩
                StoppedWindow.stoppedWindow (LG p m Aᶜ hAc B)
                  (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₂) := by rw [hS₂]
        rw [h1, h2]
        linarith [hbd₁, hbd₂, hbad, hNull0]

/-! ## 6. The `(loccoord)` carrier instantiated at the paper's constant and error -/

/-- The `(loccoord)` geometric window: the walker minimum at `s` is nonnegative and at least
`r - (T+2)L`, and the running maximum at `t` is at most `r + (T+2)L`.  This is the set on which the
accepted `(loccoord)` display (`Loccoord.loccoord_full_window`) applies. -/
def locCoordGeom (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (r T L : ℕ) :
    ℕ → ℕ → Set (Array N) :=
  fun s t => {U : Array N |
    0 ≤ Xmin p m U A hA s ∧ r - (T + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
      (runMaxA p m U hA t).toNat ≤ r + (T + 2) * L}

/-- **The `(locmove)` measured clause at the literal actual record clock, with the `(loccoord)`
carrier instantiated.**  All `(loccoord)` content is discharged by the accepted
`Loccoord.loccoord_full_window`: the bad set is the paper's `LsBad` at the constant `(2C₀+1)/2`,
the geometric window is `locCoordGeom`, and its error is the paper's
`exp (-c * xOf ((2T+4)L))`.  The two remaining terms are the clock-anchored two-endpoint deviation
bounds of Section 3 — the first and only place where the record clock `tau_r` enters, and it enters
without a union over clock values. -/
theorem exists_measureReal_locMoveFailAtClock_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {C₀ : ℝ} (hC₀1 : 1 ≤ C₀) (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ max L₀ 2, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      ∀ {B ε₁ ε₂ : ℝ}, 0 < B → 0 < ε₁ → 0 < ε₂ →
      (arrayMeasure N).real
          {U : Array N |
            locMoveFailAtClock p m A hA hAc r T L B ((2 * C₀ + 1) / 2)
              ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ) ε₁ ε₂
              (locCoordGeom p m A hA r T L) U}
        ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(ε₁ ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))
          + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(ε₂ ^ 2) / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * B) ^ 2))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
  obtain ⟨c, hc, L₀, hLc⟩ :=
    Loccoord.loccoord_full_window (N := N) hp0 hp1 hm hC₀1 hC₀M
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig T r hr B ε₁ ε₂ hB hε₁ hε₂
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hLbig
  -- the paper's hypothesis `(T+3)L ≤ r` from `(3T+6)L ≤ r`
  have hr' : (T + 3) * L ≤ r :=
    le_trans (Nat.mul_le_mul_right L (by omega : T + 3 ≤ 3 * T + 6)) hr
  set bad : Set (Array N) :=
    LocSumR1.LsBad N p m C₀ ((2 * T + 4) * L) (r - (T + 2) * L) with hbaddef
  have hbadmeas : (arrayMeasure N).real bad ≤ Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
    have h1 := (hLc L hL0 T r hr).1
    rw [measureReal_def]
    calc ((arrayMeasure N) bad).toReal
        ≤ (ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) :=
          ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hβ0 : (0 : ℝ) ≤ ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ) := by
    refine (LocSumAct.betaT_pos ?_).le
    apply LocSumAct.one_le_xOf
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
  have hC1 : (1 : ℝ) ≤ (2 * C₀ + 1) / 2 := by linarith
  have hcc : ∀ s t : ℕ, s ≤ t → ∀ U : Array N, U ∉ bad →
      U ∈ locCoordGeom p m A hA r T L s t →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ ((2 * C₀ + 1) / 2)
            * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
          + 3 * ((2 * C₀ + 1) / 2) *
              ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ) := by
    intro s t hst U hUb hUg
    obtain ⟨hX0, hAle, hLb⟩ := hUg
    have hres := (hLc L hL0 T r hr).2 U hUb A hA s t hst hX0 hAle hLb
    have hRmax : ((Loccoord.Rmax p m U A hA t : ℤ) : ℝ) = ((runMaxA p m U hA t : ℤ) : ℝ) :=
      rfl
    rw [hRmax] at hres
    have hstep : 3 * C₀ * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
        ≤ 3 * ((2 * C₀ + 1) / 2) *
            ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ) := by
      nlinarith [hβ0, hC₀1]
    linarith
  have hmain := measureReal_locMoveFailAtClock_le (N := N) hp0 hp1 (by omega : 1 ≤ m) A hA hAc
    hL2 hr' (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := (2 * C₀ + 1) / 2)
    (β := ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ))
    hB hC1 hγC hε₁ hε₂ (bad := bad)
    (eb := Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)))
    (geom := locCoordGeom p m A hA r T L) hcc hbadmeas
  exact hmain

end ClockLocMove
