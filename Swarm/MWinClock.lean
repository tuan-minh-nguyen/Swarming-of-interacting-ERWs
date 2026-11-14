/-
# The measured `(locmove)` clause at the actual record clock, on the windowed envelope

`ClockLocMove.measureReal_locMoveFailAtClock_le` is the measured `(locmove)` clause of Proposition
`local` at the literal record clock `τ_r`.  Its first error term is the two-endpoint deviation of
the `Γ`-half martingale `QG`, which is built from `dQT`, i.e. from the *prefix* envelope
`LocGroupQ.GoodW`; `PrefixObstruction` shows that envelope is not a function of the `(locmax)`
window, so the clause is not dischargeable on the record window.

This file replaces that martingale by the windowed one of `LocGroupSimul` (`dQTW`, envelope
`2·stepEnv p B`, obtained from `GoodWWin` at level `Aw` together with the record-geometry position
bound), keeping:

* the same process-and-band machinery (`StoppedWindow.measureReal_band_stoppedWindow_le`,
  instantiated at the cumulative windowed martingale `QGW`);
* the same max-growth half (`LG`, `lTr`, `Lcum`, unchanged);
* the same union-bound architecture and the same final error expression
  `2 (K+1)² e^{-ε₁²/(4K(2 envB)²)} + 2 (K+1)² e^{-ε₂²/(4K(2B)²)} + e_b`, `K = (T+3)L`.

The `(locmove)` failure event is now stated with the windowed good window
`MWin.locmoveGoodWin`, whose `W`-conjunct is `LocGroupSimul.winTrunc` (windowed envelope plus
positions `≥ Aw+1`) rather than `GoodW`.  Nothing else changes: no `(loccoord)`, `(lococc)`,
`(locsum)`, `(locgroup)`, tightness, halving, regeneration or speed input is added or claimed.
-/
import Swarm.MWinMove
import Swarm.ClockLocMove

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
open Loccoord Swarming.Enl ClockLocMove

namespace MWin

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The windowed `Γ`-half increment, truncated pointwise at its a.e. envelope -/

/-- `dQTW` truncated at `2 · stepEnv p B`, exactly as `ClockLocMove.dQTtr` truncates `dQT`.  The
truncation is inert almost surely (`ae_dQTWtr_eq`), so the martingale-difference property survives,
while the envelope becomes pointwise, which is what the band estimate needs. -/
noncomputable def dQTWtr (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) (U : Array N) : ℝ :=
  if |dQTW p m t A Aᶜ hA hAc B Aw U| ≤ 2 * stepEnv (N := N) p B
    then dQTW p m t A Aᶜ hA hAc B Aw U else 0

theorem stronglyMeasurable_dQTWtr (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m (t + 1)] (dQTWtr p m A hA hAc B Aw t) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (t + 1)
  have hmeas : Measurable (dQTW p m t A Aᶜ hA hAc B Aw) :=
    (stronglyMeasurable_dQTW p m t A Aᶜ hA hAc B Aw).measurable
  have hset : MeasurableSet
      {U : Array N | |dQTW p m t A Aᶜ hA hAc B Aw U| ≤ 2 * stepEnv (N := N) p B} :=
    measurableSet_le hmeas.abs measurable_const
  exact (Measurable.ite hset hmeas measurable_const).stronglyMeasurable

theorem abs_dQTWtr_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (Aw : ℕ) (t : ℕ) (U : Array N) :
    |dQTWtr p m A hA hAc B Aw t U| ≤ 2 * stepEnv (N := N) p B := by
  have hE0 : 0 ≤ stepEnv (N := N) p B := stepEnv_nonneg (N := N) hp0 hp1 hB
  unfold dQTWtr
  split_ifs with h
  · exact h
  · rw [abs_zero]; linarith

theorem ae_dQTWtr_eq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (Aw : ℕ) (t : ℕ) :
    dQTWtr p m A hA hAc B Aw t =ᵐ[arrayMeasure N] dQTW p m t A Aᶜ hA hAc B Aw := by
  filter_upwards [ae_abs_dQTW_le (N := N) hp0 hp1 A Aᶜ hA hAc hid hB (A := Aw) (n := t)] with U hU
  unfold dQTWtr
  rw [if_pos hU]

theorem integrable_dQTWtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (Aw : ℕ) (t : ℕ) :
    Integrable (dQTWtr p m A hA hAc B Aw t) (arrayMeasure N) :=
  (integrable_dQTW (N := N) hp0.le hp1 m t A Aᶜ hA hAc B Aw).congr
    (ae_dQTWtr_eq hp0 hp1 A hA hAc hid hB Aw t).symm

theorem condExp_dQTWtr {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (Aw : ℕ) (t : ℕ) :
    (arrayMeasure N)[dQTWtr p m A hA hAc B Aw t | posFilt N p m t] =ᵐ[arrayMeasure N] 0 :=
  (condExp_congr_ae (ae_dQTWtr_eq hp0 hp1 A hA hAc hid hB Aw t)).trans
    (condExp_dQTW hp0.le hp1 m t A Aᶜ hA hAc B Aw)

/-! ## 2. The cumulative windowed martingale `QGW` -/

/-- The cumulative windowed `Γ`-half martingale. -/
noncomputable def QGW (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) (U : Array N) : ℝ :=
  LocMart.psum (fun j => dQTWtr p m A hA hAc B Aw j) t U

theorem QGW_succ (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) (U : Array N) :
    QGW p m A hA hAc B Aw (t + 1) U = QGW p m A hA hAc B Aw t U + dQTWtr p m A hA hAc B Aw t U :=
  LocMart.psum_succ _ t U

theorem stronglyMeasurable_QGW (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) :
    StronglyMeasurable[posFilt N p m t] (QGW p m A hA hAc B Aw t) :=
  LocMart.stronglyMeasurable_psum (ℱ := posFilt N p m)
    (fun k => stronglyMeasurable_dQTWtr p m A hA hAc B Aw k) t

theorem integrable_QGW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (Aw : ℕ) (t : ℕ) :
    Integrable (QGW p m A hA hAc B Aw t) (arrayMeasure N) := by
  induction t with
  | zero =>
      have h0 : QGW p m A hA hAc B Aw 0 = fun _ => (0 : ℝ) := LocMart.psum_zero _
      rw [h0]
      exact integrable_const 0
  | succ t ih =>
      have hgoal : QGW p m A hA hAc B Aw (t + 1)
          = fun U => QGW p m A hA hAc B Aw t U + dQTWtr p m A hA hAc B Aw t U := by
        funext U
        exact QGW_succ p m A hA hAc B Aw t U
      rw [hgoal]
      exact ih.add (integrable_dQTWtr hp0 hp1 A hA hAc hid hB Aw t)

theorem increments_QGW (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (B : ℝ) (Aw : ℕ) (t : ℕ) :
    StoppedWindow.increments (QGW p m A hA hAc B Aw) t = dQTWtr p m A hA hAc B Aw t := by
  funext U
  rw [StoppedWindow.increments, QGW_succ]
  ring

theorem abs_increments_QGW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (Aw : ℕ) (t : ℕ) (U : Array N) :
    |QGW p m A hA hAc B Aw (t + 1) U - QGW p m A hA hAc B Aw t U| ≤ 2 * stepEnv (N := N) p B := by
  have hdiff : QGW p m A hA hAc B Aw (t + 1) U - QGW p m A hA hAc B Aw t U
      = dQTWtr p m A hA hAc B Aw t U := by
    rw [QGW_succ]; ring
  rw [hdiff]
  exact abs_dQTWtr_le hp0 hp1 A hA hAc hB Aw t U

theorem condExp_increments_QGW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hid : Disjoint A Aᶜ)
    {B : ℝ} (hB : 0 ≤ B) (Aw : ℕ) (t : ℕ) :
    (arrayMeasure N)[StoppedWindow.increments (QGW p m A hA hAc B Aw) t
      | posFilt N p m t] =ᵐ[arrayMeasure N] 0 := by
  rw [increments_QGW]
  exact condExp_dQTWtr hp0 hp1 A hA hAc hid hB Aw t

/-! ## 3. The two-endpoint deviation at the record clock for the windowed martingale -/

/-- **The windowed `Γ`-half two-endpoint deviation at the actual record clock.**  Same count-free
form as `ClockLocMove.measureReal_recordClock_QTpair_le`, with the cumulative *windowed* martingale
`QGW` in place of `QG`, and the identical envelope `2 · stepEnv p B`. -/
theorem measureReal_recordClock_QTWpair_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {B : ℝ} (hB : 0 < B) (r L K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) (Aw : ℕ) :
    (arrayMeasure N).real
        (RecClockLG.recordCarrier (N := N) p m r L ∩
          StoppedWindow.stoppedWindow (QGW p m A hA hAc B Aw)
            (fun U : Array N => recTimeA p m U r) K ε)
      ≤ 2 * ((K : ℝ) + 1) ^ 2 *
          Real.exp (-(ε ^ 2) /
            (4 * (K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hEpos : 0 < stepEnv (N := N) p B := stepEnv_pos (N := N) hp0 hp1.le hB
  have hC : (0 : ℝ) < 2 * stepEnv (N := N) p B := by linarith
  exact StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := arrayMeasure N) (ℱ := posFilt N p m)
    (Q := QGW p m A hA hAc B Aw) (σ := fun U : Array N => recTimeA p m U r)
    (B := fun a => RecClockLG.recordBand (N := N) p m r L a)
    (G := RecClockLG.recordCarrier (N := N) p m r L)
    (fun t => stronglyMeasurable_QGW p m A hA hAc B Aw t)
    (fun t => integrable_QGW hp0 hp1.le A hA hAc disjoint_compl_right hB.le Aw t)
    (fun t => condExp_increments_QGW hp0 hp1.le A hA hAc disjoint_compl_right hB.le Aw t)
    hC (fun t U => abs_increments_QGW hp0 hp1.le A hA hAc hB.le Aw t U)
    (fun a => RecClockLG.measurableSet_recordBand p m r L a)
    (fun a b hab => RecClockLG.disjoint_recordBand hab)
    (RecClockLG.subset_iUnion_recordBand p m r L)
    (fun a => RecClockLG.carrier_inter_band_subset_clock_eq p m r L a) hK hε


/-! ## 4. The `(locmove)` failure event at the record clock, on the windowed envelope -/

/-- The actual-clock `(locmove)` failure event with the **windowed** good window: the defect
carrier `{d_r ≤ L}`, and a window `[s,t]` inside `[tau_r, tau_r + (T+3)L]` on which
`MWin.locmoveGoodWin` holds (windowed envelope `GoodWWin` at level `Aw` together with positions
`≥ Aw+1`, plus `GoodStep`), the `(loccoord)` geometric window `geom s t` holds, and the display
fails.  No prefix envelope `GoodW` appears. -/
def locMoveFailAtClockWin (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ)
    (geom : ℕ → ℕ → Set (Array N)) (Aw : ℕ) (U : Array N) : Prop :=
  RecClockLG.recordCarrier (N := N) p m r L U ∧
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + (T + 3) * L ∧
      locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw (recTimeA p m U r) s t U ∧
      U ∈ geom s t ∧
      ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
          ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U)

/-- **The measured `(locmove)` clause at the literal actual record clock, on the windowed
envelope.**

For every truncation level `B > 0`, every `ε₁, ε₂ > 0`, every `(loccoord)` constant `C ≥ 1` with
`1 ≤ gammaRate p m A * C` and error `β ≥ 0`, if the `(loccoord)` budget `bad` has measure at most
`e_b` and the pointwise `(loccoord)` window inequality holds for every window of the record window,
then the event "on `{d_r ≤ L}`, some `tau_r ≤ s ≤ t ≤ tau_r + (T+3)L` on which the *windowed* good
window holds and the display fails" has measure at most the two clock-anchored two-endpoint
deviation bounds plus `e_b`.

The first bound is now `measureReal_recordClock_QTWpair_le`, i.e. the deviation of the **windowed**
`Γ`-half martingale (`dQTW`, envelope `2·stepEnv p B`); the second is the unchanged max-growth
bound.  The error constants are identical to `ClockLocMove.measureReal_locMoveFailAtClock_le`. -/
theorem measureReal_locMoveFailAtClockWin_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {T : ℕ} {L : ℕ} (hL : 2 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) {Aw : ℕ} (hC1 : 1 ≤ C)
    (hγC : 1 ≤ gammaRate p m A * C)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    {bad : Set (Array N)} {eb : ℝ} {geom : ℕ → ℕ → Set (Array N)}
    (hcc : ∀ s t : ℕ, s ≤ t → ∀ U : Array N, U ∉ bad → U ∈ geom s t →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ)) + 3 * C * β)
    (hbad : (arrayMeasure N).real bad ≤ eb) :
    (arrayMeasure N).real
        {U : Array N | locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U}
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₁ ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))
        + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₂ ^ 2) / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * B) ^ 2))
        + eb := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  have hL1 : 1 ≤ L := by omega
  have hK1 : 1 ≤ (T + 3) * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- (A) the conull master statement, simultaneously for every deterministic triple
  have hkey : ∀ n0 s t : ℕ, ∀ᵐ U ∂(arrayMeasure N),
      n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw n0 s t U ∧ U ∉ bad ∧
        U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U := by
    intro n0 s t
    by_cases h1 : n0 ≤ s
    · by_cases h2 : s ≤ t
      · by_cases h3 : t ≤ n0 + (T + 3) * L
        · have h := locmove_ae_win (N := N) hp0 hp1 hm A hA hAc (Th := T) (Lh := L)
            (by omega : 1 ≤ L) (r := (r : ℤ)) (by exact_mod_cast hr) h1 h2 h3
            (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := C) (β := β) (Aw := Aw) hC1 hγC
            (bad := bad) (geom := geom s t) (hcc s t h2)
          filter_upwards [h] with U hU
          exact fun _ _ _ hconj => hU (by simpa only [locmoveGoodWin, and_assoc] using hconj)
        · filter_upwards with U
          exact fun _ _ h3' => absurd h3' h3
      · filter_upwards with U
        exact fun _ h2' => absurd h2' h2
    · filter_upwards with U
      exact fun h1' => absurd h1' h1
  have hae : ∀ᵐ U ∂(arrayMeasure N), ∀ n0 s t : ℕ,
      n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw n0 s t U ∧ U ∉ bad ∧
        U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U :=
    MeasureTheory.ae_all_iff.2 fun n0 =>
      MeasureTheory.ae_all_iff.2 fun s =>
        MeasureTheory.ae_all_iff.2 fun t => hkey n0 s t
  -- (B) the three conull sets
  have hG₁ae : ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      dQTWtr p m A hA hAc B Aw t U = dQTW p m t A Aᶜ hA hAc B Aw U :=
    MeasureTheory.ae_all_iff.2 fun t => ae_dQTWtr_eq hp0 hp1.le A hA hAc hid hB.le Aw t
  have hG₂ae : ∀ᵐ U ∂(arrayMeasure N), ∀ t : ℕ,
      lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U :=
    MeasureTheory.ae_all_iff.2 fun t => ae_lTr_eq hp0.le hp1.le Aᶜ hAc hB.le t
  have hG₁ : (arrayMeasure N)
      {U : Array N | ¬ ∀ t : ℕ, dQTWtr p m A hA hAc B Aw t U
        = dQTW p m t A Aᶜ hA hAc B Aw U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hG₁ae
  have hG₂ : (arrayMeasure N)
      {U : Array N | ¬ ∀ t : ℕ, lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hG₂ae
  have haeNull : (arrayMeasure N)
      {U : Array N | ¬ ∀ n0 s t : ℕ, n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
        (locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw n0 s t U ∧ U ∉ bad ∧
          U ∈ geom s t ∧
          (∀ k ≤ t - s,
            |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
          (∀ k ≤ t - s,
            |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
        WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
          ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae
  -- (C) the pointwise reduction
  set S₁ : Set (Array N) :=
    RecClockLG.recordCarrier (N := N) p m r L ∩
      StoppedWindow.stoppedWindow (QGW p m A hA hAc B Aw)
        (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₁ with hS₁
  set S₂ : Set (Array N) :=
    RecClockLG.recordCarrier (N := N) p m r L ∩
      StoppedWindow.stoppedWindow (LG p m Aᶜ hAc B)
        (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₂ with hS₂
  set Null : Set (Array N) :=
    {U : Array N | ¬ ∀ n0 s t : ℕ, n0 ≤ s → s ≤ t → t ≤ n0 + (T + 3) * L →
      (locmoveGoodWin (N := N) p m A hA (r : ℤ) T L B Aw n0 s t U ∧ U ∉ bad ∧
        U ∈ geom s t ∧
        (∀ k ≤ t - s,
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂)) →
      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
        ≤ locmoveRHS (N := N) p m A hA L C β ε₁ ε₂ s t U} ∪
    {U : Array N | ¬ ∀ t : ℕ, dQTWtr p m A hA hAc B Aw t U
      = dQTW p m t A Aᶜ hA hAc B Aw U} ∪
    {U : Array N | ¬ ∀ t : ℕ, lTr p m Aᶜ hAc B t U = LdM p m t Aᶜ hAc B U} with hNull
  have hNull0 : (arrayMeasure N).real Null = 0 := by
    have h0 : (arrayMeasure N) Null = 0 := by
      rw [hNull]
      exact measure_union_null (measure_union_null haeNull hG₁) hG₂
    calc (arrayMeasure N).real Null = ((0 : ℝ≥0∞)).toReal := by rw [measureReal_def, h0]
      _ = 0 := ENNReal.toReal_zero
  have hsub : {U : Array N | locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U}
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
          |LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U| < ε₁) ∧
        (∀ k ≤ t - s,
          |Lcum p m (s + k) Aᶜ hAc B U - Lcum p m s Aᶜ hAc B U| < ε₂) := by
      constructor
      · intro k hk
        by_contra hc
        push Not at hc
        have hmem : U ∈ S₁ := by
          refine ⟨hcarr, mem_stoppedWindow_of_pair hclk (Nat.le_add_right s k) ?_ ?_⟩
          · omega
          · have h1 : LocMart.psum (fun j => dQTW p m (s + j) A Aᶜ hA hAc B Aw) k U
                = QGW p m A hA hAc B Aw (s + k) U - QGW p m A hA hAc B Aw s U := by
              have h2 := congrFun (LocGroupSimul.psum_sub_eq
                (ξ := fun j => dQTW p m j A Aᶜ hA hAc B Aw) s k) U
              have h4t : LocMart.psum (fun j => dQTW p m j A Aᶜ hA hAc B Aw) (s + k) U
                  = LocMart.psum (fun j => dQTWtr p m A hA hAc B Aw j) (s + k) U := by
                simp only [LocMart.psum]
                exact Finset.sum_congr rfl fun j _ => (htr1 j).symm
              have h4s : LocMart.psum (fun j => dQTW p m j A Aᶜ hA hAc B Aw) s U
                  = LocMart.psum (fun j => dQTWtr p m A hA hAc B Aw j) s U := by
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
  have hbd₁ := measureReal_recordClock_QTWpair_le (N := N) (m := m) hp0 hp1 A hA hAc hB r L
    ((T + 3) * L) hK1 hε₁ Aw
  have hbd₂ := measureReal_recordClock_LGpair_le (N := N) (m := m) hp0.le hp1.le Aᶜ hAc hB r L
    ((T + 3) * L) hK1 hε₂
  calc (arrayMeasure N).real
        {U : Array N | locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U}
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
                StoppedWindow.stoppedWindow (QGW p m A hA hAc B Aw)
                  (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₁) := by rw [hS₁]
        have h2 : (arrayMeasure N).real S₂
            = (arrayMeasure N).real (RecClockLG.recordCarrier (N := N) p m r L ∩
                StoppedWindow.stoppedWindow (LG p m Aᶜ hAc B)
                  (fun U : Array N => recTimeA p m U r) ((T + 3) * L) ε₂) := by rw [hS₂]
        rw [h1, h2]
        linarith [hbd₁, hbd₂, hbad, hNull0]

/-! ## 5. Axiom audit -/


end MWin
