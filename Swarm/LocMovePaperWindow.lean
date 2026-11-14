/-
# `(locmove)` on the paper's own window, with the `(loccoord)` carrier discharged

`ClockLocMove.locCoordGeom` is the geometric carrier of the `(loccoord)` display, and it is an
explicit *premise* of the published family clause
`LocalGoodFamily.familyGood_locmove` (and of the `hC` input of `familyGood_loccoord`).  The point
of this file is that on the paper's own window it is not a premise at all.

* `locmoveGood_iff_of_carrier` — on `recordCarrier` the five-conjunct `LocMoveCompose.locmoveGood`
  is equivalent to its first four conjuncts: the level pin `r - L ≤ R^A_{τ_r} ≤ r` is a
  deterministic consequence of the record carrier (`LocCoordGeomCarrier.locmoveGood_pin`), so a
  consumer never has to prove it.
* `familyGood_locmove_paperWindow` — the family `(locmove)` clause on the paper's window
  `[τ_r, τ_r + TL]`, with the hypothesis `U ∈ ClockLocMove.locCoordGeom …` **removed**: it is
  supplied by `LocCoordGeomCarrier.mem_locCoordGeom_of_carrier`.  No new mathematical hypothesis is
  introduced: `hcarr` and `(T+3)L ≤ r` are already hypotheses of every consumer of the family
  headline.  The window is *narrowed* from `(T+3)L` to `TL`, which is the paper's window; the
  `(T+3)L` version cannot drop `locCoordGeom`, the geometric range stops at `(T+2)L`
  (`mem_locCoordGeom_of_carrier_wide`).
* `familyGood_locmove_paperWindow_good` — the same with `locmoveGood` replaced by its four
  non-geometric conjuncts (`ambGood`, `(sep)`, `GoodW`, `GoodStep`), so both the pin and the
  carrier are discharged.
* `loccoord_geom_drop_paperWindow` — the `(loccoord)` input `hC` of `familyGood_loccoord` may be
  stated without its `locCoordGeom` hypothesis on the paper's window.

Nothing here is probabilistic and no display is weakened: the conclusions are the same
`(locmove)`/`(loccoord)` inequalities at the same common constants `Cmax`/`betaOf`.
-/
import Swarm.LocalGoodFamily
import Swarm.LocCoordGeomCarrier

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

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
open LocalGoodFamily

namespace LocCoordGeomCarrier

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. `locmoveGood` without its level pin -/

/-- **The level pin of `locmoveGood` is not a hypothesis.**  On the record carrier the five
conjuncts of `LocMoveCompose.locmoveGood` (at the actual record clock `n₀ = τ_r` and `Lh = L`) are
equivalent to the first four: `ambGood`, `(sep)`, `GoodW` and `GoodStep`.  The fifth,
`r - L ≤ R^A_{τ_r} ≤ r`, is `locmoveGood_pin`. -/
theorem locmoveGood_iff_of_carrier {p : ℝ} {m r L T : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (A : Finset (Fin N)) (hAn : A.Nonempty) (B : ℝ) (s t : ℕ) :
    locmoveGood p m A hAn (r : ℤ) T L B (recTimeA p m U r) s t U ↔
      (U ∈ ambGood p m hAn (r : ℤ) T L ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hAn B U) ∧
        (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U)) := by
  unfold locmoveGood
  constructor
  · rintro ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, locmoveGood_pin (N := N) hcarr hAn⟩

/-- **`locmoveGood` reduced to three conjuncts.**  On the record carrier, `locmoveGood` (at
`n₀ = τ_r`, `Lh = L`) is equivalent to `ambGood ∧ GoodW ∧ GoodStep`: the fifth conjunct is
`locmoveGood_pin`, and the second conjunct `(sep)` for the pair `(A, Aᶜ)` is *itself a conjunct of*
`GoodStep p m n Aᶜ B U = SepSet p m n (Aᶜ)ᶜ Aᶜ U ∧ StepOk p m n Aᶜ B U` (so it is implied by the
fourth, after `Finset.compl_compl`).  Hence the `(locmove)` good window has three irreducible
requirements, not five. -/
theorem locmoveGood_iff_of_carrier_three {p : ℝ} {m r L T : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (A : Finset (Fin N)) (hAn : A.Nonempty) (B : ℝ) (s t : ℕ) :
    locmoveGood p m A hAn (r : ℤ) T L B (recTimeA p m U r) s t U ↔
      (U ∈ ambGood p m hAn (r : ℤ) T L ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hAn B U) ∧
        (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ B U)) := by
  unfold locmoveGood
  constructor
  · rintro ⟨h1, -, h3, h4, -⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨h1, ?_, h3, h4, locmoveGood_pin (N := N) hcarr hAn⟩
    intro n hn
    have hsep := (h4 n hn).1
    simpa using hsep

/-! ## 2. The family `(locmove)` clause on the paper's window -/

/-- **`(locmove)` on `[τ_r, τ_r + TL]` with the `(loccoord)` carrier discharged.**

This is `LocalGoodFamily.familyGood_locmove` with two changes and nothing else: the window is the
paper's `TL` (instead of `(T+3)L`), and the hypothesis `U ∈ ClockLocMove.locCoordGeom …` is gone,
because `mem_locCoordGeom_of_carrier` proves it from the carrier on that window.  The conclusion is
the same display with the same common constants `Cmax`/`betaOf` and the same two `L^{3/4}` errors.
-/
theorem familyGood_locmove_paperWindow {p : ℝ} {m : ℕ} {Cerr : ℝ}
    {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (A : Finset (Fin N)) (hAm : A ∈ moveFam), ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      locmoveGood p m A (hne A hAm) (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
      WA p m U t A Aᶜ (hne A hAm) (hco A hAm) - WA p m U s A Aᶜ (hne A hAm) (hco A hAm)
        ≤ locmoveRHS (N := N) p m A (hne A hAm) L (Cmax (N := N) p m)
            (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
            ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U := by
  intro A hAm s t hτs hst htT hgood
  have htK : t ≤ recTimeA p m U r + (T + 3) * L := by
    have hmul : T * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    omega
  exact familyGood_locmove (N := N) hcarr h A hAm s t hτs hst htK hgood
    (mem_locCoordGeom_of_carrier (N := N) hcarr hr A (hne A hAm) s t hτs hst htT)

/-- **The same clause with the pin discharged as well.**  On the carrier, the `(locmove)` display
at the paper's window follows from `ambGood`, `(sep)`, `GoodW` and `GoodStep` — neither the level
pin of `locmoveGood` nor the `(loccoord)` geometric carrier is a hypothesis. -/
theorem familyGood_locmove_paperWindow_good {p : ℝ} {m : ℕ} {Cerr : ℝ}
    {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (A : Finset (Fin N)) (hAm : A ∈ moveFam), ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m (hne A hAm) (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ (hne A hAm) (RecClockLG.Bstar L) U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ (hne A hAm) (hco A hAm) - WA p m U s A Aᶜ (hne A hAm) (hco A hAm)
        ≤ locmoveRHS (N := N) p m A (hne A hAm) L (Cmax (N := N) p m)
            (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
            ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U := by
  intro A hAm s t hτs hst htT hamb hsep hW hstep
  refine familyGood_locmove_paperWindow (N := N) hcarr hr h A hAm s t hτs hst htT ?_
  exact (locmoveGood_iff_of_carrier (N := N) hcarr A (hne A hAm) (RecClockLG.Bstar L) s t).mpr
    ⟨hamb, hsep, hW, hstep⟩

/-- **The paper's `(locmove)` with only the three irreducible good-window requirements.**  Same as
`familyGood_locmove_paperWindow_good` with `(sep)` dropped: on the carrier it is a conjunct of
`GoodStep p m n Aᶜ`. -/
theorem familyGood_locmove_paperWindow_good3 {p : ℝ} {m : ℕ} {Cerr : ℝ}
    {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (A : Finset (Fin N)) (hAm : A ∈ moveFam), ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
      U ∈ ambGood p m (hne A hAm) (r : ℤ) T L →
      (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ (hne A hAm) (RecClockLG.Bstar L) U) →
      (∀ n ∈ Finset.Ico s t, GoodStep p m n Aᶜ (RecClockLG.Bstar L) U) →
      WA p m U t A Aᶜ (hne A hAm) (hco A hAm) - WA p m U s A Aᶜ (hne A hAm) (hco A hAm)
        ≤ locmoveRHS (N := N) p m A (hne A hAm) L (Cmax (N := N) p m)
            (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
            ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U := by
  intro A hAm s t hτs hst htT hamb hW hstep
  refine familyGood_locmove_paperWindow (N := N) hcarr hr h A hAm s t hτs hst htT ?_
  exact (locmoveGood_iff_of_carrier_three (N := N) hcarr A (hne A hAm) (RecClockLG.Bstar L)
    s t).mpr ⟨hamb, hW, hstep⟩

/-! ## 3. Dropping the `(loccoord)` carrier from the `(locsum)` input of `familyGood_loccoord` -/

/-- **The `(loccoord)` input of `familyGood_loccoord` without its geometric carrier.**

`LocalGoodFamily.familyGood_loccoord` consumes `hC`, which takes
`U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t` as a hypothesis.  On the paper's window that
membership is a theorem about the carrier (`mem_locCoordGeom_of_carrier`), so `hC` may be stated
without it, at the price of the explicit window bound `τ_r ≤ s`, `t ≤ τ_r + TL`.  This is the
`(loccoord)` counterpart of `familyGood_locmove_paperWindow`. -/
theorem loccoord_geom_drop_paperWindow {p : ℝ} {m : ℕ} {T : ℕ} {L₀ : ℕ} {Cerr : ℝ}
    (hC : ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∉ locSumBadCommon (N := N) p m r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ LocalGoodFamily.Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * LocalGoodFamily.Cmax (N := N) p m * betaOf (N := N) p m T L Cerr)
    {L : ℕ} (hL : L₀ ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r) {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hU : U ∉ locSumBadCommon (N := N) p m r T L) :
    ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      recTimeA p m U r ≤ s → t ≤ recTimeA p m U r + T * L →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ LocalGoodFamily.Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * LocalGoodFamily.Cmax (N := N) p m * betaOf (N := N) p m T L Cerr := by
  intro B hB s t hst hτs htT
  exact hC L hL r hr U hU B hB s t hst
    (mem_locCoordGeom_of_carrier (N := N) hcarr hr B hB s t hτs hst htT)

/-! ## 4. `ClockLocMove`'s `(T+3)L` failure event with no geometric premise

`ClockLocMove.locMoveFailAtClock` quantifies over *every* window inside `[τ_r, τ_r+(T+3)L]` and
carries the `(loccoord)` carrier `geom` as a conjunct.  At the paper's slack `(T+2)L` that conjunct
has content on the last `L` of the window (`RANGE_FRONTIER.md`), so it cannot be dropped there.  At
slack `(T+4)L` it can: `mem_locCoordGeomSlack_clockWindow` covers the whole `(T+3)L` box.  The two
theorems below make that exact — the failure event computed with the slack carrier is the same set
as the one computed with `Set.univ`, and the measured `(locmove)` bound therefore holds with no
geometric hypothesis at all, only the record carrier and `(T+4)L ≤ r`. -/

/-- **The geometric conjunct of `locMoveFailAtClock` is `Set.univ` at slack `(T+4)L`.**  For a
trajectory on the record carrier, the failure event computed with the slack `(loccoord)` carrier
`locCoordGeomSlack (T+4)` is *the same set* as the one computed with `Set.univ`: the carrier
membership is automatic on the whole `(T+3)L` window. -/
theorem locMoveFailAtClock_geomSlack_iff_univ {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    (A : Finset (Fin N)) (hAn : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {B C β ε₁ ε₂ : ℝ} (hr : (T + 4) * L ≤ r) :
    ClockLocMove.locMoveFailAtClock p m A hAn hAc r T L B C β ε₁ ε₂
        (locCoordGeomSlack (N := N) (T + 4) p m A hAn r L) U ↔
      ClockLocMove.locMoveFailAtClock p m A hAn hAc r T L B C β ε₁ ε₂ (fun _ _ => Set.univ) U := by
  unfold ClockLocMove.locMoveFailAtClock
  constructor
  · rintro ⟨hc, s, t, h1, h2, h3, h4, -, h6⟩
    exact ⟨hc, s, t, h1, h2, h3, h4, Set.mem_univ _, h6⟩
  · rintro ⟨hc, s, t, h1, h2, h3, h4, -, h6⟩
    exact ⟨hc, s, t, h1, h2, h3, h4,
      mem_locCoordGeomSlack_clockWindow (N := N) hc hr A hAn s t h1 h2 h3, h6⟩

/-- **The measured `(locmove)` clause at the actual record clock with no geometric carrier.**

This is `ClockLocMove.measureReal_locMoveFailAtClock_le` at `geom := Set.univ` (the failure event
with the `(loccoord)` carrier removed), for the `(loccoord)` display at slack `(T+4)L`.  Its
hypotheses are the three genuinely non-geometric ones — the record carrier, the `(locsum)` bad set
with its bound, and the `(loccoord)` display at slack `(T+4)L` — and the conclusion is the paper's
two clock-anchored deviation bounds plus `eb`. -/
theorem measureReal_locMoveFailAtClock_le_noGeom {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin N)) (hAn : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {T : ℕ} {L : ℕ} (hL : 2 ≤ L) {r : ℕ} (hr : (T + 4) * L ≤ r)
    {B ε₁ ε₂ C β : ℝ} (hB : 0 < B) (hC1 : 1 ≤ C) (hγC : 1 ≤ gammaRate p m A * C)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    {bad : Set (Swarming.Uniform.Array N)} {eb : ℝ}
    (hcc : ∀ s t : ℕ, s ≤ t → ∀ U : Swarming.Uniform.Array N, U ∉ bad →
      U ∈ locCoordGeomSlack (N := N) (T + 4) p m A hAn r L s t →
      Swarming.Group.average A
        (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
        ≤ C * (((runMaxA p m U hAn t : ℤ) : ℝ) - ((Xmin p m U A hAn s : ℤ) : ℝ)) + 3 * C * β)
    (hbad : (arrayMeasure N).real bad ≤ eb) :
    (arrayMeasure N).real
        {U : Swarming.Uniform.Array N |
          ClockLocMove.locMoveFailAtClock p m A hAn hAc r T L B C β ε₁ ε₂ (fun _ _ => Set.univ) U}
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₁ ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))
        + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(ε₂ ^ 2) / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * B) ^ 2))
        + eb := by
  have hr' : (T + 3) * L ≤ r := by
    have hmul : (T + 3) * L ≤ (T + 4) * L := Nat.mul_le_mul_right L (by omega)
    omega
  have hmain := ClockLocMove.measureReal_locMoveFailAtClock_le (N := N) hp0 hp1 hm A hAn hAc hL hr'
    (B := B) (ε₁ := ε₁) (ε₂ := ε₂) (C := C) (β := β) hB hC1 hγC hε₁ hε₂
    (bad := bad) (eb := eb) (geom := locCoordGeomSlack (N := N) (T + 4) p m A hAn r L) hcc hbad
  have hset : {U : Swarming.Uniform.Array N |
      ClockLocMove.locMoveFailAtClock p m A hAn hAc r T L B C β ε₁ ε₂ (fun _ _ => Set.univ) U}
      = {U : Swarming.Uniform.Array N |
        ClockLocMove.locMoveFailAtClock p m A hAn hAc r T L B C β ε₁ ε₂
          (locCoordGeomSlack (N := N) (T + 4) p m A hAn r L) U} := by
    ext U
    exact (locMoveFailAtClock_geomSlack_iff_univ (N := N) A hAn hAc
      (B := B) (C := C) (β := β) (ε₁ := ε₁) (ε₂ := ε₂) hr).symm
  rw [hset]
  exact hmain

end LocCoordGeomCarrier

/-! ## Axiom audit (source order) -/


/-! ## Axiom audit of the clock-window results -/


