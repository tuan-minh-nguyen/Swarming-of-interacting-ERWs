/-
# The literal paper form of display `(locmove)`

## What this file is

`LocalGoodFamily.familyGood_locmove` (and the universal-family form in `UniversalFamily`)
exports display `(locmove)` in the *intermediate* shape

`W_t - W_s <= (1 + Cmax^2)(R_s - min_A X_s) - (t-s)/(1 + Cmax^2) + max (3*Cmax*beta + eps2) (gammaErr + eps1)`

with `max` remainder, `eps1 = eps2 = L^{3/4}` and the window `t <= tau_r + (T+3)L`.  The paper
writes

`W^{A,A^c}_t - W^{A,A^c}_s <= C (R^A_s - min_{i in A} X^i_s) - (t-s)/C + C_T L^{3/4}`

with `C = C(N,m,p)` **independent of `T` and `L`**, `C_T = C_T(N,m,p,T)`, on the record window
`t <= tau_r + T L`.  This file performs that conversion:

* `gammaErr_le` bounds the negative-drift error `gammaErr` by `6m L^{3/4}`, from its literal
  definition via `Real.sqrt (L * sqrt L) = L^{3/4}` (`sqrt_mul_sqrt_eq`);
* `paperC` is the paper's coefficient `C = 1 + Cmax^2`, which depends only on `N, m, p`;
* `paperCT` is the paper's error coefficient `C_T = max (Cerr+1) (6m+1)`;
* `paperMoveRHS` is the paper's right-hand side verbatim;
* `locmoveRHS_le_paperMoveRHS` replaces the `max` remainder by `C_T L^{3/4}`, using
  `LocalGoodFamily.three_mul_Cmax_betaOf`;
* `exists_universal_move_paper` carries the resulting display, **for every nonempty proper `A`**,
  with the paper's record window `t <= tau_r + T L`, joined to the same universal bad event and
  the same measured bound as `UniversalFamily.exists_universal_bad_and_good`.

## Exact boundary

This is the *movement* half only.  `locmoveGood` (the paper's window hypotheses `(sep)`,
truncation `GoodW`, `GoodStep`, pinned record window) and the geometric window `locCoordGeom`
remain explicit hypotheses, exactly as in the finite-family package; nothing is claimed about
their probability or non-vacuity, and no new probabilistic estimate is proved here.  The
`(loccoord)` single-time conversion (direction B1) and the `(lococc)` paper-scale conversion
(direction C) are separate.
-/
import Swarm.UniversalFamily

noncomputable section

set_option maxHeartbeats 2000000
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

namespace LocMovePaper

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The two real-analysis inputs -/

/-- `sqrt (x * sqrt x) = x^{3/4}` for `x >= 0`: the paper's `sqrt (L sqrt L) = L^{3/4}`. -/
theorem sqrt_mul_sqrt_eq {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x * Real.sqrt x) = x ^ ((3 : ℝ) / 4) := by
  rcases lt_or_eq_of_le hx with hx0 | h0
  · have h1 : x ^ ((3 : ℝ) / 2) = x * x ^ (1 / 2 : ℝ) := by
      have h := Real.rpow_add hx0 (1 : ℝ) (1 / 2 : ℝ)
      rw [Real.rpow_one] at h
      rw [show ((1 : ℝ) + 1 / 2) = (3 : ℝ) / 2 from by norm_num] at h
      exact h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← h1, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  · rw [← h0]; simp

/-- **The negative-drift error is `O(L^{3/4})` with coefficient `6m`:**
`gammaErr = (2p-1)/|A| ((2m(1-p)^{(2m-1)|A|} + 4m) sqrt(L sqrt L)) <= 6m L^{3/4}`. -/
theorem gammaErr_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) {Lh : ℕ} (hL : 1 ≤ Lh) :
    LocMoveCompose.gammaErr (N := N) p m A Lh ≤ 6 * (m : ℝ) * (Lh : ℝ) ^ ((3 : ℝ) / 4) := by
  have hp2 : 0 < 2 * p - 1 := by linarith
  have hp3 : 2 * p - 1 ≤ 1 := by linarith
  have hc1 : (1 : ℝ) ≤ (A.card : ℝ) := by
    have := Finset.card_pos.mpr hA
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hfrac : (2 * p - 1) / ((A.card : ℝ)) ≤ 1 := by
    rw [div_le_one hcpos]; linarith
  have hbase0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hbase1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ ((2 * m - 1) * A.card) ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hbr : 2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ) ≤ 6 * (m : ℝ) := by
    nlinarith [hpow, Nat.cast_nonneg (α := ℝ) m]
  have hL0 : (0 : ℝ) < (Lh : ℝ) := by exact_mod_cast hL
  have hLnn : (0 : ℝ) ≤ (Lh : ℝ) := le_of_lt hL0
  have hsqrt : Real.sqrt ((Lh : ℝ) * Real.sqrt (Lh : ℝ)) = (Lh : ℝ) ^ ((3 : ℝ) / 4) :=
    sqrt_mul_sqrt_eq hLnn
  have h34 : (0 : ℝ) ≤ (Lh : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hLnn _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  unfold LocMoveCompose.gammaErr
  rw [hsqrt]
  calc (2 * p - 1) / (A.card : ℝ) *
        ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ))
          * (Lh : ℝ) ^ ((3 : ℝ) / 4))
      ≤ 1 * (6 * (m : ℝ) * (Lh : ℝ) ^ ((3 : ℝ) / 4)) := by
        apply mul_le_mul hfrac ?_ (by positivity) (by linarith)
        exact mul_le_mul hbr le_rfl h34 (by positivity)
    _ = 6 * (m : ℝ) * (Lh : ℝ) ^ ((3 : ℝ) / 4) := by ring

/-! ## 2. The paper's constants and right-hand side -/

/-- **The paper's coefficient `C = 1 + Cmax^2`.**  `Cmax = commonCoordCoefficient N p m` is the
`(loccoord)` coefficient of the common `(locsum)` carrier, so `C` depends on `N, m, p` only —
not on `T`, not on `L`, not on the walker set `A`. -/
noncomputable def paperC (p : ℝ) (m : ℕ) : ℝ :=
  1 + LocalGoodFamily.Cmax (N := N) p m ^ 2

/-- `C = 1 + Cmax^2`, by definition. -/
theorem paperC_eq (p : ℝ) (m : ℕ) :
    paperC (N := N) p m = 1 + LocalGoodFamily.Cmax (N := N) p m ^ 2 := rfl

theorem one_le_paperC (p : ℝ) (m : ℕ) : 1 ≤ paperC (N := N) p m := by
  rw [paperC_eq]; nlinarith [LocalGoodFamily.Cmax_pos (N := N) p m]

theorem paperC_pos (p : ℝ) (m : ℕ) : 0 < paperC (N := N) p m :=
  lt_of_lt_of_le zero_lt_one (one_le_paperC p m)

/-- **The paper's error coefficient `C_T = max (Cerr+1) (6m+1)`**, where `Cerr >= 1` is the
`(loccoord)` error coefficient of the common `(locsum)` carrier. -/
noncomputable def paperCT (m : ℕ) (Cerr : ℝ) : ℝ :=
  max (Cerr + 1) (6 * (m : ℝ) + 1)

theorem paperCT_eq (m : ℕ) (Cerr : ℝ) : paperCT m Cerr = max (Cerr + 1) (6 * (m:ℝ) + 1) := rfl

theorem paperCT_pos (m : ℕ) (Cerr : ℝ) (hCerr : 1 ≤ Cerr) : 0 < paperCT m Cerr := by
  rw [paperCT_eq]
  have : (0:ℝ) < Cerr + 1 := by linarith
  exact lt_of_lt_of_le this (le_max_left _ _)

/-- The `(loccoord)` error coefficient is dominated by the paper's `C_T`, so that a single
constant `C_T` serves both `(loccoord)` and `(locmove)`. -/
theorem Cerr_mul_le_paperCT {m : ℕ} {Cerr : ℝ} (hCerr : 1 ≤ Cerr) (L : ℕ) :
    Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) ≤ paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have h34 : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  apply mul_le_mul_of_nonneg_right ?_ h34
  rw [paperCT_eq]; exact le_trans (by linarith : Cerr ≤ Cerr + 1) (le_max_left _ _)

/-- **The paper's `(locmove)` right-hand side, verbatim:**
`C (R^A_s - min_{i in A} X^i_s) - (t-s)/C + C_T L^{3/4}`. -/
noncomputable def paperMoveRHS (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (Cerr : ℝ) (L s t : ℕ) (U : Array N) : ℝ :=
  paperC (N := N) p m
      * (((runMaxA p m U hA s : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
    - ((t - s : ℕ) : ℝ) / paperC (N := N) p m
    + paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)

/-! ## 3. Replacing the `max` remainder by `C_T L^{3/4}` -/

/-- **The intermediate `(locmove)` right-hand side is at most the paper's**, at the common
coefficient `Cmax = (2 CUmax + 1)/2`, the common error `betaOf Cerr` and `eps1 = eps2 = L^{3/4}`.
The `max` remainder is dominated by `C_T L^{3/4}` with `C_T = max (Cerr+1) (6m+1)` because
`3 Cmax betaOf = Cerr L^{3/4}` and `gammaErr <= 6m L^{3/4}`. -/
theorem locmoveRHS_le_paperMoveRHS {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) {L : ℕ} (hL : 1 ≤ L) {Cerr : ℝ}
    (s t : ℕ) (U : Array N) :
    LocMoveCompose.locmoveRHS (N := N) p m A hA L (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U
      ≤ paperMoveRHS (N := N) p m A hA Cerr L s t U := by
  have h34 : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (by positivity) _
  have hβ : 3 * LocalGoodFamily.Cmax (N := N) p m
      * LocalGoodFamily.betaOf (N := N) p m T L Cerr
      = Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) :=
    LocalGoodFamily.three_mul_Cmax_betaOf (N := N) p m T L Cerr
  have hγ : LocMoveCompose.gammaErr (N := N) p m A L ≤ 6 * (m : ℝ) * (L : ℝ) ^ ((3 : ℝ) / 4) :=
    gammaErr_le (N := N) hp0 hp1 A hA hL
  have hE : max (3 * LocalGoodFamily.Cmax (N := N) p m
        * LocalGoodFamily.betaOf (N := N) p m T L Cerr + (L : ℝ) ^ ((3 : ℝ) / 4))
      (LocMoveCompose.gammaErr (N := N) p m A L + (L : ℝ) ^ ((3 : ℝ) / 4))
      ≤ paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    apply max_le
    · rw [hβ]
      have h1 : (Cerr + 1) * (L : ℝ) ^ ((3 : ℝ) / 4)
          ≤ paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _) h34
      nlinarith [h1, h34]
    · have h1 : (6 * (m : ℝ) + 1) * (L : ℝ) ^ ((3 : ℝ) / 4)
          ≤ paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) h34
      nlinarith [h1, hγ, h34]
  unfold LocMoveCompose.locmoveRHS paperMoveRHS paperC
  linarith [hE]

/-! ## 4. The display for every nonempty proper `A`, on the paper's window -/

/-- **The paper's literal `(locmove)` display, universally in `A` and joined to the universal
bad event.**

Same `Cerr >= 1`, `CT, cT > 0` and threshold `L₀` as
`UniversalFamily.exists_universal_bad_and_good`; the measured bound is repeated here so that this
statement is self-contained.  Beyond the threshold, for every `L >= L₀`, every `r >= (T+3)L`,
every `U` on the record carrier and off `univBad`, **every nonempty proper** `A` satisfies, on
the paper's record window `tau_r <= s <= t <= tau_r + T L` and on the paper's window hypotheses,
`W_t - W_s <= C (R^A_s - min_A X_s) - (t-s)/C + C_T L^{3/4}` with `C = paperC N p m`
(independent of `T`, `L`, `A`) and `C_T = paperCT m Cerr`. -/
theorem exists_universal_move_paper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty), ∀ s t : ℕ,
          recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
          locmoveGood p m A hA (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
          U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t → 
          WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
            ≤ paperMoveRHS (N := N) p m A hA Cerr L s t U) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max L₀ 1, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left L₀ 1) hL) r hr
  · intro L hL r hr U hcarr hnot A hA hAc s t hs hst htK hmg hgeom
    have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
    have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
    -- the window `T L` is inside the exported window `(T+3)L`
    have hK : t ≤ recTimeA p m U r + (T + 3) * L := by
      have hle : T * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
      omega
    obtain ⟨-, -, hlocmove, -⟩ := hgood L hL₀ r hr U hcarr hnot
    have hdisp := hlocmove A hA hAc s t hs hst hK hmg hgeom
    exact le_trans hdisp (locmoveRHS_le_paperMoveRHS (N := N) hp0 hp1 A hA hL1 s t U)

/-! ## 5. `(locmart)` reindexed to the paper's window, with `C_T = 1` -/

/-- **`(locmart)` in the paper's form.**  `RecordClock.locMartGood_spec` is stated for the
increments `[tau_r + s, tau_r + s + k]` with `s + k <= T L`; the paper states it for an arbitrary
sub-window `[s, t]` of `[tau_r, tau_r + T L]`.  The two are the same statement after the
substitution `s' = s - tau_r`, `k = t - s`, and the constant is `C_T = 1`. -/
theorem locmart_recordWindow {p : ℝ} {m r T L : ℕ} {U : Array N}
    (h : U ∈ RecordClock.locMartGood (N := N) p m r T L) :
    ∀ (i : Fin N) (s t : ℕ), recTimeA p m U r ≤ s → s ≤ t →
      t ≤ recTimeA p m U r + T * L →
      |driftMartingale p m U t i - driftMartingale p m U s i| ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  intro i s t hs hst ht
  have h1 : s - recTimeA p m U r ≤ T * L := by omega
  have h2 : t - s ≤ T * L - (s - recTimeA p m U r) := by omega
  have hspec := RecordClock.locMartGood_spec (N := N) h i (s - recTimeA p m U r) (t - s) h1 h2
  rwa [show recTimeA p m U r + (s - recTimeA p m U r) + (t - s) = t from by omega,
    show recTimeA p m U r + (s - recTimeA p m U r) = s from by omega] at hspec

/-! ## 6. The paper-shaped universal bundle -/

/-- **The universal-family local-good theorem in the paper's `(locmart)` and `(locmove)` shapes.**

Same constants and same single bad event `univBad` as
`UniversalFamily.exists_universal_bad_and_good`; compared with that statement,

* `(locmart)` is reindexed to an arbitrary sub-window `[s,t]` of `[tau_r, tau_r + T L]`, with
  `C_T = 1` (`locmart_recordWindow`);
* `(locmove)` is the paper's literal display, at the `T`- and `L`-independent coefficient
  `C = paperC = 1 + Cmax^2`, on the paper's window `t <= tau_r + T L`, with `C_T = paperCT`;
* `(locgroup)` keeps its `C_T = 1` shape and its `T L` window, as exported by the family package;

and everything else (`(loccoord)` at the common coefficient, `(lococc)` at the actual record
fibre, the `GoodWinAllPairs` fibres, the potential support and the `(locsum)` content) is carried
unchanged. -/
theorem exists_universal_paper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
          (∀ (i : Fin N) (s t : ℕ), recTimeA p m U r ≤ s → s ≤ t →
            t ≤ recTimeA p m U r + T * L →
            |driftMartingale p m U t i - driftMartingale p m U s i|
              ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            locmoveGood p m A hA (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
            U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
            WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
              ≤ paperMoveRHS (N := N) p m A hA Cerr L s t U) ∧
          (∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
            U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
            Swarming.Group.average B
                (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
              ≤ LocalGoodFamily.Cmax (N := N) p m
                  * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
                + paperCT m Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          OccDisplayNull.occFace (N := N) p m (LocOccSiteRate.Ccan p m) r T L
            (recTimeA p m U r) U ∧
          (∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
            U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0) ∧
          (∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
            ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
            WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          (∀ j : Fin N, ∀ a0 b0 : ℕ,
            LocOccCarrierAssembly.A0 r T L ≤ a0 →
            b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
            ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
              ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
                + 6 * LocOccSiteRate.Ccan p m
                  * ((betaT (xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ))) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max L₀ 1, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left L₀ 1) hL) r hr
  · intro L hL r hr U hcarr hnot
    have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
    have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
    obtain ⟨hpot, hlocmart, hlocmove, hloccoord, hocc, hgoodwin, hlocgroup, hsum⟩ :=
      hgood L hL₀ r hr U hcarr hnot
    refine ⟨hpot, ?_, ?_, ?_, hocc, hgoodwin, hlocgroup, hsum⟩
    · intro i s t hs hst ht
      exact locmart_recordWindow hlocmart i s t hs hst ht
    · intro A hA hAc s t hs hst htK hmg hgeom
      have hK : t ≤ recTimeA p m U r + (T + 3) * L := by
        have hle : T * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
        omega
      have hdisp := hlocmove A hA hAc s t hs hst hK hmg hgeom
      exact le_trans hdisp (locmoveRHS_le_paperMoveRHS (N := N) hp0 hp1 A hA hL1 s t U)
    · intro B hB s t hst hgeom
      have hstep := Cerr_mul_le_paperCT (m := m) hCerr1 L
      linarith [hloccoord B hB s t hst hgeom]

end LocMovePaper
