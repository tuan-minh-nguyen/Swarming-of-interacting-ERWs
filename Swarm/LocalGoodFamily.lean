/-
# The local-good event quantified over a finite family of walker groups

## What this file is

`LocalGoodAll` proves, for **one fixed** proper walker set `A` and **one fixed** disjoint pair
`I, J`, a measured bad event `LocalBad` with `(arrayMeasure N).real LocalBad <= CT * exf cT L`,
and derives the component clauses of Proposition `local` off it.  The proposition itself
quantifies over **all** nonempty proper `A ⊂ Fin N` and **all** disjoint nonempty `I, J`, with
constants `c_T, C_T` depending only on `N, m, p, T`.

This file closes that quantifier.  Its bad event is one set `famBad` for a finite family of
groups, and off it every group of the family simultaneously satisfies its clauses on the carrier.
Two genuine changes make this more than a repeated union bound:

* **One `(locsum)` carrier.**  `RecordGroupUniform.exists_loccoord_common` gives the `(locsum)`
  bad set at the group-independent constant `CUmax N p m`, together with its `(loccoord)`
  content at the single coefficient `commonCoordCoefficient N p m = (2 CUmax + 1)/2` and the
  single error `CTof CUmax T * L^{3/4}`.  So the `(locsum)`/`(loccoord)` event is charged once
  and the `(loccoord)` display is uniform over all groups (`loccoord_of_not_mem`).
* **One `(locmove)` coefficient.**  `moveBadCommon` is the `(locmove)` failure event at that same
  coefficient `Cmax = commonCoordCoefficient` and the common error `betaOf Cerr`, using the same
  common `(locsum)` set `locSumBadCommon` as its `(loccoord)` input
  (`ClockLocMove.measureReal_locMoveFailAtClock_le` with `bad := locSumBadCommon`).  Hence the
  `(locmove)` clause holds with the coefficient `1 + Cmax^2` — independent of the group — in the
  form `W_t - W_s <= (1 + Cmax^2)(R_s - X_s) - (t-s)/(1 + Cmax^2) + gammaErr + L^{3/4}`
  (`locmoveRHS`), i.e. the paper's `C` independent of `A`.
* **The `(lococc)` display.**  `OccDisplayNull.occNull` is the named null event of
  `lococc_recordCarrier_allPairs_singleWindow`; it is part of the bad event, so off `famBad` the
  literal pointwise occupation display holds at every record fibre, not merely `GoodWinAllPairs`
  membership (`lococc_of_not_mem`).

Everything else (`(locmax)`, `(locmart)`, the potential support, the `(locsum)` pointwise
content, the `(locgroup)` pairs) is charged per clause as in `LocalGoodAll`.

## Scope

* The family is a pair of `Finset`s of walker sets `(moveFam, grpFam)` with their nonemptiness,
  complement-nonemptiness and disjointness hypotheses.  Nothing assumes one group's bad set
  contains another's; each group contributes its own terms.
* `CT` and `cT` depend on the family only through its cardinality (via `Finset.sum`); for the
  universal family `allMoveFam`/`allGrpFam` this is a function of `N` alone, which is exactly
  Proposition `local`'s `C_T = C_T(N,m,p,T)`.
* `(sep)`, `locmoveGood` (which contains `GoodW`, `GoodStep` and the pinned record window),
  `locCoordGeom`, and the `(locsum)` range content remain **carriers/hypotheses** of the
  corresponding displays.  No probability is claimed for them, no non-vacuity, no separation
  survival, no blocks, tightness, speed or `MainClaim`.
-/
import Swarm.OccDisplayNull
import Swarm.UnifiedGroupCoefficient
import Swarm.LocalGoodAll

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

namespace LocalGoodFamily

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The group-independent constants of the family -/

/-- The `(locsum)`/`(loccoord)`/`(locmove)` coefficient that is common to **all** nonempty walker
groups: `(2 CUmax + 1)/2` at the maximum `CUmax` of the group constants. -/
noncomputable def Cmax (p : ℝ) (m : ℕ) : ℝ :=
  RecordGroupUniform.commonCoordCoefficient N p m

theorem one_le_Cmax (p : ℝ) (m : ℕ) : 1 ≤ Cmax (N := N) p m :=
  RecordGroupUniform.one_le_commonCoordCoefficient (N := N) p m

theorem Cmax_pos (p : ℝ) (m : ℕ) : 0 < Cmax (N := N) p m :=
  lt_of_lt_of_le zero_lt_one (one_le_Cmax p m)

/-- The common `(loccoord)` error parameter at the common error coefficient `Cerr`, chosen so
that the `(locmove)` composition sees exactly `Cerr * L^{3/4}`. -/
noncomputable def betaOf (p : ℝ) (m : ℕ) (T L : ℕ) (Cerr : ℝ) : ℝ :=
  Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) / (3 * Cmax (N := N) p m)

theorem three_mul_Cmax_betaOf (p : ℝ) (m : ℕ) (T L : ℕ) (Cerr : ℝ) :
    3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr
      = Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hC : Cmax (N := N) p m ≠ 0 := ne_of_gt (Cmax_pos p m)
  unfold betaOf
  field_simp

/-! ## 2. The group-independent part of the bad event -/

/-- The single `(locsum)` bad set at the maximum group constant: it serves every group at once. -/
abbrev locSumBadCommon (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  LocSumR1.LsBad N p m (RecordGroupUniform.CUmax N p m) ((2 * T + 4) * L) (r - (T + 2) * L)

/-- The `(lococc)` failure of the all-pairs single-window event together with the named null
event of the occupation display: both are "zero-cost" pieces of the bad event. -/
def zeroBad (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  LocalGoodAll.potBad (N := N) p m
    ∪ OccDisplayNull.occNull (N := N) p m (LocOccSiteRate.Ccan p m) r T L

/-- **The group-independent bad event** of Proposition `local`: the `(locsum)` defect at the
`(lococc)` scale, the `(lococc)` clock-fibre union, the common `(locsum)` defect, the `(locmax)`
defect, the `(locmart)` defect, and the zero-cost potential support plus occupation null event. -/
def commonBad (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  LocalGoodAll.sumBadOcc (N := N) p m r T L ∪ LocalGoodAll.occBad (N := N) p m r T L
    ∪ locSumBadCommon (N := N) p m r T L ∪ LocGroupSimul.LocMaxBad (N := N) p m r T L
    ∪ RecordClock.locMartBad (N := N) p m r T L ∪ zeroBad (N := N) p m r T L

/-- The `(locsum)` content that `(lococc)` needs, in the shape of the source display. -/
theorem locsumContent {p : ℝ} {m : ℕ} {C : ℝ} {L : ℕ} {r T : ℕ}
    (h : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
    (j : Fin N) (U : Array N) (hU : U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L))
    (a b : ℕ) (ha : A0 r T L ≤ a) (hb : b ≤ A0 r T L + Lw T L) (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
      ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ) :=
  h j U hU a b ha hb hab

/-- The zero-cost part has measure zero: the forward-potential support is a.e. and the occupation
failure event is the named null event of `OccDisplayNull`. -/
theorem measureReal_zeroBad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) {L : ℕ} (hL1 : 1 ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m (LocOccSiteRate.Ccan p m) (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * (LocOccSiteRate.Ccan p m) * ((b : ℝ) - (a : ℝ))
            + 6 * (LocOccSiteRate.Ccan p m) * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    (arrayMeasure N).real (zeroBad (N := N) p m r T L) = 0 := by
  have hpot : (arrayMeasure N) (LocalGoodAll.potBad (N := N) p m) = 0 :=
    ae_iff.mp (ae_bddAbove_Gtrunc_arrayMeasure (N := N) hp0 hp1 hm)
  have hocc : (arrayMeasure N)
      (OccDisplayNull.occNull (N := N) p m (LocOccSiteRate.Ccan p m) r T L) = 0 :=
    OccDisplayNull.measure_occNull (N := N) hp0 hp1 hm (LocOccSiteRate.one_le_Ccan p m) hL1 hT hr
      hLsum
  have hz : (arrayMeasure N) (zeroBad (N := N) p m r T L) = 0 := by
    unfold zeroBad
    rw [measure_union_null hpot hocc]
  rw [measureReal_def, hz, ENNReal.toReal_zero]


/-! ## 3. The measured bound for the group-independent part -/

/-- **One measured bound for all the group-independent clauses at once.**  The `(locsum)` defects
(at the `(lococc)` and `(loccoord)` scales), the `(lococc)` clock-fibre union, `(locmax)`,
`(locmart)`, the potential support and the occupation null event are all charged to a single
`CT * exf cT L`, with constants independent of the walker group. -/
theorem exists_commonBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N) :
    ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (commonBad (N := N) p m r T L) ≤ CT * LocalGoodAll.exf cT L := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  -- (1) `(locsum)` at the `(lococc)` scale
  obtain ⟨c₁, hc₁, L₁, h₁⟩ :=
    LocOccSiteRate.exists_lsBad_rate_single_window (N := N) hp0 hp1 hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m) T
  -- (2) `(lococc)` all-pair clock-fibre union
  obtain ⟨c₂, hc₂, C₂, hC₂, L₂, h₂⟩ :=
    LocOccAllPairFibreSum.exists_iUnion_allPairs_complement_paper_canonical_offDiag
      (N := N) (p := p) (m := m) hp0 hp1 hm hN (T := T) hT
  -- (3) the common `(locsum)` carrier at `CUmax`, and its `(loccoord)` content
  obtain ⟨c₃, C₃, hc₃, hC₃1, L₃, h₃⟩ :=
    RecordGroupUniform.exists_loccoord_common (N := N) hp0 hp1 hm T
  -- (4) `(locmax)`
  obtain ⟨c₅, hc₅, L₅, h₅⟩ := LocGroupSimul.exists_locMaxBad_le (N := N) hp0 hp1 hm T hT
  -- (5) `(locmart)`
  obtain ⟨c₇, hc₇, L₇, h₇⟩ := RecordClock.exists_locMartBad_le (N := N) hp0 hp1 hm hN T hT
  -- (6) the `(locsum)` pointwise content at the `(lococc)` scale (for the display's null event)
  obtain ⟨c₉, hc₉, L₉, h₉⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨(((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃) + 1) + 1,
    min (min (min (min c₁ c₂) c₃) c₅) c₇, ?_,
    lt_min (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₅) hc₇,
    max (max (max (max (max (max (max L₁ L₂) L₃) L₅) L₇) L₉) L₁₀) 1, ?_⟩
  · -- positivity of the coefficient
    have h0 : (0 : ℝ) ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ :=
      mul_nonneg (by positivity) hC₂
    have h1 : (1 : ℝ) ≤ C₃ := hC₃1
    linarith
  intro L hL r hr
  have hL1 : L₁ ≤ L := by omega
  have hL2 : L₂ ≤ L := by omega
  have hL3 : L₃ ≤ L := by omega
  have hL5 : L₅ ≤ L := by omega
  have hL7 : L₇ ≤ L := by omega
  have hL9 : L₉ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  have hLpos : 1 ≤ L := by omega
  -- the `(locsum)` content of the common constant
  have hside : 2 * ellT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
      ≤ LocOccCarrierAssembly.A0 r T L := by
    have hArith : L + (T + 2) * L ≤ r := by
      have hEq : L + (T + 2) * L = (T + 3) * L := by ring
      rw [hEq]; exact hr
    have hLA0 : L ≤ LocOccCarrierAssembly.A0 r T L := by
      unfold LocOccCarrierAssembly.A0
      exact Nat.le_sub_of_add_le hArith
    exact le_trans (hL₁₀ L hL10) hLA0
  have hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m (LocOccSiteRate.Ccan p m) (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * (LocOccSiteRate.Ccan p m) * ((b : ℝ) - (a : ℝ))
            + 6 * (LocOccSiteRate.Ccan p m) * ((betaT (xOf (Lw T L)) : ℕ) : ℝ) :=
    fun j U hU a b ha hb hab =>
      (h₉ (LocOccCarrierAssembly.Lw T L)
        (le_trans hL9 (LocOccCarrierAssembly.le_Lw T L)) (A0 r T L) hside).2
        U hU j a b ha hb hab
  -- each component at the common `L`
  have hB1 : (arrayMeasure N).real (LocalGoodAll.sumBadOcc (N := N) p m r T L)
      ≤ 1 * LocalGoodAll.exf c₁ L := by
    have hb := (h₁ L hL1 (r := r) hr)
    have hreal : (arrayMeasure N).real (LocalGoodAll.sumBadOcc (N := N) p m r T L)
        ≤ Real.exp (-c₁ * LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) := by
      rw [measureReal_def]
      refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hLle : L ≤ LocOccCarrierAssembly.Lw T L := by
      unfold LocOccCarrierAssembly.Lw
      calc L = L * 1 := (Nat.mul_one L).symm
        _ ≤ L * (2 * T + 2) := Nat.mul_le_mul_left L (by omega)
        _ = (2 * T + 2) * L := Nat.mul_comm _ _
        _ ≤ (2 * T + 2) * L + 1 := Nat.le_succ _
    have hmono : LocSumAct.xOf L ≤ LocSumAct.xOf (LocOccCarrierAssembly.Lw T L) := by
      apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLle) (by norm_num)
    have hexp : Real.exp (-c₁ * LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
        ≤ LocalGoodAll.exf c₁ L := by
      unfold LocalGoodAll.exf
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [one_mul]
    exact le_trans hreal hexp
  have hB2 : (arrayMeasure N).real (LocalGoodAll.occBad (N := N) p m r T L)
      ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * LocalGoodAll.exf c₂ L := by
    have hb := h₂ L hL2 (r := r) hr
    simpa only [LocalGoodAll.occBad, LocalGoodAll.exf, LocSumAct.xOf] using hb
  have hB3 : (arrayMeasure N).real (locSumBadCommon (N := N) p m r T L)
      ≤ C₃ * LocalGoodAll.exf c₃ L := by
    have hb := (h₃ L hL3 r hr).1
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hB5 : (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L)
      ≤ 1 * LocalGoodAll.exf c₅ L := by
    have hb := h₅ L hL5 r hr
    rw [one_mul]
    have hreal : (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L)
        ≤ Real.exp (-c₅ * LocSumAct.xOf L) := by
      rw [measureReal_def]
      refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simpa only [LocalGoodAll.exf, LocSumAct.xOf, neg_mul] using hreal
  have hB7 : (arrayMeasure N).real (RecordClock.locMartBad (N := N) p m r T L)
      ≤ 1 * LocalGoodAll.exf c₇ L := by
    have hb := h₇ L hL7 r
    have hxeq : RecordClock.xOf L = LocSumAct.xOf L := rfl
    rw [hxeq] at hb
    rw [one_mul]
    simpa only [LocalGoodAll.exf, LocSumAct.xOf, neg_mul] using hb
  have hB6 : (arrayMeasure N).real (zeroBad (N := N) p m r T L) ≤ 0 * LocalGoodAll.exf c₁ L := by
    rw [zero_mul, measureReal_zeroBad (N := N) hp0 hp1 hm hT hLpos hr hLsum]
  -- the union bound
  have hunion : (arrayMeasure N).real (commonBad (N := N) p m r T L)
      ≤ (arrayMeasure N).real (LocalGoodAll.sumBadOcc (N := N) p m r T L)
        + (arrayMeasure N).real (LocalGoodAll.occBad (N := N) p m r T L)
        + (arrayMeasure N).real (locSumBadCommon (N := N) p m r T L)
        + (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L)
        + (arrayMeasure N).real (RecordClock.locMartBad (N := N) p m r T L)
        + (arrayMeasure N).real (zeroBad (N := N) p m r T L) := by
    have h1 := measureReal_union_le (μ := arrayMeasure N)
      (LocalGoodAll.sumBadOcc (N := N) p m r T L ∪ LocalGoodAll.occBad (N := N) p m r T L
        ∪ locSumBadCommon (N := N) p m r T L ∪ LocGroupSimul.LocMaxBad (N := N) p m r T L
        ∪ RecordClock.locMartBad (N := N) p m r T L) (zeroBad (N := N) p m r T L)
    have h2 := measureReal_union_le (μ := arrayMeasure N)
      (LocalGoodAll.sumBadOcc (N := N) p m r T L ∪ LocalGoodAll.occBad (N := N) p m r T L
        ∪ locSumBadCommon (N := N) p m r T L ∪ LocGroupSimul.LocMaxBad (N := N) p m r T L)
      (RecordClock.locMartBad (N := N) p m r T L)
    have h3 := measureReal_union_le (μ := arrayMeasure N)
      (LocalGoodAll.sumBadOcc (N := N) p m r T L ∪ LocalGoodAll.occBad (N := N) p m r T L
        ∪ locSumBadCommon (N := N) p m r T L) (LocGroupSimul.LocMaxBad (N := N) p m r T L)
    have h4 := measureReal_union_le (μ := arrayMeasure N)
      (LocalGoodAll.sumBadOcc (N := N) p m r T L ∪ LocalGoodAll.occBad (N := N) p m r T L)
      (locSumBadCommon (N := N) p m r T L)
    have h5 := measureReal_union_le (μ := arrayMeasure N)
      (LocalGoodAll.sumBadOcc (N := N) p m r T L) (LocalGoodAll.occBad (N := N) p m r T L)
    unfold commonBad
    linarith [h1, h2, h3, h4, h5]
  have hkey : (arrayMeasure N).real (commonBad (N := N) p m r T L)
      ≤ 1 * LocalGoodAll.exf c₁ L
        + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * LocalGoodAll.exf c₂ L
        + C₃ * LocalGoodAll.exf c₃ L + 1 * LocalGoodAll.exf c₅ L
        + 1 * LocalGoodAll.exf c₇ L + 0 * LocalGoodAll.exf c₁ L := by
    linarith [hunion, hB1, hB2, hB3, hB5, hB7, hB6]
  refine le_trans hkey ?_
  have hC10 : (0 : ℝ) ≤ 1 := by norm_num
  have hC20 : (0 : ℝ) ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ := by positivity
  have hC30 : (0 : ℝ) ≤ C₃ := le_trans zero_le_one hC₃1
  -- the fold into one profile term
  have s1 : 1 * LocalGoodAll.exf c₁ L
        + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * LocalGoodAll.exf c₂ L
      ≤ (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        * LocalGoodAll.exf (min c₁ c₂) L := by
    have h := LocalGoodAll.exf_two (C₁ := 1) (C₂ := ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
      (c₁ := c₁) (c₂ := c₂) hC10 hC20 hc₁ hc₂ L
    exact h
  have s2 : (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) * LocalGoodAll.exf (min c₁ c₂) L
        + C₃ * LocalGoodAll.exf c₃ L
      ≤ ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃)
        * LocalGoodAll.exf (min (min c₁ c₂) c₃) L :=
    LocalGoodAll.exf_two (C₁ := 1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) (C₂ := C₃)
      (c₁ := min c₁ c₂) (c₂ := c₃) (by linarith) hC30 (lt_min hc₁ hc₂) hc₃ L
  have s3 : ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃)
        * LocalGoodAll.exf (min (min c₁ c₂) c₃) L + 1 * LocalGoodAll.exf c₅ L
      ≤ (((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃) + 1)
        * LocalGoodAll.exf (min (min (min c₁ c₂) c₃) c₅) L :=
    LocalGoodAll.exf_two (C₁ := (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃)
      (C₂ := 1) (c₁ := min (min c₁ c₂) c₃) (c₂ := c₅) (by linarith) hC10
      (lt_min (lt_min hc₁ hc₂) hc₃) hc₅ L
  have s4 : (((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃) + 1)
        * LocalGoodAll.exf (min (min (min c₁ c₂) c₃) c₅) L + 1 * LocalGoodAll.exf c₇ L
      ≤ ((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃) + 1) + 1)
        * LocalGoodAll.exf (min (min (min (min c₁ c₂) c₃) c₅) c₇) L :=
    LocalGoodAll.exf_two (C₁ := ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) + C₃) + 1)
      (C₂ := 1) (c₁ := min (min (min c₁ c₂) c₃) c₅) (c₂ := c₇) (by linarith) hC10
      (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₅) hc₇ L
  have hzero : (0 : ℝ) * LocalGoodAll.exf c₁ L ≤ (0 : ℝ) := by
    rw [zero_mul]
  linarith [s1, s2, s3, s4, hzero]


/-! ## 4. The genuine common `(locsum)` carrier for every group -/

/-- **The common `(locsum)` facts at `CUmax`, for every walker group at once.**  This is
`RecordGroupUniform.exists_loccoord_common` unpacked: one error coefficient `Cerr ≥ 1`, one rate
`c > 0`, one threshold `L₁`, such that

* the `(locsum)` bad set `locSumBadCommon` at `CUmax` has measure at most `Cerr * exf c L`, and
* off that *same* set, every nonempty group `B ⊆ Fin N` satisfies the `(loccoord)` display at the
  *single* coefficient `Cmax = (2 CUmax + 1)/2` with the *single* error `Cerr * L^{3/4}`.
-/
theorem commonLocsumFacts {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (T : ℕ) :
    ∃ Cerr c : ℝ, 1 ≤ Cerr ∧ 0 < c ∧ ∃ L₁ : ℕ,
      (∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (locSumBadCommon (N := N) p m r T L)
          ≤ Cerr * LocalGoodAll.exf c L) ∧
      (∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
          U ∉ locSumBadCommon (N := N) p m r T L →
          ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
          U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
          Swarming.Group.average B
              (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
            ≤ Cmax (N := N) p m
                * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
              + 3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr) := by
  obtain ⟨c, C, hc, hC1, L₁, hbody⟩ :=
    RecordGroupUniform.exists_loccoord_common (N := N) hp0 hp1 hm T
  refine ⟨C, c, hC1, hc, L₁, ?_, ?_⟩
  · intro L hL r hr
    have hb := (hbody L hL r hr).1
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  · intro L hL r hr U hU B hB s t hst hgeom
    have hres := (hbody L hL r hr).2 U hU B hB s t hst hgeom.1 hgeom.2.1 hgeom.2.2
    have hR : ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) = ((runMaxA p m U hB t : ℤ) : ℝ) := rfl
    rw [hR] at hres
    rw [three_mul_Cmax_betaOf (N := N)]
    exact hres

/-! ## 5. The `(locmove)` clause at one common coefficient -/

/-- **The `(locmove)` failure event at the common coefficient.**  Same actual-clock event as
`LocalGoodAll.moveBad`, but at the group-independent coefficient `Cmax = (2 CUmax + 1)/2` and the
common error `betaOf Cerr`, with the *common* `(locsum)` set as its `(loccoord)` input. -/
def moveBadCommon (p : ℝ) (m : ℕ) (Cerr : ℝ) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (r T L : ℕ) : Set (Array N) :=
  {U : Array N |
    ClockLocMove.locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
      (Cmax (N := N) p m) (betaOf (N := N) p m T L Cerr)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
      (ClockLocMove.locCoordGeom p m A hA r T L) U}

/-- **The measured `(locmove)` clause at the common coefficient, for one group.**  The only
group-dependent inputs are the geometric window `locCoordGeom` and the two `W^{A,Aᶜ}` endpoints;
the coefficient, the error and the `(locsum)` set are the common ones. -/
theorem moveBadCommon_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {T : ℕ} (hN : 1 ≤ N)
    {Cerr c : ℝ} (hCerr1 : 1 ≤ Cerr) (hc : 0 < c) {L₁ : ℕ}
    (hbad : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (locSumBadCommon (N := N) p m r T L)
        ≤ Cerr * LocalGoodAll.exf c L)
    (hcc : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∉ locSumBadCommon (N := N) p m r T L →
        ∀ s t : ℕ, s ≤ t → U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
        Swarming.Group.average A
            (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
          ≤ Cmax (N := N) p m
              * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
            + 3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr) :
    ∃ CT lam : ℝ, 0 < CT ∧ 0 < lam ∧ ∃ L₀ : ℕ, ∀ L ≥ max L₀ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (moveBadCommon (N := N) p m Cerr A hA hAc r T L)
        ≤ CT * LocalGoodAll.exf lam L := by
  -- absorption constants
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha₁ : (0 : ℝ) < 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2) := by positivity
  have ha₂ : (0 : ℝ) < 1 / (1024 * ((T : ℝ) + 3)) := by positivity
  have hcT : (0 : ℝ) < c / 2 := by linarith
  obtain ⟨C₁, hC₁0, Lc₁, hLc₁⟩ :=
    LocalGood.absorb_rpow (a := 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
      (c_T := c / 2) ha₁ hcT (j := 4) (k := 2) (by norm_num) (by norm_num)
  obtain ⟨C₂a, hC₂a0, Lc₂, hLc₂⟩ :=
    LocalGood.absorb_rpow (a := 1 / (1024 * ((T : ℝ) + 3)))
      (c_T := c / 2) ha₂ hcT (j := 6) (k := 2) (by norm_num) (by norm_num)
  refine ⟨2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂a + Cerr, c / 2,
    by positivity, hcT, max (max L₁ Lc₁) Lc₂, ?_⟩
  intro L hLbig r hr
  have hbig' : max (max (max L₁ Lc₁) Lc₂) 2 ≤ L := hLbig
  have hL' : L₁ ≤ L :=
    le_trans (le_trans (le_trans (le_max_left L₁ Lc₁) (le_max_left (max L₁ Lc₁) Lc₂))
      (le_max_left (max (max L₁ Lc₁) Lc₂) 2)) hbig'
  have hLc₁' : Lc₁ ≤ L :=
    le_trans (le_trans (le_trans (le_max_right L₁ Lc₁) (le_max_left (max L₁ Lc₁) Lc₂))
      (le_max_left (max (max L₁ Lc₁) Lc₂) 2)) hbig'
  have hLc₂' : Lc₂ ≤ L :=
    le_trans (le_trans (le_max_right (max L₁ Lc₁) Lc₂)
      (le_max_left (max (max L₁ Lc₁) Lc₂) 2)) hbig'
  have hL2 : 2 ≤ L := le_trans (le_max_right (max (max L₁ Lc₁) Lc₂) 2) hbig'
  have hL1 : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := Real.rpow_nonneg (by positivity) _
  have hε : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hBpos : 0 < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL1
  have hγC : 1 ≤ LocMoveCompose.gammaRate p m A * Cmax (N := N) p m :=
    RecordGroupUniform.gammaRate_mul_common (N := N) hp0 hp1 hA
  have hC0 : (0 : ℝ) ≤ Cerr := le_trans zero_le_one hCerr1
  -- the measured event bound at the common coefficient
  have hprev := ClockLocMove.measureReal_locMoveFailAtClock_le (N := N) hp0 hp1 (by omega : 1 ≤ m)
    A hA hAc (L := L) hL2 hr
    (B := RecClockLG.Bstar L) (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4))
    (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) (C := Cmax (N := N) p m)
    (β := betaOf (N := N) p m T L Cerr) hBpos (one_le_Cmax (N := N) p m) hγC hε hε
    (bad := locSumBadCommon (N := N) p m r T L) (eb := Cerr * LocalGoodAll.exf c L)
    (geom := ClockLocMove.locCoordGeom p m A hA r T L)
    (fun s t hst U hU hgeom => hcc L hL' r hr U hU s t hst hgeom)
    (hbad L hL' r hr)
  -- the polynomial prefactor at the record scale
  have hK2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by
    have h1 : ((((T + 3) * L : ℕ) : ℝ) + 1) ≤ ((T : ℝ) + 4) * (L : ℝ) := by
      push_cast
      nlinarith [hLr, Nat.cast_nonneg (α := ℝ) T]
    have h2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 := h2
      _ = ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hexp₁ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
          * (LocSumAct.xOf L) ^ 4)) := by
    apply Real.exp_le_exp.mpr
    have h := ClockLocMove.gamma_exp_at_Bstar (N := N) (T := T) (L := L) hp0 hp1.le hN hL1
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)) from by rw [neg_div]]
    linarith
  have hexp₂ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
    apply Real.exp_le_exp.mpr
    have h := ClockLocMove.maxgrowth_exp_at_Bstar (T := T) (L := L) hL1
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)) from by rw [neg_div]]
    linarith
  have hT1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := by
      refine mul_le_mul ?_ hexp₁ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4))) := by ring
  have hT2 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
      refine mul_le_mul ?_ hexp₂ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
              * (LocSumAct.xOf L) ^ 6))) := by ring
  have hT3 : Cerr * LocalGoodAll.exf c L ≤ Cerr * LocalGoodAll.exf (c / 2) L := by
    refine mul_le_mul_of_nonneg_left ?_ hC0
    unfold LocalGoodAll.exf
    apply Real.exp_le_exp.mpr
    nlinarith [hx0]
  have hsum : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      + Cerr * LocalGoodAll.exf c L
      ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ * LocalGoodAll.exf (c / 2) L
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂a * LocalGoodAll.exf (c / 2) L
        + Cerr * LocalGoodAll.exf (c / 2) L := by
    have h1'' : (L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
          * (LocSumAct.xOf L) ^ 4)) ≤ C₁ * LocalGoodAll.exf (c / 2) L := by
      simpa only [LocalGoodAll.exf, neg_mul] using hLc₁ L hLc₁'
    have h1' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * LocalGoodAll.exf (c / 2) L) :=
      mul_le_mul_of_nonneg_left h1'' (by positivity)
    have h2'' : (L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
          * (LocSumAct.xOf L) ^ 6)) ≤ C₂a * LocalGoodAll.exf (c / 2) L := by
      simpa only [LocalGoodAll.exf, neg_mul] using hLc₂ L hLc₂'
    have h2' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₂a * LocalGoodAll.exf (c / 2) L) :=
      mul_le_mul_of_nonneg_left h2'' (by positivity)
    have e1 : 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * LocalGoodAll.exf (c / 2) L)
        = 2 * ((T : ℝ) + 4) ^ 2 * C₁ * LocalGoodAll.exf (c / 2) L := by ring
    have e2 : 2 * ((T : ℝ) + 4) ^ 2 * (C₂a * LocalGoodAll.exf (c / 2) L)
        = 2 * ((T : ℝ) + 4) ^ 2 * C₂a * LocalGoodAll.exf (c / 2) L := by ring
    linarith [hT1, hT2, hT3, h1', h2', e1, e2]
  have hfinal : 2 * ((T : ℝ) + 4) ^ 2 * C₁ * LocalGoodAll.exf (c / 2) L
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂a * LocalGoodAll.exf (c / 2) L
        + Cerr * LocalGoodAll.exf (c / 2) L
      = (2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂a + Cerr)
        * LocalGoodAll.exf (c / 2) L := by ring
  rw [hfinal] at hsum
  exact le_trans hprev hsum

/-- The `(locmove)` bound for one group, with the common `(locsum)` carrier chosen by
`commonLocsumFacts`. -/
theorem exists_moveBadCommon_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) {T : ℕ}
    (hN : 1 ≤ N) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT lam : ℝ, 0 < CT ∧ 0 < lam ∧ ∃ L₀ : ℕ,
      ∀ L ≥ max L₀ 2, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (moveBadCommon (N := N) p m Cerr A hA hAc r T L)
          ≤ CT * LocalGoodAll.exf lam L := by
  obtain ⟨Cerr, c, hCerr1, hc, L₁, hbad, hcc⟩ := commonLocsumFacts (N := N) hp0 hp1 hm T
  obtain ⟨CT, lam, hCT, hlam, L₀, hle⟩ :=
    moveBadCommon_le (N := N) hp0 hp1 hm A hA hAc hN hCerr1 hc hbad
      (fun L hL r hr U hU s t hst hgeom => hcc L hL r hr U hU A hA s t hst hgeom)
  exact ⟨Cerr, hCerr1, CT, lam, hCT, hlam, L₀, hle⟩

/-! ## 6. The `(locgroup)` clause of one pair -/

/-- The `(locgroup)` bad event of a disjoint pair, at the actual record clock. -/
abbrev pairBad (p : ℝ) (m : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L

/-- **The measured `(locgroup)` clause for one pair**, in the `exf` profile. -/
theorem exists_pairBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {T : ℕ} (hT : 1 ≤ T) (hN : 1 ≤ N) :
    ∃ CT lam : ℝ, 0 < CT ∧ 0 < lam ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (pairBad (N := N) p m I J hI hJ r T L)
        ≤ CT * LocalGoodAll.exf lam L := by
  obtain ⟨c, hc, L₀, h⟩ :=
    RecClockLG.exists_recordClock_locgroup (N := N) hp0 hp1 hm I J hI hJ hid hT
  refine ⟨LocGroupSimul.locConst N T, c, LocGroupSimul.locConst_pos hN hT, hc, L₀, ?_⟩
  intro L hL r hr
  simpa only [LocalGoodAll.exf, LocSumAct.xOf, neg_mul] using h L hL r hr


/-! ## 7. The finite group family -/

/-- The `(locmove)` part of the family bad event: the finite union of the per-group movement
failures, all at the *same* common coefficient `Cmax` and the same common error `betaOf Cerr`. -/
noncomputable def famMovePart (p : ℝ) (m : ℕ) (Cerr : ℝ)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty) (r T L : ℕ) : Set (Array N) :=
  ⋃ A ∈ moveFam, (if h : A ∈ moveFam then
    moveBadCommon (N := N) p m Cerr A (hne A h) (hco A h) r T L else ∅)

/-- The `(locgroup)` part of the family bad event: the finite union over the pair family. -/
noncomputable def famPairPart (p : ℝ) (m : ℕ)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  ⋃ q ∈ grpFam, (if h : q ∈ grpFam then
    pairBad (N := N) p m q.1 q.2 (hI q h) (hJ q h) r T L else ∅)

/-- **The bad event of a finite family of walker groups.**  It is the group-independent part
`commonBad` (which contains the single `(locsum)` carrier at `CUmax`, `(lococc)`, `(locmax)`,
`(locmart)`, the potential support and the named occupation null event) together with the
`(locmove)` failure of every group of `moveFam` at the common coefficient and the `(locgroup)`
failure of every pair of `grpFam`. -/
def famBad (p : ℝ) (m : ℕ) (Cerr : ℝ)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  commonBad (N := N) p m r T L ∪ famMovePart (N := N) p m Cerr moveFam hne hco r T L
    ∪ famPairPart (N := N) p m grpFam hI hJ r T L

/-- **A finite union of per-element events with individual exponential bounds has a single
exponential bound.**  No set inclusion between the members is used, and the constants are the
`Finset` sum of the coefficients and the minimum of the rates. -/
theorem exists_iUnion_finset_le {ι : Type*} [DecidableEq ι] (T : ℕ) (s : Finset ι)
    (f : ℕ → ℕ → ι → Set (Array N)) :
    (∀ i ∈ s, ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
        ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
          (arrayMeasure N).real (f r L i) ≤ CT * LocalGoodAll.exf cT L) →
    ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (⋃ i ∈ s, f r L i) ≤ CT * LocalGoodAll.exf cT L := by
  intro h
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 1, one_pos, one_pos, 0, ?_⟩
      intro L hL r hr
      have h0 : (⋃ i ∈ (∅ : Finset ι), f r L i) = (∅ : Set (Array N)) := by simp
      rw [h0, measureReal_def, measure_empty, ENNReal.toReal_zero]
      exact mul_nonneg zero_le_one (Real.exp_pos _).le
  | insert a s ha ih =>
      have hsingle := h a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
          ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
            (arrayMeasure N).real (f r L i) ≤ CT * LocalGoodAll.exf cT L :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      obtain ⟨CT₁, cT₁, hCT₁, hcT₁, L₁, h₁⟩ := ih hrest
      obtain ⟨CT₂, cT₂, hCT₂, hcT₂, L₂, h₂⟩ := hsingle
      refine ⟨CT₁ + CT₂, min cT₁ cT₂, by linarith, lt_min hcT₁ hcT₂, max L₁ L₂, ?_⟩
      intro L hL r hr
      have hL1 : L₁ ≤ L := le_trans (le_max_left L₁ L₂) hL
      have hL2 : L₂ ≤ L := le_trans (le_max_right L₁ L₂) hL
      have hb1 := h₁ L hL1 r hr
      have hb2 := h₂ L hL2 r hr
      have hsub : (⋃ i ∈ insert a s, f r L i) ⊆ (⋃ i ∈ s, f r L i) ∪ f r L a := by
        intro U hU
        simp only [Set.mem_iUnion, Set.mem_union] at hU ⊢
        obtain ⟨i, hi, hUi⟩ := hU
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · exact Or.inr hUi
        · exact Or.inl ⟨i, hi', hUi⟩
      refine le_trans (measureReal_mono hsub) ?_
      calc (arrayMeasure N).real ((⋃ i ∈ s, f r L i) ∪ f r L a)
          ≤ (arrayMeasure N).real (⋃ i ∈ s, f r L i) + (arrayMeasure N).real (f r L a) :=
            measureReal_union_le _ _
        _ ≤ CT₁ * LocalGoodAll.exf cT₁ L + CT₂ * LocalGoodAll.exf cT₂ L := by linarith
        _ ≤ (CT₁ + CT₂) * LocalGoodAll.exf (min cT₁ cT₂) L :=
            LocalGoodAll.exf_two hCT₁.le hCT₂.le hcT₁ hcT₂ L

/-- **The measured bound for the whole finite family, with constants that do not depend on the
family except through its size.**  Every group of `moveFam` contributes its own `(locmove)` term
and every pair of `grpFam` its own `(locgroup)` term; the `(locsum)`/`(lococc)`/`(locmax)`/
`(locmart)`/potential terms are charged once. -/
theorem exists_famBad_le_at {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) {Cerr c : ℝ} (hCerr1 : 1 ≤ Cerr) (hc : 0 < c)
    {L₁ : ℕ}
    (hbadLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (locSumBadCommon (N := N) p m r T L)
        ≤ Cerr * LocalGoodAll.exf c L)
    (hccLS : ∀ L ≥ L₁, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∉ locSumBadCommon (N := N) p m r T L →
        ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
        U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
        Swarming.Group.average B
            (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
          ≤ Cmax (N := N) p m
              * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
            + 3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr) :
    ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real
            (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  -- the group-independent part
  obtain ⟨CTc, cTc, hCTc, hcTc, L₀c, hcommon⟩ := exists_commonBad_le (N := N) hp0 hp1 hm hT hN
  -- the per-group `(locmove)` bounds at the common coefficient
  have hmove : ∀ A ∈ moveFam, ∃ CT lam : ℝ, 0 < CT ∧ 0 < lam ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real ((if h : A ∈ moveFam then
          moveBadCommon (N := N) p m Cerr A (hne A h) (hco A h) r T L else ∅))
          ≤ CT * LocalGoodAll.exf lam L := by
    intro A hA
    obtain ⟨CT, lam, hCT, hlam, L₀, hle⟩ :=
      moveBadCommon_le (N := N) hp0 hp1 hm A (hne A hA) (hco A hA) (by omega : 1 ≤ N)
        hCerr1 hc hbadLS
        (fun L hL r hr U hU s t hst hgeom =>
          hccLS L hL r hr U hU A (hne A hA) s t hst hgeom)
    exact ⟨CT, lam, hCT, hlam, max L₀ 2, fun L hL r hr => by
      simpa only [dif_pos hA] using hle L hL r hr⟩
  obtain ⟨CTm, cTm, hCTm, hcTm, L₀m, hmoveb⟩ :=
    exists_iUnion_finset_le (N := N) T moveFam
      (fun r L A => if h : A ∈ moveFam then
        moveBadCommon (N := N) p m Cerr A (hne A h) (hco A h) r T L else ∅) hmove
  -- the per-pair `(locgroup)` bounds
  have hpair : ∀ q ∈ grpFam, ∃ CT lam : ℝ, 0 < CT ∧ 0 < lam ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real ((if h : q ∈ grpFam then
          pairBad (N := N) p m q.1 q.2 (hI q h) (hJ q h) r T L else ∅))
          ≤ CT * LocalGoodAll.exf lam L := by
    intro q hq
    obtain ⟨CT, lam, hCT, hlam, L₀, hle⟩ :=
      exists_pairBad_le (N := N) hp0 hp1 hm q.1 q.2 (hI q hq) (hJ q hq) (hdisj q hq) hT
        (by omega : 1 ≤ N)
    exact ⟨CT, lam, hCT, hlam, L₀, fun L hL r hr => by
      simpa only [dif_pos hq] using hle L hL r hr⟩
  obtain ⟨CTp, cTp, hCTp, hcTp, L₀p, hpairb⟩ :=
    exists_iUnion_finset_le (N := N) T grpFam
      (fun r L q => if h : q ∈ grpFam then
        pairBad (N := N) p m q.1 q.2 (hI q h) (hJ q h) r T L else ∅) hpair
  refine ⟨CTc + CTm + CTp, min (min cTc cTm) cTp, by positivity,
    lt_min (lt_min hcTc hcTm) hcTp, max (max L₀c L₀m) L₀p, ?_⟩
  intro L hL r hr
  have hLc : L₀c ≤ L :=
    le_trans (le_trans (le_max_left L₀c L₀m) (le_max_left (max L₀c L₀m) L₀p)) hL
  have hLm : L₀m ≤ L :=
    le_trans (le_trans (le_max_right L₀c L₀m) (le_max_left (max L₀c L₀m) L₀p)) hL
  have hLp : L₀p ≤ L := le_trans (le_max_right (max L₀c L₀m) L₀p) hL
  have hb1 := hcommon L hLc r hr
  have hb2 := hmoveb L hLm r hr
  have hb3 := hpairb L hLp r hr
  have hunion : (arrayMeasure N).real
      (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
      ≤ (arrayMeasure N).real (commonBad (N := N) p m r T L)
        + (arrayMeasure N).real (⋃ A ∈ moveFam, (if h : A ∈ moveFam then
            moveBadCommon (N := N) p m Cerr A (hne A h) (hco A h) r T L else ∅))
        + (arrayMeasure N).real (⋃ q ∈ grpFam, (if h : q ∈ grpFam then
            pairBad (N := N) p m q.1 q.2 (hI q h) (hJ q h) r T L else ∅)) := by
    have h1 := measureReal_union_le (μ := arrayMeasure N)
      (commonBad (N := N) p m r T L)
      (famMovePart (N := N) p m Cerr moveFam hne hco r T L)
    have h2 := measureReal_union_le (μ := arrayMeasure N)
      (commonBad (N := N) p m r T L ∪ famMovePart (N := N) p m Cerr moveFam hne hco r T L)
      (famPairPart (N := N) p m grpFam hI hJ r T L)
    unfold famMovePart at h1
    unfold famMovePart famPairPart at h2
    unfold famBad famMovePart famPairPart
    linarith [h1, h2]
  have hkey : (arrayMeasure N).real
      (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
      ≤ CTc * LocalGoodAll.exf cTc L + CTm * LocalGoodAll.exf cTm L
        + CTp * LocalGoodAll.exf cTp L := by
    linarith [hunion, hb1, hb2, hb3]
  refine le_trans hkey ?_
  have s1 : CTc * LocalGoodAll.exf cTc L + CTm * LocalGoodAll.exf cTm L
      ≤ (CTc + CTm) * LocalGoodAll.exf (min cTc cTm) L :=
    LocalGoodAll.exf_two hCTc.le hCTm.le hcTc hcTm L
  have s2 : (CTc + CTm) * LocalGoodAll.exf (min cTc cTm) L + CTp * LocalGoodAll.exf cTp L
      ≤ ((CTc + CTm) + CTp) * LocalGoodAll.exf (min (min cTc cTm) cTp) L :=
    LocalGoodAll.exf_two (by linarith) hCTp.le (lt_min hcTc hcTm) hcTp L
  linarith [s1, s2]


/-- **The measured bound for the whole finite family** (with the common `(locsum)` carrier chosen
internally). -/
theorem exists_famBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ Cerr CT cT : ℝ, 1 ≤ Cerr ∧ 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real
            (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  obtain ⟨Cerr, c, hCerr1, hc, L₁, hbadLS, hccLS⟩ := commonLocsumFacts (N := N) hp0 hp1 hm T
  obtain ⟨CT, cT, hCT, hcT, L₀, hle⟩ :=
    exists_famBad_le_at (N := N) hp0 hp1 hm hT hN moveFam hne hco grpFam hI hJ hdisj
      hCerr1 hc hbadLS hccLS
  exact ⟨Cerr, CT, cT, hCerr1, hCT, hcT, L₀, hle⟩

/-! ## 8. Extraction of the components from the family bad event -/

/-- The six group-independent components of `commonBad`, as negative facts. -/
theorem not_mem_commonBad {p : ℝ} {m : ℕ} {r T L : ℕ} {U : Array N}
    (h : U ∉ commonBad (N := N) p m r T L) :
    U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L
      ∧ U ∉ LocalGoodAll.occBad (N := N) p m r T L
      ∧ U ∉ locSumBadCommon (N := N) p m r T L
      ∧ U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L
      ∧ U ∉ RecordClock.locMartBad (N := N) p m r T L
      ∧ U ∉ LocalGoodAll.potBad (N := N) p m
      ∧ U ∉ OccDisplayNull.occNull (N := N) p m (LocOccSiteRate.Ccan p m) r T L := by
  unfold commonBad zeroBad at h
  simp only [Set.mem_union, not_or] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

/-- The three parts of `famBad`, as negative facts. -/
theorem not_mem_famBad {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    (U ∉ commonBad (N := N) p m r T L
      ∧ U ∉ famMovePart (N := N) p m Cerr moveFam hne hco r T L)
      ∧ U ∉ famPairPart (N := N) p m grpFam hI hJ r T L := by
  unfold famBad at h
  simp only [Set.mem_union, not_or] at h
  exact h

/-- A member of `moveFam` is off the family bad event. -/
theorem not_mem_moveBadCommon {p : ℝ} {m : ℕ} {Cerr : ℝ}
    {moveFam : Finset (Finset (Fin N))} {hne : ∀ A ∈ moveFam, A.Nonempty}
    {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty} {r T L : ℕ} {U : Array N}
    (h : U ∉ famMovePart (N := N) p m Cerr moveFam hne hco r T L)
    (A : Finset (Fin N)) (hA : A ∈ moveFam) :
    U ∉ moveBadCommon (N := N) p m Cerr A (hne A hA) (hco A hA) r T L := by
  intro hc
  refine h ?_
  unfold famMovePart
  simp only [Set.mem_iUnion]
  exact ⟨A, hA, by rw [dif_pos hA]; exact hc⟩

/-- A member of `grpFam` is off the family bad event. -/
theorem not_mem_pairBad {p : ℝ} {m : ℕ}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ famPairPart (N := N) p m grpFam hI hJ r T L)
    (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam) :
    U ∉ pairBad (N := N) p m q.1 q.2 (hI q hq) (hJ q hq) r T L := by
  intro hc
  refine h ?_
  unfold famPairPart
  simp only [Set.mem_iUnion]
  exact ⟨q, hq, by rw [dif_pos hq]; exact hc⟩

/-- The potential support clause (the a.e. forward-potential bound is part of the bad event). -/
theorem familyGood_pot {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)) :=
  Classical.not_not.mp (not_mem_commonBad (not_mem_famBad h).1.1).2.2.2.2.2.1

/-- The `(locmart)` clause at the actual record clock. -/
theorem familyGood_locmart {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    U ∈ RecordClock.locMartGood (N := N) p m r T L := by
  have h7 := (not_mem_commonBad (not_mem_famBad h).1.1).2.2.2.2.1
  simpa [RecordClock.locMartGood] using h7

/-- **The `(locmove)` clause for every group of the family, at the common coefficient.**  Off the
family bad event, on the carrier, each `A ∈ moveFam` satisfies the paper's `(locmove)` display
with the coefficient `Cmax` and the error `betaOf Cerr`, on every window of `[τ_r, τ_r+(T+3)L]` on
which the paper's window hypotheses hold. -/
theorem familyGood_locmove {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (A : Finset (Fin N)) (hA : A ∈ moveFam), ∀ s t : ℕ,
      recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
      locmoveGood p m A (hne A hA) (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
      U ∈ ClockLocMove.locCoordGeom p m A (hne A hA) r T L s t →
      WA p m U t A Aᶜ (hne A hA) (hco A hA) - WA p m U s A Aᶜ (hne A hA) (hco A hA)
        ≤ locmoveRHS (N := N) p m A (hne A hA) L (Cmax (N := N) p m)
            (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U := by
  intro A hA s t hs hst htK hgood hgeom
  have hneg := not_mem_moveBadCommon (not_mem_famBad h).1.2 A hA
  by_contra hcon
  exact hneg ⟨hcarr, s, t, hs, hst, htK, hgood, hgeom, hcon⟩

/-- **The `(loccoord)` clause at the common coefficient, for every nonempty group at once.** -/
theorem familyGood_loccoord {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {L₀ : ℕ} {Cerr : ℝ}
    (hC : ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∉ locSumBadCommon (N := N) p m r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr)
    {L : ℕ} (hL : L₀ ≤ L) {r : ℕ} (hr : (T + 3) * L ≤ r) {U : Array N}
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
      U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
      Swarming.Group.average B
          (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
        ≤ Cmax (N := N) p m
            * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hU := (not_mem_commonBad (not_mem_famBad h).1.1).2.2.1
  intro B hB s t hst hgeom
  have hres := hC L hL r hr U hU B hB s t hst hgeom
  have hbeta : 3 * Cmax (N := N) p m * betaOf (N := N) p m T L Cerr
      = Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := three_mul_Cmax_betaOf (N := N) p m T L Cerr
  linarith [hres, hbeta]

/-- **The `(lococc)` display at the actual record fibre, off the family bad event.**  This is the
pointwise occupation display of Proposition `local` at `τ_r` on the carrier, obtained from the
named null event `OccDisplayNull.occNull` inside the bad event (not from an unnamed a.e. set). -/
theorem familyGood_lococc {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    OccDisplayNull.occFace (N := N) p m (LocOccSiteRate.Ccan p m) r T L (recTimeA p m U r) U :=
  OccDisplayNull.occFace_of_not_mem (N := N)
    (not_mem_commonBad (not_mem_famBad h).1.1).2.2.2.2.2.2

/-- The `(lococc)` clock-fibre event: every band member is in the all-pairs good event. -/
theorem familyGood_goodWin {p : ℝ} {m : ℕ} {Cerr : ℝ} {moveFam : Finset (Finset (Fin N))}
    {hne : ∀ A ∈ moveFam, A.Nonempty} {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
    {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
    {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty}
    {r T L : ℕ} {U : Array N}
    (h : U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L) :
    ∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
      U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
        (LocOccSiteRate.Ccan p m) r T L s0 := by
  have h2 := (not_mem_commonBad (not_mem_famBad h).1.1).2.1
  intro s0 hs0
  have hnotin : U ∉ LocOccFibreSum.band p m r L s0 ∩
      (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
        (LocOccSiteRate.Ccan p m) r T L s0)ᶜ := by
    intro hc
    exact h2 (Set.mem_iUnion.mpr ⟨s0, hc⟩)
  by_contra hcon
  exact hnotin ⟨hs0, hcon⟩

/-- **The `(locgroup)` clause for every pair of the family, with one uniform threshold.**  The
per-pair content is `RecClockLG.locgroup_at_recordClock`; the uniform threshold over the finite
pair family is the `Finset.sup` of the per-pair thresholds. -/
theorem familyGood_locgroup {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ L₈ : ℕ, ∀ L ≥ L₈, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L →
      (∀ j : Fin N, ∀ u : ℕ,
        BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) →
      (U ∉ famPairPart (N := N) p m grpFam hI hJ r T L) →
      ∀ (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam), ∀ s t : ℕ,
        recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        (∀ u ∈ Finset.Ico s t, SepSet p m u q.1 q.2 U) →
        WA p m U t q.1 q.2 (hI q hq) (hJ q hq) - WA p m U s q.1 q.2 (hI q hq) (hJ q hq)
          ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  -- the per-pair thresholds
  have hex : ∀ (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam), ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L →
        (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) →
        U ∉ pairBad (N := N) p m q.1 q.2 (hI q hq) (hJ q hq) r T L →
        ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
          (∀ u ∈ Finset.Ico s t, SepSet p m u q.1 q.2 U) →
          WA p m U t q.1 q.2 (hI q hq) (hJ q hq) - WA p m U s q.1 q.2 (hI q hq) (hJ q hq)
            ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro q hq
    obtain ⟨c, hc, L₀, hL₀⟩ :=
      RecClockLG.locgroup_at_recordClock (N := N) hp0 hp1 hm q.1 q.2 (hI q hq) (hJ q hq)
        (hdisj q hq) hT
    exact ⟨L₀, fun L hL r hr U hcarr hLM hpot hbad s t hs hst htK hsep =>
      hL₀ L hL r hr U hcarr hLM hpot hbad s t hs hst htK hsep⟩
  let Lf : Finset (Fin N) × Finset (Fin N) → ℕ := fun q =>
    if h : q ∈ grpFam then Classical.choose (hex q h) else 0
  have hLf : ∀ (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam),
      ∀ L ≥ Lf q, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L →
        (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) →
        U ∉ pairBad (N := N) p m q.1 q.2 (hI q hq) (hJ q hq) r T L →
        ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
          (∀ u ∈ Finset.Ico s t, SepSet p m u q.1 q.2 U) →
          WA p m U t q.1 q.2 (hI q hq) (hJ q hq) - WA p m U s q.1 q.2 (hI q hq) (hJ q hq)
            ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
    intro q hq L hL r hr
    have hspec := Classical.choose_spec (hex q hq)
    have hLfq : Lf q = Classical.choose (hex q hq) := by
      simp only [Lf, dif_pos hq]
    rw [hLfq] at hL
    exact hspec L hL r hr
  refine ⟨grpFam.sup Lf, ?_⟩
  intro L hL r hr U hcarr hLM hpot hpairpart q hq s t hs hst htK hsep
  have hqL : Lf q ≤ L := le_trans (Finset.le_sup (f := Lf) hq) hL
  exact hLf q hq L hqL r hr U hcarr hLM hpot
    (not_mem_pairBad hpairpart q hq) s t hs hst htK hsep


/-! ## 9. The headline: one bad event, one bound, all groups' clauses -/

/-- **The finite-family local-good event of Proposition `local`.**

For `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, every fixed `T ≥ 1` and every finite family of nonempty
proper walker sets `moveFam` and disjoint nonempty pairs `grpFam`, there are

* one error coefficient `Cerr ≥ 1` (the `(loccoord)`/`(locmove)` error coefficient of the common
  `(locsum)` carrier at `CUmax`),
* one exponential bound `CT * exf cT L` for the *single* bad event `famBad`,

such that beyond a threshold, for every `L`, every `r ≥ (T+3)L`, and every trajectory `U` on the
paper's carrier `recordCarrier` (which contains `ReachAll`) that is off `famBad`:

* the forward-potential support holds;
* `(locmart)` holds at the actual record clock;
* `(locmove)` holds for **every** `A ∈ moveFam`, at the group-independent coefficient `Cmax`;
* `(loccoord)` holds for **every** nonempty group at the same coefficient and error;
* `(lococc)` holds as the literal pointwise display at the actual record fibre `τ_r` (and at every
  record fibre), i.e. with the named null event `OccDisplayNull.occNull` inside the bad event;
* the `GoodWinAllPairs` fibre event holds;
* `(locgroup)` holds for every pair of `grpFam`;
* the `(locsum)` pointwise content holds at the `(lococc)` scale.

The carriers `(sep)` (`SepSet`), `locmoveGood`, `locCoordGeom` and the `(locsum)` range content
remain hypotheses of the respective displays; nothing is claimed about their probability. -/
theorem exists_famBad_and_good {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧
      (∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
        ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
          (arrayMeasure N).real
              (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
            ≤ CT * LocalGoodAll.exf cT L) ∧
      (∃ Lg : ℕ, ∀ L ≥ Lg, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
        (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
          U ∈ RecordClock.locMartGood (N := N) p m r T L ∧
          (∀ (A : Finset (Fin N)) (hA : A ∈ moveFam), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
            locmoveGood p m A (hne A hA) (r : ℤ) T L (RecClockLG.Bstar L)
              (recTimeA p m U r) s t U →
            U ∈ ClockLocMove.locCoordGeom p m A (hne A hA) r T L s t →
            WA p m U t A Aᶜ (hne A hA) (hco A hA) - WA p m U s A Aᶜ (hne A hA) (hco A hA)
              ≤ locmoveRHS (N := N) p m A (hne A hA) L (Cmax (N := N) p m)
                  (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
                  ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U) ∧
          (∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
            U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
            Swarming.Group.average B
                (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
              ≤ Cmax (N := N) p m
                  * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
                + Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          OccDisplayNull.occFace (N := N) p m (LocOccSiteRate.Ccan p m) r T L
            (recTimeA p m U r) U ∧
          (∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
            U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0) ∧
          (∀ (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            (∀ u ∈ Finset.Ico s t, SepSet p m u q.1 q.2 U) →
            WA p m U t q.1 q.2 (hI q hq) (hJ q hq) - WA p m U s q.1 q.2 (hI q hq) (hJ q hq)
              ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          (∀ j : Fin N, ∀ a0 b0 : ℕ,
            LocOccCarrierAssembly.A0 r T L ≤ a0 →
            b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
            ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
              ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
                + 6 * LocOccSiteRate.Ccan p m
                  * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ))) := by
  obtain ⟨Cerr, c, hCerr1, hc, L₁, hbadLS, hccLS⟩ := commonLocsumFacts (N := N) hp0 hp1 hm T
  -- the bound at this `Cerr`
  obtain ⟨CT, cT, hCT, hcT, Lb, hbound⟩ :=
    exists_famBad_le_at (N := N) hp0 hp1 hm hT hN moveFam hne hco grpFam hI hJ hdisj
      hCerr1 hc hbadLS hccLS
  -- the `(locgroup)` threshold
  obtain ⟨L₈, hL₈⟩ := familyGood_locgroup (N := N) hp0 hp1 hm hT grpFam hI hJ hdisj
  -- the `(locsum)` content at the `(lococc)` scale
  obtain ⟨c₉, hc₉, L₉, h₉⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨Cerr, hCerr1, ⟨CT, cT, hCT, hcT, Lb, hbound⟩,
    max (max (max (max Lb L₈) L₉) L₁) L₁₀, ?_⟩
  intro L hL r hr U hcarr hnot
  have hbig : max (max (max (max Lb L₈) L₉) L₁) L₁₀ ≤ L := hL
  have hLb : Lb ≤ L := by omega
  have hL8 : L₈ ≤ L := by omega
  have hL9 : L₉ ≤ L := by omega
  have hL1 : L₁ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  obtain ⟨⟨hcom, hmove⟩, hpair⟩ := not_mem_famBad hnot
  obtain ⟨hsumOcc, hocc, hlsC, hlocMax, hlocMart, hpot, hoccNull⟩ := not_mem_commonBad hcom
  -- the `(locsum)` side condition
  have hside : 2 * ellT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
      ≤ LocOccCarrierAssembly.A0 r T L := by
    have hArith : L + (T + 2) * L ≤ r := by
      have hEq : L + (T + 2) * L = (T + 3) * L := by ring
      rw [hEq]; exact hr
    have hLA0 : L ≤ LocOccCarrierAssembly.A0 r T L := by
      unfold LocOccCarrierAssembly.A0
      exact Nat.le_sub_of_add_le hArith
    exact le_trans (hL₁₀ L hL10) hLA0
  refine ⟨familyGood_pot hnot, familyGood_locmart hnot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(locmove)` for every group of the family
    exact familyGood_locmove (N := N) (Cerr := Cerr) (moveFam := moveFam) (grpFam := grpFam) hcarr hnot
  · -- `(loccoord)` at the common coefficient for every group
    exact familyGood_loccoord (N := N) hp0 hp1 hm (L₀ := L₁) (Cerr := Cerr) hccLS hL1 hr hnot
  · -- `(lococc)`: the literal display at the actual record fibre
    exact familyGood_lococc (N := N) (Cerr := Cerr) hcarr hnot
  · -- the `GoodWinAllPairs` fibre event
    exact familyGood_goodWin (N := N) (Cerr := Cerr) hnot
  · -- `(locgroup)` for every pair
    exact hL₈ L hL8 r hr U hcarr hlocMax
      (familyGood_pot hnot) hpair
  · -- the `(locsum)` content at the `(lococc)` scale
    intro j a0 b0 ha0 hb0 hab
    exact (h₉ (LocOccCarrierAssembly.Lw T L)
      (le_trans hL9 (LocOccCarrierAssembly.le_Lw T L)) (LocOccCarrierAssembly.A0 r T L) hside).2
      U hsumOcc j a0 b0 ha0 hb0 hab

end LocalGoodFamily
