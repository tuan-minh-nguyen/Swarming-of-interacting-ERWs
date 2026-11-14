/-
# One measured local-good bad event at the literal actual record clock

## What this file is

This is the **single measured event** version of the good event of Proposition `local` of the paper,
at the paper's own record threshold `(T+3)L ≤ r`, on the literal actual objects
`SwarmRecordMeas.Actual.recTimeA` (the record clock `τ_r`), `SepGroup.Model.X` / `ActX` (the
nearest-neighbour trajectories of the deterministic model) and `Swarm.Uniform.arrayMeasure N`.

`LocalBad` is the actual set-theoretic union of the *actual measured clauses* already proved in the
public tree (one component here is new, `ClockLocMove.exists_measureReal_locMoveFailAtClock_T3_paper`
in `LocMoveT3.lean`); it is not a symbolic conjunction and it is not a union of deterministic-clock
statements:

| component | set | proved in |
|---|---|---|
| `(locsum)` at the `(lococc)` scale | `LsBad Ccan (Lw T L) (A0 r T L)` | `R4Assemble` / `SingleWindowSiteRate` |
| `(lococc)` all-pair clock-fibre union | `⋃ s0, band s0 ∩ GoodWinAllPairsᶜ` | `LocOccAllPairFibreSum` |
| `(locsum)` at the `(loccoord)` scale | `LsBad (CU p m A) ((2T+4)L) (r-(T+2)L)` | `LocalGoodCore` |
| `(locmove)` at `τ_r`, `(T+3)L ≤ r` | `locMoveFailAtClock … (Bstar L) ((2CU+1)/2) (betaCU …) L^{3/4} L^{3/4} locCoordGeom` | `LocMoveT3` (new) |
| `(locmax)` | `LocGroupSimul.LocMaxBad r T L` | `LocGroupSimultaneous` |
| `(locgroup)` at `τ_r` | `RecClockLG.locGroupBad I J r T L` | `RecClockLocgroup` |
| `(locmart)` at `τ_r` | `RecordClock.locMartBad r T L` | `RecordClockLocal` |
| potential support | `potBad` (a.e. null) | `ae_bddAbove_Gtrunc_arrayMeasure` |

`exists_LocalBad_le` bounds the whole union by **one** `CT * exp (-(cT * xOf L))` with
`CT, cT, L₀` independent of `r` (they may depend on `T`, `N`, `m`, `p` and on the group/walker
parameter `A`, `I`, `J`, as Proposition `local` allows).  `localGood_of_not_mem` records, off this
one event and on the carrier `{d_r ≤ L}`, the simultaneous component conclusions with their exact
carriers: `(locmart)`, `(locgroup)` at `τ_r`, `(locmove)` at `τ_r`, `(loccoord)`, the a.e.
potential support, and the `(lococc)` event at the carrier fibre.

## What is deliberately NOT claimed

* `(sep)` on `[s,t)` (`SepSet`), the `(locmove)` carrier `locmoveGood` (which contains `GoodW`,
  `GoodStep`, the pinned record window and the two step truncations), the geometric window
  `locCoordGeom` and the `(locsum)` content are **hypotheses** of the corresponding displays, never
  conclusions.  `GoodW`/`GoodStep`/`pin`/geometry/separation are not certified to hold.
* `(lococc)` is delivered as membership in `LocOccSingleWindowAllPairs.GoodWinAllPairs` at the
  carrier fibre, i.e. as the *event* `GoodWinAllPairs` (off the three raw sets `LsBad`,
  `qplDrop`, `OscSup`), plus the pointwise `(locsum)` content that the display consumes
  (clause 7 of `localGood_of_not_mem`).  Turning that membership into the paper's occupation
  display `(0.10)`-style inequality pointwise is **not** done here: the public route
  `LocOccSingleWindowAllPairs.lococc_recordCarrier_allPairs_singleWindow` is stated `∀ᵐ U` and its
  null set is not a named set of that module, so it cannot be folded into `LocalBad` without
  extracting it.
* The parameter family is **fixed**: one nonempty proper `A` and one disjoint nonempty pair `I, J`.
  The paper's `𝒢` quantifies over all of them; passing from this fixed-parameter clause to the
  finite family is a finite union bound (`Finset`-indexed), which is not carried out here.  The
  constant `CU p m A` genuinely depends on `A`, so that step is *not* an inclusion: the `A`-indexed
  `LsBad` sets are distinct.
* No separation survival, no event positivity/non-vacuity, no invariant measure, no
  stationarity/regeneration, no coalescence or collision-density input, no halving/lag, no
  tightness, no `MainClaim`, no velocity statement.
-/
import Swarm.LocMoveT3
import Swarm.RecordClockLocal
import Swarm.LocOccAllPairFibreSum
import Swarm.LocGroupSimultaneous

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

namespace LocalGoodAll

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The eight actual measured clauses -/

/-- `(locsum)` at the `(lococc)` scale: the single-window `(locsum)`/`(locmax)` defect of the
all-pair occupation estimate. -/
abbrev sumBadOcc (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  LocSumR1.LsBad N p m (LocOccSiteRate.Ccan p m) (LocOccCarrierAssembly.Lw T L) (LocOccCarrierAssembly.A0 r T L)

/-- `(lococc)`: the exact all-pair clock-fibre union
`⋃ s0, band s0 ∩ (GoodWinAllPairs s0)ᶜ`; the bands `band s0 = recordPrefixBand p m r s0 L` are
pairwise disjoint, which is what makes the summation count-free. -/
abbrev occBad (p : ℝ) (m : ℕ) (r T L : ℕ) : Set (Array N) :=
  ⋃ s0, LocOccFibreSum.band p m r L s0 ∩
    (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
      (LocOccSiteRate.Ccan p m) r T L s0)ᶜ

/-- `(locsum)` at the `(loccoord)`/`(locmove)` scale, at the single explicitly named constant
`CU p m A` — the *same* set that carries `(loccoord)` and the `(locmove)` conditional. -/
abbrev sumBadCoord (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (r T L : ℕ) : Set (Array N) :=
  LocSumR1.LsBad N p m (LocalGood.CU p m A) ((2 * T + 4) * L) (r - (T + 2) * L)

/-- `(locmove)` at the literal `τ_r`, at the paper's record threshold `(T+3)L ≤ r`, at the
explicit constant `CU`, with `B = Bstar L` and `ε₁ = ε₂ = L^{3/4}`. -/
abbrev moveBad (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (r T L : ℕ) : Set (Array N) :=
  {U : Array N |
    ClockLocMove.locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
      ((2 * LocalGood.CU p m A + 1) / 2)
      (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
        (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
      (ClockLocMove.locCoordGeom p m A hA r T L) U}

/-- The a.e. potential support: the complement of "every forward potential truncation is bounded
above at every site".  This set is `arrayMeasure`-null. -/
def potBad (p : ℝ) (m : ℕ) : Set (Array N) :=
  {U : Array N | ¬ (∀ j : Fin N, ∀ u : ℕ,
    BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)))}

/-- **The single measured local-good bad event of Proposition `local`** at the literal record clock
`τ_r = recTimeA p m U r`, at the paper's record threshold, for the fixed walker parameter `A` and
the fixed disjoint group pair `(I, J)`.

It is the actual union of the eight measured clauses of the table in the module header; off it, and
on the paper's carrier `{d_r ≤ L}`, the component displays hold simultaneously
(`localGood_of_not_mem`). -/
def LocalBad (p : ℝ) (m : ℕ) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (r T L : ℕ) : Set (Array N) :=
  sumBadOcc p m r T L ∪ occBad p m r T L ∪ sumBadCoord p m A r T L ∪ moveBad p m A hA hAc r T L ∪
    LocGroupSimul.LocMaxBad (N := N) p m r T L ∪
      RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L ∪
        RecordClock.locMartBad (N := N) p m r T L ∪ potBad p m

/-! ## 2. Absorption arithmetic: two terms into one -/

/-- `xOf L ≥ 0`. -/
theorem xOf_nonneg (L : ℕ) : 0 ≤ LocSumAct.xOf L :=
  Real.rpow_nonneg (Nat.cast_nonneg L) _

/-- **Two exponential terms with nonnegative constants and positive rates are dominated by one.**
This is the only arithmetic input of the union bound: no new probabilistic content. -/
theorem exp_two {C₁ C₂ c₁ c₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) {L : ℕ} :
    C₁ * Real.exp (-(c₁ * LocSumAct.xOf L)) + C₂ * Real.exp (-(c₂ * LocSumAct.xOf L))
      ≤ (C₁ + C₂) * Real.exp (-((min c₁ c₂) * LocSumAct.xOf L)) := by
  have hx : 0 ≤ LocSumAct.xOf L := xOf_nonneg L
  have h1 : Real.exp (-(c₁ * LocSumAct.xOf L))
      ≤ Real.exp (-((min c₁ c₂) * LocSumAct.xOf L)) := by
    apply Real.exp_le_exp.mpr
    have := min_le_left c₁ c₂
    nlinarith
  have h2 : Real.exp (-(c₂ * LocSumAct.xOf L))
      ≤ Real.exp (-((min c₁ c₂) * LocSumAct.xOf L)) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right c₁ c₂
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 hC₁
  have h4 := mul_le_mul_of_nonneg_left h2 hC₂
  have h5 : C₁ * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L)
      + C₂ * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L)
      = (C₁ + C₂) * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L) := by ring
  linarith [h3, h4, h5]

end LocalGoodAll

namespace LocalGoodAll

variable {N : ℕ} [Nonempty (Fin N)]

/-- Shorthand for the paper's profile term `exp (-c * xOf L)`.  Keeping the profile as a named
application is what lets the seven component bounds be folded into one by pure linear arithmetic
over the monomials `const * exf c L`. -/
noncomputable def exf (c : ℝ) (L : ℕ) : ℝ := Real.exp (-c * LocSumAct.xOf L)

/-- **Two profile terms merge.**  The kernel of the fold below: no probabilistic content. -/
theorem exf_two {C₁ C₂ c₁ c₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (L : ℕ) :
    C₁ * exf c₁ L + C₂ * exf c₂ L ≤ (C₁ + C₂) * exf (min c₁ c₂) L := by
  unfold exf
  have hx : 0 ≤ LocSumAct.xOf L := xOf_nonneg L
  have h1 : Real.exp (-c₁ * LocSumAct.xOf L) ≤ Real.exp (-(min c₁ c₂) * LocSumAct.xOf L) := by
    apply Real.exp_le_exp.mpr
    have := min_le_left c₁ c₂
    nlinarith
  have h2 : Real.exp (-c₂ * LocSumAct.xOf L) ≤ Real.exp (-(min c₁ c₂) * LocSumAct.xOf L) := by
    apply Real.exp_le_exp.mpr
    have := min_le_right c₁ c₂
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 hC₁
  have h4 := mul_le_mul_of_nonneg_left h2 hC₂
  have h5 : C₁ * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L)
      + C₂ * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L)
      = (C₁ + C₂) * Real.exp (-(min c₁ c₂) * LocSumAct.xOf L) := by ring
  linarith [h3, h4, h5]

/-- The eight-fold subadditivity of `Measure.real` used by the union bound. -/
theorem measureReal_union8_le (a b c d e f g h : Set (Array N)) :
    (arrayMeasure N).real (a ∪ b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h)
      ≤ (arrayMeasure N).real a + (arrayMeasure N).real b + (arrayMeasure N).real c
        + (arrayMeasure N).real d + (arrayMeasure N).real e + (arrayMeasure N).real f
        + (arrayMeasure N).real g + (arrayMeasure N).real h := by
  have h1 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b ∪ c ∪ d ∪ e ∪ f ∪ g) h
  have h2 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b ∪ c ∪ d ∪ e ∪ f) g
  have h3 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b ∪ c ∪ d ∪ e) f
  have h4 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b ∪ c ∪ d) e
  have h5 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b ∪ c) d
  have h6 := measureReal_union_le (μ := arrayMeasure N) (a ∪ b) c
  have h7 := measureReal_union_le (μ := arrayMeasure N) a b
  linarith

/-! ## 3. The single measured bound for the whole event -/

/-- **The one measured bound for the unified local-good event.**

For `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, nonempty proper `A`, disjoint nonempty `I J`, and every fixed
`T ≥ 1` there are `CT > 0`, `cT > 0` and `L₀` such that for every `L ≥ L₀` and **every** record
level `r ≥ (T+3)L`:

`(arrayMeasure N).real (LocalBad … r T L) ≤ CT * exf cT L`.

All eight inputs are measured clauses at the literal record clock `recTimeA p m U r` on
`arrayMeasure N`; there is no union over clock values, no truncation of the clock, no stationarity,
invariant-measure, regeneration, coalescence or collision-density input.  The constants `CT, cT, L₀`
may depend on `T, N, m, p` and on `A, I, J`, which is exactly what Proposition `local` allows. -/
theorem exists_LocalBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N) :
    ∃ CT : ℝ, 0 < CT ∧ ∃ cT : ℝ, 0 < cT ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (LocalBad (N := N) p m A hA hAc I J hI hJ r T L)
        ≤ CT * exf cT L := by
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
  -- (3) `(locsum)` at the `(loccoord)` scale
  obtain ⟨c₃, hc₃, L₃, h₃⟩ := LocalGood.loccoord_CU_explicit (N := N) hp0 hp1 hm A hA T
  -- (4) `(locmove)` at `tau_r` and at `(T+3)L <= r`
  obtain ⟨c₄, C₄, hc₄, hC₄, L₄, h₄⟩ :=
    ClockLocMove.exists_measureReal_locMoveFailAtClock_T3_paper (N := N) hp0 hp1 hm A hA hAc
      (by omega : 1 ≤ N) T
  -- (5) `(locmax)`
  obtain ⟨c₅, hc₅, L₅, h₅⟩ := LocGroupSimul.exists_locMaxBad_le (N := N) hp0 hp1 hm T hT
  -- (6) `(locgroup)` at `tau_r`
  obtain ⟨c₆, hc₆, L₆, h₆⟩ := RecClockLG.exists_recordClock_locgroup (N := N) hp0 hp1 hm I J hI hJ hid hT
  -- (7) `(locmart)` at `tau_r`
  obtain ⟨c₇, hc₇, L₇, h₇⟩ := RecordClock.exists_locMartBad_le (N := N) hp0 hp1 hm hN T hT
  -- (8) the a.e. potential support is null
  have hpot : (arrayMeasure N).real (potBad (N := N) p m) = 0 := by
    have h0 : (arrayMeasure N) (potBad (N := N) p m) = 0 :=
      ae_iff.mp (ae_bddAbove_Gtrunc_arrayMeasure (N := N) hp0 hp1 hm)
    rw [measureReal_def, h0, ENNReal.toReal_zero]
  refine ⟨(((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
      + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1
      + LocGroupSimul.locConst N T + 1, by
        have h0 : (0 : ℝ) ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ :=
          mul_nonneg (by positivity) hC₂
        have h1 : (0 : ℝ) ≤ 1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ := by linarith
        have h2 : (1 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T :=
          LocCoordPaper.one_le_CTof (le_trans zero_le_one (LocalGood.one_le_CU p m A)) T
        have h3 : (0 : ℝ) ≤ LocGroupSimul.locConst N T :=
          (LocGroupSimul.locConst_pos (by omega : 1 ≤ N) hT).le
        have h4 : (0 : ℝ) ≤ C₄ := hC₄.le
        linarith,
    min (min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) c₇,
    lt_min (lt_min (lt_min (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₄) hc₅) hc₆) hc₇,
    L₁ + L₂ + L₃ + L₄ + L₅ + L₆ + L₇ + 2, ?_⟩
  intro L hL r hr
  have hL1 : L₁ ≤ L := by omega
  have hL2 : L₂ ≤ L := by omega
  have hL3 : L₃ ≤ L := by omega
  have hL4 : L₄ ≤ L := by omega
  have hL5 : L₅ ≤ L := by omega
  have hL6 : L₆ ≤ L := by omega
  have hL7 : L₇ ≤ L := by omega
  have hLpos : 1 ≤ L := by omega
  -- each component, at the common `L`
  have hB1 : (arrayMeasure N).real (sumBadOcc (N := N) p m r T L) ≤ 1 * exf c₁ L := by
    have hb := (h₁ L hL1 (r := r) hr)
    have hreal : (arrayMeasure N).real (sumBadOcc (N := N) p m r T L)
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
    have hexp : Real.exp (-c₁ * LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) ≤ exf c₁ L := by
      unfold exf
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [one_mul]
    exact le_trans hreal hexp
  have hB2 : (arrayMeasure N).real (occBad (N := N) p m r T L)
      ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * exf c₂ L := by
    have hb := h₂ L hL2 (r := r) hr
    simpa only [occBad, exf, LocSumAct.xOf] using hb
  have hB3 : (arrayMeasure N).real (sumBadCoord (N := N) p m A r T L)
      ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T * exf c₃ L := by
    have hb := (h₃ L hL3 r hr).1
    rw [measureReal_def]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
    have hCT0 : (0 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T :=
      le_trans zero_le_one
        (LocCoordPaper.one_le_CTof (le_trans zero_le_one (LocalGood.one_le_CU p m A)) T)
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hB4 : (arrayMeasure N).real (moveBad (N := N) p m A hA hAc r T L) ≤ C₄ * exf c₄ L := by
    have hb := h₄ L (max_le hL4 (by omega)) r hr
    simpa only [exf, LocSumAct.xOf, neg_mul] using hb
  have hB5 : (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L) ≤ 1 * exf c₅ L := by
    have hb := h₅ L hL5 r hr
    rw [one_mul]
    have hreal : (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L)
        ≤ Real.exp (-c₅ * LocSumAct.xOf L) := by
      rw [measureReal_def]
      refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb) ?_
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simpa only [exf, LocSumAct.xOf, neg_mul] using hreal
  have hB6 : (arrayMeasure N).real (RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L)
      ≤ LocGroupSimul.locConst N T * exf c₆ L := by
    have hb := h₆ L hL6 r hr
    simpa only [exf, LocSumAct.xOf, neg_mul] using hb
  have hB7 : (arrayMeasure N).real (RecordClock.locMartBad (N := N) p m r T L) ≤ 1 * exf c₇ L := by
    have hb := h₇ L hL7 r
    have hxeq : RecordClock.xOf L = LocSumAct.xOf L := rfl
    rw [hxeq] at hb
    rw [one_mul]
    simpa only [exf, LocSumAct.xOf, neg_mul] using hb
  -- the union bound
  have hunion : (arrayMeasure N).real (LocalBad (N := N) p m A hA hAc I J hI hJ r T L)
      ≤ (arrayMeasure N).real (sumBadOcc (N := N) p m r T L)
        + (arrayMeasure N).real (occBad (N := N) p m r T L)
        + (arrayMeasure N).real (sumBadCoord (N := N) p m A r T L)
        + (arrayMeasure N).real (moveBad (N := N) p m A hA hAc r T L)
        + (arrayMeasure N).real (LocGroupSimul.LocMaxBad (N := N) p m r T L)
        + (arrayMeasure N).real (RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L)
        + (arrayMeasure N).real (RecordClock.locMartBad (N := N) p m r T L)
        + (arrayMeasure N).real (potBad (N := N) p m) := by
    have h := measureReal_union8_le (N := N)
      (sumBadOcc (N := N) p m r T L) (occBad (N := N) p m r T L)
      (sumBadCoord (N := N) p m A r T L) (moveBad (N := N) p m A hA hAc r T L)
      (LocGroupSimul.LocMaxBad (N := N) p m r T L)
      (RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L)
      (RecordClock.locMartBad (N := N) p m r T L) (potBad (N := N) p m)
    unfold LocalBad
    exact h
  rw [hpot] at hunion
  have hkey : (arrayMeasure N).real (LocalBad (N := N) p m A hA hAc I J hI hJ r T L)
      ≤ 1 * exf c₁ L + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * exf c₂ L
        + LocCoordPaper.CTof (LocalGood.CU p m A) T * exf c₃ L + C₄ * exf c₄ L
        + 1 * exf c₅ L + LocGroupSimul.locConst N T * exf c₆ L + 1 * exf c₇ L := by
    linarith [hunion, hB1, hB2, hB3, hB4, hB5, hB6, hB7]
  refine le_trans hkey ?_
  have hC10 : (0 : ℝ) ≤ 1 := by norm_num
  have hC20 : (0 : ℝ) ≤ ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ := by positivity
  have hC30 : (0 : ℝ) ≤ LocCoordPaper.CTof (LocalGood.CU p m A) T :=
    le_trans zero_le_one
      (LocCoordPaper.one_le_CTof (le_trans zero_le_one (LocalGood.one_le_CU p m A)) T)
  have hC40 : (0 : ℝ) ≤ C₄ := hC₄.le
  have hC60 : (0 : ℝ) ≤ LocGroupSimul.locConst N T :=
    (LocGroupSimul.locConst_pos (by omega : 1 ≤ N) hT).le
  -- the fold into one profile term
  have s1 : 1 * exf c₁ L + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * exf c₂ L
      ≤ (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) * exf (min c₁ c₂) L := by
    have h := exf_two (C₁ := 1) (C₂ := ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
      (c₁ := c₁) (c₂ := c₂) hC10 hC20 hc₁ hc₂ L
    exact h
  have s2 : (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂) * exf (min c₁ c₂) L
      + LocCoordPaper.CTof (LocalGood.CU p m A) T * exf c₃ L
      ≤ ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) * exf (min (min c₁ c₂) c₃) L :=
    exf_two (C₁ := 1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
      (C₂ := LocCoordPaper.CTof (LocalGood.CU p m A) T)
      (c₁ := min c₁ c₂) (c₂ := c₃) (by linarith) hC30 (lt_min hc₁ hc₂) hc₃ L
  have s3 : ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) * exf (min (min c₁ c₂) c₃) L
      + C₄ * exf c₄ L
      ≤ (((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) * exf (min (min (min c₁ c₂) c₃) c₄) L :=
    exf_two (C₁ := (1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T)
      (C₂ := C₄) (c₁ := min (min c₁ c₂) c₃) (c₂ := c₄)
      (by linarith) hC40 (lt_min (lt_min hc₁ hc₂) hc₃) hc₄ L
  have s4 : (((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) * exf (min (min (min c₁ c₂) c₃) c₄) L
      + 1 * exf c₅ L
      ≤ ((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1)
        * exf (min (min (min (min c₁ c₂) c₃) c₄) c₅) L := by
    have h := exf_two (C₁ := ((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) (C₂ := 1)
      (c₁ := min (min (min c₁ c₂) c₃) c₄) (c₂ := c₅)
      (by linarith) hC10 (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₄) hc₅ L
    exact h
  have s5 : ((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1)
        * exf (min (min (min (min c₁ c₂) c₃) c₄) c₅) L
      + LocGroupSimul.locConst N T * exf c₆ L
      ≤ (((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1) + LocGroupSimul.locConst N T)
        * exf (min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) L :=
    exf_two (C₁ := (((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1)
      (C₂ := LocGroupSimul.locConst N T)
      (c₁ := min (min (min (min c₁ c₂) c₃) c₄) c₅) (c₂ := c₆)
      (by linarith) hC60 (lt_min (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₄) hc₅) hc₆ L
  have s6 : (((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1) + LocGroupSimul.locConst N T)
        * exf (min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) L
      + 1 * exf c₇ L
      ≤ ((((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1) + LocGroupSimul.locConst N T) + 1)
        * exf (min (min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) c₇) L := by
    have h := exf_two (C₁ := ((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1) + LocGroupSimul.locConst N T)
      (C₂ := 1)
      (c₁ := min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) (c₂ := c₇)
      (by linarith) hC10
      (lt_min (lt_min (lt_min (lt_min (lt_min hc₁ hc₂) hc₃) hc₄) hc₅) hc₆) hc₇ L
    exact h
  have hfold : 1 * exf c₁ L + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂ * exf c₂ L
        + LocCoordPaper.CTof (LocalGood.CU p m A) T * exf c₃ L + C₄ * exf c₄ L
        + 1 * exf c₅ L + LocGroupSimul.locConst N T * exf c₆ L + 1 * exf c₇ L
      ≤ ((((((1 + ((LocOccAllPairs.offDiag N).card : ℝ) * C₂)
        + LocCoordPaper.CTof (LocalGood.CU p m A) T) + C₄) + 1) + LocGroupSimul.locConst N T) + 1)
        * exf (min (min (min (min (min (min c₁ c₂) c₃) c₄) c₅) c₆) c₇) L := by
    linarith [s1, s2, s3, s4, s5, s6]
  exact hfold

end LocalGoodAll
namespace LocalGoodAll

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 4. The simultaneous component conclusions off the one event -/

/-- **What `LocalBad` buys.**  Off the single measured event `LocalBad` and on the paper's carrier
`{d_r ≤ L}` (i.e. `RecClockLG.recordCarrier`, which also pins `ReachAll`), all component clauses of
the paper's good event hold **simultaneously**, each with its own exact carriers:

1. the a.e. forward-potential support (`∀ j u, BddAbove (range (Gtrunc …))`);
2. `(locmart)` for every walker at `[τ_r, τ_r + T*L]`;
3. `(locgroup)` at `τ_r`: for every window `[s,t] ⊆ [τ_r, τ_r+T*L]` on which `(sep)` holds,
   `W^{I,J}_t - W^{I,J}_s ≤ L^{3/4}`;
4. `(locmove)` at `τ_r`: for every window `[s,t] ⊆ [τ_r, τ_r+(T+3)*L]` on which the paper's
   `locmoveGood` and the geometric window hold, `W^{A,Aᶜ}_t - W^{A,Aᶜ}_s ≤ locmoveRHS`;
5. `(loccoord)`: for every `s ≤ t` on the geometric window, the `(loccoord)` display at the
   constant `(2 CU + 1)/2` with the explicit remainder `CTof (CU p m A) T * L^{3/4}`;
6. `(lococc)` at every record fibre: `U ∈ band s0 → U ∈ GoodWinAllPairs s0` (the paper's all-pair
   single-window `(lococc)` event; see the module header for the exact remaining step from this
   membership to the paper's occupation display);
7. `(locsum)` at the `(lococc)` scale, pointwise at every walker `j` and every subinterval of the
   window `[A0, A0 + Lw)`: `Σ_{x∈[a0,b0)} h_j(x)² ≤ 2 Ccan (b0-a0) + 6 Ccan β`, from
   `LocSumR1.array_locsum_h_start` at `L = Lw T L`, `A = A0 r T L` (the side condition
   `2 ellT (xOf (Lw T L)) ≤ A0 r T L` is *derived* here from `(T+3)L ≤ r` and
   `LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le`, not assumed).

Separations `(sep)` (`SepSet`), `locmoveGood`, `locCoordGeom` and `(locsum)` are **carriers** in
3–6, never conclusions.  Nothing here certifies `(sep)` survival, non-vacuity, or any later paper
field. -/
theorem localGood_of_not_mem {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ LocalBad (N := N) p m A hA hAc I J hI hJ r T L →
      (∀ j : Fin N, ∀ u : ℕ,
          BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
        U ∈ RecordClock.locMartGood (N := N) p m r T L ∧
        (∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
          (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) →
          WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
        (∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
          locmoveGood p m A hA (r : ℤ) T L (RecClockLG.Bstar L) (recTimeA p m U r) s t U →
          U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
          WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
            locmoveRHS (N := N) p m A hA L ((2 * LocalGood.CU p m A + 1) / 2)
              (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
                (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U) ∧
        (∀ s t : ℕ, s ≤ t → U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t →
          Swarming.Group.average A
            (fun k => HA p m U t A (X p m U t k) - HA p m U s A (X p m U s k))
            ≤ ((2 * LocalGood.CU p m A + 1) / 2)
                * (((runMaxA p m U hA t : ℤ) : ℝ) - ((Xmin p m U A hA s : ℤ) : ℝ))
              + LocCoordPaper.CTof (LocalGood.CU p m A) T * (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
        (∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
          U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
            (LocOccSiteRate.Ccan p m) r T L s0) ∧
        (∀ j : Fin N, ∀ a0 b0 : ℕ,
          LocOccCarrierAssembly.A0 r T L ≤ a0 →
          b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
            ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
              + 6 * LocOccSiteRate.Ccan p m
                * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ)) := by
  -- the six witnesses
  obtain ⟨c₃, hc₃, L₃, h₃⟩ := LocalGood.loccoord_CU_explicit (N := N) hp0 hp1 hm A hA T
  obtain ⟨c₆, hc₆, L₆, h₆⟩ := RecClockLG.exists_recordClock_locgroup (N := N) hp0 hp1 hm I J hI hJ hid hT
  obtain ⟨c₈, hc₈, L₈, h₈⟩ := RecClockLG.locgroup_at_recordClock (N := N) hp0 hp1 hm I J hI hJ hid hT
  obtain ⟨c₉, hc₉, L₉, h₉⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨max (max (max (max (max L₃ L₆) L₈) L₉) L₁₀) 1, ?_⟩
  intro L hL r hr U hcarr hnot
  have hL3 : L₃ ≤ L := by omega
  have hL6 : L₆ ≤ L := by omega
  have hL8 : L₈ ≤ L := by omega
  have hL9 : L₉ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  -- peel the eight components of `LocalBad`
  have hn1 : U ∉ sumBadOcc (N := N) p m r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn2 : U ∉ occBad (N := N) p m r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn3 : U ∉ sumBadCoord (N := N) p m A r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn4 : ¬ ClockLocMove.locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L)
      ((2 * LocalGood.CU p m A + 1) / 2)
      (LocalGood.betaCU ((2 * LocalGood.CU p m A + 1) / 2)
        (LocCoordPaper.CTof (LocalGood.CU p m A) T) L)
      ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
      (ClockLocMove.locCoordGeom p m A hA r T L) U := by
    intro hc; exact hnot (by unfold LocalBad moveBad; simp only [Set.mem_union, Set.mem_ofPred_eq]; tauto)
  have hn5 : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn6 : U ∉ RecClockLG.locGroupBad (N := N) p m I J hI hJ r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn7 : U ∉ RecordClock.locMartBad (N := N) p m r T L := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hn8 : U ∉ potBad (N := N) p m := by
    intro hc; exact hnot (by unfold LocalBad; simp only [Set.mem_union]; tauto)
  have hpot : ∀ j : Fin N, ∀ u : ℕ,
      BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1)) := by
    have h : ¬ ¬ (∀ j : Fin N, ∀ u : ℕ,
        BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) := hn8
    exact Classical.not_not.mp h
  refine ⟨hpot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(locmart)`
    simpa [RecordClock.locMartGood] using hn7
  · -- `(locgroup)` at `tau_r`
    exact h₈ L hL8 r hr U hcarr hn5 hpot hn6
  · -- `(locmove)` at `tau_r`
    intro s t hs hst htK hgood hgeom
    by_contra hcon
    exact hn4 ⟨hcarr, s, t, hs, hst, htK, hgood, hgeom, hcon⟩
  · -- `(loccoord)`
    intro s t hst hgeom
    have hres := (h₃ L hL3 r hr).2 U hn3 A hA s t hst hgeom.1 hgeom.2.1 hgeom.2.2
    have hRmax : ((Loccoord.Rmax p m U A hA t : ℤ) : ℝ) = ((runMaxA p m U hA t : ℤ) : ℝ) := rfl
    rw [hRmax] at hres
    exact hres
  · -- `(lococc)` at every record fibre
    intro s0 hs0
    have hnotin : U ∉ LocOccFibreSum.band p m r L s0 ∩
        (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
          (LocOccSiteRate.Ccan p m) r T L s0)ᶜ := by
      intro hc
      exact hn2 (Set.mem_iUnion.mpr ⟨s0, hc⟩)
    by_contra hcon
    exact hnotin ⟨hs0, hcon⟩

  · -- `(locsum)` content at the `(lococc)` scale
    intro j a0 b0 ha0 hb0 hab
    have hEq : L + (T + 2) * L = (T + 3) * L := by ring
    have hArith : L + (T + 2) * L ≤ r := by rw [hEq]; exact hr
    have hLA0 : L ≤ LocOccCarrierAssembly.A0 r T L := by
      unfold LocOccCarrierAssembly.A0
      exact Nat.le_sub_of_add_le hArith
    have hside : 2 * ellT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L))
        ≤ LocOccCarrierAssembly.A0 r T L := le_trans (hL₁₀ L hL10) hLA0
    have hL9' : L₉ ≤ LocOccCarrierAssembly.Lw T L :=
      le_trans hL9 (LocOccCarrierAssembly.le_Lw T L)
    exact (h₉ (LocOccCarrierAssembly.Lw T L) hL9' (LocOccCarrierAssembly.A0 r T L) hside).2
      U hn1 j a0 b0 ha0 hb0 hab

end LocalGoodAll
