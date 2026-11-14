/-
# One measured bad event for the local-good core: `univBad ∪ ambBadAll`

## The gap this file closes

The paper's `(local)`/`(goodprob)` is stated off **one** good event with **one** exponential
profile.  In the current tree the deterministic local-good package
(`UniversalFamily.exists_universal_bad_and_good`, profile `CT * exf cT L`) and the ambient
`Γ`-count package (`Swarming.Enl.gamma_ambient_good_measure_ge`, profile
`C_T exp (-c_T √L)`) are measured **separately**, and `UniversalFamily.univBad` does *not*
contain `ambBadAll`.  Every consumer therefore has to carry `U ∈ ambGoodAll` as a second
hypothesis: e.g. `AstarPos.carrierMoveWin_of_univBad` (the only producer of the windowed
carrier from measured events) lists both `U ∉ univBad` and `U ∈ ambGoodAll`, and
`MWin.paper_local_clauses_win` keeps `ambGoodAll` inside `MWin.MoveCarrierWinTrunc`.

This file adds the single set

  `badAll p m Cerr r T L = univBad p m Cerr r T L ∪ ambBadAll p m (r : ℤ) T L`

proves an `exf`-profile bound for it (the paper's profile shape, one pair of constants), and
proves that its complement alone drives the windowed movement carrier and therefore the
paper's `(locmove)` display.  `ambGoodAll` is *measured here*, never assumed: its bound is
derived from `gamma_ambient_good_measure_ge` and the numerical comparison
`xOf L = L^{1/16} ≤ √L`.

## Exact scope

* `exists_badAll_bound` — one `Cerr ≥ 1`, one `CT, cT > 0`, one `L₀`: the single event obeys
  `μ.real (badAll …) ≤ CT * exf cT L` for every `L ≥ L₀` and `r ≥ (T+3)L`.
* `exists_badAll_and_good` — off that single event, on `recordCarrier`, the universal-family
  clause package holds **and** `U ∈ ambGoodAll` (hence `ambGood` for every nonempty proper
  group), with the same constants.
* `carrierMoveWin_of_badAll` / `exists_carrierMoveWin_of_badAll` — the windowed carrier
  `CarrierWin.MoveCarrierWin` off the single event, with a scale `L₀` chosen **before** `N`
  (the campaign's `κ`-before-`N` order), replacing the two-event hypothesis pair of
  `AstarPos.carrierMoveWin_of_univBad`.
* `moveCarrierWinTrunc_of_badAll` — the same in the `MWin.MoveCarrierWinTrunc` shape.

Not proved here and not claimed: the finite run event, the per-group windowed `(locmove)`
failure event, the record carrier itself, block/`d_T` tightness, coalescence, the velocity.
No probability of a good event is assumed; the only probabilistic statements used are the two
already-proved measured bounds.
-/
import Swarm.MWinBlock
import Swarm.AstarPosition

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace SingleBad

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The single bad event -/

/-- **The single measured bad event.**  The deterministic universal-family bad event of
`(locmove)`/`(locgroup)`/`(locmax)`/`(locmart)`/`(lococc)` together with the ambient `Γ`-count
failure set over all nonempty proper groups. -/
noncomputable def badAll (p : ℝ) (m : ℕ) (Cerr : ℝ) (r T L : ℕ) : Set (Array N) :=
  UniversalFamily.univBad (N := N) p m Cerr r T L
    ∪ Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L

theorem mem_badAll {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N} :
    U ∈ badAll (N := N) p m Cerr r T L ↔
      U ∈ UniversalFamily.univBad (N := N) p m Cerr r T L
        ∨ U ∈ Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L := Iff.rfl

/-- Off the single event, the deterministic universal-family bad event is avoided. -/
theorem not_mem_univBad_of_not_mem_badAll {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ}
    {U : Array N} (h : U ∉ badAll (N := N) p m Cerr r T L) :
    U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L :=
  fun hc => h (Or.inl hc)

/-- Off the single event, the ambient `Γ`-count failure set is avoided. -/
theorem not_mem_ambBadAll_of_not_mem_badAll {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ}
    {U : Array N} (h : U ∉ badAll (N := N) p m Cerr r T L) :
    U ∉ Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L :=
  fun hc => h (Or.inr hc)

/-- **Off the single event the paper's simultaneous ambient `Γ`-count event holds.** -/
theorem ambGoodAll_of_not_mem_badAll {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ badAll (N := N) p m Cerr r T L) :
    U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L :=
  not_mem_ambBadAll_of_not_mem_badAll h

/-- **Off the single event every nonempty proper group has its ambient `Γ`-count bound.** -/
theorem ambGood_of_not_mem_badAll {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ} {U : Array N}
    (h : U ∉ badAll (N := N) p m Cerr r T L) {A : Finset (Fin N)} (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) :
    U ∈ Swarming.Enl.ambGood p m hA (r : ℤ) T L :=
  MoveStep.ambGood_of_ambGoodAll hA hAc (ambGoodAll_of_not_mem_badAll h)

/-! ## 2. The measured profile of the ambient bad event in the `exf` shape -/

/-- `xOf L = L^{1/16}` is dominated by `√L` from `L ≥ 1` on.  This is the only numerical
comparison needed to bring the ambient `Γ`-count profile into the `exf` profile of the
deterministic local-good package. -/
theorem xOf_le_sqrt {L : ℕ} (hL : 1 ≤ L) : LocSumAct.xOf L ≤ Real.sqrt (L : ℝ) := by
  rw [LocSumAct.xOf, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) (by norm_num)

/-- **The ambient bad event `ambBadAll` in the `exf` profile.**  Simultaneous over every
nonempty proper group and every integer subinterval of the deterministic ambient window;
the constants are `max (ambConst N m T) 1` and `2/(2T+7)`. -/
theorem exists_measureReal_ambBadAll_le {p : ℝ} (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1)
    {m : ℕ} (hm : 0 < m) (T : ℕ) :
    ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine ⟨max (Swarming.Enl.ambConst N m T) 1, 2 / (2 * (T : ℝ) + 7),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), by positivity, 1, ?_⟩
  intro L hL r hr
  -- the measured complement bound of the ambient event
  have hmeas := Swarming.Enl.measurableSet_ambBadAll (N := N) p hp0 hp1 m hm (r : ℤ) T L
  have hge := Swarming.Enl.gamma_ambient_good_measure_ge (N := N) p hp0 hp1 m hm
    (r := (r : ℤ)) (T := T) (L := L) hL (by exact_mod_cast hr)
  have hcompl : (arrayMeasure N) (Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L)
      = 1 - (arrayMeasure N) (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L) := by
    rw [Swarming.Enl.ambGoodAll]
    exact prob_compl_eq_one_sub (μ := arrayMeasure N) hmeas
  have hbadle1 : (arrayMeasure N) (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L) ≤ 1 := by
    rw [← measure_univ (μ := arrayMeasure N)]
    exact measure_mono (Set.subset_univ _)
  -- `μ ambBadAll ≤ ofReal (ambConst * exp (-c √L))`
  have hENN : (arrayMeasure N) (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)
      ≤ ENNReal.ofReal (Swarming.Enl.ambConst N m T
          * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ))) := by
    refine (ENNReal.sub_le_sub_iff_left (a := (1 : ℝ≥0∞))
      (c := (arrayMeasure N) (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L))
      (b := ENNReal.ofReal (Swarming.Enl.ambConst N m T
          * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ)))) hbadle1
      ENNReal.one_ne_top).mp ?_
    calc 1 - ENNReal.ofReal (Swarming.Enl.ambConst N m T
            * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ)))
        ≤ (arrayMeasure N) (Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L) := hge
      _ = 1 - (arrayMeasure N) (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L) := hcompl
  -- pass to `real`
  have hreal : (arrayMeasure N).real (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)
      ≤ Swarming.Enl.ambConst N m T
          * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ)) := by
    rw [Measure.real]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN) ?_
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (Swarming.Enl.ambConst_nonneg N m T) (Real.exp_pos _).le
  -- bring the profile into the `exf` shape
  have hxL : LocSumAct.xOf L ≤ Real.sqrt (L : ℝ) := xOf_le_sqrt hL
  have hcpos : (0 : ℝ) < 2 / (2 * (T : ℝ) + 7) := by positivity
  have hexp : Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ))
      ≤ Real.exp (-(2 / (2 * (T : ℝ) + 7)) * LocSumAct.xOf L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ)) :=
    (Real.exp_pos _).le
  have hexpnn' : (0 : ℝ) ≤ Real.exp (-(2 / (2 * (T : ℝ) + 7)) * LocSumAct.xOf L) :=
    (Real.exp_pos _).le
  have hsingle : Swarming.Enl.ambConst N m T
        * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt (L : ℝ))
      ≤ max (Swarming.Enl.ambConst N m T) 1
        * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * LocSumAct.xOf L) := by
    refine le_trans (mul_le_mul_of_nonneg_right
      (le_max_left (Swarming.Enl.ambConst N m T) (1 : ℝ)) hexpnn) ?_
    exact mul_le_mul_of_nonneg_left hexp (le_trans zero_le_one (le_max_right _ 1))
  simpa only [LocalGoodAll.exf, neg_mul] using le_trans hreal hsingle

/-
## 3. The single profile, and the paper-form good package off the single event
-/

section Combined

variable {p : ℝ} {m : ℕ} {Cerr : ℝ} {r T L : ℕ}

/-- **Everything that follows from both measured events follows from the single event.** -/
theorem good_of_badAll {P : Array N → Prop}
    (h : ∀ U : Array N, U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
      U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L → P U)
    {U : Array N} (hU : U ∉ badAll (N := N) p m Cerr r T L) : P U :=
  h U (not_mem_univBad_of_not_mem_badAll hU) (ambGoodAll_of_not_mem_badAll hU)

theorem compl_badAll_subset :
    (badAll (N := N) p m Cerr r T L)ᶜ
      ⊆ (UniversalFamily.univBad (N := N) p m Cerr r T L)ᶜ
          ∩ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L :=
  fun U hU => ⟨not_mem_univBad_of_not_mem_badAll hU, ambGoodAll_of_not_mem_badAll hU⟩

end Combined

/-- **One bad event, one profile.**  The union of the deterministic universal-family bad event and
the ambient `Γ`-count failure set over all nonempty proper groups obeys the paper's single
exponential profile `CT * exf cT L`, with constants that are functions of `N, m, p, T` alone. -/
theorem exists_badAll_bound {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (badAll (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L := by
  obtain ⟨Cerr, CT₁, c₁, hCerr1, hCT₁, hc₁, L₁, hb₁⟩ :=
    UniversalFamily.exists_univBad_bound (N := N) hp0 hp1 hm hN hT
  obtain ⟨CT₂, c₂, hCT₂, hc₂, L₂, hb₂⟩ :=
    exists_measureReal_ambBadAll_le (N := N) (m := m) hp0.le hp1 (by omega) T
  refine ⟨Cerr, hCerr1, CT₁ + CT₂, min c₁ c₂, by linarith, lt_min hc₁ hc₂, max L₁ L₂, ?_⟩
  intro L hL r hr
  have hL1 : L₁ ≤ L := le_trans (le_max_left L₁ L₂) hL
  have hL2 : L₂ ≤ L := le_trans (le_max_right L₁ L₂) hL
  refine le_trans (measureReal_union_le (μ := arrayMeasure N)
    (UniversalFamily.univBad (N := N) p m Cerr r T L)
    (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
  refine le_trans (add_le_add (hb₁ L hL1 r hr) (hb₂ L hL2 r hr)) ?_
  exact LocalGoodAll.exf_two hCT₁.le hCT₂.le hc₁ hc₂ L

/-- **Proposition `local` off the single measured bad event.**

Same constants `Cerr ≥ 1`, `CT, cT > 0`, `L₀` as the universal-family theorem, but the
avoidance hypothesis is the *single* event `badAll = univBad ∪ ambBadAll`; off it the ambient
`Γ`-count event `ambGoodAll` holds as well, hence `ambGood` for **every** nonempty proper group
simultaneously.  Nothing here estimates a good event: the bound on `badAll` is
`exists_badAll_bound`, proved from the two already-measured component bounds. -/
theorem exists_badAll_and_good {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (badAll (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ badAll (N := N) p m Cerr r T L →
        (∀ (A : Finset (Fin N)) (hA : A.Nonempty), A ≠ Finset.univ →
            U ∈ Swarming.Enl.ambGood p m hA (r : ℤ) T L) ∧
          U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L ∧
          U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L) := by
  obtain ⟨Cerr, CT₁, c₁, hCerr1, hCT₁, hc₁, L₁, hb₁⟩ :=
    UniversalFamily.exists_univBad_bound (N := N) hp0 hp1 hm hN hT
  obtain ⟨CT₂, c₂, hCT₂, hc₂, L₂, hb₂⟩ :=
    exists_measureReal_ambBadAll_le (N := N) (m := m) hp0.le hp1 (by omega) T
  refine ⟨Cerr, hCerr1, CT₁ + CT₂, min c₁ c₂, by linarith, lt_min hc₁ hc₂, max L₁ L₂, ?_, ?_⟩
  · intro L hL r hr
    have hL1 : L₁ ≤ L := le_trans (le_max_left L₁ L₂) hL
    have hL2 : L₂ ≤ L := le_trans (le_max_right L₁ L₂) hL
    refine le_trans (measureReal_union_le (μ := arrayMeasure N)
      (UniversalFamily.univBad (N := N) p m Cerr r T L)
      (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
    refine le_trans (add_le_add (hb₁ L hL1 r hr) (hb₂ L hL2 r hr)) ?_
    exact LocalGoodAll.exf_two hCT₁.le hCT₂.le hc₁ hc₂ L
  · intro L hL r hr U _ hU
    refine ⟨?_, ambGoodAll_of_not_mem_badAll hU,
      AstarPos.not_mem_LocMaxBad_of_not_mem_univBad (not_mem_univBad_of_not_mem_badAll hU)⟩
    intro A hA hne
    exact ambGood_of_not_mem_badAll hU hA (by
      rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hne)

/-! ## 4. The windowed movement carrier off the single event, with the scale chosen before `N` -/

/-- **`AstarPos.exists_Kc` is independent of `N`.**  Re-exported in the exact shape used below:
the run length `Kc p L` is admissible from a scale depending only on `p`. -/
theorem exists_Kc' {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      1 ≤ AstarPos.Kc p L ∧
        (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p) :=
  AstarPos.exists_Kc hp0 hp1

/-- **The windowed movement carrier off the single measured event.**

There is a scale `L₀`, depending only on `p` (so chosen before `N` and before `m`, `T`, `r`),
such that for every `N ≥ 2`, every `L ≥ L₀`, every block scale `T`, every error coefficient and
every record level `r ≥ (T+3)L`: on the record carrier, *off the single event `badAll`*, with the
finite run event on the record window, the windowed movement carrier holds.

Compared with `AstarPos.carrierMoveWin_of_univBad` the two hypotheses `U ∉ univBad` and
`U ∈ ambGoodAll` are replaced by the single `U ∉ badAll`, whose `exf` profile is
`exists_badAll_bound`; the `∃ L₀` is outside both `∀ N` and all other parameters. -/
theorem exists_carrierMoveWin_of_badAll {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ L₀ : ℕ, ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ L ≥ L₀, ∀ (T : ℕ) (Cerr : ℝ) (r : ℕ),
      (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ badAll (N := N) p m Cerr r T L →
        (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
          ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L)) →
        CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  obtain ⟨L₀, hL₀⟩ := exists_Kc' hp0 hp1
  refine ⟨max L₀ 2, ?_⟩
  intro N _ hN L hL T Cerr r hr U hcarr hnot hrun
  have hL1 : 1 ≤ L := le_trans (by omega : (1 : ℕ) ≤ max L₀ 2) hL
  have hL0 : L₀ ≤ L := le_trans (le_max_left L₀ 2) hL
  have hr2 : (T + 2) * L + 2 ≤ r := by
    refine le_trans ?_ hr
    calc (T + 2) * L + 2 ≤ (T + 2) * L + L := Nat.add_le_add_left (by omega : 2 ≤ L) _
      _ = (T + 3) * L := by ring
  have hamb : U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L :=
    ambGoodAll_of_not_mem_badAll hnot
  have hnb : U ∉ LocGroupSimul.LocMaxBad (N := N) p m r T L :=
    AstarPos.not_mem_LocMaxBad_of_not_mem_univBad (not_mem_univBad_of_not_mem_badAll hnot)
  exact AstarPos.moveCarrierWin_of_carrier_hybrid (N := N) hp0 hp1 hL1 hr2 hcarr hamb hnb
    (hL₀ L hL0).1 (hL₀ L hL0).2 hrun

/-- **Every walker is one level above `Astar` throughout the record window.**  `winTrunc` states
its position conjunct as `Aw + 1 ≤ X`, one more than the `Astar` bound of
`AstarPos.Astar_le_X_of_carrier`; the slack-parametric left edge at `K = T` gives exactly
`r - (T+1)L - 1 = Astar + L - ... ≥ Astar + 1` because `L ≥ 1`. -/
theorem Astar_succ_le_X_of_carrier {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) (hL : 1 ≤ L)
    (hr : (T + 2) * L + 1 ≤ r) {s : ℕ} (hs1 : recTimeA p m U r ≤ s)
    (hs2 : s ≤ recTimeA p m U r + T * L) (j : Fin N) :
    RecClockLG.Astar r T L + 1 ≤ (X p m U s j).toNat := by
  have hsplit : (T + 2) * L = (T + 1) * L + L := by ring
  have hr' : (T + 1) * L + 1 ≤ r := by
    rw [hsplit] at hr
    omega
  have hle := AstarPos.leftEdge_le_actX_of_carrier (N := N) (T := T) (K := T) hcarr hr' hs1 hs2 j
  have hle' : (T + 1) * L + 1 ≤ (T + 2) * L := by
    rw [hsplit]
    exact Nat.add_le_add_left hL _
  have hnat : RecClockLG.Astar r T L + 1 ≤ r - ((T + 1) * L + 1) := by
    have hAst : RecClockLG.Astar r T L = r - ((T + 2) * L + 1) := rfl
    rw [hAst]
    have hstep : r - ((T + 2) * L + 1) + 1 = r - (T + 2) * L := by omega
    rw [hstep]
    exact Nat.sub_le_sub_left hle' r
  have hcast : ((RecClockLG.Astar r T L + 1 : ℕ) : ℤ) ≤ ((r - ((T + 1) * L + 1) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  have hX : ((RecClockLG.Astar r T L + 1 : ℕ) : ℤ) ≤ actX p m U j s := le_trans hcast hle
  have hnn : (0 : ℤ) ≤ actX p m U j s := le_trans (by exact_mod_cast Nat.zero_le _) hX
  rw [SepGroup.Model.X_apply, ← LocCoordPaper.actX_eq_pos, Int.le_toNat hnn]
  exact hX

/-- **The same carrier in the `winTrunc` shape** used by `MWin.paper_local_clauses_win`:
`MWin.MoveCarrierWinTrunc` at `Aw = Astar r T L`. -/
theorem moveCarrierWinTrunc_of_badAll {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {L₀ : ℕ}
    (hL₀ : ∀ L : ℕ, L₀ ≤ L → 1 ≤ AstarPos.Kc p L ∧
      (AstarPos.Kc p L : ℝ) ≤ LocSumAct.xOf L * (1 - (1 - p) / p))
    {N : ℕ} [Nonempty (Fin N)] {L : ℕ} (hL : L₀ ≤ L) (hL2 : 2 ≤ L)
    {T : ℕ} {Cerr : ℝ} {r : ℕ} {U : Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hr : (T + 3) * L ≤ r)
    (hnot : U ∉ badAll (N := N) p m Cerr r T L)
    (hrun : ∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
      ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L)) :
    MWin.MoveCarrierWinTrunc (N := N) p m r T L (RecClockLG.Astar r T L) U := by
  have hr2 : (T + 2) * L + 2 ≤ r := by
    refine le_trans ?_ hr
    calc (T + 2) * L + 2 ≤ (T + 2) * L + L := Nat.add_le_add_left (by omega : 2 ≤ L) _
      _ = (T + 3) * L := by ring
  have hwin : CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U :=
    AstarPos.moveCarrierWin_of_carrier_hybrid (N := N) hp0 hp1 (by omega : 1 ≤ L) hr2 hcarr
      (ambGoodAll_of_not_mem_badAll hnot)
      (AstarPos.not_mem_LocMaxBad_of_not_mem_univBad (not_mem_univBad_of_not_mem_badAll hnot))
      (hL₀ L hL).1 (hL₀ L hL).2 hrun
  intro A hA hne s t hs hst ht hsep
  obtain ⟨hamb, hgW, hstep⟩ := hwin A hA hne s t hs hst ht hsep
  exact ⟨hamb, fun n hn => MWin.winTrunc_of_goodWWin (hgW n hn) (fun k => by
    exact Astar_succ_le_X_of_carrier (N := N) hcarr (by omega) (by omega)
      (le_trans hs (Finset.mem_Ico.mp hn).1)
      (le_trans (le_of_lt (Finset.mem_Ico.mp hn).2) ht) k), hstep⟩

/-! ## 5. Axiom audit -/


end SingleBad
