/-
Raw `hpath` from raw exhaustiveness.

`ActualNeutralCapstone.main_claim_actual_of_invariant_neutral` (and hence
`NeutralPaperBridge.paperClaim_of_invariant_neutral`) consumes a path-law
input `hpath`: for every `N ≥ 2` there are measurable `S : Array N → ℕ` and
`c : Array N → ℝ` with

  `(arrayMeasure N).map (fun U n i => pos (actualX) (n + S U) i U - c U)`
    `= (seedCond).map (M6Star.actPath)`.

This file discharges that input from the single remaining stochastic
statement `mu {D = top} = 0`, the same nullity that `RawAttemptBridge`
identifies with the nullity of its infinite-failure event.

The engine is the already-proved *restricted* identity
`RawInitialPathLaw.restrict_D_ne_top_map_firstFutureR`: the removal set of the
restricted translated-path law is exactly `{D != top}`, and on it the total
first-cell selectors `firstTime`/`firstLevel` give the `seedCond` path law
multiplied by the mass of that set.  When the set has mass one the coefficient
is one and the restriction is invisible, which is literally `hpath`.

No exhaustiveness is asserted here: `mu {D = top} = 0` remains an explicit
hypothesis of every theorem below.  The point is that it is the *only*
stochastic input of `hpath`; the rest is exact measure algebra.
-/
import Swarm.RawInitialPathLaw

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace HpathFromDtopNull

open Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRawTimeStrictSum

variable {N : ℕ}

/-! ## Reusable measure algebra -/

/-- A measurable set whose complement is null carries the whole probability. -/
theorem restrict_eq_of_compl_null {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) (h : μ sᶜ = 0) :
    μ.restrict s = μ := by
  ext t ht
  rw [Measure.restrict_apply ht]
  have hdiff : μ (t \ s) = 0 := measure_mono_null (fun x hx => hx.2) h
  have hsum := measure_inter_add_sdiff (μ := μ) t hs
  rw [hdiff, add_zero] at hsum
  exact hsum

/-- A measurable set whose complement is null has full probability. -/
theorem measure_eq_one_of_compl_null {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) (h : μ sᶜ = 0) :
    μ s = 1 := by
  have hsum := measure_add_measure_compl (μ := μ) hs
  rw [h, measure_univ, add_zero] at hsum
  exact hsum

/-- **Removal of a null restriction.**  If the restricted translated law carries
the full total mass as coefficient, the unrestricted translated law is the
target law.  This is the exact step from the restricted `hpath` statement to
the paper's `hpath` statement. -/
theorem map_eq_of_restrict_smul {α β : Type*} {m0 : MeasurableSpace α} {m1 : MeasurableSpace β}
    {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) (h : μ sᶜ = 0)
    {f : α → β} {ν : Measure β} (hmap : (μ.restrict s).map f = μ s • ν) :
    μ.map f = ν := by
  have hμ : μ s = 1 := measure_eq_one_of_compl_null hs h
  rw [restrict_eq_of_compl_null hs h, hμ, one_smul] at hmap
  exact hmap

/-! ## The raw removal set is exactly `{D = top}` -/

/-- The union of the canonical raw first cells is measurable. -/
theorem measurableSet_iUnion_rawFirstCell (p : ℝ) (m : ℕ) :
    MeasurableSet (⋃ q : LevelTime,
      RawInitialPathLaw.rawFirstCell (N := N) p m q Set.univ) :=
  MeasurableSet.iUnion fun q =>
    RawInitialPathLaw.measurableSet_rawFirstCell p m q MeasurableSet.univ

/-- The raw completed event `{D != top}` is measurable. -/
theorem measurableSet_D_ne_top (p : ℝ) (m : ℕ) (hN : 0 < N) :
    MeasurableSet {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤} := by
  rw [← RawInitialPathLaw.iUnion_rawFirstCell_univ p m hN]
  exact measurableSet_iUnion_rawFirstCell p m

/-- Complement-nullity of the raw completed set, as the `hpath` removal form. -/
theorem compl_D_ne_top_eq_zero {p : ℝ} {m : ℕ}
    (htop : (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0) :
    (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤}ᶜ = 0 := by
  have hset : {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤}ᶜ =
      {U : Array N | RegenPath.D (posPath p m U) = ⊤} := by
    ext U
    simp
  rw [hset]
  exact htop

/-! ## The exact raw `hpath` identity from raw exhaustiveness -/

/-- **`hpath` from `mu {D = top} = 0`.**  The finite measurable selectors are the
literal raw first-cell selectors `firstTime` (time shift) and `firstLevel`
(spatial shift).  No invariant record law and no positivity of the original raw
path is used; only the strict-path mass being nonzero, which holds in the paper
parameter range. -/
theorem hpath_of_D_top_null {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (htop : (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0) :
    ∃ (S : Array N → ℕ) (c : Array N → ℝ), Measurable S ∧ Measurable c ∧
      Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N) =
      Measure.map (M6Star.actPath (N := N) p m)
        (SwarmFB.seedCond (p := p) (m := m) (N := N)) := by
  have hNpos : 0 < N := by omega
  refine ⟨RawStrictTransport.firstTime p m,
    fun U => (RawStrictTransport.firstLevel p m U : ℝ), ?_, ?_, ?_⟩
  · exact RawStrictTransport.measurable_firstTime p m
  · exact (measurable_of_countable (fun d : ℕ => (d : ℝ))).comp
      (RawStrictTransport.measurable_firstLevel p m)
  · have hmeas : MeasurableSet {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤} :=
      measurableSet_D_ne_top p m hNpos
    have hcompl := compl_D_ne_top_eq_zero (N := N) (p := p) (m := m) htop
    have hmap := RawInitialPathLaw.restrict_D_ne_top_map_firstFutureR
      (N := N) hp0 hp1 hm hN
    have hout := map_eq_of_restrict_smul hmeas hcompl hmap
    exact hout

/-- The `hpath` premise of `NeutralPaperBridge` in its exact quantifier order,
derived from raw exhaustiveness for every `N ≥ 2`. -/
theorem hpath_of_D_top_null_all {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m)
    (htop : ∀ (N : ℕ), 2 ≤ N →
      (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) = ⊤} = 0) :
    ∀ (N : ℕ), 2 ≤ N →
      ∃ (S : Array N → ℕ) (c : Array N → ℝ), Measurable S ∧ Measurable c ∧
        Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
          Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N) =
        Measure.map (M6Star.actPath (N := N) p m)
          (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
  fun N hN => hpath_of_D_top_null hp0 hp1 hm hN (htop N hN)

/-- Raw cell exhaustiveness in cover form is the same nullity, so `hpath` also
follows from a full-mass raw cell cover. -/
theorem hpath_of_rawCells_full {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hcover : (arrayMeasure N)
      (⋃ q : LevelTime, RawInitialPathLaw.rawFirstCell (N := N) p m q Set.univ) = 1) :
    ∃ (S : Array N → ℕ) (c : Array N → ℝ), Measurable S ∧ Measurable c ∧
      Measure.map (fun U : Array N => fun (n : ℕ) (i : Fin N) =>
        Swarm.pos (Swarm.actualX (N := N) p m) (n + S U) i U - c U) (arrayMeasure N) =
      Measure.map (M6Star.actPath (N := N) p m)
        (SwarmFB.seedCond (p := p) (m := m) (N := N)) := by
  have hNpos : 0 < N := by omega
  have hmeas : MeasurableSet (⋃ q : LevelTime,
      RawInitialPathLaw.rawFirstCell (N := N) p m q Set.univ) :=
    measurableSet_iUnion_rawFirstCell (N := N) p m
  have hc' : (arrayMeasure N) (⋃ q : LevelTime,
      RawInitialPathLaw.rawFirstCell (N := N) p m q Set.univ)ᶜ = 0 := by
    rw [measure_compl hmeas (measure_ne_top _ _), hcover, measure_univ]
    simp
  have hset : (⋃ q : LevelTime,
      RawInitialPathLaw.rawFirstCell (N := N) p m q Set.univ) =
      {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤} :=
    RawInitialPathLaw.iUnion_rawFirstCell_univ p m hNpos
  rw [hset] at hc'
  refine hpath_of_D_top_null hp0 hp1 hm hN ?_
  have hcompl : {U : Array N | RegenPath.D (posPath p m U) = ⊤} =
      {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤}ᶜ := by
    ext U
    simp
  rw [hcompl]
  exact hc'

end HpathFromDtopNull
