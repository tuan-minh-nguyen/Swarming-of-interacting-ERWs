/-  The paper (`main_1d_revised.tex`, proof of Proposition `ball`) uses the projected
  potential

      H_{j,n}(x) = E[H_j(x) | F_n],      F_n = enlarged filtration (positions + revealed marks),

  and needs the two structural facts

  * for `x <= r_n = M_n^j`:  `H_{j,n}(x) = H_j(x)`   (the value is revealed below the record),
  * `(projH)`: for `y > r_n`,
      `H_{j,n}(y) = H_j(r_n) + (y-r_n) (1+a)/(1-a)
                     + (E[h_j(r_n)|F_n] - (1+a)/(1-a)) (1-a^{y-r_n})/(1-a)`.

  `Swarm/RecordAbove.lean` proves the above-record *summed* identity for the
  conditional expectation of the potential at the random site `r_n + g` and explicitly records
  that the replacement of `E[H_j(r_n)|F_n]` by the quenched `H_j(r_n)` is NOT proved there
  (it needs `enlFilt`-measurability of the potential at the record).  `S14.lean` in
  `spatialavg` proves the analogous recursion on the mark space at a *deterministic* record.

  This file closes exactly that gap at the actual array, in the sitewise form the paper uses
  (the projection `projH` evaluated at a fixed site `y`, with the statement restricted to the
  `F_n`-measurable piece on which `y` is the record or the `g`-th site above it).  The point
  is that `projH (r_n)` is the sitewise projection read at the random site, which is *not* the
  optional projection of the random-site potential; each statement therefore carries the piece
  condition explicitly.

  Contents:
  * `Hpot_record_eq_sum_belowSeed`, `measurable_Hpot_record_enlFilt` — the quenched potential at
    the running record is `enlFilt n`-measurable, hence its own conditional expectation;
  * `condExp_Hpot_record` — `E[H_j(r_n)|F_n] = H_j(r_n)`;
  * `projH_eq_Hpot_of_le_record` — the paper's `x <= r_n` identity at a fixed site;
  * `projH_closed_form_piece` — the paper's `(projH)` for the projection at a fixed site `y` on
    the piece `{y = r_n + g}`, with `e_0 = E[h_j(r_n)|F_n]` (`eRec`).

  No `sorry`, no custom axiom.
-/
import Swarm.RecordAbove
import Swarm.BelowRecord
import Swarm.ProjLedger

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ### 1. The quenched potential at the running record -/

/-- The below-record seed at site `u` is the actual value of `h_j` when `u` is below the record. -/
lemma belowSeed_eq_hof {p : ℝ} (m n : ℕ) (j : Fin N) (u : ℕ) {U : Array N}
    (h : (u : ℤ) < recVal j (prefOf p m n U)) :
    belowSeed p m n j u U = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := by
  have h' : U ∈ {U : Array N | (u : ℤ) < recVal j (prefOf p m n U)} := h
  rw [belowSeed]
  exact Set.indicator_of_mem h' _

/-- **`H_j(M_n^j)` as a piece function of the record**, with the below-record seeds. -/
theorem Hpot_record_eq_piece (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
      = (if recVal j (prefOf p m n U) ≤ 0 then
          ((recVal j (prefOf p m n U) : ℤ) : ℝ)
         else ∑ u ∈ Finset.range ((recVal j (prefOf p m n U)).toNat), belowSeed p m n j u U) := by
  set r := recVal j (prefOf p m n U) with hr
  have hr0 : 0 ≤ r := zero_le_recVal_prefOf p m U j n
  rw [SwarmOcc.Hpot]
  by_cases hpos : r ≤ 0
  · rw [if_pos hpos, if_pos hpos]
  · rw [if_neg hpos, if_neg hpos]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' : u < r.toNat := Finset.mem_range.mp hu
    have hlt : (u : ℤ) < r := by
      have h1 : ((u : ℕ) : ℤ) < ((r.toNat : ℕ) : ℤ) := by exact_mod_cast hu'
      rwa [Int.toNat_of_nonneg hr0] at h1
    exact (belowSeed_eq_hof m n j u hlt).symm

/-- **`H_j(M_n^j)` is the sum of the below-record seeds.**  Because every site strictly below the
running record is revealed, the quenched potential at the record is a finite sum of below-record
pieces. -/
theorem Hpot_record_eq_sum_belowSeed (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
      = ∑ u ∈ Finset.range ((recVal j (prefOf p m n U)).toNat), belowSeed p m n j u U := by
  rw [Hpot_record_eq_piece]
  by_cases hpos : recVal j (prefOf p m n U) ≤ 0
  · rw [if_pos hpos]
    have hz : recVal j (prefOf p m n U) = 0 :=
      le_antisymm hpos (zero_le_recVal_prefOf p m U j n)
    rw [hz]
    simp
  · rw [if_neg hpos]

/-- **The quenched potential at the running record is `enlFilt n`-measurable.**  This is the
paper's `H_j(r_n) in F_n` (via `x < r_n`-revealedness), at the random record. -/
theorem measurable_Hpot_record_enlFilt {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))) := by
  classical
  letI : MeasurableSpace (Array N) := enlFilt p m n
  have hpiece : ∀ i : ℤ, Measurable fun U : Array N =>
      (if i ≤ 0 then ((i : ℤ) : ℝ)
       else ∑ u ∈ Finset.range i.toNat, belowSeed p m n j u U) := by
    intro i
    by_cases hi : i ≤ 0
    · simp only [if_pos hi]; exact measurable_const
    · simp only [if_neg hi]
      exact Finset.measurable_sum _ fun u _ => measurable_belowSeed hp m n j u
  have hidx : Measurable fun U : Array N => recVal j (prefOf p m n U) := by
    have h := measurable_runMax_enl (N := N) p m n j
    simpa only [runMax_eq_recVal] using h
  have h := SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℤ)
    (U := fun i : ℤ => fun U : Array N =>
      (if i ≤ 0 then ((i : ℤ) : ℝ)
       else ∑ u ∈ Finset.range i.toNat, belowSeed p m n j u U))
    hpiece (fun U => recVal j (prefOf p m n U))
    (fun i => hidx (measurableSet_singleton i))
  have hfun : (fun U : Array N =>
      (if recVal j (prefOf p m n U) ≤ 0 then ((recVal j (prefOf p m n U) : ℤ) : ℝ)
       else ∑ u ∈ Finset.range ((recVal j (prefOf p m n U)).toNat), belowSeed p m n j u U))
      = fun U : Array N => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U)) := by
    funext U
    exact (Hpot_record_eq_piece p m n j U).symm
  rwa [hfun] at h

/-! ### 2. The truncated values are measurable below the record -/

/-- The record level `k ≤ M_n^j` is `enlFilt n`-measurable. -/
lemma measurableSet_le_record (p : ℝ) (m n : ℕ) (j : Fin N) (k : ℤ) :
    MeasurableSet[enlFilt p m n] {U : Array N | k ≤ recVal j (prefOf p m n U)} := by
  have hidx : Measurable[enlFilt p m n] (fun U : Array N => recVal j (prefOf p m n U)) := by
    have h := measurable_runMax_enl (N := N) p m n j
    simpa only [runMax_eq_recVal] using h
  exact measurableSet_le measurable_const hidx

/-- The indicator of a record level is `enlFilt`-strongly measurable. -/
lemma stronglyMeasurable_indicator_level (p : ℝ) (m n : ℕ) (j : Fin N) (k : ℤ) :
    StronglyMeasurable[enlFilt p m n]
      (({U : Array N | k ≤ recVal j (prefOf p m n U)}.indicator (fun _ => (1 : ℝ)))) :=
  StronglyMeasurable.ite (p := fun U : Array N => k ≤ recVal j (prefOf p m n U))
    (measurableSet_le_record p m n j k) stronglyMeasurable_const stronglyMeasurable_const

/-- **Truncation of `h_j(u)` at a record level above it is `enlFilt`-strongly measurable.** -/
lemma stronglyMeasurable_indicator_hof_le_record {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    (m n : ℕ) (j : Fin N) (u : ℕ) {k : ℤ} (huk : (u : ℤ) < k) :
    StronglyMeasurable[enlFilt p m n]
      ({U : Array N | k ≤ recVal j (prefOf p m n U)}.indicator
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)) := by
  have hB : StronglyMeasurable[enlFilt p m n] (belowSeed p m n j u) :=
    (measurable_belowSeed hp m n j u).stronglyMeasurable
  have hI := stronglyMeasurable_indicator_level (N := N) p m n j k
  have hEq : ({U : Array N | k ≤ recVal j (prefOf p m n U)}.indicator
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u))
      = fun U : Array N =>
        (({U : Array N | k ≤ recVal j (prefOf p m n U)}.indicator (fun _ => (1 : ℝ))) U)
          * belowSeed p m n j u U := by
    funext U
    by_cases h : U ∈ {U : Array N | k ≤ recVal j (prefOf p m n U)}
    · have hk : k ≤ recVal j (prefOf p m n U) := h
      simp only [Set.indicator_of_mem h, one_mul]
      exact (belowSeed_eq_hof m n j u (lt_of_lt_of_le huk hk)).symm
    · simp [Set.indicator_of_notMem h]
  rw [hEq]
  exact hI.mul hB

/-- **The potential cut off at a record level is `enlFilt`-strongly measurable.** This is the
paper's `H_j(x) in F_n` for `x ≤ r_n`. -/
theorem stronglyMeasurable_indicator_Hpot_le_record {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p)
    (m n : ℕ) (j : Fin N) (y : ℤ) :
    StronglyMeasurable[enlFilt p m n]
      ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
        (fun U => SwarmOcc.Hpot (siteH p m j U) y)) := by
  by_cases hy : y ≤ 0
  · have hconst : ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
        (fun U => SwarmOcc.Hpot (siteH p m j U) y))
        = fun U : Array N => (y : ℝ) *
          ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator (fun _ => (1 : ℝ))) U := by
      funext U
      by_cases h : U ∈ {U : Array N | y ≤ recVal j (prefOf p m n U)}
      · simp only [Set.indicator_of_mem h, SwarmOcc.Hpot_of_nonpos hy, mul_one]
      · simp [Set.indicator_of_notMem h]
    rw [hconst]
    exact stronglyMeasurable_const.mul (stronglyMeasurable_indicator_level p m n j y)
  · push Not at hy
    have hsum : ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
        (fun U => SwarmOcc.Hpot (siteH p m j U) y))
        = fun U : Array N => ∑ u ∈ Finset.range y.toNat,
            ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
              (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)) U := by
      funext U
      by_cases h : U ∈ {U : Array N | y ≤ recVal j (prefOf p m n U)}
      · rw [Set.indicator_of_mem h, SwarmOcc.Hpot, if_neg (by omega)]
        exact Finset.sum_congr rfl fun u _ =>
          (Set.indicator_of_mem h (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)).symm
      · simp only [Set.indicator_of_notMem h, Finset.sum_const_zero]
    rw [hsum]
    have hterm : ∀ u ∈ Finset.range y.toNat, StronglyMeasurable[enlFilt p m n]
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)) := by
      intro u hu
      exact stronglyMeasurable_indicator_hof_le_record (N := N) (p := p) hp m n j u
        (k := y) (by
          have hu' : u < y.toNat := Finset.mem_range.mp hu
          have h1 : ((u : ℕ) : ℤ) < ((y.toNat : ℕ) : ℤ) := by exact_mod_cast hu'
          rwa [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ y)] at h1)
    have hsum' := Finset.stronglyMeasurable_sum (Finset.range y.toNat) hterm
    have hfun : (fun U : Array N => ∑ u ∈ Finset.range y.toNat,
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)) U)
        = ∑ u ∈ Finset.range y.toNat, fun U : Array N =>
            ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
              (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)) U := by
      funext U
      simp only [Finset.sum_apply]
    rw [hfun]
    exact hsum'

/-! ### 3. `E[H_j(r_n) | F_n] = H_j(r_n)` -/

/-- **The potential at the record is already revealed.** -/
theorem condExp_Hpot_record {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
          (recVal j (prefOf p m n U)))
      =ᵐ[arrayMeasure N]
        fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
          (recVal j (prefOf p m n U)) :=
  Filter.EventuallyEq.of_eq
    (condExp_of_stronglyMeasurable ((enlFilt (N := N) p m).le n)
      (measurable_Hpot_record_enlFilt hp1.le m n j).stronglyMeasurable
      (integrable_Hpot_record hp1 hp2 m n j))

/-! ### 4. The paper's `x ≤ r_n` identity, sitewise -/

/-- **`H_{j,n}(x) = H_j(x)` on `{x ≤ r_n}`**, in the sitewise form: for a fixed site `y`, on the
`F_n`-measurable piece where `y ≤ M_n^j`, the projection at `y` is the revealed value. -/
theorem projH_eq_Hpot_of_le_record {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (j : Fin N) (y : ℤ) :
    ∀ᵐ U ∂(arrayMeasure N), y ≤ recVal j (prefOf p m n U) →
      projH p m j n U y = SwarmOcc.Hpot (siteH p m j U) y := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hidxA : Measurable (fun U : Array N => recVal j (prefOf p m n U)) := by
    have h := (measurable_runMax_enl (N := N) p m n j).mono
      ((enlFilt (N := N) p m).le n) le_rfl
    simpa only [runMax_eq_recVal] using h
  have hAmeas : MeasurableSet {U : Array N | y ≤ recVal j (prefOf p m n U)} :=
    measurableSet_le measurable_const hidxA
  have hgint : Integrable (fun V : Array N => SwarmOcc.Hpot (siteH p m j V) y) (arrayMeasure N) :=
    integrable_Hpot_site hp1 hp2 hpne m j y
  have htruncInt : Integrable
      ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
        (fun V => SwarmOcc.Hpot (siteH p m j V) y)) (arrayMeasure N) :=
    hgint.indicator hAmeas
  have hfix : condExp (enlFilt p m n) (arrayMeasure N)
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun V => SwarmOcc.Hpot (siteH p m j V) y))
      =ᵐ[arrayMeasure N]
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun V => SwarmOcc.Hpot (siteH p m j V) y)) :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((enlFilt (N := N) p m).le n)
      (stronglyMeasurable_indicator_Hpot_le_record hp1.le m n j y) htruncInt)
  have hind : condExp (enlFilt p m n) (arrayMeasure N)
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun V => SwarmOcc.Hpot (siteH p m j V) y))
      =ᵐ[arrayMeasure N]
        ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (condExp (enlFilt p m n) (arrayMeasure N)
            (fun V => SwarmOcc.Hpot (siteH p m j V) y))) :=
    condExp_indicator hgint (measurableSet_le_record p m n j y)
  filter_upwards [hfix, hind] with U h1 h2 hU
  have hmem : U ∈ {U : Array N | y ≤ recVal j (prefOf p m n U)} := hU
  have h3 : (SwarmOcc.Hpot (siteH p m j U) y) = projH p m j n U y := by
    have h4 : ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
        (condExp (enlFilt p m n) (arrayMeasure N)
          (fun V => SwarmOcc.Hpot (siteH p m j V) y))) U
        = ({U : Array N | y ≤ recVal j (prefOf p m n U)}.indicator
          (fun V => SwarmOcc.Hpot (siteH p m j V) y)) U := by
      rw [← h2, h1]
    simpa only [Set.indicator_of_mem hmem, projH] using h4.symm
  exact h3.symm

/-! ### 5. The paper's `(projH)` above-record closed form, sitewise -/

/-- The potential at the shifted record `M_n^j + g` is integrable (from the record decomposition). -/
theorem integrable_Hpot_record_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (g : ℕ) :
    Integrable (fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U) + (g : ℤ))) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hRec : Integrable (fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))) (arrayMeasure N) :=
    integrable_Hpot_record hp1 hp2 m n j
  have hSum : Integrable (fun U : Array N => ∑ k ∈ Finset.range g,
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((recVal j (prefOf p m n U)).toNat + k)) (arrayMeasure N) := by
    have h := integrable_finsetSum' (Finset.range g) (fun k _ =>
      integrable_hof_siteMarks_add hp1 hp2 m n j k)
    refine h.congr (Filter.Eventually.of_forall fun U => ?_)
    simp only [Finset.sum_apply]
  refine (hRec.add hSum).congr (Filter.Eventually.of_forall fun U => ?_)
  simp only [Pi.add_apply]
  exact (Hpot_record_add p m n j g U).symm

/-- The record-level set `{y = M_n^j + g}` is `enlFilt n`-measurable. -/
lemma measurableSet_record_eq_add (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℤ) (g : ℕ) :
    MeasurableSet[enlFilt p m n] {U : Array N | y = recVal j (prefOf p m n U) + (g : ℤ)} := by
  refine measurableSet_eq_fun measurable_const ?_
  have h : Measurable[enlFilt p m n] (fun U : Array N => recVal j (prefOf p m n U)) := by
    have h' := measurable_runMax_enl (N := N) p m n j
    simpa only [runMax_eq_recVal] using h'
  exact h.add_const (g : ℤ)

/-- **The paper's `(projH)`, sitewise, at the actual random record.**

For a fixed site `y` and shift `g`, on the `enlFilt n`-measurable piece `{y = M_n^j + g}` the
projected potential at `y` is the paper's closed form

    H_{j,n}(r_n + g) = H_j(r_n) + g (1+a)/(1-a)
                       + (e_0 - (1+a)/(1-a)) (1-a^g)/(1-a),

with `e_0 = E[h_j(r_n)|F_n]` (`eRec p m n j 0`).  This is exactly the paper's display `(projH)`:
the base value is the *quenched* `H_j(r_n)`, not its projection, because every site at or below
the record is revealed (`condExp_Hpot_record`). -/
theorem projH_closed_form_piece {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), y = recVal j (prefOf p m n U) + (g : ℤ) →
      projH p m j n U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  set L : ℝ := (1 + aRec p m) / (1 - aRec p m) with hL
  set A : Set (Array N) := {U : Array N | y = recVal j (prefOf p m n U) + (g : ℤ)} with hAdef
  have hAenl : MeasurableSet[enlFilt p m n] A := measurableSet_record_eq_add p m n j y g
  have hAamb : MeasurableSet A := (enlFilt (N := N) p m).le n A hAenl
  -- integrability of the two potentials involved
  have hIntY : Integrable (fun V : Array N => SwarmOcc.Hpot (siteH p m j V) y) (arrayMeasure N) :=
    integrable_Hpot_site hp1 hp2 hpne m j y
  have hIntAdd : Integrable (fun V : Array N =>
      SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ))) (arrayMeasure N) :=
    integrable_Hpot_record_add hp1 hp2 m j g
  -- step 1: `1_A H_{j,n}(·,y) = 1_A E[H_j(y)|F_n]`
  have h1 : A.indicator (fun U : Array N => projH p m j n U y)
      =ᵐ[arrayMeasure N] A.indicator (condExp (enlFilt p m n) (arrayMeasure N)
        (fun V => SwarmOcc.Hpot (siteH p m j V) y)) :=
    Filter.EventuallyEq.of_eq rfl
  -- step 2: pull the `F_n`-measurable indicator inside
  have h2 : A.indicator (condExp (enlFilt p m n) (arrayMeasure N)
        (fun V => SwarmOcc.Hpot (siteH p m j V) y))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (A.indicator (fun V => SwarmOcc.Hpot (siteH p m j V) y)) :=
    (condExp_indicator hIntY hAenl).symm
  -- step 3: on `A`, the site `y` is the shifted record
  have h3 : A.indicator (fun V => SwarmOcc.Hpot (siteH p m j V) y)
      = A.indicator (fun V =>
          SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ))) := by
    funext U
    by_cases hU : U ∈ A
    · have hUy : y = recVal j (prefOf p m n U) + (g : ℤ) := hU
      simp only [Set.indicator_of_mem hU, hUy]
    · simp only [Set.indicator_of_notMem hU]
  -- step 4: pull out again (now for the shifted-record potential)
  have h4 : condExp (enlFilt p m n) (arrayMeasure N)
        (A.indicator (fun V =>
          SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ))))
      =ᵐ[arrayMeasure N] A.indicator (condExp (enlFilt p m n) (arrayMeasure N)
        (fun V => SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ)))) :=
    condExp_indicator hIntAdd hAenl
  -- step 5: the summed projected potential, with the quenched base value and the closed form
  have h5 : condExp (enlFilt p m n) (arrayMeasure N)
        (fun V => SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ)))
      =ᵐ[arrayMeasure N] fun U => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
    refine (condExp_Hpot_record_add hp1 hp2 m (n := n) j g).trans ?_
    filter_upwards [condExp_Hpot_record (p := p) hp1 hp2 m (n := n) j] with U hU
    rw [hU, eRec_partial_sum p m n j (aRec_ne_one hp1 hp2 m) g U]
    have hsite : SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
        = SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
            (recVal j (prefOf p m n U)) := rfl
    rw [hsite]
    ring
  have hchain : A.indicator (fun U : Array N => projH p m j n U y)
      =ᵐ[arrayMeasure N] A.indicator (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m))) := by
    have h4' : condExp (enlFilt p m n) (arrayMeasure N)
          (A.indicator (fun V =>
            SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ))))
        =ᵐ[arrayMeasure N] A.indicator (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m))) := by
      refine h4.trans ?_
      filter_upwards [h5] with U hU
      by_cases h : U ∈ A
      · simp only [Set.indicator_of_mem h, hU]
      · simp only [Set.indicator_of_notMem h]
    have h23 : A.indicator (condExp (enlFilt p m n) (arrayMeasure N)
          (fun V => SwarmOcc.Hpot (siteH p m j V) y))
        =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          (A.indicator (fun V =>
            SwarmOcc.Hpot (siteH p m j V) (recVal j (prefOf p m n V) + (g : ℤ)))) :=
      h2.trans (Filter.EventuallyEq.of_eq (by rw [h3]))
    exact (h1.trans h23).trans h4'
  filter_upwards [hchain] with U hU hUA
  have hmem : U ∈ A := hUA
  have hleft : (A.indicator (fun U : Array N => projH p m j n U y)) U = projH p m j n U y :=
    Set.indicator_of_mem hmem _
  have hright : (A.indicator (fun U : Array N => SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
        + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ g) / (1 - aRec p m)))) U
      = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
        + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ g) / (1 - aRec p m)) :=
    Set.indicator_of_mem hmem _
  rw [← hleft, ← hright]
  exact hU

/-! ### 6. The two cases at the walker's own position -/

/-- **The paper's `x ≤ r_n` identity for all sites simultaneously.** -/
theorem ae_forall_projH_eq_Hpot_of_le_record {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ, y ≤ recVal j (prefOf p m n U) →
      projH p m j n U y = SwarmOcc.Hpot (siteH p m j U) y :=
  MeasureTheory.ae_all_iff.mpr fun y => projH_eq_Hpot_of_le_record hp1 hp2 hpne m n j y

/-- **The paper's `(projH)` for all sites above the record simultaneously.** -/
theorem ae_forall_projH_closed_form {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ (y : ℤ) (g : ℕ),
      y = recVal j (prefOf p m n U) + (g : ℤ) →
      projH p m j n U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)) :=
  MeasureTheory.ae_all_iff.mpr fun y =>
    MeasureTheory.ae_all_iff.mpr fun g => projH_closed_form_piece hp1 hp2 m j y g

/-- `e_0 ≤ b_n` for the actual record. -/
theorem eRec_zero_le_bRec' {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) :
    eRec p m n j 0 ≤ᵐ[arrayMeasure N] bRec p m n j :=
  eRec_zero_le_bRec hp1 hp2 m (n := n) j (measurable_HprevAt_enlFilt hp1.le m n j)

/-- **The paper's `(Vbound)` ingredient at the walker's own position (above-record case).**

For `X_n^i > r_n` the projected potential is at most the quenched record value plus the drift
slope times the distance plus the record cost `b_n/(1-a)`:

    H_{j,n}(X_n^i) ≤ H_j(r_n) + (X_n^i - r_n) (1+a)/(1-a) + b_n/(1-a).

This is the display used at `(Vbound)` (`r_n ≤ n`, `b_n = O(log n)`, `H_j(r_n)/r_n → (1+a)/(1-a)`),
now with the quenched base value `H_j(r_n)`. -/
theorem projH_pos_above_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), recVal j (prefOf p m n U) < (trajectory p m U n).pos i →
      projH p m j n U ((trajectory p m U n).pos i)
        ≤ SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (((trajectory p m U n).pos i - recVal j (prefOf p m n U) : ℤ) : ℝ)
              * ((1 + aRec p m) / (1 - aRec p m))
          + bRec p m n j U / (1 - aRec p m) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have hden : (0 : ℝ) < 1 - aRec p m := by linarith
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    eRec_zero_le_bRec' (p := p) hp1 hp2 m (n := n) j] with U hcl hb
  intro hgt
  set r := recVal j (prefOf p m n U) with hr
  set X := (trajectory p m U n).pos i with hX
  have hg : 0 < X - r := by omega
  obtain ⟨g, hgk⟩ : ∃ g : ℕ, (g : ℤ) = X - r :=
    ⟨(X - r).toNat, by rw [Int.toNat_of_nonneg (le_of_lt hg)]⟩
  have hXeq : X = r + (g : ℤ) := by omega
  have hform := hcl X g hXeq
  rw [hform]
  -- bound the correction term
  -- the correction term is bounded by `b_n/(1-a)`
  have hstep : (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
        * ((1 - aRec p m ^ g) / (1 - aRec p m))
      ≤ bRec p m n j U / (1 - aRec p m) := by
    set Lc : ℝ := (1 + aRec p m) / (1 - aRec p m) with hLc
    set F : ℝ := (1 - aRec p m ^ g) / (1 - aRec p m) with hF
    have hLpos : 0 < Lc := by
      rw [hLc]; positivity
    have hF0 : 0 ≤ F := by
      rw [hF, div_eq_mul_inv]
      refine mul_nonneg ?_ (by positivity)
      have : aRec p m ^ g ≤ 1 := pow_le_one₀ ha0 (le_of_lt ha1)
      linarith
    have hF1 : F ≤ 1 / (1 - aRec p m) := by
      rw [hF, div_eq_mul_inv]
      have h1 : 1 - aRec p m ^ g ≤ 1 := by
        have : (0:ℝ) ≤ aRec p m ^ g := pow_nonneg ha0 g
        linarith
      have h2 : (0:ℝ) ≤ (1 - aRec p m)⁻¹ := by positivity
      calc (1 - aRec p m ^ g) * (1 - aRec p m)⁻¹ ≤ 1 * (1 - aRec p m)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = 1 / (1 - aRec p m) := by rw [one_mul, one_div]
    have hB0 : 0 ≤ bRec p m n j U := by linarith [three_le_bRec hp1 hp2 m n j U]
    by_cases he : 0 ≤ eRec p m n j 0 U - Lc
    · have h1 : (eRec p m n j 0 U - Lc) * F ≤ (bRec p m n j U - Lc) * F :=
        mul_le_mul_of_nonneg_right (by linarith) hF0
      have h2 : (bRec p m n j U - Lc) * F ≤ bRec p m n j U * F := by
        have : (-Lc) * F ≤ 0 := by
          have := mul_nonneg (le_of_lt hLpos) hF0
          linarith
        nlinarith
      have h3 : bRec p m n j U * F ≤ bRec p m n j U * (1 / (1 - aRec p m)) :=
        mul_le_mul_of_nonneg_left hF1 hB0
      have h4 : bRec p m n j U * (1 / (1 - aRec p m)) = bRec p m n j U / (1 - aRec p m) := by
        rw [one_div, div_eq_mul_inv]
      rw [hLc, hF] at h1 h2
      rw [hF] at h3
      rw [hLc, hF]
      linarith
    · have h1 : (eRec p m n j 0 U - Lc) * F ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp he)) hF0
      have h3 : 0 ≤ bRec p m n j U / (1 - aRec p m) := div_nonneg hB0 hden.le
      rw [hLc, hF] at h1 ⊢
      linarith
  have hcast : (((X - r : ℤ)) : ℝ) = (g : ℝ) := by
    rw [← hgk]
    push_cast
    ring
  calc SwarmOcc.Hpot (siteH p m j U) r + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ g) / (1 - aRec p m))
      ≤ SwarmOcc.Hpot (siteH p m j U) r + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + bRec p m n j U / (1 - aRec p m) := by linarith
    _ = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
          + (((trajectory p m U n).pos i - recVal j (prefOf p m n U) : ℤ) : ℝ)
              * ((1 + aRec p m) / (1 - aRec p m))
          + bRec p m n j U / (1 - aRec p m) := by
        have hsub : ((trajectory p m U n).pos i - recVal j (prefOf p m n U) : ℤ) = (g : ℤ) := by
          rw [hr, hX] at hgk
          exact hgk.symm
        rw [hsub, ← hr]
        push_cast
        ring

/-- **The paper's `(Vbound)` ingredient at the walker's own position, both cases.**

At the walker's position the projected potential is at most the better of the revealed value
(at or below the record) and the above-record drift bound. -/
theorem projH_pos_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      projH p m j n U ((trajectory p m U n).pos i)
        ≤ max (SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i))
            (SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U))
              + (((trajectory p m U n).pos i - recVal j (prefOf p m n U) : ℤ) : ℝ)
                  * ((1 + aRec p m) / (1 - aRec p m))
              + bRec p m n j U / (1 - aRec p m)) := by
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (p := p) hp1 hp2 (by linarith) m n j,
    projH_pos_above_le (p := p) hp1 hp2 m (n := n) i j] with U hbelow habove
  by_cases h : (trajectory p m U n).pos i ≤ recVal j (prefOf p m n U)
  · rw [hbelow _ h]
    exact le_max_left _ _
  · have h' : recVal j (prefOf p m n U) < (trajectory p m U n).pos i := not_le.mp h
    exact le_trans (habove h') (le_max_right _ _)

/-! ### 7. The paper's increment identity in the no-advance case -/

/-- **The paper's `(projH)` increment identity when the record does not move.**

If `M_{n+1}^j = M_n^j` and `y = M_n^j + g` with `g ≥ 0`, then evaluating `(projH)` at the two
times gives

    H_{j,n+1}(y) - H_{j,n}(y)
      = (E[h_j(M_n^j)|F_{n+1}] - E[h_j(M_n^j)|F_n]) (1-a^g)/(1-a),

the paper's display in the case `r_{n+1} = r_n`.  Here `E[h_j(M_n^j)|F_{n+1}] = eRec n+1 0` is
legitimate exactly because `M_{n+1}^j = M_n^j`.  The remaining (record-advancing) case needs the
conditional independence of the fresh mark at the *new* record given `F_{n+1}`; it is not proved
here. -/
theorem projH_increment_no_advance {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      recVal j (prefOf p m n U) = recVal j (prefOf p m (n + 1) U) →
      y = recVal j (prefOf p m n U) + (g : ℤ) →
      projH p m j (n + 1) U y - projH p m j n U y
        = (eRec p m (n + 1) j 0 U - eRec p m n j 0 U)
            * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  filter_upwards [ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n) j,
    ae_forall_projH_closed_form (p := p) hp1 hp2 m (n := n + 1) j] with U hcln hcln1 hsame hy
  have h1 := hcln y g hy
  have hy' : y = recVal j (prefOf p m (n + 1) U) + (g : ℤ) := by rw [← hsame]; exact hy
  have h2 := hcln1 y g hy'
  have hHpot : SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m (n + 1) U))
      = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m n U)) := by rw [hsame]
  rw [h2, h1, hHpot]
  ring

theorem eRec_zero_bounds_ae {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), 1 ≤ eRec p m n j 0 U ∧ eRec p m n j 0 U ≤ bRec p m n j U := by
  filter_upwards [one_le_eRec_zero hp1 hp2 m (n := n) j, eRec_zero_le_bRec' (p := p) hp1 hp2 m
    (n := n) j] with U h1 h2
  exact ⟨h1, h2⟩

/-- **The paper's increment bound when the record does not move**:
`|H_{j,n+1}(y) - H_{j,n}(y)| ≤ b_n/(1-a)` for `y = M_n^j + g` with `M_{n+1}^j = M_n^j`. -/
theorem abs_projH_increment_no_advance_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (y : ℤ) (g : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) →
      y = recVal j (prefOf p m n U) + (g : ℤ) →
      |projH p m j (n + 1) U y - projH p m j n U y| ≤ bRec p m n j U / (1 - aRec p m) := by
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have hden : (0 : ℝ) < 1 - aRec p m := by linarith
  filter_upwards [projH_increment_no_advance (p := p) hp1 hp2 m j y g,
    eRec_zero_bounds_ae (p := p) hp1 hp2 m (n := n) j,
    eRec_zero_bounds_ae (p := p) hp1 hp2 m (n := n + 1) j] with U hid hb hb'
  intro hsame hy
  have hb1 := hb.1
  have hb2 := hb.2
  have hb1' := hb'.1
  have hb2' := hb'.2
  have hb'eq : bRec p m (n + 1) j U = bRec p m n j U := by
    simp only [bRec, HprevAt, ← hsame]
  rw [hb'eq] at hb2'
  rw [hid hsame.symm hy]
  have hF0 : 0 ≤ (1 - aRec p m ^ g) / (1 - aRec p m) := by
    have h : aRec p m ^ g ≤ 1 := pow_le_one₀ ha0 (le_of_lt ha1)
    exact div_nonneg (by linarith) hden.le
  have hFK : (1 - aRec p m ^ g) / (1 - aRec p m) ≤ 1 / (1 - aRec p m) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (0:ℝ) ≤ aRec p m ^ g := pow_nonneg ha0 g
    linarith
  rw [abs_mul]
  have hdiff : |eRec p m (n + 1) j 0 U - eRec p m n j 0 U| ≤ bRec p m n j U := by
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  have hbn : 0 ≤ bRec p m n j U := by linarith [three_le_bRec hp1 hp2 m n j U]
  calc |eRec p m (n + 1) j 0 U - eRec p m n j 0 U|
        * |(1 - aRec p m ^ g) / (1 - aRec p m)|
      = |eRec p m (n + 1) j 0 U - eRec p m n j 0 U|
        * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by rw [abs_of_nonneg hF0]
    _ ≤ bRec p m n j U * (1 / (1 - aRec p m)) :=
        mul_le_mul hdiff hFK hF0 (by positivity)
    _ = bRec p m n j U / (1 - aRec p m) := by rw [one_div, div_eq_mul_inv]


/-! ### Axiom audit -/


