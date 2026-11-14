/-
  # Raw record-fibre summation for the single-window occupation event

  `LocOccSingleWindow.measureReal_recordCarrier_singleWindow_le` bounds, *at a fixed record fibre*
  `s0`, the mass of `recordPrefixBand p m r s0 L ∩ (GoodWin ... s0)ᶜ` by four raw pieces

  * `2 * exp (-c * xOf Lw)`                     (`LsBad` twice: directly and through `OscSup`),
  * `mu.real (band s0) * envQ`                  (carrier-weighted `Qpl` Azuma),
  * `mu.real (band s0 ∩ harmDefect ...)`        (the harmonic `(locmax)` defect),
  * `Lw * (mu.real (band s0) * envOsc)`         (`Lw`-carrier-weighted projected Azuma).

  Summing that *already normalised* bound over `s0` diverges, because the first term carries no
  carrier factor.  This file sums the raw pieces instead:

  * the record bands `recordPrefixBand p m r s0 L` are pairwise disjoint and measurable, so
    `∑_{s0 ∈ S} mu.real (band s0) = mu.real (⋃_{s0 ∈ S} band s0)`;
  * consequently the two `s0`-independent defective sets (`LsBad` and `harmDefect`) are charged
    exactly once: `∑_{s0 ∈ S} mu.real (band s0 ∩ D) = mu.real ((⋃_{s0∈S} band s0) ∩ D)`.

  The main results are the finite sum (`measureReal_finset_iUnion_band_inter_goodWin_compl_le`)
  and the countable sum (`measureReal_iUnion_band_inter_goodWin_compl_le`) over the exact fibre
  union `⋃_{s0} (band s0 ∩ (GoodWin s0)ᶜ)`; both have the same three-mass raw form as the per-fibre
  theorem with the single fibre replaced by the total record carrier `⋃_{s0} band s0`.
  Measurability of `LsBad` and of `harmDefect` are the only measurability inputs beyond
  `measurableSet_recordPrefixBand`; `harmDefect` is discharged unconditionally here
  (`measurableSet_harmDefect`), `LsBad` stays an explicit hypothesis of the summation theorems
  (`hLsMeas`).

  Sections 8–9 do supply the paper-scale (`exp (-c_T L^{1/16})`) collapse for one fixed
  ordered pair. The `LsBad` rate and measurability inputs remain explicit there; harmonic-defect
  measurability can be supplied by `measurableSet_Harm`.
  Not claimed here: the identification of `⋃_{s0} band s0` with `{d_r ≤ L}` (the separate
  `LocOccRecordFibres` result requires `ReachAll`), any all-pairs/`N`-factor statement,
  any non-vacuity, and any unconditional `locmart` statement.
-/
import Swarm.LocOccSingleWindow
import Swarm.CarrierQplResidual
import Swarm.LocOccCarrierAssembly

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal BigOperators Topology

namespace LocOccFibreSum

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 0. The raw pieces of the single-window estimate, as abbreviations -/

/-- The record fibre `s0`: the first hitting time of level `r` together with its defect band. -/
abbrev band (p : ℝ) (m r L : ℕ) (s0 : ℕ) : Set (Array N) :=
  ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L

/-- The `s0`-independent `(locsum)`/`(locmax)` defect of the single-window estimate. -/
abbrev LsBad (p : ℝ) (m : ℕ) (C : ℝ) (r T L : ℕ) : Set (Array N) :=
  LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)

/-- The adapted projected `Qpl` drop over the paper's *single* window `[s0, s0 + T L]`. -/
abbrev Qdrop (p : ℝ) (m : ℕ) (i j : Fin N) (T L : ℕ) (s0 : ℕ) : Set (Array N) :=
  LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L) (2 * L34 L (Lw T L))

/-- The start-indexed projected-oscillation event at the record carrier. -/
abbrev OscS (p : ℝ) (m : ℕ) (j : Fin N) (r T L s0 : ℕ) : Set (Array N) :=
  OscSup p m j r T L s0

/-- The harmonic `(locmax)` defect on the carrier site window (independent of the record time). -/
abbrev Harm (p : ℝ) (m : ℕ) (j : Fin N) (V : ℝ) (r T L : ℕ) : Set (Array N) :=
  QplWindow.harmDefect p m j V (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L)

/-- The `Qpl` Azuma factor multiplying the carrier mass. -/
noncomputable abbrev envQ (p : ℝ) (m : ℕ) (V : ℝ) (T L : ℕ) : ℝ :=
  2 * (((T * L : ℕ) : ℝ) + 1) *
    Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
      (4 * ((T * L : ℕ) : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))

/-- The projected-oscillation Azuma factor multiplying `Lw` times the carrier mass. -/
noncomputable abbrev envOsc (p : ℝ) (m : ℕ) (T L : ℕ) : ℝ :=
  2 * (((T * L : ℕ) : ℝ) + 1) *
    Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
      (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))

/-! ### 1. Generic bookkeeping: finite/countable unions and real monotone convergence -/

theorem monotone_biUnion_range {α : Type*} (f : ℕ → Set α) :
    Monotone fun n => ⋃ s0 ∈ Finset.range n, f s0 := by
  intro n m hnm U hU
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hU ⊢
  obtain ⟨s0, hs0, h⟩ := hU
  exact ⟨s0, lt_of_lt_of_le hs0 hnm, h⟩

theorem iUnion_range_biUnion {α : Type*} (f : ℕ → Set α) :
    (⋃ n, ⋃ s0 ∈ Finset.range n, f s0) = ⋃ s0, f s0 := by
  ext U
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨n, s0, hs0, hU⟩
    exact ⟨s0, hU⟩
  · rintro ⟨s0, hU⟩
    exact ⟨s0 + 1, s0, Nat.lt_succ_self s0, hU⟩

theorem biUnion_finset_inter {α : Type*} (f : ℕ → Set α) (t : Set α) (S : Finset ℕ) :
    (⋃ s0 ∈ S, f s0) ∩ t = ⋃ s0 ∈ S, f s0 ∩ t := by
  ext U
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨s0, hs0, h1⟩, h2⟩
    exact ⟨s0, hs0, h1, h2⟩
  · rintro ⟨s0, hs0, h1, h2⟩
    exact ⟨⟨s0, hs0, h1⟩, h2⟩

/-- Real-valued monotone convergence of measures along an increasing family. -/
theorem tendsto_measureReal_iUnion_atTop (f : ℕ → Set (Array N)) (hmono : Monotone f) :
    Tendsto (fun n => (arrayMeasure N).real (f n)) atTop
      (𝓝 ((arrayMeasure N).real (⋃ n, f n))) := by
  have hne : (arrayMeasure N) (⋃ n, f n) ≠ ∞ := measure_ne_top _ _
  have h1 : Tendsto (fun n => (arrayMeasure N) (f n)) atTop
      (𝓝 ((arrayMeasure N) (⋃ n, f n))) := tendsto_measure_iUnion_atTop hmono
  have h2 : Tendsto (fun a : ℝ≥0∞ => a.toReal) (𝓝 ((arrayMeasure N) (⋃ n, f n)))
      (𝓝 ((arrayMeasure N) (⋃ n, f n)).toReal) := ENNReal.tendsto_toReal hne
  simpa only [Measure.real_def, Function.comp_def] using h2.comp h1

/-- Disjoint finite sums of a measurable family: the fibre masses add up to the mass of the
finite union. -/
theorem measureReal_biUnion_finset_eq_sum {f : ℕ → Set (Array N)}
    (hmeas : ∀ s0, MeasurableSet (f s0))
    (hdisj : ∀ ⦃a b : ℕ⦄, a ≠ b → Disjoint (f a) (f b)) (S : Finset ℕ) :
    (arrayMeasure N).real (⋃ s0 ∈ S, f s0)
      = ∑ s0 ∈ S, (arrayMeasure N).real (f s0) := by
  have hunion : (⋃ s0 ∈ S, f s0) = ⋃ s0 : {x // x ∈ S}, f s0 := by
    ext U
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s0, hs0, hU⟩
      exact ⟨⟨s0, hs0⟩, hU⟩
    · rintro ⟨⟨s0, hs0⟩, hU⟩
      exact ⟨s0, hs0, hU⟩
  have hmain := measureReal_iUnion_fintype (μ := arrayMeasure N)
    (f := fun s0 : {x // x ∈ S} => f (s0 : ℕ))
    (fun a b hab => hdisj (fun h => hab (Subtype.ext h)))
    (fun i => hmeas i) (fun i => measure_ne_top _ _)
  rw [hunion, hmain, Finset.sum_coe_sort S (fun s0 => (arrayMeasure N).real (f s0))]

/-- `∑ c * (a s0 * e) = c * ((∑ a s0) * e)`. -/
theorem sum_const_mul (S : Finset ℕ) (a : ℕ → ℝ) (c e : ℝ) :
    ∑ s0 ∈ S, c * (a s0 * e) = c * ((∑ s0 ∈ S, a s0) * e) := by
  rw [← Finset.mul_sum, Finset.sum_mul]

/-! ### 2. The record fibres: disjoint, measurable -/

theorem measurableSet_band {p : ℝ} {m r L : ℕ} {s0 : ℕ} :
    MeasurableSet (band (N := N) p m r L s0) :=
  (enlFilt (N := N) p m).le s0 _
    (ActualRecordFiltration.measurableSet_recordPrefixBand (N := N) p m r s0 L)

/-- Two distinct record times cannot both be first hits of level `r`: the fibres are disjoint.
(The same statement is proved in `LocOccRecordFibres`; re-derived here so that the summation does
not depend on that module.) -/
theorem band_disjoint {p : ℝ} {m r L : ℕ} {s0 s0' : ℕ} (h : s0 ≠ s0') :
    Disjoint (band (N := N) p m r L s0) (band (N := N) p m r L s0') := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro U hU
  have h1 : U ∈ ActualRecordFiltration.firstRecordAt p m r s0 := hU.1.1
  have h2 : U ∈ ActualRecordFiltration.firstRecordAt p m r s0' := hU.2.1
  have h1' : runMax (actX p m U) s0 = (r : ℤ) ∧
      ∀ t < s0, runMax (actX p m U) t ≠ (r : ℤ) := h1
  have h2' : runMax (actX p m U) s0' = (r : ℤ) ∧
      ∀ t < s0', runMax (actX p m U) t ≠ (r : ℤ) := h2
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact h2'.2 s0 hlt h1'.1
  · exact h1'.2 s0' hlt h2'.1

theorem measureReal_biUnion_band_eq_sum {p : ℝ} {m r L : ℕ} (S : Finset ℕ) :
    (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0)
      = ∑ s0 ∈ S, (arrayMeasure N).real (band p m r L s0) :=
  measureReal_biUnion_finset_eq_sum (f := fun s0 => band (N := N) p m r L s0)
    (fun s0 => measurableSet_band (N := N) (s0 := s0))
    (fun a b hab => band_disjoint (p := p) (m := m) (r := r) (L := L) (N := N) hab) S

theorem measureReal_biUnion_band_inter_eq_sum {p : ℝ} {m r L : ℕ} {t : Set (Array N)}
    (hmeas : MeasurableSet t) (S : Finset ℕ) :
    (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0 ∩ t)
      = ∑ s0 ∈ S, (arrayMeasure N).real (band p m r L s0 ∩ t) :=
  measureReal_biUnion_finset_eq_sum
    (f := fun s0 => band (N := N) p m r L s0 ∩ t)
    (fun s0 => (measurableSet_band (N := N) (s0 := s0)).inter hmeas)
    (fun a b hab => Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (band_disjoint (p := p) (m := m) (r := r) (L := L) (N := N) hab)) S

/-! ### 3. Measurability and the once-charged mass of the harmonic defect -/

/-- The harmonic `(locmax)` defect is a finite union of measurable events. -/
theorem measurableSet_harmDefect {p : ℝ} {m : ℕ} {j : Fin N} (V : ℝ) (A M : ℕ) :
    MeasurableSet (QplWindow.harmDefect p m j V A M) := by
  have hset : QplWindow.harmDefect p m j V A M
      = ⋃ y ∈ Finset.Ico (A - 1) (A + M),
          {U : Array N | V < hof p (siteMarks p m U j) y} := by
    ext U
    simp only [QplWindow.harmDefect, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop,
      Finset.mem_Ico, not_forall, not_le]
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun y _ =>
    measurableSet_lt measurable_const (Swarming.Enl.measurable_hof_siteMarks p m j y))

theorem measurableSet_Harm {p : ℝ} {m : ℕ} {j : Fin N} {V : ℝ} {r T L : ℕ} :
    MeasurableSet (Harm (N := N) p m j V r T L) :=
  measurableSet_harmDefect (N := N) V (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L)

/-- **The harmonic defect charged once.**  It is contained in the capped wide `(locmax)` event
estimated by `WideRepair.array_locmax_bound_paper_window`: no carrier factor, no reference to the
record time. -/
theorem measureReal_harmDefect_le_exp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r : ℕ} {j : Fin N}, (T + 3) * L ≤ r →
      (arrayMeasure N).real (Harm p m j (xOf (Lw T L)) r T L) ≤
        Real.exp (-c * xOf (Lw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ :=
    WideRepair.array_locmax_bound_paper_window (N := N) (p := p) hp1 hp2 hm T hT
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL r j hr
  have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper (T := T) (L := L) (r := r) hT hL1 hr
  have hMU : 1 + CarrierQplResidual.cM T L ≤ 2 * (T + 3) * CarrierQplResidual.cLw T L := by
    unfold CarrierQplResidual.cM CarrierQplResidual.cLw
    have h1 : (2 * T + 2) * L + 3 ≤ 4 * ((2 * T + 2) * L + 1) := by omega
    have h2 : 4 ≤ 2 * (T + 3) := by omega
    have h3 : 4 * ((2 * T + 2) * L + 1) ≤ 2 * (T + 3) * ((2 * T + 2) * L + 1) :=
      Nat.mul_le_mul_right _ h2
    have h4 : 1 + ((2 * T + 2) * L + 2) = (2 * T + 2) * L + 3 := by omega
    rw [h4]
    exact le_trans h1 h3
  have hL' : L₀ ≤ CarrierQplResidual.cLw T L := by
    have hlen : L ≤ (2 * T + 2) * L := Nat.le_mul_of_pos_left L (by omega)
    unfold CarrierQplResidual.cLw
    omega
  have hbnd := hb (CarrierQplResidual.cLw T L) hL' (CarrierQplResidual.cA r T L) 1
    (CarrierQplResidual.cM T L) hA1 hMU
  have hmono : (arrayMeasure N) (Harm p m j (xOf (Lw T L)) r T L) ≤
      (arrayMeasure N) {U : Array N | WideRepair.HMaxBadW p m (CarrierQplResidual.cLw T L) 1
        (CarrierQplResidual.cM T L) (CarrierQplResidual.cA r T L) U} := by
    refine measure_mono fun U hU => ?_
    exact CarrierQplResidual.harmDefect_subset_HMaxBadW hU
  have hexp : Real.exp (-c * xOf (CarrierQplResidual.cLw T L)) =
      Real.exp (-c * xOf (Lw T L)) := by
    rw [show CarrierQplResidual.cLw T L = Lw T L from rfl]
  calc (arrayMeasure N).real (Harm p m j (xOf (Lw T L)) r T L)
      = ((arrayMeasure N) (Harm p m j (xOf (Lw T L)) r T L)).toReal := Measure.real_def _ _
    _ ≤ ((arrayMeasure N) {U : Array N | WideRepair.HMaxBadW p m (CarrierQplResidual.cLw T L) 1
          (CarrierQplResidual.cM T L) (CarrierQplResidual.cA r T L) U}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ (ENNReal.ofReal (Real.exp (-c * xOf (CarrierQplResidual.cLw T L)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    _ = Real.exp (-c * xOf (Lw T L)) := by
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hexp]

/-! ### 4. The per-fibre raw pieces -/

theorem measureReal_band_inter_qplDrop_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V) :
    (arrayMeasure N).real (band p m r L s0 ∩ Qdrop p m i j T L s0) ≤
      (arrayMeasure N).real (band p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real (band p m r L s0 ∩ Harm p m j V r T L) := by
  have hTL1 : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper (T := T) (L := L) (r := r) hT hL hr
  have hL34pos : 0 < L34 L (Lw T L) :=
    lt_of_lt_of_le zero_lt_one (one_le_L34 (L := L) (Lw := Lw T L) hL)
  exact CarrierQplResidual.measureReal_recordCarrier_qplDrop_singleResidual (N := N) hp1 hp2 m
    (1 / 8) i j (by norm_num) (r := r) (s := s0) (T := T) (L := L) (n := T * L)
    hTL1 le_rfl hA0 hA1 hV1 (KQ := 2) (by norm_num) hL34pos

theorem measureReal_band_inter_oscSup_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r) :
    (arrayMeasure N).real (band p m r L s0 ∩ OscS p m j r T L s0) ≤
      (Lw T L : ℝ) * ((arrayMeasure N).real (band p m r L s0) * envOsc p m T L) +
        (arrayMeasure N).real (band p m r L s0 ∩ LsBad p m C r T L) :=
  LocOccAllStarts.measureReal_oscSup_le (N := N) hp1 hp2 (m := m) (i := i) (j := j) (C := C)
    hL hT (r := r) (s0 := s0) hr

/-- The `LsBad` mass of one record fibre, bounded by the ambient `LsBad` rate. -/
theorem measureReal_band_inter_lsBad_le {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ} {c : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real (band p m r L s0 ∩ LsBad p m C r T L) ≤
      Real.exp (-c * xOf (Lw T L)) :=
  le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
    (measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad)

/-! ### 5. The finite sum over record fibres -/

/-- The set-level decomposition of the summed bad event: only the `s0`-independent `LsBad`, the
per-fibre `Qpl` drop and the per-fibre oscillation sup survive. -/
theorem biUnion_band_inter_goodWin_compl_subset {p : ℝ} {m r L T : ℕ} {C : ℝ} {i j : Fin N}
    {V : ℝ} (S : Finset ℕ) :
    (⋃ s0 ∈ S, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ⊆
      (((⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L) ∪
          (⋃ s0 ∈ S, band p m r L s0 ∩ Qdrop p m i j T L s0)) ∪
        (⋃ s0 ∈ S, band p m r L s0 ∩ OscS p m j r T L s0) := by
  intro U hU
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union,
    Set.mem_compl_iff] at hU ⊢
  obtain ⟨s0, hs0, hU1, hU2⟩ := hU
  rcases LocOccSingleWindow.carrier_fail_subset_singleWindow
      (p := p) (m := m) (r := r) (s0 := s0) (L := L) (T := T) (C := C) (i := i) (j := j)
      ⟨hU1, hU2⟩ with ⟨h1, h2⟩ | (⟨h1, h3⟩ | ⟨h1, h4⟩)
  · exact Or.inl (Or.inl ⟨⟨s0, hs0, h1⟩, h2⟩)
  · exact Or.inl (Or.inr ⟨s0, hs0, h1, h3⟩)
  · exact Or.inr ⟨s0, hs0, h1, h4⟩

/-- **Raw record-fibre summation, finite index set.**

The summed bad event over a finite set `S` of record times has the same three-mass raw form as the
per-fibre theorem: the total carrier mass `mu.real (⋃_{s0∈S} band s0)` replaces the single fibre
mass, and both `s0`-independent defects (`LsBad`, `harmDefect`) are charged exactly once. -/
theorem measureReal_finset_iUnion_band_inter_goodWin_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {i j : Fin N} {C : ℝ}
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {V : ℝ} (hV1 : 1 ≤ V) {c : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hLsMeas : MeasurableSet (LsBad (N := N) p m C r T L))
    (hHarmMeas : MeasurableSet (Harm (N := N) p m j V r T L)) (S : Finset ℕ) :
    (arrayMeasure N).real
        (⋃ s0 ∈ S, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
        (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real ((⋃ s0 ∈ S, band p m r L s0) ∩ Harm p m j V r T L) +
        (Lw T L : ℝ) * ((arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0) * envOsc p m T L) := by
  have hLsTerm : (arrayMeasure N).real ((⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L) ≤
      Real.exp (-c * xOf (Lw T L)) :=
    le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
      (measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad)
  have hstep : (arrayMeasure N).real
      (⋃ s0 ∈ S, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
      (arrayMeasure N).real ((⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L) +
        (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0 ∩ Qdrop p m i j T L s0) +
        (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0 ∩ OscS p m j r T L s0) := by
    have h1 := measureReal_mono_array (biUnion_band_inter_goodWin_compl_subset
      (p := p) (m := m) (r := r) (L := L) (T := T) (C := C) (i := i) (j := j) (V := V) S)
      (measure_ne_top _ _)
    have h2 := measureReal_union_le (μ := arrayMeasure N)
      (s₁ := ((⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L) ∪
        (⋃ s0 ∈ S, band p m r L s0 ∩ Qdrop p m i j T L s0))
      (s₂ := (⋃ s0 ∈ S, band p m r L s0 ∩ OscS p m j r T L s0))
    have h3 := measureReal_union_le (μ := arrayMeasure N)
      (s₁ := (⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L)
      (s₂ := (⋃ s0 ∈ S, band p m r L s0 ∩ Qdrop p m i j T L s0))
    linarith
  have hQsum : (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0 ∩ Qdrop p m i j T L s0) ≤
      (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real ((⋃ s0 ∈ S, band p m r L s0) ∩ Harm p m j V r T L) := by
    refine le_trans (measureReal_biUnion_finset_le S _) ?_
    refine le_trans (Finset.sum_le_sum (fun s0 _ =>
      measureReal_band_inter_qplDrop_le (p := p) (m := m) (i := i) (j := j)
        hp1 hp2 hL hT hr hV1)) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      ← measureReal_biUnion_band_eq_sum (p := p) (m := m) (r := r) (L := L) (N := N) S,
      ← measureReal_biUnion_band_inter_eq_sum (p := p) (m := m) (r := r) (L := L)
        (N := N) hHarmMeas S,
      biUnion_finset_inter]
  have hOscSum : (arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0 ∩ OscS p m j r T L s0) ≤
      (Lw T L : ℝ) * ((arrayMeasure N).real (⋃ s0 ∈ S, band p m r L s0) * envOsc p m T L) +
        Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_biUnion_finset_le S _) ?_
    refine le_trans (Finset.sum_le_sum (fun s0 _ =>
      measureReal_band_inter_oscSup_le (p := p) (m := m) (i := i) (j := j) (C := C)
        hp1 hp2 hL hT hr)) ?_
    have hLsSum : ∑ s0 ∈ S, (arrayMeasure N).real (band p m r L s0 ∩ LsBad p m C r T L)
        = (arrayMeasure N).real ((⋃ s0 ∈ S, band p m r L s0) ∩ LsBad p m C r T L) := by
      rw [← measureReal_biUnion_band_inter_eq_sum (p := p) (m := m) (r := r) (L := L)
        (N := N) hLsMeas S, biUnion_finset_inter]
    rw [Finset.sum_add_distrib,
      sum_const_mul S (fun s0 => (arrayMeasure N).real (band p m r L s0)) (Lw T L : ℝ)
        (envOsc p m T L),
      measureReal_biUnion_band_eq_sum (p := p) (m := m) (r := r) (L := L) (N := N) S,
      hLsSum]
    linarith
  linarith

/-! ### 6. The countable sum over all record fibres -/

/-- **Raw record-fibre summation over the exact fibre union.**

Over the full countable family of record times the raw bound keeps the same three-mass form; the
fibre union `⋃_{s0} band s0` is the total record carrier, so no factor of the number of fibres
appears anywhere.  Obtained from the finite version by `atTop` monotone convergence of
`mu.real`, not by summing the per-fibre normalised bound. -/
theorem measureReal_iUnion_band_inter_goodWin_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {i j : Fin N} {C : ℝ}
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {V : ℝ} (hV1 : 1 ≤ V) {c : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hLsMeas : MeasurableSet (LsBad (N := N) p m C r T L))
    (hHarmMeas : MeasurableSet (Harm (N := N) p m j V r T L)) :
    (arrayMeasure N).real
        (⋃ s0, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L)) +
        (arrayMeasure N).real (⋃ s0, band p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real ((⋃ s0, band p m r L s0) ∩ Harm p m j V r T L) +
        (Lw T L : ℝ) * ((arrayMeasure N).real (⋃ s0, band p m r L s0) * envOsc p m T L) := by
  set A : ℕ → Set (Array N) :=
    fun n => ⋃ s0 ∈ Finset.range n,
      band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ with hA
  set U : ℕ → Set (Array N) := fun n => ⋃ s0 ∈ Finset.range n, band p m r L s0 with hU
  have hAmono : Monotone A :=
    monotone_biUnion_range (fun s0 : ℕ =>
      band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ)
  have hUmono : Monotone U := monotone_biUnion_range (fun s0 : ℕ => band p m r L s0)
  have hHmono : Monotone fun n => U n ∩ Harm p m j V r T L :=
    fun n m hnm => Set.inter_subset_inter (hUmono hnm) (subset_refl _)
  have hAt : Tendsto (fun n => (arrayMeasure N).real (A n)) atTop
      (𝓝 ((arrayMeasure N).real
        (⋃ s0, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ))) := by
    have h := tendsto_measureReal_iUnion_atTop A hAmono
    rwa [iUnion_range_biUnion] at h
  have hUt : Tendsto (fun n => (arrayMeasure N).real (U n)) atTop
      (𝓝 ((arrayMeasure N).real (⋃ s0, band p m r L s0))) := by
    have h := tendsto_measureReal_iUnion_atTop U hUmono
    rwa [iUnion_range_biUnion] at h
  have hHunion : (⋃ n, (U n ∩ Harm p m j V r T L))
      = (⋃ s0, band p m r L s0) ∩ Harm p m j V r T L := by
    rw [show (⋃ n, (U n ∩ Harm p m j V r T L))
        = (⋃ n, U n) ∩ Harm p m j V r T L from ?_, iUnion_range_biUnion]
    ext U0
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨⟨n, h1⟩, h2⟩
    · rintro ⟨⟨n, h1⟩, h2⟩
      exact ⟨n, h1, h2⟩
  have hHt : Tendsto (fun n => (arrayMeasure N).real (U n ∩ Harm p m j V r T L)) atTop
      (𝓝 ((arrayMeasure N).real ((⋃ s0, band p m r L s0) ∩ Harm p m j V r T L))) := by
    have h := tendsto_measureReal_iUnion_atTop (fun n => U n ∩ Harm p m j V r T L) hHmono
    rwa [hHunion] at h
  have hRt : Tendsto (fun n => 2 * Real.exp (-c * xOf (Lw T L)) +
        (arrayMeasure N).real (U n) * envQ p m V T L +
        (arrayMeasure N).real (U n ∩ Harm p m j V r T L) +
        (Lw T L : ℝ) * ((arrayMeasure N).real (U n) * envOsc p m T L)) atTop
      (𝓝 (2 * Real.exp (-c * xOf (Lw T L)) +
        (arrayMeasure N).real (⋃ s0, band p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real ((⋃ s0, band p m r L s0) ∩ Harm p m j V r T L) +
        (Lw T L : ℝ) * ((arrayMeasure N).real (⋃ s0, band p m r L s0) * envOsc p m T L))) := by
    have h0 : Tendsto (fun _ : ℕ => 2 * Real.exp (-c * xOf (Lw T L))) atTop
        (𝓝 (2 * Real.exp (-c * xOf (Lw T L)))) := tendsto_const_nhds
    have h1 : Tendsto (fun n => (arrayMeasure N).real (U n) * envQ p m V T L) atTop
        (𝓝 ((arrayMeasure N).real (⋃ s0, band p m r L s0) * envQ p m V T L)) :=
      hUt.mul_const _
    have h2 : Tendsto (fun n => (Lw T L : ℝ) *
          ((arrayMeasure N).real (U n) * envOsc p m T L)) atTop
        (𝓝 ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0, band p m r L s0) * envOsc p m T L))) :=
      (hUt.mul_const _).const_mul _
    simpa only using ((h0.add h1).add hHt).add h2
  refine le_of_tendsto_of_tendsto' hAt hRt (fun n => ?_)
  exact measureReal_finset_iUnion_band_inter_goodWin_compl_le (N := N) (p := p) (m := m)
    (i := i) (j := j) (C := C) hp1 hp2 hL hT hr hV1 hLsBad hLsMeas hHarmMeas (Finset.range n)

/-! ### 7. Consequent bounds: total carrier mass and paper-form numerics -/

/-- The total record carrier is at most the whole space, so its mass is at most `1`: this is what
replaces the `s0`-dependent carrier factor after summation. -/
theorem measureReal_iUnion_band_le_one {p : ℝ} {m r L : ℕ} :
    (arrayMeasure N).real (⋃ s0, band p m r L s0) ≤ 1 := by
  have h := measureReal_mono_array (Set.subset_univ (⋃ s0, band (N := N) p m r L s0)) (measure_ne_top _ _)
  simpa only [probReal_univ] using h

/-- The once-charged harmonic defect mass of the *whole* carrier, at the paper's range. -/
theorem measureReal_iUnion_band_inter_harm_le_exp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r : ℕ} {j : Fin N}, (T + 3) * L ≤ r →
      (arrayMeasure N).real ((⋃ s0, band p m r L s0) ∩ Harm p m j (xOf (Lw T L)) r T L) ≤
        Real.exp (-c * xOf (Lw T L)) := by
  obtain ⟨c, hc, L₀, hb⟩ := measureReal_harmDefect_le_exp (N := N) hp1 hp2 hm (T := T) hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL r j hr
  exact le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
    (hb L hL hr)

/-- **The summed raw bound with the total carrier mass replaced by `1`.**

This is the form in which the summed estimate is consumed downstream: two `exp (-c xOf Lw)`
charges (`LsBad` once, harmonic defect once), the `Qpl` Azuma factor, and `Lw` times the
oscillation Azuma factor.  No factor of the number of record fibres occurs. -/
theorem measureReal_iUnion_band_inter_goodWin_compl_le_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {i j : Fin N} {C : ℝ}
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r)
    {V : ℝ} (hV1 : 1 ≤ V) {c c' : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hLsMeas : MeasurableSet (LsBad (N := N) p m C r T L))
    (hHarmMeas : MeasurableSet (Harm (N := N) p m j V r T L))
    (hHarm : (arrayMeasure N).real ((⋃ s0, band p m r L s0) ∩ Harm p m j V r T L) ≤
      Real.exp (-c' * xOf (Lw T L))) :
    (arrayMeasure N).real
        (⋃ s0, band p m r L s0 ∩ (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L)) + envQ p m V T L +
        Real.exp (-c' * xOf (Lw T L)) + (Lw T L : ℝ) * envOsc p m T L := by
  have hmain := measureReal_iUnion_band_inter_goodWin_compl_le (N := N) (p := p) (m := m)
    (i := i) (j := j) (C := C) hp1 hp2 hL hT hr hV1 hLsBad
    hLsMeas hHarmMeas
  have hD1 : (arrayMeasure N).real (⋃ s0, band p m r L s0) ≤ 1 :=
    measureReal_iUnion_band_le_one
  have hD0 : (0 : ℝ) ≤ (arrayMeasure N).real (⋃ s0, band p m r L s0) := measureReal_nonneg
  have henvQ0 : (0 : ℝ) ≤ envQ p m V T L := by rw [envQ]; positivity
  have henvOsc0 : (0 : ℝ) ≤ envOsc p m T L := by rw [envOsc]; positivity
  have hLw0 : (0 : ℝ) ≤ (Lw T L : ℝ) := by positivity
  have h1 : (arrayMeasure N).real (⋃ s0, band p m r L s0) * envQ p m V T L ≤
      1 * envQ p m V T L := mul_le_mul_of_nonneg_right hD1 henvQ0
  have h2 : (Lw T L : ℝ) * ((arrayMeasure N).real (⋃ s0, band p m r L s0) * envOsc p m T L) ≤
      (Lw T L : ℝ) * (1 * envOsc p m T L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD1 henvOsc0) hLw0
  linarith


/-! ### 8. Paper-scale absorption of the summed raw bound

The arithmetic of `LocOccSingleWindow.exists_singleWindow_complement_paper` (`azuma_exp_arg_ge`,
`osc_exp_arg_ge`, `pow_mul_exp_neg_absorb`) applied to the *four summed pieces*: the total carrier
mass is `<= 1`, so the same `C_T * exp (-c_T * L^{1/16})` collapse holds for the summed bound, with
no factor of the number of record fibres. -/

noncomputable section

theorem paper_profile_absorb {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {T : ℕ} (hT : 1 ≤ T) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      2 * Real.exp (-c * xOf (Lw T L)) + envQ p m (xOf (Lw T L)) T L +
          Real.exp (-c' * xOf (Lw T L)) + (Lw T L : ℝ) * envOsc p m T L ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ ((1:ℝ) / 16)) := by
  -- the two envelope constants
  set K1 : ℝ := RecCarrierPaper.Kb p m * (((2 * T + 3 : ℕ)) : ℝ) with hK1def
  set K2 : ℝ := 9 * SiteHMax.Cproj p m * (((2 * T + 3 : ℕ)) : ℝ) with hK2def
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT3pos : (0 : ℝ) < (((2 * T + 3 : ℕ)) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * T + 3 := by omega
    exact_mod_cast this
  have hK1 : 0 < K1 := mul_pos (RecCarrierPaper.Kb_pos (p := p) (m := m) hp1 hp2) hT3pos
  have hK2 : 0 < K2 := by
    have := RecCarrierPaper.Cproj_pos (p := p) (m := m) hp1 hp2
    rw [hK2def]; positivity
  set b : ℝ := min (min c c') (min (1 / (4 * (T : ℝ) * K1 ^ 2)) (1 / (16 * (T : ℝ) * K2 ^ 2)))
    with hbdef
  have hb1 : 0 < 1 / (4 * (T : ℝ) * K1 ^ 2) := by positivity
  have hb2 : 0 < 1 / (16 * (T : ℝ) * K2 ^ 2) := by positivity
  have hbpos : 0 < b := by
    rw [hbdef]
    exact lt_min (lt_min hc hc') (lt_min hb1 hb2)
  have hblec : b ≤ c := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hblec' : b ≤ c' := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hbleK1 : b ≤ 1 / (4 * (T : ℝ) * K1 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hbleK2 : b ≤ 1 / (16 * (T : ℝ) * K2 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  set K3 : ℝ := 3 + 2 * ((T : ℝ) + 1) + 2 * ((T : ℝ) + 1) * (2 * (T : ℝ) + 4) with hK3def
  have hK3 : 0 ≤ K3 := by rw [hK3def]; positivity
  refine ⟨b / 2, by linarith, K3 * (((48).factorial : ℝ) / (b / 2) ^ 48), ?_, 1, ?_⟩
  · have hfac : (0 : ℝ) < (((48).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos 48
    have hb2' : (0 : ℝ) < (b / 2) ^ 48 := pow_pos (by linarith) 48
    positivity
  intro L hL
  set Lr : ℝ := (L : ℝ) ^ ((1:ℝ) / 16) with hLrdef
  set E : ℝ := QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
    with hEdef
  set B : ℝ := SiteHMax.capB p m (xOf (Lw T L)) with hBdef
  have hharm : Real.exp (-c' * xOf (Lw T L)) ≤ Real.exp (-c' * xOf (Lw T L)) := le_refl _
  have hA0' : (0:ℝ) ≤ 1 := zero_le_one
  have hA1' : (1:ℝ) ≤ 1 := le_refl 1
  have hLr_le : Lr ≤ xOf (Lw T L) := by
    have := RecCarrierPaper.xOf_le_of_le (L := L) (M := Lw T L) (le_Lw (T := T) L)
    simpa [hLrdef, LocSumAct.xOf] using this
  have hLr0 : 0 ≤ Lr := by rw [hLrdef]; positivity
  have hharm2 : Real.exp (-c' * xOf (Lw T L)) ≤ Real.exp (-b * Lr) := by
    have harg : -c' * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c' * Lr := mul_le_mul_of_nonneg_right hblec' hLr0
      have h2 : c' * Lr ≤ c' * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc'.le
      linarith
    exact Real.exp_le_exp.mpr harg
  have hharm' : Real.exp (-c' * xOf (Lw T L)) ≤ Real.exp (-b * Lr) := hharm2
  have hterm1 : 2 * Real.exp (-c * xOf (Lw T L)) ≤ 2 * Real.exp (-b * Lr) := by
    have harg : -c * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c * Lr := mul_le_mul_of_nonneg_right hblec hLr0
      have h2 : c * Lr ≤ c * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc.le
      linarith
    have := Real.exp_le_exp.mpr harg
    linarith
  -- the Azuma exponent
  have hV1x : (1 : ℝ) ≤ xOf (Lw T L) := RecCarrierPaper.one_le_xOf_Lw T L
  have hV0x : (0 : ℝ) ≤ xOf (Lw T L) := by linarith
  have hEpos : 0 < E := by
    rw [hEdef]
    exact QplPredEnv.envB_pos hp1 hp2 m hV0x (QplWindow.envC_nonneg hp1 hp2 m hV0x)
  have hEK : E ≤ K1 * Lr := by
    rw [hEdef, hK1def, hLrdef]
    exact RecCarrierPaper.envB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hTLcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hL34 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L (Lw T L) := L34_lower_rpow L (Lw T L)
  have hAzarg : Lr / (4 * (T : ℝ) * K1 ^ 2) ≤ L34 L (Lw T L) ^ 2 /
      (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
    have h := RecCarrierPaper.azuma_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K1) (E := E)
      (L34 := L34 L (Lw T L)) (by exact_mod_cast hL) hTpos hK1 hEpos hEK hL34
    simpa [hLrdef, hTLcast] using h
  have hAz : Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
        have h2 : b * Lr ≤ Lr / (4 * (T : ℝ) * K1 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK1 hLr0
          calc b * Lr ≤ (1 / (4 * (T : ℝ) * K1 ^ 2)) * Lr := h3
            _ = Lr / (4 * (T : ℝ) * K1 ^ 2) := by ring
        linarith
      have heq : ((2 * L34 L (Lw T L) / 2) ^ 2) = L34 L (Lw T L) ^ 2 := by ring
      have hneg : -(L34 L (Lw T L) ^ 2) / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)
          = -(L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the oscillation exponent
  have hBpos : 0 < B := by
    rw [hBdef]
    exact SiteHMax.capB_pos hp1 hp2 m hV0x
  have hBK : B ≤ K2 * Lr := by
    rw [hBdef, hK2def, hLrdef]
    exact RecCarrierPaper.capB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hOsc : Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
        have h2 : b * Lr ≤ Lr / (16 * (T : ℝ) * K2 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK2 hLr0
          calc b * Lr ≤ (1 / (16 * (T : ℝ) * K2 ^ 2)) * Lr := h3
            _ = Lr / (16 * (T : ℝ) * K2 ^ 2) := by ring
        have h4 := RecCarrierPaper.osc_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K2) (B := B)
          (by exact_mod_cast hL) hTpos hK2 hBpos hBK
        have h4' : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
          rw [hTLcast]
          linarith
        linarith
      have heq : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (L : ℝ) ^ (3 / 2 : ℝ) :=
        RecCarrierPaper.sq_three_quarters (by linarith)
      have hneg : -((L : ℝ) ^ (3 / 2 : ℝ)) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)
          = -((L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the two products with the carrier mass
  have hcoef : (0 : ℝ) ≤ 2 * ((((T * L : ℕ)) : ℝ) + 1) := by positivity
  have hprodA : (1:ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) ≤
      (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by
    have h1 : (1:ℝ) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hAz (Real.exp_pos _).le (by norm_num)
    calc (1:ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)))
        = (2 * ((((T * L : ℕ)) : ℝ) + 1)) *
            ((1:ℝ) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
              (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) := by ring
      _ ≤ (2 * ((((T * L : ℕ)) : ℝ) + 1)) * (1 * Real.exp (-b * Lr)) :=
          mul_le_mul_of_nonneg_left h1 hcoef
      _ = (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by ring
  have hprodO : (Lw T L : ℝ) * ((1:ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
        Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)))) ≤
      ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    have h1 : (1:ℝ) * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
          (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hOsc (Real.exp_pos _).le (by norm_num)
    calc (Lw T L : ℝ) * ((1:ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
          Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))))
        = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
            ((1:ℝ) * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
              (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))) := by ring
      _ ≤ ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * (1 * Real.exp (-b * Lr)) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by ring
  -- the polynomial prefactor is at most `K3 * L^2`
  have hTL1 : (((T * L : ℕ)) : ℝ) + 1 ≤ ((T : ℝ) + 1) * (L : ℝ) := by
    have h1 : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    rw [h1]; nlinarith
  have hLwle : (Lw T L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
    have h1 : Lw T L ≤ (2 * T + 3) * L := RecCarrierPaper.Lw_le_paper (T := T) hL
    have h1' : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 3) * L : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (((2 * T + 3) * L : ℕ) : ℝ) = (2 * (T : ℝ) + 3) * (L : ℝ) := by push_cast; ring
    have h3 : (2 * (T : ℝ) + 3) * (L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith
      nlinarith
    linarith
  have hpoly : 3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
      (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1)) ≤ K3 * (L : ℝ) ^ 2 := by
    have h2 : 2 * ((((T * L : ℕ)) : ℝ) + 1) ≤ 2 * (((T : ℝ) + 1) * (L : ℝ)) := by linarith
    have h3 : (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))
        ≤ ((2 * (T : ℝ) + 4) * (L : ℝ)) * (2 * (((T : ℝ) + 1) * (L : ℝ))) := by
      apply mul_le_mul hLwle h2
      · positivity
      · positivity
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [hK3def]
    nlinarith
  -- absorb the polynomial into the stretched exponential
  have habs := RecCarrierPaper.pow_mul_exp_neg_absorb hbpos 2 (L := (L : ℝ))
    (by exact_mod_cast hL)
  have hfinal : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
        (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) ≤
      (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by
    have h1 : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
          (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) ≤
        (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    have h2 : (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr)
        = K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) := by ring
    have h3 : K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) ≤
        K3 * ((((16 * (2 + 1)).factorial : ℝ) / (b / 2) ^ (16 * (2 + 1))) *
          Real.exp (-(b / 2) * Lr)) := by
      apply mul_le_mul_of_nonneg_left _ hK3
      simpa [hLrdef] using habs
    have h4 : (16 * (2 + 1)) = 48 := by norm_num
    rw [h4] at h3
    have h5 : K3 * ((((48).factorial : ℝ) / (b / 2) ^ 48) * Real.exp (-(b / 2) * Lr))
        = (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by ring
    linarith [h1, h2, h3, h5]
  have hprodA' : envQ p m (xOf (Lw T L)) T L ≤
      (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by
    simpa [envQ, hEdef] using hprodA
  have hprodO' : (Lw T L : ℝ) * envOsc p m T L ≤
      ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    simpa [envOsc, hBdef] using hprodO
  have hgoal : 2 * Real.exp (-c * xOf (Lw T L)) + envQ p m (xOf (Lw T L)) T L +
        Real.exp (-c' * xOf (Lw T L)) + (Lw T L : ℝ) * envOsc p m T L ≤
      (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
          (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    have hthree : (3 : ℝ) = 2 + 1 := by norm_num
    linarith [hterm1, hharm', hprodA', hprodO']
  linarith [hgoal, hfinal]

end

/-! ### 9. The paper-scale record-fibre-union bound -/

/-- **The paper profile on the whole record-fibre union.**

Combining the summed raw estimate (`measureReal_iUnion_band_inter_goodWin_compl_le_paper`), the
once-charged harmonic rate (`measureReal_iUnion_band_inter_harm_le_exp`) and the absorption
(`paper_profile_absorb`) gives, for the *union* over all record times and at the paper's original
range `(T+3)*L ≤ r`, the same normalised profile `C_T exp (-c_T L^{1/16})` as the per-fibre
theorem — with a constant that does not depend on the number of record fibres.  The only
probabilistic input beyond the paper range is the `LsBad` rate, exactly as in the per-fibre
statement, and the two measurability inputs of the summation. -/
theorem exists_iUnion_complement_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {i j : Fin N} {C : ℝ} {c : ℝ} (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      MeasurableSet (LsBad (N := N) p m C r T L) →
      MeasurableSet (Harm (N := N) p m j (xOf (Lw T L)) r T L) →
      (arrayMeasure N).real
          (⋃ s0, band (N := N) p m r L s0 ∩
            (LocOccSingleWindow.GoodWin p m i j C r T L s0)ᶜ) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ ((1:ℝ) / 16)) := by
  obtain ⟨c', hc', L₀', hb'⟩ :=
    measureReal_iUnion_band_inter_harm_le_exp (N := N) hp1 hp2 hm (T := T) hT
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀'', hbound⟩ :=
    paper_profile_absorb hp1 hp2 (m := m) hT hc hc'
  refine ⟨c_T, hc_T, C_T, hC_T, max (max L₀' L₀'') 1, ?_⟩
  intro L hL r hr hLsBad hLsMeas hHarmMeas
  have hL1 : 1 ≤ L := le_trans (le_max_right _ 1) hL
  have hL' : L₀' ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL'' : L₀'' ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hharm : (arrayMeasure N).real
      ((⋃ s0, band (N := N) p m r L s0) ∩
        Harm (N := N) p m j (xOf (Lw T L)) r T L) ≤ Real.exp (-c' * xOf (Lw T L)) :=
    hb' L hL' hr
  have hpaper := measureReal_iUnion_band_inter_goodWin_compl_le_paper (N := N) (p := p) (m := m)
    (i := i) (j := j) (C := C) hp1 hp2 (L := L) hL1 (T := T) hT (r := r) hr
    (V := xOf (Lw T L)) (RecCarrierPaper.one_le_xOf_Lw T L) hLsBad hLsMeas hHarmMeas hharm
  have habs := hbound L hL''
  linarith

end LocOccFibreSum
