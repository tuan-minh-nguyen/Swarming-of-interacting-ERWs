import Swarm.LocOccSingleWindowAllPairs
import Swarm.LocOccFibreSum
import Swarm.LocOccRecordFibres
import Swarm.SingleWindowSiteRate

/-!
  # All-pair clock-fibre summation for the single-window occupation event


  `LocOccSingleWindowAllPairs` (`GoodWinAllPairs`) bounds, at **one fixed record fibre**
  `{tau_r = s0} ∩ {d_r <= L}`, the mass of the complement of the all-pairs single-window
  occupation event, with a supplied `LsBad` rate and with the harmonic `(locmax)` defect riding
  inside the per-pair `Qpl` budget.
  `LocOccFibreSum` performs the **single-pair** clock sum, charging the two `s0`-independent
  defective sets once and the carrier-weighted terms against the disjoint fibres.

  This file performs the **all-pair** clock summation, from the raw per-fibre accounting rather
  than by summing the already normalised per-fibre bounds.  The object of study is the exact
  union over the record clock

      `B(L) = ⋃ s0, band s0 ∩ (GoodWinAllPairs p m C r T L s0)^c`

  with `band s0 = recordPrefixBand p m r s0 L`.  The structural decomposition is
  `LocOccSingleWindowAllPairs.carrier_fail_subset_goodWinAllPairs_shared` unioned over the fibres:
  failure at *some* fibre means either the `s0`-independent `LsBad`, or the `Qpl` drop of some
  ordered pair at that fibre, or the projected oscillation of some record walker at that fibre.
  Summing the raw pieces gives (Section 5, finite index set; Section 6, the full countable clock)

      `mu.real B <= (1+N) e^{-c x} + card(offDiag) e^{-c' x}
                    + card(offDiag) (mu.real U * envQ) + N (Lw * (mu.real U * envOsc))`

  where `U = ⋃ s0 band s0` and `x = xOf (Lw T L)`.  **No factor of the number of record fibres
  appears**: the carrier mass is charged once through `U` (hence at most `1`), `LsBad` once, and
  the harmonic defect once per ordered pair through its ambient rate.  Each per-fibre constant is
  located in the statement: the `LsBad` exponential carries no fibre weight, the `Qpl` Azuma price
  and the harmonic rate are per ordered pair (`card(offDiag)`), the oscillation price is per record
  walker (`N`).

  Section 7 applies the paper's stretching/absorption arithmetic
  (`LocOccFibreSum.paper_profile_absorb`, used, not re-derived) to obtain the paper profile
  `(1 + N + card(offDiag)) C_T exp (-c_T L^{1/16})`; for `N >= 2` this is
  `card(offDiag) C_T' exp (...)` — the paper's `(lococc)` shape with the `offDiag` factor explicit.

  Measurability: the harmonic defect is measurable unconditionally
  (`LocOccFibreSum.measurableSet_Harm`), and the oscillation term is handled **without**
  measurability of `LsBad`: outside `LsBad` the truncation residual of `OscSup` is empty, so the
  per-fibre oscillation charge is bounded on `LsBad^c`
  (`measureReal_band_inter_oscSup_sdiff_lsBad_le`).  The single remaining input is the `LsBad`
  **rate** `c > 0` — exactly the input pattern of `LocOccFibreSum` — and Section 9 discharges even
  that at the canonical `Ccan = |Mb| + 1` of `LocOccSiteRate` (`SingleWindowSiteRate`).

  The `ReachAll` carrier distinction is preserved (Section 8): the bound is a bound for the
  *fibre union*, and only on `ReachAll` is that union the paper's defect band
  (`LocOccRecordFibres.reachAll_inter_iUnion_recordPrefixBand_eq`); the `ReachAll`-qualified
  statements are given separately.  Nothing here claims an `s0`-free right-hand side (the raw
  carrier factors are summed through `U`, not claimed away), non-vacuity of the good event, an
  invariant measure, regeneration or speed.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal BigOperators Topology

namespace LocOccAllPairFibreSum

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open LocOccFibreSum LocOccSingleWindow LocOccAllPairs
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The deterministic decomposition of the all-pair bad event over a fibre set -/

/-- **Failure of the all-pairs event at any fibre of `S` is one of three raw events.**

For a finite set `S` of record times, the union over `s0 ∈ S` of
`band s0 ∩ (GoodWinAllPairs s0)^c` is covered by the single `s0`-independent `LsBad`, the union of
the per-pair `Qpl` drop sets, and the union of the projected-oscillation sets, both taken over the
same fibre set `S`.  No summation over `s0` and no normalisation occurs here: this is the pointwise
content of `LocOccSingleWindowAllPairs.carrier_fail_subset_goodWinAllPairs_shared` unioned over the
fibres. -/
theorem finset_carrier_fail_subset {p : ℝ} {m r L T : ℕ} {C : ℝ} (S : Finset ℕ) :
    (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩
        (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ⊆
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L) ∪
        ((⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
            band (N := N) p m r L s0 ∩ Qdrop (N := N) p m q.1 q.2 T L s0) ∪
          (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
            band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0)) := by
  intro U hU
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    exists_prop] at hU ⊢
  obtain ⟨s0, hs0, hU1, hU2⟩ := hU
  rcases LocOccSingleWindowAllPairs.carrier_fail_subset_goodWinAllPairs_shared (N := N)
    (p := p) (m := m) (r := r) (s0 := s0) (L := L) (T := T) (C := C) ⟨hU1, hU2⟩
    with h | h | h
  · exact Or.inl ⟨⟨s0, hs0, h.1⟩, h.2⟩
  · simp only [Set.mem_iUnion, exists_prop] at h
    obtain ⟨q, hq, h1, h2⟩ := h
    exact Or.inr (Or.inl ⟨q, hq, s0, hs0, h1, h2⟩)
  · simp only [Set.mem_iUnion, exists_prop] at h
    obtain ⟨q, hq, h1, h2⟩ := h
    exact Or.inr (Or.inr ⟨q, hq, s0, hs0, h1, h2⟩)

/-! ### 2. The oscillation term without `LsBad` measurability -/

/-- The truncation residual `{∃ k < T L, ¬ siteGood (s0+k)}` of the site-window oscillation
estimate is contained in `LsBad` on the carrier: off `LsBad` the paper's `(locmax)` cap holds on
the whole wide window, exactly what `QplWindow.HprevAt_le_of_window` consumes. -/
theorem siteOsc_residual_subset_lsBad {p : ℝ} {m r L T : ℕ} {j : Fin N} {C : ℝ} {s0 : ℕ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hr : (T + 3) * L ≤ r) :
    {U : Array N | U ∈ band (N := N) p m r L s0 ∧ ∃ k < T * L,
        U ∉ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)} ⊆
      band (N := N) p m r L s0 ∩ LsBad (N := N) p m C r T L := by
  rintro U ⟨hU, k, hk, hbad⟩
  refine ⟨hU, ?_⟩
  by_contra hls
  have hloc := hloc_of_not_LsBad (p := p) (m := m) (r := r) (s := s0) (C := C) (T := T)
    (L := L) j hL hls
  have hku : s0 + k ≤ s0 + T * L := by omega
  have hrec := recVal_window hU hr j (u := s0 + k) (by omega) hku
  have hA1 : 1 ≤ A0 r T L := one_le_A0 hL hr
  have hV1 : (1 : ℝ) ≤ xOf (Lw T L) := one_le_xOf (one_le_Lw T L)
  exact hbad (QplWindow.HprevAt_le_of_window (N := N) hp1 hp2 (m := m) j (A := A0 r T L)
    (M := Lw T L) (t := s0 + k) hA1 hV1 hrec hloc)

/-- **The per-fibre oscillation charge, with the `LsBad` part removed.**

`LocOccFibreSum.measureReal_band_inter_oscSup_le` bounds `mu.real (band s0 ∩ OscSup s0)` by the
Azuma price *plus* `mu.real (band s0 ∩ LsBad)`; summing that over the fibres would need
measurability of `LsBad` to charge the second term once.  Here the per-fibre statement is proved on
`LsBad^c` instead, where the truncation residual vanishes, so the charge is a pure Azuma price and
no `LsBad` term is ever summed over the clock. -/
theorem measureReal_band_inter_oscSup_sdiff_lsBad_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {j : Fin N} {C : ℝ}
    {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ} (hr : (T + 3) * L ≤ r) :
    (arrayMeasure N).real
        ((band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) \
          LsBad (N := N) p m C r T L) ≤
      (Lw T L : ℝ) * ((arrayMeasure N).real (band (N := N) p m r L s0) * envOsc p m T L) := by
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hV0 : (0 : ℝ) ≤ xOf (Lw T L) := le_trans zero_le_one (one_le_xOf hLw1)
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hn : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hsub : (band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) \
        LsBad (N := N) p m C r T L ⊆
      ⋃ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
        (band (N := N) p m r L s0 ∩
            {U : Array N | ∀ k < T * L, U ∈ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)} ∩
          {U : Array N | ∃ u v : ℕ, s0 ≤ u ∧ u ≤ v ∧ v ≤ s0 + T * L ∧
            (L : ℝ) ^ (3 / 4 : ℝ) ≤
              |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|}) := by
    rintro U ⟨⟨hUband, hUosc⟩, hUls⟩
    simp only [OscS, OscSup, Set.mem_ofPred_eq] at hUosc
    obtain ⟨y, hy, u, v, h1, h2, h3, h4⟩ := hUosc
    have hUgood : ∀ k < T * L, U ∈ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k) := by
      intro k hk
      by_contra hbad
      exact hUls (siteOsc_residual_subset_lsBad (N := N) (p := p) (m := m) (r := r) (j := j)
        (C := C) (T := T) (L := L) (s0 := s0) hp1 hp2 hL hT hr ⟨hUband, k, hk, hbad⟩).2
    exact Set.mem_biUnion hy ⟨⟨hUband, hUgood⟩, u, v, h1, h2, h3, h4⟩
  have hcard : ((Finset.Ico (A0 r T L) (A0 r T L + Lw T L)).card : ℝ) = (Lw T L : ℝ) := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  refine le_trans (measureReal_mono_array hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N)
    (Finset.Ico (A0 r T L) (A0 r T L + Lw T L)) (fun y =>
      (band (N := N) p m r L s0 ∩
          {U : Array N | ∀ k < T * L, U ∈ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)} ∩
        {U : Array N | ∃ u v : ℕ, s0 ≤ u ∧ u ≤ v ∧ v ≤ s0 + T * L ∧
          (L : ℝ) ^ (3 / 4 : ℝ) ≤
            |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|}))) ?_
  have hsum : (∑ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
        (arrayMeasure N).real
          (band (N := N) p m r L s0 ∩
              {U : Array N | ∀ k < T * L, U ∈ SiteHMax.siteGood p m j (xOf (Lw T L)) (s0 + k)} ∩
            {U : Array N | ∃ u v : ℕ, s0 ≤ u ∧ u ≤ v ∧ v ≤ s0 + T * L ∧
              (L : ℝ) ^ (3 / 4 : ℝ) ≤
                |projH p m j v U ((y : ℕ) : ℤ) - projH p m j u U ((y : ℕ) : ℤ)|}))
      ≤ ∑ _y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
          (arrayMeasure N).real (band (N := N) p m r L s0) *
            (2 * (((T * L : ℕ) : ℝ) + 1) *
              Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                (16 * (((T * L : ℕ)) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))) :=
    Finset.sum_le_sum (fun y _ =>
      M3Hosc.measureReal_cell_siteOsc_pair_le_sharp (N := N) (p := p) hp1 hp2 m j
        ((y : ℕ) : ℤ)
        (ActualRecordFiltration.measurableSet_recordPrefixBand (N := N) p m r s0 L) hV0 hn hε)
  refine le_trans hsum ?_
  rw [Finset.sum_const, nsmul_eq_mul, hcard, envOsc]

/-! ### 3. The summed `Qpl` price of one ordered pair -/

/-- **The `Qpl` drop of one ordered pair, summed over a fibre set.**

The per-fibre decomposition
`band s0 ∩ Qdrop <= mu.real (band s0) * envQ + mu.real (band s0 ∩ Harm)` is summed against the
*disjoint* fibres, so the carrier factor becomes the mass of the whole fibre union `U_S` and the
harmonic defect becomes the single intersection `U_S ∩ Harm`.  Nothing is normalised per fibre and
no count of fibres appears. -/
theorem measureReal_finset_iUnion_band_inter_qplDrop_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {i j : Fin N} {L : ℕ}
    (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    (hHarmMeas : MeasurableSet (Harm (N := N) p m j V r T L)) (S : Finset ℕ) :
    (arrayMeasure N).real
        (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩ Qdrop (N := N) p m i j T L s0) ≤
      (arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envQ p m V T L +
        (arrayMeasure N).real
          ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ Harm (N := N) p m j V r T L) := by
  refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) S _) ?_
  refine le_trans (Finset.sum_le_sum (fun s0 _ =>
    measureReal_band_inter_qplDrop_le (N := N) (p := p) (m := m) (i := i) (j := j)
      hp1 hp2 hL hT hr hV1)) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    ← measureReal_biUnion_band_eq_sum (p := p) (m := m) (r := r) (L := L) (N := N) S,
    ← measureReal_biUnion_band_inter_eq_sum (p := p) (m := m) (r := r) (L := L)
      (N := N) hHarmMeas S,
    biUnion_finset_inter]

/-! ### 4. The summed oscillation price of one record walker -/

/-- **The projected oscillation of one record walker, summed over a fibre set.**

Same accounting as the single-pair clock sum, but with the oscillation charge taken on `LsBad^c`
(Section 2), so that the constant `LsBad` exponential is charged exactly once through
`mu.real LsBad <= exp (-c xOf Lw)` and never summed over the fibres. -/
theorem measureReal_finset_iUnion_band_inter_oscSup_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {j : Fin N} {C : ℝ} {L : ℕ}
    (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r) {c : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) (S : Finset ℕ) :
    (arrayMeasure N).real
        (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) ≤
      (Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L) +
        Real.exp (-c * xOf (Lw T L)) := by
  have hsub : (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) ⊆
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L) ∪
        ⋃ s0 ∈ S, (band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) \
          LsBad (N := N) p m C r T L := by
    intro U hU
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
      exists_prop] at hU ⊢
    obtain ⟨s0, hs0, h1, h2⟩ := hU
    by_cases hls : U ∈ LsBad (N := N) p m C r T L
    · exact Or.inl ⟨⟨s0, hs0, h1⟩, hls⟩
    · exact Or.inr ⟨s0, hs0, ⟨h1, h2⟩, hls⟩
  have hstep : (arrayMeasure N).real
      (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) ≤
      (arrayMeasure N).real
          ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L) +
        (arrayMeasure N).real
          (⋃ s0 ∈ S, (band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) \
            LsBad (N := N) p m C r T L) := by
    refine le_trans (measureReal_mono_array hsub (measure_ne_top _ _)) ?_
    exact measureReal_union_le (μ := arrayMeasure N) _ _
  have hls : (arrayMeasure N).real
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L) ≤
      Real.exp (-c * xOf (Lw T L)) :=
    le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
      (measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad)
  have hsum : (arrayMeasure N).real
      (⋃ s0 ∈ S, (band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0) \
        LsBad (N := N) p m C r T L) ≤
      (Lw T L : ℝ) *
        ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L) := by
    refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) S _) ?_
    refine le_trans (Finset.sum_le_sum (fun s0 _ =>
      measureReal_band_inter_oscSup_sdiff_lsBad_le (N := N) (p := p) (m := m) (j := j) (C := C)
        hp1 hp2 hL hT hr)) ?_
    rw [sum_const_mul S (fun s0 => (arrayMeasure N).real (band (N := N) p m r L s0))
        (Lw T L : ℝ) (envOsc p m T L),
      measureReal_biUnion_band_eq_sum (p := p) (m := m) (r := r) (L := L) (N := N) S]
  linarith

/-! ### 5. The finite all-pair clock sum -/

/-- **All-pair clock summation over a finite fibre set.**

The raw four-piece accounting of Section 1, summed against the disjoint fibres:

* `LsBad` is `s0`-independent and charged once (weight `1` on its exponential, plus the `N` copies
  coming from the oscillation residual charge);
* the `Qpl` Azuma price is charged once per ordered pair (`card(offDiag)`);
* the harmonic `(locmax)` defect is charged once per ordered pair, through the ambient rate `c'`;
* the projected oscillation is charged once per record walker (`N` copies of the `Lw`-weighted
  Azuma price), because `OscSup` depends on the ordered pair only through `q.2`.

The carrier mass enters only as `mu.real U_S`, the mass of the whole finite fibre union, which is
`<= 1`; no factor of the number of fibres and no normalised per-fibre term appears. -/
theorem measureReal_finset_iUnion_band_inter_goodWinAllPairs_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ} {L : ℕ} (hL : 1 ≤ L)
    {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c c' : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hHarm : ∀ j : Fin N, (arrayMeasure N).real
      ((⋃ s0, band (N := N) p m r L s0) ∩ Harm (N := N) p m j V r T L) ≤
        Real.exp (-c' * xOf (Lw T L))) (S : Finset ℕ) :
    (arrayMeasure N).real
        (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envQ p m V T L) +
        (N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L)) := by
  -- (0) the carrier of the fibre set sits inside the full fibre union
  have hUsub : (⋃ s0 ∈ S, band (N := N) p m r L s0) ⊆ ⋃ s0, band (N := N) p m r L s0 := by
    intro U hU
    simp only [Set.mem_iUnion, exists_prop] at hU ⊢
    obtain ⟨s0, -, h⟩ := hU
    exact ⟨s0, h⟩
  have hHarmS : ∀ j : Fin N, (arrayMeasure N).real
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ Harm (N := N) p m j V r T L) ≤
        Real.exp (-c' * xOf (Lw T L)) :=
    fun j => le_trans (measureReal_mono_array (Set.inter_subset_inter hUsub (subset_refl _))
      (measure_ne_top _ _)) (hHarm j)
  -- (1) the `LsBad` charge, once
  have hA : (arrayMeasure N).real
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L) ≤
      Real.exp (-c * xOf (Lw T L)) :=
    le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
      (measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad)
  -- (2) the `Qpl` drops, once per ordered pair
  have hB : (arrayMeasure N).real
      (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ Qdrop (N := N) p m q.1 q.2 T L s0) ≤
      ((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envQ p m V T L) +
        ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) := by
    refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) (offDiag (N := N)) _) ?_
    refine le_trans (Finset.sum_le_sum (fun q _ =>
      measureReal_finset_iUnion_band_inter_qplDrop_le (N := N) (p := p) (m := m)
        (i := q.1) (j := q.2) hp1 hp2 hL hT hr hV1
        (measurableSet_Harm (N := N) (p := p) (m := m) (j := q.2) (V := V) (r := r) (T := T)
          (L := L)) S)) ?_
    refine le_trans (Finset.sum_le_sum (fun q _ => add_le_add le_rfl (hHarmS q.2))) ?_
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, le_refl]
  -- (3) the projected oscillation, at most once per record walker
  have hCsub : (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0) ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin N)), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ OscS (N := N) p m j r T L s0 := by
    intro U hU
    simp only [Set.mem_iUnion, exists_prop] at hU ⊢
    obtain ⟨q, -, s1, hs1, h1, h2⟩ := hU
    exact ⟨q.2, Finset.mem_univ _, s1, hs1, h1, h2⟩
  have hC : (arrayMeasure N).real
      (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0) ≤
      (N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L)) +
        (N : ℝ) * Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array hCsub (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N)
      (Finset.univ : Finset (Fin N)) _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ =>
      measureReal_finset_iUnion_band_inter_oscSup_le (N := N) (p := p) (m := m) (j := j) (C := C)
        hp1 hp2 hL hT hr hLsBad S)) ?_
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, le_refl]
  -- (4) assemble the three masses
  have hstep : (arrayMeasure N).real
      (⋃ s0 ∈ S, band (N := N) p m r L s0 ∩
        (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      (arrayMeasure N).real ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩
          LsBad (N := N) p m C r T L) +
        ((arrayMeasure N).real
            (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
              band (N := N) p m r L s0 ∩ Qdrop (N := N) p m q.1 q.2 T L s0) +
          (arrayMeasure N).real
            (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
              band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0)) := by
    refine le_trans (measureReal_mono_array
      (finset_carrier_fail_subset (N := N) (p := p) (m := m) (r := r) (L := L) (T := T)
        (C := C) S) (measure_ne_top _ _)) ?_
    have hu1 := measureReal_union_le (μ := arrayMeasure N)
      ((⋃ s0 ∈ S, band (N := N) p m r L s0) ∩ LsBad (N := N) p m C r T L)
      ((⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
            band (N := N) p m r L s0 ∩ Qdrop (N := N) p m q.1 q.2 T L s0) ∪
        (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
            band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0))
    have hu2 := measureReal_union_le (μ := arrayMeasure N)
      (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ Qdrop (N := N) p m q.1 q.2 T L s0)
      (⋃ q ∈ offDiag (N := N), ⋃ s0 ∈ S,
        band (N := N) p m r L s0 ∩ OscS (N := N) p m q.2 r T L s0)
    linarith
  -- (5) the arithmetic: the multiplicities `1+N`, `card`, `card`, `N` fit inside `1 + N + card`
  have htot : (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envQ p m V T L) +
        (N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L))
      = Real.exp (-c * xOf (Lw T L)) +
        (((offDiag (N := N)).card : ℝ) *
            ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envQ p m V T L) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L))) +
        ((N : ℝ) * ((Lw T L : ℝ) *
            ((arrayMeasure N).real (⋃ s0 ∈ S, band (N := N) p m r L s0) * envOsc p m T L)) +
          (N : ℝ) * Real.exp (-c * xOf (Lw T L))) := by ring
  rw [htot]
  linarith [hstep, hA, hB, hC]

/-! ### 6. The full countable clock -/

/-- **All-pair clock summation over the exact fibre union.**

The countable union over *all* record times `s0` of `band s0 ∩ (GoodWinAllPairs s0)^c`, bounded by
the same four raw pieces with the total record carrier `⋃ s0 band s0` in place of the finite `U_S`.
Obtained from the finite version by atTop monotone convergence of `mu.real`, never by summing the
normalised per-fibre bounds: no factor of the number of fibres appears.

The only probabilistic input is the `LsBad` rate `c`; the harmonic rate `c'` is supplied per record
walker.  In particular `LsBad` measurability is *not* required (Section 2). -/
theorem measureReal_iUnion_band_inter_goodWinAllPairs_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ} {L : ℕ} (hL : 1 ≤ L)
    {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c c' : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hHarm : ∀ j : Fin N, (arrayMeasure N).real
      ((⋃ s0, band (N := N) p m r L s0) ∩ Harm (N := N) p m j V r T L) ≤
        Real.exp (-c' * xOf (Lw T L))) :
    (arrayMeasure N).real
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envQ p m V T L) +
        (N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envOsc p m T L)) := by
  set A : ℕ → Set (Array N) := fun n => ⋃ s0 ∈ Finset.range n,
    band (N := N) p m r L s0 ∩
      (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ with hA
  set U : ℕ → Set (Array N) := fun n => ⋃ s0 ∈ Finset.range n,
    band (N := N) p m r L s0 with hU
  have hAmono : Monotone A :=
    monotone_biUnion_range (fun s0 : ℕ =>
      band (N := N) p m r L s0 ∩
        (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ)
  have hUmono : Monotone U := monotone_biUnion_range (fun s0 : ℕ => band (N := N) p m r L s0)
  have hAt : Tendsto (fun n => (arrayMeasure N).real (A n)) atTop
      (𝓝 ((arrayMeasure N).real
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ))) := by
    have h := tendsto_measureReal_iUnion_atTop A hAmono
    rwa [iUnion_range_biUnion] at h
  have hUt : Tendsto (fun n => (arrayMeasure N).real (U n)) atTop
      (𝓝 ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0))) := by
    have h := tendsto_measureReal_iUnion_atTop U hUmono
    rwa [iUnion_range_biUnion] at h
  have hRt : Tendsto (fun n =>
        (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) *
            ((arrayMeasure N).real (U n) * envQ p m V T L) +
          (N : ℝ) * ((Lw T L : ℝ) * ((arrayMeasure N).real (U n) * envOsc p m T L))) atTop
      (𝓝 ((1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) *
            ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envQ p m V T L) +
          (N : ℝ) * ((Lw T L : ℝ) *
            ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envOsc p m T L)))) := by
    have h0 : Tendsto (fun _ : ℕ => (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L))) atTop
        (𝓝 ((1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)))) :=
      tendsto_const_nhds
    have h1 : Tendsto (fun n => ((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (U n) * envQ p m V T L)) atTop
        (𝓝 (((offDiag (N := N)).card : ℝ) *
          ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envQ p m V T L))) :=
      (hUt.mul_const _).const_mul _
    have h2 : Tendsto (fun n => (N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (U n) * envOsc p m T L))) atTop
        (𝓝 ((N : ℝ) * ((Lw T L : ℝ) *
          ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envOsc p m T L)))) :=
      ((hUt.mul_const _).const_mul _).const_mul _
    simpa only using (h0.add h1).add h2
  refine le_of_tendsto_of_tendsto' hAt hRt (fun n => ?_)
  exact measureReal_finset_iUnion_band_inter_goodWinAllPairs_compl_le (N := N) (p := p) (m := m)
    (C := C) hp1 hp2 hL hT hr hV1 hLsBad hHarm (Finset.range n)

/-! ### 7. The paper profile: carrier mass at most one, then absorption -/

/-- **The paper form with the total carrier mass replaced by `1`.**

`mu.real (⋃ s0 band s0) <= 1` is what replaces the `s0`-dependent carrier factor after summation;
the four pieces keep their multiplicities `1+N` (constant exponentials, one of them `LsBad`),
`card(offDiag)` (harmonic rate and `Qpl` Azuma price) and `N` (oscillation Azuma price). -/
theorem measureReal_iUnion_band_inter_goodWinAllPairs_compl_le_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ} {L : ℕ} (hL : 1 ≤ L)
    {T : ℕ} (hT : 1 ≤ T) {r : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c c' : ℝ}
    (hLsBad : (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))))
    (hHarm : ∀ j : Fin N, (arrayMeasure N).real
      ((⋃ s0, band (N := N) p m r L s0) ∩ Harm (N := N) p m j V r T L) ≤
        Real.exp (-c' * xOf (Lw T L))) :
    (arrayMeasure N).real
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
        ((offDiag (N := N)).card : ℝ) * envQ p m V T L +
        (N : ℝ) * ((Lw T L : ℝ) * envOsc p m T L) := by
  have hmain := measureReal_iUnion_band_inter_goodWinAllPairs_compl_le (N := N) (p := p) (m := m)
    (C := C) hp1 hp2 hL hT hr hV1 hLsBad hHarm
  have hD1 : (arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) ≤ 1 :=
    measureReal_iUnion_band_le_one (N := N) (p := p) (m := m) (r := r) (L := L)
  have hD0 : (0 : ℝ) ≤ (arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) :=
    measureReal_nonneg
  have henvQ0 : (0 : ℝ) ≤ envQ p m V T L := by rw [envQ]; positivity
  have henvOsc0 : (0 : ℝ) ≤ envOsc p m T L := by rw [envOsc]; positivity
  have hLw0 : (0 : ℝ) ≤ (Lw T L : ℝ) := by positivity
  have hc0 : (0 : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h1 : (arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envQ p m V T L ≤
      1 * envQ p m V T L := mul_le_mul_of_nonneg_right hD1 henvQ0
  have h2 : (Lw T L : ℝ) *
        ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envOsc p m T L) ≤
      (Lw T L : ℝ) * (1 * envOsc p m T L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD1 henvOsc0) hLw0
  have h3 : ((offDiag (N := N)).card : ℝ) *
        ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envQ p m V T L) ≤
      ((offDiag (N := N)).card : ℝ) * (1 * envQ p m V T L) :=
    mul_le_mul_of_nonneg_left h1 hc0
  have h4 : (N : ℝ) * ((Lw T L : ℝ) *
        ((arrayMeasure N).real (⋃ s0, band (N := N) p m r L s0) * envOsc p m T L)) ≤
      (N : ℝ) * ((Lw T L : ℝ) * (1 * envOsc p m T L)) :=
    mul_le_mul_of_nonneg_left h2 hN0
  linarith [hmain, h3, h4]

/-- **Paper-scale absorption of the summed all-pair bound.**

`LocOccFibreSum.paper_profile_absorb` collapses the single-fibre four-piece sum
`2 e^{-c x} + envQ + e^{-c' x} + Lw envOsc` to `C_T exp (-c_T L^{1/16})`; multiplying by the fixed
nonnegative weight `K = 1 + N + card(offDiag)` — which is where each per-fibre constant lives:
`1+N` constant exponentials, `card(offDiag)` per-pair prices, `N` per-walker prices — gives the same
profile for the summed bound.  `K` depends on `N, T` but not on `L` or `r`, exactly as the paper's
`C_T` allows. -/
theorem allPairs_profile_absorb {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {T : ℕ} (hT : 1 ≤ T) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * Real.exp (-c' * xOf (Lw T L)) +
          ((offDiag (N := N)).card : ℝ) * envQ p m (xOf (Lw T L)) T L +
          (N : ℝ) * ((Lw T L : ℝ) * envOsc p m T L) ≤
        (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hb⟩ :=
    paper_profile_absorb (p := p) hp1 hp2 (m := m) (T := T) hT hc hc'
  refine ⟨c_T, hc_T, C_T, hC_T, max L₀ 1, ?_⟩
  intro L hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hbound := hb L hL₀
  -- abbreviations (proof only)
  set E1 : ℝ := Real.exp (-c * xOf (Lw T L)) with hE1
  set E2 : ℝ := Real.exp (-c' * xOf (Lw T L)) with hE2
  set Q : ℝ := envQ p m (xOf (Lw T L)) T L with hQ
  set O : ℝ := envOsc p m T L with hO
  set Lwv : ℝ := (Lw T L : ℝ) with hLwv
  set S4 : ℝ := 2 * E1 + Q + E2 + Lwv * O with hS4
  set K : ℝ := 1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ) with hKdef
  have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
  have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
  have hQ0 : 0 ≤ Q := by rw [hQ, envQ]; positivity
  have hO0 : 0 ≤ O := by rw [hO, envOsc]; positivity
  have hLwv0 : 0 ≤ Lwv := by rw [hLwv]; positivity
  have hLO0 : 0 ≤ Lwv * O := mul_nonneg hLwv0 hO0
  have hcard0 : (0 : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by positivity
  have hNr0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKN : (1 + (N : ℝ)) ≤ K := by rw [hKdef]; linarith
  have hKc : ((offDiag (N := N)).card : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKNN : (N : ℝ) ≤ K := by rw [hKdef]; linarith
  -- termwise: each piece is bounded by the corresponding piece of `K * S4`
  have hterm1 : (1 + (N : ℝ)) * E1 ≤ K * (2 * E1) := by
    have h1 : (1 + (N : ℝ)) * E1 ≤ K * E1 := mul_le_mul_of_nonneg_right hKN hE10
    have h2 : K * E1 ≤ K * (2 * E1) := by
      apply mul_le_mul_of_nonneg_left _ hK0
      linarith
    linarith
  have hterm2 : ((offDiag (N := N)).card : ℝ) * E2 ≤ K * E2 :=
    mul_le_mul_of_nonneg_right hKc hE20
  have hterm3 : ((offDiag (N := N)).card : ℝ) * Q ≤ K * Q :=
    mul_le_mul_of_nonneg_right hKc hQ0
  have hterm4 : (N : ℝ) * (Lwv * O) ≤ K * (Lwv * O) :=
    mul_le_mul_of_nonneg_right hKNN hLO0
  have hG : (1 + (N : ℝ)) * E1 + ((offDiag (N := N)).card : ℝ) * E2 +
      ((offDiag (N := N)).card : ℝ) * Q + (N : ℝ) * (Lwv * O) ≤ K * S4 := by
    have hkey : (1 + (N : ℝ)) * E1 + ((offDiag (N := N)).card : ℝ) * E2 +
        ((offDiag (N := N)).card : ℝ) * Q + (N : ℝ) * (Lwv * O) ≤
        K * (2 * E1) + K * E2 + K * Q + K * (Lwv * O) := by
      linarith
    have hsum : K * (2 * E1) + K * E2 + K * Q + K * (Lwv * O) = K * S4 := by
      rw [hS4]; ring
    linarith
  have hboundS : S4 ≤ C_T * Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
    rw [hS4, hE1, hE2, hQ, hO, hLwv]
    exact hbound
  have hKS : K * S4 ≤ K * (C_T * Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16))) :=
    mul_le_mul_of_nonneg_left hboundS hK0
  have hfin : K * (C_T * Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16))) =
      (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
        Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
    rw [hKdef]; ring
  -- unfold the proof abbreviations in the two chain pieces, keeping `K * S4` opaque
  have hG' := hG
  rw [hE1, hE2, hQ, hO, hLwv] at hG'
  have hKS' := hKS
  rw [hfin] at hKS'
  exact le_trans hG' hKS'

/-- **The all-pair clock-union bound at paper scale.**

For `1/2 < p < 1`, `m >= 2`, `T >= 1` and a supplied `LsBad` rate `c > 0` there are `c_T > 0`,
`C_T >= 0` and `L₀` such that for every `L >= L₀` and every record level `r` with `(T+3) L <= r`,
the mass of the whole clock union of the all-pairs bad sets is at most

`(1 + N + card(offDiag N)) * C_T * exp (-c_T L^{1/16})`.

No measurability of `LsBad` is assumed; the harmonic `(locmax)` rate is supplied internally from
`LocOccFibreSum.measureReal_iUnion_band_inter_harm_le_exp`.  The carrier is the fibre union; see
Section 8 for the `ReachAll`-qualified defect-band form. -/
theorem exists_iUnion_allPairs_complement_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} {c : ℝ} (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (⋃ s0, band (N := N) p m r L s0 ∩
            (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
        (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c', hc', L₀', hharm⟩ :=
    measureReal_iUnion_band_inter_harm_le_exp (N := N) (p := p) hp1 hp2 (m := m) hm (T := T) hT
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀'', habs⟩ :=
    allPairs_profile_absorb (N := N) (p := p) hp1 hp2 (m := m) (T := T) hT hc hc'
  refine ⟨c_T, hc_T, C_T, hC_T, max (max L₀' L₀'') 1, ?_⟩
  intro L hLbound r hr hLsBad
  have hL : 1 ≤ L := le_trans (le_max_right _ 1) hLbound
  have hL' : L₀' ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbound
  have hL'' : L₀'' ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbound
  have hHarm : ∀ j : Fin N, (arrayMeasure N).real
      ((⋃ s0, band (N := N) p m r L s0) ∩
        Harm (N := N) p m j (xOf (Lw T L)) r T L) ≤ Real.exp (-c' * xOf (Lw T L)) :=
    fun j => hharm L hL' (r := r) (j := j) hr
  have hpaper := measureReal_iUnion_band_inter_goodWinAllPairs_compl_le_paper (N := N) (p := p)
    (m := m) (C := C) hp1 hp2 hL hT hr (V := xOf (Lw T L))
    (RecCarrierPaper.one_le_xOf_Lw T L) hLsBad hHarm
  have habs' := habs L hL''
  linarith

/-- `card (offDiag N) = N * (N - 1)`. -/
theorem card_offDiag_eq (N : ℕ) : (offDiag N).card = N * (N - 1) := by
  have h : offDiag N = (Finset.univ : Finset (Fin N)).offDiag := by
    ext q
    simp [LocOccAllPairs.offDiag, Finset.mem_offDiag]
  rw [h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib,
    mul_one]

/-- **The `offDiag`-factored form of the paper bound (`N >= 2`).**

For `N >= 2` one has `1 + N + card(offDiag N) <= 3 * card(offDiag N)`, so the previous bound reads
`card(offDiag N) * C_T' * exp (-c_T L^{1/16})` — the paper's `(lococc)` shape with the number of
ordered pairs factored out explicitly and `C_T'` independent of the pair, of `L` and of `r`. -/
theorem exists_iUnion_allPairs_complement_paper_offDiag
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) {C : ℝ} {c : ℝ} (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (⋃ s0, band (N := N) p m r L s0 ∩
            (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
        ((offDiag (N := N)).card : ℝ) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hb⟩ :=
    exists_iUnion_allPairs_complement_paper (N := N) (p := p) (m := m) hp1 hp2 hm (C := C) (c := c) hc
      (T := T) hT
  -- `card(offDiag N) = N (N-1) >= N` and `>= 2`
  have hcardN : (N : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by
    have h1 : N ≤ N * (N - 1) := by
      have h2 : 1 ≤ N - 1 := by omega
      calc N = N * 1 := by ring
        _ ≤ N * (N - 1) := Nat.mul_le_mul_left N h2
    have h3 : ((N : ℕ) : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [card_offDiag_eq]
    simpa using h3
  have hcard2 : (2 : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by
    have h2 : 2 ≤ N * (N - 1) := by
      have h3 : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
      simpa using h3
    have h4 : ((2 : ℕ) : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by exact_mod_cast h2
    rw [card_offDiag_eq]
    simpa using h4
  refine ⟨c_T, hc_T, 3 * C_T, by positivity, L₀, ?_⟩
  intro L hL r hr hLsBad
  have hmain := hb L hL hr hLsBad
  have hK : (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) ≤
      3 * ((offDiag (N := N)).card : ℝ) := by linarith
  have hE : (0 : ℝ) ≤ Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := (Real.exp_pos _).le
  have h1 : (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T ≤
      (3 * ((offDiag (N := N)).card : ℝ)) * C_T :=
    mul_le_mul_of_nonneg_right hK hC_T
  calc (arrayMeasure N).real
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ)
      ≤ (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := hmain
    _ = ((1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by ring
    _ ≤ ((3 * ((offDiag (N := N)).card : ℝ)) * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = ((offDiag (N := N)).card : ℝ) * (3 * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by ring

/-! ### 8. The `ReachAll` carrier distinction -/

/-- **On `ReachAll` the all-pair clock union sits inside the paper's defect band.**

The summation above is a statement about the fibre union `⋃ s0 band s0`, which is *not* the paper's
defect event off `ReachAll` (the record clock defaults to zero there).  Restricted to `ReachAll` the
fibre union is exactly `{d_r <= L}` (`LocOccRecordFibres.reachAll_inter_iUnion_recordPrefixBand_eq`),
so the all-pair bad set is a subset of the paper's defect band.  Kept separate on purpose: nothing
here identifies the two events off `ReachAll`. -/
theorem reachAll_inter_iUnion_bad_subset_defect {p : ℝ} {m r L T : ℕ} {C : ℝ}
    (hr0 : r ≠ 0) :
    ReachAll (N := N) p m ∩
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ⊆
      ReachAll (N := N) p m ∩
        {U : Array N | (defect (actX p m U) (recTimeA p m U) r).toNat ≤ L} := by
  intro U hU
  obtain ⟨hR, hUi⟩ := hU
  obtain ⟨s0, h1, -⟩ := Set.mem_iUnion.1 hUi
  refine ⟨hR, ?_⟩
  have heq := LocOccRecordFibres.reachAll_inter_iUnion_recordPrefixBand_eq (N := N) (p := p)
    (m := m) (r := r) (L := L) hr0
  have hmem : U ∈ ReachAll (N := N) p m ∩
      (⋃ s0, ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) :=
    ⟨hR, Set.mem_iUnion.2 ⟨s0, h1⟩⟩
  rw [heq] at hmem
  exact hmem.2

/-- **The `ReachAll` form of the all-pair clock-union bound.** -/
theorem exists_iUnion_allPairs_complement_paper_reachAll
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} {c : ℝ} (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LsBad (N := N) p m C r T L) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (ReachAll (N := N) p m ∩
            (⋃ s0, band (N := N) p m r L s0 ∩
              (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m C r T L s0)ᶜ)) ≤
        (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hb⟩ :=
    exists_iUnion_allPairs_complement_paper (N := N) (p := p) (m := m) hp1 hp2 hm (C := C) (c := c) hc
      (T := T) hT
  refine ⟨c_T, hc_T, C_T, hC_T, L₀, ?_⟩
  intro L hL r hr hLsBad
  exact le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _))
    (hb L hL hr hLsBad)

/-! ### 9. No supplied rate: the canonical constant `Ccan = |Mb| + 1` -/

/-- **The all-pair clock-union bound with the `LsBad` rate discharged.**

`LocOccSiteRate.exists_lsBad_rate_single_window` instantiates the `LsBad` rate at the paper's
canonical `C = Ccan p m = |Mb p (qOf p m)| + 1` (the constant `LocSumR1.array_locsum_h_start`
needs: `C >= 1`, `C > Mb`), with `c > 0` and `L₀` independent of `r`.  Composed with the summation
this removes the last free rate input: the statement below has no rate hypothesis at all. -/
theorem exists_iUnion_allPairs_complement_paper_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (⋃ s0, band (N := N) p m r L s0 ∩
            (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0)ᶜ) ≤
        (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c, hc, L₁, hL₁⟩ :=
    LocOccSiteRate.exists_lsBad_rate_single_window (N := N) hp1 hp2 (m := m) hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m) T
  obtain ⟨c_T, hc_T, C_T, hC_T, L₂, hL₂⟩ :=
    exists_iUnion_allPairs_complement_paper (N := N) (p := p) (m := m) hp1 hp2 hm
      (C := LocOccSiteRate.Ccan p m) (c := c) hc (T := T) hT
  refine ⟨c_T, hc_T, C_T, hC_T, max L₁ L₂, ?_⟩
  intro L hL r hr
  exact hL₂ L (le_trans (le_max_right _ _) hL) hr (hL₁ L (le_trans (le_max_left _ _) hL) hr)

/-- **Rate-free `offDiag`-factored form (`N >= 2`).**

The canonical constant and the paper profile together: no supplied rate, no measurability premise,
and the number of ordered pairs factored out explicitly. -/
theorem exists_iUnion_allPairs_complement_paper_canonical_offDiag
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N).real
          (⋃ s0, band (N := N) p m r L s0 ∩
            (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0)ᶜ) ≤
        ((offDiag (N := N)).card : ℝ) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hb⟩ :=
    exists_iUnion_allPairs_complement_paper_canonical (N := N) hp1 hp2 hm (T := T) hT
  have hcardN : (N : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by
    have h1 : N ≤ N * (N - 1) := by
      have h2 : 1 ≤ N - 1 := by omega
      calc N = N * 1 := by ring
        _ ≤ N * (N - 1) := Nat.mul_le_mul_left N h2
    have h3 : ((N : ℕ) : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [card_offDiag_eq]
    simpa using h3
  have hcard2 : (2 : ℝ) ≤ ((offDiag (N := N)).card : ℝ) := by
    have h2 : 2 ≤ N * (N - 1) := by
      have h3 : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
      simpa using h3
    have h4 : ((2 : ℕ) : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by exact_mod_cast h2
    rw [card_offDiag_eq]
    simpa using h4
  refine ⟨c_T, hc_T, 3 * C_T, by positivity, L₀, ?_⟩
  intro L hL r hr
  have hmain := hb L hL hr
  have hK : (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) ≤
      3 * ((offDiag (N := N)).card : ℝ) := by linarith
  have hE : (0 : ℝ) ≤ Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := (Real.exp_pos _).le
  have h1 : (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T ≤
      (3 * ((offDiag (N := N)).card : ℝ)) * C_T :=
    mul_le_mul_of_nonneg_right hK hC_T
  calc (arrayMeasure N).real
        (⋃ s0, band (N := N) p m r L s0 ∩
          (LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
            (LocOccSiteRate.Ccan p m) r T L s0)ᶜ)
      ≤ (1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := hmain
    _ = ((1 + (N : ℝ) + ((offDiag (N := N)).card : ℝ)) * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by ring
    _ ≤ ((3 * ((offDiag (N := N)).card : ℝ)) * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = ((offDiag (N := N)).card : ℝ) * (3 * C_T) *
          Real.exp (-c_T * (L : ℝ) ^ ((1 : ℝ) / 16)) := by ring

end LocOccAllPairFibreSum
