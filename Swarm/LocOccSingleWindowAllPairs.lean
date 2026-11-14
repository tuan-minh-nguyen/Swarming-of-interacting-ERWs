/-
  # `(lococc)` for all ordered pairs on the paper's *single* window

  `LocOccSingleWindow` re-anchored the paper's `(lococc)` good event at the record time `s0`
  over the paper's own window `[s0, s0 + T L]` and proved, for one fixed ordered pair `(i,j)`,
  the every-start display and the raw three-mass carrier complement bound
  `measureReal_recordCarrier_singleWindow_le` (with the geometric `Qpl` residual
  `shiftedContDefect` *empty* on the carrier, unlike the doubled-window version).

  `LocOccAllPairs` intersected the *doubled-window* events over all ordered pairs.  This file does
  the same for the single-window event, so that the two improvements compose:

  * `GoodWinAllPairs` is the finite intersection of `GoodWin p m q.1 q.2 C r T L s0` over
    `q ∈ offDiag N`, i.e. over all ordered pairs of *distinct* walkers;
  * `lococc_recordCarrier_allPairs_singleWindow` : a.e. path, on the *same* event and at the
    *same* fixed record fibre `recordPrefixBand p m r s0 L`, `(lococc)` holds for every ordered
    pair and every pair of display times `s0 <= s <= t <= s0 + T L` — no pair-dependent event,
    no doubling of the window;
  * `measureReal_goodWinAllPairs_compl_le` : the complement mass at the fibre is at most the sum
    over ordered pairs of the single-window three-mass form (no `shiftedContDefect` residual);
  * `measureReal_goodWinAllPairs_compl_le_shared` sharpens the accounting in `N`: the
    `(locsum)`/`(locmax)` event `LsBad` (which does not depend on the pair at all) is charged
    *once*, the `Qpl` Azuma price is charged per ordered pair (it genuinely depends on `(i,j)`),
    and the site-window oscillation price is charged per record walker `j` (it does not depend
    on `i`), so the total is `(1+N)` copies of the `LsBad` exponential and `N` copies of the
    oscillation exponential instead of `N (N-1)` copies of each.  The harmonic `(locmax)`
    defect `harmDefect` still rides inside the per-pair `Qpl` budget;
  * `exists_singleWindow_complement_paper_uniform` records that the paper-scale constants
    `(c_T, C_T, L₀)` produced by `LocOccSingleWindow.exists_singleWindow_complement_paper` do
    *not* depend on the ordered pair;
  * `exists_singleWindow_allPairs_complement_paper` : at paper scale the all-pairs complement at
    the fibre is at most `(offDiag N).card * C_T * exp (-c_T L^(1/16))`, i.e. `C_T` may depend on
    `N` (here explicitly `N (N-1) * C_T`), which is all the paper's `C_T` is allowed to do.

  Scope (all explicit, nothing else is claimed):

  * Everything is *conditional on the fixed record fibre* `{tau_r = s0} ∩ {d_r <= L}`; the
    summation over the clock fibres `s0` is **not** performed here (that is m1's direction), and
    the fibre-coverage statement `⋃ s0 band s0 = {d_r <= L}` is not used.
  * `hLsBad` (the actual `(locsum)` exponential rate) is an *input* in every mass bound; its
    instantiation from the verified model is m4's direction.  The `(locsum)` *content*
    (`hLsum`) is likewise an explicit hypothesis of the display theorems, exactly as in
    `LocOccSingleWindow`.
  * The constant `C` in `(locsum)` is never required to be independent of `N`; `C_T` is not
    either.
  * No non-vacuity of `GoodWinAllPairs`, no later paper fields, no invariant measure, no speed.
-/
import Swarm.LocOccSingleWindow
import Swarm.LocOccAllPairs

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccSingleWindowAllPairs

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open SummedSlope.Model
open LocOccSingleWindow LocOccAllPairs

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The all-pairs single-window event -/

/-- **The paper's `(lococc)` event for all ordered pairs at once, on the paper's own window.**

Finite intersection of the per-pair single-window events `GoodWin` over the ordered pairs
`q = (i,j)` with `i != j`.  Each factor is anchored at the same record time `s0` and uses the
same window `[s0, s0 + T L]`; only `i, j` vary. -/
def GoodWinAllPairs (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) : Set (Array N) :=
  ⋂ q ∈ offDiag (N := N), GoodWin p m q.1 q.2 C r T L s0

/-- Membership in the all-pairs event, unfolded over the ordered pairs. -/
theorem mem_goodWinAllPairs {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ} {U : Array N} :
    U ∈ GoodWinAllPairs (N := N) p m C r T L s0 ↔
      ∀ q ∈ offDiag (N := N), U ∈ GoodWin p m q.1 q.2 C r T L s0 := by
  simp [GoodWinAllPairs]

/-- The all-pairs event implies each per-pair event. -/
theorem goodWinAllPairs_subset {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ}
    {q : Fin N × Fin N} (hq : q ∈ offDiag (N := N)) :
    GoodWinAllPairs (N := N) p m C r T L s0 ⊆ GoodWin p m q.1 q.2 C r T L s0 :=
  Set.biInter_subset_of_mem hq

/-- The all-pairs event is contained in the event of any single ordered pair of `Fin N`, when
that pair is off-diagonal — the form used for the per-pair display theorems. -/
theorem goodWinAllPairs_subset_of_ne {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    GoodWinAllPairs (N := N) p m C r T L s0 ⊆ GoodWin p m i j C r T L s0 := by
  intro U hU
  exact mem_goodWinAllPairs.1 hU (i, j) (mem_offDiag.2 hij)

/-! ### 2. The display, for every ordered pair and every display time of the window -/

/-- **The paper's `(lococc)` for all `i != j` at once on the single window.**

At the fixed record fibre `recordPrefixBand p m r s0 L`, on the single event
`GoodWinAllPairs`, every ordered pair `q` of distinct walkers satisfies `(lococc)` at every pair
of display times `s0 <= s <= t <= s0 + T L`, with the record-dependent right-hand side of
`LocOccSingleWindow.lococc_recordCarrier_allStarts_singleWindow` (no `T L + 3 L` collapse).

The only model-content hypothesis is `hLsum`, the pointwise `(locsum)` content of `LsBad` for
every walker `j`, exactly as supplied by `LocSumR1.array_locsum_h_start`. -/
theorem lococc_recordCarrier_allPairs_singleWindow
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodWinAllPairs (N := N) p m C r T L s0 →
      ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
          ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
              ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ))
                + (((runMax p m U q.1 s).toNat : ℝ) - (((trajectory p m U s).pos q.1).toNat : ℝ))
                + max 0 (((runMax p m U q.1 s).toNat : ℝ) - ((runMax p m U q.2 s).toNat : ℝ)))
            + ((t : ℝ) - (s : ℝ)) / 8
            + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  rw [ae_all_iff]
  intro q
  by_cases hq : q.1 = q.2
  · filter_upwards with U hmem
    exact absurd hq (mem_offDiag.1 hmem)
  · have hqmem : q ∈ offDiag (N := N) := mem_offDiag.2 hq
    have hp := lococc_recordCarrier_allStarts_singleWindow (N := N) hp1 hp2 hm hq hC1 hL hT
      (r := r) (s0 := s0) hr
      (fun U hU a b ha hb hab => hLsum q.2 U hU a b ha hb hab)
    filter_upwards [hp] with U hall hmem hU hgood s t h1 h2 h3
    exact hall s t hU (goodWinAllPairs_subset hqmem hgood) h1 h2 h3

/-- **The collapsed `T L + 3 L` form of the all-pairs display at the record start `s0`.**

Same event and fibre as `lococc_recordCarrier_allPairs_singleWindow`, with the display started at
the record time itself; the record-carrier geometry
(`LocOccCarrierAssembly.record_geometry`) bounds the record-dependent factor by `T L + 3 L` for
every ordered pair simultaneously. -/
theorem lococc_recordCarrier_TL_allPairs_singleWindow
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodWinAllPairs (N := N) p m C r T L s0 →
      ∀ t : ℕ, s0 ≤ t → t ≤ s0 + T * L →
        ∑ u ∈ Finset.Ico s0 t,
            (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
          ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) * (((T * L : ℕ) : ℝ) + 3 * (L : ℝ))
            + ((t : ℝ) - (s0 : ℝ)) / 8
            + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                + 4 / (1 - aRec p m)) * L34 L (Lw T L) := by
  rw [ae_all_iff]
  intro q
  by_cases hq : q.1 = q.2
  · filter_upwards with U hmem
    exact absurd hq (mem_offDiag.1 hmem)
  · have hqmem : q ∈ offDiag (N := N) := mem_offDiag.2 hq
    have hp := lococc_recordCarrier_allStarts_singleWindow (N := N) hp1 hp2 hm hq hC1 hL hT
      (r := r) (s0 := s0) hr
      (fun U hU a b ha hb hab => hLsum q.2 U hU a b ha hb hab)
    filter_upwards [hp] with U hall hmem hU hgood t hst htT
    -- the record-start display, then the record-carrier geometry for every pair at once
    have h0 := hall s0 t hU (goodWinAllPairs_subset hqmem hgood) (le_refl s0) hst htT
    have h2 := record_geometry (N := N) hU hr q.1 q.2 hst htT
    have hcoef : (0 : ℝ) ≤ (2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1 := by
      have h1 := Lc_nonneg (p := p) (m := m) hp1 hp2
      have h2 := CJc_nonneg (p := p) (m := m) hp1 hp2
      have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
      nlinarith
    have h3 : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
        ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s0).toNat : ℝ))
          + (((runMax p m U q.1 s0).toNat : ℝ)
              - (((trajectory p m U s0).pos q.1).toNat : ℝ))
          + max 0 (((runMax p m U q.1 s0).toNat : ℝ) - ((runMax p m U q.2 s0).toNat : ℝ)))
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            (((T * L : ℕ) : ℝ) + 3 * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 hcoef
    linarith

/-! ### 3. The three named prices of the single-window budget

The single-window complement bound of `LocOccSingleWindow` has three explicit pieces.  Naming them
is what makes the all-pairs accounting legible: the first does not depend on the pair at all, the
second depends on the record walker `j` only, the third on the occupied walker `i` only through
`Qpl`. -/

/-- The carrier mass at the fixed record fibre `{tau_r = s0} ∩ {d_r <= L}`. -/
noncomputable def winCarr (p : ℝ) (m : ℕ) (r T L s0 : ℕ) : ℝ :=
  (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)

/-- The carrier-weighted maximal-Azuma price of the adapted `Qpl` drop over the paper's window
`[s0, s0 + T L]`.  This is the only term in the single-window budget that genuinely depends on
both walkers of the pair. -/
noncomputable def winAzuma (p : ℝ) (m : ℕ) (r T L s0 : ℕ) (V : ℝ) : ℝ :=
  winCarr (N := N) p m r T L s0 *
    (2 * (((T * L : ℕ) : ℝ) + 1) *
      Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
        (4 * ((T * L : ℕ) : ℝ) * (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2)))

/-- The carrier-weighted site-window oscillation price at threshold `L^{3/4}`.  It depends on the
record walker `j` only through the *excluded set* `OscSup p m j r T L s0`, not through its price:
the numerical value below is the same for every `j`. -/
noncomputable def winOsc (p : ℝ) (m : ℕ) (r T L s0 : ℕ) : ℝ :=
  (Lw T L : ℝ) *
    (winCarr (N := N) p m r T L s0 *
      (2 * (((T * L : ℕ) : ℝ) + 1) *
        Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
          (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))))

/-- The harmonic `(locmax)` defect of the record walker `j` on the carrier — the only surviving
residual of the single-window analysis. -/
noncomputable def winHarm (p : ℝ) (m : ℕ) (r T L s0 : ℕ) (V : ℝ) (j : Fin N) : ℝ :=
  (arrayMeasure N).real
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      QplWindow.harmDefect p m j V (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L))

/-- **The public per-pair single-window bound, in named-term form.**

Verbatim `LocOccSingleWindow.measureReal_recordCarrier_singleWindow_le`, with the two carrier
products and the harmonic defect replaced by `winAzuma`, `winOsc`, `winHarm`. -/
theorem measureReal_recordCarrier_singleWindow_le_terms
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodWin p m i j C r T L s0)ᶜ) ≤
      2 * Real.exp (-c * xOf (Lw T L))
        + (winAzuma (N := N) p m r T L s0 V + winHarm (N := N) p m r T L s0 V j)
        + winOsc (N := N) p m r T L s0 := by
  have h := measureReal_recordCarrier_singleWindow_le (N := N) hp1 hp2 (m := m) (i := i) (j := j)
    (C := C) hL hT (r := r) (s0 := s0) hr (V := V) hV1 hc hLsBad
  unfold winAzuma winHarm winOsc winCarr
  linarith [h]

/-- **The `Qpl` drop on the carrier costs one Azuma price plus the record walker's harmonic
defect.**  `LocOccSingleWindow`'s proof of the single-window budget uses exactly this bound
internally (`CarrierQplResidual.measureReal_recordCarrier_qplDrop_singleResidual`); it is exposed
here because the all-pairs union is taken over the drop sets, not over the composite events. -/
theorem measureReal_carrier_qplDrop_le_terms
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s0 (T * L)
            (2 * L34 L (Lw T L))) ≤
      winAzuma (N := N) p m r T L s0 V + winHarm (N := N) p m r T L s0 V j := by
  have hTL1 : 1 ≤ T * L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hA0 : (T + 2) * L ≤ r := le_trans (Nat.mul_le_mul_right L (by omega : T + 2 ≤ T + 3)) hr
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper hT hL hr
  have hL34pos : 0 < L34 L (Lw T L) := by linarith [one_le_L34 (L := L) (Lw := Lw T L) hL]
  have h := CarrierQplResidual.measureReal_recordCarrier_qplDrop_singleResidual (N := N)
    hp1 hp2 m (1 / 8) i j (by norm_num) (r := r) (s := s0) (T := T) (L := L) (n := T * L)
    hTL1 le_rfl hA0 hA1 hV1 (KQ := 2) (by norm_num) hL34pos
  -- `hA1` of the citation above is `1 ≤ cA r T L`, supplied by `cA_hyp_of_paper`
  clear hTL1 hL34pos
  unfold winAzuma winHarm winCarr
  linarith [h]

/-- **The site-window oscillation on the carrier costs one oscillation price plus one `LsBad`
exponential**, the latter because `LocOccAllStarts.measureReal_oscSup_le` charges its truncation
residual through `LsBad`. -/
theorem measureReal_carrier_oscSup_le_terms
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r)
    {c : ℝ} (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m j r T L s0) ≤
      winOsc (N := N) p m r T L s0 + Real.exp (-c * xOf (Lw T L)) := by
  have h := LocOccAllStarts.measureReal_oscSup_le (N := N) hp1 hp2 (m := m) (i := i) (j := j)
    (C := C) hL hT (r := r) (s0 := s0) hr
  have hls : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  unfold winOsc winCarr
  linarith [h, hls]

/-! ### 4. The joint carrier complement: finite union over the ordered pairs -/

/-- **Failure of the all-pairs event is failure of at least one pair's event.**

Since `GoodWinAllPairs` is an intersection over the (finitely many) ordered pairs, its complement
inside the record fibre is covered by the union over those pairs of the single-pair bad sets.  No
summation over the record clock `s0` occurs here: the fibre is fixed. -/
theorem carrier_fail_subset_goodWinAllPairs {p : ℝ} {m r s0 L T : ℕ} {C : ℝ} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ ⊆
      ⋃ q ∈ offDiag (N := N),
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodWin p m q.1 q.2 C r T L s0)ᶜ) := by
  rintro U ⟨hUc, hbad⟩
  by_contra hcon
  exact hbad (Set.mem_biInter (fun q hq => by
    by_contra hqb
    exact hcon (Set.mem_biUnion hq ⟨hUc, hqb⟩)))

/-- **The all-pairs complement at the fibre is at most the sum of the per-pair single-window
budgets.**

Each summand is exactly `LocOccSingleWindow`'s raw three-mass form at the *same* fixed fibre: the
`(locsum)`/`(locmax)` exponential `2 exp(-c xOf Lw)` (charged once per ordered pair here), the
carrier-weighted adapted-Azuma price of the `Qpl` drop over the paper's window, the harmonic
`(locmax)` defect of the record walker, and the site-window oscillation price.  There is **no**
`shiftedContDefect` term: at the paper's single window it is empty on the carrier. -/
theorem measureReal_goodWinAllPairs_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      ∑ q ∈ offDiag (N := N),
        (2 * Real.exp (-c * xOf (Lw T L))
          + (winAzuma (N := N) p m r T L s0 V + winHarm (N := N) p m r T L s0 V q.2)
          + winOsc (N := N) p m r T L s0) := by
  refine le_trans (measureReal_mono_array
    (carrier_fail_subset_goodWinAllPairs (N := N) (p := p) (m := m) (r := r) (s0 := s0)
      (L := L) (T := T) (C := C)) (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) (offDiag (N := N))
    (fun q => ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      (GoodWin p m q.1 q.2 C r T L s0)ᶜ)) ?_
  exact Finset.sum_le_sum (fun q hqmem =>
    measureReal_recordCarrier_singleWindow_le_terms (N := N) hp1 hp2 (i := q.1) (j := q.2)
      (C := C) hL hT hr hV1 hc hLsBad)

/-! ### 5. Sharpening the accounting in `N`: shared sets are charged once

The per-pair sum above charges the pair-independent `LsBad` exponential `N (N-1)` times and the
oscillation price `N (N-1)` times.  But `LsBad` does not depend on the pair at all, and
`OscSup p m j r T L s0` depends on the pair only through the record walker `j`.  Taking the union
over ordered pairs before measuring charges `LsBad` once and the oscillation price at most once
per record walker.  What remains genuinely per-pair is the `Qpl` Azuma price (and, inside it, the
harmonic `(locmax)` defect of `j`). -/

/-- **Failure set with the shared masses separated.** -/
theorem carrier_fail_subset_goodWinAllPairs_shared {p : ℝ} {m r s0 L T : ℕ} {C : ℝ} :
    ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ ⊆
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ∪
        ((⋃ q ∈ offDiag (N := N),
            ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
                (2 * L34 L (Lw T L))) ∪
          (⋃ q ∈ offDiag (N := N),
            ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              OscSup p m q.2 r T L s0)) := by
  rintro U ⟨hU, hbad⟩
  by_cases hls : U ∈ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)
  · exact Or.inl ⟨hU, hls⟩
  by_cases hq : ∃ q ∈ offDiag (N := N),
      U ∈ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
        (2 * L34 L (Lw T L))
  · obtain ⟨q, hqmem, hqU⟩ := hq
    exact Or.inr (Or.inl (Set.mem_biUnion hqmem ⟨hU, hqU⟩))
  by_cases ho : ∃ q ∈ offDiag (N := N), U ∈ OscSup p m q.2 r T L s0
  · obtain ⟨q, hqmem, hoU⟩ := ho
    exact Or.inr (Or.inr (Set.mem_biUnion hqmem ⟨hU, hoU⟩))
  · exact absurd (mem_goodWinAllPairs.2 (fun q hqmem =>
      goodWin_iff.2 ⟨hls, (fun hd => hq ⟨q, hqmem, hd⟩), (fun hd => ho ⟨q, hqmem, hd⟩)⟩)) hbad

/-- **The sharpened all-pairs complement bound.**

Compared with `measureReal_goodWinAllPairs_compl_le_explicit` the copies of the pair-independent
`LsBad` exponential drop from `2 N (N-1)` to `1 + N`, and the copies of the oscillation price from
`N (N-1)` to `N`; the `Qpl` Azuma price is still charged once per ordered pair (it depends on both
walkers) and the harmonic defect once per ordered pair (it rides inside the `Qpl` budget). -/
theorem measureReal_goodWinAllPairs_compl_le_shared
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      (1 + (N : ℝ)) * Real.exp (-c * xOf (Lw T L))
        + (∑ q ∈ offDiag (N := N),
            (winAzuma (N := N) p m r T L s0 V + winHarm (N := N) p m r T L s0 V q.2))
        + (N : ℝ) * winOsc (N := N) p m r T L s0 := by
  -- abbreviations for the three masses
  have hEpos : (0 : ℝ) ≤ Real.exp (-c * xOf (Lw T L)) := (Real.exp_pos _).le
  -- (a) the LsBad mass, charged once
  have hA : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤ Real.exp (-c * xOf (Lw T L)) := by
    refine le_trans (measureReal_mono_array Set.inter_subset_right (measure_ne_top _ _)) ?_
    exact measureReal_le_of_measure_le_ofReal (le_of_lt (Real.exp_pos _)) hLsBad
  -- (b) the Qpl drops, per ordered pair
  have hB : (arrayMeasure N).real
      (⋃ q ∈ offDiag (N := N),
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
            (2 * L34 L (Lw T L)))
      ≤ ∑ q ∈ offDiag (N := N),
          (winAzuma (N := N) p m r T L s0 V + winHarm (N := N) p m r T L s0 V q.2) := by
    refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) (offDiag (N := N))
      (fun q => ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
          (2 * L34 L (Lw T L)))) ?_
    exact Finset.sum_le_sum (fun q _ =>
      measureReal_carrier_qplDrop_le_terms (N := N) hp1 hp2 (i := q.1) (j := q.2) hL hT hr hV1)
  -- (c) the oscillation, charged at most once per record walker `j`
  have hCsub : (⋃ q ∈ offDiag (N := N),
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m q.2 r T L s0) ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin N)),
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m j r T L s0) := by
    intro U hU
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop] at hU ⊢
    obtain ⟨q, -, h1, h2⟩ := hU
    exact ⟨q.2, Finset.mem_univ _, h1, h2⟩
  have hC : (arrayMeasure N).real
      (⋃ q ∈ offDiag (N := N),
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m q.2 r T L s0)
      ≤ (N : ℝ) * winOsc (N := N) p m r T L s0 + (N : ℝ) * Real.exp (-c * xOf (Lw T L)) := by
    have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
    refine le_trans (measureReal_mono_array hCsub (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N)
      (Finset.univ : Finset (Fin N))
      (fun j => ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        OscSup p m j r T L s0)) ?_
    have hterm : ∀ j : Fin N,
        (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            OscSup p m j r T L s0)
        ≤ winOsc (N := N) p m r T L s0 + Real.exp (-c * xOf (Lw T L)) :=
      fun j => measureReal_carrier_oscSup_le_terms (N := N) hp1 hp2 (i := j) (j := j)
        (C := C) hL hT hr hLsBad
    refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  -- assemble
  have hsub := carrier_fail_subset_goodWinAllPairs_shared (N := N) (p := p) (m := m) (r := r)
    (s0 := s0) (L := L) (T := T) (C := C)
  have hstep1 : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ)
      ≤ (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) +
        ((arrayMeasure N).real
            (⋃ q ∈ offDiag (N := N),
              ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
                  (2 * L34 L (Lw T L))) +
          (arrayMeasure N).real
            (⋃ q ∈ offDiag (N := N),
              ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                OscSup p m q.2 r T L s0)) := by
    refine le_trans (measureReal_mono_array hsub (measure_ne_top _ _)) ?_
    have hu1 := measureReal_union_le (μ := arrayMeasure N)
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        LocSumR1.LsBad N p m C (Lw T L) (A0 r T L))
      ((⋃ q ∈ offDiag (N := N),
          ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
              (2 * L34 L (Lw T L))) ∪
        (⋃ q ∈ offDiag (N := N),
          ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            OscSup p m q.2 r T L s0))
    have hu2 := measureReal_union_le (μ := arrayMeasure N)
      (⋃ q ∈ offDiag (N := N),
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) q.1 q.2) s0 (T * L)
            (2 * L34 L (Lw T L)))
      (⋃ q ∈ offDiag (N := N),
        ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          OscSup p m q.2 r T L s0)
    linarith [hu1, hu2]
  nlinarith [hstep1, hA, hB, hC]


/-! ### 6. The paper-scale constant is *uniform in the ordered pair*

`LocOccSingleWindow.exists_singleWindow_complement_paper` produces, for each fixed pair `(i,j)`,
constants `(c_T, C_T, L₀)` with `mass (band ∩ (GoodWin i j)ᶜ) ≤ C_T exp (-c_T L^{1/16})`.
For the all-pairs union bound we need one triple that works for all pairs at once.  This is a
strict logical strengthening (`∀ i j ∃ c_T C_T L₀` becomes `∃ c_T C_T L₀ ∀ i j`), and it holds:
in the proof below none of the chosen constants touches `i` or `j` — they are built from
`min c c'`, `T`, `RecCarrierPaper.Kb p m`, `SiteHMax.Cproj p m`, the harmonic rate `c'` of
`CarrierQplResidual.measureReal_carrier_harmDefect_le_exp` and the arithmetic envelope `K3`, all
independent of the pair.  The only `i, j`-dependent ingredient is the per-pair raw bound
`measureReal_recordCarrier_singleWindow_le`, invoked at the end.

(The proof is the proof of the public theorem with `i j` moved inside the quantifiers; the
exponent bookkeeping `azuma_exp_arg_ge`, `osc_exp_arg_ge`, `pow_mul_exp_neg_absorb` and the
harmonic rate are those already verified in `RecordCarrierPaperScale` / `CarrierQplResidual`.)
-/
theorem exists_singleWindow_complement_paper_uniform
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C c : ℝ} (hC1 : 1 ≤ C) (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      ∀ (i j : Fin N),
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (GoodWin p m i j C r T L s0)ᶜ) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  -- the harmonic rate of `CarrierQplResidual`
  obtain ⟨c', hc', L₀', hb'⟩ :=
    CarrierQplResidual.measureReal_carrier_harmDefect_le_exp (N := N) hp1 hp2 hm T hT
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
  refine ⟨b / 2, by linarith, K3 * (((48).factorial : ℝ) / (b / 2) ^ 48), ?_, max L₀' 1, ?_⟩
  · have hfac : (0 : ℝ) < (((48).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos 48
    have hb2' : (0 : ℝ) < (b / 2) ^ 48 := pow_pos (by linarith) 48
    positivity
  intro L hLbound r s0 hr hLsBad i j
  have hL : 1 ≤ L := le_trans (le_max_right L₀' 1) hLbound
  have hL₀' : L₀' ≤ L := le_trans (le_max_left L₀' 1) hLbound
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper hT hL hr
  -- the single-window union bound with `V = xOf Lw`
  have hmain := measureReal_recordCarrier_singleWindow_le (N := N) hp1 hp2 (m := m) (i := i)
    (j := j) (C := C) hL hT (r := r) (s0 := s0) hr (V := xOf (Lw T L))
    (RecCarrierPaper.one_le_xOf_Lw T L) hc.le hLsBad
  -- the harmonic residual, at the paper window
  have hharmraw := hb' (r := r) (s := s0) (L := L) (j := j) hL₀' hA1
  have hharmdefeq : QplWindow.harmDefect p m j (xOf (CarrierQplResidual.cLw T L))
      (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L)
      = QplWindow.harmDefect p m j (xOf (Lw T L))
        (CarrierQplResidual.cA r T L) (CarrierQplResidual.cM T L) := by
    rw [show CarrierQplResidual.cLw T L = Lw T L from rfl]
  rw [hharmdefeq] at hharmraw
  -- abbreviations
  set Lr : ℝ := (L : ℝ) ^ (1 / 16 : ℝ) with hLrdef
  set E : ℝ := QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
    with hEdef
  set B : ℝ := SiteHMax.capB p m (xOf (Lw T L)) with hBdef
  set A : ℝ := (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
    with hAdef
  set harm : ℝ := (arrayMeasure N).real
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      QplWindow.harmDefect p m j (xOf (Lw T L)) (CarrierQplResidual.cA r T L)
        (CarrierQplResidual.cM T L)) with hharmdef
  have hharm : harm ≤ Real.exp (-c' * xOf (Lw T L)) := by
    rw [hharmdef]; exact hharmraw
  have hA0' : 0 ≤ A := by rw [hAdef]; exact measureReal_nonneg
  have hA1' : A ≤ 1 := by rw [hAdef]; exact measureReal_le_one
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
  have hharm' : harm ≤ Real.exp (-b * Lr) := le_trans hharm hharm2
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
  have hprodA : A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) ≤
      (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hAz (Real.exp_pos _).le (by norm_num)
    calc A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)))
        = (2 * ((((T * L : ℕ)) : ℝ) + 1)) *
            (A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
              (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) := by ring
      _ ≤ (2 * ((((T * L : ℕ)) : ℝ) + 1)) * (1 * Real.exp (-b * Lr)) :=
          mul_le_mul_of_nonneg_left h1 hcoef
      _ = (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by ring
  have hprodO : (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
        Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)))) ≤
      ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
          (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hOsc (Real.exp_pos _).le (by norm_num)
    calc (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
          Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))))
        = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
            (A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
              (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))) := by ring
      _ ≤ ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * (1 * Real.exp (-b * Lr)) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by ring
  have hsum : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
        (GoodWin p m i j C r T L s0)ᶜ) ≤
      (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) +
          (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    nlinarith [hmain, hterm1, hharm', hprodA, hprodO]
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
  linarith [hsum, hfinal]

/-! ### 7. The all-pairs paper-scale remainder at the fixed record fibre -/

/-- **The all-pairs complement at the fibre, at paper scale.**

For `1/2 < p < 1`, `m >= 2`, `T >= 1` there are `c_T > 0`, `C_T >= 0` and `L₀` such that for every
`L >= L₀`, every record level `r` with `(T+3) L <= r` and every fibre index `s0`, if the verified
`(locsum)`/`(locmax)` event `LsBad` has the exponential rate `exp (-c * xOf (Lw T L))`, then the
carrier mass of the complement of the *all-pairs* single-window event at the fibre is at most

`(offDiag N).card * C_T * exp (-c_T L^{1/16})`, i.e. `N (N-1) C_T exp (...)`

with `c_T`, `C_T` **independent of the ordered pair** (Section 6) and `C_T` allowed to depend on
`N` — here explicitly through the factor `N (N-1)`.  Note `xOf (Lw T L) >= L^{1/16}` up to the
record window, which is where the stretched-exponential rate comes from. -/
theorem exists_singleWindow_allPairs_complement_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C c : ℝ} (hC1 : 1 ≤ C) (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
        ((offDiag (N := N)).card : ℝ) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀, hL₀⟩ :=
    exists_singleWindow_complement_paper_uniform (N := N) hp1 hp2 hm hC1 hc hT
  refine ⟨c_T, hc_T, C_T, hC_T, L₀, ?_⟩
  intro L hL r s0 hr hLsBad
  have hsub := carrier_fail_subset_goodWinAllPairs (N := N) (p := p) (m := m) (r := r)
    (s0 := s0) (L := L) (T := T) (C := C)
  refine le_trans (measureReal_mono_array hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) (offDiag (N := N))
    (fun q => ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      (GoodWin p m q.1 q.2 C r T L s0)ᶜ)) ?_
  have hper : ∀ q ∈ offDiag (N := N),
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (GoodWin p m q.1 q.2 C r T L s0)ᶜ) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) :=
    fun q _ => hL₀ L hL hr hLsBad q.1 q.2
  refine le_trans (Finset.sum_le_sum hper) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_assoc]

/-- **Capstone: the paper's `(lococc)` for all ordered pairs on one event, with its probability
bound, at a fixed record fibre.**

Everything the single-window analysis can currently give for *all* pairs simultaneously, at the
fibre `{tau_r = s0} ∩ {d_r <= L}`:

* one event `GoodWinAllPairs` (finite intersection over the ordered off-diagonal pairs of the
  single-window events `GoodWin`, whose `Qpl` exclusion is anchored at `s0` over `T L`, not `2 T L`);
* the display `(lococc)` for every ordered pair `q` and every pair of display times
  `s0 <= s <= t <= s0 + T L`, with the record-dependent right-hand side;
* the carrier mass of the complement at the fibre, at paper scale
  `N (N-1) C_T exp (-c_T L^{1/16})`.

Not claimed: the summation over the record fibres `s0` (m1), the instantiation of the `LsBad`
rate from the model (m4), non-vacuity of the intersection, and any later paper field. -/
theorem singleWindow_allPairs_at_fibre
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C c : ℝ} (hC1 : 1 ≤ C) (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s0 : ℕ}, (T + 3) * L ≤ r →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (∀ (j : Fin N) (U : Array N),
        U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
        ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
          ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) →
      ((arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
            (GoodWinAllPairs (N := N) p m C r T L s0)ᶜ) ≤
        ((offDiag (N := N)).card : ℝ) * C_T *
          Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)))
      ∧ (∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
          U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
          U ∈ GoodWinAllPairs (N := N) p m C r T L s0 →
          ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
            ∑ u ∈ Finset.Ico s t,
                (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
              ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
                  ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ))
                    + (((runMax p m U q.1 s).toNat : ℝ)
                        - (((trajectory p m U s).pos q.1).toNat : ℝ))
                    + max 0 (((runMax p m U q.1 s).toNat : ℝ)
                        - ((runMax p m U q.2 s).toNat : ℝ)))
                + ((t : ℝ) - (s : ℝ)) / 8
                + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
                    + 4 / (1 - aRec p m)) * L34 L (Lw T L)) := by
  obtain ⟨c_T, hc_T, C_T, hC_T, L₁, hL₁⟩ :=
    exists_singleWindow_allPairs_complement_paper (N := N) hp1 hp2 hm hC1 hc hT
  refine ⟨c_T, hc_T, C_T, hC_T, max L₁ 1, ?_⟩
  intro L hLbound r s0 hr hLsBad hLsum
  have hL1 : L₁ ≤ L := le_trans (le_max_left L₁ 1) hLbound
  have hL : 1 ≤ L := le_trans (le_max_right L₁ 1) hLbound
  exact ⟨hL₁ L hL1 hr hLsBad,
    lococc_recordCarrier_allPairs_singleWindow (N := N) hp1 hp2 hm hC1 hL hT hr hLsum⟩
