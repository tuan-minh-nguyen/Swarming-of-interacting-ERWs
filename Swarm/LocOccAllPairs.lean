/-
  # `(lococc)` for all walker pairs on one event

  `LocOccAllStarts.lococc_recordCarrier_allStarts` proves the paper's display at every start `s` of
  the window, but for one fixed ordered pair `(i,j)` and on an event that depends on that pair.
  The paper's `Proposition local` asserts `(lococc)` for *all* `i != j` simultaneously on one event
  `G_{r,L,T}`.  This module intersects the per-pair events over the finite set of ordered pairs of
  distinct walkers and sums the per-pair complement bounds, which is exactly the paper's union bound
  "for all martingales in the collection".
-/
import Swarm.LocOccAllStarts

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccAllPairs

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccCarrierAssembly
open SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-- The ordered pairs of *distinct* walkers; the paper's index set for `(lococc)`. -/
def offDiag (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun q => q.1 ≠ q.2)

theorem mem_offDiag {q : Fin N × Fin N} : q ∈ offDiag N ↔ q.1 ≠ q.2 := by
  simp [offDiag]

/-- **The paper's single event.**  Intersection of the per-pair events
`LocOccAllStarts.GoodAllStarts` over all ordered pairs of distinct walkers. -/
def GoodAllPairs (p : ℝ) (m : ℕ) (C : ℝ) (r T L s0 : ℕ) : Set (Array N) :=
  ⋂ q ∈ offDiag (N := N), GoodAllStarts p m q.1 q.2 C r T L s0

theorem goodAllPairs_subset {p : ℝ} {m : ℕ} {C : ℝ} {r T L s0 : ℕ}
    {q : Fin N × Fin N} (hq : q ∈ offDiag (N := N)) :
    GoodAllPairs (N := N) p m C r T L s0 ⊆ GoodAllStarts p m q.1 q.2 C r T L s0 :=
  Set.biInter_subset_of_mem hq

/-- **The paper's `(lococc)`, for all `i != j` and all starts of the window, on one event.**

This is the literal quantified statement of `Proposition local`'s display `(lococc)`: the carrier
encodes `{tau_r = s0} ∩ {d_r <= L}`, the time range is `s0 <= s <= t <= s0 + T L`, the walker pairs
range over all ordered pairs of distinct walkers with `i` the occupied walker and `j` the record
walker, and the right-hand side is the paper's record-dependent combination (no `T L + 3 L`
collapse away from `s0`). -/
theorem lococc_recordCarrier_allPairs
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
      U ∈ GoodAllPairs (N := N) p m C r T L s0 →
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
    have hp := lococc_recordCarrier_allStarts (N := N) hp1 hp2 hm hq hC1 hL hT
      (r := r) (s0 := s0) hr
      (fun U hU a b ha hb hab => hLsum q.2 U hU a b ha hb hab)
    filter_upwards [hp] with U hall hmem hU hgood s t h1 h2 h3
    exact hall s t hU (goodAllPairs_subset hqmem hgood) h1 h2 h3

/-- **The complement of the all-pairs event, as a finite sum of the paper's three masses.**

`(GoodAllPairs)^c` is covered by the union over the `N (N - 1)` ordered pairs of the per-pair bad
sets, so its carrier mass is at most the sum of the per-pair bounds: the `(locsum)`/`(locmax)`
exponential (repeated because it is charged through the carrier intersection for each pair), the
adapted Azuma term over the doubled window with both shifted residuals, and the site-window
oscillation term.  For fixed `N` this sum has `N (N - 1)` summands, which the paper absorbs into
`C_T`. -/
theorem measureReal_goodAllPairs_compl_le
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T)
    {r s0 : ℕ} (hr : (T + 3) * L ≤ r) {V : ℝ} (hV1 : 1 ≤ V) {w M : ℕ} (hw : 1 ≤ w)
    {c : ℝ} (hc : 0 ≤ c)
    (hLsBad : (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
      ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) :
    (arrayMeasure N).real
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodAllPairs (N := N) p m C r T L s0)ᶜ) ≤
      ∑ q ∈ offDiag (N := N),
        (2 * Real.exp (-c * xOf (Lw T L)) +
          ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((2 * (T * L) : ℕ) : ℝ) + 1) *
                Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
                  (4 * ((2 * (T * L) : ℕ) : ℝ) *
                    (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
            (arrayMeasure N).real
              (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                ShiftedQplResidual.shiftedContDefect p m q.1 q.2 s0 w M (2 * (T * L))) +
            (arrayMeasure N).real
              (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                QplWindow.harmDefect p m q.2 V w M)) +
          (Lw T L : ℝ) *
            ((arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
              (2 * (((T * L : ℕ) : ℝ) + 1) *
                Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                  (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2))))) := by
  have hsub : ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      (GoodAllPairs (N := N) p m C r T L s0)ᶜ ⊆
      ⋃ q ∈ offDiag (N := N),
        (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
          (GoodAllStarts p m q.1 q.2 C r T L s0)ᶜ) := by
    rintro U ⟨hUc, hbad⟩
    by_contra hcon
    exact hbad (Set.mem_biInter (fun q hq => by
      by_contra hqb
      exact hcon (Set.mem_biUnion hq ⟨hUc, hqb⟩)))
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le (μ := arrayMeasure N) (offDiag (N := N))
    (fun q => ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
      (GoodAllStarts p m q.1 q.2 C r T L s0)ᶜ)) ?_
  exact Finset.sum_le_sum (fun q hqmem =>
    measureReal_recordCarrier_allStarts_le (N := N) hp1 hp2 hm (i := q.1) (j := q.2)
      (mem_offDiag.1 hqmem) (C := C) hL hT hr hV1 hw hc hLsBad)


/-! ### 3. Packaging: only the compiled `(locsum)` scale hypothesis remains

`LocSumR1.array_locsum_h_start` supplies the exponential bound on `LsBad` and its pointwise
`(locsum)` content for *every* walker at the window `Lw T L`.  Both the display and the complement
sum below are therefore free of `hLsum`/`hLsBad`, leaving exactly the arithmetical start condition
`2 ellT (xOf (Lw T L)) <= A0 r T L` (automatic for large `r`, see
`LocOccCarrierAssembly.hbig_of_r`) and the numerical defects `V, w, M`. -/

theorem exists_lococc_recordCarrier_allPairs
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 : ℕ},
      (T + 3) * L ≤ r → 2 * ellT (xOf (Lw T L)) ≤ A0 r T L →
      ((arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
          ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) ∧
      (∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
        U ∈ GoodAllPairs (N := N) p m C r T L s0 →
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
                  + 4 / (1 - aRec p m)) * L34 L (Lw T L)) ∧
      (∀ {V : ℝ}, 1 ≤ V → ∀ {w M : ℕ}, 1 ≤ w →
        (arrayMeasure N).real
            (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
              (GoodAllPairs (N := N) p m C r T L s0)ᶜ) ≤
          ∑ q ∈ offDiag (N := N),
            (2 * Real.exp (-c * xOf (Lw T L)) +
              ((arrayMeasure N).real
                    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
                  (2 * (((2 * (T * L) : ℕ) : ℝ) + 1) *
                    Real.exp (-(((2 * L34 L (Lw T L)) / 2) ^ 2) /
                      (4 * ((2 * (T * L) : ℕ) : ℝ) *
                        (QplPredEnv.envB p m V (QplWindow.envC p m V)) ^ 2))) +
                (arrayMeasure N).real
                  (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                    ShiftedQplResidual.shiftedContDefect p m q.1 q.2 s0 w M (2 * (T * L))) +
                (arrayMeasure N).real
                  (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L ∩
                    QplWindow.harmDefect p m q.2 V w M)) +
              (Lw T L : ℝ) *
                ((arrayMeasure N).real
                    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L) *
                  (2 * (((T * L : ℕ) : ℝ) + 1) *
                    Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
                      (16 * ((T * L : ℕ) : ℝ) * (SiteHMax.capB p m (xOf (Lw T L))) ^ 2)))))) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
  intro r s0 hr hbig
  have hLLw : L₀ ≤ Lw T L := le_trans hL₀ (le_Lw T L)
  have hres := hL0 (Lw T L) hLLw (A0 r T L) hbig
  refine ⟨hres.1, ?_, ?_⟩
  · exact lococc_recordCarrier_allPairs (N := N) hp1 hp2 hm hC1 hL1 hT hr
      (fun j U hU a b ha hb hab => hres.2 U hU j a b ha hb hab)
  · intro V hV1 w M hw
    exact measureReal_goodAllPairs_compl_le (N := N) hp1 hp2 hm hL1 hT hr hV1 hw
      (le_of_lt hc) hres.1

end LocOccAllPairs
