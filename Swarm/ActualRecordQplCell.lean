/-
Literal actual-record `Qpl` cells, using the focused record filtration core.

The first theorem is exact but explicitly conditional on `ReachAll` being
adapted at the candidate time. The second needs no such hypothesis: at a
positive candidate time it charges the larger adapted first-hit prefix. Both
retain the genuine predictable carrier, its increment envelope, and its
complement term; neither constructs a cosmetic carrier or an `AdvanceClause`.
-/
import Swarm.ActualRecordFiltration
import Swarm.QplWeightedCell

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Classical
open scoped BigOperators ENNReal
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmRecordMeas.Actual
open ShiftedAdvance

namespace ActualRecordQplCell

open ActualRecordFiltration

variable {N : ℕ} [Nonempty (Fin N)]

/-- Exact literal `Qpl` record-cell estimate when `ReachAll` is measurable at
the candidate time. This is the only extra start-filtration input; all genuine
predictable-carrier hypotheses and the entire suffix window are retained. -/
theorem measureReal_qpl_recTimeA_cell_le_of_reachAll {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (hε : 0 < eps) {r s : ℕ} (hr : 1 ≤ r)
    (hR : MeasurableSet[Swarming.Enl.enlFilt p m s] (ReachAll (N := N) p m))
    {A : Set (Array N)} (hA : MeasurableSet[Swarming.Enl.enlFilt p m s] A)
    {G : ℕ → Set (Array N)}
    (hG : ∀ k, MeasurableSet[Swarming.Enl.enlFilt p m (s + k)] (G k))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.projInc p m eps i j (s + k) U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell
        (Swarming.Enl.ProjLedger.Qpl p m eps i j)
        (fun U => recTimeA p m U r) n δ s) ≤
      (arrayMeasure N).real (A ∩ {U | recTimeA p m U r = s}) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      (arrayMeasure N).real ((A ∩ {U | recTimeA p m U r = s}) ∩
        {U | ∃ k < n, U ∉ G k}) := by
  exact QplWeightedCell.measureReal_qpl_oscStartCell_le_of_ptrunc
    hp0 hp1 m eps i j hε hA
    (measurableSet_recTimeA_eq_of_reachAll p m hr hR) hG hC hbdd hn hδ

/-- Unconditional conservative literal-`Qpl` estimate at a positive record
candidate. The true record cell is bounded using only the adapted first-hit
prefix; no adaptedness of the zero-defaulted `recTimeA` is asserted. -/
theorem measureReal_qpl_recTimeA_cell_le_prefix {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (hε : 0 < eps) {r s : ℕ} (hs : 1 ≤ s) {A : Set (Array N)}
    (hA : MeasurableSet[Swarming.Enl.enlFilt p m s] A)
    {G : ℕ → Set (Array N)}
    (hG : ∀ k, MeasurableSet[Swarming.Enl.enlFilt p m (s + k)] (G k))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.projInc p m eps i j (s + k) U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell
        (Swarming.Enl.ProjLedger.Qpl p m eps i j)
        (fun U => recTimeA p m U r) n δ s) ≤
      (arrayMeasure N).real (A ∩ firstRecordAt p m r s) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      (arrayMeasure N).real ((A ∩ firstRecordAt p m r s) ∩
        {U | ∃ k < n, U ∉ G k}) := by
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  let B : Set (Array N) := A ∩ firstRecordAt p m r s
  have hB : MeasurableSet[Swarming.Enl.enlFilt p m s] B :=
    hA.inter (measurableSet_firstRecordAt p m r s)
  have hdiff : ∀ t, (fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j t U) =
      Swarming.Enl.ProjLedger.projInc p m eps i j t := by
    intro t
    funext U
    exact QplWeightedCell.Qpl_succ_sub p m eps i j t U
  have hQm : ∀ k, StronglyMeasurable[Swarming.Enl.enlFilt p m (s + k + 1)]
      (fun U : Array N => Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U) := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m (s + k) eps i j
  have hQi : ∀ k, Integrable (fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U) (arrayMeasure N) := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m (s + k) i j hε
  have hQ0 : ∀ k, (arrayMeasure N)[fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U |
        Swarming.Enl.enlFilt p m (s + k)] =ᵐ[arrayMeasure N] 0 := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.condExp_projInc_eq_zero hp0 hp1 m (s + k) i j hε
  have hbdd' : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U| ≤ C := by
    intro k U hU
    rw [QplWeightedCell.Qpl_succ_sub]
    exact hbdd k U hU
  have hbase := measureReal_cell_max_abs_shift_le_of_ptrunc
    (μ := arrayMeasure N) (ℱ := Swarming.Enl.enlFilt p m) (s := s) (A := B)
    (ξ := fun t U => Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
      Swarming.Enl.ProjLedger.Qpl p m eps i j t U)
    hB hG hQm hQi hQ0 hC hbdd' hn hδ
  have htele : ∀ (k : ℕ) (U : Array N),
      LocMart.psum (fun t U => Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j t U) (s + k) U -
      LocMart.psum (fun t U => Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j t U) s U =
      Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j s U := by
    intro k U
    rw [psum_succ_sub, psum_succ_sub]
    ring
  have hsub : A ∩ OscStartCell (Swarming.Enl.ProjLedger.Qpl p m eps i j)
      (fun U => recTimeA p m U r) n δ s ⊆
      B ∩ {U | ∃ k ≤ n, δ ≤ abs (
        LocMart.psum (fun t U => Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
          Swarming.Enl.ProjLedger.Qpl p m eps i j t U) (s + k) U -
        LocMart.psum (fun t U => Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
          Swarming.Enl.ProjLedger.Qpl p m eps i j t U) s U)} := by
    rintro U ⟨hUA, hτ, k, hk, hdev⟩
    obtain ⟨-, hhit⟩ := (recTimeA_eq_iff_reach_all_firstRecordAt hs U).1 hτ
    refine ⟨⟨hUA, hhit⟩, k, hk, ?_⟩
    rw [htele]
    exact hdev
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans hbase

end ActualRecordQplCell
