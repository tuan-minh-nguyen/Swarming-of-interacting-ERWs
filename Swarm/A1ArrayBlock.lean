/-
  **`locsum`, layer A1: transport of the block concentration bound to the actual array.**

  `LocSum.block_concentration` (Swarm/L5Block.lean) is a statement about the
  canonical i.i.d. mark row `markMeasure (boolMeasure q)`.  This file moves it to the actual
  interacting array `Swarming.Uniform.arrayMeasure N`, whose coordinates are independent
  uniforms indexed by `Fin N × ℤ × ℕ`:

  * `siteMarks p m U j` is the Boolean site-mark row of walker `j`, and
    `SwarmLogRatio.measurePreserving_siteMarks` (Swarm/RawLogRatio.lean) says its
    law is exactly `markMeasure (boolMeasure ((1-p)^(m-1)))`.  Hence every event defined by
    the potential of one walker's row pulls back with the same probability.
  * `LocSum.rat` is exactly the paper's ratio `(1-ω)/ω` of the two-valued environment
    (`omegaAt` takes the values `p` and `1/2`, `Reveal.omegaAt`), so `LocSum.Q p k x` of the
    actual site-mark row *is* the paper's truncated potential `h^*_{k-1}(x)` of that walker.
  * `array_all_concentration` unions over the `N` walkers, and `array_window_concentration`
    over the `T` blocks of a window.

  No independence of adaptively revealed coordinates is used: the only probabilistic input is
  the already-proved law of the full i.i.d. mark row.
-/
import Swarm.L5Block
import Swarm.RawLogRatio

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- The number `q = (1-p)^{m-1}` of the paper: the probability of a site mark. -/
def qOf (p : ℝ) (m : ℕ) : ℝ := (1 - p) ^ (m - 1)

/-- **The bad block event of one walker.**  The sum of the squared truncated potential over
the `n*k`-site block starting at `a0` exceeds `C*n*k`.  The `k` residue classes mod `k` of the
block each contribute `n` sites; this is exactly the event of `LocSum.block_concentration`. -/
def BlockBad {N : ℕ} (p : ℝ) (m n k a0 : ℕ) (C : ℝ) (U : Array N) (j : Fin N) : Prop :=
  C * ((n : ℝ) * (k : ℝ)) ≤
    ∑ r : Fin k, ∑ i : Fin n,
      (LocSum.Q p k (a0 + r.1 + i.1 * k) (siteMarks p m U j)) ^ 2

/-- The same event as a set of mark rows. -/
def MarkBlockBad (p : ℝ) (n k a0 : ℕ) (C : ℝ) (ω : ℕ → Bool) : Prop :=
  C * ((n : ℝ) * (k : ℝ)) ≤
    ∑ r : Fin k, ∑ i : Fin n, (LocSum.Q p k (a0 + r.1 + i.1 * k) ω) ^ 2

lemma measurable_markBlockSum (p : ℝ) (n k a0 : ℕ) :
    Measurable (fun ω : ℕ → Bool =>
      ∑ r : Fin k, ∑ i : Fin n, (LocSum.Q p k (a0 + r.1 + i.1 * k) ω) ^ 2) :=
  Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun i _ =>
    (LocSum.measurable_Q p k _).pow_const 2

lemma measurableSet_markBlockBad (p : ℝ) (n k a0 : ℕ) (C : ℝ) :
    MeasurableSet {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω} :=
  measurableSet_le measurable_const (measurable_markBlockSum p n k a0)

lemma measurable_siteMarks {N : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) :
    Measurable (fun U : Array N => siteMarks p m U j) :=
  (measurePreserving_siteMarks hp0 hp1 m j).measurable

/-- The mark-row map of one walker. -/
def rowMap {N : ℕ} (p : ℝ) (m : ℕ) (j : Fin N) : Array N → (ℕ → Bool) :=
  fun U => siteMarks p m U j

lemma blockBad_eq_preimage {N : ℕ} (p : ℝ) (m n k a0 : ℕ) (C : ℝ) (j : Fin N) :
    {U : Array N | BlockBad p m n k a0 C U j}
      = (fun U : Array N => siteMarks p m U j) ⁻¹'
          {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω} := rfl

lemma measurable_rowMap {N : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) :
    Measurable (rowMap (N := N) p m j) :=
  measurable_siteMarks hp0 hp1 m j

/-- **Transport of the block concentration bound to one walker of the actual array.** -/
theorem array_block_concentration {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n k a0 : ℕ) (hk : 1 ≤ k) (ha : k ≤ a0) {C : ℝ}
    (hCM : LocSum.Mb p (qOf p m) ≤ C) (j : Fin N) :
    arrayMeasure N {U : Array N | BlockBad p m n k a0 C U j}
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ)))) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ qOf p m := by unfold qOf; positivity
  have hq1 : qOf p m ≤ 1 := by
    unfold qOf
    exact pow_le_one₀ (by linarith) (by linarith)
  have hqpos : 0 < qOf p m := by
    unfold qOf
    exact pow_pos (by linarith) _
  have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
  have hmeas := measurableSet_markBlockBad p n k a0 C
  calc arrayMeasure N {U : Array N | BlockBad p m n k a0 C U j}
      = arrayMeasure N ((fun U : Array N => siteMarks p m U j) ⁻¹'
          {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω}) := by rw [blockBad_eq_preimage]
    _ = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
          {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω} := by
        rw [Measure.map_apply (measurable_siteMarks hp0 hp2 m j) hmeas]
    _ = (markMeasure (boolMeasure (qOf p m))) {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω} :=
        congrArg (fun μ : Measure (ℕ → Bool) =>
          μ {ω : ℕ → Bool | MarkBlockBad p n k a0 C ω}) hmp.map_eq
    _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ)))) :=
        LocSum.block_concentration hq0 hq1 hk ha hp1 hp2 hqpos hCM

/-- **Union over the walkers.**  For every walker there is a block of the stated kind with the
same probability bound, so the union costs a factor `N`. -/
theorem array_all_concentration {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n k a0 : ℕ) (hk : 1 ≤ k) (ha : k ≤ a0) {C : ℝ}
    (hCM : LocSum.Mb p (qOf p m) ≤ C) :
    arrayMeasure N {U : Array N | ∃ j : Fin N, BlockBad p m n k a0 C U j}
      ≤ (N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ))))) := by
  calc arrayMeasure N {U : Array N | ∃ j : Fin N, BlockBad p m n k a0 C U j}
      = arrayMeasure N (⋃ j : Fin N, {U : Array N | BlockBad p m n k a0 C U j}) := by
        simp only [Set.setOf_exists, Set.mem_iUnion]
    _ ≤ ∑ j : Fin N, arrayMeasure N {U : Array N | BlockBad p m n k a0 C U j} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin N, ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ))))) :=
        Finset.sum_le_sum fun j _ => array_block_concentration hp1 hp2 m n k a0 hk ha hCM j
    _ = (N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ))))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `T` blocks of length `n*k` starting at `A`, `A + n*k`, … : the bad set of a window. -/
def WindowBad {N : ℕ} (p : ℝ) (m n k A T : ℕ) (C : ℝ) (U : Array N) : Prop :=
  ∃ j : Fin N, ∃ t : Fin T, BlockBad p m n k (A + t.1 * (n * k)) C U j

/-- **Union over the blocks of a window.**  With `A ≥ k` every block start `A + t*n*k` is a
legal truncation site, so `array_all_concentration` applies to each `t < T`. -/
theorem array_window_concentration {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n k A T : ℕ) (hk : 1 ≤ k) (hA : k ≤ A) {C : ℝ}
    (hCM : LocSum.Mb p (qOf p m) ≤ C) :
    arrayMeasure N {U : Array N | WindowBad p m n k A T C U}
      ≤ (T : ℝ≥0∞) * ((N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ)))))) := by
  have hstep : arrayMeasure N {U : Array N | WindowBad p m n k A T C U}
      ≤ ∑ t : Fin T, arrayMeasure N
          {U : Array N | ∃ j : Fin N, BlockBad p m n k (A + t.1 * (n * k)) C U j} := by
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    intro U hU
    simp only [WindowBad, Set.mem_setOf_eq, Set.mem_iUnion] at hU ⊢
    obtain ⟨j, t, ht⟩ := hU
    exact ⟨t, j, ht⟩
  refine hstep.trans ?_
  have hblock : ∀ t : Fin T, arrayMeasure N
      {U : Array N | ∃ j : Fin N, BlockBad p m n k (A + t.1 * (n * k)) C U j}
      ≤ (N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ))))) := by
    intro t
    refine array_all_concentration hp1 hp2 m n k (A + t.1 * (n * k)) hk ?_ hCM
    have : k ≤ A := hA
    omega
  calc ∑ t : Fin T, arrayMeasure N
        {U : Array N | ∃ j : Fin N, BlockBad p m n k (A + t.1 * (n * k)) C U j}
      ≤ ∑ _t : Fin T, (N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ))))) :=
        Finset.sum_le_sum fun t _ => hblock t
    _ = (T : ℝ≥0∞) * ((N : ℝ≥0∞) * ((k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - LocSum.Mb p (qOf p m))) ^ 2)
            / (2 * ((∑ _i : Fin n, LocSum.subGnn k : ℝ≥0) : ℝ)))))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The complement of the "all blocks of the window are good" event is contained in the
window bad set: on the good event every one of the `T` blocks has sum at most `C*n*k`. -/
theorem not_good_subset_windowBad {N : ℕ} (p : ℝ) (m n k A T : ℕ) (C : ℝ) :
    {U : Array N | ¬ (∀ j : Fin N, ∀ t : Fin T,
        (∑ r : Fin k, ∑ i : Fin n,
          (LocSum.Q p k (A + t.1 * (n * k) + r.1 + i.1 * k) (siteMarks p m U j)) ^ 2)
          ≤ C * ((n : ℝ) * (k : ℝ)))}
      ⊆ {U : Array N | WindowBad p m n k A T C U} := by
  intro U hU
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hU
  obtain ⟨j, t, hjt⟩ := hU
  exact ⟨j, t, le_of_lt hjt⟩

end

end LocSumAct
