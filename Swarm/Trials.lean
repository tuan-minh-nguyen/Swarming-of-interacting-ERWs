/-
# Geometric trials: an almost surely finite initial regeneration from `P(V) > 0`

Paper `main_1d_revised.tex`, §3.3 (`regen`, initial regeneration step):

> "Since `P(V) > 0`, the probability of not hitting `V` in `k` independent trials is at most
> `(1 - P(V))^k -> 0`, hence the initial regeneration time is almost surely finite."

This file proves exactly that step, on the abstract fresh-block interface
`KacFormula.FreshBlocks` of `Swarm/RegenIid.lean` (paper `(factor)`: the
`k`-th regeneration block has law `Q` conditionally on the first `k` blocks).  Nothing else
is assumed: no transience, no speed, no interacting-model input.

Main results
* `fresh_avoid_eq` : the geometric tail, exactly
  `mu {for all k<n the k-th trial misses C} = (1 - Q C)^n`;
* `measure_iInter_compl_eq_zero` : the intersection over *all* trials has measure zero;
* `ae_eventually_mem` : **geometric trials succeed almost surely**, `Q C > 0 ->`
  almost surely some trial hits `C`.  This is the a.s. finiteness of the initial
  regeneration index;
* `firstSuccess` / `firstSuccess_mem` / `firstSuccess_le_of_mem` : the a.s. finite first
  successful trial index and its defining property;
* `fresh_avoid_toReal` / `fresh_avoid_toReal_le` / `ae_eventually_mem_of_le` : the
  real-valued tail bound and the form in which only a lower bound `0 < delta <= Q C`
  (obtained from the paper's `P(V) > 0`, `Swarm.P_V_pos`) is supplied.
-/
import Swarm.RegenIid

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Swarm.Trials

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {S : Type*} [MeasurableSpace S]

/-! ### The geometric tail -/

/-- **Failure of the first `n` trials has probability `(1 - Q C)^n`.**  The blocks are fresh
with law `Q` (`KacFormula.FreshBlocks`), so the first `n` of them are independent with law
`Q`; the `n`-fold product of the complement is `(1 - Q C)^n`. -/
theorem fresh_avoid_eq {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) (n : ℕ) :
    μ (⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ) = (1 - Q C) ^ n := by
  rw [KacFormula.prod_initial h (fun _ => Cᶜ) (fun _ => hC.compl) n, Finset.prod_const,
    Finset.card_range, measure_compl hC (measure_ne_top Q C), measure_univ]

/-- The real-valued form of the geometric tail `(1 - delta)^n`, `delta = Q C`. -/
theorem fresh_avoid_toReal {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) (n : ℕ) :
    (μ (⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ)).toReal = (1 - (Q C).toReal) ^ n := by
  rw [fresh_avoid_eq h hC n, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (a := 1) (b := Q C)
      (by simpa using measure_mono (μ := Q) (subset_univ C)) (by simp)]
  norm_num

/-- **The first `n` trials all fail only with probability at most `(1 - delta)^n`**, whenever
`delta` is a lower bound for the one-trial success probability `Q C`. -/
theorem fresh_avoid_toReal_le {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) {δ : ℝ}
    (hδ : δ ≤ (Q C).toReal) (n : ℕ) :
    (μ (⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ)).toReal ≤ (1 - δ) ^ n := by
  have h2 : Q C ≤ Q univ := measure_mono (μ := Q) (subset_univ C)
  have h3 : (Q C).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (a := Q C) (b := 1) (by simp) (by simpa using h2)
  have h1 : δ ≤ 1 := le_trans hδ h3
  rw [fresh_avoid_toReal h hC n]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-! ### Almost sure success -/

/-- The complement of "some trial succeeds" is the intersection of all failure events. -/
theorem not_exists_mem_eq_iInter {Z : ℕ → Ω → S} {C : Set S} :
    {ω | ¬ ∃ k, Z k ω ∈ C} = ⋂ k, Z k ⁻¹' Cᶜ := by
  ext ω
  simp

/-- The finite failure events are decreasing in `n`. -/
theorem antitone_range_iInter {Z : ℕ → Ω → S} {C : Set S} :
    Antitone fun n => ⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ := by
  intro m n hmn x hx
  simp only [Set.mem_iInter, Finset.mem_range] at hx ⊢
  exact fun k hk => hx k (lt_of_lt_of_le hk hmn)

theorem iInter_range_iInter {Z : ℕ → Ω → S} {C : Set S} :
    (⋂ n, ⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ) = ⋂ k, Z k ⁻¹' Cᶜ := by
  ext x
  simp only [Set.mem_iInter, Finset.mem_range]
  exact ⟨fun h k => h (k + 1) k (Nat.lt_succ_self k), fun h n k hk => h k⟩

/-- **A geometric-decay squeeze.**  If a decreasing sequence of sets has `mu (s n) <= a^n` with
`a < 1`, then its intersection is null.  This is the general form of "the probability of failing
`n` independent trials decays geometrically, hence the probability of failing forever is `0`". -/
theorem measure_iInter_eq_zero_of_pow_le {s : ℕ → Set Ω} {a : ℝ≥0∞} (ha : a < 1)
    (hle : ∀ n, μ (s n) ≤ a ^ n) : μ (⋂ n, s n) = 0 := by
  have hmono : ∀ n, μ (⋂ n, s n) ≤ μ (s n) := fun n => measure_mono (Set.iInter_subset s n)
  have hp : Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ha
  have h0 : μ (⋂ n, s n) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hp
      (Eventually.of_forall fun n => le_trans (hmono n) (hle n))
  simpa using h0

/-- **The probability that every trial fails is zero**, when one trial succeeds with
positive probability.  This is the paper's `(1 - P(V))^k -> 0` step. -/
theorem measure_iInter_compl_eq_zero {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) (hpos : 0 < Q C) :
    μ (⋂ k, Z k ⁻¹' Cᶜ) = 0 := by
  have hlt : (1 - Q C) < 1 := ENNReal.sub_lt_self (by simp) (by simp) hpos.ne'
  have hkey : μ (⋂ n, ⋂ k ∈ Finset.range n, Z k ⁻¹' Cᶜ) = 0 :=
    measure_iInter_eq_zero_of_pow_le hlt (fun n => le_of_eq (fresh_avoid_eq h hC n))
  rwa [iInter_range_iInter] at hkey

/-- **Geometric trials succeed almost surely.**  If a single trial hits the good set `C` with
positive probability, then almost surely some trial does.  In the paper's application `C` is
the event `V` of a complete regeneration and `Q C = P(V) > 0`
(`Swarm.P_V_pos` in `results/lean/areas/escape/`). -/
theorem ae_eventually_mem {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) (hpos : 0 < Q C) :
    ∀ᵐ ω ∂μ, ∃ k, Z k ω ∈ C := by
  rw [ae_iff, not_exists_mem_eq_iInter]
  exact measure_iInter_compl_eq_zero h hC hpos

/-- The same with the success probability supplied only as a positive lower bound. -/
theorem ae_eventually_mem_of_le {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : KacFormula.FreshBlocks μ Z Q) {C : Set S} (hC : MeasurableSet C) {δ : ℝ≥0∞}
    (hδ : 0 < δ) (hle : δ ≤ Q C) : ∀ᵐ ω ∂μ, ∃ k, Z k ω ∈ C :=
  ae_eventually_mem h hC (lt_of_lt_of_le hδ hle)

/-! ### The first successful trial -/

/-- The index of the first trial in the good set (`0` if there is none). -/
noncomputable def firstSuccess (Z : ℕ → Ω → S) (C : Set S) (ω : Ω) : ℕ :=
  if h : ∃ k, Z k ω ∈ C then Nat.find h else 0

theorem firstSuccess_mem {Z : ℕ → Ω → S} {C : Set S}
    (h : ∀ᵐ ω ∂μ, ∃ k, Z k ω ∈ C) : ∀ᵐ ω ∂μ, Z (firstSuccess Z C ω) ω ∈ C := by
  filter_upwards [h] with ω hω
  simp only [firstSuccess, dif_pos hω]
  exact Nat.find_spec hω

theorem firstSuccess_le_of_mem {Z : ℕ → Ω → S} {C : Set S} {ω : Ω} {k : ℕ}
    (hk : Z k ω ∈ C) : firstSuccess Z C ω ≤ k := by
  have hex : ∃ j, Z j ω ∈ C := ⟨k, hk⟩
  simp only [firstSuccess, dif_pos hex]
  exact Nat.find_min' hex hk

end Swarm.Trials
