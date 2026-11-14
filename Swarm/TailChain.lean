import Swarm.Imports
import Swarm.TailStep

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace TrialTail

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Γ : ℕ → Set Ω} {ρ : ℝ} {σ : ℕ → Ω → WithTop ℕ}
variable {ℱ : ℕ → MeasurableSpace Ω} {c : ℝ}

section Chain

variable (hle : ∀ n, ℱ n ≤ m0)
variable (Hσ : ∀ i n, MeasurableSet[ℱ n] {p | σ i p = (n : WithTop ℕ)})
variable (HΓ : ∀ i k n, i < k → MeasurableSet[ℱ n] ({p | σ k p = (n : WithTop ℕ)} ∩ Γ i))
variable (Hmass : ∀ i n (H : Set Ω), MeasurableSet[ℱ n] H →
    H ⊆ {p | σ i p = (n : WithTop ℕ)} → ENNReal.ofReal c * μ H ≤ μ (H ∩ Γ i))
variable (HGamb : ∀ i, MeasurableSet (Γ i))
variable (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
variable (Hnest : ∀ k, {p | σ (k + 1) p ≠ ⊤} ⊆ {p | σ k p ≠ ⊤})
variable (Hfin : ∀ i, Γ i ⊆ {p | σ i p ≠ ⊤})

include hle Hσ HΓ Hmass HGamb hc0 hc1 hρ0 hρ1 Hnest Hfin in
/-- **The product-martingale (multiplicative moment) bound.** -/
theorem chain_bound (k : ℕ) :
    ∫⁻ ω in {p | σ k p ≠ ⊤}, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
      ≤ ENNReal.ofReal ((1 - c + c * ρ) ^ k) * μ {p | σ 0 p ≠ ⊤} := by
  classical
  have hρle : 0 ≤ ρ := le_of_lt hρ0
  have hR0 : 0 ≤ 1 - c + c * ρ := by nlinarith
  induction k with
  | zero =>
      simp only [pow_zero, ENNReal.ofReal_one, trialW_zero, one_mul]
      rw [setLIntegral_const, one_mul]
  | succ k ih =>
      have hstep : ∫⁻ ω in {p | σ (k + 1) p ≠ ⊤},
            ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ
          ≤ ENNReal.ofReal (1 - c + c * ρ) *
              ∫⁻ ω in {p | σ k p ≠ ⊤}, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ := by
        refine (lintegral_mono' (Measure.restrict_mono (Hnest k) le_rfl) le_rfl).trans ?_
        rw [lintegral_level_tsum (σ k) (fun n : ℕ => hle n _ (Hσ k n))
          (measurable_ofReal_trialW HGamb hρle (k + 1))]
        calc ∑' j : ℕ, ∫⁻ ω in {p | σ k p = (j : WithTop ℕ)},
              ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ
            ≤ ∑' j : ℕ, ENNReal.ofReal (1 - c + c * ρ) *
                ∫⁻ ω in {p | σ k p = (j : WithTop ℕ)},
                  ENNReal.ofReal (trialW Γ ρ k ω) ∂μ :=
              ENNReal.tsum_le_tsum fun j =>
                one_step hle Hσ HΓ Hmass HGamb hc0 hc1 hρ0 hρ1 k j
          _ = ENNReal.ofReal (1 - c + c * ρ) *
                ∑' j : ℕ, ∫⁻ ω in {p | σ k p = (j : WithTop ℕ)},
                  ENNReal.ofReal (trialW Γ ρ k ω) ∂μ := ENNReal.tsum_mul_left
          _ = ENNReal.ofReal (1 - c + c * ρ) *
                ∫⁻ ω in {p | σ k p ≠ ⊤}, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ := by
              rw [lintegral_level_tsum (σ k) (fun n : ℕ => hle n _ (Hσ k n))
                (measurable_ofReal_trialW HGamb hρle k)]
      refine hstep.trans ?_
      calc ENNReal.ofReal (1 - c + c * ρ) *
            ∫⁻ ω in {p | σ k p ≠ ⊤}, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
          ≤ ENNReal.ofReal (1 - c + c * ρ) *
              (ENNReal.ofReal ((1 - c + c * ρ) ^ k) * μ {p | σ 0 p ≠ ⊤}) :=
            mul_le_mul_right ih _
        _ = ENNReal.ofReal ((1 - c + c * ρ) ^ (k + 1)) * μ {p | σ 0 p ≠ ⊤} := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hR0, ← pow_succ']

/-- Iterated nesting: a record that has already reached level `k` has reached level `0`. -/
lemma ne_top_zero_of_ne_top (Hnest : ∀ k, {p | σ (k + 1) p ≠ ⊤} ⊆ {p | σ k p ≠ ⊤})
    (k : ℕ) : {p | σ k p ≠ ⊤} ⊆ {p | σ 0 p ≠ ⊤} := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Hnest k).trans ih

include hle Hσ HΓ Hmass HGamb hc0 hc1 hρ0 hρ1 Hnest Hfin in
/-- **The count tail** for the trial indicators on one residue class: the number of successful
trials among the first `K` is below `j` only with probability bounded by the multiplicative
moment bound, plus the two *record-window* exceptions `{σ 0 = ⊤}` (the class never starts) and
`{σ K = ⊤}` (the class stops before the `K`-th trial). -/
theorem count_tail (K j : ℕ) :
    μ {ω | ((Finset.range K).filter (fun i => ω ∈ Γ i)).card ≤ j}
      ≤ μ {p | σ 0 p = ⊤} + ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K)
        + μ {p | σ K p = ⊤} := by
  classical
  have hρle : 0 ≤ ρ := le_of_lt hρ0
  have hR0 : 0 ≤ 1 - c + c * ρ := by nlinarith
  set E : Set Ω := {ω | ((Finset.range K).filter (fun i => ω ∈ Γ i)).card ≤ j} with hE
  set T : Set Ω := {p | σ K p ≠ ⊤} with hT
  have hT0 : T ⊆ {p | σ 0 p ≠ ⊤} := ne_top_zero_of_ne_top Hnest K
  have hmT : MeasurableSet T := by
    rw [hT, ← iUnion_level_eq_ne_top (σ K)]
    exact MeasurableSet.iUnion fun n => hle n _ (Hσ K n)
  -- (1) no trial succeeds once the record has stopped
  have htriv : ∀ (ω : Ω) (i : ℕ), σ 0 ω = ⊤ → σ i ω = ⊤ := by
    intro ω i
    induction i with
    | zero => exact id
    | succ k ih =>
        intro h
        by_contra hne
        exact (Hnest k) hne (ih h)
  have hzero : ∀ ω, σ 0 ω = ⊤ → ω ∈ E := by
    intro ω hω
    have hempty : (Finset.range K).filter (fun i => ω ∈ Γ i) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun i _ hi => ?_
      exact (Hfin i hi) (htriv ω i hω)
    simp only [hE, Set.mem_ofPred_eq, hempty, Finset.card_empty]
    exact Nat.zero_le j
  -- (2) the pointwise Markov estimate on `{σ K ≠ ⊤}`
  have hpt : ∀ ω ∈ (E ∩ T), ENNReal.ofReal (ρ ^ j) ≤ ENNReal.ofReal (trialW Γ ρ K ω) := by
    intro ω hω
    rw [trialW_eq_pow_card]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hρle hρ1 hω.1)
  have h1 : ∫⁻ ω in T, ENNReal.ofReal (trialW Γ ρ K ω) ∂μ
      ≤ ENNReal.ofReal ((1 - c + c * ρ) ^ K) := by
    refine (chain_bound hle Hσ HΓ Hmass HGamb hc0 hc1 hρ0 hρ1 Hnest Hfin K).trans ?_
    have h := measure_mono (μ := μ) (Set.subset_univ {p | σ 0 p ≠ ⊤})
    have h1 : μ {p | σ 0 p ≠ ⊤} ≤ 1 := by simpa using h
    calc ENNReal.ofReal ((1 - c + c * ρ) ^ K) * μ {p | σ 0 p ≠ ⊤}
        ≤ ENNReal.ofReal ((1 - c + c * ρ) ^ K) * 1 := mul_le_mul_right h1 _
      _ = ENNReal.ofReal ((1 - c + c * ρ) ^ K) := mul_one _
  have hmark : ENNReal.ofReal (ρ ^ j) * μ (E ∩ T)
      ≤ ∫⁻ ω in T, ENNReal.ofReal (trialW Γ ρ K ω) ∂μ := by
    calc ENNReal.ofReal (ρ ^ j) * μ (E ∩ T)
        = ∫⁻ ω in (E ∩ T), ENNReal.ofReal (ρ ^ j) ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ ω in (E ∩ T), ENNReal.ofReal (trialW Γ ρ K ω) ∂μ :=
          setLIntegral_mono (measurable_ofReal_trialW HGamb hρle K) hpt
      _ ≤ ∫⁻ ω in T, ENNReal.ofReal (trialW Γ ρ K ω) ∂μ :=
          lintegral_mono' (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hdiv : μ (E ∩ T) ≤ ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K) := by
    have hb : ENNReal.ofReal (ρ ^ j) * μ (E ∩ T)
        ≤ ENNReal.ofReal ((1 - c + c * ρ) ^ K) := hmark.trans h1
    have hne0 : ENNReal.ofReal (ρ ^ j) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (pow_pos hρ0 j)).ne'
    calc μ (E ∩ T) = 1 * μ (E ∩ T) := (one_mul _).symm
      _ = (ENNReal.ofReal (ρ ^ j))⁻¹ * ENNReal.ofReal (ρ ^ j) * μ (E ∩ T) := by
          rw [ENNReal.inv_mul_cancel hne0 ENNReal.ofReal_ne_top]
      _ = (ENNReal.ofReal (ρ ^ j))⁻¹ * (ENNReal.ofReal (ρ ^ j) * μ (E ∩ T)) :=
          mul_assoc _ _ _
      _ ≤ (ENNReal.ofReal (ρ ^ j))⁻¹ * ENNReal.ofReal ((1 - c + c * ρ) ^ K) :=
          mul_le_mul_right hb _
      _ = ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hρle j)),
            ENNReal.ofReal_inv_of_pos (pow_pos hρ0 j)]
  -- (3) assemble
  have hE1 : μ E ≤ μ {p | σ 0 p = ⊤} + μ (E ∩ {p | σ 0 p ≠ ⊤}) := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    by_cases h : σ 0 ω = ⊤
    · exact Or.inl h
    · exact Or.inr ⟨hω, h⟩
  have hE2 : μ (E ∩ {p | σ 0 p ≠ ⊤}) ≤ ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K)
      + μ {p | σ K p = ⊤} := by
    have hsub : E ∩ {p | σ 0 p ≠ ⊤} ⊆ (E ∩ T) ∪ {p | σ K p = ⊤} := by
      intro ω hω
      by_cases h : σ K ω = ⊤
      · exact Or.inr h
      · exact Or.inl ⟨hω.1, h⟩
    refine ((measure_mono hsub).trans (measure_union_le _ _)).trans ?_
    exact add_le_add hdiv (le_refl _)
  calc μ E ≤ μ {p | σ 0 p = ⊤} + μ (E ∩ {p | σ 0 p ≠ ⊤}) := hE1
    _ ≤ μ {p | σ 0 p = ⊤} + (ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K)
          + μ {p | σ K p = ⊤}) := by gcongr
    _ = μ {p | σ 0 p = ⊤} + ENNReal.ofReal ((ρ ^ j)⁻¹ * (1 - c + c * ρ) ^ K)
          + μ {p | σ K p = ⊤} := by rw [add_assoc]

end Chain

end TrialTail
