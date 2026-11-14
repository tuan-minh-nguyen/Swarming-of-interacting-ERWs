/-
  **Stopped conditional trial bound ⇒ exponential count tail** (abstract core).

  See `README.md`.  This file is generic measure theory: no array-specific input.
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace TrialTail

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The product weight -/

/-- The one-step factor `ρ^{1_{Γ i}}`. -/
noncomputable def trialFac (Γ : ℕ → Set Ω) (ρ : ℝ) (i : ℕ) : Ω → ℝ :=
  fun ω => if ω ∈ Γ i then ρ else 1

/-- `∏_{i<k} ρ^{1_{Γ i}}`, i.e. `ρ` to the number of successes among the first `k` trials. -/
noncomputable def trialW (Γ : ℕ → Set Ω) (ρ : ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => ∏ i ∈ Finset.range k, trialFac Γ ρ i ω

lemma trialFac_nonneg (Γ : ℕ → Set Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ℕ) (ω : Ω) :
    0 ≤ trialFac Γ ρ i ω := by
  rw [trialFac]; split_ifs <;> linarith

lemma trialFac_le_one (Γ : ℕ → Set Ω) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (i : ℕ)
    (ω : Ω) : trialFac Γ ρ i ω ≤ 1 := by
  rw [trialFac]; split_ifs <;> linarith

theorem trialW_succ (Γ : ℕ → Set Ω) (ρ : ℝ) (k : ℕ) (ω : Ω) :
    trialW Γ ρ (k + 1) ω = trialW Γ ρ k ω * trialFac Γ ρ k ω := by
  simp only [trialW, Finset.prod_range_succ]

@[simp] lemma trialW_zero (Γ : ℕ → Set Ω) (ρ : ℝ) (ω : Ω) : trialW Γ ρ 0 ω = 1 := by
  simp [trialW]

lemma trialW_nonneg (Γ : ℕ → Set Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) (ω : Ω) :
    0 ≤ trialW Γ ρ k ω :=
  Finset.prod_nonneg fun i _ => trialFac_nonneg Γ hρ i ω

lemma trialW_le_one (Γ : ℕ → Set Ω) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (ω : Ω) :
    trialW Γ ρ k ω ≤ 1 :=
  Finset.prod_le_one (fun i _ => trialFac_nonneg Γ hρ0 i ω)
    (fun i _ => trialFac_le_one Γ hρ0 hρ1 i ω)

/-- The weight is `ρ` to the number of successes. -/
theorem trialW_eq_pow_card (Γ : ℕ → Set Ω) (ρ : ℝ) (k : ℕ) (ω : Ω) :
    trialW Γ ρ k ω = ρ ^ ((Finset.range k).filter (fun i => ω ∈ Γ i)).card := by
  have h1 : (fun i => trialFac Γ ρ i ω) = (fun i => if ω ∈ Γ i then ρ else 1) := by
    funext i; rw [trialFac]
  simp only [trialW, h1, Finset.prod_ite, Finset.prod_const]
  rw [one_pow, mul_one]

/-! ## The level partition of `{σ ≠ ⊤}` -/

lemma iUnion_level_eq_ne_top (σ : Ω → WithTop ℕ) :
    (⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)}) = {ω | σ ω ≠ ⊤} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨fun ⟨n, hn⟩ => hn ▸ WithTop.coe_ne_top, fun h => by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    exact ⟨n, hn.symm⟩⟩

lemma pairwiseDisjoint_level (σ : Ω → WithTop ℕ) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => {ω | σ ω = (n : WithTop ℕ)}) := by
  intro m n hmn
  refine disjoint_left.mpr fun ω hm hn => hmn ?_
  exact WithTop.coe_inj.mp (hm.symm.trans hn)

/-- **Level decomposition** of the integral over `{σ ≠ ⊤}`. -/
theorem lintegral_level_tsum (σ : Ω → WithTop ℕ) {f : Ω → ℝ≥0∞}
    (hmeas : ∀ n : ℕ, MeasurableSet ({ω | σ ω = (n : WithTop ℕ)})) (hf : Measurable f) :
    ∫⁻ ω in {ω | σ ω ≠ ⊤}, f ω ∂μ
      = ∑' n : ℕ, ∫⁻ ω in {ω | σ ω = (n : WithTop ℕ)}, f ω ∂μ := by
  rw [← iUnion_level_eq_ne_top σ]
  refine lintegral_iUnion (s := fun n : ℕ => {ω | σ ω = (n : WithTop ℕ)}) (fun n => hmeas n) ?_ f
  intro m n hmn
  refine disjoint_left.mpr fun ω hm hn => hmn ?_
  exact WithTop.coe_inj.mp (hm.symm.trans hn)

/-! ## From the conditional-mass form to a set-integral form -/

theorem weight_lemma {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {B A : Set Ω} {c : ℝ≥0∞}
    (hge : ∀ H, MeasurableSet[m] H → c * μ (H ∩ B) ≤ μ (H ∩ A))
    {w : Ω → ℝ≥0∞} (hw : Measurable[m] w) :
    c * ∫⁻ ω in B, w ω ∂μ ≤ ∫⁻ ω in A, w ω ∂μ := by
  have hcmp : c • (μ.restrict B).trim hm ≤ (μ.restrict A).trim hm := by
    refine Measure.le_iff.mpr fun H hH => ?_
    have h1 : (c • (μ.restrict B).trim hm) H = c * μ (H ∩ B) := by
      rw [Measure.smul_apply, smul_eq_mul, trim_measurableSet_eq hm hH]
      rw [Measure.restrict_apply (hm H hH)]
    have h2 : ((μ.restrict A).trim hm) H = μ (H ∩ A) := by
      rw [trim_measurableSet_eq hm hH]
      rw [Measure.restrict_apply (hm H hH)]
    rw [h1, h2]
    exact hge H hH
  calc c * ∫⁻ ω in B, w ω ∂μ
      = c * ∫⁻ ω, w ω ∂((μ.restrict B).trim hm) := by rw [lintegral_trim hm hw]
    _ = ∫⁻ ω, w ω ∂(c • ((μ.restrict B).trim hm)) := by
        rw [lintegral_smul_measure]; rfl
    _ ≤ ∫⁻ ω, w ω ∂((μ.restrict A).trim hm) := lintegral_mono' hcmp le_rfl
    _ = ∫⁻ ω, w ω ∂(μ.restrict A) := by rw [lintegral_trim hm hw]
    _ = ∫⁻ ω in A, w ω ∂μ := rfl

end TrialTail
