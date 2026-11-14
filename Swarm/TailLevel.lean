import Swarm.Imports
import Swarm.TailAbstract

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace TrialTail

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Γ : ℕ → Set Ω} {ρ : ℝ} {σ : ℕ → Ω → WithTop ℕ}

/-! ## Ambient measurability of the weight -/

lemma measurable_trialFac (HGamb : ∀ i, MeasurableSet (Γ i)) (ρ : ℝ) (i : ℕ) :
    Measurable (trialFac Γ ρ i) := by
  unfold trialFac
  exact Measurable.ite (HGamb i) measurable_const measurable_const

lemma measurable_ofReal_trialW (HGamb : ∀ i, MeasurableSet (Γ i)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (k : ℕ) : Measurable fun ω => ENNReal.ofReal (trialW Γ ρ k ω) := by
  have h : (fun ω => ENNReal.ofReal (trialW Γ ρ k ω))
      = fun ω => ∏ i ∈ Finset.range k, ENNReal.ofReal (trialFac Γ ρ i ω) := by
    funext ω
    rw [trialW, ENNReal.ofReal_prod_of_nonneg (fun i _ => trialFac_nonneg Γ hρ i ω)]
  rw [h]
  exact Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp (measurable_trialFac HGamb ρ i)

/-! ## The level weight

`levelW k j` is the weight `ofReal (∏_{i<k} ρ^{1_{Γ i}})` cut down to the record level
`{σ k = j}`, written as a product of level-`j`-measurable factors so that its
`ℱ j`-measurability (the "no future leakage" requirement of the weight lemma) is
structural. -/

/-- The `i`-th factor of the level-`j`-cut weight at record time `k`. -/
noncomputable def levelFac (Γ : ℕ → Set Ω) (ρ : ℝ) (σ : ℕ → Ω → WithTop ℕ) (k j i : ℕ) :
    Ω → ℝ≥0∞ :=
  ({ω | σ k ω = (j : WithTop ℕ)} ∩ Γ i).indicator (fun _ => ENNReal.ofReal ρ)
  + ({ω | σ k ω = (j : WithTop ℕ)} \ ({ω | σ k ω = (j : WithTop ℕ)} ∩ Γ i)).indicator
      (fun _ => 1)

lemma levelFac_apply (k j i : ℕ) (ω : Ω) :
    levelFac Γ ρ σ k j i ω
      = if σ k ω = (j : WithTop ℕ) then ENNReal.ofReal (trialFac Γ ρ i ω) else 0 := by
  by_cases h1 : σ k ω = (j : WithTop ℕ)
  · by_cases h2 : ω ∈ Γ i
    · simp [levelFac, trialFac, h1, h2]
    · simp [levelFac, trialFac, h1, h2]
  · simp [levelFac, h1]

/-- The level-`j`-cut weight at record time `k`. -/
noncomputable def levelW (Γ : ℕ → Set Ω) (ρ : ℝ) (σ : ℕ → Ω → WithTop ℕ) (k j : ℕ) :
    Ω → ℝ≥0∞ :=
  fun ω => if σ k ω = (j : WithTop ℕ) then
    ∏ i ∈ Finset.range k, levelFac Γ ρ σ k j i ω else 0

lemma levelW_apply {ρ : ℝ} (hρ : 0 ≤ ρ) (k j : ℕ) (ω : Ω) :
    levelW Γ ρ σ k j ω
      = if σ k ω = (j : WithTop ℕ) then ENNReal.ofReal (trialW Γ ρ k ω) else 0 := by
  by_cases h : σ k ω = (j : WithTop ℕ)
  · simp only [levelW, h, if_true, levelFac_apply, trialW,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => trialFac_nonneg Γ hρ i ω)]
  · simp [levelW, h]

/-- **On the level set `{σ k = j}`**, multiplying the cut weight by the next factor gives the
weight of the longer product. -/
lemma levelW_mul_trialFac {ρ : ℝ} (hρ : 0 ≤ ρ) (k j : ℕ) (ω : Ω)
    (h : σ k ω = (j : WithTop ℕ)) :
    levelW Γ ρ σ k j ω * ENNReal.ofReal (trialFac Γ ρ k ω)
      = ENNReal.ofReal (trialW Γ ρ (k + 1) ω) := by
  rw [levelW_apply hρ k j ω, if_pos h, ← ENNReal.ofReal_mul (trialW_nonneg Γ hρ k ω),
    trialW_succ]

lemma measurable_levelFac {ℱ : ℕ → MeasurableSpace Ω}
    (Hσ : ∀ i n, MeasurableSet[ℱ n] {ω | σ i ω = (n : WithTop ℕ)})
    (HΓ : ∀ i k n, i < k → MeasurableSet[ℱ n] ({ω | σ k ω = (n : WithTop ℕ)} ∩ Γ i))
    {k j i : ℕ} (hik : i < k) : Measurable[ℱ j] (levelFac Γ ρ σ k j i) := by
  have hB : MeasurableSet[ℱ j] {ω | σ k ω = (j : WithTop ℕ)} := Hσ k j
  have hBG : MeasurableSet[ℱ j] ({ω | σ k ω = (j : WithTop ℕ)} ∩ Γ i) := HΓ i k j hik
  have hd : MeasurableSet[ℱ j]
      ({ω | σ k ω = (j : WithTop ℕ)} \ ({ω | σ k ω = (j : WithTop ℕ)} ∩ Γ i)) := hB.diff hBG
  exact (Measurable.indicator measurable_const hBG).add (Measurable.indicator measurable_const hd)

lemma measurable_levelW {ℱ : ℕ → MeasurableSpace Ω}
    (Hσ : ∀ i n, MeasurableSet[ℱ n] {ω | σ i ω = (n : WithTop ℕ)})
    (HΓ : ∀ i k n, i < k → MeasurableSet[ℱ n] ({ω | σ k ω = (n : WithTop ℕ)} ∩ Γ i))
    (k j : ℕ) : Measurable[ℱ j] (levelW Γ ρ σ k j) := by
  have h2 : Measurable[ℱ j]
      (fun ω => ∏ i ∈ Finset.range k, levelFac Γ ρ σ k j i ω) :=
    Finset.measurable_prod _ fun i hi =>
      measurable_levelFac Hσ HΓ (Finset.mem_range.mp hi)
  exact Measurable.ite (Hσ k j) h2 measurable_const

end TrialTail
