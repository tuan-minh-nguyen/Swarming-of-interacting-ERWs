/-
Krylov--Bogoliubov machinery, part 1: kernel algebra and the Cesaro shift estimate.

Contains no proof holes; imports only Mathlib.

Setting: `X` a measurable space, `κ : Kernel X X` a Markov kernel, `μ` a probability
measure.  `step κ μ = μ.bind κ` is the one-step push-forward and
`avg κ μ n = (n+1)⁻¹ • ∑_{k≤n} (step κ)^[k] μ` the Cesaro average of the first `n+1`
iterates.
-/
import Swarm.Imports

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X]

/-! ## Kernel algebra -/

/-- One-step push-forward of a measure through a kernel. -/
noncomputable def step (κ : Kernel X X) (μ : Measure X) : Measure X :=
  μ.bind (⇑κ)

lemma step_zero (κ : Kernel X X) : step κ 0 = 0 :=
  Measure.bind_zero_left _

lemma step_add (κ : Kernel X X) (μ ν : Measure X) :
    step κ (μ + ν) = step κ μ + step κ ν := by
  show (μ + ν).bind (⇑κ) = μ.bind ⇑κ + ν.bind ⇑κ
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable κ), Measure.add_apply,
    Measure.bind_apply hs (Kernel.aemeasurable κ),
    Measure.bind_apply hs (Kernel.aemeasurable κ), lintegral_add_measure]

lemma step_smul (κ : Kernel X X) (c : ℝ≥0∞) (μ : Measure X) :
    step κ (c • μ) = c • step κ μ :=
  Measure.bind_smul c μ _

lemma step_finset_sum (κ : Kernel X X) {ι : Type*} (s : Finset ι)
    (μ : ι → Measure X) :
    step κ (∑ i ∈ s, μ i) = ∑ i ∈ s, step κ (μ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [step_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, step_add, ih]

lemma step_isProbabilityMeasure (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] : IsProbabilityMeasure (step κ μ) := by
  constructor
  rw [step, Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable κ)]
  have h1 : ∀ a, κ a Set.univ = 1 := fun a => measure_univ
  rw [show (fun a => κ a Set.univ) = fun _ => (1 : ℝ≥0∞) from funext h1, lintegral_one]
  exact measure_univ

lemma step_iterate_isProbabilityMeasure (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure ((step κ)^[k] μ) := by
  induction k with
  | zero => simpa using ‹IsProbabilityMeasure μ›
  | succ k ih =>
    have h := step_isProbabilityMeasure κ ((step κ)^[k] μ)
    simpa [Function.iterate_succ_apply'] using h

/-! ## The Cesaro average -/

/-- Cesaro average of the first `n+1` iterates of the one-step operator. -/
noncomputable def avg (κ : Kernel X X) (μ : Measure X) (n : ℕ) : Measure X :=
  ((n + 1 : ℝ≥0∞))⁻¹ • ∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ

lemma sum_apply_univ (s : Finset ℕ) (ν : ℕ → Measure X) :
    (∑ k ∈ s, ν k) Set.univ = ∑ k ∈ s, ν k Set.univ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, Measure.add_apply]

lemma avg_isProbabilityMeasure (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (avg κ μ n) := by
  constructor
  rw [avg, Measure.smul_apply, smul_eq_mul, sum_apply_univ]
  have h1 : ∀ k ∈ Finset.range (n + 1), (step κ)^[k] μ Set.univ = 1 := by
    intro k _
    exact @measure_univ X _ ((step κ)^[k] μ) (step_iterate_isProbabilityMeasure κ μ k)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    mul_comm]
  simp only [Nat.cast_add, Nat.cast_one]
  exact ENNReal.mul_inv_cancel (a := ((n : ℝ≥0∞) + 1)) (by simp) (by simp)

/-! ## Integrals against the average -/

lemma lintegral_avg [TopologicalSpace X] (κ : Kernel X X) (μ : Measure X) (n : ℕ)
    (f : X →ᵇ ℝ≥0) :
    ∫⁻ y, (f y : ℝ≥0∞) ∂(avg κ μ n)
      = ((n + 1 : ℝ≥0∞))⁻¹ *
        ∑ k ∈ Finset.range (n + 1), ∫⁻ y, (f y : ℝ≥0∞) ∂((step κ)^[k] μ) := by
  rw [avg, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp [smul_eq_mul]

lemma lintegral_step_avg [TopologicalSpace X] (κ : Kernel X X) (μ : Measure X) (n : ℕ)
    (f : X →ᵇ ℝ≥0) :
    ∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (avg κ μ n))
      = ((n + 1 : ℝ≥0∞))⁻¹ *
        ∑ k ∈ Finset.range (n + 1), ∫⁻ y, (f y : ℝ≥0∞) ∂((step κ)^[k + 1] μ) := by
  have h1 : step κ (avg κ μ n)
      = ((n + 1 : ℝ≥0∞))⁻¹ • ∑ k ∈ Finset.range (n + 1), (step κ)^[k + 1] μ := by
    have hsm : step κ (((n + 1 : ℝ≥0∞))⁻¹ • ∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ)
        = ((n + 1 : ℝ≥0∞))⁻¹ • step κ (∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ) :=
      step_smul κ ((n + 1 : ℝ≥0∞))⁻¹ _
    rw [avg, hsm, step_finset_sum κ (Finset.range (n + 1)) (fun k => (step κ)^[k] μ)]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by rw [step, Function.iterate_succ_apply']; rfl)
  rw [h1, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp [smul_eq_mul]

end SwarmKB

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The sequence of integrals of `f` against the iterates of `step`. -/
noncomputable def av (κ : Kernel X X) (μ : Measure X) (f : X →ᵇ ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, (f y : ℝ≥0∞) ∂((step κ)^[k] μ)

lemma av_le (f : X →ᵇ ℝ≥0) {C : ℝ≥0∞} (hC : ∀ x, (f x : ℝ≥0∞) ≤ C) (k : ℕ) :
    av κ μ f k ≤ C := by
  have hprob : IsProbabilityMeasure ((step κ)^[k] μ) := step_iterate_isProbabilityMeasure κ μ k
  calc av κ μ f k = ∫⁻ y, (f y : ℝ≥0∞) ∂((step κ)^[k] μ) := rfl
    _ ≤ ∫⁻ _y, C ∂((step κ)^[k] μ) := lintegral_mono hC
    _ = C := by
        rw [lintegral_const, @measure_univ X _ _ hprob, mul_one]

/-- Shifting the index forward in a finite sum of a bounded sequence costs at most the bound. -/
lemma sum_shift_le (a : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (ha : ∀ k, a k ≤ C) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), a (k + 1)) ≤ (∑ k ∈ Finset.range (n + 1), a k) + C := by
  rw [Finset.sum_range_succ (f := fun k => a (k + 1)) (n := n),
    Finset.sum_range_succ' (f := a) (n := n)]
  calc (∑ k ∈ Finset.range n, a (k + 1)) + a (n + 1)
      ≤ (∑ k ∈ Finset.range n, a (k + 1)) + C := by gcongr; exact ha (n + 1)
    _ ≤ ((∑ k ∈ Finset.range n, a (k + 1)) + a 0) + C := by
        rw [add_assoc]
        exact add_le_add_right le_add_self _

/-- The reverse inequality of `sum_shift_le`. -/
lemma sum_shift_ge (a : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (ha : ∀ k, a k ≤ C) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), a k) ≤ (∑ k ∈ Finset.range (n + 1), a (k + 1)) + C := by
  rw [Finset.sum_range_succ (f := fun k => a (k + 1)) (n := n),
    Finset.sum_range_succ' (f := a) (n := n)]
  calc (∑ k ∈ Finset.range n, a (k + 1)) + a 0
      ≤ (∑ k ∈ Finset.range n, a (k + 1)) + C := by gcongr; exact ha 0
    _ ≤ ((∑ k ∈ Finset.range n, a (k + 1)) + a (n + 1)) + C := by
        rw [add_assoc]
        exact add_le_add_right le_add_self _

end SwarmKB

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Cesaro one-step estimate.**  The average of the integrals against the first `n+1`
iterates and the integral against the push-forward of the Cesaro average differ by at
most `C/(n+1)`, where `C` bounds `f` pointwise. -/
lemma abs_avg_step_diff_le (f : X →ᵇ ℝ≥0) {C : ℝ≥0∞} (hC : ∀ x, (f x : ℝ≥0∞) ≤ C)
    (hCtop : C ≠ ⊤) (n : ℕ) :
    |((∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (avg κ μ n))).toReal
        - (∫⁻ y, (f y : ℝ≥0∞) ∂(avg κ μ n)).toReal)| ≤ C.toReal / (n + 1) := by
  have hane : ∀ k, av κ μ f k ≠ ⊤ := fun k => ne_top_of_le_ne_top hCtop (av_le f hC k)
  have hS0ne : (∑ k ∈ Finset.range (n + 1), av κ μ f k) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => hane k)
  have hS1ne : (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => hane (k + 1))
  have hb1 : (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1))
      ≤ (∑ k ∈ Finset.range (n + 1), av κ μ f k) + C :=
    sum_shift_le (fun k => av κ μ f k) C (fun k => av_le f hC k) n
  have hb2 : (∑ k ∈ Finset.range (n + 1), av κ μ f k)
      ≤ (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)) + C :=
    sum_shift_ge (fun k => av κ μ f k) C (fun k => av_le f hC k) n
  have hS0C : (∑ k ∈ Finset.range (n + 1), av κ μ f k) + C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hS0ne, hCtop⟩
  have hS1C : (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)) + C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hS1ne, hCtop⟩
  have hr1 : (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)).toReal
      ≤ (∑ k ∈ Finset.range (n + 1), av κ μ f k).toReal + C.toReal := by
    have h := ENNReal.toReal_mono hS0C hb1
    rwa [ENNReal.toReal_add hS0ne hCtop] at h
  have hr2 : (∑ k ∈ Finset.range (n + 1), av κ μ f k).toReal
      ≤ (∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)).toReal + C.toReal := by
    have h := ENNReal.toReal_mono hS1C hb2
    rwa [ENNReal.toReal_add hS1ne hCtop] at h
  have habs : |(∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)).toReal
      - (∑ k ∈ Finset.range (n + 1), av κ μ f k).toReal| ≤ C.toReal :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hEq1 : ∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (avg κ μ n))
      = ((n + 1 : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1) :=
    lintegral_step_avg κ μ n f
  have hEq2 : ∫⁻ y, (f y : ℝ≥0∞) ∂(avg κ μ n)
      = ((n + 1 : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (n + 1), av κ μ f k :=
    lintegral_avg κ μ n f
  rw [hEq1, hEq2, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hc : (((n + 1 : ℝ≥0∞))⁻¹).toReal = 1 / ((n : ℝ) + 1) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one, one_div]
  have hpos : (0:ℝ) ≤ 1 / ((n : ℝ) + 1) :=
    le_of_lt (one_div_pos.mpr (by positivity : (0:ℝ) < (n : ℝ) + 1))
  rw [hc, ← mul_sub, abs_mul, abs_of_nonneg hpos]
  calc 1 / ((n : ℝ) + 1) * |(∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)).toReal - (∑ k ∈ Finset.range (n + 1), av κ μ f k).toReal|
      = |(∑ k ∈ Finset.range (n + 1), av κ μ f (k + 1)).toReal - (∑ k ∈ Finset.range (n + 1), av κ μ f k).toReal| / ((n : ℝ) + 1) := by ring
    _ ≤ C.toReal / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right habs (le_of_lt (by positivity : (0:ℝ) < (n : ℝ) + 1))

/-- The Cesaro one-step difference tends to zero. -/
lemma tendsto_abs_avg_step_diff (f : X →ᵇ ℝ≥0) {C : ℝ≥0∞} (hC : ∀ x, (f x : ℝ≥0∞) ≤ C)
    (hCtop : C ≠ ⊤) :
    Tendsto (fun n => |((∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (avg κ μ n))).toReal
        - (∫⁻ y, (f y : ℝ≥0∞) ∂(avg κ μ n)).toReal)|) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C.toReal * (1 / ((n : ℝ) + 1))) atTop (𝓝 (C.toReal * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => abs_nonneg _) (fun n => ?_)
  have h := abs_avg_step_diff_le (κ := κ) (μ := μ) f hC hCtop n
  rwa [div_eq_mul_one_div] at h

end SwarmKB

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The Cesaro one-step difference itself (not its absolute value) tends to zero. -/
lemma tendsto_avg_step_diff (f : X →ᵇ ℝ≥0) {C : ℝ≥0∞} (hC : ∀ x, (f x : ℝ≥0∞) ≤ C)
    (hCtop : C ≠ ⊤) :
    Tendsto (fun n => ((∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (avg κ μ n))).toReal
        - (∫⁻ y, (f y : ℝ≥0∞) ∂(avg κ μ n)).toReal)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using tendsto_abs_avg_step_diff (κ := κ) (μ := μ) f hC hCtop

end SwarmKB

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Pointwise bounded measurable functions integrate to at most their bound against a
probability measure. -/
lemma lintegral_coe_le_of_bound {ν : Measure X} [IsProbabilityMeasure ν] (f : X →ᵇ ℝ≥0)
    {C : ℝ≥0∞} (hC : ∀ x, (f x : ℝ≥0∞) ≤ C) :
    ∫⁻ y, (f y : ℝ≥0∞) ∂ν ≤ C := by
  calc ∫⁻ y, (f y : ℝ≥0∞) ∂ν ≤ ∫⁻ _y, C ∂ν := lintegral_mono hC
    _ = C := by rw [lintegral_const, measure_univ, mul_one]

/-- A pointwise bound for an `ℝ≥0`-valued bounded continuous function. -/
lemma exists_pointwise_bound (f : X →ᵇ ℝ≥0) : ∃ C : ℝ≥0, ∀ x, f x ≤ C :=
  ⟨nndist f 0, fun x => BoundedContinuousFunction.NNReal.upper_bound f x⟩

end SwarmKB
