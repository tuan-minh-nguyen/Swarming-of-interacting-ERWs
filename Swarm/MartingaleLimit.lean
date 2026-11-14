/-
The martingale strong law used throughout §2 of `main_1d_revised.tex`
(Hall–Heyde, Theorem 2.18): if `Q` is a martingale whose increments have
summable squared expectations when weighted by `1/(n+1)^2`, then `Q n / n → 0`
almost surely, and moreover the running maximum is `o(n)`.

This is the analytic engine of Proposition `group` (separated groups) and
Proposition `ball` (ballistic lower bound) of the paper.  Mathlib has Doob's
almost-sure convergence theorem for L¹-bounded submartingales but not this
consequence, so the module proves it from scratch.  No hypotheses are assumed
beyond the paper's, and nothing is weakened: the increments of `Q` need only be
square integrable.
-/
import Swarm.Imports

open Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace MartingaleLimit

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ## Increments of a martingale -/

/-- The increment `Q (n+1) - Q n` of a process. -/
noncomputable def inc (Q : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := Q (n + 1) - Q n

@[simp] lemma inc_apply (Q : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    inc Q n ω = Q (n + 1) ω - Q n ω := rfl

/-- **Martingale increments have zero mean.** -/
theorem integral_inc_eq_zero [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (n : ℕ) : ∫ ω, inc Q n ω ∂μ = 0 := by
  have hint1 : Integrable (Q (n + 1)) μ := hQ.integrable (n + 1)
  have hint0 : Integrable (Q n) μ := hQ.integrable n
  have hce : μ[Q (n + 1) | ℱ n] =ᵐ[μ] Q n := hQ.condExp_ae_eq (Nat.le_succ n)
  have h1 : ∫ ω, μ[Q (n + 1) | ℱ n] ω ∂μ = ∫ ω, Q n ω ∂μ := integral_congr_ae hce
  have h2 : ∫ ω, μ[Q (n + 1) | ℱ n] ω ∂μ = ∫ ω, Q (n + 1) ω ∂μ :=
    integral_condExp (ℱ.le n)
  have hsub : ∫ ω, inc Q n ω ∂μ = ∫ ω, Q (n + 1) ω ∂μ - ∫ ω, Q n ω ∂μ :=
    integral_sub hint1 hint0
  rw [hsub, ← h2, h1, sub_self]

/-- The conditional expectation of a martingale increment vanishes. -/
theorem condExp_inc_eq_zero [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (n : ℕ) : μ[inc Q n | ℱ n] =ᵐ[μ] 0 := by
  have hint1 : Integrable (Q (n + 1)) μ := hQ.integrable (n + 1)
  have hint0 : Integrable (Q n) μ := hQ.integrable n
  have hce : μ[Q (n + 1) | ℱ n] =ᵐ[μ] Q n := hQ.condExp_ae_eq (Nat.le_succ n)
  have hself : μ[Q n | ℱ n] = Q n :=
    condExp_of_stronglyMeasurable (ℱ.le n) (hQ.stronglyAdapted n) hint0
  have hsub : μ[inc Q n | ℱ n] =ᵐ[μ] μ[Q (n + 1) | ℱ n] - μ[Q n | ℱ n] :=
    condExp_sub hint1 hint0 (ℱ n : MeasurableSpace Ω)
  filter_upwards [hsub, hce] with ω h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
  rw [h1, h2, hself, sub_self]

/-- The increment is integrable. -/
theorem integrable_inc [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (n : ℕ) : Integrable (inc Q n) μ :=
  (hQ.integrable (n + 1)).sub (hQ.integrable n)

/-- **Orthogonality of martingale increments against the past.** -/
theorem integral_mul_inc_eq_zero [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) {n : ℕ} {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ n] g) (hgm : Integrable (fun ω => g ω * inc Q n ω) μ) :
    ∫ ω, g ω * inc Q n ω ∂μ = 0 := by
  have hci : Integrable (inc Q n) μ := integrable_inc hQ n
  have hpull : μ[(fun ω => g ω * inc Q n ω) | ℱ n] =ᵐ[μ]
      fun ω => g ω * μ[inc Q n | ℱ n] ω :=
    condExp_mul_of_stronglyMeasurable_left hg hgm hci
  have hzero : μ[inc Q n | ℱ n] =ᵐ[μ] 0 := condExp_inc_eq_zero hQ n
  have hprod : μ[(fun ω => g ω * inc Q n ω) | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, mul_zero]
  have h1 : ∫ ω, μ[(fun ω => g ω * inc Q n ω) | ℱ n] ω ∂μ
      = ∫ ω, g ω * inc Q n ω ∂μ := integral_condExp (ℱ.le n)
  have h2 : ∫ ω, μ[(fun ω => g ω * inc Q n ω) | ℱ n] ω ∂μ = 0 := by
    rw [integral_congr_ae hprod]; simp
  rw [← h1, h2]

/-! ## Elementary square-integrability lemmas -/

section SqHelpers

/-- The product of two square-integrable functions is integrable (Cauchy–Schwarz). -/
theorem integrable_mul_of_sq {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have hmaj : Integrable (fun ω => (f ω ^ 2 + g ω ^ 2) / 2) μ :=
    (hf2.add hg2).div_const 2
  refine Integrable.mono' hmaj (hf.mul hg) ?_
  filter_upwards with ω
  have h1 : |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
  have h2 : (|f ω| - |g ω|) ^ 2 ≥ 0 := sq_nonneg _
  have h3 : |f ω| * |g ω| ≤ (f ω ^ 2 + g ω ^ 2) / 2 := by
    have h4 := sq_abs (f ω); have h5 := sq_abs (g ω); nlinarith
  rw [Real.norm_eq_abs, h1]
  exact h3

end SqHelpers

/-! ## The weighted martingale of increments -/

/-- The `1/(k+1)`-weighted sum of the increments of `Q`; Kronecker's input. -/
noncomputable def weightedSum (Q : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range n, fun ω => ((k : ℝ) + 1)⁻¹ * inc Q k ω

lemma weightedSum_zero (Q : ℕ → Ω → ℝ) : weightedSum Q 0 = 0 := by
  simp [weightedSum]

lemma weightedSum_succ (Q : ℕ → Ω → ℝ) (n : ℕ) :
    weightedSum Q (n + 1) = weightedSum Q n + fun ω => ((n : ℝ) + 1)⁻¹ * inc Q n ω := by
  simp [weightedSum, Finset.sum_range_succ]

/-- The weighted sum is adapted. -/
lemma stronglyMeasurable_weightedSum [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (n : ℕ) : StronglyMeasurable[ℱ n] (weightedSum Q n) := by
  refine Finset.stronglyMeasurable_sum _ ?_
  intro k hk
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hsm : StronglyMeasurable[ℱ n] (inc Q k) :=
    ((hQ.stronglyAdapted (k + 1)).mono (ℱ.mono hk')).sub
      ((hQ.stronglyAdapted k).mono (ℱ.mono (Nat.le_of_succ_le hk')))
  exact hsm.const_mul _

/-- A finite sum of almost-everywhere equal functions is almost everywhere equal. -/
lemma finset_ae_sum_congr {ι M : Type*} [AddCommMonoid M] {s : Finset ι}
    {f g : ι → Ω → M} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (∑ i ∈ s, f i) =ᵐ[μ] ∑ i ∈ s, g i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add
        (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- Truncating a sum at `i` using an indicator. -/
lemma sum_range_ite_lt {M : Type*} [AddCommMonoid M] {g : ℕ → M} {i j : ℕ} (hij : i ≤ j) :
    (∑ k ∈ Finset.range j, (if k < i then g k else 0)) = ∑ k ∈ Finset.range i, g k := by
  rw [← Nat.add_sub_of_le hij, Finset.sum_range_add]
  have h4 : (∑ k ∈ Finset.range i, (if k < i then g k else 0)) = ∑ k ∈ Finset.range i, g k :=
    Finset.sum_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.1 hk)])
  have h5 : (∑ k ∈ Finset.range (j - i), (if i + k < i then g (i + k) else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [if_neg (by omega)]
  rw [h4, h5, add_zero]

/-- The weighted sum of the increments of a martingale is itself a martingale. -/
theorem martingale_weightedSum [IsFiniteMeasure μ] {Q : ℕ → Ω → ℝ} (hQ : Martingale Q ℱ μ) :
    Martingale (weightedSum Q) ℱ μ := by
  refine ⟨fun n => stronglyMeasurable_weightedSum hQ n, ?_⟩
  intro i j hij
  let g : ℕ → Ω → ℝ := fun k ω => ((k : ℝ) + 1)⁻¹ * inc Q k ω
  have hFint : ∀ k, Integrable (g k) μ := fun k => (integrable_inc hQ k).const_mul _
  have hsum : ∀ k : ℕ, μ[g k | ℱ i] =ᵐ[μ] (if k < i then g k else 0) := by
    intro k
    split_ifs with hk
    · have hle : ℱ (k + 1) ≤ ℱ i := ℱ.mono (Nat.succ_le_of_lt hk)
      have hsm : StronglyMeasurable[ℱ i] (inc Q k) :=
        ((hQ.stronglyAdapted (k + 1)).mono hle).sub
          ((hQ.stronglyAdapted k).mono (ℱ.mono hk.le))
      have hce : μ[inc Q k | ℱ i] = inc Q k :=
        condExp_of_stronglyMeasurable (ℱ.le i) hsm (integrable_inc hQ k)
      have hsmul := condExp_smul (μ := μ) ((k : ℝ) + 1)⁻¹ (inc Q k) (ℱ i : MeasurableSpace Ω)
      calc μ[g k | ℱ i] = μ[((k : ℝ) + 1)⁻¹ • inc Q k | ℱ i] := rfl
        _ =ᵐ[μ] ((k : ℝ) + 1)⁻¹ • μ[inc Q k | ℱ i] := hsmul
        _ = g k := by rw [hce]; rfl
    · have hik : i ≤ k := Nat.le_of_not_lt hk
      have hle : ℱ i ≤ ℱ k := ℱ.mono hik
      have htower : μ[μ[inc Q k | ℱ k] | ℱ i] =ᵐ[μ] μ[inc Q k | ℱ i] :=
        condExp_condExp_of_le hle (ℱ.le k)
      have hzero : μ[inc Q k | ℱ k] =ᵐ[μ] 0 := condExp_inc_eq_zero hQ k
      have hstep : μ[μ[inc Q k | ℱ k] | ℱ i] =ᵐ[μ] μ[(0 : Ω → ℝ) | ℱ i] :=
        condExp_congr_ae hzero
      have hstep0 : μ[μ[inc Q k | ℱ k] | ℱ i] =ᵐ[μ] 0 := by
        refine hstep.trans ?_
        rw [condExp_zero]
      have hce : μ[inc Q k | ℱ i] =ᵐ[μ] 0 := htower.symm.trans hstep0
      have hsmul := condExp_smul (μ := μ) ((k : ℝ) + 1)⁻¹ (inc Q k) (ℱ i : MeasurableSpace Ω)
      calc μ[g k | ℱ i] = μ[((k : ℝ) + 1)⁻¹ • inc Q k | ℱ i] := rfl
        _ =ᵐ[μ] ((k : ℝ) + 1)⁻¹ • μ[inc Q k | ℱ i] := hsmul
        _ =ᵐ[μ] ((k : ℝ) + 1)⁻¹ • (0 : Ω → ℝ) := by
            filter_upwards [hce] with ω hω
            simp only [Pi.smul_apply, hω, Pi.zero_apply, smul_zero]
        _ = 0 := by simp
  have h1 := condExp_finsetSum (s := Finset.range j) (f := g) (fun k _ => hFint k)
    (ℱ i : MeasurableSpace Ω)
  have h2 : (∑ k ∈ Finset.range j, μ[g k | ℱ i]) =ᵐ[μ]
      ∑ k ∈ Finset.range j, (if k < i then g k else 0) :=
    finset_ae_sum_congr (fun k _ => hsum k)
  have h3 : (∑ k ∈ Finset.range j, (if k < i then g k else 0)) = ∑ k ∈ Finset.range i, g k :=
    sum_range_ite_lt hij
  show μ[∑ k ∈ Finset.range j, g k | ℱ i] =ᵐ[μ] (∑ k ∈ Finset.range i, g k)
  exact h3 ▸ h1.trans h2

/-! ## The L² identity for the weighted sum -/

/-- **Exact second moment of the weighted sum.**  The cross terms vanish by
orthogonality of martingale increments, so the second moment is the sum of the
weighted increment variances. -/
theorem weightedSum_sq_integral [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (hint : ∀ k : ℕ, Integrable (fun ω => (inc Q k ω) ^ 2) μ)
    (n : ℕ) :
    Integrable (weightedSum Q n) μ ∧
      Integrable (fun ω => (weightedSum Q n ω) ^ 2) μ ∧
      ∫ ω, (weightedSum Q n ω) ^ 2 ∂μ
        = ∑ k ∈ Finset.range n, (((k : ℝ) + 1)⁻¹) ^ 2 * ∫ ω, (inc Q k ω) ^ 2 ∂μ := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    obtain ⟨hS1, hS2, hval⟩ := ih
    have hb1 : Integrable (inc Q n) μ := integrable_inc hQ n
    have hb2 : Integrable (fun ω => (inc Q n ω) ^ 2) μ := hint n
    have hSmeas : AEStronglyMeasurable (weightedSum Q n) μ :=
      ((stronglyMeasurable_weightedSum hQ n).mono (ℱ.le n)).aestronglyMeasurable
    have hSb : Integrable (fun ω => weightedSum Q n ω * inc Q n ω) μ :=
      integrable_mul_of_sq hSmeas hb1.aestronglyMeasurable hS2 hb2
    have horth : ∫ ω, weightedSum Q n ω * inc Q n ω ∂μ = 0 :=
      integral_mul_inc_eq_zero hQ (stronglyMeasurable_weightedSum hQ n) hSb
    have h1 : Integrable (fun ω => 2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω)) μ :=
      hSb.const_mul _
    have h2 : Integrable (fun ω => ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2) μ :=
      hb2.const_mul _
    have hpt : (fun ω => (weightedSum Q (n + 1) ω) ^ 2)
        = fun ω => (weightedSum Q n ω) ^ 2
            + (2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω)
              + ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2) := by
      funext ω
      rw [weightedSum_succ]
      simp only [Pi.add_apply]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [weightedSum_succ]
      exact hS1.add (hb1.const_mul _)
    · rw [hpt]
      exact hS2.add (h1.add h2)
    · rw [hpt]
      have s1 : ∫ ω, (weightedSum Q n ω) ^ 2
            + (2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω)
              + ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2) ∂μ
          = (∫ ω, (weightedSum Q n ω) ^ 2 ∂μ)
            + ∫ ω, (2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω)
              + ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2) ∂μ :=
        integral_add hS2 (h1.add h2)
      have s2 : ∫ ω, 2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω)
            + ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2 ∂μ
          = (∫ ω, 2 * ((n : ℝ) + 1)⁻¹ * (weightedSum Q n ω * inc Q n ω) ∂μ)
            + ∫ ω, ((n : ℝ) + 1)⁻¹ ^ 2 * (inc Q n ω) ^ 2 ∂μ :=
        integral_add h1 h2
      rw [s1, s2, integral_const_mul, integral_const_mul, horth, Finset.sum_range_succ, ← hval]
      ring

/-! ## Kronecker's lemma -/

/-- `((n : ℝ) + 1) / n → 1`. -/
lemma tendsto_succ_div_self : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
  have h_inv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 1 + ((n : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h_inv
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

/-- **Kronecker's lemma**, in the form used by the martingale strong law: if the series
`∑ a k` converges then `(∑_{k<n} (k+1) a k)/n → 0`.  The identity used is the Abel
summation formula `∑_{k<n} (k+1) a k = (n+1) T_n - ∑_{k≤n} T_k`. -/
theorem kronecker {a : ℕ → ℝ} {T : ℝ}
    (hT : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, a k) atTop (𝓝 T)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * a k) / n) atTop (𝓝 0) := by
  set Tf : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, a k with hTf
  have hTf_succ : ∀ n : ℕ, Tf (n + 1) = Tf n + a n := by
    intro n
    simp only [hTf]
    exact Finset.sum_range_succ a n
  have hkey : ∀ n : ℕ, (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * a k)
      = ((n : ℝ) + 1) * Tf n - ∑ k ∈ Finset.range (n + 1), Tf k := by
    intro n
    induction n with
    | zero => simp [hTf]
    | succ n ih =>
      have h1 : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * a k)
          = (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * a k) + ((n : ℝ) + 1) * a n :=
        Finset.sum_range_succ _ n
      have h2 : (∑ k ∈ Finset.range (n + 1 + 1), Tf k)
          = (∑ k ∈ Finset.range (n + 1), Tf k) + Tf (n + 1) := by
        simpa using Finset.sum_range_succ Tf (n + 1)
      rw [h1, ih, h2, hTf_succ n]
      push_cast
      ring
  have hces : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, Tf k) atTop (𝓝 T) := by
    simpa only [hTf] using hT.cesaro
  have hces' : Tendsto (fun n : ℕ => (((n + 1 : ℕ)) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), Tf k)
      atTop (𝓝 T) := hces.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n : ℕ =>
      Tf n - (((n + 1 : ℕ)) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), Tf k) atTop (𝓝 (T - T)) :=
    hT.sub hces'
  have hprod : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n *
      (Tf n - (((n + 1 : ℕ)) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), Tf k)) atTop (𝓝 0) := by
    have := tendsto_succ_div_self.mul hdiff
    simpa using this
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hn1 : (((n + 1 : ℕ)) : ℝ) ≠ 0 := by
    have : (0:ℕ) < n + 1 := Nat.succ_pos n
    exact_mod_cast Nat.ne_of_gt this
  rw [hkey n]
  push_cast
  field_simp

/-! ## The martingale strong law -/

/-- Sums of increments telescope. -/
lemma sum_inc (Q : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, inc Q k ω = Q n ω - Q 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, inc_apply]
    ring

/-- **Hall–Heyde's martingale strong law (Theorem 2.18).**

If `Q` is a martingale and `∑_k E[(Q_{k+1}-Q_k)^2]/(k+1)^2 < ∞`, then `Q n / n → 0`
almost surely.  The proof is Doob's a.e. convergence theorem applied to the
`L²`-bounded martingale `∑_k (Q_{k+1}-Q_k)/(k+1)`, followed by Kronecker's lemma. -/
theorem martingale_strong_law [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (hint : ∀ k : ℕ, Integrable (fun ω => (inc Q k ω) ^ 2) μ)
    (hsum : Summable fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 2 * ∫ ω, (inc Q k ω) ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (Q n ω - Q 0 ω) / n) atTop (𝓝 0) := by
  set C : ℝ := ∑' k : ℕ, (((k : ℝ) + 1)⁻¹) ^ 2 * ∫ ω, (inc Q k ω) ^ 2 ∂μ with hC
  have hCnn : 0 ≤ C := tsum_nonneg (fun k => by positivity)
  have hbound : ∀ n : ℕ, ∫ ω, (weightedSum Q n ω) ^ 2 ∂μ ≤ C := by
    intro n
    rw [(weightedSum_sq_integral hQ hint n).2.2]
    exact hsum.sum_le_tsum _ (fun k _ => by positivity)
  have hL1 : ∀ n : ℕ, eLpNorm (weightedSum Q n) 1 μ ≤ ENNReal.ofReal ((1 + C) / 2) := by
    intro n
    have hint1 : Integrable (weightedSum Q n) μ := (weightedSum_sq_integral hQ hint n).1
    have hint2 : Integrable (fun ω => (weightedSum Q n ω) ^ 2) μ :=
      (weightedSum_sq_integral hQ hint n).2.1
    have hmono : ∫ ω, |weightedSum Q n ω| ∂μ ≤ (1 + C) / 2 := by
      have habs : Integrable (fun ω => |weightedSum Q n ω|) μ := hint1.abs
      have hmaj : Integrable (fun ω => (1 + (weightedSum Q n ω) ^ 2) / 2) μ :=
        ((integrable_const 1).add hint2).div_const 2
      have hle1 : ∫ ω, |weightedSum Q n ω| ∂μ
          ≤ ∫ ω, (1 + (weightedSum Q n ω) ^ 2) / 2 ∂μ := by
        refine integral_mono habs hmaj (fun ω => ?_)
        nlinarith [abs_nonneg (weightedSum Q n ω), sq_abs (weightedSum Q n ω),
          sq_nonneg (1 - |weightedSum Q n ω|)]
      have hle2 : ∫ ω, (1 + (weightedSum Q n ω) ^ 2) / 2 ∂μ ≤ (1 + C) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) hint2, integral_const]
        simp only [smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, mul_one]
        linarith [hbound n]
      linarith
    calc eLpNorm (weightedSum Q n) 1 μ = ∫⁻ ω, ‖weightedSum Q n ω‖ₑ ∂μ :=
          eLpNorm_one_eq_lintegral_enorm
      _ = ∫⁻ ω, ENNReal.ofReal |weightedSum Q n ω| ∂μ := by
          simp only [Real.enorm_eq_ofReal_abs]
      _ = ENNReal.ofReal (∫ ω, |weightedSum Q n ω| ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint1.abs
            (Eventually.of_forall (fun _ => abs_nonneg _))).symm
      _ ≤ ENNReal.ofReal ((1 + C) / 2) := ENNReal.ofReal_le_ofReal hmono
  have hdoob : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => weightedSum Q n ω) atTop (𝓝 c) := by
    refine Submartingale.exists_ae_tendsto_of_bdd (R := Real.toNNReal ((1 + C) / 2))
      (martingale_weightedSum hQ).submartingale ?_
    intro n
    exact hL1 n
  filter_upwards [hdoob] with ω hconv
  obtain ⟨c, hc⟩ := hconv
  have hconv' : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ * inc Q k ω)
      atTop (𝓝 c) := by
    simpa only [weightedSum, Finset.sum_apply] using hc
  refine (kronecker (a := fun k : ℕ => ((k : ℝ) + 1)⁻¹ * inc Q k ω) (T := c) hconv').congr' ?_
  filter_upwards with n
  have hpt : (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (((k : ℝ) + 1)⁻¹ * inc Q k ω))
      = ∑ k ∈ Finset.range n, inc Q k ω := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hpt, sum_inc]

/-! ## The running maximum is `o(n)` -/

/-- **Upgrade of an `o(n)` limit to its running maximum** (paper: after the martingale
strong law, "the first `k` terms contribute `O(1)` and the remaining terms are at most
`ε n`"). -/
theorem tendsto_running_max [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω / n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ n → |Q t ω| ≤ ε * n := by
  filter_upwards [h] with ω hω ε hε
  have habs : Tendsto (fun n : ℕ => |Q n ω| / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => |Q n ω / n|) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun n : ℕ => |Q n ω / n|) atTop (𝓝 |(0 : ℝ)|) :=
        (continuous_abs.tendsto (0 : ℝ)).comp hω
      simpa using hcomp
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, Nat.abs_cast]
  have hhalf : ∀ᶠ n : ℕ in atTop, |Q n ω| < (ε / 2) * n := by
    have hIio : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by linarith)
    filter_upwards [habs.eventually hIio, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hn0'] at hn
    linarith
  obtain ⟨K, hK⟩ := eventually_atTop.1 hhalf
  set C : ℝ := ∑ t ∈ Finset.range K, |Q t ω| with hCdef
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun t _ => abs_nonneg _)
  refine eventually_atTop.2 ⟨max K (Nat.ceil (C / ε) + 1), ?_⟩
  intro n hn t ht
  have hnK : K ≤ n := le_trans (le_max_left _ _) hn
  have hnC : Nat.ceil (C / ε) + 1 ≤ n := le_trans (le_max_right _ _) hn
  rcases lt_or_ge t K with hlt | hge
  · have hmem : t ∈ Finset.range K := Finset.mem_range.2 hlt
    have htC : |Q t ω| ≤ C := by
      rw [hCdef]
      exact Finset.single_le_sum (f := fun t => |Q t ω|) (fun i _ => abs_nonneg _) hmem
    have hCle : C ≤ ε * n := by
      have h1 : C / ε ≤ (Nat.ceil (C / ε) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (C / ε) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (Nat.le_succ _) hnC
      rw [div_le_iff₀ hε] at h1
      nlinarith
    linarith
  · have h1 : |Q t ω| < (ε / 2) * t := hK t hge
    have h2 : (ε / 2) * t ≤ (ε / 2) * n := by
      have : (t : ℝ) ≤ n := by exact_mod_cast ht
      nlinarith
    have h3 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

/-- The paper's `max_{0 ≤ t ≤ n} |Q_t| = o(n)` in limit form. -/
theorem running_max_div [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω / n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩ (fun t => |Q t ω|)
        ≤ ε * n := by
  filter_upwards [tendsto_running_max h] with ω hω ε hε
  filter_upwards [hω ε hε] with n hn
  refine Finset.sup'_le _ _ ?_
  intro t ht
  exact hn t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))

/-! ## The paper's logarithmic variance regime

Propositions `ball` and `group` apply the martingale strong law to martingales whose
increments satisfy `E[(Q_{k+1}-Q_k)^2] ≤ C log⁴(k+2)`; the summability hypothesis of
`martingale_strong_law` is verified here once and for all. -/

section LogVariance

lemma log_le_rpow_div {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) : Real.log x ≤ x ^ ε / ε := by
  have hxε : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx ε
  have h := Real.log_le_sub_one_of_pos hxε
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hε]
  nlinarith

/-- `(log x)^4 ≤ 4096 * x^(1/2)` for `x ≥ 1`. -/
lemma log_pow_four_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 4 ≤ 4096 * x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h8 : Real.log x ≤ x ^ (1 / 8 : ℝ) / (1 / 8) := log_le_rpow_div hx0 (by norm_num)
  have hdiv : x ^ (1 / 8 : ℝ) / (1 / 8) = 8 * x ^ (1 / 8 : ℝ) := by
    field_simp
  have h8' : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by rw [hdiv] at h8; exact h8
  have hpow : (Real.log x) ^ 4 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ hlog0 h8' 4
  have hxpos : (0 : ℝ) ≤ x := le_of_lt hx0
  have hrw : (8 * x ^ (1 / 8 : ℝ)) ^ 4 = 4096 * x ^ (1 / 2 : ℝ) := by
    rw [mul_pow]
    have h2 : (x ^ (1 / 8 : ℝ)) ^ 4 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos]
      norm_num
    rw [h2]
    norm_num
  rw [hrw] at hpow
  exact hpow

/-- `∑_k (k+1)⁻² (log (k+2))⁴ < ∞`. -/
theorem summable_log_four_div_sq :
    Summable (fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 4) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Real.summable_nat_rpow).2 (by norm_num)
  have hshift : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
    have h := hbase.comp_injective (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ))
      (i := fun k : ℕ => k + 1) (fun a b hab => Nat.succ_injective hab)
    have heq : (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2) : ℝ))
        = (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) ∘ fun k : ℕ => k + 1 := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact h
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hshift.mul_left (4096 * 2))
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlog : (Real.log ((k : ℝ) + 2)) ^ 4 ≤ 4096 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ) :=
    log_pow_four_le_sqrt (by linarith)
  have hstep1 : (((k : ℝ) + 1)⁻¹) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 4
      ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (4096 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hfour : ((4 : ℝ)) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hstep3 : ((k : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ 2 * ((k : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    have h1 : ((k : ℝ) + 2) ≤ 4 * ((k : ℝ) + 1) := by linarith
    calc ((k : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (4 * ((k : ℝ) + 1)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      _ = 2 * ((k : ℝ) + 1) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hk1.le, hfour]
  have hbase1 : (((k : ℝ) + 1)⁻¹) ^ 2 = ((k : ℝ) + 1) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hk1.le, Real.rpow_two, inv_pow]
  have hident : (((k : ℝ) + 1)⁻¹) ^ 2 * (2 * ((k : ℝ) + 1) ^ (1 / 2 : ℝ))
      = 4096 * (((k : ℝ) + 1) ^ (-(3 / 2) : ℝ)) * 2 / 4096 := by
    rw [hbase1, show (-(3 / 2) : ℝ) = -(2 : ℝ) + 1 / 2 by ring, Real.rpow_add hk1]
    field_simp
  calc (((k : ℝ) + 1)⁻¹) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 4
      ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (4096 * ((k : ℝ) + 2) ^ (1 / 2 : ℝ)) := hstep1
    _ ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (4096 * (2 * ((k : ℝ) + 1) ^ (1 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [hstep3]
    _ = 4096 * 2 * (((k : ℝ) + 1) ^ (-(3 / 2) : ℝ)) := by
        rw [hbase1, show (-(3 / 2) : ℝ) = -(2 : ℝ) + 1 / 2 by ring, Real.rpow_add hk1]
        ring

/-- **The martingale strong law with the paper's logarithmic variance bound.** -/
theorem martingale_strong_law_of_log_variance [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQ : Martingale Q ℱ μ) (hint : ∀ k : ℕ, Integrable (fun ω => (inc Q k ω) ^ 2) μ)
    {C : ℝ}
    (hvar : ∀ k : ℕ, ∫ ω, (inc Q k ω) ^ 2 ∂μ ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (Q n ω - Q 0 ω) / n) atTop (𝓝 0) := by
  refine martingale_strong_law hQ hint ?_
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_log_four_div_sq.mul_left C)
  have h1 : ∫ ω, (inc Q k ω) ^ 2 ∂μ ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4 := hvar k
  have h2 : (0 : ℝ) ≤ (((k : ℝ) + 1)⁻¹) ^ 2 := by positivity
  calc (((k : ℝ) + 1)⁻¹) ^ 2 * ∫ ω, (inc Q k ω) ^ 2 ∂μ
      ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (C * (Real.log ((k : ℝ) + 2)) ^ 4) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = C * ((((k : ℝ) + 1)⁻¹) ^ 2 * (Real.log ((k : ℝ) + 2)) ^ 4) := by ring


end LogVariance


end MartingaleLimit
