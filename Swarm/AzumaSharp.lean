/-
# Side-condition-free maximal Azuma–Hoeffding

`LocMaxVar.measure_max_abs_psum_ge_le_ae` (and its one-sided ancestors in `Azuma.lean`) require
the Chernoff side condition `ε * c k ≤ 2 * S` for every `k < n`.  At the paper's local scale
(`c = 2 envB`, `S = K (2 envB)²`, `ε = L^{3/4}`, `B = L^{1/16}`) that condition is exactly
`L ≤ t - s`, the restriction recorded in `LOC_MOVE_COMPOSE.md`.  It is not a real restriction of
the inequality: it is an artefact of bounding the exponential by `1 + x + x²` on `|x| ≤ 1`.

With `WCJFSharp.condExp_exp_mul_le_half` the exponential moment bound holds for **every**
`t > 0` with the sharp constant `t² c²/2`, so no truncation and no side condition is needed:

* `integral_exp_psum_le_all` — `∫ exp (t · psum ξ n) ≤ exp (t² proxy c n / 2)` for all `t > 0`;
* `measure_psum_ge_le_sharp` — one-sided Chernoff `≤ exp (-ε² / (2 proxy c n))` for all `ε > 0`;
* `measure_max_abs_psum_ge_le_sharp` — maximal two-sided bound
  `≤ 2 (n+1) exp (-ε²/(2 S))` for all `ε > 0`, with `proxy c n ≤ S`.

This is strictly stronger than the accepted statement: same union factor `(n+1)`, exponent better
by a factor `2`, and **no hypothesis** linking `ε`, `c` and `S`.

No `sorry`, no new axiom.
-/
import Swarm.CondHoeffSharp
import Swarm.LocMaxVar

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace WCJFSharp

open LocMart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {ξ : ℕ → Ω → ℝ} {c : ℕ → ℝ} {t : ℝ}

/-- Almost-sure envelope of the partial sums by the summed envelopes. -/
theorem ae_abs_psum_le_sum [IsProbabilityMeasure μ]
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k) (n : ℕ) :
    ∀ᵐ ω ∂μ, |psum ξ n ω| ≤ ∑ k ∈ Finset.range n, c k := by
  induction n with
  | zero => filter_upwards with ω; simp [psum_zero]
  | succ n ih =>
    filter_upwards [ih, hbdd n] with ω h1 h2
    rw [psum_succ, Finset.sum_range_succ]
    calc |psum ξ n ω + ξ n ω| ≤ |psum ξ n ω| + |ξ n ω| := abs_add_le _ _
      _ ≤ (∑ k ∈ Finset.range n, c k) + c n := add_le_add h1 h2

/-- The exponential moment bound at every horizon, for **all** `t > 0`, from a.e. envelopes and
vanishing conditional means. -/
theorem integral_exp_psum_le_all [IsProbabilityMeasure μ]
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k, 0 ≤ c k) (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0) (ht : 0 < t) (n : ℕ) :
    ∫ ω, Real.exp (t * psum ξ n ω) ∂μ ≤ Real.exp (t ^ 2 * LocMax.proxy c n / 2) := by
  letI : MeasurableSpace Ω := m0
  -- a.e. envelope of the partial sums
  have hbS : ∀ n, ∀ᵐ ω ∂μ, |psum ξ n ω| ≤ ∑ k ∈ Finset.range n, c k :=
    fun n => ae_abs_psum_le_sum (μ := μ) hbdd n
  have hSb : ∀ n, ∀ᵐ ω ∂μ, Real.exp (t * psum ξ n ω)
      ≤ Real.exp (t * ∑ k ∈ Finset.range n, c k) := by
    intro n
    filter_upwards [hbS n] with ω hω
    refine Real.exp_le_exp.2 ?_
    calc t * psum ξ n ω ≤ |t * psum ξ n ω| := le_abs_self _
      _ = t * |psum ξ n ω| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ t * ∑ k ∈ Finset.range n, c k := mul_le_mul_of_nonneg_left hω ht.le
  have hmeasS : ∀ n, AEStronglyMeasurable (fun ω => Real.exp (t * psum ξ n ω)) μ := by
    intro n
    exact Real.continuous_exp.comp_aestronglyMeasurable
      (((stronglyMeasurable_psum hmeas n).mono (ℱ.le n)).const_mul t).aestronglyMeasurable
  have hexpint : ∀ n, Integrable (fun ω => Real.exp (t * psum ξ n ω)) μ := by
    intro n
    refine Integrable.of_bound (hmeasS n) (Real.exp (t * ∑ k ∈ Finset.range n, c k)) ?_
    filter_upwards [hbS n] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc t * psum ξ n ω ≤ |t * psum ξ n ω| := le_abs_self _
      _ = t * |psum ξ n ω| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ t * ∑ k ∈ Finset.range n, c k :=
          mul_le_mul_of_nonneg_left hω ht.le
  have hξb : ∀ k, ∀ᵐ ω ∂μ, Real.exp (t * ξ k ω) ≤ Real.exp (t * c k) := by
    intro k
    filter_upwards [hbdd k] with ω hω
    refine Real.exp_le_exp.2 ?_
    calc t * ξ k ω ≤ |t * ξ k ω| := le_abs_self _
      _ = t * |ξ k ω| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ t * c k := mul_le_mul_of_nonneg_left hω ht.le
  have hξint : ∀ k, Integrable (fun ω => Real.exp (t * ξ k ω)) μ := by
    intro k
    refine Integrable.of_bound
      (Real.continuous_exp.comp_aestronglyMeasurable
        (((hmeas k).mono (ℱ.le (k + 1))).const_mul t).aestronglyMeasurable)
      (Real.exp (t * c k)) ?_
    filter_upwards [hξb k] with ω hω
    rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmgf : ∀ k, μ[fun ω => Real.exp (t * ξ k ω) | ℱ k]
      ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c k ^ 2 / 2) := by
    intro k
    exact condExp_exp_mul_le_half (μ := μ) (m := ℱ k) (ℱ.le k) (hc k) ht
      ((hmeas k).mono (ℱ.le (k + 1))).aemeasurable (hbdd k) (hmean k)
  induction n with
  | zero =>
    simp only [psum_zero, mul_zero, Real.exp_zero, Nat.cast_zero, LocMax.proxy, Finset.range_zero,
      Finset.sum_empty, mul_zero, div_zero, Real.exp_zero]
    simp [integral_const]
  | succ n ih =>
    have hstep : ∀ ω, Real.exp (t * psum ξ (n + 1) ω)
        = Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω) := by
      intro ω
      rw [psum_succ, mul_add, Real.exp_add]
    simp only [hstep]
    rw [← integral_condExp (μ := μ) (m := ℱ n) (ℱ.le n)
      (f := fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω))]
    have hmeasf : AEStronglyMeasurable[ℱ n] (fun ω => Real.exp (t * psum ξ n ω)) μ :=
      (Real.continuous_exp.comp_stronglyMeasurable
        ((stronglyMeasurable_psum hmeas n).const_mul t)).aestronglyMeasurable
    have hprodint : Integrable
        (fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω)) μ := by
      refine Integrable.of_bound ((hmeasS n).mul (hξint n).1)
        (Real.exp (t * ∑ k ∈ Finset.range n, c k) * Real.exp (t * c n)) ?_
      filter_upwards [hSb n, hξb n] with ω h1 h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul h1 h2 (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    have hpull : μ[(fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω)) | ℱ n]
        =ᵐ[μ] fun ω => Real.exp (t * psum ξ n ω) * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω :=
      condExp_mul_of_aestronglyMeasurable_left hmeasf hprodint (hξint n)
    rw [integral_congr_ae hpull]
    have hnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] :=
      condExp_nonneg (Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _))
    have hcondint : Integrable (fun ω => μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ :=
      integrable_condExp
    have hprodint2 : Integrable
        (fun ω => Real.exp (t * psum ξ n ω) * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ := by
      refine Integrable.of_bound ((hmeasS n).mul hcondint.1)
        (Real.exp (t * ∑ k ∈ Finset.range n, c k) * Real.exp (t ^ 2 * c n ^ 2 / 2)) ?_
      filter_upwards [hSb n, hnonneg, hmgf n] with ω h1 h2 h3
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h2]
      exact mul_le_mul h1 h3 h2 (le_of_lt (Real.exp_pos _))
    have hmono_int : ∫ ω, Real.exp (t * psum ξ n ω)
          * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω ∂μ
        ≤ ∫ ω, Real.exp (t * psum ξ n ω) * Real.exp (t ^ 2 * c n ^ 2 / 2) ∂μ := by
      refine integral_mono_ae hprodint2 ((hexpint n).mul_const _) ?_
      filter_upwards [hmgf n] with ω hω
      exact mul_le_mul_of_nonneg_left hω (le_of_lt (Real.exp_pos _))
    have hconst : ∫ ω, Real.exp (t * psum ξ n ω) * Real.exp (t ^ 2 * c n ^ 2 / 2) ∂μ
        = Real.exp (t ^ 2 * c n ^ 2 / 2) * ∫ ω, Real.exp (t * psum ξ n ω) ∂μ := by
      rw [integral_mul_const, mul_comm]
    have hprox : (∑ k ∈ Finset.range (n + 1), c k ^ 2)
        = LocMax.proxy c n + c n ^ 2 := by
      rw [LocMax.proxy, Finset.sum_range_succ]
    calc ∫ ω, Real.exp (t * psum ξ n ω)
          * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω ∂μ
        ≤ Real.exp (t ^ 2 * c n ^ 2 / 2) * ∫ ω, Real.exp (t * psum ξ n ω) ∂μ := by
          rw [← hconst]; exact hmono_int
      _ ≤ Real.exp (t ^ 2 * c n ^ 2 / 2)
            * Real.exp (t ^ 2 * LocMax.proxy c n / 2) := by
          refine mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
      _ = Real.exp (t ^ 2 * LocMax.proxy c (n + 1) / 2) := by
          have hprox2 : LocMax.proxy c (n + 1) = LocMax.proxy c n + c n ^ 2 := by
            rw [LocMax.proxy, Finset.sum_range_succ, LocMax.proxy]
          rw [hprox2, ← Real.exp_add]
          congr 1
          ring

/-- **One-sided Chernoff bound, no side condition.** -/
theorem measure_psum_ge_le_sharp [IsProbabilityMeasure μ]
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k, 0 ≤ c k) (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {n : ℕ} {S : ℝ} (hS : 0 < S) (hSp : LocMax.proxy c n ≤ S)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ psum ξ n ω} ≤ Real.exp (-(ε ^ 2) / (2 * S)) := by
  letI : MeasurableSpace Ω := m0
  set tt : ℝ := ε / S with htt
  have htpos : 0 < tt := by rw [htt]; positivity
  have hbS : ∀ᵐ ω ∂μ, |psum ξ n ω| ≤ ∑ k ∈ Finset.range n, c k :=
    ae_abs_psum_le_sum (μ := μ) hbdd n
  have hmeasS : AEStronglyMeasurable (fun ω => Real.exp (tt * psum ξ n ω)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable
      (((stronglyMeasurable_psum hmeas n).mono (ℱ.le n)).const_mul tt).aestronglyMeasurable
  have hexpint : Integrable (fun ω => Real.exp (tt * psum ξ n ω)) μ := by
    refine Integrable.of_bound hmeasS (Real.exp (tt * ∑ k ∈ Finset.range n, c k)) ?_
    filter_upwards [hbS] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc tt * psum ξ n ω ≤ |tt * psum ξ n ω| := le_abs_self _
      _ = tt * |psum ξ n ω| := by rw [abs_mul, abs_of_pos htpos]
      _ ≤ tt * ∑ k ∈ Finset.range n, c k := mul_le_mul_of_nonneg_left hω htpos.le
  have hnonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (tt * psum ξ n ω) :=
    Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hexpint (Real.exp (tt * ε))
  have hset : {ω | Real.exp (tt * ε) ≤ Real.exp (tt * psum ξ n ω)}
      = {ω | ε ≤ psum ξ n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor
    · intro h; exact le_of_mul_le_mul_left h htpos
    · intro h; exact mul_le_mul_of_nonneg_left h htpos.le
  rw [hset] at hmarkov
  have hmom := integral_exp_psum_le_all (μ := μ) (ℱ := ℱ) (ξ := ξ) (c := c) hmeas hc hbdd hmean
    htpos n
  have hbnd : Real.exp (tt * ε) * μ.real {ω | ε ≤ psum ξ n ω}
      ≤ Real.exp (tt ^ 2 * (LocMax.proxy c n) / 2) :=
    le_trans hmarkov hmom
  have hpos : 0 < Real.exp (tt * ε) := Real.exp_pos _
  have hdiv : μ.real {ω | ε ≤ psum ξ n ω}
      ≤ Real.exp (tt ^ 2 * (LocMax.proxy c n) / 2) / Real.exp (tt * ε) := by
    rw [le_div_iff₀ hpos]
    linarith [hbnd]
  refine le_trans hdiv ?_
  rw [← Real.exp_sub]
  refine Real.exp_le_exp.2 ?_
  have h1 : tt ^ 2 * LocMax.proxy c n / 2 ≤ tt ^ 2 * S / 2 := by
    have h3 : tt ^ 2 / 2 * LocMax.proxy c n ≤ tt ^ 2 / 2 * S :=
      mul_le_mul_of_nonneg_left hSp (by positivity)
    linarith
  have h2 : tt ^ 2 * S / 2 - tt * ε = -(ε ^ 2) / (2 * S) := by
    rw [htt]
    field_simp
    ring
  linarith

/-- **Maximal two-sided Azuma–Hoeffding, no side condition.**  For every `ε > 0`,
`μ{∃ k ≤ n, ε ≤ |psum ξ k|} ≤ 2 (n+1) exp (-ε²/(2S))` whenever `proxy c n ≤ S` and `S > 0`. -/
theorem measure_max_abs_psum_ge_le_sharp [IsProbabilityMeasure μ]
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k, 0 ≤ c k) (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {n : ℕ} {S : ℝ} (hS : 0 < S) (hSp : LocMax.proxy c n ≤ S)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |psum ξ k ω|} ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (2 * S)) := by
  letI : MeasurableSpace Ω := m0
  have hsub : {ω | ∃ k ≤ n, ε ≤ |psum ξ k ω|}
      ⊆ ⋃ k ∈ Finset.range (n + 1),
          ({ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω}) := by
    rintro ω ⟨k, hk, hdev⟩
    have hkn : k < n + 1 := Nat.lt_succ_of_le hk
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hkn, ?_⟩⟩
    exact le_abs.1 hdev
  have hmeasSet : ∀ k ∈ Finset.range (n + 1),
      MeasurableSet ({ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω}) := by
    intro k _
    have h1 : MeasurableSet {ω | ε ≤ psum ξ k ω} :=
      measurableSet_le measurable_const
        ((stronglyMeasurable_psum hmeas k).mono (ℱ.le k)).measurable
    have h2 : MeasurableSet {ω | ε ≤ -psum ξ k ω} :=
      measurableSet_le measurable_const
        (((stronglyMeasurable_psum hmeas k).mono (ℱ.le k)).neg).measurable
    exact h1.union h2
  have hbound : ∀ k ∈ Finset.range (n + 1),
      μ.real ({ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω})
        ≤ 2 * Real.exp (-(ε ^ 2) / (2 * S)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hprox : LocMax.proxy c k ≤ S := le_trans (LocMax.proxy_mono hkn) hSp
    have h1 : μ.real {ω | ε ≤ psum ξ k ω} ≤ Real.exp (-(ε ^ 2) / (2 * S)) :=
      measure_psum_ge_le_sharp (μ := μ) (ℱ := ℱ) hmeas hc hbdd hmean hS hprox hε
    have hneg : μ.real {ω | ε ≤ -psum ξ k ω}
        ≤ Real.exp (-(ε ^ 2) / (2 * S)) := by
      have hξ' : ∀ j, StronglyMeasurable[ℱ (j + 1)] (fun ω => -ξ j ω) := fun j => (hmeas j).neg
      have hbdd' : ∀ j, ∀ᵐ ω ∂μ, |(fun ω => -ξ j ω) ω| ≤ c j := by
        intro j
        filter_upwards [hbdd j] with ω hω
        simpa using hω
      have hmean' : ∀ j, μ[(fun ω => -ξ j ω) | ℱ j] =ᵐ[μ] 0 := by
        intro j
        have hneg := condExp_neg (μ := μ) (ξ j) (ℱ j)
        have hz : (-μ[ξ j | ℱ j] : Ω → ℝ) =ᵐ[μ] 0 := by
          filter_upwards [hmean j] with ω hω
          simpa using hω
        exact hneg.trans hz
      have hkey := measure_psum_ge_le_sharp (μ := μ) (ℱ := ℱ) (ξ := fun j => -ξ j) (c := c)
        hξ' hc hbdd' hmean' hS hprox hε
      have hpsum_neg : ∀ k, LocMart.psum (fun j => -ξ j) k = fun ω => -psum ξ k ω := by
        intro k
        induction k with
        | zero => funext ω; simp [psum_zero]
        | succ k ih =>
          funext ω
          rw [psum_succ, psum_succ, ih]
          simp only [Pi.add_apply, Pi.neg_apply]
          ring
      rwa [hpsum_neg k] at hkey
    have hreal : μ.real ({ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω})
        ≤ μ.real {ω | ε ≤ psum ξ k ω} + μ.real {ω | ε ≤ -psum ξ k ω} :=
      measureReal_union_le (μ := μ) {ω | ε ≤ psum ξ k ω} {ω | ε ≤ -psum ξ k ω}
    linarith
  refine le_trans (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le (Finset.range (n + 1))
    (fun k => {ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω})) ?_
  calc ∑ k ∈ Finset.range (n + 1), μ.real ({ω | ε ≤ psum ξ k ω} ∪ {ω | ε ≤ -psum ξ k ω})
      ≤ ∑ k ∈ Finset.range (n + 1), 2 * Real.exp (-(ε ^ 2) / (2 * S)) :=
        Finset.sum_le_sum hbound
    _ = 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (2 * S)) := by
        rw [Finset.sum_const, Finset.card_range]
        push_cast
        ring

end WCJFSharp
