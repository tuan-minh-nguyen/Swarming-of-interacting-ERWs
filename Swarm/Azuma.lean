/-
Azuma--Hoeffding for a finite martingale-difference sequence, with the *maximal* (two-sided)
form used by the paper's display `(locmart)`.

Rationale (see `results/lean/areas/martingale/README.md`, "What is still open in this area"):
the paper bounds `max_{k ≤ ⌊TL⌋} |Q̃_k|` by maximal Azuma--Hoeffding.  Mathlib has only the
final-time form.  Rather than a Doob maximal inequality we use a finite union bound over the
horizon, which loses only a factor `(n+1)` and is more than enough for the paper's
`C_T e^{-c_T L^{1/16}}` error probabilities.

The one-step input is the conditional mgf bound proved in `CondHoeffding.lean`; no optional
sampling and no submartingale structure is used, so every statement below is about a fixed
horizon and a fixed increment sequence, which is exactly what is available for the paper's
martingales at a *deterministic* start.
-/
import Swarm.Imports
import Swarm.CondHoeffding

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LocMart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Partial sums of an increment sequence -/

/-- Partial sums of an increment sequence. -/
noncomputable def psum (ξ : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range n, ξ k ω

lemma psum_zero (ξ : ℕ → Ω → ℝ) : psum ξ 0 = fun _ => 0 := by
  funext ω; simp [psum]

lemma psum_succ (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    psum ξ (n + 1) ω = psum ξ n ω + ξ n ω := by
  simp [psum, Finset.sum_range_succ]

lemma abs_psum_le {ξ : ℕ → Ω → ℝ} {C : ℝ} (hbdd : ∀ k ω, |ξ k ω| ≤ C) (hC : 0 ≤ C) :
    ∀ n ω, |psum ξ n ω| ≤ n * C := by
  intro n
  induction n with
  | zero => intro ω; simp [psum_zero]
  | succ n ih =>
    intro ω
    rw [psum_succ]
    have h1 : |psum ξ n ω + ξ n ω| ≤ |psum ξ n ω| + |ξ n ω| := abs_add_le _ _
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, add_mul, one_mul]
    linarith [ih ω, hbdd n ω]

lemma stronglyMeasurable_psum {ℱ : Filtration ℕ m0} {ξ : ℕ → Ω → ℝ}
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (psum ξ n) := by
  induction n with
  | zero =>
    rw [psum_zero]
    exact stronglyMeasurable_const
  | succ n ih =>
    have hgoal : psum ξ (n + 1) = fun ω => psum ξ n ω + ξ n ω := by
      funext ω; exact psum_succ ξ n ω
    rw [hgoal]
    have hmono := ℱ.mono (Nat.le_succ n : n ≤ n + 1)
    exact (ih.mono hmono).add (hmeas n)

/-! ### The exponential moment bound for partial sums -/

section Azuma

variable {ℱ : Filtration ℕ m0} {ξ : ℕ → Ω → ℝ} {C t : ℝ} [IsProbabilityMeasure μ]

theorem integral_exp_psum_le
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hC : 0 ≤ C) (hbdd : ∀ k ω, |ξ k ω| ≤ C)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (htC : |t| * C ≤ 1) (n : ℕ) :
    ∫ ω, Real.exp (t * psum ξ n ω) ∂μ ≤ Real.exp (n * (t ^ 2 * C ^ 2)) := by
  letI : MeasurableSpace Ω := m0
  -- measurability of the exponential of a partial sum (ambient σ-algebra)
  have hmeasS : ∀ n, AEStronglyMeasurable (fun ω => Real.exp (t * psum ξ n ω)) μ := by
    intro n
    have h : StronglyMeasurable (fun ω => t * psum ξ n ω) :=
      ((stronglyMeasurable_psum hmeas n).mono (ℱ.le n)).const_mul t
    exact Real.continuous_exp.comp_aestronglyMeasurable h.aestronglyMeasurable
  have hbS : ∀ (n : ℕ) (ω : Ω), Real.exp (t * psum ξ n ω) ≤ Real.exp n := by
    intro n ω
    refine Real.exp_le_exp.2 ?_
    calc t * psum ξ n ω ≤ |t * psum ξ n ω| := le_abs_self _
      _ = |t| * |psum ξ n ω| := abs_mul _ _
      _ ≤ |t| * (n * C) := mul_le_mul_of_nonneg_left (abs_psum_le hbdd hC n ω) (abs_nonneg t)
      _ ≤ (n : ℝ) := by
          calc |t| * (n * C) = (n : ℝ) * (|t| * C) := by ring
            _ ≤ (n : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left htC (Nat.cast_nonneg n)
            _ = (n : ℝ) := by ring
  have hexpint : ∀ n, Integrable (fun ω => Real.exp (t * psum ξ n ω)) μ := by
    intro n
    refine Integrable.of_bound (hmeasS n) (Real.exp n) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hbS n ω
  -- pointwise bound for the exponential of an increment
  have hbξ : ∀ (k : ℕ) (ω : Ω), Real.exp (t * ξ k ω) ≤ Real.exp 1 := by
    intro k ω
    refine Real.exp_le_exp.2 ?_
    calc t * ξ k ω ≤ |t * ξ k ω| := le_abs_self _
      _ = |t| * |ξ k ω| := abs_mul _ _
      _ ≤ |t| * C := mul_le_mul_of_nonneg_left (hbdd k ω) (abs_nonneg t)
      _ ≤ 1 := htC
  induction n with
  | zero =>
    simp only [psum_zero, mul_zero, Real.exp_zero, Nat.cast_zero]
    simp
  | succ n ih =>
    have hstep : ∀ ω, Real.exp (t * psum ξ (n + 1) ω)
        = Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω) := by
      intro ω
      rw [psum_succ, mul_add, Real.exp_add]
    simp only [hstep]
    -- tower property
    rw [← integral_condExp (μ := μ) (m := ℱ n) (ℱ.le n)
      (f := fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω))]
    -- pull out the `ℱ n`-measurable multiplier
    have hmeasf : AEStronglyMeasurable[ℱ n] (fun ω => Real.exp (t * psum ξ n ω)) μ :=
      (Real.continuous_exp.comp_stronglyMeasurable
        ((stronglyMeasurable_psum hmeas n).const_mul t)).aestronglyMeasurable
    have hξint : Integrable (fun ω => Real.exp (t * ξ n ω)) μ := by
      refine Integrable.of_bound ?_ (Real.exp 1) ?_
      · exact Real.continuous_exp.comp_aestronglyMeasurable
          (((hmeas n).mono (ℱ.le (n + 1))).const_mul t).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hbξ n ω
    have hprodint : Integrable
        (fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω)) μ := by
      refine Integrable.of_bound ((hmeasS n).mul hξint.1) (Real.exp n * Real.exp 1) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hbS n ω) (hbξ n ω) (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    have hpull : μ[(fun ω => Real.exp (t * psum ξ n ω) * Real.exp (t * ξ n ω)) | ℱ n]
        =ᵐ[μ] fun ω => Real.exp (t * psum ξ n ω) * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω :=
      condExp_mul_of_aestronglyMeasurable_left hmeasf hprodint hξint
    rw [integral_congr_ae hpull]
    -- the conditional mgf bound and the resulting a.e. bound on the pulled-out function
    have hmgf : μ[fun ω => Real.exp (t * ξ n ω) | ℱ n]
        ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * C ^ 2) :=
      condExp_exp_mul_le (μ := μ) (m := ℱ n) (ℱ.le n) hC htC
        ((hmeas n).mono (ℱ.le (n + 1))).aemeasurable
        (Filter.Eventually.of_forall (hbdd n)) (hmean n)
    have hnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] :=
      condExp_nonneg (Filter.Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _))
    have hcondint : Integrable (fun ω => μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ :=
      integrable_condExp
    have hprodint2 : Integrable
        (fun ω => Real.exp (t * psum ξ n ω) * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ := by
      refine Integrable.of_bound ((hmeasS n).mul hcondint.1)
        (Real.exp n * Real.exp (t ^ 2 * C ^ 2)) ?_
      filter_upwards [hnonneg, hmgf] with ω h2 h3
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h2]
      exact mul_le_mul (hbS n ω) h3 h2 (by positivity)
    have hmono_int : ∫ ω, Real.exp (t * psum ξ n ω)
          * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω ∂μ
        ≤ ∫ ω, Real.exp (t * psum ξ n ω) * Real.exp (t ^ 2 * C ^ 2) ∂μ := by
      refine integral_mono_ae hprodint2 (by
        have h := (hexpint n).mul_const (Real.exp (t ^ 2 * C ^ 2))
        simpa [mul_comm] using h) ?_
      filter_upwards [hmgf] with ω hω
      exact mul_le_mul_of_nonneg_left hω (le_of_lt (Real.exp_pos _))
    have hconst : ∫ ω, Real.exp (t * psum ξ n ω) * Real.exp (t ^ 2 * C ^ 2) ∂μ
        = Real.exp (t ^ 2 * C ^ 2) * ∫ ω, Real.exp (t * psum ξ n ω) ∂μ := by
      rw [integral_mul_const, mul_comm]
    refine le_trans (le_trans hmono_int (le_of_eq hconst)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))) (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring

end Azuma

/-! ### Chernoff / Markov consequences -/

section Chernoff

variable {ℱ : Filtration ℕ m0} {ξ : ℕ → Ω → ℝ} {C ε : ℝ} [IsProbabilityMeasure μ]

/-- Partial sums of a negated increment sequence. -/
lemma psum_neg {u un : ℕ → Ω → ℝ} (h : ∀ k ω, un k ω = -u k ω) (n : ℕ) :
    psum un n = fun ω => -psum u n ω := by
  funext ω
  simp only [psum]
  have h1 : ∑ k ∈ Finset.range n, un k ω = ∑ k ∈ Finset.range n, -u k ω :=
    Finset.sum_congr rfl fun k _ => h k ω
  rw [h1, Finset.sum_neg_distrib]

/-- One-sided Chernoff bound for the partial sum at a fixed horizon. -/
theorem measure_psum_ge_le
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hC : 0 < C) (hbdd : ∀ k ω, |ξ k ω| ≤ C)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {n : ℕ} (hn : 1 ≤ n) (hε : 0 < ε) (hεC : ε ≤ 2 * n * C) :
    μ.real {ω | ε ≤ psum ξ n ω} ≤ Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
  letI : MeasurableSpace Ω := m0
  set t : ℝ := ε / (2 * (n : ℝ) * C ^ 2) with ht_def
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hCne : (C : ℝ) ≠ 0 := ne_of_gt hC
  have htpos : 0 < t := by
    rw [ht_def]
    positivity
  have htC : |t| * C ≤ 1 := by
    have h1 : |t| = t := abs_of_pos htpos
    rw [h1, ht_def]
    have hden : (0 : ℝ) < 2 * (n : ℝ) * C ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_one hden]
    nlinarith [hεC, hε.le, hC.le, hnpos]
  have hexpint : Integrable (fun ω => Real.exp (t * psum ξ n ω)) μ := by
    refine Integrable.of_bound ?_ (Real.exp n) ?_
    · exact Real.continuous_exp.comp_aestronglyMeasurable
        (((stronglyMeasurable_psum hmeas n).mono (ℱ.le n)).const_mul t).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      calc t * psum ξ n ω ≤ |t * psum ξ n ω| := le_abs_self _
        _ = |t| * |psum ξ n ω| := abs_mul _ _
        _ ≤ |t| * (n * C) := mul_le_mul_of_nonneg_left (abs_psum_le hbdd hC.le n ω) (abs_nonneg t)
        _ ≤ (n : ℝ) := by
            calc |t| * (n * C) = (n : ℝ) * (|t| * C) := by ring
              _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left htC (Nat.cast_nonneg n)
              _ = (n : ℝ) := by ring
  have hnonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (t * psum ξ n ω) :=
    Filter.Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hexpint (Real.exp (t * ε))
  have hset : {ω | Real.exp (t * ε) ≤ Real.exp (t * psum ξ n ω)} = {ω | ε ≤ psum ξ n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor
    · intro h
      exact (le_of_mul_le_mul_left h htpos)
    · intro h
      exact mul_le_mul_of_nonneg_left h htpos.le
  rw [hset] at hmarkov
  have hbd : Real.exp (t * ε) * μ.real {ω | ε ≤ psum ξ n ω}
      ≤ Real.exp (n * (t ^ 2 * C ^ 2)) :=
    le_trans hmarkov (integral_exp_psum_le hmeas hC.le hbdd hmean htC n)
  have hpos : 0 < Real.exp (t * ε) := Real.exp_pos _
  have hdiv : μ.real {ω | ε ≤ psum ξ n ω}
      ≤ Real.exp (n * (t ^ 2 * C ^ 2)) / Real.exp (t * ε) := by
    rw [le_div_iff₀ hpos]
    linarith [hbd]
  refine le_trans hdiv (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  rw [ht_def]
  field_simp
  ring

/-- Two-sided Chernoff bound at a fixed horizon. -/
theorem measure_abs_psum_ge_le
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hC : 0 < C) (hbdd : ∀ k ω, |ξ k ω| ≤ C)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {n : ℕ} (hn : 1 ≤ n) (hε : 0 < ε) (hεC : ε ≤ 2 * n * C) :
    μ.real {ω | ε ≤ |psum ξ n ω|} ≤ 2 * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
  letI : MeasurableSpace Ω := m0
  set ξn : ℕ → Ω → ℝ := fun k (ω : Ω) => -ξ k ω with hξn
  have hmeas' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξn k) := by
    intro k
    exact (hmeas k).neg
  have hbdd' : ∀ k ω, |ξn k ω| ≤ C := by
    intro k ω
    simpa [hξn] using hbdd k ω
  have hmean' : ∀ k, μ[ξn k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    have h := condExp_neg (μ := μ) (m := ℱ k) (f := ξ k)
    have h2 : ((-ξ k : Ω → ℝ)) = fun ω => -ξ k ω := rfl
    have hzero : μ[fun ω => -ξ k ω | ℱ k] =ᵐ[μ] 0 := by
      rw [← h2]
      filter_upwards [h, hmean k] with ω hω1 hω2
      simp [hω1, hω2]
    simpa [hξn] using hzero
  have hneg : ∀ k, psum ξn k = fun ω => -psum ξ k ω :=
    fun k => psum_neg (u := ξ) (un := ξn) (fun k ω => by rw [hξn]) k
  have hsub : {ω | ε ≤ |psum ξ n ω|}
      ⊆ {ω | ε ≤ psum ξ n ω} ∪ {ω | ε ≤ psum ξn n ω} := by
    intro ω hω
    have hω' : ε ≤ |psum ξ n ω| := hω
    rcases le_abs.1 hω' with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show ε ≤ psum ξn n ω
      rw [hneg n]
      exact h
  calc μ.real {ω | ε ≤ |psum ξ n ω|}
      ≤ μ.real ({ω | ε ≤ psum ξ n ω} ∪ {ω | ε ≤ psum ξn n ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ε ≤ psum ξ n ω} + μ.real {ω | ε ≤ psum ξn n ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) + Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
        refine add_le_add (measure_psum_ge_le hmeas hC hbdd hmean hn hε hεC)
          (measure_psum_ge_le hmeas' hC hbdd' hmean' hn hε hεC)
    _ = 2 * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by ring

/-- **Maximal (two-sided) Azuma--Hoeffding over a horizon.**  This is the bound on
`max_{k ≤ n} |Q_{t+k} - Q_t|` used in the paper's display `(locmart)`.  It is obtained from the
fixed-horizon bound by a union over the horizon and needs no side condition relating `ε` to
`n * C`: horizons too short to support a deviation of size `ε` are handled by the deterministic
increment bound. -/
theorem measure_max_abs_psum_ge_le
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hC : 0 < C) (hbdd : ∀ k ω, |ξ k ω| ≤ C)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {n : ℕ} (hn : 1 ≤ n) (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |psum ξ k ω|}
      ≤ 2 * (n + 1) * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
  letI : MeasurableSpace Ω := m0
  have hterm : ∀ k ∈ Finset.range (n + 1),
      μ.real {ω | ε ≤ |psum ξ k ω|} ≤ 2 * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hempty : {ω | ε ≤ |psum ξ 0 ω|} = ∅ := by
        ext ω
        simp only [psum_zero, mul_zero, Real.exp_zero, Pi.zero_apply, abs_zero,
          Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact hε
      rw [hempty, measureReal_empty]
      positivity
    · by_cases hsmall : (k : ℝ) * C < ε
      · have hempty : {ω | ε ≤ |psum ξ k ω|} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have h := abs_psum_le hbdd hC.le k ω
          nlinarith
        rw [hempty, measureReal_empty]
        positivity
      · have hkC : ε ≤ 2 * (k : ℝ) * C := by
          have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
          push_neg at hsmall
          nlinarith
        refine le_trans (measure_abs_psum_ge_le hmeas hC hbdd hmean hkpos hε hkC) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        apply Real.exp_le_exp.2
        have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        have hkn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [neg_div, neg_div, neg_le_neg_iff]
        have h4k : (0 : ℝ) < 4 * (k : ℝ) * C ^ 2 := by positivity
        have h4kn : 4 * (k : ℝ) * C ^ 2 ≤ 4 * (n : ℝ) * C ^ 2 := by nlinarith
        exact div_le_div_of_nonneg_left (by positivity) h4k h4kn
  have hsub : {ω | ∃ k ≤ n, ε ≤ |psum ξ k ω|}
      ⊆ ⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ |psum ξ k ω|} := by
    intro ω hω
    obtain ⟨k, hk, hdev⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hdev
  calc μ.real {ω | ∃ k ≤ n, ε ≤ |psum ξ k ω|}
      ≤ μ.real (⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ |psum ξ k ω|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ.real {ω | ε ≤ |psum ξ k ω|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), 2 * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = 2 * (n + 1) * Real.exp (-(ε ^ 2) / (4 * n * C ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring


end Chernoff

end LocMart
