/-
# `LocMaxVar`: maximal deviation with a *computed, non-uniform* variance proxy, from a.e. bounds

`Swarm/Azuma.lean` and `LocMartRate.lean` prove the maximal Hoeffding--Azuma bound
only for a **single uniform** increment constant `C` (`∀ k ω, |ξ k ω| ≤ C`, pointwise).  That
interface is too rigid for the `(locmove)` maximum process of `LocMoveMart`:

* its increments are only **a.e.** bounded (`abs_dM_le : |dM_n| ≤ 4n+10` a.e.; a pointwise
  version cannot exist because `Mcomp` is a conditional expectation), and
* the bound **grows with the index** (`4n+10`), so no uniform `C` is available at all.

This file removes both restrictions: the envelope `c : ℕ → ℝ` is an arbitrary positive sequence,
the increment bound is an `∀ᵐ` statement, and the exponent carries the honest proxy
`∑_{k<n} c_k²` instead of `n · C²`.  The argument is the tower + conditional Hoeffding +
Chernoff + union over the horizon of `LocMart.integral_exp_psum_le`,
`LocMart.measure_psum_ge_le`, `LocMart.measure_abs_psum_ge_le`,
`LocMart.measure_max_abs_psum_ge_le` (credited: the proofs below are those proofs with `C`
replaced by `c k` and the pointwise bounds by a.e. ones) together with one genuinely new step,
the **envelope extension** `extξ`/`extc`, which turns hypotheses known only on `k < n` (all the
`(locmove)` instantiation can supply) into the global hypotheses of the moment bound.

The statements are used in `LocMaxProfile.lean` on the actual interacting array, where
`c k = 4(s+k)+10` on the window `[s,s+K)`.
-/
import Swarm.Azuma

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace LocMax

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0} {ξ : ℕ → Ω → ℝ} {c : ℕ → ℝ}

/-! ## 1. Partial sums are bounded a.e. by the running sum of the envelope -/

/-- **`|Σ_{k<n} ξ_k| ≤ Σ_{k<n} c_k` a.e.**, from `|ξ_k| ≤ c_k` a.e. and `0 ≤ c_k`. -/
lemma abs_psum_le_ae (hc : ∀ k, 0 ≤ c k)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k) (n : ℕ) :
    ∀ᵐ ω ∂μ, |LocMart.psum ξ n ω| ≤ ∑ k ∈ Finset.range n, c k := by
  induction n with
  | zero =>
    filter_upwards with ω
    simp [LocMart.psum_zero]
  | succ n ih =>
    filter_upwards [ih, hbdd n] with ω h1 h2
    rw [LocMart.psum_succ, Finset.sum_range_succ]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ## 2. The exponential moment bound with variance proxy `Σ c_k²` -/

/-- **Tower with non-uniform constants.**  If `ξ_k` is `ℱ_{k+1}`-measurable, centred given
`ℱ_k`, and `|ξ_k| ≤ c_k` a.e., then for every real `t` with `|t| · c_k ≤ 1` for all `k`,

  `∫ exp (t · Σ_{k<n} ξ_k) ≤ exp (Σ_{k<n} t² c_k²)`.

`LocMart.integral_exp_psum_le` is the special case `c ≡ C` with pointwise bounds. -/
theorem integral_exp_psum_le_ae
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k, 0 ≤ c k) (hbdd : ∀ k, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {t : ℝ} (htc : ∀ k, |t| * c k ≤ 1) (n : ℕ) :
    ∫ ω, Real.exp (t * LocMart.psum ξ n ω) ∂μ
      ≤ Real.exp (∑ k ∈ Finset.range n, t ^ 2 * c k ^ 2) := by
  letI : MeasurableSpace Ω := m0
  have hmeasS : ∀ n, AEStronglyMeasurable (fun ω => Real.exp (t * LocMart.psum ξ n ω)) μ := by
    intro n
    have h : StronglyMeasurable (fun ω => t * LocMart.psum ξ n ω) :=
      ((LocMart.stronglyMeasurable_psum hmeas n).mono (ℱ.le n)).const_mul t
    exact Real.continuous_exp.comp_aestronglyMeasurable h.aestronglyMeasurable
  have hbS : ∀ n, ∀ᵐ ω ∂μ, Real.exp (t * LocMart.psum ξ n ω)
      ≤ Real.exp (|t| * ∑ k ∈ Finset.range n, c k) := by
    intro n
    filter_upwards [abs_psum_le_ae (μ := μ) hc hbdd n] with ω hω
    refine Real.exp_le_exp.2 ?_
    calc t * LocMart.psum ξ n ω ≤ |t * LocMart.psum ξ n ω| := le_abs_self _
      _ = |t| * |LocMart.psum ξ n ω| := abs_mul _ _
      _ ≤ |t| * ∑ k ∈ Finset.range n, c k :=
          mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  have hexpint : ∀ n, Integrable (fun ω => Real.exp (t * LocMart.psum ξ n ω)) μ := by
    intro n
    refine Integrable.of_bound (hmeasS n) (Real.exp (|t| * ∑ k ∈ Finset.range n, c k)) ?_
    filter_upwards [hbS n] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hω
  have hbξ : ∀ k, ∀ᵐ ω ∂μ, Real.exp (t * ξ k ω) ≤ Real.exp 1 := by
    intro k
    filter_upwards [hbdd k] with ω hω
    refine Real.exp_le_exp.2 ?_
    calc t * ξ k ω ≤ |t * ξ k ω| := le_abs_self _
      _ = |t| * |ξ k ω| := abs_mul _ _
      _ ≤ |t| * c k := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
      _ ≤ 1 := htc k
  induction n with
  | zero =>
    simp only [LocMart.psum_zero, mul_zero, Real.exp_zero]
    simp
  | succ n ih =>
    have hstep : ∀ ω, Real.exp (t * LocMart.psum ξ (n + 1) ω)
        = Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t * ξ n ω) := by
      intro ω
      rw [LocMart.psum_succ, mul_add, Real.exp_add]
    simp only [hstep]
    rw [← integral_condExp (μ := μ) (m := ℱ n) (ℱ.le n)
      (f := fun ω => Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t * ξ n ω))]
    have hmeasf : AEStronglyMeasurable[ℱ n] (fun ω => Real.exp (t * LocMart.psum ξ n ω)) μ :=
      (Real.continuous_exp.comp_stronglyMeasurable
        ((LocMart.stronglyMeasurable_psum hmeas n).const_mul t)).aestronglyMeasurable
    have hξint : Integrable (fun ω => Real.exp (t * ξ n ω)) μ := by
      refine Integrable.of_bound ?_ (Real.exp 1) ?_
      · exact Real.continuous_exp.comp_aestronglyMeasurable
          (((hmeas n).mono (ℱ.le (n + 1))).const_mul t).aestronglyMeasurable
      · filter_upwards [hbξ n] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hω
    have hprodint : Integrable
        (fun ω => Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t * ξ n ω)) μ := by
      refine Integrable.of_bound ((hmeasS n).mul hξint.1)
        (Real.exp (|t| * ∑ k ∈ Finset.range n, c k) * Real.exp 1) ?_
      filter_upwards [hbS n, hbξ n] with ω h1 h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul h1 h2 (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    have hpull : μ[(fun ω => Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t * ξ n ω)) | ℱ n]
        =ᵐ[μ] fun ω => Real.exp (t * LocMart.psum ξ n ω)
            * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω :=
      condExp_mul_of_aestronglyMeasurable_left hmeasf hprodint hξint
    rw [integral_congr_ae hpull]
    have hmgf : μ[fun ω => Real.exp (t * ξ n ω) | ℱ n]
        ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c n ^ 2) :=
      LocMart.condExp_exp_mul_le (μ := μ) (m := ℱ n) (ℱ.le n) (hc n) (htc n)
        ((hmeas n).mono (ℱ.le (n + 1))).aemeasurable
        (hbdd n) (hmean n)
    have hnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] :=
      condExp_nonneg (Filter.Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _))
    have hcondint : Integrable (fun ω => μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ :=
      integrable_condExp
    have hprodint2 : Integrable
        (fun ω => Real.exp (t * LocMart.psum ξ n ω)
          * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω) μ := by
      refine Integrable.of_bound ((hmeasS n).mul hcondint.1)
        (Real.exp (|t| * ∑ k ∈ Finset.range n, c k) * Real.exp (t ^ 2 * c n ^ 2)) ?_
      filter_upwards [hbS n, hnonneg, hmgf] with ω h1 h2 h3
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h2]
      exact mul_le_mul h1 h3 h2 (by positivity)
    have hmono_int : ∫ ω, Real.exp (t * LocMart.psum ξ n ω)
          * μ[fun ω => Real.exp (t * ξ n ω) | ℱ n] ω ∂μ
        ≤ ∫ ω, Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t ^ 2 * c n ^ 2) ∂μ := by
      refine integral_mono_ae hprodint2 (by
        have h := (hexpint n).mul_const (Real.exp (t ^ 2 * c n ^ 2))
        simpa [mul_comm] using h) ?_
      filter_upwards [hmgf] with ω hω
      exact mul_le_mul_of_nonneg_left hω (le_of_lt (Real.exp_pos _))
    have hconst : ∫ ω, Real.exp (t * LocMart.psum ξ n ω) * Real.exp (t ^ 2 * c n ^ 2) ∂μ
        = Real.exp (t ^ 2 * c n ^ 2) * ∫ ω, Real.exp (t * LocMart.psum ξ n ω) ∂μ := by
      rw [integral_mul_const, mul_comm]
    refine le_trans (le_trans hmono_int (le_of_eq hconst)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))) (le_of_eq ?_)
    rw [← Real.exp_add, Finset.sum_range_succ]
    congr 1
    ring

/-! ## 3. The variance proxy `S = Σ_{k<n} c_k²` -/

/-- The computed variance proxy of the horizon `n`. -/
noncomputable def proxy (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, c k ^ 2

lemma proxy_pos {n : ℕ} (hc : ∀ k < n, 0 < c k) (hn : 1 ≤ n) : 0 < proxy c n := by
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.2 hn
  have h0 : c 0 ^ 2 ≤ proxy c n :=
    Finset.single_le_sum (f := fun k => c k ^ 2) (fun i _ => sq_nonneg (c i)) hmem
  have hpos : 0 < c 0 ^ 2 := pow_pos (hc 0 hn) 2
  linarith

lemma proxy_mono {m n : ℕ} (hmn : m ≤ n) : proxy c m ≤ proxy c n := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn) ?_
  intro i _ _
  exact sq_nonneg (c i)

lemma proxy_eq_mul {t : ℝ} (n : ℕ) :
    ∑ k ∈ Finset.range n, t ^ 2 * c k ^ 2 = t ^ 2 * proxy c n := by
  rw [proxy, Finset.mul_sum]

/-! ## 4. Envelope extension: hypotheses known only below the horizon

The `(locmove)` instantiation knows `|dM_{s+k}| ≤ 4(s+k)+10` only for `k < K`, and the moment
bound wants a *global* envelope.  We extend `ξ` by `0` and `c` by the constant `1/(|t|+1)`
outside the horizon; neither the partial sum over the horizon, nor its proxy, nor the Chernoff
side condition changes. -/

/-- `ξ` cut off after the horizon. -/
noncomputable def extξ (n : ℕ) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k => if k < n then ξ k else 0

/-- A positive envelope outside the horizon, small enough that `|t| · c k ≤ 1` holds there. -/
noncomputable def extc (t : ℝ) (n : ℕ) (c : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < n then c k else 1 / (|t| + 1)

lemma psum_extξ (n : ℕ) :
    LocMart.psum (extξ n ξ) n = LocMart.psum ξ n := by
  funext ω
  simp only [LocMart.psum]
  exact Finset.sum_congr rfl fun k hk => by
    simp only [extξ, Finset.mem_range.1 hk, if_true]

lemma casext (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, t ^ 2 * extc t n c k ^ 2
      = ∑ k ∈ Finset.range n, t ^ 2 * c k ^ 2 := by
  exact Finset.sum_congr rfl fun k hk => by
    simp only [extc, Finset.mem_range.1 hk, if_true]

lemma extc_nonneg (t : ℝ) (n : ℕ) (hc : ∀ k < n, 0 ≤ c k) :
    ∀ k, 0 ≤ extc t n c k := by
  intro k
  by_cases hk : k < n
  · simp only [extc, hk, if_true]; exact hc k hk
  · simp only [extc, hk, if_false]; positivity

lemma extc_side (t : ℝ) (n : ℕ) (hc : ∀ k < n, |t| * c k ≤ 1) :
    ∀ k, |t| * extc t n c k ≤ 1 := by
  intro k
  by_cases hk : k < n
  · simp only [extc, hk, if_true]; exact hc k hk
  · have hgt : (0 : ℝ) < |t| + 1 := by positivity
    simp only [extc, hk, if_false]
    rw [mul_one_div, div_le_one hgt]
    linarith [abs_nonneg t]

/-! ## 5. Chernoff consequences at a horizon with proxy `S = Σ_{k<n} c_k²` -/

section Chernoff

variable {ε : ℝ}

/-- One-sided Chernoff bound at a fixed horizon: the computed proxy `Σ_{k<n} c_k²` is dominated
by a supplied `S`, and the increment bound is only assumed on `k < n`.  The `S` interface is what
lets the maximal version below feed the *same* `S = proxy c n` to every horizon `k ≤ n`, so that
all terms of the union carry one exponent. -/
theorem measure_psum_ge_le_ae {n : ℕ} {S : ℝ}
    (hS : 0 < S) (hSp : proxy c n ≤ S)
    (hmeas : ∀ k < n, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k < n, 0 < c k) (hbdd : ∀ k < n, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k < n, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (hε : 0 < ε)
    (hεc : ∀ k < n, ε * c k ≤ 2 * S) :
    μ.real {ω | ε ≤ LocMart.psum ξ n ω} ≤ Real.exp (-(ε ^ 2) / (4 * S)) := by
  letI : MeasurableSpace Ω := m0
  set tt : ℝ := ε / (2 * S) with htt
  have htpos : 0 < tt := by rw [htt]; positivity
  have hmeas' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (extξ n ξ k) := by
    intro k
    by_cases hk : k < n
    · simp only [extξ, hk, if_true]; exact hmeas k hk
    · simp only [extξ, hk, if_false]; exact stronglyMeasurable_const
  have hc' : ∀ k, 0 ≤ extc tt n c k := extc_nonneg tt n (fun k hk => (hc k hk).le)
  have hbdd' : ∀ k, ∀ᵐ ω ∂μ, |extξ n ξ k ω| ≤ extc tt n c k := by
    intro k
    by_cases hk : k < n
    · filter_upwards [hbdd k hk] with ω hω
      simp only [extξ, extc, hk, if_true]
      exact hω
    · filter_upwards with ω
      simp only [extξ, extc, hk, if_false, Pi.zero_apply, abs_zero]
      positivity
  have hmean' : ∀ k, μ[extξ n ξ k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    by_cases hk : k < n
    · have hξ : extξ n ξ k = ξ k := by funext ω; simp only [extξ, hk, if_true]
      rw [hξ]; exact hmean k hk
    · have hξ : extξ n ξ k = (0 : Ω → ℝ) := by funext ω; simp only [extξ, hk, if_false]
      rw [hξ]; simp
  have htc' : ∀ k, |tt| * extc tt n c k ≤ 1 := by
    refine extc_side tt n ?_
    intro k hk
    have h1 : |tt| = tt := abs_of_pos htpos
    rw [h1, htt, div_mul_eq_mul_div, div_le_one (by positivity)]
    have h2 := hεc k hk
    nlinarith [hS]
  have hmom := integral_exp_psum_le_ae (μ := μ) (ℱ := ℱ) (ξ := extξ n ξ)
    (c := extc tt n c) hmeas' hc' hbdd' hmean' htc' n
  rw [psum_extξ, casext, proxy_eq_mul] at hmom
  have hsum_ext : ∑ k ∈ Finset.range n, extc tt n c k = ∑ k ∈ Finset.range n, c k :=
    Finset.sum_congr rfl fun k hk => by
      simp only [extc, Finset.mem_range.1 hk, if_true]
  have htsum : ∀ᵐ ω ∂μ, |LocMart.psum ξ n ω| ≤ ∑ k ∈ Finset.range n, c k := by
    have := abs_psum_le_ae (μ := μ) (ξ := extξ n ξ) (c := extc tt n c) hc' hbdd' n
    rw [psum_extξ, hsum_ext] at this
    exact this
  have hexpint : Integrable (fun ω => Real.exp (tt * LocMart.psum ξ n ω)) μ := by
    refine Integrable.of_bound ?_ (Real.exp (|tt| * ∑ k ∈ Finset.range n, c k)) ?_
    · have hsm : StronglyMeasurable (fun ω => tt * LocMart.psum ξ n ω) := by
        have h0 : StronglyMeasurable (fun ω => tt * LocMart.psum (extξ n ξ) n ω) :=
          ((LocMart.stronglyMeasurable_psum hmeas' n).mono (ℱ.le n)).const_mul tt
        rwa [psum_extξ] at h0
      exact Real.continuous_exp.comp_aestronglyMeasurable hsm.aestronglyMeasurable
    · filter_upwards [htsum] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      calc tt * LocMart.psum ξ n ω ≤ |tt * LocMart.psum ξ n ω| := le_abs_self _
        _ = |tt| * |LocMart.psum ξ n ω| := abs_mul _ _
        _ ≤ |tt| * ∑ k ∈ Finset.range n, c k :=
            mul_le_mul_of_nonneg_left hω (abs_nonneg tt)
  have hnonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (tt * LocMart.psum ξ n ω) :=
    Filter.Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hexpint (Real.exp (tt * ε))
  have hset : {ω | Real.exp (tt * ε) ≤ Real.exp (tt * LocMart.psum ξ n ω)}
      = {ω | ε ≤ LocMart.psum ξ n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor
    · intro h; exact (le_of_mul_le_mul_left h htpos)
    · intro h; exact mul_le_mul_of_nonneg_left h htpos.le
  rw [hset] at hmarkov
  have hbd : Real.exp (tt * ε) * μ.real {ω | ε ≤ LocMart.psum ξ n ω} ≤ Real.exp (tt ^ 2 * S) :=
    le_trans hmarkov (le_trans hmom
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hSp (sq_nonneg tt))))
  have hpos : 0 < Real.exp (tt * ε) := Real.exp_pos _
  have hdiv : μ.real {ω | ε ≤ LocMart.psum ξ n ω}
      ≤ Real.exp (tt ^ 2 * S) / Real.exp (tt * ε) := by
    rw [le_div_iff₀ hpos]
    linarith [hbd]
  refine le_trans hdiv (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  rw [htt]
  field_simp
  ring

/-- Two-sided Chernoff bound at a fixed horizon, with the proxy dominated by `S`. -/
theorem measure_abs_psum_ge_le_ae {n : ℕ} {S : ℝ}
    (hS : 0 < S) (hSp : proxy c n ≤ S)
    (hmeas : ∀ k < n, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k < n, 0 < c k) (hbdd : ∀ k < n, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k < n, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (hε : 0 < ε)
    (hεc : ∀ k < n, ε * c k ≤ 2 * S) :
    μ.real {ω | ε ≤ |LocMart.psum ξ n ω|} ≤ 2 * Real.exp (-(ε ^ 2) / (4 * S)) := by
  letI : MeasurableSpace Ω := m0
  set ξn : ℕ → Ω → ℝ := fun k (ω : Ω) => -ξ k ω with hξn
  have hmeas' : ∀ k < n, StronglyMeasurable[ℱ (k + 1)] (ξn k) := by
    intro k hk; exact (hmeas k hk).neg
  have hbdd' : ∀ k < n, ∀ᵐ ω ∂μ, |ξn k ω| ≤ c k := by
    intro k hk
    filter_upwards [hbdd k hk] with ω hω
    simpa [hξn] using hω
  have hmean' : ∀ k < n, μ[ξn k | ℱ k] =ᵐ[μ] 0 := by
    intro k hk
    have h := condExp_neg (μ := μ) (m := ℱ k) (f := ξ k)
    have h2 : ((-ξ k : Ω → ℝ)) = fun ω => -ξ k ω := rfl
    have hzero : μ[fun ω => -ξ k ω | ℱ k] =ᵐ[μ] 0 := by
      rw [← h2]
      filter_upwards [h, hmean k hk] with ω hω1 hω2
      simp [hω1, hω2]
    have hξ : ξn k = fun ω => -ξ k ω := by funext ω; simp [hξn]
    rw [hξ]; exact hzero
  have hneg : LocMart.psum ξn n = fun ω => -LocMart.psum ξ n ω :=
    LocMart.psum_neg (u := ξ) (un := ξn) (fun k ω => by simp [hξn]) n
  have hsub : {ω | ε ≤ |LocMart.psum ξ n ω|}
      ⊆ {ω | ε ≤ LocMart.psum ξ n ω} ∪ {ω | ε ≤ LocMart.psum ξn n ω} := by
    intro ω hω
    have hω' : ε ≤ |LocMart.psum ξ n ω| := hω
    rcases le_abs.1 hω' with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show ε ≤ LocMart.psum ξn n ω
      rw [hneg]
      exact h
  calc μ.real {ω | ε ≤ |LocMart.psum ξ n ω|}
      ≤ μ.real ({ω | ε ≤ LocMart.psum ξ n ω} ∪ {ω | ε ≤ LocMart.psum ξn n ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ε ≤ LocMart.psum ξ n ω} + μ.real {ω | ε ≤ LocMart.psum ξn n ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(ε ^ 2) / (4 * S)) + Real.exp (-(ε ^ 2) / (4 * S)) := by
        refine add_le_add
          (measure_psum_ge_le_ae hS hSp hmeas hc hbdd hmean hε hεc)
          (measure_psum_ge_le_ae hS hSp hmeas' hc hbdd' hmean' hε hεc)
    _ = 2 * Real.exp (-(ε ^ 2) / (4 * S)) := by ring

/-- **Maximal two-sided bound over a horizon, with the computed proxy.**

  `μ{∃ k ≤ n, ε ≤ |ξ_0 + ⋯ + ξ_{k-1}|} ≤ 2 (n+1) exp (-ε² / (4 Σ_{k<n} c_k²))`.

The proxy is computed from the actual envelopes; the only side condition is the Chernoff one
`ε · c_k ≤ 2 Σ c²` on the window, which in the `(locmove)` instantiation is an explicit
inequality between polynomials in the window parameters. -/
theorem measure_max_abs_psum_ge_le_ae {n : ℕ} {S : ℝ}
    (hn : 1 ≤ n) (hS : 0 < S) (hSp : proxy c n ≤ S)
    (hmeas : ∀ k < n, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hc : ∀ k < n, 0 < c k) (hbdd : ∀ k < n, ∀ᵐ ω ∂μ, |ξ k ω| ≤ c k)
    (hmean : ∀ k < n, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    (hε : 0 < ε)
    (hεc : ∀ k < n, ε * c k ≤ 2 * S) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * S)) := by
  letI : MeasurableSpace Ω := m0
  have hterm : ∀ k ∈ Finset.range (n + 1),
      μ.real {ω | ε ≤ |LocMart.psum ξ k ω|}
        ≤ 2 * Real.exp (-(ε ^ 2) / (4 * S)) := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hempty : {ω | ε ≤ |LocMart.psum ξ 0 ω|} = ∅ := by
        ext ω
        simp only [LocMart.psum_zero, mul_zero, Pi.zero_apply, abs_zero,
          Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact hε
      rw [hempty, measureReal_empty]
      positivity
    · exact measure_abs_psum_ge_le_ae (c := c) hS (le_trans (proxy_mono (c := c) hkn) hSp)
        (fun j hj => hmeas j (lt_of_lt_of_le hj hkn))
        (fun j hj => hc j (lt_of_lt_of_le hj hkn))
        (fun j hj => hbdd j (lt_of_lt_of_le hj hkn))
        (fun j hj => hmean j (lt_of_lt_of_le hj hkn))
        hε (fun j hj => hεc j (lt_of_lt_of_le hj hkn))
  have hsub : {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ⊆ ⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ |LocMart.psum ξ k ω|} := by
    intro ω hω
    obtain ⟨k, hk, hdev⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hdev
  calc μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ μ.real (⋃ k ∈ Finset.range (n + 1), {ω | ε ≤ |LocMart.psum ξ k ω|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ.real {ω | ε ≤ |LocMart.psum ξ k ω|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), 2 * Real.exp (-(ε ^ 2) / (4 * S)) :=
        Finset.sum_le_sum hterm
    _ = 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * S)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Chernoff

end LocMax
