/-
  **`locsum`, layer 2: the uniform first and second moments of the truncations.**

  With `a = E[rho]` and `b = E[rho^2]` (`aC`, `bC` below, `b < 1`), the recursion
  `Q (k+1) x = 1 + rho(x)(1 + Q k (x-1))` and the independence of `rho(x)` from
  `Q k (x-1)` (a function of the marks `x-k, …, x-1`) give

      E[Q (k+1) x]      = 1 + a (1 + E[Q k (x-1)])
      E[Q (k+1) x ^ 2]  = 1 + 2a (1 + E[Q k (x-1)])
                            + b (1 + 2 E[Q k (x-1)] + E[Q k (x-1) ^ 2]),

  hence the two uniform bounds `E[Q k x] <= L` and `E[Q k x ^ 2] <= M` for all `k <= x`,
  with `L = (1+a)/(1-a)` and `M` depending only on `p` and `q`.  These are the real
  "raw-array" moments that the block concentration needs.
-/
import Swarm.Imports
import Swarm.L1Trunc

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocSum

noncomputable section

open SwarmMarks SwarmSpatial

/-- The first moment of the ratio. -/
def aC (p q : ℝ) : ℝ := q * ((1 - p) / p) + (1 - q)

/-- The second moment of the ratio. -/
def bC (p q : ℝ) : ℝ := q * ((1 - p) / p) ^ 2 + (1 - q)

lemma aC_nonneg {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ aC p q := by
  have hr : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (by linarith)
  have : 0 ≤ q * ((1 - p) / p) := mul_nonneg hq0 hr
  simp only [aC]; linarith

lemma bC_nonneg {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ bC p q := by
  have hr : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (by linarith)
  have : 0 ≤ q * ((1 - p) / p) ^ 2 := mul_nonneg hq0 (by positivity)
  simp only [bC]; linarith

lemma aC_lt_one {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) : aC p q < 1 := by
  have hr0 : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (by linarith)
  have hr1 : (1 - p) / p < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have : q * ((1 - p) / p) < q * 1 := by
    exact mul_lt_mul_of_pos_left hr1 hq
  simp only [aC]; linarith

lemma bC_lt_one {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) : bC p q < 1 := by
  have hr0 : 0 ≤ (1 - p) / p := div_nonneg (by linarith) (by linarith)
  have hr1 : (1 - p) / p < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hsq : ((1 - p) / p) ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have : q * ((1 - p) / p) ^ 2 < q * 1 := mul_lt_mul_of_pos_left hsq hq
  simp only [bC]; linarith

/-- The truncations stay above `-1`. -/
lemma Q_ge_neg_one (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (ω : ℕ → Bool) :
    -1 ≤ Q p k x ω := by
  have hnn : 0 ≤ Gsum p k x ω := Finset.sum_nonneg fun j _ => Pz_nonneg hp1 hp2 x j ω
  unfold Q
  linarith

/-! ### Integrability of bounded functionals of the mark row -/

lemma integrable_of_bound {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : (ℕ → Bool) → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f (markMeasure (boolMeasure q))) (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := by
    haveI := isProbabilityMeasure_boolMeasure h0 h1
    infer_instance
  exact Integrable.of_bound hf C (Filter.Eventually.of_forall hC)

lemma integrable_rat {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (n : ℕ) : Integrable (fun ω : ℕ → Bool => rat p ω n)
      (markMeasure (boolMeasure q)) := by
  refine integrable_of_bound h0 h1 (fun ω : ℕ → Bool => rat p ω n) 1
    (measurable_rat p n).aestronglyMeasurable ?_
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (rat_nonneg hp1 hp2 ω n)]
  exact rat_le_one hp1 hp2 ω n

lemma integrable_Q {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (k x : ℕ) : Integrable (Q p k x) (markMeasure (boolMeasure q)) := by
  refine integrable_of_bound h0 h1 (Q p k x) (2 * (k : ℝ) + 1)
    (measurable_Q p k x).aestronglyMeasurable ?_
  intro ω
  rw [Real.norm_eq_abs]
  exact Q_abs_le hp1 hp2 k x ω

lemma integrable_one_add_Q {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) :
    Integrable (fun ω => 1 + Q p k x ω) (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := by
    haveI := isProbabilityMeasure_boolMeasure h0 h1
    infer_instance
  exact (integrable_const 1).add (integrable_Q h0 h1 hp1 hp2 k x)

lemma integrable_rat_mul {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x n : ℕ) :
    Integrable (fun ω : ℕ → Bool => rat p ω n * (1 + Q p k x ω))
      (markMeasure (boolMeasure q)) := by
  refine integrable_of_bound h0 h1
    (fun ω : ℕ → Bool => rat p ω n * (1 + Q p k x ω)) (2 * (k : ℝ) + 2)
    ((measurable_rat p n).mul (measurable_const.add (measurable_Q p k x))).aestronglyMeasurable
    ?_
  intro ω
  have hr0 := rat_nonneg hp1 hp2 ω n
  have hr1 := rat_le_one hp1 hp2 ω n
  have hQ := Q_abs_le hp1 hp2 k x ω
  have hQle : Q p k x ω ≤ 2 * (k : ℝ) + 1 := (abs_le.1 hQ).2
  have hQge : -(2 * (k : ℝ) + 1) ≤ Q p k x ω := (abs_le.1 hQ).1
  have hpos : 0 ≤ rat p ω n * (1 + Q p k x ω) := by
    have h1' : 0 ≤ 1 + Q p k x ω := by
      have := Q_ge_neg_one hp1 hp2 k x ω; linarith
    exact mul_nonneg hr0 h1'
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  nlinarith

lemma integrable_rat_sq_mul_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x n : ℕ) :
    Integrable (fun ω : ℕ → Bool => (rat p ω n) ^ 2 * (1 + Q p k x ω) ^ 2)
      (markMeasure (boolMeasure q)) := by
  refine integrable_of_bound h0 h1
    (fun ω : ℕ → Bool => (rat p ω n) ^ 2 * (1 + Q p k x ω) ^ 2) ((2 * (k : ℝ) + 2) ^ 2)
    (((measurable_rat p n).pow_const 2).mul
      ((measurable_const.add (measurable_Q p k x)).pow_const 2)).aestronglyMeasurable
    ?_
  intro ω
  have hr0 := rat_nonneg hp1 hp2 ω n
  have hr1 := rat_le_one hp1 hp2 ω n
  have hQnl : 0 ≤ 1 + Q p k x ω := by
    have := Q_ge_neg_one hp1 hp2 k x ω; linarith
  have hQle : 1 + Q p k x ω ≤ 2 * (k : ℝ) + 2 := by
    have hQ := Q_abs_le hp1 hp2 k x ω
    linarith [(abs_le.1 hQ).2]
  have hsq : (1 + Q p k x ω) ^ 2 ≤ (2 * (k : ℝ) + 2) ^ 2 := by
    have h2 : 0 ≤ 2 * (k : ℝ) + 2 := by positivity
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hr2 : (rat p ω n) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (2 * (k : ℝ) + 2)]

/-! ### The law of the ratio -/

lemma integral_rat {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (n : ℕ) :
    ∫ ω, rat p ω n ∂(markMeasure (boolMeasure q)) = aC p q := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hb : ∫ ω, rat p ω n ∂(markMeasure (boolMeasure q))
      = ∫ b, (if b then (1 - p) / p else 1) ∂(boolMeasure q) :=
    SwarmSpatial.integral_eval (μB := boolMeasure q)
      (fun b : Bool => if b then (1 - p) / p else 1) n
  rw [hb, integral_boolMeasure h0 h1]
  simp [aC]

lemma integral_rat_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (n : ℕ) :
    ∫ ω, (rat p ω n) ^ 2 ∂(markMeasure (boolMeasure q)) = bC p q := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hb : ∫ ω, (rat p ω n) ^ 2 ∂(markMeasure (boolMeasure q))
      = ∫ b, (if b then (1 - p) / p else 1) ^ 2 ∂(boolMeasure q) :=
    SwarmSpatial.integral_eval (μB := boolMeasure q)
      (fun b : Bool => (if b then (1 - p) / p else 1) ^ 2) n
  rw [hb, integral_boolMeasure h0 h1]
  simp [bC]

/-! ### Independence of the current ratio from the truncated past -/

lemma mem_blkS_le {k x n : ℕ} (h : n ∈ blkS k x) : n ≤ x := by
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
  exact Nat.sub_le x u

lemma not_mem_blkS_self {k x : ℕ} (hx : 0 < x) : x ∉ blkS k (x - 1) := by
  intro h
  have := mem_blkS_le h
  omega

/-- `rho(x)` is independent of `Q k (x-1)`, which depends only on the marks `x-k, …, x-1`. -/
lemma indepFun_rat_Q {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (k x : ℕ) (hx : 0 < x) :
    IndepFun (fun ω : ℕ → Bool => rat p ω x) (Q p k (x - 1)) (markMeasure (boolMeasure q)) := by
  classical
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hdisj : Disjoint ({x} : Finset ℕ) (blkS k (x - 1)) := by
    rw [Finset.disjoint_singleton_left]
    exact not_mem_blkS_self hx
  have hbase := (iIndepFun_eval (μB := boolMeasure q)).indepFun_finset ({x} : Finset ℕ)
    (blkS k (x - 1)) hdisj (fun i => measurable_pi_apply i)
  have hleft : Measurable (fun v : (↑({x} : Finset ℕ)) → Bool => rat p (ext {x} v) x) :=
    measurable_of_finite _
  have hright : Measurable (fun v : (↑(blkS k (x - 1))) → Bool => Qblk p k (x - 1) v) :=
    measurable_Qblk p k (x - 1)
  have hcomp := hbase.comp hleft hright
  have e1 : ((fun v : (↑({x} : Finset ℕ)) → Bool => rat p (ext {x} v) x) ∘
      (fun (a : ℕ → Bool) (i : ({x} : Finset ℕ)) => a (i : ℕ)))
      = fun ω : ℕ → Bool => rat p ω x := by
    funext ω
    have hx' : x ∈ ({x} : Finset ℕ) := Finset.mem_singleton_self x
    show rat p (ext {x} (Finset.restrict {x} ω)) x = rat p ω x
    simp only [rat]
    rw [ext_restrict {x} ω x hx']
  have e2 : ((fun v : (↑(blkS k (x - 1))) → Bool => Qblk p k (x - 1) v) ∘
      (fun (a : ℕ → Bool) (i : (blkS k (x - 1))) => a (i : ℕ)))
      = fun ω : ℕ → Bool => Q p k (x - 1) ω := by
    funext ω
    exact (Q_eq_Qblk p k (x - 1) ω).symm
  rw [e1, e2] at hcomp
  exact hcomp

/-- Independence of `rho(x)` from `1 + Q k (x-1)`. -/
lemma indepFun_rat_one_add_Q {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (k x : ℕ) (hx : 0 < x) :
    IndepFun (fun ω : ℕ → Bool => rat p ω x) (fun ω => 1 + Q p k (x - 1) ω)
      (markMeasure (boolMeasure q)) := by
  have h := (indepFun_rat_Q h0 h1 p k x hx).comp (measurable_id)
    (by fun_prop : Measurable fun y : ℝ => 1 + y)
  simpa [Function.comp_def] using h

/-- Independence of `rho(x)^2` from `(1 + Q k (x-1))^2`. -/
lemma indepFun_rat_sq_Q_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (k x : ℕ) (hx : 0 < x) :
    IndepFun (fun ω : ℕ → Bool => (rat p ω x) ^ 2) (fun ω => (1 + Q p k (x - 1) ω) ^ 2)
      (markMeasure (boolMeasure q)) := by
  have h := (indepFun_rat_Q h0 h1 p k x hx).comp (by fun_prop : Measurable fun y : ℝ => y ^ 2)
    (by fun_prop : Measurable fun y : ℝ => (1 + y) ^ 2)
  simpa [Function.comp_def] using h

end

end LocSum
