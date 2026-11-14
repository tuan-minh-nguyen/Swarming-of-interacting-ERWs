/-
  Moment bounds for the fluctuation `M_r = sum_{n<r} (mk(n+1)-q) h(n)`:
  `E M_r^2 <= C r` and `E M_r^4 <= B r^2`, by induction on `r`.

  The induction uses the expansion of `(M + d)^4`, the vanishing `E[M^3 d] = 0`
  (`integral_dep_mul_mark_sub`), the identity `E[M^2 d^2] = q(1-q) E[M^2 h(r)^2]`
  (`integral_dep_mul_mark_sub_sq`) and weighted AM-GM with a step-dependent weight.
  No Cauchy--Schwarz in `L^p` is needed: the weights are handled by pointwise Young
  inequalities whose parameter depends on `r`, which still gives `E M_r^4 = O(r^2)`.
-/
import Swarm.Imports
import Swarm.SpatialAvg.S1
import Swarm.SpatialAvg.S2
import Swarm.S3

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q C6 : ℝ}

/-- Weighted AM-GM: `2 a b <= c a ^ 2 + b ^ 2 / c` for `c > 0`. -/
lemma two_mul_le_weighted (a b c : ℝ) (hc : 0 < c) :
    2 * a * b ≤ c * a ^ 2 + b ^ 2 / c := by
  have h2 : c * a ^ 2 + b ^ 2 / c - 2 * a * b = (c * a - b) ^ 2 / c := by
    field_simp
    ring
  have h3 : 0 ≤ (c * a - b) ^ 2 / c := by positivity
  linarith

/-- `2 x y <= x^2 + y^2`. -/
lemma two_mul_le_sq_add_sq (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- `|x * y| <= x^2 + y^2`. -/
lemma abs_mul_le_sq_add_sq (x y : ℝ) : |x * y| ≤ x ^ 2 + y ^ 2 := by
  have key : 2 * |x| * |y| ≤ |x| ^ 2 + |y| ^ 2 := two_mul_le_sq_add_sq |x| |y|
  rw [sq_abs, sq_abs] at key
  have hnn : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  have h1 : |x| * |y| ≤ x ^ 2 + y ^ 2 := by linarith
  rwa [abs_mul]

/-- `|x * y| <= (x^2 + y^2)/2`. -/
lemma abs_mul_le_half (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have key : 2 * |x| * |y| ≤ |x| ^ 2 + |y| ^ 2 := two_mul_le_sq_add_sq |x| |y|
  rw [sq_abs, sq_abs] at key
  rw [abs_mul]
  linarith

/-- `∫ h(n)^k ≤ C6` for `k ≤ 6`, since `h >= 1`. -/
lemma integral_hof_pow_le_six (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {q : ℝ}
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6)
    {k : ℕ} (hk : k ≤ 6) (n : ℕ) :
    ∫ ω, (hof p ω n) ^ k ∂(markMeasure (boolMeasure q)) ≤ C6 := by
  refine le_trans (integral_mono (integrable_hof_pow hp1 hp2 hk hu6i n) (hu6i n) ?_) (hu6b n)
  exact fun ω => hof_pow_le_six hp1 hp2 hk ω n

/-- Integrability of any power `≤ 6` of a martingale difference. -/
lemma integrable_dfun_pow (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    {k : ℕ} (hk : k ≤ 6) (n : ℕ) :
    Integrable (fun ω => (dfun q p n ω) ^ k) (markMeasure (boolMeasure q)) := by
  refine Integrable.mono' (hu6i n)
    (((measurable_dfun (by linarith : p ≠ 0) n).pow_const k).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hu1 : (1:ℝ) ≤ hof p ω n := one_le_hof hp1.le hp2 ω n
  have hmk : |mk ω (n + 1) - q| ≤ 1 := by
    rcases mk_zero_or_one ω (n + 1) with h | h
    · rw [h, zero_sub, abs_neg, abs_of_nonneg h0]; linarith
    · rw [h, abs_le]; constructor <;> linarith
  have hd1 : |dfun q p n ω| ≤ hof p ω n := by
    rw [dfun, abs_mul]
    calc |mk ω (n + 1) - q| * |hof p ω n| ≤ 1 * hof p ω n := by
          apply mul_le_mul hmk ?_ (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (by linarith)]
      _ = hof p ω n := by ring
  rw [Real.norm_eq_abs, abs_pow]
  exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hd1 k)
    (hof_pow_le_six hp1 hp2 hk ω n)


/-! ### The moment induction -/

/-- `M_r` times the mark-centred increment: `E[M_r d_r] = 0`. -/
lemma integral_Msum_mul_dfun {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) (hI2 : Integrable (fun ω => (Msum q p r ω) ^ 2) (markMeasure (boolMeasure q))) :
    ∫ ω, Msum q p r ω * dfun q p r ω ∂(markMeasure (boolMeasure q)) = 0 := by
  have hdep : DependsOn r (fun ω => Msum q p r ω * hof p ω r) :=
    (dependsOn_Msum r).mul (dependsOn_hof (le_refl r))
  have hW : Measurable (fun ω => Msum q p r ω * hof p ω r) :=
    (measurable_Msum (by linarith : p ≠ 0) r).mul (measurable_hof (by linarith) r)
  have hu2 : Integrable (fun ω => (hof p ω r) ^ 2) (markMeasure (boolMeasure q)) :=
    integrable_hof_pow hp1 hp2 (by norm_num) hu6i r
  have hint : Integrable (fun ω => Msum q p r ω * hof p ω r) (markMeasure (boolMeasure q)) := by
    refine Integrable.mono' (hI2.add hu2)
      (hW.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    simpa using abs_mul_le_sq_add_sq (Msum q p r ω) (hof p ω r)
  have h := integral_dep_mul_mark_sub h0 h1 hdep hW hint
  calc ∫ ω, Msum q p r ω * dfun q p r ω ∂(markMeasure (boolMeasure q))
      = ∫ ω, (Msum q p r ω * hof p ω r) * (mk ω (r + 1) - q)
          ∂(markMeasure (boolMeasure q)) := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [dfun]
        ring
    _ = 0 := h

/-- `E[M_r^2 d_r^2] = q (1-q) E[M_r^2 h(r)^2]`. -/
lemma integral_Msum_sq_mul_dfun_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) (hI4 : Integrable (fun ω => (Msum q p r ω) ^ 4) (markMeasure (boolMeasure q)))
    (hI2 : Integrable (fun ω => (Msum q p r ω) ^ 2) (markMeasure (boolMeasure q))) :
    ∫ ω, (Msum q p r ω) ^ 2 * (dfun q p r ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = q * (1 - q) * ∫ ω, (Msum q p r ω) ^ 2 * (hof p ω r) ^ 2
          ∂(markMeasure (boolMeasure q)) := by
  have hdep : DependsOn r (fun ω => (Msum q p r ω) ^ 2 * (hof p ω r) ^ 2) :=
    ((dependsOn_Msum r).pow 2).mul ((dependsOn_hof (le_refl r)).pow 2)
  have hW : Measurable (fun ω => (Msum q p r ω) ^ 2 * (hof p ω r) ^ 2) :=
    ((measurable_Msum (by linarith : p ≠ 0) r).pow_const 2).mul
      ((measurable_hof (by linarith) r).pow_const 2)
  have hu4 : Integrable (fun ω => (hof p ω r) ^ 4) (markMeasure (boolMeasure q)) :=
    integrable_hof_pow hp1 hp2 (by norm_num) hu6i r
  have hint : Integrable (fun ω => (Msum q p r ω) ^ 2 * (hof p ω r) ^ 2)
      (markMeasure (boolMeasure q)) := by
    refine Integrable.mono' ((hI4.const_mul (1/2)).add (hu4.const_mul (1/2)))
      (hW.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have h := abs_mul_le_half ((Msum q p r ω) ^ 2) ((hof p ω r) ^ 2)
    have e1 : ((Msum q p r ω) ^ 2) ^ 2 = (Msum q p r ω) ^ 4 := by ring
    have e2 : ((hof p ω r) ^ 2) ^ 2 = (hof p ω r) ^ 4 := by ring
    rw [e1, e2] at h
    have h2 : ((Msum q p r ω) ^ 4 + (hof p ω r) ^ 4) / 2
        = 1 / 2 * (Msum q p r ω) ^ 4 + 1 / 2 * (hof p ω r) ^ 4 := by ring
    rw [h2] at h
    simpa using h
  have h := integral_dep_mul_mark_sub_sq h0 h1 hdep hW hint
  calc ∫ ω, (Msum q p r ω) ^ 2 * (dfun q p r ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = ∫ ω, ((Msum q p r ω) ^ 2 * (hof p ω r) ^ 2) * (mk ω (r + 1) - q) ^ 2
          ∂(markMeasure (boolMeasure q)) := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [dfun]
        ring
    _ = _ := h

end
end SwarmSpatial
