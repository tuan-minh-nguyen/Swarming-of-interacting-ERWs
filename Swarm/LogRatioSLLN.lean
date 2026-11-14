/-
  **The exact log-ratio strong law of the paper's i.i.d. site marks.**

  `main_1d_revised.tex`, proof of Lemma `transience`, uses

      "By the strong law of large numbers we have a.s.
         (1/r) sum_{x=1}^{r} log((1 - omega_j(x))/omega_j(x)) -> (1-p)^{m-1} log((1-p)/p) = -4c."

  This file proves exactly that statement for the actual mark law, with no
  hypothesis hidden in a structure and no `0 log 0` convention assumed:

  * `SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)` is the i.i.d. Bernoulli(`q`)
    family of site marks on `ℕ` (the law of the paper's `B_j(x)`), and
    `SwarmSpatial.rhoOf p (ω x) = (1 - omega_j(x))/omega_j(x)` is a function of the
    mark at site `x` only, taking the values `(1-p)/p` (marked) and `1` (unmarked).
  * `tendsto_avg_boolFun` : the general strong law for an arbitrary real function of
    an i.i.d. `Bool` coordinate, with the exact mean `q * Φ true + (1-q) * Φ false`.
  * `integral_logRhoFun` / `tendsto_avg_logRho` : the concrete log-ratio average
    converges a.s. to `q * log ((1-p)/p)`; the unmarked branch contributes exactly
    `log 1 = 0`, which is *proved*, not assumed.
  * `paperC` is the paper's constant `c` with `-4c = q log((1-p)/p)`;
    `paperC_pos` proves `0 < c` in the paper's parameter range `1/2 < p < 1`, `q > 0`.

  All proofs here are complete and use standard foundations: the only probabilistic input is Mathlib's
  Etemadi strong law `ProbabilityTheory.strong_law_ae_real`, applied to the
  coordinates of the product measure `Measure.infinitePi`.
-/
import Swarm.Imports
import Swarm.MarkProcess
import Swarm.SpatialData

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace SwarmLogRatio

noncomputable section

section AbsBound

/-- A real function of a `Bool` is bounded by the sum of its two absolute values. -/
lemma abs_le_sum_parts (Φ : Bool → ℝ) (b : Bool) : |Φ b| ≤ |Φ true| + |Φ false| := by
  cases b with
  | false => exact le_add_of_nonneg_left (abs_nonneg _)
  | true => exact le_add_of_nonneg_right (abs_nonneg _)

end AbsBound

/-! ### The one-site function and its exact mean -/

/-- The paper's site ratio `(1 - omega_j(x))/omega_j(x)` is a function of the mark at `x`. -/
@[simp] lemma rhoOf_true (p : ℝ) : SwarmSpatial.rhoOf p true = (1 - p) / p :=
  SwarmSpatial.rhoOf_true p

@[simp] lemma rhoOf_false (p : ℝ) : SwarmSpatial.rhoOf p false = 1 :=
  SwarmSpatial.rhoOf_false p

/-- A marked site has ratio `(1-p)/p`, an unmarked site ratio `1`. -/
lemma log_rhoOf_eq (p : ℝ) (b : Bool) :
    Real.log (SwarmSpatial.rhoOf p b) = if b then Real.log ((1 - p) / p) else 0 := by
  cases b with
  | false => simp
  | true => simp

/-- The site ratio is positive throughout the paper's range `0 < p < 1`. -/
lemma rhoOf_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    0 < SwarmSpatial.rhoOf p b := by
  cases b with
  | false => simp
  | true =>
      simp only [rhoOf_true]
      positivity

/-- The two laws agree definitionally: the marks area writes `boolMeasure`, the
spatial area `markLaw`, and they are the same two-point Bernoulli law. -/
lemma boolMeasure_eq_markLaw (q : ℝ) :
    SwarmMarks.boolMeasure q = SwarmSpatial.markLaw q := rfl

/-- **The exact mean of a function of the mark at one site.**  For the product
measure of the i.i.d. Bernoulli(`q`) marks, `E[Φ(mark 0)] = q Φ(true) + (1-q) Φ(false)`. -/
theorem integral_boolFun {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (Φ : Bool → ℝ) :
    ∫ ω, Φ (ω 0) ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))
      = q * Φ true + (1 - q) * Φ false := by
  haveI : IsProbabilityMeasure (SwarmMarks.boolMeasure q) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure h0 h1
  have hmap : (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)).map
      (fun ω : ℕ → Bool => ω 0) = SwarmMarks.boolMeasure q := by
    simp only [SwarmMarks.markMeasure]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => SwarmMarks.boolMeasure q) 0
  have hΦm : Measurable Φ := measurable_of_finite Φ
  have hφm : Measurable fun ω : ℕ → Bool => ω 0 := measurable_pi_apply 0
  have hfm : AEStronglyMeasurable Φ
      (Measure.map (fun ω : ℕ → Bool => ω 0)
        (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))) := hΦm.aestronglyMeasurable
  rw [← integral_map (φ := fun ω : ℕ → Bool => ω 0) (f := Φ) hφm.aemeasurable hfm, hmap,
    boolMeasure_eq_markLaw q]
  exact SwarmSpatial.integral_markLaw h0 h1 Φ

/-- **The exact mean of the log-ratio at one site:**
`E[log rho_j(0)] = q log((1-p)/p)`; the unmarked sites contribute `log 1 = 0`. -/
theorem integral_logRhoFun {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∫ ω, Real.log (SwarmSpatial.rhoOf p (ω 0))
        ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))
      = q * Real.log ((1 - p) / p) := by
  have h := integral_boolFun (q := q) h0 h1 (fun b : Bool => Real.log (SwarmSpatial.rhoOf p b))
  simpa using h

/-! ### The general strong law for a function of the i.i.d. marks -/

/-- **Strong law for the site-mark average.**  For any real `Φ` on the two-point mark
space, the Cesàro averages of `Φ(ω x)` converge almost surely to the exact mean
`q Φ(true) + (1-q) Φ(false)`.  The coordinates of `Measure.infinitePi` are i.i.d.
(`SwarmMarks.iIndepFun_eval` plus `Measure.infinitePi_map_eval`), so Etemadi's strong
law applies. -/
theorem tendsto_avg_boolFun {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (Φ : Bool → ℝ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Tendsto (fun n : ℕ => (∑ x ∈ Finset.range n, Φ (ω x)) / n) atTop
        (𝓝 (q * Φ true + (1 - q) * Φ false)) := by
  haveI : IsProbabilityMeasure (SwarmMarks.boolMeasure q) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure h0 h1
  have hμm : ∀ k : ℕ, (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)).map
      (fun ω : ℕ → Bool => ω k) = SwarmMarks.boolMeasure q := by
    intro k
    simp only [SwarmMarks.markMeasure]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => SwarmMarks.boolMeasure q) k
  have hΦm : Measurable Φ := measurable_of_finite Φ
  -- bounded, hence integrable
  have hint : Integrable (fun ω : ℕ → Bool => Φ (ω 0))
      (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)) := by
    refine Integrable.of_bound (hΦm.comp (measurable_pi_apply 0)).aestronglyMeasurable
      (|Φ true| + |Φ false|) ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using abs_le_sum_parts Φ (ω 0)
  -- pairwise independence
  have hindep : Pairwise (fun (i j : ℕ) =>
      IndepFun (fun ω : ℕ → Bool => Φ (ω i)) (fun ω => Φ (ω j))
        (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))) := by
    intro i j hij
    have h := (SwarmMarks.iIndepFun_eval (μB := SwarmMarks.boolMeasure q)).indepFun hij
    simpa only [Function.comp_def] using h.comp hΦm hΦm
  -- identical distribution
  have hidEval : ∀ k : ℕ, IdentDistrib (fun ω : ℕ → Bool => ω k) (fun ω => ω 0)
      (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))
      (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)) := by
    intro k
    refine ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
    rw [hμm k, hμm 0]
  have hident : ∀ k : ℕ, IdentDistrib (fun ω : ℕ → Bool => Φ (ω k)) (fun ω => Φ (ω 0))
      (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))
      (SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)) :=
    fun k => (hidEval k).comp hΦm
  have key := strong_law_ae_real (μ := SwarmMarks.markMeasure (SwarmMarks.boolMeasure q))
    (fun k ω => Φ (ω k)) hint hindep hident
  rw [integral_boolFun h0 h1 Φ] at key
  exact key

/-- **The exact log-ratio strong law** (the display quoted at the start of
`Swarm/ProdDecay.lean`): almost surely,

`(1/r) sum_{x<r} log((1 - omega_j(x))/omega_j(x)) -> q * log((1-p)/p)`.

No hypothesis on `p` is needed for the identity itself (for `p ≤ 0` or `p ≥ 1` the Lean
value `(1-p)/p` and `Real.log` are still well defined); `paperC_pos` below supplies the
paper's range where the limit is negative. -/
theorem tendsto_avg_logRho {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Tendsto
        (fun r : ℕ => (∑ x ∈ Finset.range r, Real.log (SwarmSpatial.rhoOf p (ω x))) / r)
        atTop (𝓝 (q * Real.log ((1 - p) / p))) := by
  have h := tendsto_avg_boolFun (q := q) h0 h1
    (fun b : Bool => Real.log (SwarmSpatial.rhoOf p b))
  simpa using h

/-- The same limit in the `(1/r) * sum` form of the paper's display. -/
theorem tendsto_inv_mul_logRho {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Tendsto
        (fun r : ℕ => (r : ℝ)⁻¹ * ∑ x ∈ Finset.range r, Real.log (SwarmSpatial.rhoOf p (ω x)))
        atTop (𝓝 (q * Real.log ((1 - p) / p))) := by
  filter_upwards [tendsto_avg_logRho (q := q) h0 h1 p] with ω hω
  refine hω.congr (fun r => ?_)
  rw [div_eq_inv_mul]

/-! ### The paper's constant `c` with `-4c = q log((1-p)/p)` -/

/-- The paper's constant: `c = -(q log((1-p)/p))/4`, so that `-4c = q log((1-p)/p)`. -/
def paperC (p q : ℝ) : ℝ := -(q * Real.log ((1 - p) / p)) / 4

/-- `-4 c = q log((1-p)/p)` by definition of `paperC`. -/
theorem neg_four_paperC (p q : ℝ) : -4 * paperC p q = q * Real.log ((1 - p) / p) := by
  unfold paperC; ring

/-- **`c > 0` in the paper's range.**  For `1/2 < p < 1` and `q > 0` the log-ratio
`log((1-p)/p)` is strictly negative, so `c = -(q log((1-p)/p))/4 > 0`. -/
theorem paperC_pos {p q : ℝ} (hq : 0 < q) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) :
    0 < paperC p q := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < (1 - p) / p := by positivity
  have hr1 : (1 - p) / p < 1 := by
    rw [div_lt_one hp0]; linarith
  have hlog : Real.log ((1 - p) / p) < 0 := Real.log_neg hr0 hr1
  have hneg : q * Real.log ((1 - p) / p) < 0 := mul_neg_of_pos_of_neg hq hlog
  unfold paperC
  linarith

end

end SwarmLogRatio
