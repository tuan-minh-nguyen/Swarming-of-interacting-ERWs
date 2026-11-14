/-
  Assembly of (spav): from the strong law for the ratio process, `h(r)/r -> 0`, and the
  vanishing of the fluctuation `M_r/r`, the spatial average converges to the paper's limit.
-/
import Swarm.Imports
import Swarm.MarkTails
import Swarm.S8

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p : ℝ}

/-- The paper's limit written as `(1+a) / (1-a)`, using `1 - a = q (1 - rho)`. -/
lemma targetParam_eq (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    (1 + aParam p m) / ((1 - p) ^ (m - 1) * (1 - (1 - p) / p)) = targetParam p m := by
  rw [targetParam, ← one_sub_aParam (show p ≠ 0 by linarith) hm]

/-- **Assembly of (spav).** -/
theorem spav_of_vanishes (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (hfl : FluctuationVanishes p m)
    (hzero : ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * hof p ω r) Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k)
        Filter.atTop (nhds (targetParam p m)) := by
  have hp0 : p ≠ 0 := by linarith
  have hQpos : (0:ℝ) < (1 - p) ^ (m - 1) * (1 - (1 - p) / p) :=
    mul_pos (qpos hp2) (one_sub_rho_pos hp1 hp2)
  have hQne : ((1 - p) ^ (m - 1) * (1 - (1 - p) / p)) ≠ 0 := ne_of_gt hQpos
  filter_upwards [tendsto_xi_average hp1 hp2 hm, hfl, hzero] with ω hxi hM hz
  have hint : Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * hof p ω 0) Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun r : ℕ => ((r : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using hinv.mul_const (hof p ω 0)
  have hMc : Filter.Tendsto
      (fun r : ℕ => (1 - (1 - p) / p) * ((r : ℝ)⁻¹ * Msum ((1 - p) ^ (m - 1)) p r ω))
      Filter.atTop (nhds 0) := by
    simpa using hM.const_mul (1 - (1 - p) / p)
  have hlimR : Filter.Tendsto (fun r : ℕ =>
      1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1)
        + (r : ℝ)⁻¹ * hof p ω 0 - (r : ℝ)⁻¹ * hof p ω r
        - (1 - (1 - p) / p) * ((r : ℝ)⁻¹ * Msum ((1 - p) ^ (m - 1)) p r ω))
      Filter.atTop (nhds (1 + aParam p m)) := by
    have h1 : Filter.Tendsto
        (fun r : ℕ => 1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1))
        Filter.atTop (nhds (1 + aParam p m)) := Filter.Tendsto.const_add 1 hxi
    have h2 : Filter.Tendsto (fun r : ℕ =>
        (1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1)) + (r : ℝ)⁻¹ * hof p ω 0)
        Filter.atTop (nhds (1 + aParam p m)) := by
      simpa using h1.add hint
    have h3 : Filter.Tendsto (fun r : ℕ =>
        ((1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1)) + (r : ℝ)⁻¹ * hof p ω 0)
          - (r : ℝ)⁻¹ * hof p ω r)
        Filter.atTop (nhds (1 + aParam p m)) := by
      simpa using h2.sub hz
    have h4 : Filter.Tendsto (fun r : ℕ =>
        (((1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1)) + (r : ℝ)⁻¹ * hof p ω 0)
          - (r : ℝ)⁻¹ * hof p ω r) - (1 - (1 - p) / p) * ((r : ℝ)⁻¹ * Msum ((1 - p) ^ (m - 1)) p r ω))
        Filter.atTop (nhds (1 + aParam p m)) := by
      simpa using h3.sub hMc
    simpa using h4
  have hmain : Filter.Tendsto (fun r : ℕ =>
      ((1 - p) ^ (m - 1) * (1 - (1 - p) / p))
        * ((r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k))
      Filter.atTop (nhds (1 + aParam p m)) := by
    refine hlimR.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    exact (spav_identity hp0 ((1 - p) ^ (m - 1)) ω hr).symm
  have h2 := hmain.const_mul (((1 - p) ^ (m - 1) * (1 - (1 - p) / p)))⁻¹
  have h3 : ((1 - p) ^ (m - 1) * (1 - (1 - p) / p))⁻¹ * (1 + aParam p m)
      = (1 + aParam p m) / ((1 - p) ^ (m - 1) * (1 - (1 - p) / p)) := by
    field_simp
  rw [h3] at h2
  have hfin : Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k)
      Filter.atTop (nhds ((1 + aParam p m) / ((1 - p) ^ (m - 1) * (1 - (1 - p) / p)))) := by
    refine h2.congr' ?_
    filter_upwards with r
    rw [inv_mul_cancel_left₀ hQne]
  rw [targetParam_eq hp1 hp2 hm] at hfin
  exact hfin

end
end SwarmSpatial
