/-
  `h(r)/r -> 0` almost surely, from the logarithmic bound (Kmom) proved in `MarkTails`.
-/
import Swarm.Imports
import Swarm.MarkTails
import Swarm.S9

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p : ℝ}

/-- `log (r + c) / r -> 0`. -/
lemma tendsto_log_div_nat {c : ℝ} (hc : 0 ≤ c) :
    Filter.Tendsto (fun r : ℕ => Real.log ((r : ℝ) + c) / (r : ℝ)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    simpa using h
  have hshift : Filter.Tendsto (fun r : ℕ => (r : ℝ) + c) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun r : ℕ => by push_cast; linarith)
      tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun r : ℕ => Real.log ((r : ℝ) + c) / ((r : ℝ) + c))
      Filter.atTop (nhds 0) := h1.comp hshift
  have h3 : Filter.Tendsto (fun r : ℕ => ((r : ℝ) + c) / (r : ℝ)) Filter.atTop (nhds 1) := by
    have h4 : Filter.Tendsto (fun r : ℕ => c / (r : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c
    have h5 : Filter.Tendsto (fun r : ℕ => 1 + c / (r : ℝ)) Filter.atTop (nhds 1) := by
      have hc1 : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
      have h := hc1.add h4
      simpa using h
    refine h5.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    field_simp
  have h6 := h2.mul h3
  have h6' : Filter.Tendsto
      (fun r : ℕ => Real.log ((r : ℝ) + c) / ((r : ℝ) + c) * (((r : ℝ) + c) / (r : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using h6
  refine h6'.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hrc : ((r : ℝ) + c) ≠ 0 := by
    have : (0:ℝ) < r := by exact_mod_cast hr
    positivity
  field_simp

/-- **`h(r)/r -> 0` almost surely.** -/
theorem tendsto_hof_ratio (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * hof p ω r) Filter.atTop (nhds 0) := by
  have hq0 : 0 < (1 - p) ^ (m - 1) := qpos hp2
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := qle_one hp1 hp2 (by omega)
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ (m - 1))) :=
    isProbabilityMeasure_boolMeasure hq0.le hq1
  obtain ⟨θ, hθ, hγ⟩ := exists_theta hp1 hp2 hq0 hq1
  have hγpos : 0 < (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
      + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by
    have h1 : 0 ≤ (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ) := by positivity
    have h2 : 0 < (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by
      have hr : 0 < (1 - p) / p := by positivity
      positivity
    linarith
  have ht := hof_eventually_log_bound (p := p) (q := (1 - p) ^ (m - 1)) hp1 hp2 hq0 hq1 hθ
    hγpos hγ le_rfl
  have hlog := tendsto_log_div_nat (c := 2) (by norm_num)
  have hlim : Filter.Tendsto (fun r : ℕ => (3 / θ) * (Real.log ((r : ℝ) + 2) / (r : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul (3 / θ)
  filter_upwards [ht] with ω hω
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hω, Filter.eventually_gt_atTop 0] with r hr hr0
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr0
  have hb : hof p ω r ≤ (3 / θ) * Real.log ((r : ℝ) + 2) := hr r (by omega)
  have hnn : 0 ≤ hof p ω r := by linarith [one_le_hof hp1.le hp2 ω r]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show (r : ℝ)⁻¹ * hof p ω r = hof p ω r / (r : ℝ) by ring]
  calc hof p ω r / (r : ℝ) ≤ ((3 / θ) * Real.log ((r : ℝ) + 2)) / (r : ℝ) := by
        apply div_le_div_of_nonneg_right hb hrpos.le
    _ = (3 / θ) * (Real.log ((r : ℝ) + 2) / (r : ℝ)) := by ring

/-- **(spav), first display, modulo the single fluctuation lemma.**  For the actual i.i.d.
Bernoulli site marks with `q = (1-p)^{m-1}`, the spatial average of the paper's `h_j`
converges almost surely to `(1+a)/(1-a)`, `a = 1 - (2p-1)q/p`. -/
theorem spav (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hfl : FluctuationVanishes p m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k)
        Filter.atTop (nhds (targetParam p m)) :=
  spav_of_vanishes hp1 hp2 (by omega) hfl (tendsto_hof_ratio hp1 hp2 hm)

end
end SwarmSpatial
