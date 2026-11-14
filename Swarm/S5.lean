/-
  Moment bounds for the fluctuation and the almost-sure strong law `M_r / r -> 0`.
-/
import Swarm.Imports
import Swarm.SpatialAvg.S1
import Swarm.SpatialAvg.S2
import Swarm.S3
import Swarm.S4

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q C6 : ℝ}

/-- Integrability of `h(r)`. -/
lemma integrable_hof (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {q : ℝ}
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (r : ℕ) : Integrable (fun ω => hof p ω r) (markMeasure (boolMeasure q)) := by
  simpa only [pow_one] using integrable_hof_pow (k := 1) hp1 hp2 (by norm_num) hu6i r

/-- **Second moment step.** -/
lemma Msum_sq_step {p : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6)
    (hC6 : 0 ≤ C6) (r : ℕ)
    (hI2 : Integrable (fun ω => (Msum q p r ω) ^ 2) (markMeasure (boolMeasure q))) :
    Integrable (fun ω => (Msum q p (r + 1) ω) ^ 2) (markMeasure (boolMeasure q)) ∧
      ∫ ω, (Msum q p (r + 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))
        ≤ ∫ ω, (Msum q p r ω) ^ 2 ∂(markMeasure (boolMeasure q)) + C6 := by
  have hd2 : Integrable (fun ω => (dfun q p r ω) ^ 2) (markMeasure (boolMeasure q)) :=
    integrable_dfun_pow hp1 hp2 h0 h1 hu6i (by norm_num) r
  have hMd : Integrable (fun ω => Msum q p r ω * dfun q p r ω)
      (markMeasure (boolMeasure q)) := by
    refine Integrable.mono' (hI2.add hd2)
      (((measurable_Msum (by linarith : p ≠ 0) r).mul (measurable_dfun (by linarith : p ≠ 0) r)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    simpa using abs_mul_le_sq_add_sq (Msum q p r ω) (dfun q p r ω)
  have hcross : ∫ ω, Msum q p r ω * dfun q p r ω ∂(markMeasure (boolMeasure q)) = 0 :=
    integral_Msum_mul_dfun h0 h1 hp1 hp2 hu6i r hI2
  have hdsq : ∫ ω, (dfun q p r ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = q * (1 - q) * ∫ ω, (hof p ω r) ^ 2 ∂(markMeasure (boolMeasure q)) :=
    integral_dfun_sq h0 h1 hp1 hp2 hu6i r
  have hu2le : ∫ ω, (hof p ω r) ^ 2 ∂(markMeasure (boolMeasure q)) ≤ C6 :=
    integral_hof_pow_le_six hp1 hp2 hu6i hu6b (by norm_num) r
  have hq : 0 ≤ q * (1 - q) := by nlinarith
  have hq1 : q * (1 - q) ≤ 1 := by nlinarith
  have hFG : Integrable (fun ω => (Msum q p r ω) ^ 2 + 2 * (Msum q p r ω * dfun q p r ω))
      (markMeasure (boolMeasure q)) :=
    (hI2.add (hMd.const_mul 2)).congr
      (Filter.Eventually.of_forall fun ω => by simp [Pi.add_apply])
  have hstep : ∫ ω, (Msum q p (r + 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = ∫ ω, (Msum q p r ω) ^ 2 ∂(markMeasure (boolMeasure q))
        + 2 * ∫ ω, Msum q p r ω * dfun q p r ω ∂(markMeasure (boolMeasure q))
        + ∫ ω, (dfun q p r ω) ^ 2 ∂(markMeasure (boolMeasure q)) := by
    have e1 : ∫ ω, (Msum q p (r + 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))
        = ∫ ω, ((Msum q p r ω) ^ 2 + 2 * (Msum q p r ω * dfun q p r ω)
            + (dfun q p r ω) ^ 2) ∂(markMeasure (boolMeasure q)) := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Msum_succ]; ring
    rw [e1, integral_add hFG hd2]
    have : ∫ ω, ((Msum q p r ω) ^ 2 + 2 * (Msum q p r ω * dfun q p r ω))
        ∂(markMeasure (boolMeasure q))
        = ∫ ω, (Msum q p r ω) ^ 2 ∂(markMeasure (boolMeasure q))
          + 2 * ∫ ω, Msum q p r ω * dfun q p r ω ∂(markMeasure (boolMeasure q)) := by
      rw [integral_add hI2 (hMd.const_mul 2), integral_const_mul]
    rw [this]
  refine ⟨?_, ?_⟩
  · refine (hFG.add hd2).congr ?_
    filter_upwards with ω
    simp only [Pi.add_apply]
    rw [Msum_succ]; ring
  · rw [hstep, hcross, hdsq]
    have hu2le' : q * (1 - q) * ∫ ω, (hof p ω r) ^ 2 ∂(markMeasure (boolMeasure q)) ≤ C6 := by
      calc q * (1 - q) * ∫ ω, (hof p ω r) ^ 2 ∂(markMeasure (boolMeasure q))
          ≤ 1 * C6 := by
            apply mul_le_mul hq1 hu2le (by positivity) (by norm_num)
        _ = C6 := by ring
    linarith

end
end SwarmSpatial
