import Swarm.GammaTailExp
import Swarm.ActualBounds

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Enl

variable {N : ℕ}

/-- Enlarged group records attain every nonnegative level almost surely.  One member
of the group is unbounded above, and any position it attains is below the group record. -/
theorem ae_sigmaA_ne_top {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y : ℤ} (hy : 0 ≤ y) :
    ∀ᵐ U : Array N ∂(arrayMeasure N), sigmaA p m U hA y ≠ ⊤ := by
  filter_upwards [Swarming.Actual.ae_unbounded_above (N := N) hp m hA.choose] with U hU
  obtain ⟨n, hn⟩ := hU y.toNat
  rw [Int.toNat_of_nonneg hy] at hn
  have hle : sigmaA p m U hA y ≤ (n : WithTop ℕ) :=
    sigmaA_le_of_record_le ⟨n, le_rfl, hn.trans (pos_le_runMaxA hA.choose_spec)⟩
  exact ne_top_of_le_ne_top WithTop.coe_ne_top hle

/-- The infinite first-passage event has zero mass at every nonnegative group level. -/
theorem measure_sigmaA_eq_top {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y : ℤ} (hy : 0 ≤ y) :
    arrayMeasure N {U : Array N | sigmaA p m U hA y = ⊤} = 0 := by
  have h := (ae_iff (μ := arrayMeasure N)
    (p := fun U : Array N => sigmaA p m U hA y ≠ ⊤)).mp
    (ae_sigmaA_ne_top hp m A hA hy)
  simpa only [not_ne_iff] using h

/-- Both record-attainment defects in `gamma_count_tail` vanish on the actual model. -/
theorem gamma_count_tail_finite_records (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y0 : ℤ} (hy0 : 0 ≤ y0)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (K j : ℕ) :
    arrayMeasure N {U : Array N | ((Finset.range K).filter
        (fun i => U ∈ GammaSet p m hA (lvl y0 m i))).card ≤ j}
      ≤ ENNReal.ofReal ((ρ ^ j)⁻¹ *
          (1 - (1 - p) ^ ((2 * m - 1) * A.card)
            + (1 - p) ^ ((2 * m - 1) * A.card) * ρ) ^ K) := by
  have h := gamma_count_tail p hp0 hp1 m A hA hy0 ρ hρ0 hρ1 K j
  rw [measure_sigmaA_eq_top hp0 m A hA (lvl_nonneg hy0),
    measure_sigmaA_eq_top hp0 m A hA (lvl_nonneg hy0)] at h
  simp only [zero_add, add_zero] at h
  exact h

/-- Exponential stopped trial-count tail without either non-attainment defect. -/
theorem gamma_count_tail_exp_finite_records (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (A : Finset (Fin N)) (hA : A.Nonempty) {y0 : ℤ} (hy0 : 0 ≤ y0)
    (K j : ℕ) (hK : 0 < K)
    (hjc : (j : ℝ) ≤ (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card))
    (hthalf : (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) - j ≤ (K : ℝ) / 2) :
    arrayMeasure N {U : Array N | ((Finset.range K).filter
        (fun i => U ∈ GammaSet p m hA (lvl y0 m i))).card ≤ j}
      ≤ ENNReal.ofReal (Real.exp (-((((K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) - j) ^ 2)
          / (K : ℝ)))) := by
  have h := gamma_count_tail_exp p hp0 hp1 m A hA hy0 K j hK hjc hthalf
  rw [measure_sigmaA_eq_top hp0 m A hA (lvl_nonneg hy0),
    measure_sigmaA_eq_top hp0 m A hA (lvl_nonneg hy0)] at h
  simp only [zero_add, add_zero] at h
  exact h

end Swarming.Enl


