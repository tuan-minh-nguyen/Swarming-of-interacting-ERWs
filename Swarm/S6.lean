/-
  The fourth-moment step for the fluctuation `M_r`, the moment induction, and the
  almost-sure strong law `M_r / r -> 0`.
-/
import Swarm.Imports
import Swarm.S5

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q C6 : ℝ}

/-- `A^3 B <= (3 A^4 + B^4)/4` for `A, B >= 0`. -/
lemma pow_three_mul_le (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A ^ 3 * B ≤ (3 * A ^ 4 + B ^ 4) / 4 := by
  have h1 : 2 * A ^ 2 * (A * B) ≤ A ^ 4 + (A * B) ^ 2 := by
    have h := two_mul_le_sq_add_sq (A ^ 2) (A * B)
    have e : (A ^ 2) ^ 2 = A ^ 4 := by ring
    rwa [e] at h
  have h2 : 2 * A * B ≤ A ^ 2 + B ^ 2 := two_mul_le_sq_add_sq A B
  have h3 : 0 ≤ A * B := mul_nonneg hA hB
  nlinarith [h1, h2, h3]

/-- `|M| u^3 <= (M^2 u^2 + u^4)/2`. -/
lemma abs_mul_cube_le (M u : ℝ) (_hu : 0 ≤ u) :
    |M| * u ^ 3 ≤ (M ^ 2 * u ^ 2 + u ^ 4) / 2 := by
  have h1 : 2 * (|M| * u) * (u ^ 2) ≤ (|M| * u) ^ 2 + (u ^ 2) ^ 2 :=
    two_mul_le_sq_add_sq (|M| * u) (u ^ 2)
  have h2 : (|M| * u) ^ 2 = M ^ 2 * u ^ 2 := by rw [mul_pow, sq_abs]
  have h3 : (u ^ 2) ^ 2 = u ^ 4 := by ring
  rw [h2, h3] at h1
  nlinarith [h1, _hu, abs_nonneg M]

/-- Pointwise Young for `M^2 u^2` with a step-dependent weight. -/
lemma sq_mul_sq_le (M u : ℝ) (c : ℝ) (hc : 0 < c) :
    M ^ 2 * u ^ 2 ≤ c / 2 * M ^ 4 + 1 / (2 * c) * u ^ 4 := by
  have h := two_mul_le_weighted (M ^ 2) (u ^ 2) c hc
  have e1 : (M ^ 2) ^ 2 = M ^ 4 := by ring
  have e2 : (u ^ 2) ^ 2 = u ^ 4 := by ring
  rw [e1, e2] at h
  have key : 2 * c * (M ^ 2 * u ^ 2) ≤ c ^ 2 * M ^ 4 + u ^ 4 := by
    have hmul : c * (2 * M ^ 2 * u ^ 2) ≤ c * (c * M ^ 4 + u ^ 4 / c) :=
      mul_le_mul_of_nonneg_left h hc.le
    have hrhs : c * (c * M ^ 4 + u ^ 4 / c) = c ^ 2 * M ^ 4 + u ^ 4 := by
      field_simp
    rw [hrhs] at hmul
    nlinarith [hmul]
  have e3 : c / 2 * M ^ 4 + 1 / (2 * c) * u ^ 4 = (c ^ 2 * M ^ 4 + u ^ 4) / (2 * c) := by
    field_simp
  rw [e3, le_div_iff₀ (by positivity)]
  linarith [key]


end
end SwarmSpatial
