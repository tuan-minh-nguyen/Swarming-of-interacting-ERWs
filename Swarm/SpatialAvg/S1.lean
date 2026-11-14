/-
  The telescoping identity behind (spav) and its rewriting in terms of the mark indicator.
-/
import Swarm.Imports
import Swarm.S0

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p : ℝ}

/-- One step of the recursion, in the form used for telescoping:
`h(k+1) - h(k) = 1 + xi(k+1) - (1 - xi(k+1)) h(k)`. -/
lemma hof_step_sub (hp0 : p ≠ 0) (ω : ℕ → Bool) (k : ℕ) :
    hof p ω (k + 1) - hof p ω k
      = 1 + xi p ω (k + 1) - (1 - xi p ω (k + 1)) * hof p ω k := by
  rw [hof_succ_xi p hp0]
  ring

/-- **The telescoping identity.**  With `h(-1)` replaced by the summand index shift, the weighted
sum of `(1 - xi) h` over the first `r` sites is explicit up to the two endpoints and the sum of
the ratios. -/
theorem telescope (hp0 : p ≠ 0) (ω : ℕ → Bool) (r : ℕ) :
    ∑ k ∈ Finset.range r, (1 - xi p ω (k + 1)) * hof p ω k
      = r + ∑ k ∈ Finset.range r, xi p ω (k + 1) + hof p ω 0 - hof p ω r := by
  have htel : ∑ k ∈ Finset.range r, (hof p ω (k + 1) - hof p ω k)
      = hof p ω r - hof p ω 0 := by
    simpa using Finset.sum_range_sub (fun k => hof p ω k) r
  have hcongr : ∑ k ∈ Finset.range r, (hof p ω (k + 1) - hof p ω k)
      = ∑ k ∈ Finset.range r, (1 + xi p ω (k + 1) - (1 - xi p ω (k + 1)) * hof p ω k) :=
    Finset.sum_congr rfl fun k _ => hof_step_sub hp0 ω k
  rw [hcongr, Finset.sum_sub_distrib, Finset.sum_add_distrib] at htel
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at htel
  linarith

/-- The complement of the ratio is `(1-rho)` times the mark indicator. -/
lemma one_sub_xi (ω : ℕ → Bool) (n : ℕ) :
    1 - xi p ω n = (1 - (1 - p) / p) * mk ω n := by
  rw [xi_eq]; ring

/-- The telescoping identity with the weights written as mark indicators. -/
theorem telescope_mk (hp0 : p ≠ 0) (ω : ℕ → Bool) (r : ℕ) :
    (1 - (1 - p) / p) * ∑ k ∈ Finset.range r, mk ω (k + 1) * hof p ω k
      = r + ∑ k ∈ Finset.range r, xi p ω (k + 1) + hof p ω 0 - hof p ω r := by
  rw [← telescope hp0 ω r]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_sub_xi]
  ring

end
end SwarmSpatial
