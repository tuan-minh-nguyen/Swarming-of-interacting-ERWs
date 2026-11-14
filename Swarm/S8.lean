/-
  Assembly of the spatial ergodic average (spav) from three almost-sure inputs:
  the strong law for the ratio process (`tendsto_xi_average`), the vanishing of `h(r)/r`,
  and the vanishing of the fluctuation `M_r/r`.  The last one is recorded as the named
  hypothesis `FluctuationVanishes`; everything else is proved.
-/
import Swarm.Imports
import Swarm.S7

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p : ℝ}

/-- **The key algebraic identity.**  Dividing the telescoping identity `telescope_mk` by `r`
expresses the spatial average of `h` through the average of the ratio process and the
fluctuation `M_r`. -/
theorem spav_identity (hp0 : p ≠ 0) (q : ℝ) (ω : ℕ → Bool) {r : ℕ} (hr : 1 ≤ r) :
    q * (1 - (1 - p) / p) * ((r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, hof p ω k)
      = 1 + (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1)
        + (r : ℝ)⁻¹ * hof p ω 0 - (r : ℝ)⁻¹ * hof p ω r
        - (1 - (1 - p) / p) * ((r : ℝ)⁻¹ * Msum q p r ω) := by
  have ht := telescope_mk hp0 ω r
  have hsplit : ∑ k ∈ Finset.range r, mk ω (k + 1) * hof p ω k
      = q * (∑ k ∈ Finset.range r, hof p ω k) + Msum q p r ω := by
    rw [Msum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dfun]
    ring
  rw [hsplit, mul_add] at ht
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0:ℝ) < r := by exact_mod_cast hr
    positivity
  field_simp at ht ⊢
  linarith [ht]

/-- **The one missing lemma.**  The centred-mark fluctuation is `o(r)` almost surely. -/
def FluctuationVanishes (p : ℝ) (m : ℕ) : Prop :=
  ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
    Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * Msum ((1 - p) ^ (m - 1)) p r ω)
      Filter.atTop (nhds 0)

end
end SwarmSpatial
