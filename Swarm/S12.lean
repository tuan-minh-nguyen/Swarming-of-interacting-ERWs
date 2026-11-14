import Swarm.Imports
import Swarm.S11
import Swarm.MartingaleLimit

/-!
Uniform initial-segment form of the spatial-average limit.

The sequential limit supplies `Q t / t → 0` for the centred spatial sum.  The
already verified `MartingaleLimit.tendsto_running_max` proves the needed uniform
estimate: the early terms form a finite deterministic set, while the bound for
later `t ≤ n` is inherited from the bound at `t`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open SwarmMarks

namespace SwarmSpatial
noncomputable section

/-- Uniform running-maximum form of `spav`, conditional on the fluctuation input. -/
theorem spav_uniform_of_vanishes {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hfl : FluctuationVanishes p m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ n →
        |∑ k ∈ Finset.range t, hof p ω k - (t : ℝ) * targetParam p m| ≤ ε * n := by
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := (qpos hp2).le
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := qle_one hp1 hp2 (by omega)
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ (m - 1))) :=
    isProbabilityMeasure_boolMeasure hq0 hq1
  have hseq : ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Tendsto (fun n : ℕ =>
        ((∑ k ∈ Finset.range n, hof p ω k) - (n : ℝ) * targetParam p m) / n)
        atTop (nhds 0) := by
    filter_upwards [spav hp1 hp2 hm hfl] with ω hω
    have h1 : Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, hof p ω k - targetParam p m)
        atTop (nhds 0) := by
      simpa using hω.sub (tendsto_const_nhds (x := targetParam p m))
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  exact MartingaleLimit.tendsto_running_max
    (Q := fun t ω => (∑ k ∈ Finset.range t, hof p ω k) - (t : ℝ) * targetParam p m) hseq

/-- **Unconditional uniform projection estimate.**  Almost surely, for every `ε > 0`,
eventually every error in `∑_{k<t} h(k) - t * targetParam p m`, uniformly in `t ≤ n`,
is at most `εn`. -/
theorem spav_uniform {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ n →
        |∑ k ∈ Finset.range t, hof p ω k - (t : ℝ) * targetParam p m| ≤ ε * n :=
  spav_uniform_of_vanishes hp1 hp2 hm (fluctuationVanishes hp1 hp2 hm)

/-- The same unconditional estimate as a `Finset.sup'` running maximum. -/
theorem spav_uniform_sup' {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
          (fun t => |∑ k ∈ Finset.range t, hof p ω k - (t : ℝ) * targetParam p m|) ≤ ε * n := by
  filter_upwards [spav_uniform hp1 hp2 hm] with ω hω ε hε
  filter_upwards [hω ε hε] with n hn
  refine Finset.sup'_le _ _ ?_
  intro t ht
  exact hn t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))

end
end SwarmSpatial


