/-
  **Bridge: the exact log-ratio strong law feeds `ProdDecay`.**

  `Swarm/ProdDecay.lean` proves the deterministic step

      Cesaro limit `psum L n / n -> -4c`,  `a_k/b_k -> 1/2`
        ==> `prod_{a_k < x <= b_k} exp (L x) <= exp (-c b_k)` eventually,

  and supplies the paper's levels `lvlA k / lvlB k -> 1/2`, but takes the Cesaro limit
  as a hypothesis `hL`.  This file discharges `hL` for the actual i.i.d. site marks
  using `SwarmLogRatio.tendsto_avg_logRho`, with `L x = log rho_j(x)` and
  `c = paperC p q = -(q log((1-p)/p))/4`, and therefore obtains the paper's display
  `prod_{a_k < x <= b_k} rho_j(x) <= e^{-c b_k}` almost surely, for the paper's
  parameter choice `q = (1-p)^{m-1}` and any `m >= 2`, `1/2 < p < 1`.

  The Borel--Cantelli summability of the resulting bound is proved separately in
  `BCSummable.lean` (`summable_poly_exp_lvlB_paper`).  This file does *not* claim
  Lemma `transience`: the remaining input there is the stopped crossing probability
  of eq. (cross), i.e. target A/B of the campaign.  What is removed here is one named
  hypothesis of the paper's argument (`hL` of `ProdDecay.block_sum_decay`).
-/
import Swarm.Imports
import Swarm.LogRatioSLLN
import Swarm.MarkN
import Swarm.ProdDecay

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace SwarmLogRatio

noncomputable section

/-- **The Cesaro hypothesis of `block_sum_decay`, discharged**, in the exact `psum`
shape used by `SwarmSpeed`: almost surely,
`(1/r) sum_{x<r} log rho_j(x) -> q log((1-p)/p)`. -/
theorem ae_tendsto_psum_logRho {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Tendsto
        (fun n : ℕ =>
          SwarmSpeed.psum (fun x => Real.log (SwarmSpatial.rhoOf p (ω x))) n / n)
        atTop (𝓝 (q * Real.log ((1 - p) / p))) := by
  filter_upwards [tendsto_avg_logRho (q := q) h0 h1 p] with ω hω
  simpa [SwarmSpeed.psum] using hω

/-- The same, in the `-4 c` form required by `prod_decay_paper_levels`, for the
paper's constant `c = paperC p q`. -/
theorem ae_tendsto_psum_logRho_paperC {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Tendsto
        (fun n : ℕ =>
          SwarmSpeed.psum (fun x => Real.log (SwarmSpatial.rhoOf p (ω x))) n / n)
        atTop (𝓝 (-4 * paperC p q)) := by
  filter_upwards [ae_tendsto_psum_logRho (q := q) (p := p) h0 h1] with ω hω
  rwa [neg_four_paperC]

/-- **The paper's product display `prod_{a_k < x <= b_k} rho_j(x) <= e^{-c b_k}`,
almost surely, with the paper's levels `a_k = floor(b_k/2)`, `b_k = floor(k^{1/4}) - 1`.**

This is the deterministic conclusion of the strong law; it is the input to the
Borel--Cantelli step of Lemma `transience`, and it is now unconditional in the site
marks (the only assumptions are the paper's `1/2 < p < 1` and `0 < q <= 1`). -/
theorem ae_prod_decay_eventually {q p : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : 0 < q)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω x)
          ≤ Real.exp (-(paperC p q) * (SwarmSpeed.lvlB k : ℝ)) := by
  have hc : 0 < paperC p q := paperC_pos hq hp1 hp2
  have hp0 : 0 < p := by linarith
  filter_upwards [ae_tendsto_psum_logRho_paperC (q := q) (p := p) hq0 hq1] with ω hω
  filter_upwards [SwarmSpeed.prod_decay_paper_levels hc hω] with k hk
  have hprod : ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
        SwarmSpatial.rhoOf p (ω x)
      = ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
          Real.exp (Real.log (SwarmSpatial.rhoOf p (ω x))) :=
    Finset.prod_congr rfl (fun x _ => (Real.exp_log (rhoOf_pos hp0 hp2 (ω x))).symm)
  rw [hprod]
  exact hk

/-- **The paper's parameters**: `q = (1-p)^{m-1}` for `m >= 2`, `1/2 < p < 1`.  The
product of the site ratios over the block `(a_k, b_k]` decays like `e^{-c b_k}` almost
surely, with `c = paperC p ((1-p)^{m-1}) > 0`. -/
theorem ae_prod_decay_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))),
      ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω x)
          ≤ Real.exp (-(paperC p ((1 - p) ^ (m - 1))) * (SwarmSpeed.lvlB k : ℝ)) := by
  have hqp : 0 < (1 - p) ^ (m - 1) := SwarmSpatial.q_paper_pos hp2
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 :=
    le_of_lt (SwarmSpatial.q_paper_lt_one hp1 hp2 hm)
  exact ae_prod_decay_eventually (le_of_lt hqp) hq1 hqp hp1 hp2

/-- The constant of the paper's display is positive at the paper's marks:
`0 < paperC p ((1-p)^{m-1})`, for every `m` (only `q = (1-p)^{m-1} > 0` is used). -/
theorem paperC_paper_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} :
    0 < paperC p ((1 - p) ^ (m - 1)) :=
  paperC_pos (SwarmSpatial.q_paper_pos hp2) hp1 hp2

/-! ### Simultaneously for the `N` walkers' mark families -/

/-- **The log-ratio strong law simultaneously for the `N` walkers.**  Under the joint law
`markMeasureN N (boolMeasure q)` of the paper's `N` independent mark families `B_1, …, B_N`,
one single almost-sure event carries the convergence of every walker's average.  This is the
form in which the estimate is used: the null set must not depend on the walker index. -/
theorem tendsto_avg_logRho_N {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (N : ℕ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure q)),
      ∀ j : Fin N,
        Tendsto
          (fun r : ℕ => (∑ x ∈ Finset.range r, Real.log (SwarmSpatial.rhoOf p (ω j x))) / r)
          atTop (𝓝 (q * Real.log ((1 - p) / p))) := by
  haveI : IsProbabilityMeasure (SwarmMarks.boolMeasure q) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure h0 h1
  refine (ae_all_iff (μ := SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure q))
    (ι := Fin N)).mpr (fun j => ?_)
  exact SwarmMarks.markMeasureN_ae N j (tendsto_avg_logRho (q := q) h0 h1 p)

/-- **The paper's product display simultaneously for the `N` walkers**, with one common
almost-sure event: for `1/2 < p < 1` and `0 < q <= 1`, almost surely every walker's own
site ratios over `(a_k, b_k]` decay like `e^{-c b_k}` with the same constant
`c = paperC p q > 0`. -/
theorem ae_prod_decay_eventually_N {q p : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : 0 < q)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (N : ℕ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure q)),
      ∀ j : Fin N, ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω j x)
          ≤ Real.exp (-(paperC p q) * (SwarmSpeed.lvlB k : ℝ)) := by
  haveI : IsProbabilityMeasure (SwarmMarks.boolMeasure q) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure hq0 hq1
  have hsingle := ae_prod_decay_eventually (q := q) (p := p) hq0 hq1 hq hp1 hp2
  have h1 : ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure q)),
      ∀ j : Fin N, ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω j x)
          ≤ Real.exp (-(paperC p q) * (SwarmSpeed.lvlB k : ℝ)) :=
    (ae_all_iff (μ := SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure q))
      (ι := Fin N)).mpr (fun j => SwarmMarks.markMeasureN_ae N j hsingle)
  filter_upwards [h1] with ω hω
  exact hω

/-- The paper's parameters, simultaneously in `N`: with `q = (1-p)^{m-1}`, `m >= 2`,
`1/2 < p < 1`, one almost-sure event of `markMeasureN N (boolMeasure ((1-p)^{m-1}))` carries
the product decay for all `N` walkers. -/
theorem ae_prod_decay_paper_N {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))),
      ∀ j : Fin N, ∀ᶠ k : ℕ in atTop,
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω j x)
          ≤ Real.exp (-(paperC p ((1 - p) ^ (m - 1))) * (SwarmSpeed.lvlB k : ℝ)) := by
  have hqp : 0 < (1 - p) ^ (m - 1) := SwarmSpatial.q_paper_pos hp2
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := le_of_lt (SwarmSpatial.q_paper_lt_one hp1 hp2 hm)
  exact ae_prod_decay_eventually_N (le_of_lt hqp) hq1 hqp hp1 hp2 N

end

end SwarmLogRatio
