/-
  **The Borel--Cantelli summability behind Lemma `transience`.**

  `main_1d_revised.tex` (proof of Lemma `transience`) finishes with

      sum_{k >= 16} P(...) <= sum_{k >= 16} ((k+1)^4 + 1) e^{-c b_k} < inf,

  where `b_k = lvlB k = floor(k^{1/4}) - 1` and `c = paperC p q > 0`.  The inequality
  `P(...) <= ((k+1)^4 + 1) e^{-c b_k}` is the crossing estimate (eq. (cross) plus a union
  bound over `s <= (k+1)^4`); the summability of the right-hand side is purely analytic.
  That is the display the paper's Borel--Cantelli step consumes
  (`summable_poly_exp_lvlB_paper`), and this file also records an environment-side
  statement (`ae_summable_prod_decay`) in which the exponential is replaced by the actual
  block product:

  * `lvlB_lt_add_three_pow_four` : `k < (b_k + 3)^4`, i.e. `b_k >= k^{1/4} - 3`;
  * `summable_poly_exp_lvlB` : `Summable (fun k => ((k:ℝ)+1)^4 * exp (-c * b_k))` for `c > 0`;
  * `ae_summable_prod_decay` : almost surely the *environment products itself* are summable
    against the polynomial weight,
    `Summable (fun k => ((k:ℝ)+1)^4 * prod_{a_k < x <= b_k} rho_j(x))`,
    which is exactly the hypothesis `sum_k P(E_k) < inf` of the Borel--Cantelli step once the
    crossing probability is bounded by the product.

  Method for the analytic step: `isLittleO_log_rpow_atTop` gives
  `log x / x^{1/4} -> 0`, so eventually `6 log k <= c b_k`; then
  `exp (-c b_k) <= k^{-6}` and `((k+1)^4) k^{-6} <= 16 k^{-2}`, and
  `Real.summable_nat_pow_inv` finishes.  Summability is transferred across the finitely many
  exceptional indices with `summable_nat_add_iff`.  No extra hypothesis on `p, q` beyond the
  paper's; no unproved premise.
-/
import Swarm.Imports
import Swarm.ProdDecayBridge

open Filter Topology MeasureTheory
open scoped BigOperators Topology ENNReal

namespace SwarmLogRatio

noncomputable section

/-! ### The size of the paper's level -/

/-- **The paper's level is at least `k^{1/4}` up to an additive constant**: `k < (b_k+3)^4`. -/
lemma lvlB_lt_add_three_pow_four (k : ℕ) : k < (SwarmSpeed.lvlB k + 3) ^ 4 := by
  have h1 : k < (Nat.sqrt k + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt k
    simpa [pow_two] using this
  have h2 : Nat.sqrt k + 1 ≤ (Nat.sqrt (Nat.sqrt k) + 2) ^ 2 := by
    have h := Nat.lt_succ_sqrt (Nat.sqrt k)
    nlinarith
  have h3 : Nat.sqrt (Nat.sqrt k) + 2 ≤ SwarmSpeed.lvlB k + 3 := by
    unfold SwarmSpeed.lvlB
    omega
  have h4 : ((Nat.sqrt (Nat.sqrt k) + 2) ^ 2) ^ 2
      ≤ ((SwarmSpeed.lvlB k + 3) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) 2
  calc k < (Nat.sqrt k + 1) ^ 2 := h1
    _ ≤ ((Nat.sqrt (Nat.sqrt k) + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ ((SwarmSpeed.lvlB k + 3) ^ 2) ^ 2 := h4
    _ = (SwarmSpeed.lvlB k + 3) ^ 4 := by ring

/-- **`k^{1/4} < b_k + 3`** in the reals. -/
lemma rpow_quarter_lt_lvlB (k : ℕ) :
    (k : ℝ) ^ (1 / 4 : ℝ) < (SwarmSpeed.lvlB k : ℝ) + 3 := by
  have hnat := lvlB_lt_add_three_pow_four k
  have hcast : (k : ℝ) < ((SwarmSpeed.lvlB k : ℝ) + 3) ^ 4 := by
    have h : ((k : ℕ) : ℝ) < ((SwarmSpeed.lvlB k + 3 : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast hnat
    simpa [Nat.cast_add] using h
  have h := Real.rpow_lt_rpow (Nat.cast_nonneg k) hcast (by norm_num : (0 : ℝ) < 1 / 4)
  have hpow : (((SwarmSpeed.lvlB k : ℝ) + 3) ^ 4 : ℝ) ^ (1 / 4 : ℝ)
      = (SwarmSpeed.lvlB k : ℝ) + 3 := by
    rw [← Real.rpow_natCast ((SwarmSpeed.lvlB k : ℝ) + 3) 4,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (SwarmSpeed.lvlB k : ℝ) + 3)]
    norm_num
  rwa [hpow] at h

/-- `log x / x^{1/4} -> 0` (the logarithmic growth is slower than any positive power). -/
lemma tendsto_log_div_rpow_quarter :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero

/-! ### The analytic summability -/

/-- **`sum_k (k+1)^4 e^{-c b_k} < inf`** for `c > 0`, `b_k = floor(k^{1/4}) - 1`.

This is the summability in the last display of the proof of Lemma `transience`
(the polynomial factor `(k+1)^4` comes from the union bound over the times `s <= (k+1)^4`). -/
theorem summable_poly_exp_lvlB {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ 4 * Real.exp (-c * (SwarmSpeed.lvlB k : ℝ))) := by
  -- eventually `log k <= (c/12) k^{1/4}`
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x / x ^ (1 / 4 : ℝ) ≤ c / 12 :=
    tendsto_log_div_rpow_quarter.eventually (eventually_le_nhds (by positivity))
  have hle_nat : ∀ᶠ k : ℕ in atTop, Real.log (k : ℝ) ≤ (c / 12) * (k : ℝ) ^ (1 / 4 : ℝ) := by
    have hcomp : ∀ᶠ k : ℕ in atTop, Real.log (k : ℝ) / (k : ℝ) ^ (1 / 4 : ℝ) ≤ c / 12 :=
      tendsto_natCast_atTop_atTop.eventually hsmall
    filter_upwards [hcomp, eventually_ge_atTop (1 : ℕ)] with k hk hk1
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hp : (0 : ℝ) < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hk0 _
    rw [div_le_iff₀ hp] at hk
    exact hk
  -- hence eventually `6 log k <= c b_k`
  have hkey : ∀ᶠ k : ℕ in atTop, 6 * Real.log (k : ℝ) ≤ c * (SwarmSpeed.lvlB k : ℝ) := by
    have h3 : ∀ᶠ k : ℕ in atTop, 3 ≤ SwarmSpeed.lvlB k :=
      SwarmSpeed.tendsto_lvlB.eventually (eventually_ge_atTop 3)
    filter_upwards [hle_nat, h3] with k hk hk3
    have hr := (rpow_quarter_lt_lvlB k).le
    have hm : (3 : ℝ) ≤ (SwarmSpeed.lvlB k : ℝ) := by exact_mod_cast hk3
    nlinarith [hc]
  -- each term is eventually at most `16 / k^2`
  have hev : ∀ᶠ k : ℕ in atTop,
      ((k : ℝ) + 1) ^ 4 * Real.exp (-c * (SwarmSpeed.lvlB k : ℝ))
        ≤ 16 * ((k : ℝ) ^ 2)⁻¹ := by
    filter_upwards [hkey, eventually_ge_atTop (1 : ℕ)] with k hk hk1
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hexp : Real.exp (-c * (SwarmSpeed.lvlB k : ℝ)) ≤ ((k : ℝ) ^ 6)⁻¹ := by
      have h2 : -c * (SwarmSpeed.lvlB k : ℝ) ≤ -(6 * Real.log (k : ℝ)) := by linarith
      calc Real.exp (-c * (SwarmSpeed.lvlB k : ℝ))
          ≤ Real.exp (-(6 * Real.log (k : ℝ))) := Real.exp_le_exp.mpr h2
        _ = ((Real.exp (Real.log (k : ℝ))) ^ 6)⁻¹ := by
            rw [show -(6 * Real.log (k : ℝ)) = -(((6 : ℕ) : ℝ) * Real.log (k : ℝ)) by
              push_cast; ring]
            rw [Real.exp_neg, Real.exp_nat_mul]
        _ = ((k : ℝ) ^ 6)⁻¹ := by rw [Real.exp_log hk0]
    have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by positivity
    have h6 : (0 : ℝ) ≤ ((k : ℝ) ^ 6)⁻¹ := by positivity
    have hlin : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by linarith
    have hquart : ((k : ℝ) + 1) ^ 4 ≤ 16 * (k : ℝ) ^ 4 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hlin 4
      calc ((k : ℝ) + 1) ^ 4 ≤ (2 * (k : ℝ)) ^ 4 := h
        _ = 16 * (k : ℝ) ^ 4 := by ring
    calc ((k : ℝ) + 1) ^ 4 * Real.exp (-c * (SwarmSpeed.lvlB k : ℝ))
        ≤ ((k : ℝ) + 1) ^ 4 * ((k : ℝ) ^ 6)⁻¹ := mul_le_mul_of_nonneg_left hexp hpos
      _ ≤ (16 * (k : ℝ) ^ 4) * ((k : ℝ) ^ 6)⁻¹ :=
          mul_le_mul_of_nonneg_right hquart h6
      _ = 16 * ((k : ℝ) ^ 2)⁻¹ := by
          field_simp
  -- the comparison series is summable
  have hsum2 : Summable (fun k : ℕ => 16 * ((k : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num) |>.mul_left 16
  -- shift past the finitely many exceptional indices
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  have hshift : Summable (fun n : ℕ =>
      (((n + K : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-c * (SwarmSpeed.lvlB (n + K) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_nat_add_iff K).mpr hsum2)
    · exact mul_nonneg (by positivity) (by positivity)
    · exact hK (n + K) (by omega)
  exact (summable_nat_add_iff K).mp hshift

/-- The paper's exact summand: `sum_k ((k+1)^4 + 1) e^{-c b_k} < inf` for `c > 0`. -/
theorem summable_poly_exp_lvlB_paper {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ =>
      (((k : ℝ) + 1) ^ 4 + 1) * Real.exp (-c * (SwarmSpeed.lvlB k : ℝ))) := by
  have h := summable_poly_exp_lvlB (c := c) hc
  have h2 : Summable (fun k : ℕ =>
      2 * (((k : ℝ) + 1) ^ 4 * Real.exp (-c * (SwarmSpeed.lvlB k : ℝ)))) :=
    h.mul_left 2
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h2
  · have := Real.exp_pos (-c * (SwarmSpeed.lvlB k : ℝ))
    have h0 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by positivity
    nlinarith [h0, this.le]
  · have hexp : (0:ℝ) < Real.exp (-c * (SwarmSpeed.lvlB k : ℝ)) := Real.exp_pos _
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := by
      have h0 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ ((k : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h0 4
    nlinarith [hexp, h1]

/-! ### Almost-sure summability of the actual environment products -/

/-- **The environment side of the Borel--Cantelli step of Lemma `transience`.**  Almost surely,
with the paper's parameters `1/2 < p < 1`, `0 < q <= 1`, the block products of the site ratios
are summable against the polynomial weight:

`Summable (fun k => ((k:ℝ)+1)^4 * prod_{a_k < x <= b_k} rho_j(x))`.

The crossing estimate bounds `P(E_k | F_s)` by such a product; this statement says the
weighted products are a.s. summable, i.e. the environment side of the Borel--Cantelli
budget is finite.  (For `sum_k P(E_k) < inf` itself one still takes expectations; the
paper instead restricts `E_k` to the good event `{prod <= e^{-c b_k}}`, which turns the
crossing estimate into the *deterministic* bound `((k+1)^4+1) e^{-c b_k}` summed by
`summable_poly_exp_lvlB_paper`.) -/
theorem ae_summable_prod_decay {q p : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : 0 < q)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure q)),
      Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 *
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω x)) := by
  have hc : 0 < paperC p q := paperC_pos hq hp1 hp2
  have hp0 : 0 < p := by linarith
  have hsum := summable_poly_exp_lvlB hc
  filter_upwards [ae_prod_decay_eventually (q := q) (p := p) hq0 hq1 hq hp1 hp2] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  have hshift : Summable (fun n : ℕ => (((n + K : ℕ) : ℝ) + 1) ^ 4 *
      ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA (n + K)) (SwarmSpeed.lvlB (n + K)),
          SwarmSpatial.rhoOf p (ω x)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_nat_add_iff K).mpr hsum)
    · exact mul_nonneg (by positivity)
        (Finset.prod_nonneg (fun x _ => (rhoOf_pos hp0 hp2 (ω x)).le))
    · exact mul_le_mul_of_nonneg_left (hK (n + K) (by omega)) (by positivity)
  exact (summable_nat_add_iff K).mp hshift

/-- The same at the paper's parameters `q = (1-p)^{m-1}`, `m >= 2`. -/
theorem ae_summable_prod_decay_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))),
      Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 *
        ∏ x ∈ Finset.Ioc (SwarmSpeed.lvlA k) (SwarmSpeed.lvlB k),
            SwarmSpatial.rhoOf p (ω x)) := by
  have hqp : 0 < (1 - p) ^ (m - 1) := SwarmSpatial.q_paper_pos hp2
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := le_of_lt (SwarmSpatial.q_paper_lt_one hp1 hp2 hm)
  exact ae_summable_prod_decay (le_of_lt hqp) hq1 hqp hp1 hp2

end

end SwarmLogRatio
