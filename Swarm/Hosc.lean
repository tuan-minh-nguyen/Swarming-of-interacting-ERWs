/-
  Direction (E): from a bounded-increment drift-martingale maximal bound to
  the oscillation statement `max(M - X) = o(n)` (paper: `(prelim)`, second part of
  Lemma `transience`), which is the `hosc` premise of the verified covering argument
  `SwarmSpeed.speed_lower_bound`.

  The mathematical content of this file:

  If `u` is an integer path, `M` a real martingale with `M_0 = 0`, and the drift
  accumulator `E` is monotone with `u_n = M_n + c E_n` (`c >= 0`), then for `t <= n`

      u_t - u_n = (M_t - M_n) + c (E_t - E_n) <= M_t - M_n <= |M_t| + |M_n|,

  so the running maximum exceeds the current position by at most twice the running
  maximum of `|M|`.  Hence `max_{t<=n}(u_t - u_n) <= 2 max_{t<=n} |M_t|`, and the
  paper's `max(M^i_t) - X^i_t = o(n)` follows from `max_{t<=n} |M_t| = o(n)`
  (supplied for bounded-increment martingales by `MartingaleLimit.martingale_strong_law`
  and `MartingaleLimit.tendsto_running_max`).

  Nothing here is probabilistic beyond the `o(n)` input: it is the deterministic
  inequality chain the paper writes as "the first `k` terms contribute `O(1)`".
-/
import Swarm.Imports
import Swarm.Speed
import Swarm.MartingaleLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

namespace SwarmHosc

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Deterministic core: the running maximum is within `2 max |M|` of the position -/

/-- **`hosc` from a drift decomposition and a maximal `o(n)` bound.**

`u` is an integer path, `M` the drift martingale, `E` a monotone step counter, and
`u_n = M_n + c E_n` with `c >= 0`.  If `max_{t<=n} |M_t| <= eps n` eventually for every
`eps > 0`, then `(max_{t<=n} u_t - u_n)/n -> 0`. -/
theorem hosc_pointwise {u : ℕ → ℤ} {M : ℕ → ℝ} {E : ℕ → ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hrepr : ∀ n, (u n : ℝ) = M n + c * (E n : ℝ))
    (hmono : Monotone E)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t ≤ n, |M t| ≤ ε * n) :
    Tendsto (fun n => ((SwarmSpeed.runMax u n : ℝ) - (u n : ℝ)) / n) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr (fun δ hδ => ?_)
  have hε : (0 : ℝ) < δ / 4 := by linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hmax (δ / 4) hε)
  refine ⟨max N₁ ⌈4 / δ⌉₊, fun n hn => ?_⟩
  have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hceiln : ⌈4 / δ⌉₊ ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : 1 ≤ ⌈4 / δ⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
    have h2 : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans h1 hceiln)
    exact_mod_cast h2
  -- the key pointwise inequality: `u t - u n <= |M t| + |M n|`
  have hkey : ∀ t ≤ n, (u t : ℝ) ≤ (u n : ℝ) + δ / 2 * (n : ℝ) := by
    intro t ht
    have hMt := hN₁ n hN₁n t ht
    have hMn := hN₁ n hN₁n n le_rfl
    have hmono' : (E t : ℝ) ≤ (E n : ℝ) := by exact_mod_cast hmono ht
    have hrepr_t := hrepr t
    have hrepr_n := hrepr n
    have hEt : c * (E t : ℝ) ≤ c * (E n : ℝ) := mul_le_mul_of_nonneg_left hmono' hc
    have h1 : M t ≤ |M t| := le_abs_self _
    have h2 : -|M n| ≤ M n := neg_abs_le _
    have h3 : |M t| ≤ δ / 4 * (n : ℝ) := hMt
    have h4 : |M n| ≤ δ / 4 * (n : ℝ) := hMn
    rw [hrepr_t, hrepr_n]
    nlinarith
  -- integer form
  set K : ℕ := ⌈δ / 2 * (n : ℝ)⌉₊ with hK
  have hKle : δ / 2 * (n : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hInt : ∀ t ≤ n, u t ≤ u n + (K : ℤ) := by
    intro t ht
    have h1 : ((u t : ℤ) : ℝ) ≤ ((u n + (K : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith [hkey t ht, hKle]
    exact_mod_cast h1
  have hrun : SwarmSpeed.runMax u n ≤ u n + (K : ℤ) := SwarmSpeed.runMax_le hInt
  have hrunR : (SwarmSpeed.runMax u n : ℝ) ≤ (u n : ℝ) + (δ / 2 * (n : ℝ) + 1) := by
    have h1 : ((SwarmSpeed.runMax u n : ℤ) : ℝ) ≤ ((u n + (K : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hrun
    have h2 : (K : ℝ) < δ / 2 * (n : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ δ / 2 * (n : ℝ) := by positivity
      exact Nat.ceil_lt_add_one h0
    push_cast at h1
    linarith
  have hlow : (0 : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) - (u n : ℝ) := by
    have h1 : u n ≤ SwarmSpeed.runMax u n := SwarmSpeed.le_runMax le_rfl
    have h2 : (u n : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) := by exact_mod_cast h1
    linarith
  have hinv : 1 / (n : ℝ) ≤ δ / 4 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : 4 / δ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hceiln)
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  have hinv2 : (1 : ℝ) ≤ δ / 4 * (n : ℝ) := by
    rw [div_le_iff₀ hnpos] at hinv
    linarith
  have hbound : ((SwarmSpeed.runMax u n : ℝ) - (u n : ℝ)) / n ≤ 3 * δ / 4 := by
    rw [div_le_iff₀ hnpos]
    nlinarith [hrunR, hinv2]
  have hnn : (0 : ℝ) ≤ ((SwarmSpeed.runMax u n : ℝ) - (u n : ℝ)) / n := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-! ### Maximal `o(n)` bound for bounded-increment martingales -/

/-- **`max_{t<=n} |Q_t| = o(n)`** for a martingale started at `0` whose increments are
uniformly bounded.  Combination of the Hall–Heyde strong law
(`MartingaleLimit.martingale_strong_law`) with the running-maximum upgrade
(`MartingaleLimit.tendsto_running_max`). -/
theorem ae_max_div_of_bounded_inc [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ m0} (hQ : Martingale Q ℱ μ) (hQ0 : ∀ ω, Q 0 ω = 0)
    {C : ℝ} (_hCnn : 0 ≤ C) (hC : ∀ n ω, |MartingaleLimit.inc Q n ω| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t ≤ n, |Q t ω| ≤ ε * n := by
  -- square integrability of the increments
  have hsqi : ∀ k : ℕ, Integrable (fun ω => (MartingaleLimit.inc Q k ω) ^ 2) μ := by
    intro k
    have hmeas : AEStronglyMeasurable (fun ω => (MartingaleLimit.inc Q k ω) ^ 2) μ :=
      (MartingaleLimit.integrable_inc hQ k).aestronglyMeasurable.pow 2
    refine Integrable.of_bound hmeas (C ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h3 : |MartingaleLimit.inc Q k ω| ^ 2 ≤ |C| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (le_trans (hC k ω) (le_abs_self C)) 2
    rwa [sq_abs, sq_abs] at h3
  -- the weighted variance series is summable
  have hsum : Summable fun k : ℕ =>
      (((k : ℝ) + 1)⁻¹) ^ 2 * ∫ ω, (MartingaleLimit.inc Q k ω) ^ 2 ∂μ := by
    have hmaj : Summable fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 2 * C ^ 2 := by
      have hbase : Summable fun k : ℕ => (((k : ℝ) + 1)⁻¹) ^ 2 := by
        have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num : (1 : ℝ) < 2)
        refine h.congr fun k => ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), Real.rpow_two, one_div,
          ← inv_pow]
      have := hbase.mul_left (C ^ 2)
      exact this.congr fun k => by ring
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
    · refine mul_nonneg (by positivity) (integral_nonneg fun ω => sq_nonneg _)
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hC' : ∀ ω, |MartingaleLimit.inc Q k ω| ≤ C := hC k
      have hle : ∫ ω, (MartingaleLimit.inc Q k ω) ^ 2 ∂μ ≤ ∫ _ : Ω, C ^ 2 ∂μ := by
        refine integral_mono (hsqi k) (integrable_const (C ^ 2)) (fun ω => ?_)
        have h3 : |MartingaleLimit.inc Q k ω| ^ 2 ≤ |C| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (le_trans (hC' ω) (le_abs_self C)) 2
        rwa [sq_abs, sq_abs] at h3
      simpa using hle
  have hae := MartingaleLimit.martingale_strong_law hQ hsqi hsum
  have hzero : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω / n) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    refine hω.congr' ?_
    filter_upwards with n
    rw [hQ0 ω]
    simp
  exact MartingaleLimit.tendsto_running_max hzero

/-- **`hosc` for a path with a bounded-increment drift martingale.**  Composition of the
deterministic core with the maximal bound. -/
theorem ae_hosc_of_martingale [IsProbabilityMeasure μ] {u : ℕ → Ω → ℤ}
    {M : ℕ → Ω → ℝ} {E : ℕ → Ω → ℕ} {ℱ : Filtration ℕ m0} {c : ℝ}
    (hM : Martingale M ℱ μ) (hM0 : ∀ ω, M 0 ω = 0)
    {C : ℝ} (hCnn : 0 ≤ C) (hC : ∀ n ω, |MartingaleLimit.inc M n ω| ≤ C)
    (hc : 0 ≤ c) (hrepr : ∀ n ω, (u n ω : ℝ) = M n ω + c * (E n ω : ℝ))
    (hmono : ∀ t n ω, t ≤ n → E t ω ≤ E n ω) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => ((SwarmSpeed.runMax (fun t => u t ω) n : ℝ) - (u n ω : ℝ)) / n) atTop (𝓝 0) := by
  have hmax := ae_max_div_of_bounded_inc (μ := μ) hM hM0 hCnn hC
  filter_upwards [hmax] with ω hω
  exact hosc_pointwise hc (fun n => hrepr n ω) (fun t n ht => hmono t n ω ht) hω

end SwarmHosc
