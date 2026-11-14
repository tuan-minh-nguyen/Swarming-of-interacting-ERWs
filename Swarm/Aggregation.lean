/-
  The **Borel--Cantelli half of the no-bad-time condition** of Lemma `transience`
  (`main_1d_revised.tex`, §2.2, step (2) of the proof).

  `Main.ae_transience_of_no_bad_times` reduces transience of walker `i` to the pathwise
  statement that, above some level `K`, no time `s <= (k+1)^4` is a bad time.  This file
  proves that statement from a *numerical* input only: the crossing estimate eq. (cross)
  integrated out of the conditional expectation, i.e. for each level `k` and each
  deterministic time `s`,

    `P(bad time at (k,s)) <= exp(-c b_k)`   (`c > 0` arbitrary).

  The union bound over the `(k+1)^4 + 1` times and Borel--Cantelli then give the
  no-bad-time condition, because `sum_k (k+1)^4 exp(-c b_k) < infinity`: `b_k` grows like
  `k^{1/4}`, so the exponential beats the polynomial factor.  That summability is proved
  here (`summable_lvlB_exp`), it is not assumed.

  Consequently `ae_transience_of_crossing_bound` proves Lemma `transience` for the actual
  interacting trajectory from the crossing estimate alone.
-/
import Swarm.Transience.Main

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators Topology

namespace SwarmDischarge

open SwarmSpeed

/-! ### The analytic tail bound -/

/-- `Nat.sqrt m` is within one of the real square root: `sqrt m - 1 < Nat.sqrt m`. -/
theorem sqrt_sub_one_lt_natSqrt (m : ℕ) : Real.sqrt (m : ℝ) - 1 < (Nat.sqrt m : ℝ) := by
  have hlt : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' m
    have h' : (m : ℝ) < (((Nat.sqrt m + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : Real.sqrt (m : ℝ) < (Nat.sqrt m : ℝ) + 1 := by
    have h2 : Real.sqrt (m : ℝ) < Real.sqrt (((Nat.sqrt m : ℝ) + 1) ^ 2) :=
      Real.sqrt_lt_sqrt h0 hlt
    rwa [Real.sqrt_sq (by positivity)] at h2
  linarith

/-- **The level `b_k = floor(k^{1/4}) - 1` is comparable to `k^{1/4}`.**  For `k >= 4096`,
`b_k >= sqrt(sqrt k)/4`. -/
theorem lvlB_ge_quarter (k : ℕ) (hk : 4096 ≤ k) :
    Real.sqrt (Real.sqrt (k : ℝ)) / 4 ≤ (lvlB k : ℝ) := by
  have hk4096 : (4096 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  set S : ℝ := (Nat.sqrt k : ℝ) with hS
  set b1 : ℝ := (Nat.sqrt (Nat.sqrt k) : ℝ) with hb1
  -- `u = sqrt (sqrt k)`, so `u^2 = sqrt k` and `u^4 = k`
  set u : ℝ := Real.sqrt (Real.sqrt (k : ℝ)) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = Real.sqrt (k : ℝ) := by
    rw [hu]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu4 : u ^ 4 = (k : ℝ) := by
    have h : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [h, hu2, Real.sq_sqrt hk0]
  have hu8 : u ≥ 8 := by
    have h1 : Real.sqrt (4096 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hk4096
    have h2 : Real.sqrt (4096 : ℝ) = 64 := by
      have : (4096 : ℝ) = 64 ^ 2 := by norm_num
      rw [this, Real.sqrt_sq (by norm_num)]
    have h3 : Real.sqrt (64 : ℝ) ≤ Real.sqrt (Real.sqrt (k : ℝ)) := by
      rw [← h2]
      exact Real.sqrt_le_sqrt h1
    have h4 : Real.sqrt (64 : ℝ) = 8 := by
      have : (64 : ℝ) = 8 ^ 2 := by norm_num
      rw [this, Real.sqrt_sq (by norm_num)]
    rw [hu]
    rw [← h4]
    exact h3
  -- `S` dominates `sqrt k / 2`
  have hS1 : Real.sqrt (k : ℝ) - 1 < S := by
    rw [hS]; exact sqrt_sub_one_lt_natSqrt k
  have hsqrtk2 : (2 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have : (2 : ℝ) ^ 2 ≤ (k : ℝ) := by norm_num; linarith
    calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := by
          rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt this
  have hS2 : Real.sqrt (k : ℝ) / 2 < S := by linarith
  -- hence `b1 = Nat.sqrt (Nat.sqrt k)` dominates `u / 2`
  have hb11 : Real.sqrt S - 1 < b1 := by
    rw [hb1]; exact sqrt_sub_one_lt_natSqrt (Nat.sqrt k)
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2le : Real.sqrt 2 ≤ 2 := by
    have : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  have hstep : Real.sqrt (Real.sqrt (k : ℝ) / 2) < Real.sqrt S := by
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    exact hS2
  have hsplit : Real.sqrt (Real.sqrt (k : ℝ) / 2) = u / Real.sqrt 2 := by
    rw [Real.sqrt_div (Real.sqrt_nonneg _), hu]
  have hu2' : u / 2 < Real.sqrt S := by
    have hle : u / 2 ≤ u / Real.sqrt 2 :=
      div_le_div_of_nonneg_left hu0 (by norm_num) hsqrt2le
    linarith [hstep, hsplit]
  have hub : u / 4 + 1 ≤ b1 := by
    have : u / 4 + 1 ≤ u / 2 - 1 := by linarith
    linarith
  -- cast the level back
  have hb1ge : 1 ≤ Nat.sqrt (Nat.sqrt k) := by
    have h8 : (1 : ℝ) ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
      rw [← hb1]
      linarith [hub, hu8]
    exact_mod_cast h8
  have hcast : (lvlB k : ℝ) = b1 - 1 := by
    have : lvlB k = Nat.sqrt (Nat.sqrt k) - 1 := rfl
    rw [this, Nat.cast_sub hb1ge, Nat.cast_one]
  rw [hcast]
  linarith

/-- **The polynomial factor is summable against the exponential decay of `b_k`.**
For `c > 0`, `sum_k ((k+1)^4 + 1) * exp(-c b_k) < infinity`. -/
theorem summable_lvlB_exp {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 4 + 1) * Real.exp (-(c * (lvlB k : ℝ)))) := by
  set C : ℝ := 17 * (((24 : ℕ).factorial) : ℝ) / (c / 4) ^ 24 with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]; positivity
  have hg : Summable (fun k : ℕ => C * (1 / (k : ℝ) ^ 2)) :=
    ((Real.summable_one_div_nat_pow).mpr (by norm_num : 1 < 2)).mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 4096] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℕ) ≤ k := le_trans (by norm_num) hk
    exact_mod_cast this
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  set u : ℝ := Real.sqrt (Real.sqrt (k : ℝ)) with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 hk0)
  have hu2 : u ^ 2 = Real.sqrt (k : ℝ) := by
    rw [hu]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu4 : u ^ 4 = (k : ℝ) := by
    have h : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [h, hu2, Real.sq_sqrt hk0.le]
  have hlv : u / 4 ≤ (lvlB k : ℝ) := lvlB_ge_quarter k hk
  -- exponential comparison
  have hexp_le : Real.exp (-(c * (lvlB k : ℝ))) ≤ Real.exp (-(c * u / 4)) := by
    apply Real.exp_le_exp.2
    nlinarith [hlv, hc]
  have hnum : (0 : ℝ) < c * u / 4 := by positivity
  have hfact := Real.pow_div_factorial_le_exp (c * u / 4) hnum.le 24
  -- `exp(-x) <= 24! / x^24`
  have hexp_bound : Real.exp (-(c * u / 4)) ≤ ((24 : ℕ).factorial : ℝ) / (c * u / 4) ^ 24 := by
    rw [Real.exp_neg]
    rw [show (((24 : ℕ).factorial : ℝ)) / (c * u / 4) ^ 24
        = 1 / ((c * u / 4) ^ 24 / ((24 : ℕ).factorial : ℝ)) from by
      rw [div_div_eq_mul_div, one_mul]]
    simpa using one_div_le_one_div_of_le (by positivity) hfact
  have hk4 : (k : ℝ) ^ 4 = u ^ 16 := by rw [← hu4]; ring
  have hk2 : (k : ℝ) ^ 2 = u ^ 8 := by rw [← hu4]; ring
  -- the product is `<= (24! / (c/4)^24) / k^2`
  have hmain : (k : ℝ) ^ 4 * Real.exp (-(c * u / 4))
      ≤ (((24 : ℕ).factorial : ℝ) / (c / 4) ^ 24) * (1 / (k : ℝ) ^ 2) := by
    have h1 : (k : ℝ) ^ 4 * Real.exp (-(c * u / 4))
        ≤ u ^ 16 * (((24 : ℕ).factorial : ℝ) / (c * u / 4) ^ 24) := by
      rw [hk4]
      exact mul_le_mul_of_nonneg_left hexp_bound (by positivity)
    have h2 : u ^ 16 * (((24 : ℕ).factorial : ℝ) / (c * u / 4) ^ 24)
        = (((24 : ℕ).factorial : ℝ) / (c / 4) ^ 24) * (1 / u ^ 8) := by
      rw [div_mul_div_comm, mul_one, ← mul_div_assoc]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      rw [show (c * u / 4) ^ 24 = (c / 4) ^ 24 * u ^ 24 by ring]
      ring
    have h3 : (1 : ℝ) / u ^ 8 = 1 / (k : ℝ) ^ 2 := by rw [hk2]
    rw [h2, h3] at h1
    exact h1
  have hpoly : ((k : ℝ) + 1) ^ 4 + 1 ≤ 17 * (k : ℝ) ^ 4 := by
    have h2 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by linarith
    have h3 : ((k : ℝ) + 1) ^ 4 ≤ (2 * (k : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
    have h4 : (2 * (k : ℝ)) ^ 4 = 16 * (k : ℝ) ^ 4 := by ring
    have h5 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := by
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hk1 4
    linarith
  have hnonneg : (0 : ℝ) ≤ (((k : ℝ) + 1) ^ 4 + 1) * Real.exp (-(c * (lvlB k : ℝ))) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc (((k : ℝ) + 1) ^ 4 + 1) * Real.exp (-(c * (lvlB k : ℝ)))
      ≤ (17 * (k : ℝ) ^ 4) * Real.exp (-(c * u / 4)) := by
        apply mul_le_mul hpoly hexp_le (Real.exp_pos _).le (by positivity)
    _ = 17 * ((k : ℝ) ^ 4 * Real.exp (-(c * u / 4))) := by ring
    _ ≤ 17 * ((((24 : ℕ).factorial : ℝ) / (c / 4) ^ 24) * (1 / (k : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = C * (1 / (k : ℝ) ^ 2) := by
        rw [hCdef]; ring

/-! ### Union bound and Borel--Cantelli -/

/-- **No bad time above level `K`, almost surely**, from the crossing estimate in the
integrated form `P(bad time at (k,s)) <= exp(-c b_k)`, with an extra event `Extra k` carried
along (this is the shape eq. (cross) actually delivers, see
`ae_eventually_no_bad_times_of_factored_bound`). -/
theorem ae_eventually_not_bad_inter {N : ℕ} {p : ℝ} (m : ℕ) (a b : Fin N) {K : ℕ} {c : ℝ}
    (hc : 0 < c) (Extra : ℕ → Set (Array N))
    (hcross : ∀ k ≥ K, ∀ s : ℕ,
      (arrayMeasure N) ({U : Array N | BadTime p m U a b k s} ∩ Extra k)
        ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop,
      ∀ s ≤ (k + 1) ^ 4, ¬ (BadTime p m U a b k s ∧ U ∈ Extra k) := by
  classical
  have hshift : Summable (fun j : ℕ =>
      ((((j + K : ℕ) : ℝ) + 1) ^ 4 + 1) * Real.exp (-(c * (lvlB (j + K) : ℝ)))) :=
    (summable_nat_add_iff K).mpr (summable_lvlB_exp hc)
  have hbnd : ∀ j : ℕ, (arrayMeasure N)
      (⋃ s ∈ Finset.range (((j + K) + 1) ^ 4 + 1),
        ({U : Array N | BadTime p m U a b (j + K) s} ∩ Extra (j + K)))
      ≤ ENNReal.ofReal (((((j + K : ℕ) : ℝ) + 1) ^ 4 + 1)
        * Real.exp (-(c * (lvlB (j + K) : ℝ)))) := by
    intro j
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hsum : ∑ s ∈ Finset.range (((j + K) + 1) ^ 4 + 1),
          (arrayMeasure N) ({U : Array N | BadTime p m U a b (j + K) s} ∩ Extra (j + K))
        ≤ ∑ _s ∈ Finset.range (((j + K) + 1) ^ 4 + 1),
          ENNReal.ofReal (Real.exp (-(c * (lvlB (j + K) : ℝ)))) :=
      Finset.sum_le_sum fun s _ => hcross (j + K) (Nat.le_add_left K j) s
    refine le_trans hsum ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    have hcast : ((((j + K) + 1) ^ 4 + 1 : ℕ) : ℝ) = (((j + K : ℕ) : ℝ) + 1) ^ 4 + 1 := by
      push_cast
      ring
    rw [hcast]
  have htsum : ∑' j : ℕ, (arrayMeasure N)
      (⋃ s ∈ Finset.range (((j + K) + 1) ^ 4 + 1),
        ({U : Array N | BadTime p m U a b (j + K) s} ∩ Extra (j + K))) ≠ ⊤ := by
    have hle := ENNReal.tsum_le_tsum hbnd
    have hof : ENNReal.ofReal (∑' j : ℕ,
          ((((j + K : ℕ) : ℝ) + 1) ^ 4 + 1) * Real.exp (-(c * (lvlB (j + K) : ℝ))))
        = ∑' j : ℕ, ENNReal.ofReal (((((j + K : ℕ) : ℝ) + 1) ^ 4 + 1)
            * Real.exp (-(c * (lvlB (j + K) : ℝ)))) :=
      ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hshift
    rw [← hof] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae := MeasureTheory.ae_eventually_notMem htsum
  filter_upwards [hae] with U hU
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hU
  refine eventually_atTop.2 ⟨J + K, fun k hk => ?_⟩
  have hjk : J ≤ k - K := by omega
  have hkk : k - K + K = k := by omega
  have hnot := hJ (k - K) hjk
  rw [hkk] at hnot
  intro s hs hb
  exact hnot (Set.mem_iUnion₂.2 ⟨s, Finset.mem_range.mpr (by omega), hb⟩)

/-- **No bad time above level `K`, almost surely**, from the crossing estimate in the
integrated form `P(bad time at (k,s)) <= exp(-c b_k)`. -/
theorem ae_eventually_no_bad_times {N : ℕ} {p : ℝ} (m : ℕ) (a b : Fin N) {K : ℕ} {c : ℝ}
    (hc : 0 < c)
    (hcross : ∀ k ≥ K, ∀ s : ℕ, (arrayMeasure N) {U : Array N | BadTime p m U a b k s}
      ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop,
      ∀ s ≤ (k + 1) ^ 4, ¬ BadTime p m U a b k s := by
  have h := ae_eventually_not_bad_inter (p := p) m a b (K := K) hc (fun _ => Set.univ)
    (fun k hk s => by
      have := hcross k hk s
      simpa [Set.inter_univ] using this)
  filter_upwards [h] with U hU
  filter_upwards [hU] with k hk
  intro s hs hb
  exact hk s hs ⟨hb, Set.mem_univ _⟩

/-- **The shape in which eq. (cross) delivers the estimate.**  The crossing bound is
available only on an extra event `Extra k` that holds eventually in `k` almost surely —
in the paper the extra event is the product-decay event
`prod_{a_k < x <= b_k} (1-w(x))/w(x) <= exp(-c b_k)` (from the log-ratio strong law).
Then the no-bad-time condition still holds almost surely. -/
theorem ae_eventually_no_bad_times_of_factored_bound {N : ℕ} {p : ℝ} (m : ℕ) (a b : Fin N)
    {K : ℕ} {c : ℝ} (hc : 0 < c) {Extra : ℕ → Set (Array N)}
    (hextra : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop, U ∈ Extra k)
    (hcross : ∀ k ≥ K, ∀ s : ℕ,
      (arrayMeasure N) ({U : Array N | BadTime p m U a b k s} ∩ Extra k)
        ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop,
      ∀ s ≤ (k + 1) ^ 4, ¬ BadTime p m U a b k s := by
  filter_upwards [ae_eventually_not_bad_inter (p := p) m a b (K := K) hc Extra hcross,
    hextra] with U h1 h2
  filter_upwards [h1, h2] with k hk hke
  intro s hs hb
  exact hk s hs ⟨hb, hke⟩

/-! ### Lemma `transience` from the crossing estimate -/

/-- **Transience from the eventual absence of bad times** (the form of the paper's step (2)):
almost surely, if eventually in `k` no time `s <= (k+1)^4` is a bad time, walker `a` is
transient to `+infinity`. -/
theorem ae_transience_of_eventually_no_bad {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (a b : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∀ᶠ k : ℕ in atTop, ∀ s ≤ (k + 1) ^ 4, ¬ BadTime p m U a b k s) →
        Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ K' : ℕ, 2 ≤ K' →
      ((∀ k ≥ K', ∀ s ≤ (k + 1) ^ 4, ¬ BadTime p m U a b k s) →
        Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop) := by
    refine MeasureTheory.ae_all_iff.mpr (fun K' => ?_)
    by_cases hK' : 2 ≤ K'
    · refine (ae_transience_of_no_bad_times (N := N) hp m a b hK').mono ?_
      intro U hU h2le
      exact hU
    · exact Eventually.of_forall (fun U h => absurd h hK')
  filter_upwards [hall] with U hU h1
  obtain ⟨K', hK'⟩ := eventually_atTop.1 h1
  exact hU (max K' 2) (le_max_right _ _) (fun k hk s hs =>
    hK' k (le_trans (le_max_left _ _) hk) s hs)

/-- **Lemma `transience` for the actual interacting trajectory**, from the crossing
estimate eq. (cross) alone.  For `p >= 1/2` and any two walkers `a`, `b`, if for some
`c > 0` and all levels `k >= K` and all times `s`

  `P(bad time of the paper at level k and time s) <= exp(-c b_k)`,

then walker `a` is almost surely transient to `+infinity`. -/
theorem ae_transience_of_crossing_bound {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (a b : Fin N) {K : ℕ} {c : ℝ} (hc : 0 < c)
    (hcross : ∀ k ≥ K, ∀ s : ℕ, (arrayMeasure N) {U : Array N | BadTime p m U a b k s}
      ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  filter_upwards [ae_eventually_no_bad_times (p := p) (m := m) (a := a) (b := b) (K := K) hc hcross,
    ae_transience_of_eventually_no_bad (N := N) hp m a b] with U h1 h2
  exact h2 h1

/-- **Lemma `transience` from the crossing estimate in the shape eq. (cross) delivers**
(the estimate holds on the product-decay event `Extra k`, which is eventually true
almost surely). -/
theorem ae_transience_of_factored_crossing_bound {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    (a b : Fin N) {K : ℕ} {c : ℝ} (hc : 0 < c) {Extra : ℕ → Set (Array N)}
    (hextra : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ k : ℕ in atTop, U ∈ Extra k)
    (hcross : ∀ k ≥ K, ∀ s : ℕ,
      (arrayMeasure N) ({U : Array N | BadTime p m U a b k s} ∩ Extra k)
        ≤ ENNReal.ofReal (Real.exp (-(c * (lvlB k : ℝ))))) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos a) atTop atTop := by
  filter_upwards [ae_eventually_no_bad_times_of_factored_bound (p := p) m a b (K := K) hc
      hextra hcross,
    ae_transience_of_eventually_no_bad (N := N) hp m a b] with U h1 h2
  exact h2 h1

end SwarmDischarge


