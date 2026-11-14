import Swarm.S13
import Swarm.JboundActual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
open SwarmMarks SwarmSpatial Swarming.Uniform

namespace SwarmSpatialSq

noncomputable section

/-- Moving a sum from sites `0,...,r-1` to sites `-1,...,r-2` shifts the starting
term to the initial value at `0`; this is the index conversion used by `b(x)=h(x-1)+2`. -/
theorem sum_pred (f : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ x ∈ Finset.range r, f (x - 1) = f 0 + ∑ x ∈ Finset.range (r - 1), f x := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases h0 : r = 0
    · subst r; simp
    · have hr0 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr h0
      rw [Finset.sum_range_succ, ih hr0]
      have hs := Finset.sum_range_succ f (r - 1)
      rw [Nat.sub_add_cancel hr0] at hs
      simp only [Nat.add_sub_cancel]
      rw [hs, add_assoc]

/-- The initial potential is bounded by `3/p`: at time zero it is either `3` or `(2-p)/p`. -/
theorem hof_zero_le_three_div {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (ω : ℕ → Bool) :
    hof p ω 0 ≤ 3 / p := by
  rw [hof_zero]
  cases h : ω 0 with
  | false =>
    rw [hstep_false]
    exact (le_div_iff₀ hp0).mpr (by nlinarith)
  | true =>
    rw [show hstep p true 1 = (2 - p) / p by
      rw [hstep_true]
      field_simp
      ring]
    exact div_le_div_of_nonneg_right (by linarith) hp0.le

/-- The actual second-moment bound at the shifted index `x-1`, with a deterministic
constant independent of the walker family and of `N`. -/
theorem exists_shifted_sq_linear_bound_array {N : ℕ} {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N,
      ∃ R₀ : ℕ, ∀ r ≥ R₀,
        ∑ x ∈ Finset.range r, (9 * (hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2)
          ≤ K * (r : ℝ) := by
  have hp : 0 < p := by linarith
  obtain ⟨K, hKpos, hU⟩ := exists_hof_sq_linear_bound_array (N := N) hp0 hp1 hm
  refine ⟨9 * ((3 / p) ^ 2 + K), by positivity, ?_⟩
  filter_upwards [hU] with U hU j
  obtain ⟨R₀, hR₀⟩ := hU j
  refine ⟨max 2 (R₀ + 1), fun r hr => ?_⟩
  have hr2 : 2 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : R₀ ≤ r - 1 := by
    have := le_trans (le_max_right (2 : ℕ) (R₀ + 1)) hr
    omega
  have hbase := hR₀ (r - 1) hr0
  have hzero : hof p (SwarmLogRatio.siteMarksN p m U j) 0 ≤ 3 / p :=
    hof_zero_le_three_div hp hp1.le (SwarmLogRatio.siteMarksN p m U j)
  have hzero0 : 0 ≤ hof p (SwarmLogRatio.siteMarksN p m U j) 0 := by
    linarith [one_le_hof hp0.le hp1 (SwarmLogRatio.siteMarksN p m U j) 0]
  have hzeroSq : (hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2 ≤ (3 / p) ^ 2 := by
    have hmul := mul_le_mul hzero hzero hzero0 (by positivity : (0 : ℝ) ≤ 3 / p)
    nlinarith
  have hshift := sum_pred (fun x => 9 * (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2)
    (by omega : 1 ≤ r)
  have hmul : 9 * (∑ x ∈ Finset.range (r - 1),
      (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2)
      ≤ 9 * (K * ((r - 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hrcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  calc
    (∑ x ∈ Finset.range r, (9 * (hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2))
        = 9 * (hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2
          + ∑ x ∈ Finset.range (r - 1),
            (9 * (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2) := hshift
    _ = 9 * (hof p (SwarmLogRatio.siteMarksN p m U j) 0) ^ 2
          + 9 * (∑ x ∈ Finset.range (r - 1),
            (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 9 * ((3 / p) ^ 2) + 9 * (K * ((r - 1 : ℕ) : ℝ)) := by nlinarith
    _ ≤ (9 * ((3 / p) ^ 2 + K)) * (r : ℝ) := by
      rw [hrcast] at hmul ⊢
      nlinarith

/-- The running-maximum record-cost bound with an explicit spatial threshold. This replaces
`Jbound_runMax`'s `∀m` spatial estimate by one valid above `R₀`, which is what the eventually
growing record needs in applications. -/
theorem Jbound_runMax_eventual {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε)
    {b w : ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x) (hbw : ∀ x, b x ^ 2 ≤ w x)
    {X : ℕ → ℤ} {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r (t + 1) ≤ r t + 1)
    {K : ℝ} {R₀ : ℕ}
    (hces : ∀ m ≥ R₀, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ)) (n : ℕ)
    (hM : R₀ ≤ max 0 (SwarmSpeed.runMax X n).toNat) :
    ∑ t ∈ Finset.range n, |SwarmJb.Jinc a ε b X r t| ≤
      2 * (1 / (ε * (1 - a) ^ 2)) * K * (max 0 ((SwarmSpeed.runMax X n : ℤ) : ℝ) + 1) := by
  have hden : (0 : ℝ) ≤ 1 / (ε * (1 - a) ^ 2) := by
    have : (0 : ℝ) < 1 - a := by linarith
    positivity
  have hX : ∀ t, t + 1 ≤ n → X (t + 1) ≤ ((max 0 (SwarmSpeed.runMax X n).toNat : ℕ) : ℤ) := by
    intro t ht
    have h1 : X (t + 1) ≤ SwarmSpeed.runMax X n := SwarmSpeed.le_runMax (by omega)
    exact le_trans h1 (SwarmJb.runMax_le_maxToNat _)
  have hbase := SwarmJb.Jsum_le_index (r := r) (X := X) (w := w)
    (C := 1 / (ε * (1 - a) ^ 2)) (J := fun t => SwarmJb.Jinc a ε b X r t)
    hmono hw hden (fun t => SwarmJb.Jinc_abs_le (X := X) (r := r)
      ha0 ha1 hε hb hbw hmono hstep t) n (max 0 (SwarmSpeed.runMax X n).toNat) hX
  have hs := hces (max 0 (SwarmSpeed.runMax X n).toNat + 1) (by omega)
  have hnext := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (1 / (ε * (1 - a) ^ 2)) by positivity)
  have hfinal := hbase.trans hnext
  simpa only [Nat.cast_add, Nat.cast_one, SwarmJb.natCast_max_toNat, mul_assoc] using hfinal

/-- The actual record-cost bound with the paper's cap `b(x)=h(x-1)+2` and weight
`w(x)=9h(x-1)^2`. After the record has passed the environment-dependent spatial threshold, the
record-cost sum is bounded linearly by the walker's running maximum, with a constant that depends
only on `p,m,ε`. -/
theorem actual_Jbound_runMax_eventual {N : ℕ} {p ε : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (hε : 0 < ε) {m : ℕ} (hm : 2 ≤ m) {X : ℕ → ℤ} {r : ℕ → ℕ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hstep : ∀ t, r (t + 1) ≤ r t + 1) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∃ R₀ : ℕ,
      R₀ ≤ max 0 (SwarmSpeed.runMax X n).toNat →
        ∑ t ∈ Finset.range n, |SwarmJb.Jinc (ExcitedEnv.aConst p ((1 - p) ^ (m - 1))) ε
            (fun x => hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1) + 2) X r t|
          ≤ (2 / (ε * (1 - ExcitedEnv.aConst p ((1 - p) ^ (m - 1))) ^ 2)) * K *
            (max 0 ((SwarmSpeed.runMax X n : ℤ) : ℝ) + 1) := by
  have hp : 0 < p := by linarith
  obtain ⟨K, hKpos, hU⟩ := exists_shifted_sq_linear_bound_array (N := N) hp0 hp1 hm
  have haa := ExcitedEnv.aConst_bounds hp0 hp1 (pow_pos (by linarith) (m - 1))
    (ExcitedEnv.q_le_half hp0 hp1 hm)
  have ha0 : 0 ≤ ExcitedEnv.aConst p ((1 - p) ^ (m - 1)) := by linarith [haa.1]
  have ha1 : ExcitedEnv.aConst p ((1 - p) ^ (m - 1)) < 1 := haa.2.1
  have hden : 0 < 2 / (ε * (1 - ExcitedEnv.aConst p ((1 - p) ^ (m - 1))) ^ 2) := by positivity
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hU] with U hU j
  obtain ⟨R₀, hR₀⟩ := hU j
  refine ⟨R₀, fun hM => ?_⟩
  have hb : ∀ x, 0 ≤ hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1) + 2 := by
    intro x
    have h := one_le_hof hp0.le hp1 (SwarmLogRatio.siteMarksN p m U j) (x - 1)
    linarith
  have hw : ∀ x, 0 ≤ 9 * (hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2 := by
    intro x; positivity
  have hbw : ∀ x, (hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1) + 2) ^ 2
      ≤ 9 * (hof p (SwarmLogRatio.siteMarksN p m U j) (x - 1)) ^ 2 := by
    intro x
    exact SwarmJb.sq_add_two_le_nine_mul_sq (one_le_hof hp0.le hp1
      (SwarmLogRatio.siteMarksN p m U j) (x - 1))
  have hfinal := Jbound_runMax_eventual ha0 ha1 hε hb hw hbw hmono hstep hR₀ n hM
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hfinal

end
end SwarmSpatialSq


