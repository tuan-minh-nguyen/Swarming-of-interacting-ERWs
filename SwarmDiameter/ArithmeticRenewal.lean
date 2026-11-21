import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The discrete renewal theorem with positive mass at one

The probability of an interarrival of length 'k + 1' is 'p k'. The proof uses the renewal
equation, the survival convolution identity, and square summability of
successive differences of the renewal mass.
-/

open Filter Finset
open scoped Topology

namespace Swarming.ArithmeticRenewal

/-- The renewal mass of the interarrival sequence indexed from one. -/
noncomputable def renewalMass (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), p k * renewalMass p (n - (k : ℕ))
termination_by n => n
decreasing_by omega

/-- The survival probability at integer time 'n'. -/
noncomputable def survival (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ k ∈ range n, p k

@[simp] theorem renewalMass_zero (p : ℕ → ℝ) : renewalMass p 0 = 1 := by
  rw [renewalMass]

theorem renewalMass_succ (p : ℕ → ℝ) (n : ℕ) :
    renewalMass p (n + 1) = ∑ k ∈ range (n + 1), p k * renewalMass p (n - k) := by
  rw [renewalMass]
  exact Fin.sum_univ_eq_sum_range (fun k => p k * renewalMass p (n - k)) (n + 1)

@[simp] theorem survival_zero (p : ℕ → ℝ) : survival p 0 = 1 := by
  simp [survival]

theorem survival_succ (p : ℕ → ℝ) (n : ℕ) : survival p (n + 1) = survival p n - p n := by
  rw [survival, sum_range_succ]
  unfold survival
  ring

private theorem sum_range_le_one {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hs : Summable p) (h : ∑' k, p k = 1) (n : ℕ) :
    ∑ k ∈ range n, p k ≤ 1 := by
  rw [← h]
  exact hs.sum_le_tsum _ (fun k _ => hp k)

/-- Every renewal mass lies in the probability interval. -/
theorem renewalMass_bounds {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hs : Summable p) (hsum : ∑' k, p k = 1) :
    ∀ n, 0 ≤ renewalMass p n ∧ renewalMass p n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [renewalMass_succ]
      constructor
      · exact sum_nonneg (fun k _ => mul_nonneg (hp k) (ih (n - k) (by omega)).1)
      · calc
          ∑ k ∈ range (n + 1), p k * renewalMass p (n - k)
              ≤ ∑ k ∈ range (n + 1), p k := by
                exact sum_le_sum (fun k _ =>
                  mul_le_of_le_one_right (hp k) (ih (n - k) (by omega)).2)
          _ ≤ 1 := sum_range_le_one hp hs hsum _

theorem survival_convolution (p : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), survival p k * renewalMass p (n - k) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ']
    simp only [survival_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, survival_succ,
      sub_mul, sum_sub_distrib]
    rw [ih, ← renewalMass_succ]
    ring

private theorem sum_shifted (f : ℕ → ℝ) (k n : ℕ) :
    ∑ j ∈ range n, (if k ≤ j then f (j - k) else 0) = ∑ j ∈ range (n - k), f j := by
  rw [← sum_filter]
  refine sum_bij (fun j _ => j - k) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    omega
  · intro j hj i hi h
    simp only [mem_filter, mem_range] at hj hi
    omega
  · intro j hj
    have h : j < n - k := mem_range.mp hj
    refine ⟨j + k, ?_, by omega⟩
    simp only [mem_filter, mem_range]
    omega
  · intros
    rfl

private theorem sum_convolution_le {p f : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hf : ∀ k, 0 ≤ f k) (h : ∀ n, ∑ k ∈ range n, p k ≤ 1) (n : ℕ) :
    ∑ j ∈ range n, ∑ k ∈ range (j + 1), p k * f (j - k) ≤ ∑ j ∈ range n, f j := by
  calc
    _ = ∑ j ∈ range n, ∑ k ∈ range n, (if k ≤ j then p k * f (j - k) else 0) := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      congr 1
      ext k
      simp only [mem_range, mem_filter] at hj ⊢
      omega
    _ = ∑ k ∈ range n, p k * ∑ j ∈ range (n - k), f j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [← sum_shifted f k n, mul_sum]
      apply sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ ≤ ∑ k ∈ range n, p k * ∑ j ∈ range n, f j := by
      apply sum_le_sum
      intro k _
      refine mul_le_mul_of_nonneg_left ?_ (hp k)
      exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _)) (fun j _ _ => hf j)
    _ = (∑ k ∈ range n, p k) * ∑ j ∈ range n, f j := by rw [sum_mul]
    _ ≤ _ := mul_le_of_le_one_left (sum_nonneg (fun j _ => hf j)) (h n)

private theorem energyBound {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hs : Summable p) (hsum : ∑' k, p k = 1) (n : ℕ) :
    p 0 * (renewalMass p (n + 1) - renewalMass p n) ^ 2 ≤
      (∑ k ∈ range (n + 1), p k * renewalMass p (n - k) ^ 2) -
        renewalMass p (n + 1) ^ 2 := by
  let u := renewalMass p
  have hu : ∑ k ∈ range (n + 1), p k * u (n - k) = u (n + 1) :=
    (renewalMass_succ p n).symm
  calc
    _ ≤ ∑ k ∈ range (n + 1), p k * (u (n + 1) - u (n - k)) ^ 2 := by
      have h₀ : 0 ∈ range (n + 1) := by simp
      simpa using (single_le_sum (f := fun k => p k * (u (n + 1) - u (n - k)) ^ 2)
        (fun k _ => mul_nonneg (hp k) (sq_nonneg _)) h₀)
    _ = (∑ k ∈ range (n + 1), p k) * u (n + 1) ^ 2 -
        2 * u (n + 1) ^ 2 + ∑ k ∈ range (n + 1), p k * u (n - k) ^ 2 := by
      have e (k : ℕ) : p k * (u (n + 1) - u (n - k)) ^ 2 =
          p k * u (n + 1) ^ 2 - 2 * u (n + 1) * (p k * u (n - k)) +
            p k * u (n - k) ^ 2 := by ring
      simp only [e, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hu]
      ring
    _ ≤ _ := by
      have hmul := mul_le_of_le_one_left (sq_nonneg (u (n + 1)))
        (sum_range_le_one hp hs hsum (n + 1))
      change _ ≤ (∑ k ∈ range (n + 1), p k * u (n - k) ^ 2) - u (n + 1) ^ 2
      linarith

private theorem successive_diff_tendsto_zero {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hp₀ : 0 < p 0) (hs : Summable p) (hsum : ∑' k, p k = 1) :
    Tendsto (fun n => renewalMass p (n + 1) - renewalMass p n) atTop (𝓝 0) := by
  let u := renewalMass p
  have hpartial (n : ℕ) :
      ∑ j ∈ range n, (u (j + 1) - u j) ^ 2 ≤ 1 / p 0 := by
    apply (le_div_iff₀ hp₀).2
    rw [mul_comm, mul_sum]
    calc
      _ ≤ ∑ j ∈ range n, ((∑ k ∈ range (j + 1), p k * u (j - k) ^ 2) -
            u (j + 1) ^ 2) := sum_le_sum (fun j _ => energyBound hp hs hsum j)
      _ ≤ (∑ j ∈ range n, u j ^ 2) - ∑ j ∈ range n, u (j + 1) ^ 2 := by
        rw [sum_sub_distrib]
        exact sub_le_sub_right (sum_convolution_le hp (fun j => sq_nonneg (u j))
          (sum_range_le_one hp hs hsum) n) _
      _ ≤ 1 := by
        have htel :
            (∑ j ∈ range n, u j ^ 2) + u n ^ 2 =
              (∑ j ∈ range n, u (j + 1) ^ 2) + 1 := by
          rw [← sum_range_succ, sum_range_succ']
          simp [u]
        linarith [sq_nonneg (u n)]
  have hsq : Tendsto (fun n => (u (n + 1) - u n) ^ 2) atTop (𝓝 0) :=
    (summable_of_sum_range_le (fun n => sq_nonneg _) hpartial).tendsto_atTop_zero
  rw [Metric.tendsto_nhds] at hsq ⊢
  intro ε hε
  filter_upwards [hsq (ε ^ 2) (sq_pos_of_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hn
  nlinarith [sq_abs (u (n + 1) - u n), abs_nonneg (u (n + 1) - u n)]

private theorem lagged_diff_tendsto_zero {u : ℕ → ℝ}
    (h : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => u n - u (n - k)) atTop (𝓝 0) := by
  have hf (k : ℕ) : Tendsto (fun n => u (n + k) - u n) atTop (𝓝 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have sh : Tendsto (fun n : ℕ => n + k) atTop atTop := by
        exact tendsto_atTop.2 (fun b =>
          (eventually_ge_atTop b).mono (fun n hn => by omega))
      have h₁ := (h.comp sh).add ih
      convert h₁ using 1
      · ext n
        simp only [Function.comp_apply, Nat.add_assoc]
        ring
      · simp
  have sh : Tendsto (fun n : ℕ => n - k) atTop atTop := by
    exact tendsto_atTop.2 (fun b =>
      (eventually_ge_atTop (b + k)).mono (fun n hn => by omega))
  apply ((hf k).comp sh).congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [Function.comp_apply, Nat.sub_add_cancel hn]

/-- The arithmetic renewal theorem when the interarrival law has positive mass at one. -/
theorem renewalMass_tendsto {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hp₀ : 0 < p 0)
    (hs : Summable p) (hsum : ∑' k, p k = 1) (hfin : Summable (survival p)) :
    Tendsto (renewalMass p) atTop (𝓝 ((∑' k, survival p k)⁻¹)) := by
  let u := renewalMass p
  let w := survival p
  let μ := ∑' k, w k
  have hw (k : ℕ) : 0 ≤ w k := sub_nonneg.mpr (sum_range_le_one hp hs hsum k)
  have hμ : 0 < μ := by
    have h₁ : w 0 ≤ μ := hfin.le_tsum 0 (fun k _ => hw k)
    simpa [w] using lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (by simpa [w] using h₁)
  have hu := renewalMass_bounds hp hs hsum
  let trunc (n k : ℕ) := if k ≤ n then u (n - k) else 0
  have htrunc (n k : ℕ) : 0 ≤ trunc n k ∧ trunc n k ≤ 1 := by
    by_cases h : k ≤ n
    · simpa only [trunc, if_pos h, u] using hu (n - k)
    · simp [trunc, h]
  let f (n k : ℕ) := w k * (u n - trunc n k)
  have hbound (n k : ℕ) : ‖f n k‖ ≤ w k := by
    rw [Real.norm_eq_abs, show f n k = w k * (u n - trunc n k) by rfl, abs_mul,
      abs_of_nonneg (hw k)]
    apply mul_le_of_le_one_right (hw k)
    exact abs_le.mpr ⟨by linarith [(hu n).1, (htrunc n k).2],
      by linarith [(hu n).2, (htrunc n k).1]⟩
  have hf (k : ℕ) : Tendsto (f · k) atTop (𝓝 (0 : ℝ)) := by
    have h₁ := (tendsto_const_nhds (x := w k)).mul
      (lagged_diff_tendsto_zero (successive_diff_tendsto_zero hp hp₀ hs hsum) k)
    rw [mul_zero] at h₁
    apply h₁.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    simp [f, trunc, hn, u]
  have hlimit : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence hfin hf (Eventually.of_forall hbound))
  have hsum_eq (n : ℕ) : ∑' k, f n k = μ * u n - 1 := by
    have ht : HasSum (fun k => w k * trunc n k) 1 := by
      rw [← survival_convolution p n]
      have h₁ (k : ℕ) (hk : k ∉ range (n + 1)) : w k * trunc n k = 0 := by
        have hkn : ¬ k ≤ n := by
          simp only [mem_range] at hk
          omega
        simp [trunc, hkn]
      have hs := hasSum_sum_of_ne_finset_zero
        (L := SummationFilter.unconditional ℕ) h₁
      convert hs using 1
      apply sum_congr rfl
      intro k hk
      simp only [mem_range] at hk
      simp [w, u, trunc, show k ≤ n by omega]
    have ht₂ := (hfin.hasSum.mul_right (u n)).sub ht
    convert ht₂.tsum_eq using 1
    congr 1
    ext k
    unfold f
    ring
  simp only [hsum_eq] at hlimit
  have hlast := (hlimit.add (tendsto_const_nhds (x := (1 : ℝ)))).div_const μ
  convert hlast using 1
  · ext n
    rw [sub_add_cancel, mul_comm μ, mul_div_cancel_right₀ _ (ne_of_gt hμ)]
  · rw [zero_add, one_div]

/-- Convolution with a summable sequence preserves the limit of a bounded sequence,
multiplied by the sum of the summable sequence. -/
theorem tendsto_convolution {u f : ℕ → ℝ} {c : ℝ} (hu : Tendsto u atTop (𝓝 c))
    (hbound : ∀ n, |u n| ≤ 1) (hf : Summable (fun k => |f k|)) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), f k * u (n - k)) atTop
      (𝓝 ((∑' k, f k) * c)) := by
  let term (n k : ℕ) := if k ≤ n then f k * u (n - k) else 0
  have hlim (k : ℕ) : Tendsto (term · k) atTop (𝓝 (f k * c)) := by
    have hsub : Tendsto (fun n : ℕ => n - k) atTop atTop := by
      exact tendsto_atTop.2 (fun b =>
        (eventually_ge_atTop (b + k)).mono (fun n hn => by omega))
    apply ((tendsto_const_nhds (x := f k)).mul (hu.comp hsub)).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    simp [term, hn, Function.comp_apply]
  have hdom (n k : ℕ) : ‖term n k‖ ≤ |f k| := by
    rw [Real.norm_eq_abs]
    by_cases h : k ≤ n
    · simp only [term, if_pos h, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hbound _)
    · simp [term, h]
  have h := tendsto_tsum_of_dominated_convergence hf hlim (Eventually.of_forall hdom)
  have heq (n : ℕ) : ∑' k, term n k =
      ∑ k ∈ range (n + 1), f k * u (n - k) := by
    rw [tsum_eq_sum (s := range (n + 1))]
    · refine sum_congr rfl (fun k hk => ?_)
      have hn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      simp [term, hn]
    · intro k hk
      have hn : ¬ k ≤ n := fun h => hk (mem_range.mpr (Nat.lt_succ_iff.mpr h))
      simp [term, hn]
  simpa only [heq, tsum_mul_right] using h

/-- The arithmetic renewal theorem for a summable sequence of rewards. -/
theorem renewalReward_tendsto {p f : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hp₀ : 0 < p 0)
    (hs : Summable p) (hsum : ∑' k, p k = 1) (hfin : Summable (survival p))
    (hf : Summable (fun k => |f k|)) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), f k * renewalMass p (n - k)) atTop
      (𝓝 ((∑' k, f k) / (∑' k, survival p k))) := by
  have h := tendsto_convolution (renewalMass_tendsto hp hp₀ hs hsum hfin) (fun n => by
    have h₁ := renewalMass_bounds hp hs hsum n
    simpa only [abs_of_nonneg h₁.1] using h₁.2) hf
  simpa only [div_eq_mul_inv] using h

private theorem survival_hasSum {p : ℕ → ℝ} (hs : Summable p) (hsum : ∑' j, p j = 1)
    (k : ℕ) : HasSum (fun j => if k ≤ j then p j else 0) (survival p k) := by
  have h₀ (j : ℕ) (hj : j ∉ range k) : (if j < k then p j else 0) = 0 :=
    if_neg (by simpa only [mem_range] using hj)
  have hhead : HasSum (fun j => if j < k then p j else 0) (∑ j ∈ range k, p j) := by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) h₀
    convert h using 1
    exact sum_congr rfl (fun j hj => (if_pos (mem_range.mp hj)).symm)
  have h := hs.hasSum.sub hhead
  rw [hsum] at h
  have heq : (fun j : ℕ => p j - if j < k then p j else 0) =
      (fun j : ℕ => if k ≤ j then p j else 0) := by
    funext j
    by_cases hj : j < k
    · simp [hj, Nat.not_le.mpr hj]
    · simp [hj, Nat.le_of_not_gt hj]
  rw [heq] at h
  exact h

private theorem truncatedMean_hasSum {p : ℕ → ℝ} (hs : Summable p)
    (hsum : ∑' j, p j = 1) (n : ℕ) :
    HasSum (fun j : ℕ => ((min n (j + 1) : ℕ) : ℝ) * p j)
      (∑ k ∈ range n, survival p k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h₁ := ih.add (survival_hasSum hs hsum n)
    convert h₁ using 1
    funext j
    by_cases h : n ≤ j
    · rw [if_pos h, min_eq_left (by omega : n ≤ j + 1),
        min_eq_left (by omega : n + 1 ≤ j + 1)]
      push_cast
      ring
    · rw [if_neg h, min_eq_right (by omega : j + 1 ≤ n),
        min_eq_right (by omega : j + 1 ≤ n + 1), add_zero]

/-- The mean duration is the sum of the survival probabilities. -/
theorem survival_sum_eq_mean {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hsum : ∑' k, p k = 1) (hmean : Summable (fun k : ℕ => ↑(k + 1) * p k)) :
    Summable (survival p) ∧ ∑' k, survival p k = ∑' k : ℕ, ↑(k + 1) * p k := by
  let f (n j : ℕ) := ((min n (j + 1) : ℕ) : ℝ) * p j
  have h₁ (n j : ℕ) : f n j ≤ ↑(j + 1) * p j := by
    apply mul_le_mul_of_nonneg_right ?_ (hp j)
    exact_mod_cast min_le_right n (j + 1)
  have h₀ (n j : ℕ) : 0 ≤ f n j := mul_nonneg (Nat.cast_nonneg _) (hp j)
  have hsum₁ (n : ℕ) : HasSum (f n) (∑ k ∈ range n, survival p k) :=
    truncatedMean_hasSum hs hsum n
  have hfin : Summable (survival p) := by
    apply summable_of_sum_range_le (c := ∑' j : ℕ, ↑(j + 1) * p j)
    · exact fun k => sub_nonneg.mpr (sum_range_le_one hp hs hsum k)
    · intro n
      rw [← (hsum₁ n).tsum_eq]
      exact (hsum₁ n).summable.tsum_le_tsum (h₁ n) hmean
  have ht (j : ℕ) : Tendsto (f · j) atTop (𝓝 (↑(j + 1) * p j)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (j + 1)] with n hn
    simp only [f, min_eq_right hn]
  have h :=
    tendsto_tsum_of_dominated_convergence hmean ht (Eventually.of_forall (fun n j => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h₀ n j)] using h₁ n j))
  simp only [fun n => (hsum₁ n).tsum_eq] at h
  exact ⟨hfin, tendsto_nhds_unique hfin.hasSum.tendsto_sum_nat h⟩

/-- A form of the renewal reward limit with the usual finite mean assumption. -/
theorem renewalReward_tendsto_mean {p f : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hp₀ : 0 < p 0) (hs : Summable p) (hsum : ∑' k, p k = 1)
    (hmean : Summable (fun k : ℕ => ↑(k + 1) * p k)) (hf : Summable (fun k => |f k|)) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), f k * renewalMass p (n - k)) atTop
      (𝓝 ((∑' k, f k) / (∑' k : ℕ, ↑(k + 1) * p k))) := by
  obtain ⟨hfin, hμ⟩ := survival_sum_eq_mean hp hs hsum hmean
  simpa only [hμ] using renewalReward_tendsto hp hp₀ hs hsum hfin hf

end Swarming.ArithmeticRenewal
