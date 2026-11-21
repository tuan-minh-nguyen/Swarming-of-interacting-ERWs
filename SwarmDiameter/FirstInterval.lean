import SwarmDiameter.ArithmeticRenewal

open Filter Finset
open scoped Topology

namespace Swarming.ArithmeticRenewal

/-- The first-interval recurrence and the last-renewal convolution compute the
same sequence. In the recurrence `p k` is the probability of duration `k+1`. -/
theorem eq_renewalReward_of_first_interval {p f v : ℕ → ℝ}
    (hzero : v 0 = f 0)
    (hsucc : ∀ n, v (n + 1) = f (n + 1) + ∑ k ∈ range (n + 1), p k * v (n - k)) :
    ∀ n, v n = ∑ k ∈ range (n + 1), f k * renewalMass p (n - k) := by
  let w (n : ℕ) := ∑ k ∈ range (n + 1), f k * renewalMass p (n - k)
  have conv (n : ℕ) :
      (∑ k ∈ range (n + 1), f k * ∑ j ∈ range (n - k + 1), p j * renewalMass p (n - k - j)) =
      ∑ j ∈ range (n + 1), p j * w (n - j) := by
    have filter_eq (k : ℕ) (hk : k ∈ range (n + 1)) :
        (range (n + 1)).filter (fun j => j + k ≤ n) = range (n - k + 1) := by
      ext j
      simp only [mem_range, mem_filter] at hk ⊢
      omega
    have aux (a b : ℕ → ℝ) (k : ℕ) (hk : k ∈ range (n + 1)) :
        a k * (∑ j ∈ range (n - k + 1), b j * renewalMass p (n - k - j)) =
          ∑ j ∈ range (n + 1), if j + k ≤ n then
            a k * (b j * renewalMass p (n - k - j)) else 0 := by
      rw [mul_sum, ← sum_filter, filter_eq k hk]
    calc
      _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), if j + k ≤ n then
          f k * (p j * renewalMass p (n - k - j)) else 0 := by
        exact sum_congr rfl (aux f p)
      _ = ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1), if k + j ≤ n then
          p j * (f k * renewalMass p (n - j - k)) else 0 := by
        rw [sum_comm]
        refine sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => ?_))
        rw [show n - k - j = n - j - k by omega, Nat.add_comm j k, mul_left_comm (f k)]
      _ = _ := by
        refine sum_congr rfl (fun j hj => ?_)
        exact (aux p f j hj).symm
  have wstep (n : ℕ) : w (n + 1) = f (n + 1) + ∑ j ∈ range (n + 1), p j * w (n - j) := by
    unfold w
    rw [sum_range_succ, Nat.sub_self, renewalMass_zero, mul_one, add_comm]
    congr 1
    change (∑ k ∈ range (n + 1), f k * renewalMass p (n + 1 - k)) =
      ∑ j ∈ range (n + 1), p j * w (n - j)
    rw [← conv n]
    refine sum_congr rfl (fun k hk => ?_)
    have hk' := mem_range.mp hk
    rw [show n + 1 - k = n - k + 1 by omega, renewalMass_succ]
  intro n
  change v n = w n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [w] using hzero
    | succ n =>
      rw [hsucc, wstep]
      congr 1
      refine sum_congr rfl (fun k _ => ?_)
      rw [ih (n - k) (by omega)]

end Swarming.ArithmeticRenewal
