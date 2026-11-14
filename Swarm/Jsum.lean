/-
  `(Jbound)` of the occupation-time estimate (Proposition `ball` of
  *Swarming of interacting excited random walks*, `main_1d_revised.tex`):

      sum_{t=0}^{n-1} |J_{t+1}|
        <= C_eps sum_{x=0}^{M^i_n - 1} h_j(x-1)^2
        <= C M^i_n + O(1)                                          (Jbound)

  where `J_{t+1} = F_{b_{t+1}}(X^i_{t+1} - r_{t+1}) - F_{b_t}(X^i_{t+1} - r_t)` and
  `r_n = M^j_n` is the record of walker `j`.

  The paper's argument is purely combinatorial *given* the pointwise bound
  `|J_{t+1}| <= C_eps h_j(r_t - 1)^2 1{r_{t+1} = r_t + 1, X^i_{t+1} > r_t}` proved in
  `Vdrift.J_abs_le`/`J_eq_zero_of`.  Its content is:

  * the record is nondecreasing, and it can only take each value once at an advance time, so
    `t |-> r_t` is **injective on the advance set** `{t : r_{t+1} = r_t + 1}`;
  * hence the record-cost sum is at most `2 C` times the spatial sum of `g` over the range
    `[0, r_n + 1]`, i.e. at most `2 C K M^i_n` if the spatial sum is `O(M)` — which is the
    paper's `(spav)` input.

  `Jsum_le` is that counting argument; `Jsum_bound` adds the (spav)-type linear spatial
  bound.  Nothing here is probabilistic, and no walker count occurs.
-/
import Swarm.Imports

open Finset
open scoped BigOperators

namespace SwarmOcc

/-- **Injectivity on the advance set** for any horizon: if `s < t` are both advance times then
`r s < r t`. -/
lemma advance_inj {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1)) {n s t : ℕ}
    (hs : s ∈ (Finset.range n).filter (fun u => r (u + 1) = r u + 1))
    (ht : t ∈ (Finset.range n).filter (fun u => r (u + 1) = r u + 1)) (hst : s ≠ t) :
    r s ≠ r t := by
  have hms : r s ≤ r (s + 1) := hmono s
  have hstrict : r s < r (s + 1) := by
    have := (Finset.mem_filter.mp hs).2
    omega
  have hmono' : Monotone r := monotone_nat_of_le_succ hmono
  rcases lt_or_gt_of_ne hst with h | h
  · have h2 : r (s + 1) ≤ r t := hmono' (by omega)
    omega
  · have h2 : r (t + 1) ≤ r s := hmono' (by omega)
    have hstrict' : r t < r (t + 1) := by
      have := (Finset.mem_filter.mp ht).2
      omega
    omega

/-- **`(Jbound)`, counting form.**  For a nondecreasing record `r`, a nonnegative weight `g`,
and record costs whose advance-time increments are bounded by `C (g (r_t) + g (r_t + 1))`,

    sum_{t<n} |J_{t+1}| <= 2 C sum_{x < r_n + 2} g x.

The proof is the paper's: at most one advance time per record value, and every advance value
lies below `r_n + 2`. -/
theorem Jsum_le {r : ℕ → ℕ} {g : ℕ → ℝ} {C : ℝ} {J : ℕ → ℝ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hg : ∀ x, 0 ≤ g x) (hC : 0 ≤ C)
    (hJ : ∀ t, |J (t + 1)|
      ≤ C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0))
    (n : ℕ) :
    ∑ t ∈ Finset.range n, |J (t + 1)| ≤ 2 * C * ∑ x ∈ Finset.range (r n + 2), g x := by
  classical
  have hmono' : Monotone r := monotone_nat_of_le_succ hmono
  set S : Finset ℕ := (Finset.range n).filter (fun t => r (t + 1) = r t + 1) with hS
  -- (1) the total is at most the sum of the pointwise bounds supported on `S`
  have hstep1 : ∑ t ∈ Finset.range n, |J (t + 1)|
      ≤ ∑ t ∈ S, C * (g (r t) + g (r t + 1)) := by
    have h1 : ∑ t ∈ Finset.range n, |J (t + 1)|
        ≤ ∑ t ∈ Finset.range n,
          C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0) :=
      Finset.sum_le_sum fun t _ => hJ t
    have h2 : ∑ t ∈ Finset.range n,
          C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0)
        = ∑ t ∈ S, C * (g (r t) + g (r t + 1)) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : r (t + 1) = r t + 1
      · simp [h]
      · simp [h]
    linarith
  -- (2) split into the two injective images of the record
  have hsplit : ∑ t ∈ S, C * (g (r t) + g (r t + 1))
      = C * (∑ t ∈ S, g (r t)) + C * (∑ t ∈ S, g (r t + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hinj : ∀ s ∈ S, ∀ t ∈ S, r s = r t → s = t := by
    intro s hs t ht hst
    by_contra hne
    exact advance_inj hmono hs ht hne hst
  have hinj' : ∀ s ∈ S, ∀ t ∈ S, r s + 1 = r t + 1 → s = t := by
    intro s hs t ht hst
    refine hinj s hs t ht ?_
    omega
  -- (3) each image is contained in `range (r n + 2)`
  have hsub1 : S.image r ⊆ Finset.range (r n + 2) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htn : t < n := (Finset.mem_filter.mp ht).1 |> Finset.mem_range.mp
    have : r t ≤ r n := hmono' (le_of_lt htn)
    rw [Finset.mem_range]
    omega
  have hsub2 : S.image (fun t => r t + 1) ⊆ Finset.range (r n + 2) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htn : t < n := (Finset.mem_filter.mp ht).1 |> Finset.mem_range.mp
    have : r t ≤ r n := hmono' (le_of_lt htn)
    rw [Finset.mem_range]
    omega
  have himg1 : ∑ t ∈ S, g (r t) = ∑ x ∈ S.image r, g x :=
    (Finset.sum_image hinj).symm
  have himg2 : ∑ t ∈ S, g (r t + 1) = ∑ x ∈ S.image (fun t => r t + 1), g x :=
    (Finset.sum_image hinj').symm
  have hb1 : ∑ x ∈ S.image r, g x ≤ ∑ x ∈ Finset.range (r n + 2), g x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun x _ _ => hg x
  have hb2 : ∑ x ∈ S.image (fun t => r t + 1), g x ≤ ∑ x ∈ Finset.range (r n + 2), g x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun x _ _ => hg x
  have hG : (0 : ℝ) ≤ ∑ x ∈ Finset.range (r n + 2), g x :=
    Finset.sum_nonneg fun x _ => hg x
  rw [hsplit] at hstep1
  rw [himg1, himg2] at hstep1
  nlinarith [hstep1, hb1, hb2, hG, hC]

/-- **`(Jbound)` with a linear spatial bound.**  If the spatial sum of `g` up to `m` is at
most `K m` — the paper's `(spav)` input, available on the actual array through the spatial
layer — then

    sum_{t<n} |J_{t+1}| <= 2 C K (M^j_n + 2).

This is the paper's `sum |J_{t+1}| <= C M^i_n + O(1)` up to the explicit constant `2 C K` and
the additive `2`. -/
theorem Jsum_bound {r : ℕ → ℕ} {g : ℕ → ℝ} {C K : ℝ} {J : ℕ → ℝ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hg : ∀ x, 0 ≤ g x) (hC : 0 ≤ C)
    (hJ : ∀ t, |J (t + 1)|
      ≤ C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0))
    (hces : ∀ m : ℕ, ∑ x ∈ Finset.range m, g x ≤ K * (m : ℝ)) (n : ℕ) :
    ∑ t ∈ Finset.range n, |J (t + 1)| ≤ 2 * C * K * ((r n : ℝ) + 2) := by
  have h1 := Jsum_le hmono hg hC hJ n
  have h2 : ∑ x ∈ Finset.range (r n + 2), g x ≤ K * ((r n : ℝ) + 2) := by
    have := hces (r n + 2)
    push_cast at this
    linarith
  have hG : (0 : ℝ) ≤ ∑ x ∈ Finset.range (r n + 2), g x :=
    Finset.sum_nonneg fun x _ => hg x
  have h3 : (0 : ℝ) ≤ 2 * C := by linarith
  have : 2 * C * ∑ x ∈ Finset.range (r n + 2), g x ≤ 2 * C * (K * ((r n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left h2 h3
  nlinarith [h1, this]

end SwarmOcc
