/-
  **`locsum`, layer A2: the deterministic block interpolation and the interval bound.**

  On the good event of a window every `n*k`-site block of the partition has truncated square
  sum at most `C*(n*k)`.  This file proves the paper's deterministic passage from blocks to
  *arbitrary* intervals:

  * `sum_fin_residue`: the `k` residue classes of an `n*k`-site block add up to the whole block
    (so the residue-class form of `LocSum.block_concentration` is a block sum);
  * `sum_Ico_blocks_le`: consecutive full blocks add up;
  * `interval_bound_of_blocks`: for every `[a0,b0) ⊆ [A, A+L)`, `Σ f ≤ C*(b0-a0) + 2*C*β`,
    where `β = n*k` is the block length and the `T` blocks cover the window (`L ≤ T*β`).
    (The paper's boundary term `2b·max h^*` is replaced by the same `2β` slack absorbed into
    the block constant, which is exactly the paper's "after increasing C" step.)
-/
import Swarm.A1ArrayBlock

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- **Residue classes of a block.**  Summing over the `k` residue classes mod `k` of the
`n*k`-site block `[a0, a0+n*k)` is summing over the block. -/
lemma sum_fin_residue (g : ℕ → ℝ) (a0 k n : ℕ) :
    ∑ r : Fin k, ∑ i : Fin n, g (a0 + r.1 + i.1 * k)
      = ∑ x ∈ Finset.Ico a0 (a0 + n * k), g x := by
  have h1 : ∑ r : Fin k, ∑ i : Fin n, g (a0 + r.1 + i.1 * k)
      = ∑ q : Fin n × Fin k, g (a0 + q.2.1 + q.1.1 * k) := by
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  have h2 : ∑ q : Fin n × Fin k, g (a0 + q.2.1 + q.1.1 * k)
      = ∑ x : Fin (n * k), g (a0 + (x : ℕ)) := by
    rw [← Equiv.sum_comp (finProdFinEquiv (m := n) (n := k))
      (fun x : Fin (n * k) => g (a0 + (x : ℕ)))]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hv : ((finProdFinEquiv q : Fin (n * k)) : ℕ) = q.2.1 + k * q.1.1 := by
      simp [finProdFinEquiv]
    rw [hv]
    have hm : q.1.1 * k = k * q.1.1 := Nat.mul_comm _ _
    rw [hm, Nat.add_assoc]
  have h3 : (∑ x : Fin (n * k), g (a0 + (x : ℕ)))
      = ∑ x ∈ Finset.Ico a0 (a0 + n * k), g x := by
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_Ico_eq_sum_range (f := g) (m := a0) (n := a0 + n * k)]
    rw [show a0 + n * k - a0 = n * k from by omega]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [dif_pos (Finset.mem_range.mp hx)]
  rw [h1, h2, h3]

/-- **Consecutive blocks add up.**  If every block `t < T` of the window has `f`-sum at most
`C*β`, then the sum over the consecutive blocks `[s, t)` (all inside the window) is at most
`C*((t-s)*β)`. -/
lemma sum_Ico_blocks_le (f : ℕ → ℝ) (A β : ℕ) {C : ℝ} {T : ℕ}
    (hblocks : ∀ t, t < T → ∑ x ∈ Finset.Ico (A + t * β) (A + (t + 1) * β), f x ≤ C * β) :
    ∀ t : ℕ, t ≤ T → ∀ s : ℕ, s ≤ t →
      ∑ x ∈ Finset.Ico (A + s * β) (A + t * β), f x ≤ C * (((t : ℝ) - (s : ℝ)) * β) := by
  intro t
  induction t with
  | zero =>
    intro _ s hs
    have hs0 : s = 0 := Nat.le_zero.mp hs
    subst hs0
    simp
  | succ t ih =>
    intro htT s hs
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst : s ≤ t := by omega
      have htT' : t ≤ T := by omega
      have hb := hblocks t (by omega)
      have hm1 : s * β ≤ t * β := Nat.mul_le_mul_right β hst
      have hm2 : t * β ≤ (t + 1) * β := Nat.mul_le_mul_right β (Nat.le_succ t)
      have hsplit := Finset.sum_Ico_consecutive f (m := A + s * β) (n := A + t * β)
        (k := A + (t + 1) * β) (Nat.add_le_add_left hm1 A) (Nat.add_le_add_left hm2 A)
      have hih := ih htT' s hst
      have hcast : ((↑(t + 1) : ℝ) - (s : ℝ)) = ((t : ℝ) - (s : ℝ)) + 1 := by
        push_cast [Nat.cast_sub hst]
        ring
      have hb2 : ∑ x ∈ Finset.Ico (A + t * β) (A + (t * β + β)), f x ≤ C * β := by
        simpa only [Nat.succ_mul] using hb
      rw [hsplit.symm, hcast, add_mul, one_mul]
      linarith
    · have hse : s = t + 1 := by omega
      subst hse
      simp

/-- **The deterministic block interpolation.**  If every block of the window has `f`-sum at
most `C*β`, `f ≥ 0`, and `L ≤ T*β` (the `T` blocks cover the window), then every interval
`[a0,b0) ⊆ [A, A+L)` has `f`-sum at most `C*(b0-a0) + 2*C*β`. -/
lemma interval_bound_of_blocks {f : ℕ → ℝ} {A L β : ℕ} (hβ : 1 ≤ β) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, 0 ≤ f x) {T : ℕ} (hTL : L ≤ T * β)
    (hblocks : ∀ t, t < T → ∑ x ∈ Finset.Ico (A + t * β) (A + (t + 1) * β), f x ≤ C * β)
    {a0 b0 : ℕ} (ha : A ≤ a0) (hb : b0 ≤ A + L) (hab : a0 ≤ b0) :
    ∑ x ∈ Finset.Ico a0 b0, f x ≤ C * ((b0 : ℝ) - (a0 : ℝ)) + 2 * C * β := by
  have hβpos : 0 < β := hβ
  rcases Nat.eq_or_lt_of_le hab with heq | hlt
  · subst heq
    simp only [Finset.Ico_self, Finset.sum_empty, Nat.cast_sub le_rfl, sub_self, mul_zero,
      zero_add]
    have : (0 : ℝ) ≤ 2 * C * β := by positivity
    exact this
  · obtain ⟨t0, ht0⟩ : ∃ t0, t0 = (a0 - A) / β := ⟨_, rfl⟩
    obtain ⟨t1, ht1⟩ : ∃ t1, t1 = (b0 - 1 - A) / β := ⟨_, rfl⟩
    have hstart : A + t0 * β ≤ a0 := by
      rw [ht0]
      have h := Nat.div_mul_le_self (a0 - A) β
      omega
    have hstart' : a0 < A + (t0 + 1) * β := by
      rw [ht0]
      have h2 : (a0 - A) % β < β := Nat.mod_lt _ hβpos
      have h3 : β * ((a0 - A) / β) + (a0 - A) % β = a0 - A := Nat.div_add_mod _ _
      have h4 : (a0 - A) / β * β = β * ((a0 - A) / β) := Nat.mul_comm _ _
      have h5 : a0 - A < ((a0 - A) / β + 1) * β := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hend : A + t1 * β ≤ b0 - 1 := by
      rw [ht1]
      have h := Nat.div_mul_le_self (b0 - 1 - A) β
      omega
    have hend' : b0 ≤ A + (t1 + 1) * β := by
      rw [ht1]
      have h2 : (b0 - 1 - A) % β < β := Nat.mod_lt _ hβpos
      have h3 : β * ((b0 - 1 - A) / β) + (b0 - 1 - A) % β = b0 - 1 - A := Nat.div_add_mod _ _
      have h4 : (b0 - 1 - A) / β * β = β * ((b0 - 1 - A) / β) := Nat.mul_comm _ _
      have h5 : b0 - 1 - A < ((b0 - 1 - A) / β + 1) * β := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [Nat.add_mul, Nat.one_mul] at h5 ⊢
      omega
    have ht0t1 : t0 ≤ t1 := by
      rw [ht0, ht1]
      have : a0 - A ≤ b0 - 1 - A := by omega
      exact Nat.div_le_div_right this
    have ht1T : t1 < T := by
      rw [ht1]
      have h1 : (b0 - 1 - A) / β ≤ (L - 1) / β := by
        refine Nat.div_le_div_right ?_
        omega
      have h2 : (L - 1) / β + 1 ≤ T := by
        have h3 : (L - 1) / β < T := by
          rw [Nat.div_lt_iff_lt_mul hβpos]
          omega
        omega
      omega
    have hsub : ∑ x ∈ Finset.Ico a0 b0, f x
        ≤ ∑ x ∈ Finset.Ico (A + t0 * β) (A + (t1 + 1) * β), f x := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        simp only [Finset.mem_Ico] at hx ⊢
        omega
      · intro x _ _
        exact hf x
    have hgroup : ∑ x ∈ Finset.Ico (A + t0 * β) (A + (t1 + 1) * β), f x
        ≤ C * ((((t1 + 1 : ℕ) : ℝ) - (t0 : ℝ)) * β) :=
      sum_Ico_blocks_le f A β (C := C) (T := T) hblocks (t1 + 1) (by omega) t0 (by omega)
    have hlen : ((((t1 + 1 : ℕ) : ℝ) - (t0 : ℝ)) * β) ≤ ((b0 : ℝ) - (a0 : ℝ)) + 2 * β := by
      have hcast1 : ((t1 + 1 : ℕ) : ℝ) = (t1 : ℝ) + 1 := by push_cast; ring
      rw [hcast1]
      have hb0 : 1 ≤ b0 := by omega
      have hβ' : (0 : ℝ) ≤ β := by positivity
      -- real forms of the three block-index bounds
      have hstartR : (A : ℝ) + (t0 : ℝ) * β ≤ (a0 : ℝ) := by
        have h : ((A + t0 * β : ℕ) : ℝ) ≤ ((a0 : ℕ) : ℝ) := by exact_mod_cast hstart
        push_cast at h
        linarith
      have hstartR' : (a0 : ℝ) < (A : ℝ) + ((t0 : ℝ) + 1) * β := by
        have h : ((a0 : ℕ) : ℝ) < ((A + (t0 + 1) * β : ℕ) : ℝ) := by exact_mod_cast hstart'
        push_cast at h
        linarith
      have hendR : (A : ℝ) + (t1 : ℝ) * β ≤ (b0 : ℝ) - 1 := by
        have h : ((A + t1 * β : ℕ) : ℝ) ≤ ((b0 - 1 : ℕ) : ℝ) := by exact_mod_cast hend
        push_cast [Nat.cast_sub hb0] at h
        linarith
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t0) hβ']
    nlinarith

end

end LocSumAct
