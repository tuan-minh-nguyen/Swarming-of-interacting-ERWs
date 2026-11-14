/-
  **`locsum`, layer 5: the union over the residue classes of a block.**

  A block of `n*k` consecutive sites `[a0, a0+n*k)` splits into the `k` residue classes
  `{a0 + r + j*k : j < n}`.  `residue_concentration` bounds each class; the `k`-fold union
  bound gives the paper's block estimate with per-class threshold `C*n` and total threshold
  `C*(n*k)`.
-/
import Swarm.Imports
import Swarm.L4Indep

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LocSum

noncomputable section

open SwarmMarks SwarmSpatial

/-- **The block concentration bound.**  For `a0 >= k >= 1`, `n >= 1` and any `C >= M`, the
probability that the sum of `Q^2` over the `n*k` sites of the block `[a0, a0+n*k)` exceeds
`C*n*k` is at most `k * exp (-(n(C-M))^2 / (2 n c))`, `c = subGnn k`. -/
theorem block_concentration {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {n k a0 : ℕ} (hk : 1 ≤ k)
    (ha : k ≤ a0) {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q)
    {C : ℝ} (hCM : Mb p q ≤ C) :
    (markMeasure (boolMeasure q))
        {ω : ℕ → Bool | C * ((n : ℝ) * (k : ℝ))
          ≤ ∑ r : Fin k, ∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2}
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - Mb p q)) ^ 2)
            / (2 * ((∑ _j : Fin n, subGnn k : ℝ≥0) : ℝ)))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  have hCM0 : 0 ≤ C - Mb p q := by linarith [le_trans (one_le_Mb (p := p) (q := q)) hCM]
  have hsub : {ω : ℕ → Bool | C * ((n : ℝ) * (k : ℝ))
        ≤ ∑ r : Fin k, ∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2}
      ⊆ ⋃ r : Fin k, {ω : ℕ → Bool | (n : ℝ) * (C - Mb p q)
          ≤ ∑ j : Fin n, ((Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
            - ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2 ∂(markMeasure (boolMeasure q)))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hcon
    have hFr : ∀ r : Fin k,
        (∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2) < C * (n : ℝ) := by
      intro r
      have hmom : ∀ j : Fin n, ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
          ∂(markMeasure (boolMeasure q)) ≤ Mb p q := by
        intro j
        exact integral_Q_sq_le h0 h1 hp1 hp2 hq k _ (by
          have : (0 : ℕ) ≤ j.1 * k := Nat.zero_le _
          omega)
      have hsum_le : (∑ j : Fin n, ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
          ∂(markMeasure (boolMeasure q))) ≤ (n : ℝ) * Mb p q := by
        have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hmom j)
        simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
      have hexp : (∑ j : Fin n, ((Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
            - ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2 ∂(markMeasure (boolMeasure q))))
          = (∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2) - _root_.Finset.sum
              Finset.univ (fun j : Fin n => ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
                ∂(markMeasure (boolMeasure q))) := by
        rw [Finset.sum_sub_distrib]
      have hlt := hcon r
      rw [hexp] at hlt
      nlinarith [hsum_le]
    have hstrict : (∑ r : Fin k, ∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2)
        < ∑ _r : Fin k, C * (n : ℝ) :=
      Finset.sum_lt_sum (fun r _ => le_of_lt (hFr r))
        ⟨⟨0, hk⟩, Finset.mem_univ _, hFr ⟨0, hk⟩⟩
    have hrhs : (∑ _r : Fin k, C * (n : ℝ)) = C * ((n : ℝ) * (k : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hrhs] at hstrict
    exact absurd hω (not_le.2 hstrict)
  calc (markMeasure (boolMeasure q))
        {ω : ℕ → Bool | C * ((n : ℝ) * (k : ℝ))
          ≤ ∑ r : Fin k, ∑ j : Fin n, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2}
      ≤ (markMeasure (boolMeasure q))
          (⋃ r : Fin k, {ω : ℕ → Bool | (n : ℝ) * (C - Mb p q)
            ≤ ∑ j : Fin n, ((Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
              - ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
                  ∂(markMeasure (boolMeasure q)))} ) := measure_mono hsub
    _ ≤ ∑ r : Fin k, (markMeasure (boolMeasure q))
          {ω : ℕ → Bool | (n : ℝ) * (C - Mb p q)
            ≤ ∑ j : Fin n, ((Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
              - ∫ ω, (Q p k (a0 + r.1 + j.1 * k) ω) ^ 2
                  ∂(markMeasure (boolMeasure q)))} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _r : Fin k, ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - Mb p q)) ^ 2)
            / (2 * ((∑ _j : Fin n, subGnn k : ℝ≥0) : ℝ)))) := by
      refine Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => ?_)
      have hk' : k ≤ a0 + r.1 := by omega
      have hreal := residue_concentration h0 h1 (n := n) (k := k) (a0 := a0) (r := r.1)
        hk hk' hp1 hp2 (ε := (n : ℝ) * (C - Mb p q)) (by positivity)
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le]
      exact hreal
    _ = (k : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (- (((n : ℝ) * (C - Mb p q)) ^ 2)
            / (2 * ((∑ _j : Fin n, subGnn k : ℝ≥0) : ℝ)))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end LocSum
