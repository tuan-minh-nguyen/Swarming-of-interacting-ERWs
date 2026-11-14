/-
  **The `N`-walker version of (Kmom) and (maxmom).**

  The paper's displays range over the `N` walkers' mark families `(B_j)_{1<=j<=N}`, which are
  independent copies of the single-family law (`B_j` is built from the `j`-th row `U^j` of the
  uniform array).  This file puts independent copies on one probability space,
  `markMeasureN N μB = (markMeasure μB)^{⊗N}` on `Fin N → ℕ → Bool`, and transfers the
  single-family statements by the marginal law, a finite union bound (`ae_all_iff`) and a finite
  sum.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails
import Swarm.MarkMaxmom

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

/-- The joint law of `N` independent mark families. -/
def markMeasureN (N : ℕ) (μB : Measure Bool) : Measure (Fin N → ℕ → Bool) :=
  Measure.pi (fun _ : Fin N => markMeasure μB)

instance instIsProbabilityMeasureMarkMeasureN (N : ℕ) : IsProbabilityMeasure (markMeasureN N μB) := by
  unfold markMeasureN
  infer_instance

/-- The `j`-th family of `markMeasureN N μB` has law `markMeasure μB`. -/
lemma markMeasureN_marginal (N : ℕ) (j : Fin N) :
    MeasurePreserving (fun ω : Fin N → ℕ → Bool => ω j) (markMeasureN N μB) (markMeasure μB) := by
  unfold markMeasureN
  exact measurePreserving_eval (fun _ : Fin N => markMeasure μB) j

/-- Transfer of an almost-sure statement from one family to a coordinate. -/
lemma markMeasureN_ae (N : ℕ) (j : Fin N) {P : (ℕ → Bool) → Prop}
    (hP : ∀ᵐ ξ ∂(markMeasure μB), P ξ) :
    ∀ᵐ ω ∂(markMeasureN N μB), P (ω j) := by
  have hmap := markMeasureN_marginal (μB := μB) N j
  exact hmap.quasiMeasurePreserving.ae hP

/-! ### (Kmom) for all `N` families simultaneously -/

theorem hof_log_bound_N {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (N : ℕ) :
    ∀ᵐ ω ∂(markMeasureN N (boolMeasure q)), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ j : Fin N, ∀ x ≤ n + 1, hof p (ω j) x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0.le hq1
  have hsingle := hof_eventually_log_bound hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ
  have h1 : ∀ᵐ ω ∂(markMeasureN N (boolMeasure q)), ∀ j : Fin N, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ≤ n + 1, hof p (ω j) x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) :=
    (ae_all_iff (μ := markMeasureN N (boolMeasure q)) (ι := Fin N)).mpr
      (fun j => markMeasureN_ae N j hsingle)
  filter_upwards [h1] with ω hω
  rw [Filter.eventually_all]
  exact hω

/-! ### (maxmom) with the maximum over the `N` families -/

/-- `max_{j<N} max_{x<=n+1} h_j(x)`. -/
def YfunN (p : ℝ) (N n : ℕ) (hN : 0 < N) (ω : Fin N → ℕ → Bool) : ℝ :=
  (Finset.univ).sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => Yfun p n (ω j))

theorem maxmom_N {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) (hN : 0 < N) (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((1 + YfunN p N n hN ω) ^ s)
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) := by
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ (m - 1))) := by
    have hq0 : (0:ℝ) ≤ (1 - p) ^ (m - 1) := by positivity
    have hq1 : (1 - p) ^ (m - 1) ≤ 1 := by
      have := pow_one_sub_le_half hp1 hp2 hm
      linarith
    exact isProbabilityMeasure_boolMeasure hq0 hq1
  obtain ⟨C, hCpos, hC⟩ := maxmom_h hp1 hp2 hm s hs
  have hp0 : p ≠ 0 := by linarith
  refine ⟨N * C, ?_, fun n => ?_⟩
  · exact mul_pos (Nat.cast_pos.mpr hN) hCpos
  have hbase : Measurable (fun ξ : ℕ → Bool => (1 + Yfun p n ξ) ^ s) :=
    (Measurable.add measurable_const (measurable_Yfun p hp0 n)).pow_const s
  have hmeas : Measurable (fun ξ : ℕ → Bool => ENNReal.ofReal ((1 + Yfun p n ξ) ^ s)) :=
    ENNReal.measurable_ofReal.comp hbase
  have hnn' : ∀ (ξ : ℕ → Bool), (0:ℝ) ≤ (1 + Yfun p n ξ) ^ s := fun ξ =>
    pow_nonneg (by linarith [one_le_Yfun hp1.le hp2 n ξ]) s
  -- the maximum over the families is dominated by the sum
  have hpoint : ∀ ω : Fin N → ℕ → Bool, (1 + YfunN p N n hN ω) ^ s
      ≤ ∑ j : Fin N, (1 + Yfun p n (ω j)) ^ s := by
    intro ω
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin N))) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun j => Yfun p n (ω j))
    have h1 : (1 + YfunN p N n hN ω) ^ s = (1 + Yfun p n (ω j₀)) ^ s := by
      rw [YfunN, hj₀]
    rw [h1]
    exact Finset.single_le_sum (f := fun j : Fin N => (1 + Yfun p n (ω j)) ^ s)
      (fun i _ => hnn' (ω i)) (Finset.mem_univ j₀)
  calc ∫⁻ ω, ENNReal.ofReal ((1 + YfunN p N n hN ω) ^ s)
        ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
      ≤ ∫⁻ ω, ∑ j : Fin N, ENNReal.ofReal ((1 + Yfun p n (ω j)) ^ s)
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1)))) := by
        apply lintegral_mono
        intro ω
        simp only []
        refine le_trans (ENNReal.ofReal_le_ofReal (hpoint ω)) (le_of_eq ?_)
        exact ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn' (ω j))
    _ = ∑ j : Fin N, ∫⁻ ω, ENNReal.ofReal ((1 + Yfun p n (ω j)) ^ s)
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1)))) :=
        lintegral_finsetSum _ (fun j _ => hmeas.comp (measurable_pi_apply j))
    _ = ∑ _j : Fin N, ∫⁻ ξ, ENNReal.ofReal ((1 + Yfun p n ξ) ^ s)
          ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := (markMeasureN_marginal (N := N)
          (μB := boolMeasure ((1 - p) ^ (m - 1))) j).lintegral_comp hmeas
        simpa using this
    _ ≤ ∑ _j : Fin N, ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) :=
        Finset.sum_le_sum (fun j _ => hC n)
    _ = ENNReal.ofReal (N * C * (Real.log ((n : ℝ) + 2)) ^ s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

end

end SwarmMarks
