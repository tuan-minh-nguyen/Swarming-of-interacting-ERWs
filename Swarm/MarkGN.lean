/-
  **The `N`-walker version of the `G`-part of (Kmom) and (maxmom).**

  The paper's displays range over the `N` mark families `(B_j)_{1<=j<=N}`, which are the `N` rows
  of the uniform array and hence independent copies of the single-family law.  With the joint law
  `markMeasureN N μB` of `MarkN.lean` this file transfers the single-family statements of
  `MarkG.lean` to the maximum over the `N` families:

      max_{1<=j<=N, 0<=x<=n+1} (h_j(x) + G_j(x)) = O (log (n+2))                  a.s.   (Kmom)
      E [(1 + max_{1<=j<=N, 0<=x<=n+1} (h_j(x) + G_j(x)))^s] <= C_s (log (n+2))^s        (maxmom)

  The constant `C_s` of (maxmom) depends on `N` linearly, as in the paper's union bound.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails
import Swarm.MarkG
import Swarm.MarkN

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

/-! ### (Kmom) for all `N` families simultaneously -/

theorem hofG_log_bound_N {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (N : ℕ) :
    ∀ᵐ ω ∂(markMeasureN N (boolMeasure q)), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ j : Fin N, ∀ x ≤ n + 1,
        hof p (ω j) x + Gsup p (ω j) x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0.le hq1
  have hsingle := hofG_eventually_log_bound hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ
  have h1 : ∀ᵐ ω ∂(markMeasureN N (boolMeasure q)), ∀ j : Fin N, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ≤ n + 1, hof p (ω j) x + Gsup p (ω j) x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) :=
    (ae_all_iff (μ := markMeasureN N (boolMeasure q)) (ι := Fin N)).mpr
      (fun j => markMeasureN_ae N j hsingle)
  filter_upwards [h1] with ω hω
  rw [Filter.eventually_all]
  exact hω

/-! ### (maxmom) with the maximum over the `N` families -/

/-- `max_{j<N} max_{x<=n+1} (h_j(x) + G_j(x))`. -/
def YfunGN (p : ℝ) (N n : ℕ) (hN : 0 < N) (ω : Fin N → ℕ → Bool) : ℝ :=
  (Finset.univ).sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => YfunG p n (ω j))

theorem maxmom_NG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) (hN : 0 < N) (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((1 + YfunGN p N n hN ω) ^ s)
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]; have := pow_one_sub_le_half hp1 hp2 hm; linarith
  haveI : IsProbabilityMeasure (boolMeasure qm) := isProbabilityMeasure_boolMeasure hqm0.le hqm1
  obtain ⟨C, hCpos, hC⟩ := maxmom_hG hp1 hp2 hm s hs
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨θ, hθpos, hθc⟩ := exists_theta hp1 hp2 hqm0 (by linarith)
  set γm : ℝ := (1 - qm) * Real.exp (2 * θ) + qm * ((1 - p) / p) * Real.exp (θ / p) with hγm
  have hγm1 : γm < 1 := hθc
  have hγmpos : 0 < γm := by
    have hqlt : qm < 1 := by
      rw [hqm]
      have h0 : (0:ℝ) ≤ 1 - p := by linarith
      have hlt : 1 - p < 1 := by linarith
      exact pow_lt_one₀ h0 hlt (by omega)
    have h1 : 0 < 1 - qm := by linarith
    have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by positivity
    rw [hγm]
    nlinarith [Real.exp_pos (2 * θ)]
  have hbdd := bddAbove_range_Gtrunc_ae (q := qm) (θ := θ) (γ := γm)
    hp1 hp2 hqm0.le hqm1 hθpos hγmpos hγm1 hγm.symm.le
  -- the same statement for every family, simultaneously
  have hbddN : ∀ᵐ ω ∂(markMeasureN N (boolMeasure qm)), ∀ j : Fin N, ∀ x : ℕ,
      BddAbove (Set.range fun N => Gtrunc p (ω j) N (x + 1)) :=
    (ae_all_iff (μ := markMeasureN N (boolMeasure qm)) (ι := Fin N)).mpr
      (fun j => markMeasureN_ae N j hbdd)
  refine ⟨N * C, ?_, fun n => ?_⟩
  · exact mul_pos (Nat.cast_pos.mpr hN) hCpos
  have hbase : Measurable (fun ξ : ℕ → Bool => (1 + YfunG p n ξ) ^ s) :=
    (Measurable.add measurable_const (measurable_YfunG p hp0 n)).pow_const s
  have hmeas : Measurable (fun ξ : ℕ → Bool => ENNReal.ofReal ((1 + YfunG p n ξ) ^ s)) :=
    ENNReal.measurable_ofReal.comp hbase
  -- nonnegativity of the summands, almost surely
  have hnn_ae : ∀ᵐ ω ∂(markMeasureN N (boolMeasure qm)), ∀ j : Fin N,
      (0:ℝ) ≤ (1 + YfunG p n (ω j)) ^ s := by
    filter_upwards [hbddN] with ω hb
    intro j
    apply pow_nonneg
    have h2 : 1 ≤ hof p (ω j) 0 + Gsup p (ω j) 0 := by
      have h3 := one_le_hof hp1.le hp2 (ω j) 0
      have h4 := one_le_Gsup hp1 hp2 (ω j) 0 (hb j 0)
      linarith
    linarith [one_le_YfunG hp1 hp2 n (ω j) h2]
  -- the maximum over the families is dominated by the sum
  have hpoint : ∀ᵐ ω ∂(markMeasureN N (boolMeasure qm)), (1 + YfunGN p N n hN ω) ^ s
      ≤ ∑ j : Fin N, (1 + YfunG p n (ω j)) ^ s := by
    filter_upwards [hnn_ae] with ω hnn
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin N))) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun j => YfunG p n (ω j))
    have h1 : (1 + YfunGN p N n hN ω) ^ s = (1 + YfunG p n (ω j₀)) ^ s := by
      rw [YfunGN, hj₀]
    rw [h1]
    exact Finset.single_le_sum (f := fun j : Fin N => (1 + YfunG p n (ω j)) ^ s)
      (fun i _ => hnn i) (Finset.mem_univ j₀)
  calc ∫⁻ ω, ENNReal.ofReal ((1 + YfunGN p N n hN ω) ^ s)
        ∂(markMeasureN N (boolMeasure qm))
      ≤ ∫⁻ ω, ∑ j : Fin N, ENNReal.ofReal ((1 + YfunG p n (ω j)) ^ s)
          ∂(markMeasureN N (boolMeasure qm)) := by
        apply lintegral_mono_ae
        filter_upwards [hpoint, hnn_ae] with ω hω hnn
        refine le_trans (ENNReal.ofReal_le_ofReal hω) (le_of_eq ?_)
        exact ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j)
    _ = ∑ j : Fin N, ∫⁻ ω, ENNReal.ofReal ((1 + YfunG p n (ω j)) ^ s)
          ∂(markMeasureN N (boolMeasure qm)) :=
        lintegral_finsetSum _ (fun j _ => hmeas.comp (measurable_pi_apply j))
    _ = ∑ _j : Fin N, ∫⁻ ξ, ENNReal.ofReal ((1 + YfunG p n ξ) ^ s)
          ∂(markMeasure (boolMeasure qm)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := (markMeasureN_marginal (N := N) (μB := boolMeasure qm) j).lintegral_comp hmeas
        simpa using this
    _ ≤ ∑ _j : Fin N, ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) :=
        Finset.sum_le_sum (fun j _ => hC n)
    _ = ENNReal.ofReal (N * C * (Real.log ((n : ℝ) + 2)) ^ s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

end

end SwarmMarks
