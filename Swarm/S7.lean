/-
  The spatial ergodic averages: the strong law for the ratio process (Etemadi), the
  vanishing of `h(r)/r`, the second-moment bound for the fluctuation, and the assembly
  of `H(r)/r -> (1+a)/(1-a)`.
-/
import Swarm.Imports
import Swarm.MarkTails
import Swarm.S6

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q C6 : ℝ}

/-! ### The second moment bound for the fluctuation -/

theorem Msum_sq_bound {p : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (hu6b : ∀ n, ∫ ω, (hof p ω n) ^ 6 ∂(markMeasure (boolMeasure q)) ≤ C6)
    (hC6 : 0 ≤ C6) :
    ∀ r : ℕ, Integrable (fun ω => (Msum q p r ω) ^ 2) (markMeasure (boolMeasure q)) ∧
      ∫ ω, (Msum q p r ω) ^ 2 ∂(markMeasure (boolMeasure q)) ≤ C6 * (r : ℝ) := by
  intro r
  induction r with
  | zero =>
      have h0M : (fun ω : ℕ → Bool => (Msum q p 0 ω) ^ 2) = fun _ => 0 := by
        funext ω; simp [Msum]
      refine ⟨?_, ?_⟩
      · rw [h0M]; exact integrable_zero _ _ _
      · rw [h0M]; simp
  | succ r ih =>
      obtain ⟨hI2, hB2⟩ := ih
      obtain ⟨hI2', hstep⟩ := Msum_sq_step h0 h1 hp1 hp2 hu6i hu6b hC6 r hI2
      refine ⟨hI2', ?_⟩
      push_cast
      linarith [hstep, hB2]

/-! ### The strong law for the ratio process (Etemadi) -/

theorem tendsto_xi_average {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Filter.Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, xi p ω (k + 1))
        Filter.atTop (nhds (aParam p m)) := by
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := (qpos hp2).le
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := qle_one hp1 hp2 hm
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ (m - 1))) :=
    isProbabilityMeasure_boolMeasure hq0 hq1
  set μ := markMeasure (boolMeasure ((1 - p) ^ (m - 1))) with hμ
  set X : ℕ → (ℕ → Bool) → ℝ := fun k ω => rhoOf p (ω (k + 1)) with hX
  have hindep : Pairwise (fun i j => IndepFun (X i) (X j) μ) := by
    intro i j hij
    have h := (iIndepFun_eval (μB := boolMeasure ((1 - p) ^ (m - 1)))).indepFun_finset
      ({i + 1} : Finset ℕ) {j + 1} (by simp [hij]) measurable_eval
    have hφ : Measurable (fun f : ({i + 1} : Finset ℕ) → Bool => rhoOf p (f ⟨i + 1, by simp⟩)) := by
      fun_prop
    have hψ : Measurable (fun f : ({j + 1} : Finset ℕ) → Bool => rhoOf p (f ⟨j + 1, by simp⟩)) := by
      fun_prop
    have hc := h.comp hφ hψ
    simpa [X, Function.comp_def] using hc
  have hident : ∀ k, IdentDistrib (X k) (X 0) μ μ := by
    intro k
    have hmk : Measurable (fun ω : ℕ → Bool => ω (k + 1)) := measurable_pi_apply (k + 1)
    have hm0 : Measurable (fun ω : ℕ → Bool => ω (0 + 1)) := measurable_pi_apply (0 + 1)
    have hk : μ.map (fun ω : ℕ → Bool => ω (k + 1)) = boolMeasure ((1 - p) ^ (m - 1)) := by
      rw [hμ]; unfold markMeasure
      exact Measure.infinitePi_map_eval (fun _ : ℕ => boolMeasure ((1 - p) ^ (m - 1))) (k + 1)
    have h0 : μ.map (fun ω : ℕ → Bool => ω (0 + 1)) = boolMeasure ((1 - p) ^ (m - 1)) := by
      rw [hμ]; unfold markMeasure
      exact Measure.infinitePi_map_eval (fun _ : ℕ => boolMeasure ((1 - p) ^ (m - 1))) (0 + 1)
    have hmap : μ.map (X k) = μ.map (X 0) := by
      have e1 : μ.map (X k) = (μ.map (fun ω : ℕ → Bool => ω (k + 1))).map (rhoOf p) := by
        rw [hX]
        exact (Measure.map_map (measurable_rhoOf p) hmk).symm
      have e2 : μ.map (X 0) = (μ.map (fun ω : ℕ → Bool => ω (0 + 1))).map (rhoOf p) := by
        rw [hX]
        exact (Measure.map_map (measurable_rhoOf p) hm0).symm
      rw [e1, e2, hk, h0]
    exact ⟨(measurable_rhoOf p |>.comp (measurable_pi_apply _)).aemeasurable,
      (measurable_rhoOf p |>.comp (measurable_pi_apply _)).aemeasurable, hmap⟩
  have hint : Integrable (X 0) μ := by
    refine Integrable.mono' (integrable_const (max 1 ((1 - p) / p)))
      ((measurable_rhoOf p).comp (measurable_pi_apply _)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have : |rhoOf p (ω (0 + 1))| ≤ max 1 ((1 - p) / p) := by
      rcases hb : ω (0 + 1) with _ | _
      · rw [rhoOf_false]; simp
      · rw [rhoOf_true]
        have h0' : (0:ℝ) ≤ (1 - p) / p := by positivity
        rw [abs_of_nonneg h0']
        exact le_max_right _ _
    simpa [X] using this
  have hint0 : ∫ ω, X 0 ω ∂μ = aParam p m := by
    simpa [X, xi] using integral_xi_eq_aParam hp1 hp2 hm (0 + 1)
  have h := strong_law_ae (X := X) (μ := μ) hint hindep hident
  rw [hint0] at h
  filter_upwards [h] with ω hω
  simpa only [hX, smul_eq_mul, xi] using hω

end
end SwarmSpatial
