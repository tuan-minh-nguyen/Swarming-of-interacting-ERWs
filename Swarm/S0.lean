/-
  Spatial ergodic averages for the marked-site potential `h_j` of Proposition "spatial"
  (`main_1d_revised.tex`, display (spav)).

  ## The route

  The paper obtains `H_j(r)/r -> (1+a)/(1-a)` from Birkhoff's ergodic theorem applied to the
  two-sided stationary version `h_j^*`.  We avoid the ergodic theorem entirely.  The recursion

      h(x) = 1 + xi(x) (1 + h(x-1)),      xi(x) = (1 - omega(x))/omega(x) in {1, (1-p)/p},

  gives, by pure algebra, the telescoping identity (`telescope` in `S1`): with
  `mk x = 1{xi(x) = rho}`,

      (1 - rho) * sum_{1 <= n <= r} mk(n) h(n-1)
          = r + sum_{1 <= n <= r} xi(n) + h(0) - h(r).

  Replacing `mk(n)` by its mean `q = (1-p)^(m-1)` leaves a fluctuation
  `M_r = sum_{n<r} (mk(n+1) - q) h(n)`, which is a sum of martingale differences with
  uniformly bounded fourth moments; a fourth-moment Chebyshev bound and Borel--Cantelli give
  `M_r/r -> 0` almost surely (`S2`).  The second term is the strong law for the i.i.d. marks
  (Etemadi, `ProbabilityTheory.strong_law_ae`), and `h(r)/r -> 0` follows from the exponential
  moment bound.  Since `q (1 - rho) = 1 - a`, the limit is `(1+a)/(1-a)` (`S3`).

  This file: the mark/ratio processes, the paper's parameters `q`, `rho`, `a`, the integral of
  the ratio process, and the uniform fourth moment of `h(x)`.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

/-! ### The mark indicator and the ratio process -/

/-- Indicator of a marked site: `1` at a marked site, `0` elsewhere. -/
def mk (ω : ℕ → Bool) (n : ℕ) : ℝ := if ω n then 1 else 0

/-- The ratio `(1 - omega)/omega` at site `n`: the paper's `xi`, equal to `rho = (1-p)/p` at a
marked site and to `1` at an unmarked one. -/
def xi (p : ℝ) (ω : ℕ → Bool) (n : ℕ) : ℝ := rhoOf p (ω n)

lemma xi_eq (p : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    xi p ω n = 1 - (1 - (1 - p) / p) * mk ω n := by
  rcases hb : ω n with _ | _
  · simp [xi, mk, rhoOf, hb]
  · simp [xi, mk, rhoOf, hb]

lemma mk_nonneg (ω : ℕ → Bool) (n : ℕ) : 0 ≤ mk ω n := by
  unfold mk; split <;> norm_num

lemma mk_le_one (ω : ℕ → Bool) (n : ℕ) : mk ω n ≤ 1 := by
  unfold mk; split <;> norm_num

lemma mk_zero_or_one (ω : ℕ → Bool) (n : ℕ) : mk ω n = 0 ∨ mk ω n = 1 := by
  unfold mk; split <;> simp

lemma measurable_mk (n : ℕ) : Measurable (fun ω : ℕ → Bool => mk ω n) := by
  have h : Measurable fun ω : ℕ → Bool => ω n := measurable_pi_apply n
  have : (fun ω : ℕ → Bool => mk ω n)
      = fun ω => if ω ∈ {ω : ℕ → Bool | ω n = true} then (1 : ℝ) else 0 := by
    funext ω; simp [mk]
  rw [this]
  exact Measurable.ite (h (measurableSet_singleton true)) measurable_const measurable_const

lemma measurable_xi (p : ℝ) (n : ℕ) : Measurable (fun ω : ℕ → Bool => xi p ω n) :=
  (measurable_rhoOf p).comp (measurable_pi_apply n)

lemma xi_of_unmarked {p : ℝ} {ω : ℕ → Bool} {n : ℕ} (h : ω n = false) : xi p ω n = 1 := by
  simp [xi, rhoOf, h]

lemma xi_of_marked {p : ℝ} {ω : ℕ → Bool} {n : ℕ} (h : ω n = true) :
    xi p ω n = (1 - p) / p := by
  simp [xi, rhoOf, h]

/-- The recursion in multiplicative form, with the mark of the *current* site. -/
lemma hof_succ_xi (p : ℝ) (hp0 : p ≠ 0) (ω : ℕ → Bool) (n : ℕ) :
    hof p ω (n + 1) = 1 + xi p ω (n + 1) * (1 + hof p ω n) := by
  rw [hof_succ, hstep_eq_rho hp0]
  rfl

/-! ### The parameters `rho`, `q`, `a` -/

/-- The paper's `a = E[(1-omega)/omega] = 1 - (2p-1)(1-p)^{m-1}/p`. -/
def aParam (p : ℝ) (m : ℕ) : ℝ := 1 - (2 * p - 1) * (1 - p) ^ (m - 1) / p

/-- The paper's limit `(1+a)/(1-a)`. -/
def targetParam (p : ℝ) (m : ℕ) : ℝ := (1 + aParam p m) / (1 - aParam p m)

/-- `a` written with `q = (1-p)^{m-1}` and `rho = (1-p)/p`: `a = 1 - q (1 - rho)`. -/
lemma aParam_eq {p : ℝ} (hp0 : p ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    aParam p m = 1 - (1 - p) ^ (m - 1) * (1 - (1 - p) / p) := by
  have h1 : 1 - (1 - p) / p = (2 * p - 1) / p := by
    rw [eq_div_iff hp0, sub_mul, one_mul, div_mul_cancel₀ _ hp0]; ring
  have h2 : (2 * p - 1) * (1 - p) ^ (m - 1) / p
      = (1 - p) ^ (m - 1) * ((2 * p - 1) / p) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  unfold aParam
  rw [h1, ← h2]

lemma one_sub_aParam {p : ℝ} (hp0 : p ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    1 - aParam p m = (1 - p) ^ (m - 1) * (1 - (1 - p) / p) := by
  rw [aParam_eq hp0 hm]; ring

lemma one_sub_rho_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) :
    0 < 1 - (1 - p) / p := by
  rw [show 1 - (1 - p) / p = (2 * p - 1) / p by
    rw [eq_div_iff (by linarith : p ≠ 0), sub_mul, one_mul, div_mul_cancel₀ _ (by linarith)]
    ring]
  exact div_pos (by linarith) (by linarith)

lemma qpos {p : ℝ} (hp2 : p < 1) {m : ℕ} : 0 < (1 - p) ^ (m - 1) := by
  have : 0 < 1 - p := by linarith
  positivity

lemma qle_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    (1 - p) ^ (m - 1) ≤ 1 :=
  pow_le_one₀ (by linarith) (by linarith)

lemma aParam_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ aParam p m := by
  have hp0 : p ≠ 0 := by linarith
  have hq1 := qle_one hp1 hp2 hm
  have hr := (one_sub_rho_pos hp1 hp2).le
  have hprod : (1 - p) ^ (m - 1) * (1 - (1 - p) / p) ≤ 1 := by
    have h1 : (1 - p) ^ (m - 1) * (1 - (1 - p) / p) ≤ 1 * 1 := by
      apply mul_le_mul hq1 _ hr (by norm_num)
      rw [show (1:ℝ) - (1 - p) / p = (2 * p - 1) / p by
        rw [eq_div_iff (by linarith : p ≠ 0), sub_mul, one_mul, div_mul_cancel₀ _ (by linarith)]
        ring]
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    simpa using h1
  rw [aParam_eq hp0 hm]
  linarith

lemma aParam_lt_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 1 ≤ m) :
    aParam p m < 1 := by
  have hp0 : p ≠ 0 := by linarith
  have hq0 : 0 < (1 - p) ^ (m - 1) := qpos hp2
  have hr := one_sub_rho_pos hp1 hp2
  rw [aParam_eq hp0 hm]
  nlinarith [mul_pos hq0 hr]

lemma one_sub_target_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) : 0 < 1 - aParam p m := by
  have := aParam_lt_one hp1 hp2 hm; linarith

/-! ### The law of the ratio process -/

lemma integral_boolMeasure {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(boolMeasure q) = q * f true + (1 - q) * f false := by
  unfold boolMeasure
  have hμ : Integrable f (ENNReal.ofReal q • Measure.dirac true) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hν : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac false) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hμ hν, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - q)]
  simp

lemma integral_eval {μB : Measure Bool} [IsProbabilityMeasure μB] (f : Bool → ℝ) (n : ℕ) :
    ∫ ω : ℕ → Bool, f (ω n) ∂(markMeasure μB) = ∫ b, f b ∂μB := by
  have hm : Measurable (fun ω : ℕ → Bool => ω n) := measurable_pi_apply n
  have hmap : (markMeasure μB).map (fun ω : ℕ → Bool => ω n) = μB := by
    unfold markMeasure; exact Measure.infinitePi_map_eval (fun _ : ℕ => μB) n
  have key := integral_map (φ := fun ω : ℕ → Bool => ω n) (μ := markMeasure μB) (f := f)
    hm.aemeasurable (by fun_prop)
  rw [hmap] at key
  exact key.symm

/-- The mean of the ratio process at any site: `E xi = (1-q) + q rho`. -/
lemma integral_xi {q p : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    ∫ ω, xi p ω n ∂(markMeasure (boolMeasure q))
      = q * ((1 - p) / p) + (1 - q) * 1 := by
  have : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have h : ∫ ω, xi p ω n ∂(markMeasure (boolMeasure q)) = ∫ b, rhoOf p b ∂(boolMeasure q) :=
    integral_eval (fun b => rhoOf p b) n
  rw [h, integral_boolMeasure h0 h1]
  simp [xi, rhoOf]

/-- **`E xi = a`** for the paper's `a`. -/
lemma integral_xi_eq_aParam {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (n : ℕ) :
    ∫ ω, xi p ω n ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) = aParam p m := by
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := (qpos hp2).le
  have hq1 := qle_one hp1 hp2 hm
  rw [integral_xi hq0 hq1 n, aParam_eq (by linarith : p ≠ 0) hm]
  ring

/-! ### The uniform fourth moment of `h(x)` -/

/-- **Uniform fourth moment.**  Derived from the exponential moment `(expmom)` of `MarkMoments`:
`x^4 <= (4!/theta^4) exp (theta x)` for `x >= 0`. -/
theorem exists_hof_pow_four_bound {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ n : ℕ,
      ∫ ω, (hof p ω n) ^ 4 ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) ≤ C4 := by
  obtain ⟨θ, hθ, C, hC, hbound⟩ := exists_exp_moment_hof hp1 hp2 hm
  refine ⟨24 / θ ^ 4 * C, by positivity, fun n => ?_⟩
  set μ := markMeasure (boolMeasure ((1 - p) ^ (m - 1))) with hμ
  have hpow : ∀ y : ℝ, 1 ≤ y → y ^ 4 ≤ 24 / θ ^ 4 * Real.exp (θ * y) := by
    intro y hy
    have hy0 : 0 ≤ θ * y := by positivity
    have h1 : (θ * y) ^ 4 / (Nat.factorial 4 : ℝ) ≤ Real.exp (θ * y) :=
      Real.pow_div_factorial_le_exp (θ * y) hy0 4
    have h2 : (θ * y) ^ 4 = θ ^ 4 * y ^ 4 := by ring
    rw [h2] at h1
    have h3 : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    rw [h3] at h1
    have hθ4 : (0:ℝ) < θ ^ 4 := by positivity
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 24)] at h1
    rw [show 24 / θ ^ 4 * Real.exp (θ * y) = 24 * Real.exp (θ * y) / θ ^ 4 from by ring]
    rw [le_div_iff₀ hθ4]
    linarith
  have hmono : ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ 4) ∂μ
      ≤ ENNReal.ofReal (24 / θ ^ 4 * C) := by
    calc ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ 4) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (24 / θ ^ 4 * Real.exp (θ * hof p ω n)) ∂μ := by
          apply lintegral_mono
          intro ω
          exact ENNReal.ofReal_le_ofReal (hpow _ (one_le_hof hp1.le hp2 ω n))
      _ = ENNReal.ofReal (24 / θ ^ 4)
            * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω n)) ∂μ := by
          have hcongr : (fun ω => ENNReal.ofReal (24 / θ ^ 4 * Real.exp (θ * hof p ω n)))
              = fun ω => ENNReal.ofReal (24 / θ ^ 4)
                  * ENNReal.ofReal (Real.exp (θ * hof p ω n)) := by
            funext ω
            exact ENNReal.ofReal_mul (by positivity)
          have hm : Measurable fun ω : ℕ → Bool => hof p ω n := measurable_hof (by linarith : p ≠ 0) n
          have hmexp : Measurable fun ω => ENNReal.ofReal (Real.exp (θ * hof p ω n)) :=
            ENNReal.measurable_ofReal.comp
              (Real.measurable_exp.comp (measurable_const.mul hm))
          rw [hcongr, lintegral_const_mul _ hmexp]
      _ ≤ ENNReal.ofReal (24 / θ ^ 4) * ENNReal.ofReal C := by
          exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)
      _ = ENNReal.ofReal (24 / θ ^ 4 * C) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hlt : ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ 4) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmono
  have hmeas : AEStronglyMeasurable (fun ω => (hof p ω n) ^ 4) μ :=
    ((measurable_hof (by linarith : p ≠ 0) n).pow_const 4).aestronglyMeasurable
  have hae : 0 ≤ᵐ[μ] fun ω => (hof p ω n) ^ 4 := Filter.Eventually.of_forall fun _ => by positivity
  have hint : Integrable (fun ω => (hof p ω n) ^ 4) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hae).mp hlt
  have hone : ENNReal.ofReal (∫ ω, (hof p ω n) ^ 4 ∂μ)
      = ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ 4) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hint hae
  rw [← hone] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmono

end
end SwarmSpatial
