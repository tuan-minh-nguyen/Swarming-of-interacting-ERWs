/-
  **Display (expmom) for `h_j(x) + G_j(x)`** — the combination used in Proposition "spatial".

  The potential `h(x)` depends only on the marks at the sites `0, …, x`, while
  `G(x) = 1 + sum_{l>=1} prod_{u=1}^{l} rho(x+u)` depends only on the marks at the sites
  `x+1, x+2, …`.  These mark families are independent, so

      E exp (θ (h(x) + G(x))) = E exp (θ h(x)) · E exp (θ G(x)) ≤ M²,

  with the *same* `θ` and `M` as for `h` and `G` separately.  This file proves the independence
  (past marks against future marks), the factorisation and the passage to the limit.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails
import Swarm.MarkFuture

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

/-- **Past marks are independent of future marks**: the tuple of the marks at the sites
`0, …, x` is independent of the tuple of the marks at the sites `x+1, …, x+N`. -/
lemma indep_mark_past_future (x N : ℕ) :
    IndepFun (fun ω : ℕ → Bool => fun i : Fin (x + 1) => ω i)
      (fun ω => fun i : Fin N => ω (x + 1 + i)) (markMeasure μB) := by
  classical
  set T : Finset ℕ := (Finset.range N).image (fun i => x + 1 + i) with hT
  have hdisj : Disjoint (Finset.range (x + 1)) T := by
    rw [hT]
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_image, not_exists, not_and]
    intro i hi j hj h
    omega
  have h0 := (iIndepFun_eval (μB := μB)).indepFun_finset (Finset.range (x + 1)) T hdisj
    measurable_eval
  have hφ : Measurable (fun g : (Finset.range (x + 1)) → Bool =>
      fun i : Fin (x + 1) => g ⟨i.val, Finset.mem_range.mpr i.isLt⟩) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_apply _
  have hψ : Measurable (fun g : T → Bool => fun i : Fin N => g ⟨x + 1 + i, by
      rw [hT]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, rfl⟩⟩) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_apply _
  have h1 := h0.comp hφ hψ
  have e1 : ((fun g : (Finset.range (x + 1)) → Bool =>
        fun i : Fin (x + 1) => g ⟨i.val, Finset.mem_range.mpr i.isLt⟩) ∘
      fun (b : ℕ → Bool) (i : (Finset.range (x + 1))) => b (i : ℕ))
      = fun ω : ℕ → Bool => fun i : Fin (x + 1) => ω i := by
    funext ω i
    simp
  have e2 : ((fun g : T → Bool => fun i : Fin N => g ⟨x + 1 + i, by
        rw [hT]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, rfl⟩⟩) ∘
      fun (b : ℕ → Bool) (i : T) => b (i : ℕ))
      = fun ω : ℕ → Bool => fun i : Fin N => ω (x + 1 + i) := by
    funext ω i
    simp
  rw [e1, e2] at h1
  exact h1

/-- The past potential `h(x)` is independent of the truncated future potential `G_N(x+1)`. -/
lemma indep_hof_Gtrunc (p : ℝ) (hp0 : p ≠ 0) (x N : ℕ) :
    IndepFun (fun ω : ℕ → Bool => hof p ω x)
      (fun ω => Gtrunc p ω N (x + 1)) (markMeasure μB) := by
  have h := (indep_mark_past_future (μB := μB) x N).comp (measurable_Hfun hp0 x)
    (measurable_Gv p N)
  have e1 : (Hfun p x ∘ fun ω : ℕ → Bool => fun i : Fin (x + 1) => ω i)
      = fun ω => hof p ω x := by
    funext ω
    exact (hof_eq_Hfun p x ω).symm
  have e2 : ((Gv p N) ∘ fun ω : ℕ → Bool => fun i : Fin N => ω (x + 1 + i))
      = fun ω => Gtrunc p ω N (x + 1) := by
    funext ω
    simp only [Function.comp, Gtrunc, Nat.add_assoc]
  rw [e1, e2] at h
  exact h

/-- **The exponential moment of `h(x) + G_N(x)`**: the product of the two bounds. -/
theorem lintegral_exp_hG_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1))))
        ∂(markMeasure (boolMeasure q))
      ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hp0 : p ≠ 0 := by linarith
  have hind : IndepFun (fun ω : ℕ → Bool => hof p ω x)
      (fun ω => Gtrunc p ω N (x + 1)) (markMeasure (boolMeasure q)) :=
    indep_hof_Gtrunc p hp0 x N
  have hmeasA : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * hof p ω x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_hof hp0 x)))
  have hmeasB : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_Gtrunc p N (x + 1))))
  have hprod : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1))))
        ∂(markMeasure (boolMeasure q))
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x)) ∂(markMeasure (boolMeasure q)))
        * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))
            ∂(markMeasure (boolMeasure q)) := by
    have hfac : ∀ ω : ℕ → Bool,
        ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1))))
          = ENNReal.ofReal (Real.exp (θ * hof p ω x))
            * ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1))) := by
      intro ω
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    simp only [hfac]
    have hφ : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (θ * y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
    exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hmeasA hmeasB
      (hind.comp hφ hφ)
  rw [hprod]
  have hA := lintegral_exp_hof_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x
  have hB := lintegral_exp_Gtrunc_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ N (x + 1)
  have hMnn : (0:ℝ≥0∞) ≤ ENNReal.ofReal (momConst p q θ γ) := by simp
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x)) ∂(markMeasure (boolMeasure q)))
        * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))
            ∂(markMeasure (boolMeasure q))
      ≤ ENNReal.ofReal (momConst p q θ γ) * ENNReal.ofReal (momConst p q θ γ) :=
        mul_le_mul hA hB (by simp) hMnn
    _ = ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ) :=
        (ENNReal.ofReal_mul (momConst_nonneg hp1 hp2 hq0 hγ1)).symm

/-- **Display (expmom) for `h + G`.**  For every site `x`, the exponential moment of
`h(x) + G(x)` (the limit of the truncations) is at most `M²`, with `θ = θ(m,p)` and
`M = M(m,p)` from the separate `h` and `G` bounds. -/
theorem lintegral_exp_hG_sup_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x : ℕ) :
    ∫⁻ ω, (⨆ N, ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1)))))
        ∂(markMeasure (boolMeasure q))
      ≤ ENNReal.ofReal (momConst p q θ γ * momConst p q θ γ) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hp0 : p ≠ 0 := by linarith
  have hmeas : ∀ N, Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1))))) := by
    intro N
    have hsum : Measurable (fun ω : ℕ → Bool => hof p ω x + Gtrunc p ω N (x + 1)) :=
      (measurable_hof hp0 x).add (measurable_Gtrunc p N (x + 1))
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hsum))
  have hmono : Monotone (fun N => fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1))))) := by
    intro N N' hNN' ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hle : Gtrunc p ω N (x + 1) ≤ Gtrunc p ω N' (x + 1) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNN'
      clear hNN'
      induction d with
      | zero => simp
      | succ k ih =>
          rw [show N + (k + 1) = (N + k) + 1 by ring]
          exact ih.trans (Gtrunc_mono hp1 hp2 ω (N + k) (x + 1))
    nlinarith [hθ, hle]
  rw [lintegral_iSup hmeas hmono]
  exact iSup_le fun N => lintegral_exp_hG_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x N

/-- **Display (expmom), combined form.**  For every `m ≥ 2` and `p ∈ (1/2,1)` there are
`θ = θ(m,p) > 0` and `C = C(m,p) < ∞` such that, on the i.i.d. Bernoulli`((1-p)^{m-1})`
site-mark space, for every site `x`,

    ∫⁻ ⨆_N exp (θ (h(x) + G_N(x))) dP ≤ C,

i.e. `E exp (θ (h_j(x) + G_j(x))) ≤ C` for the paper's `h_j` and `G_j`, with `θ, C` depending
only on `m` and `p`. -/
theorem exists_exp_moment_hG {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ,
      ∫⁻ ω, (⨆ N, ENNReal.ofReal
          (Real.exp (θ * (hof p ω x + Gtrunc p ω N (x + 1)))))
        ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) ≤ ENNReal.ofReal C := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by
    rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]
    have := pow_one_sub_le_half hp1 hp2 hm
    linarith
  obtain ⟨θ, hθpos, hθc⟩ := exists_theta hp1 hp2 hqm0 (by linarith)
  set γm : ℝ := (1 - qm) * Real.exp (2 * θ) + qm * ((1 - p) / p) * Real.exp (θ / p) with hγm
  have hγm1 : γm < 1 := hθc
  have hγmpos : 0 < γm := by
    have hqlt : qm < 1 := by
      rw [hqm]
      have h0 : (0:ℝ) ≤ 1 - p := by linarith
      have hlt : 1 - p < 1 := by linarith
      exact pow_lt_one₀ h0 hlt (by omega)
    have hr := rho_nonneg hp1 hp2
    have h1 : 0 < 1 - qm := by linarith
    have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by positivity
    rw [hγm]
    nlinarith [Real.exp_pos (2 * θ)]
  refine ⟨θ, hθpos, momConst p qm θ γm * momConst p qm θ γm, ?_, ?_⟩
  · have hM : 0 < momConst p qm θ γm := by
      unfold momConst
      have h1 : 0 < Real.exp (3 * θ) := Real.exp_pos _
      have h2 : 0 ≤ qm * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γm) := by
        have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
        have h3 : 0 ≤ 1 - (1 - p) / p := by linarith
        have h4 : 0 < 1 - γm := by linarith
        positivity
      linarith
    nlinarith
  · intro x
    exact lintegral_exp_hG_sup_le hp1 hp2 hqm0.le hqm1 hθpos hγmpos hγm1 hγm.symm.le x

end

end SwarmMarks
