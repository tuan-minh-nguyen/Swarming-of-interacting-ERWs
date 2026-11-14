/-
  **Proposition "spatial", displays (Kmom) and (maxmom), in the paper's own parameters.**

  The preceding files prove the two displays with explicit constants `θ, γ, M`; this file
  specialises them to the paper's parameter choice `q = (1-p)^{m-1}` (the probability that a site
  is marked by `m-1` uniform coordinates exceeding `p`) and the `θ` produced by `exists_theta`,
  which is exactly what displays (Kmom) and (maxmom) of Proposition "spatial" assert for the
  potentials `h_j + G_j` of the `N` mark families `B_1, ..., B_N`.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails
import Swarm.MarkG
import Swarm.MarkN
import Swarm.MarkGN

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

/-- The contraction constant of the paper at its own mark probability `q = (1-p)^{m-1}`. -/
theorem exists_theta_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ θ : ℝ, 0 < θ ∧
      (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ) + (1 - p) ^ (m - 1) * ((1 - p) / p)
        * Real.exp (θ / p) < 1 := by
  have h0 : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have h1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have := pow_one_sub_le_half hp1 hp2 hm; linarith
  exact exists_theta hp1 hp2 h0 h1

/-- **Display (expmom) for `h_j + G_j`, uniformly in the family `j` and the site `x`.**  The
constants `c` and `C` depend only on `m` and `p`, not on `N`, exactly as the paper states. -/
theorem expmom_G {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin N) (x : ℕ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * (hof p (ω j) x + Gsup p (ω j) x)))
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal C := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]; have := pow_one_sub_le_half hp1 hp2 hm; linarith
  have hqmlt : qm < 1 := by
    rw [hqm]
    have h0 : (0:ℝ) ≤ 1 - p := by linarith
    have hlt : 1 - p < 1 := by linarith
    exact pow_lt_one₀ h0 hlt (by omega)
  obtain ⟨θ, hθ, hθ1⟩ := exists_theta_paper hp1 hp2 hm
  have hγpos : 0 < (1 - qm) * Real.exp (2 * θ) + qm * ((1 - p) / p) * Real.exp (θ / p) := by
    have h1 : 0 < 1 - qm := by linarith
    have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by
      have hr := rho_nonneg hp1 hp2
      positivity
    nlinarith [Real.exp_pos (2 * θ)]
  haveI : IsProbabilityMeasure (boolMeasure qm) := isProbabilityMeasure_boolMeasure hqm0.le hqm1
  have hMpos : 0 < momConst p qm θ ((1 - qm) * Real.exp (2 * θ)
      + qm * ((1 - p) / p) * Real.exp (θ / p)) := by
    unfold momConst
    have h1 : 0 < Real.exp (3 * θ) := Real.exp_pos _
    have h2 : 0 ≤ qm * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - ((1 - qm) * Real.exp (2 * θ)
        + qm * ((1 - p) / p) * Real.exp (θ / p))) := by
      have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
      have h3 : 0 ≤ 1 - (1 - p) / p := by linarith
      have h4 : 0 < 1 - ((1 - qm) * Real.exp (2 * θ)
          + qm * ((1 - p) / p) * Real.exp (θ / p)) := by linarith
      positivity
    linarith
  refine ⟨θ, hθ, momConst p qm θ ((1 - qm) * Real.exp (2 * θ)
    + qm * ((1 - p) / p) * Real.exp (θ / p)) * momConst p qm θ ((1 - qm) * Real.exp (2 * θ)
    + qm * ((1 - p) / p) * Real.exp (θ / p)), by positivity, ?_⟩
  intro j x
  have hmeas : Measurable (fun ξ : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * (hof p ξ x + Gsup p ξ x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_hof (by linarith : p ≠ 0) x).add (measurable_Gsup p x))))
  have hmarg := (markMeasureN_marginal (N := N) (μB := boolMeasure qm) j).lintegral_comp hmeas
  rw [hmarg]
  exact lintegral_exp_hofGsup_le hp1 hp2 hqm0.le hqm1 hθ hγpos hθ1 le_rfl x

/-- **Display (Kmom) for `h_j + G_j`.**  For `m >= 2`, `p in (1/2,1)` there is `c > 0` with

    max_{1 <= j <= N, 0 <= x <= n+1} (h_j(x) + G_j(x)) <= (3/c) log (n+2)

eventually almost surely.  The constant implicit in the `O(.)` depends on `N`, `m`, `p`. -/
theorem kmom_G {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1)))),
      ∀ᶠ n : ℕ in Filter.atTop, ∀ j : Fin N, ∀ x ≤ n + 1,
        hof p (ω j) x + Gsup p (ω j) x ≤ (3 / c) * Real.log ((n : ℝ) + 2) := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]; have := pow_one_sub_le_half hp1 hp2 hm; linarith
  have hqmlt : qm < 1 := by
    rw [hqm]
    have h0 : (0:ℝ) ≤ 1 - p := by linarith
    have hlt : 1 - p < 1 := by linarith
    exact pow_lt_one₀ h0 hlt (by omega)
  obtain ⟨θ, hθ, hθ1⟩ := exists_theta_paper hp1 hp2 hm
  refine ⟨θ, hθ, ?_⟩
  refine hofG_log_bound_N hp1 hp2 hqm0 hqm1 hθ ?_ hθ1 le_rfl N
  have h1 : 0 < 1 - qm := by linarith
  have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by
    have hr := rho_nonneg hp1 hp2
    positivity
  nlinarith [Real.exp_pos (2 * θ)]

/-- **Display (maxmom) for `h_j + G_j`.**  For `m >= 2`, `p in (1/2,1)` and `s >= 1` there is
`C_s = C_s(N,m,p) < ∞` with

    E[(1 + max_{1 <= j <= N, 0 <= x <= n+1} (h_j(x) + G_j(x)))^s] <= C_s (log (n+2))^s.

The paper's `s in {2,4}` is a special case. -/
theorem maxmom_G {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) (hN : 0 < N) (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((1 + YfunGN p N n hN ω) ^ s)
          ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) :=
  maxmom_NG hp1 hp2 hm N hN s hs

/-- The two displays of Proposition "spatial" that involve the forward potential, together. -/
theorem spatial_G {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (N : ℕ) (hN : 0 < N) :
    (∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1)))),
        ∀ᶠ n : ℕ in Filter.atTop, ∀ j : Fin N, ∀ x ≤ n + 1,
          hof p (ω j) x + Gsup p (ω j) x ≤ (3 / c) * Real.log ((n : ℝ) + 2))
    ∧ (∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        ∫⁻ ω, ENNReal.ofReal ((1 + YfunGN p N n hN ω) ^ s)
            ∂(markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
          ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s)) :=
  ⟨kmom_G hp1 hp2 hm N, fun s hs => maxmom_G hp1 hp2 hm N hN s hs⟩

end

end SwarmMarks
