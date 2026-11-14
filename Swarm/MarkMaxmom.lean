/-
  **Display (maxmom)** of Proposition "spatial":  `E[(1 + max_{x<=n+1} h(x))^s] <= C_s (log(n+2))^s`.

  The paper proves this by Markov's inequality followed by integrating the tail bound.  Here we
  use the equivalent two-term splitting: for `Y = max_{x<=n+1} h(x)`, `U = (4/θ) log(n+2)` and
  `C_c` such that `(1+y)^s <= C_c e^{θy/2}` for all `y >= 0` (`poly_le_exp`),

      (1+Y)^s <= (1+U)^s + C_c e^{-θU/2} e^{θY},

  integrate, use `E e^{θY} <= (n+2) M` (the union bound over the `n+2` sites), and note that
  `e^{-θU/2} = (n+2)^{-2}` cancels the factor `n+2`.
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

/-! ### Polynomials are dominated by exponentials -/

theorem poly_le_exp (s : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 ≤ y → (1 + y) ^ s ≤ C * Real.exp (a * y / 2) := by
  refine ⟨2 ^ s + 2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1), ?_, ?_⟩
  · have h1 : (0:ℝ) < (a / 2) ^ (s + 1) := by positivity
    have h4 : 0 ≤ 2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1) :=
      div_nonneg (by positivity) h1.le
    have h2 : (0:ℝ) < 2 ^ s := by positivity
    linarith
  intro y hy
  set C : ℝ := 2 ^ s + 2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1) with hC
  have h2s : (0:ℝ) < 2 ^ s := by positivity
  have ha2 : (0:ℝ) < (a / 2) ^ (s + 1) := by positivity
  have hfact : (0:ℝ) < ((s + 1).factorial : ℝ) := by positivity
  have hCge : (2:ℝ) ^ s ≤ C := by
    have h4 : 0 ≤ 2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1) :=
      div_nonneg (by positivity) ha2.le
    rw [hC]; linarith
  have hexp1 : (1:ℝ) ≤ Real.exp (a * y / 2) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ a * y / 2 := by positivity
    linarith
  rcases le_or_gt y 1 with h1 | h1
  · have hy2 : (1 + y) ^ s ≤ 2 ^ s := pow_le_pow_left₀ (by linarith) (by linarith) s
    calc (1 + y) ^ s ≤ 2 ^ s := hy2
      _ = 2 ^ s * 1 := by ring
      _ ≤ 2 ^ s * Real.exp (a * y / 2) := by nlinarith
      _ ≤ C * Real.exp (a * y / 2) := by nlinarith
  · have hy1 : (1:ℝ) ≤ y := h1.le
    have hx0 : 0 ≤ a * y / 2 := by positivity
    have hsum := Real.sum_le_exp_of_nonneg hx0 (s + 2)
    have hmem : s + 1 ∈ Finset.range (s + 2) := Finset.mem_range.mpr (by omega)
    have hterm : (a * y / 2) ^ (s + 1) / ((s + 1).factorial : ℝ)
        ≤ ∑ i ∈ Finset.range (s + 2), (a * y / 2) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (a * y / 2) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) hmem
    have hexp : (a * y / 2) ^ (s + 1) / ((s + 1).factorial : ℝ) ≤ Real.exp (a * y / 2) :=
      le_trans hterm hsum
    have hpow : (a * y / 2) ^ (s + 1) = (a / 2) ^ (s + 1) * y ^ (s + 1) := by ring
    rw [hpow] at hexp
    have hyb : y ^ (s + 1) ≤ Real.exp (a * y / 2) * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1) := by
      rw [le_div_iff₀ ha2]
      calc y ^ (s + 1) * (a / 2) ^ (s + 1) = (a / 2) ^ (s + 1) * y ^ (s + 1) := by ring
        _ = ((a / 2) ^ (s + 1) * y ^ (s + 1) / ((s + 1).factorial : ℝ))
              * ((s + 1).factorial : ℝ) := by field_simp
        _ ≤ Real.exp (a * y / 2) * ((s + 1).factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hexp hfact.le
    have hys : y ^ s ≤ y ^ (s + 1) := by
      calc y ^ s = y ^ s * 1 := by ring
        _ ≤ y ^ s * y := mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy s)
        _ = y ^ (s + 1) := by ring
    calc (1 + y) ^ s ≤ (2 * y) ^ s := pow_le_pow_left₀ (by linarith) (by linarith) s
      _ = 2 ^ s * y ^ s := by ring
      _ ≤ 2 ^ s * y ^ (s + 1) := by nlinarith
      _ ≤ 2 ^ s * (Real.exp (a * y / 2) * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1)) := by
          nlinarith
      _ = (2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1)) * Real.exp (a * y / 2) := by
          ring
      _ ≤ C * Real.exp (a * y / 2) := by
          have h4 : 0 ≤ 2 ^ s * ((s + 1).factorial : ℝ) / (a / 2) ^ (s + 1) :=
            div_nonneg (by positivity) ha2.le
          rw [hC]; nlinarith

/-! ### The running maximum of `h` over the first `n+2` sites -/

/-- `max_{0 <= x <= n+1} h(x)`. -/
def Yfun (p : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun x => hof p ω x)

lemma measurable_Yfun (p : ℝ) (hp0 : p ≠ 0) (n : ℕ) :
    Measurable (fun ω : ℕ → Bool => Yfun p n ω) := by
  have hY : (fun ω : ℕ → Bool => Yfun p n ω)
      = (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
          (fun i (ω : ℕ → Bool) => hof p ω i) := by
    funext ω
    exact (Finset.sup'_apply (s := Finset.range (n + 2))
      ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun i (ω : ℕ → Bool) => hof p ω i) ω).symm
  rw [hY]
  exact Finset.measurable_sup' _ (fun i _ => measurable_hof hp0 i)

lemma hof_le_Yfun (p : ℝ) (n x : ℕ) (ω : ℕ → Bool) (hx : x ∈ Finset.range (n + 2)) :
    hof p ω x ≤ Yfun p n ω :=
  Finset.le_sup' (fun x => hof p ω x) hx

lemma one_le_Yfun {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (n : ℕ) (ω : ℕ → Bool) :
    1 ≤ Yfun p n ω := by
  have h := hof_le_Yfun p n 0 ω (Finset.mem_range.mpr (by omega))
  have := one_le_hof hp1 hp2 ω 0
  linarith

lemma exists_hof_eq_Yfun (p : ℝ) (n : ℕ) (ω : ℕ → Bool) :
    ∃ x ∈ Finset.range (n + 2), hof p ω x = Yfun p n ω := by
  obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (n + 2)) ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun x => hof p ω x)
  exact ⟨x, hx, hsup.symm⟩

/-- The exponential of the maximum is dominated by the sum over the sites. -/
lemma ofReal_exp_Yfun_le_sum {p θ : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (hθ : 0 ≤ θ)
    (n : ℕ) (ω : ℕ → Bool) :
    ENNReal.ofReal (Real.exp (θ * Yfun p n ω))
      ≤ ∑ x ∈ Finset.range (n + 2), ENNReal.ofReal (Real.exp (θ * hof p ω x)) := by
  obtain ⟨x, hx, hxeq⟩ := exists_hof_eq_Yfun p n ω
  rw [← hxeq]
  refine Finset.single_le_sum (f := fun x => ENNReal.ofReal (Real.exp (θ * hof p ω x)))
    (fun i _ => by simp) hx

/-! ### The `L^s` moment bound -/

/-- **Display (maxmom), `h`-part.**  For `m >= 2`, `p in (1/2,1)` and `s >= 1` there is
`C = C(s,m,p) < ∞` with

    E[(1 + max_{0<=x<=n+1} h(x))^s] <= C (log (n+2))^s   for every n. -/
theorem maxmom_h {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((1 + Yfun p n ω) ^ s)
          ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1))))
        ≤ ENNReal.ofReal (C * (Real.log ((n : ℝ) + 2)) ^ s) := by
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  have hqm0 : 0 < qm := by rw [hqm]; exact pow_pos (by linarith) _
  have hqm1 : qm ≤ 1 := by
    rw [hqm]; have := pow_one_sub_le_half hp1 hp2 hm; linarith
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
  haveI : IsProbabilityMeasure (boolMeasure qm) := isProbabilityMeasure_boolMeasure hqm0.le hqm1
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨Cc, hCcpos, hCc⟩ := poly_le_exp s hθpos
  set M : ℝ := momConst p qm θ γm with hM
  have hMnn : 0 ≤ M := momConst_nonneg (θ := θ) hp1 hp2 hqm0.le hγm1
  have hz0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the moment bound for each site
  have hmom : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
      ∂(markMeasure (boolMeasure qm)) ≤ ENNReal.ofReal M := fun x =>
    lintegral_exp_hof_le hp1 hp2 hqm0.le hqm1 hθpos hγmpos hγm1 hγm.symm.le x
  -- the exponential moment of the maximum
  have hexpY : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Yfun p n ω))
      ∂(markMeasure (boolMeasure qm)) ≤ ENNReal.ofReal (((n : ℝ) + 2) * M) := by
    intro n
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Yfun p n ω)) ∂(markMeasure (boolMeasure qm))
        ≤ ∫⁻ ω, ∑ x ∈ Finset.range (n + 2), ENNReal.ofReal (Real.exp (θ * hof p ω x))
            ∂(markMeasure (boolMeasure qm)) := by
          apply lintegral_mono
          intro ω
          exact ofReal_exp_Yfun_le_sum hp1.le hp2 hθpos.le n ω
      _ = ∑ x ∈ Finset.range (n + 2), ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
            ∂(markMeasure (boolMeasure qm)) :=
          lintegral_finsetSum _ (fun x _ => ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (measurable_const.mul (measurable_hof hp0 x))))
      _ ≤ ∑ x ∈ Finset.range (n + 2), ENNReal.ofReal M :=
          Finset.sum_le_sum (fun x _ => hmom x)
      _ = ENNReal.ofReal (((n : ℝ) + 2) * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          push_cast
          ring
  refine ⟨(1 / Real.log 2 + 4 / θ) ^ s + Cc * M / (Real.log 2) ^ s, ?_, ?_⟩
  · have h1 : (0:ℝ) < (1 / Real.log 2 + 4 / θ) ^ s := by positivity
    have h2 : 0 ≤ Cc * M / (Real.log 2) ^ s := by positivity
    linarith
  · intro n
    set z : ℝ := Real.log ((n : ℝ) + 2) with hz
    set U : ℝ := (4 / θ) * z with hU
    have hzpos : 0 < z := Real.log_pos (by linarith)
    have hzge : Real.log 2 ≤ z := by
      rw [hz]
      apply Real.log_le_log (by norm_num)
      linarith
    -- pointwise inequality
    have hpoint : ∀ ω : ℕ → Bool, (1 + Yfun p n ω) ^ s
        ≤ (1 + U) ^ s + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * Yfun p n ω) := by
      intro ω
      have hY0 : 0 ≤ Yfun p n ω := by linarith [one_le_Yfun hp1.le hp2 n ω]
      have hb := hCc (Yfun p n ω) hY0
      have hexpU : (0:ℝ) < Real.exp (-(θ * U / 2)) := Real.exp_pos _
      rcases le_or_gt (Yfun p n ω) U with hle | hgt
      · have h1 : (1 + Yfun p n ω) ^ s ≤ (1 + U) ^ s :=
          pow_le_pow_left₀ (by linarith) (by linarith) s
        have h2 : 0 ≤ (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * Yfun p n ω) := by positivity
        linarith
      · have hstep : Real.exp (θ * Yfun p n ω / 2) ≤ Real.exp (θ * Yfun p n ω) * Real.exp (-(θ * U / 2)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [hgt]
        have : (1 + Yfun p n ω) ^ s ≤ Cc * (Real.exp (θ * Yfun p n ω) * Real.exp (-(θ * U / 2))) :=
          le_trans hb (mul_le_mul_of_nonneg_left hstep hCcpos.le)
        have h2 : 0 ≤ (1 + U) ^ s := by positivity
        nlinarith
    calc ∫⁻ ω, ENNReal.ofReal ((1 + Yfun p n ω) ^ s) ∂(markMeasure (boolMeasure qm))
        ≤ ∫⁻ ω, ENNReal.ofReal ((1 + U) ^ s
            + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * Yfun p n ω))
            ∂(markMeasure (boolMeasure qm)) := by
          apply lintegral_mono
          intro ω
          exact ENNReal.ofReal_le_ofReal (hpoint ω)
      _ = ENNReal.ofReal ((1 + U) ^ s)
            + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Yfun p n ω))
                ∂(markMeasure (boolMeasure qm)) := by
          have hsplit : (fun ω : ℕ → Bool => ENNReal.ofReal ((1 + U) ^ s
              + (Cc * Real.exp (-(θ * U / 2))) * Real.exp (θ * Yfun p n ω)))
              = fun ω => ENNReal.ofReal ((1 + U) ^ s)
                + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
                  * ENNReal.ofReal (Real.exp (θ * Yfun p n ω)) := by
            funext ω
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity)]
          rw [hsplit]
          rw [lintegral_add_left (f := fun _ : ℕ → Bool => ENNReal.ofReal ((1 + U) ^ s))
            (g := fun ω : ℕ → Bool => ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ENNReal.ofReal (Real.exp (θ * Yfun p n ω))) measurable_const,
            lintegral_const, measure_univ, mul_one,
            lintegral_const_mul (ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2))))
              (f := fun ω : ℕ → Bool => ENNReal.ofReal (Real.exp (θ * Yfun p n ω)))
              (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                (measurable_const.mul (measurable_Yfun p hp0 n))))]
      _ ≤ ENNReal.ofReal ((1 + U) ^ s)
            + ENNReal.ofReal (Cc * Real.exp (-(θ * U / 2)))
              * ENNReal.ofReal (((n : ℝ) + 2) * M) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hexpY n) (by simp))
      _ = ENNReal.ofReal ((1 + U) ^ s
            + (Cc * Real.exp (-(θ * U / 2))) * (((n : ℝ) + 2) * M)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((1 + U) ^ s + Cc * M) := by
          apply ENNReal.ofReal_le_ofReal
          have hexpval : Real.exp (-(θ * U / 2)) = (((n : ℝ) + 2) ^ 2)⁻¹ := by
            have h1 : θ * U / 2 = 2 * z := by
              rw [hU]
              field_simp
              ring
            rw [h1, hz, Real.exp_neg,
              show (2:ℝ) * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 2) by
                rw [Real.log_pow]; push_cast; ring,
              Real.exp_log (by positivity)]
          rw [hexpval]
          have hpos2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
          have hkey : (((n : ℝ) + 2) ^ 2)⁻¹ * (((n : ℝ) + 2) * M) ≤ M := by
            have h1 : (((n : ℝ) + 2) ^ 2)⁻¹ * ((n : ℝ) + 2) = ((n : ℝ) + 2)⁻¹ := by
              field_simp
            calc (((n : ℝ) + 2) ^ 2)⁻¹ * (((n : ℝ) + 2) * M)
                = ((((n : ℝ) + 2) ^ 2)⁻¹ * ((n : ℝ) + 2)) * M := by ring
              _ = ((n : ℝ) + 2)⁻¹ * M := by rw [h1]
              _ ≤ 1 * M := by
                  apply mul_le_mul_of_nonneg_right _ hMnn
                  exact (inv_le_one₀ (by linarith : (0:ℝ) < (n:ℝ) + 2)).mpr (by linarith)
              _ = M := by ring
          nlinarith [hkey, hCcpos.le]
      _ ≤ ENNReal.ofReal (((1 / Real.log 2 + 4 / θ) ^ s + Cc * M / (Real.log 2) ^ s)
            * (Real.log ((n : ℝ) + 2)) ^ s) := by
          apply ENNReal.ofReal_le_ofReal
          have h1U : (1 + U) ^ s ≤ ((1 / Real.log 2 + 4 / θ) * z) ^ s := by
            have hb : (1 + U) = z * (1 / z + 4 / θ) := by
              rw [hU]
              field_simp
            rw [hb, mul_pow]
            have hcoef : 1 / z + 4 / θ ≤ 1 / Real.log 2 + 4 / θ := by
              have h1z : 1 / z ≤ 1 / Real.log 2 :=
                div_le_div_of_nonneg_left (by norm_num) hz0 hzge
              linarith
            calc z ^ s * (1 / z + 4 / θ) ^ s
                ≤ z ^ s * (1 / Real.log 2 + 4 / θ) ^ s := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact pow_le_pow_left₀ (by positivity) hcoef s
              _ = ((1 / Real.log 2 + 4 / θ) * z) ^ s := by
                  rw [mul_pow]; ring
          have h2 : Cc * M ≤ Cc * M / (Real.log 2) ^ s * z ^ s := by
            have hzs : (Real.log 2) ^ s ≤ z ^ s := pow_le_pow_left₀ hz0.le hzge s
            have hz0s : (0:ℝ) < (Real.log 2) ^ s := by positivity
            have hCM : 0 ≤ Cc * M := mul_nonneg hCcpos.le hMnn
            rw [div_mul_eq_mul_div, le_div_iff₀ hz0s]
            nlinarith [hzs]
          have h3 : ((1 / Real.log 2 + 4 / θ) * z) ^ s
              = (1 / Real.log 2 + 4 / θ) ^ s * z ^ s := mul_pow _ _ _
          have hfinal : (1 + U) ^ s + Cc * M
              ≤ ((1 / Real.log 2 + 4 / θ) ^ s + Cc * M / (Real.log 2) ^ s) * z ^ s := by
            rw [add_mul]
            linarith [h1U, h2, h3]
          exact hfinal

end

end SwarmMarks
