/-
  **`locsum` residual R3 (second-moment route), array level: the window sum of `Pz²`.**

  On the actual interacting array, for all large `L`, every window start `A ≥ L` and
  `ℓ = ⌈L^{1/16}⌉`, the probability that some walker has

      Σ_{y∈[A-ℓ, A+L)} Pz(y,ℓ)²  ≥  L^{1/16}

  is at most `e^{-c L^{1/16}}`, with `c = -log(b)/2` and `b = E[rho²] < 1` depending only on
  `m,p`.  The proof is Markov's inequality for the *sum*, using
  `R3Sum.lintegral_Pz_sq` for each site and the absorption `b^ℓ ≤ e^{-κ L^{1/16}}`.
-/
import Swarm.R1ProductMoments

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

namespace LocSumR1

noncomputable section

/-- The site sum of `Pz(y,ℓ)²` has the stated `lintegral` on the mark row. -/
theorem lintegral_Pz_sq_sum {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (s : Finset ℕ) {ℓ : ℕ}
    (hs : ∀ y ∈ s, ℓ ≤ y) :
    ∫⁻ ω, (∑ y ∈ s, ENNReal.ofReal ((LocSum.Pz p y ℓ ω) ^ 2)) ∂(markMeasure (boolMeasure q))
      = ENNReal.ofReal (((s.card : ℕ) : ℝ) * (LocSum.bC p q) ^ ℓ) := by
  rw [lintegral_finset_sum]
  · have hterm : ∀ y ∈ s, ∫⁻ ω, ENNReal.ofReal ((LocSum.Pz p y ℓ ω) ^ 2)
        ∂(markMeasure (boolMeasure q)) = ENNReal.ofReal ((LocSum.bC p q) ^ ℓ) :=
      fun y hy => lintegral_Pz_sq h0 h1 hp1 hp2 (hs y hy)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast (s.card), ← ENNReal.ofReal_mul (by positivity)]
  · intro y _
    exact ((LocSum.measurable_Pz p y ℓ).pow_const 2).ennreal_ofReal

/-- **The window sum event on the actual array.** -/
theorem array_Pz_sq_sum_bound {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          xOf L ≤ ∑ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            (LocSum.Pz p y (ellT (xOf L)) (siteMarks p m U j)) ^ 2}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < qOf p m := by unfold qOf; positivity
  have hq1 : qOf p m ≤ 1 := by
    unfold qOf; exact pow_le_one₀ (by linarith) (by linarith)
  have hq1' : qOf p m < 1 := by
    unfold qOf
    refine pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hb0 : 0 ≤ LocSum.bC p (qOf p m) := LocSum.bC_nonneg hp1 hp2 hq0.le hq1
  have hb1 : LocSum.bC p (qOf p m) < 1 := LocSum.bC_lt_one hp1 hp2 hq0
  have hbpos : 0 < LocSum.bC p (qOf p m) := by
    have hq : 0 < 1 - qOf p m := by linarith
    have h2 : 0 ≤ (1 - p) / p := by positivity
    unfold LocSum.bC
    nlinarith [mul_nonneg (le_of_lt hq0) (pow_nonneg h2 2)]
  have hlog : Real.log (LocSum.bC p (qOf p m)) < 0 := Real.log_neg hbpos hb1
  set κ := -Real.log (LocSum.bC p (qOf p m)) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  -- absorption of the polynomial factor
  have hpoly := eventually_poly_mul_exp_le (C := 2 * (N : ℝ)) (c := κ) (by positivity) hκ 15
  have hev : ∀ᶠ L : ℕ in atTop,
      2 * (N : ℝ) * (xOf L) ^ 15 * Real.exp (-κ * xOf L)
        ≤ Real.exp (-(κ / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨κ / 2, by linarith, max (max L₁ 4) (2 ^ 16), ?_⟩
  intro L hL A hA
  have hLge4 : 4 ≤ L := le_trans (le_trans (le_max_right L₁ 4)
    (le_max_left (max L₁ 4) (2 ^ 16))) hL
  have hLge1 : L₁ ≤ L := le_trans (le_trans (le_max_left L₁ 4)
    (le_max_left (max L₁ 4) (2 ^ 16))) hL
  have hLge : 2 ^ 16 ≤ L := le_trans (le_max_right (max L₁ 4) (2 ^ 16)) hL
  have hLpos : 1 ≤ L := by norm_num at hLge4 ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx2 : 2 ≤ x := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLge
    rw [hxdef, xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  have hℓx : x ≤ (ellT x : ℝ) := le_ellT x
  have hℓ2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
  have hℓL : ellT x ≤ L := by
    have h2 : 2 * x ≤ x ^ 16 := by
      have h1 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h3 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have h2ℓ : 2 * ellT x ≤ L := by
    have h3 : 2 * ((ellT x : ℕ) : ℝ) ≤ 4 * x := by linarith
    have h4 : 4 * x ≤ x ^ 16 := by
      have h5 : (4 : ℝ) ≤ x ^ 15 := by
        have h6 : (2 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx2 2
        have h7 : (2:ℝ) ^ 14 ≤ x ^ 14 := pow_le_pow_left₀ (by norm_num) hx2 14
        have h8 : x ^ 15 = x * x ^ 14 := by ring
        nlinarith
      nlinarith
    have : 2 * ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  -- every site of the window is at depth at least `ellT x`
  have hdepth : ∀ y ∈ Finset.Ico (A - ellT x) (A + L), ellT x ≤ y := by
    intro y hy
    have h1 : A - ellT x ≤ y := (Finset.mem_Ico.mp hy).1
    omega
  -- the per-walker Markov bound
  have hrow : ∀ j : Fin N,
      arrayMeasure N {U : Array N | x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2}
        ≤ ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x) / x) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
    have hmeas : Measurable (fun U : Array N =>
        ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) :=
      Finset.measurable_sum _ fun y _ =>
        ((LocSum.measurable_Pz p y (ellT x)).comp
          (measurable_siteMarks hp0 hp2 m j)).pow_const 2 |>.ennreal_ofReal
    -- the integral over the array equals the integral over the mark row
    have hfint : Measurable (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
        ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) :=
      Finset.measurable_sum _ fun y _ =>
        ((LocSum.measurable_Pz p y (ellT x)).pow_const 2).ennreal_ofReal
    have hrowint : ∫⁻ U, (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) (siteMarks p m U j) ∂(arrayMeasure N)
        = ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) := by
      rw [hmp.lintegral_comp hfint]
      exact lintegral_Pz_sq_sum hq0.le hq1 hp1 hp2 _ hdepth
    have hint : ∫⁻ U, (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) ∂(arrayMeasure N)
        = ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) := by
      have hcongr : (∫⁻ U, (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
            ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) ∂(arrayMeasure N))
          = ∫⁻ U, (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
              ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) (siteMarks p m U j)
              ∂(arrayMeasure N) := rfl
      rw [hcongr, hrowint]
    -- Markov
    have hmk := mul_measure_le_lintegral (μ := arrayMeasure N) hmeas (ENNReal.ofReal x)
    rw [hint] at hmk
    rw [mul_comm] at hmk
    have hxpos : 0 < x := by linarith
    have hxne : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.mpr hxpos).ne'
    have hxtop : ENNReal.ofReal x ≠ ⊤ := ENNReal.ofReal_ne_top
    have hkey : arrayMeasure N {U : Array N | ENNReal.ofReal x
        ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)}
        ≤ ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) / ENNReal.ofReal x := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hxne) (Or.inl hxtop)]
      exact hmk
    refine le_trans (measure_mono ?_) (hkey.trans (le_of_eq ?_))
    · intro U hU
      simp only [Set.mem_setOf_eq] at hU ⊢
      have hsub : ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)
          = ENNReal.ofReal (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
              (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun y _ => by positivity).symm
      rw [hsub, ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact hU
    · rw [← ENNReal.ofReal_div_of_pos hxpos]
  -- union over the walkers
  have hset : {U : Array N | ∃ j : Fin N,
        x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2}
      = ⋃ j : Fin N, {U : Array N | x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2} := by
    ext U
    simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- numerical absorption
  have hcardle : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) ≤ 2 * x ^ 16 := by
    have hcard : (Finset.Ico (A - ellT x) (A + L)).card = L + ellT x := by
      rw [Nat.card_Ico]; omega
    rw [hcard]
    have h1 : ((L : ℝ) + (ellT x : ℕ)) ≤ x ^ 16 + 2 * x := by
      have h2 : (L : ℝ) = x ^ 16 := hxe.symm
      linarith
    have h3 : 2 * x ≤ x ^ 16 := by
      have h4 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h5 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    push_cast
    linarith
  have hbpow : (LocSum.bC p (qOf p m)) ^ (ellT x) ≤ Real.exp (-(κ * x)) := by
    have h1 : (LocSum.bC p (qOf p m)) ^ (ellT x)
        = Real.exp ((ellT x : ℕ) * Real.log (LocSum.bC p (qOf p m))) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hbpos _)]
    rw [h1]
    refine Real.exp_le_exp.mpr ?_
    have h2 : κ * x ≤ κ * (ellT x : ℕ) := by
      have := hℓx
      nlinarith
    rw [hκdef]
    nlinarith
  -- assemble in `ℝ`
  have hmain : (N : ℝ) * ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (LocSum.bC p (qOf p m)) ^ (ellT x) / x)
      ≤ Real.exp (-(κ / 2) * x) := by
    have hxpos : 0 < x := by linarith
    have h1 : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
        * (LocSum.bC p (qOf p m)) ^ (ellT x) / x
        ≤ (2 * x ^ 16) * Real.exp (-(κ * x)) / x := by
      refine div_le_div_of_nonneg_right ?_ hxpos.le
      exact mul_le_mul hcardle hbpow (by positivity) (by positivity)
    have h2 : (2 * x ^ 16) * Real.exp (-(κ * x)) / x = 2 * x ^ 15 * Real.exp (-(κ * x)) := by
      field_simp
    have h3 : (N : ℝ) * ((2 * x ^ 16) * Real.exp (-(κ * x)) / x)
        ≤ Real.exp (-(κ / 2) * x) := by
      rw [h2]
      have h4 : (N : ℝ) * (2 * x ^ 15 * Real.exp (-(κ * x)))
          = 2 * (N : ℝ) * x ^ 15 * Real.exp (-(κ * x)) := by ring
      rw [h4]
      simpa [hxdef] using hL₁ L hLge1
    calc (N : ℝ) * ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
          * (LocSum.bC p (qOf p m)) ^ (ellT x) / x)
        ≤ (N : ℝ) * ((2 * x ^ 16) * Real.exp (-(κ * x)) / x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.exp (-(κ / 2) * x) := h3
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hmain

end

end LocSumR1
