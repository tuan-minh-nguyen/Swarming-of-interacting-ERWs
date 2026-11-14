/-
  **`locsum` residual R2: the window maximum of the potential, on the actual array.**

  The paper's `(locmax)` input to `(locsum)` is a bound on the potential at the sites of the
  window: on one good event, `h_j(y) ≤ L^{1/16}` for every walker `j` and every integer
  `y` in the window.  (In the paper it is stated for `h^*` and `G`; on a one-sided row the
  object that the `(hstat)` comparison `R1Identity.hof_sub_Q` actually needs is `h_j` itself,
  which is what is bounded here.  `h^*` cannot be used: see `R1Obstruction`.)

  The proof is the exponential moment of `MarkMoments.exists_exp_moment_hof` (constants
  depending only on `m,p`), Markov's inequality at the level `u = L^{1/16}`, a union bound over
  the `N` walkers and the `L + ℓ` sites of the window, transport to the actual interacting
  array by `RawLogRatio.measurePreserving_siteMarks`, and the absorption of the polynomial
  union factor `N (L+ℓ) ≤ 3N L^{1/16·16}` into the exponential rate.
-/
import Swarm.R1Identity
import Swarm.MarkTails

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

namespace LocSumR1

noncomputable section

/-- Absorption for any polynomial degree `s`: `C x^s e^{-cx} ≤ e^{-cx/2}` eventually. -/
lemma eventually_poly_mul_exp_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (s : ℕ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ s * Real.exp (-c * x) ≤ Real.exp (-(c / 2) * x) := by
  set c₂ := c / 2 with hc₂def
  have hc₂ : 0 < c₂ := by rw [hc₂def]; linarith
  have hcp : (0 : ℝ) < c₂ ^ s := by positivity
  have ht : Tendsto (fun x : ℝ => c₂ * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc₂
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero s).comp ht
  have hεpos : (0 : ℝ) < c₂ ^ s / (1 + C) := by positivity
  have hev : ∀ᶠ x : ℝ in atTop,
      (c₂ * x) ^ s * Real.exp (-(c₂ * x)) ≤ c₂ ^ s / (1 + C) :=
    h0.eventually (Iic_mem_nhds hεpos)
  filter_upwards [hev] with x hx
  have hsplit : (c₂ * x) ^ s = c₂ ^ s * x ^ s := by ring
  rw [hsplit, div_eq_mul_one_div] at hx
  have hxs : x ^ s * Real.exp (-(c₂ * x)) ≤ 1 / (1 + C) := by
    refine le_of_mul_le_mul_left ?_ hcp
    have h1 : c₂ ^ s * (x ^ s * Real.exp (-(c₂ * x)))
        = c₂ ^ s * x ^ s * Real.exp (-(c₂ * x)) := by ring
    rw [h1]
    exact hx
  have hexp : Real.exp (-c * x)
      = Real.exp (-(c₂ * x)) * Real.exp (-(c₂ * x)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hc₂def]; ring
  have hpos : (0 : ℝ) < Real.exp (-(c₂ * x)) := Real.exp_pos _
  have key : C * (x ^ s * Real.exp (-(c₂ * x))) ≤ C * (1 / (1 + C)) :=
    mul_le_mul_of_nonneg_left hxs hC
  have hC3 : C * (1 / (1 + C)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  have hfin : C * (x ^ s * Real.exp (-(c₂ * x))) ≤ 1 := le_trans key hC3
  have hmul := mul_le_mul_of_nonneg_right hfin hpos.le
  calc C * x ^ s * Real.exp (-c * x)
      = (C * (x ^ s * Real.exp (-(c₂ * x)))) * Real.exp (-(c₂ * x)) := by
        rw [hexp]; ring
    _ ≤ 1 * Real.exp (-(c₂ * x)) := hmul
    _ = Real.exp (-(c₂ * x)) := one_mul _
    _ = Real.exp (-(c / 2) * x) := by
        rw [hc₂def]
        congr 1
        ring

/-- **Markov tail of `h_j(x)`** from any exponential-moment bound. -/
theorem hof_tail_of_exp_moment {p q θ C : ℝ} (hθ : 0 < θ) (hCnn : 0 ≤ C)
    (hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
        ∂(markMeasure (boolMeasure q)) ≤ ENNReal.ofReal C)
    (hp0 : p ≠ 0) (x : ℕ) (u : ℝ) :
    markMeasure (boolMeasure q) {ω : ℕ → Bool | u ≤ hof p ω x}
      ≤ ENNReal.ofReal (C * Real.exp (-(θ * u))) := by
  have hmeas : Measurable (fun ω : ℕ → Bool => ENNReal.ofReal (Real.exp (θ * hof p ω x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_hof hp0 x)))
  have hiff : ∀ (ω : ℕ → Bool),
      (ENNReal.ofReal (Real.exp (θ * u))
        ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))) ↔ u ≤ hof p ω x := by
    intro ω
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h hθ, fun h => mul_le_mul_of_nonneg_left h hθ.le⟩
  have hset : {ω : ℕ → Bool | u ≤ hof p ω x}
      = {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
          ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hiff]
  rw [hset]
  have hmk := mul_measure_le_lintegral (μ := markMeasure (boolMeasure q)) hmeas
    (ENNReal.ofReal (Real.exp (θ * u)))
  have hchain := le_trans hmk (hC x)
  rw [mul_comm] at hchain
  have hfin : ENNReal.ofReal (Real.exp (θ * u)) ≠ 0 := by simp [Real.exp_pos]
  have htop : ENNReal.ofReal (Real.exp (θ * u)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : (markMeasure (boolMeasure q))
      {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
        ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))}
      ≤ ENNReal.ofReal C / ENNReal.ofReal (Real.exp (θ * u)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfin) (Or.inl htop)]
    exact hchain
  refine hdiv.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (θ * u)), Real.exp_neg, div_eq_mul_inv]

/-- Union bound over a finite set of sites. -/
theorem markMeasure_exists_site_tail {p q θ C : ℝ} (hθ : 0 < θ) (hCnn : 0 ≤ C)
    (hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
        ∂(markMeasure (boolMeasure q)) ≤ ENNReal.ofReal C)
    (hp0 : p ≠ 0) (s : Finset ℕ) (u : ℝ) :
    markMeasure (boolMeasure q) {ω : ℕ → Bool | ∃ y ∈ s, u ≤ hof p ω y}
      ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-(θ * u))) := by
  have hset : {ω : ℕ → Bool | ∃ y ∈ s, u ≤ hof p ω y}
      = ⋃ y ∈ s, {ω : ℕ → Bool | u ≤ hof p ω y} := by
    ext ω
    simp
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => hof_tail_of_exp_moment hθ hCnn hC hp0 y u).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

lemma measurableSet_hof_exists {p : ℝ} (hp0 : p ≠ 0) (s : Finset ℕ) (u : ℝ) :
    MeasurableSet {ω : ℕ → Bool | ∃ y ∈ s, u ≤ hof p ω y} := by
  have hset : {ω : ℕ → Bool | ∃ y ∈ s, u ≤ hof p ω y}
      = ⋃ y ∈ s, {ω : ℕ → Bool | u ≤ hof p ω y} := by
    ext ω
    simp
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun y _ =>
    measurableSet_le measurable_const (measurable_hof hp0 y)

/-- Three-factor `ofReal` monotonicity, in the associativity shape produced by `calc`. -/
lemma ofReal_mul_three_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * (b * c) ≤ d) :
    ENNReal.ofReal a * (ENNReal.ofReal b * ENNReal.ofReal c) ≤ ENNReal.ofReal d := by
  rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha]
  exact ENNReal.ofReal_le_ofReal h

/-- **The window maximum on the actual interacting array.**  There is `c > 0` (depending only
on `N,m,p`) such that for all large `L` and every window start `A ≥ L`, with
`ℓ = ⌈L^{1/16}⌉`,

    P ( ∃ j < N, ∃ y ∈ [A-ℓ, A+L),  L^{1/16} ≤ h_j(y) ) ≤ e^{-c L^{1/16}}.

This is the `(locmax)` input of the paper's `(locsum)` argument, stated for the actual
harmonic functions `h_j` of the one-sided mark rows of the uniform array. -/
theorem array_locmax_bound {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            xOf L ≤ hof p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨θ, hθ, C, hCpos, hCraw⟩ := exists_exp_moment_hof (p := p) hp1 hp2 hm
  have hp0 : 0 < p := by linarith
  have hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
      ∂(markMeasure (boolMeasure (qOf p m))) ≤ ENNReal.ofReal C := fun x => hCraw x
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  -- absorption of the union factor
  have hpoly := eventually_poly_mul_exp_le (C := 3 * (N : ℝ) * C) (c := θ)
    (by positivity) hθ 16
  have hev : ∀ᶠ L : ℕ in atTop, (3 * (N : ℝ) * C) * (xOf L) ^ 16 * Real.exp (-θ * xOf L)
      ≤ Real.exp (-(θ / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨θ / 2, by linarith, max L₁ (2 ^ 16), ?_⟩
  intro L hL A hA
  have hLge : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLge1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLge ⊢; linarith
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
  have hℓ2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
  have hℓL : ellT x ≤ L := by
    have h2 : 2 * x ≤ x ^ 16 := by
      have h1 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h3 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have hℓA : ellT x ≤ A := le_trans hℓL hA
  -- the per-walker row bound
  have hrow : ∀ j : Fin N, arrayMeasure N {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
      x ≤ hof p (siteMarks p m U j) y}
      ≤ ((Finset.Ico (A - ellT x) (A + L)).card : ℝ≥0∞)
        * ENNReal.ofReal (C * Real.exp (-(θ * x))) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
    have hmeas := measurableSet_hof_exists (p := p) (ne_of_gt hp0) (Finset.Ico (A - ellT x) (A + L)) x
    have heq : {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
        x ≤ hof p (siteMarks p m U j) y}
        = (fun U : Array N => siteMarks p m U j) ⁻¹'
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} := rfl
    rw [heq]
    calc arrayMeasure N ((fun U : Array N => siteMarks p m U j) ⁻¹'
          {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y})
        = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} := by
          rw [Measure.map_apply (measurable_siteMarks hp0 hp2 m j) hmeas]
      _ = markMeasure (boolMeasure (qOf p m))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} :=
          congrArg (fun ν : Measure (ℕ → Bool) =>
            ν {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y}) hmp.map_eq
      _ ≤ _ :=
          markMeasure_exists_site_tail hθ hCnn hC (ne_of_gt hp0)
            (Finset.Ico (A - ellT x) (A + L)) x
  -- the union over the walkers
  have hset : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
        x ≤ hof p (siteMarks p m U j) y}
      = ⋃ j : Fin N, {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
          x ≤ hof p (siteMarks p m U j) y} := by
    ext U
    simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the numerical absorption
  have hcardval : (Finset.Ico (A - ellT x) (A + L)).card = L + ellT x := by
    rw [Nat.card_Ico]
    omega
  have hcardle : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) ≤ 2 * x ^ 16 := by
    rw [hcardval]
    have h1 : ((L : ℝ) + (ellT x : ℕ)) ≤ x ^ 16 + 2 * x := by
      have : (L : ℝ) = x ^ 16 := hxe.symm
      linarith
    have h2 : 2 * x ≤ x ^ 16 := by
      have h3 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h4 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    push_cast
    linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hx16 : (0 : ℝ) ≤ x ^ 16 := by positivity
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(θ * x)) := (Real.exp_pos _).le
  have hmono : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (C * Real.exp (-(θ * x)))
      ≤ (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x)) := by
    have hstep : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C
        ≤ (3 * (N : ℝ) * C) * x ^ 16 := by
      have h1 : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C
          ≤ (N : ℝ) * (2 * x ^ 16) * C := by
        refine mul_le_mul_of_nonneg_right ?_ hCnn
        exact mul_le_mul_of_nonneg_left hcardle hNnn
      have h2 : (N : ℝ) * (2 * x ^ 16) * C ≤ (3 * (N : ℝ) * C) * x ^ 16 := by
        have hprod : (0 : ℝ) ≤ (N : ℝ) * C * x ^ 16 := by positivity
        nlinarith [hprod]
      linarith
    calc (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
          * (C * Real.exp (-(θ * x)))
        = ((N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C)
            * Real.exp (-(θ * x)) := by ring
      _ ≤ ((3 * (N : ℝ) * C) * x ^ 16) * Real.exp (-(θ * x)) :=
          mul_le_mul_of_nonneg_right hstep hexpnn
      _ = (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x)) := by ring
  have hpolyL : (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x))
      ≤ Real.exp (-(θ / 2) * x) := by
    simpa [hxdef] using hL₁ L hLge1
  have hfinal : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (C * Real.exp (-(θ * x))) ≤ Real.exp (-(θ / 2) * x) := le_trans hmono hpolyL
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast
    (Finset.Ico (A - ellT x) (A + L)).card]
  refine ofReal_mul_three_le hNnn (by positivity) (mul_nonneg hCnn hexpnn) ?_
  rw [← mul_assoc]
  exact hfinal

end

end LocSumR1
