/-
  **`locsum` R2, completed: the paper's `(locmax)` for both potentials, on the actual array.**

  The paper's display `(locmax)` bounds `max{h^*_j(x), G_j(x)}` on the window.  On a one-sided
  row `h^*` must be replaced by `h_j` (see `R1Obstruction`), so the meaningful statement is

      max_{j<N} max{h_j(y), G_j(y) : y ∈ [A-ℓ, A+L)} ≤ L^{1/16}

  outside an event of probability `≤ e^{-c L^{1/16}}`.  This file proves exactly that on the
  actual interacting array, using the already-verified joint exponential moment
  `SwarmLogRatio.expmom_G_array` (constants depending only on `m,p`, not on `N`) and Markov's
  inequality.  It is the `(locmax)` input of the paper's Proposition `local`; the `h` half is
  `R2LocMax.array_locmax_bound`.
-/
import Swarm.R2LocMax
import Swarm.RawSpatial

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

namespace LocSumR1

noncomputable section

/-- **Markov tail from an exponential-moment bound**, for any nonnegative measurable `f`. -/
theorem tail_of_expmom {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {c C x : ℝ} (hc : 0 < c) (hCnn : 0 ≤ C) (hmes : Measurable f)
    (hint : ∫⁻ ω, ENNReal.ofReal (Real.exp (c * f ω)) ∂μ ≤ ENNReal.ofReal C) :
    μ {ω | x ≤ f ω} ≤ ENNReal.ofReal (C * Real.exp (-(c * x))) := by
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (c * f ω))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hmes))
  have hiff : ∀ ω, (ENNReal.ofReal (Real.exp (c * x)) ≤ ENNReal.ofReal (Real.exp (c * f ω)))
      ↔ x ≤ f ω := by
    intro ω
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩
  have hset : {ω | x ≤ f ω}
      = {ω | ENNReal.ofReal (Real.exp (c * x)) ≤ ENNReal.ofReal (Real.exp (c * f ω))} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hiff]
  rw [hset]
  have hmk := mul_measure_le_lintegral (μ := μ) hmeas (ENNReal.ofReal (Real.exp (c * x)))
  have hchain := le_trans hmk hint
  rw [mul_comm] at hchain
  have hfin : ENNReal.ofReal (Real.exp (c * x)) ≠ 0 := by simp [Real.exp_pos]
  have htop : ENNReal.ofReal (Real.exp (c * x)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : μ {ω | ENNReal.ofReal (Real.exp (c * x)) ≤ ENNReal.ofReal (Real.exp (c * f ω))}
      ≤ ENNReal.ofReal C / ENNReal.ofReal (Real.exp (c * x)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfin) (Or.inl htop)]
    exact hchain
  refine hdiv.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (c * x)), Real.exp_neg, div_eq_mul_inv]

/-- **`(locmax)` for the forward potential `G_j` on the actual array.** -/
theorem array_locmax_G {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, C, hCpos, hbound⟩ := expmom_G_array (N := N) (p := p) hp1 hp2 hm
  have hp0 : 0 < p := by linarith
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  have hpoly := eventually_poly_mul_exp_le (C := 2 * (N : ℝ) * C) (c := c)
    (by positivity) hc 16
  have hev : ∀ᶠ L : ℕ in atTop, (2 * (N : ℝ) * C) * (xOf L) ^ 16 * Real.exp (-c * xOf L)
      ≤ Real.exp (-(c / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨c / 2, by linarith, max L₁ (2 ^ 16), ?_⟩
  intro L hL A hA
  have hLge1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLbig : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLbig ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx2 : 2 ≤ x := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLbig
    rw [hxdef, xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  -- the single-walker, single-site tail for `G`
  have hsite : ∀ y : ℕ, arrayMeasure N {U : Array N | ∃ j : Fin N,
        x ≤ Gsup p (siteMarks p m U j) y}
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-(c * x))) := by
    intro y
    have hone : ∀ j : Fin N, arrayMeasure N {U : Array N |
        x ≤ Gsup p (siteMarks p m U j) y} ≤ ENNReal.ofReal (C * Real.exp (-(c * x))) := by
      intro j
      have hmeasG : Measurable (fun U : Array N => Gsup p (siteMarks p m U j) y) :=
        (measurable_Gsup p y).comp (measurable_siteMarks hp0 hp2 m j)
      refine tail_of_expmom hc hCnn hmeasG ?_
      have hmono : ∀ U : Array N,
          ENNReal.ofReal (Real.exp (c * Gsup p (siteMarks p m U j) y))
            ≤ ENNReal.ofReal (Real.exp (c * (hof p (siteMarks p m U j) y
                + Gsup p (siteMarks p m U j) y))) := by
        intro U
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have h1 : 1 ≤ hof p (siteMarks p m U j) y := one_le_hof hp1.le hp2 _ y
        nlinarith
      exact (lintegral_mono hmono).trans (hbound j y)
    have hset : {U : Array N | ∃ j : Fin N, x ≤ Gsup p (siteMarks p m U j) y}
        = ⋃ j : Fin N, {U : Array N | x ≤ Gsup p (siteMarks p m U j) y} := by
      ext U
      simp
    rw [hset]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hone j).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hset2 : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
        x ≤ Gsup p (siteMarks p m U j) y}
      = ⋃ y ∈ Finset.Ico (A - ellT x) (A + L), {U : Array N | ∃ j : Fin N,
          x ≤ Gsup p (siteMarks p m U j) y} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, y, hy, h⟩
      exact ⟨y, hy, j, h⟩
    · rintro ⟨y, hy, j, h⟩
      exact ⟨j, y, hy, h⟩
  rw [hset2]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => hsite y).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- numerical absorption
  have hℓL : ellT x ≤ L := by
    have h1 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
    have h2 : 2 * x ≤ x ^ 16 := by
      have h3 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h4 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have h5 : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast h5
  have hcard : ((Finset.Ico (A - ellT x) (A + L)).card : ℝ≥0∞)
      ≤ ENNReal.ofReal (2 * x ^ 16) := by
    have hcardval : (Finset.Ico (A - ellT x) (A + L)).card = L + ellT x := by
      rw [Nat.card_Ico]
      omega
    rw [hcardval]
    have h2x : ((L : ℝ) + (ellT x : ℕ)) ≤ 2 * x ^ 16 := by
      have h1 : (L : ℝ) = x ^ 16 := hxe.symm
      have h2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
      have h3 : 2 * x ≤ x ^ 16 := by
        have h4 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
        have h5 : x ^ 16 = x * x ^ 15 := by ring
        nlinarith
      linarith
    rw [← ENNReal.ofReal_natCast (L + ellT x)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa using h2x
  refine le_trans (mul_le_mul' hcard le_rfl) ?_
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (2 * x ^ 16) * ((N : ℝ) * (C * Real.exp (-(c * x))))
      = (2 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(c * x)) := by ring
  rw [h2]
  simpa [hxdef] using hL₁ L hLge1

/-- **`(locmax)` for `h_j` and `G_j` together on the actual array.** -/
theorem array_locmax_hG {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            xOf L ≤ hof p (siteMarks p m U j) y ∨ xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨ch, hch, Lh, hh⟩ := array_locmax_bound (N := N) (p := p) hp1 hp2 (m := m) hm
  obtain ⟨cg, hcg, Lg, hg⟩ := array_locmax_G (N := N) (p := p) hp1 hp2 (m := m) hm
  set cmin : ℝ := min ch cg with hcmin
  have hcminpos : 0 < cmin := lt_min hch hcg
  have hev : ∀ᶠ L : ℕ in atTop, max (2 : ℝ) (2 * Real.log 2 / cmin) ≤ xOf L :=
    xOf_tendsto.eventually (eventually_ge_atTop _)
  obtain ⟨Lc, hLc⟩ := eventually_atTop.mp hev
  refine ⟨cmin / 2, by linarith, max (max Lh (max Lg Lc)) (2 ^ 16), ?_⟩
  intro L hL A hA
  have hT1 : max Lh (max Lg Lc) ≤ L := le_trans (le_max_left _ _) hL
  have hLh : Lh ≤ L := le_trans (le_max_left _ _) hT1
  have hT2 : max Lg Lc ≤ L := le_trans (le_max_right _ _) hT1
  have hLg : Lg ≤ L := le_trans (le_max_left _ _) hT2
  have hLc' : Lc ≤ L := le_trans (le_max_right _ _) hT2
  have hLbig : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLbig ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx2 : 2 ≤ x := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLbig
    rw [hxdef, xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have hx3 : max (2 : ℝ) (2 * Real.log 2 / cmin) ≤ x := by
    simpa [hxdef] using hLc L hLc'
  have hcminh : cmin ≤ ch := min_le_left _ _
  have hcming : cmin ≤ cg := min_le_right _ _
  have hxnn : 0 ≤ x := by linarith
  have e1 : Real.exp (-ch * x) ≤ Real.exp (-cmin * x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (-cg * x) ≤ Real.exp (-cmin * x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have habs : (2 : ℝ) * Real.exp (-cmin * x) ≤ Real.exp (-(cmin / 2) * x) := by
    have hlog2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have hmin : Real.log 2 ≤ cmin * x / 2 := by
      have h1 : 2 * Real.log 2 / cmin ≤ x := le_trans (le_max_right _ _) hx3
      rw [div_le_iff₀ hcminpos] at h1
      linarith
    calc (2 : ℝ) * Real.exp (-cmin * x) = Real.exp (Real.log 2) * Real.exp (-cmin * x) := by
          rw [hlog2]
      _ = Real.exp (Real.log 2 - cmin * x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(cmin / 2) * x) := Real.exp_le_exp.mpr (by linarith)
  have hset : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
        xOf L ≤ hof p (siteMarks p m U j) y ∨ xOf L ≤ Gsup p (siteMarks p m U j) y}
      ⊆ {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
          xOf L ≤ hof p (siteMarks p m U j) y}
        ∪ {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
          xOf L ≤ Gsup p (siteMarks p m U j) y} := by
    intro U hU
    obtain ⟨j, y, hy, h | h⟩ := hU
    · exact Or.inl ⟨j, y, hy, h⟩
    · exact Or.inr ⟨j, y, hy, h⟩
  refine (measure_mono hset).trans ?_
  refine (measure_union_le _ _).trans ?_
  have b1 : arrayMeasure N {U : Array N | ∃ j : Fin N,
      ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L), xOf L ≤ hof p (siteMarks p m U j) y}
      ≤ ENNReal.ofReal (Real.exp (-ch * x)) := by
    have := hh L hLh A hA
    exact this
  have b2 : arrayMeasure N {U : Array N | ∃ j : Fin N,
      ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L), xOf L ≤ Gsup p (siteMarks p m U j) y}
      ≤ ENNReal.ofReal (Real.exp (-cg * x)) := by
    have := hg L hLg A hA
    exact this
  refine (add_le_add b1 b2).trans ?_
  have e1' : ENNReal.ofReal (Real.exp (-ch * x)) ≤ ENNReal.ofReal (Real.exp (-cmin * x)) :=
    ENNReal.ofReal_le_ofReal e1
  have e2' : ENNReal.ofReal (Real.exp (-cg * x)) ≤ ENNReal.ofReal (Real.exp (-cmin * x)) :=
    ENNReal.ofReal_le_ofReal e2
  refine (add_le_add e1' e2').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [habs]

end

end LocSumR1
