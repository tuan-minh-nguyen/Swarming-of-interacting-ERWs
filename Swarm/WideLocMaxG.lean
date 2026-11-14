/-
# Widening the `(locmax)` bounds for `G` and for `h ⊔ G`

The paper's `(locmax)` display bounds `max{h^*_j(x), G_j(x)}` on a fixed spatial window;
`LocSumR1.array_locmax_hG` (`Swarm/R2bLocMaxG.lean`) formalises this for `h_j` and
`G_j` jointly, again on the narrow window `[A - ⌈L^(1/16)⌉, A + L)`.

This file re-runs

* `array_locmax_G`  — the per-site Markov tail of `SwarmLogRatio.expmom_G_array` plus a union
  bound over the window sites, and
* `array_locmax_hG` — the union of the `h` and `G` tails at the common rate `min c_h c_G`

with the independent margins `M, Up`, exactly as `WideLocMax.lean` does for `hof`.  The only
change to the numerics is that the cardinality `M + Up` is bounded by `K * L = K * x^16`
instead of by `2 * x^16`; the union factor `N * K * x^16` is absorbed by
`LocSumR1.eventually_poly_mul_exp_le … 16`.
-/
import Swarm.WideLocMax
import Swarm.R2bLocMaxG

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace WideRepair

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct LocSumR1

variable {N : ℕ}

/-- **The wide `(locmax)` bound for the forward potential `G_j`.**  Same statement and proof as
`LocSumR1.array_locmax_G`, with independent margins and the cardinality hypothesis
`M + Up ≤ K * L`. -/
theorem array_locmax_G_wide {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      ((M : ℝ) + (Up : ℝ)) ≤ K * (L : ℝ) →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - M) (A + Up),
            xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨c, hc, C, hCpos, hbound⟩ := SwarmLogRatio.expmom_G_array (N := N) (p := p) hp1 hp2 hm
  have hp0 : 0 < p := by linarith
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  have hpoly := LocSumR1.eventually_poly_mul_exp_le (C := (N : ℝ) * K * C) (c := c)
    (by positivity) hc 16
  have hev : ∀ᶠ L : ℕ in atTop,
      ((N : ℝ) * K * C) * (xOf L) ^ 16 * Real.exp (-c * xOf L)
        ≤ Real.exp (-(c / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨c / 2, by linarith, max L₁ 1, ?_⟩
  intro L hL A M Up hMA hMU
  have hLge1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 1 ≤ L := le_trans (le_max_right _ _) hL
  set x := xOf L with hxdef
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
  have hset2 : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
        x ≤ Gsup p (siteMarks p m U j) y}
      = ⋃ y ∈ Finset.Ico (A - M) (A + Up), {U : Array N | ∃ j : Fin N,
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
  -- the window cardinality, and its polynomial bound
  have hcardval : (Finset.Ico (A - M) (A + Up)).card = M + Up := by
    rw [Nat.card_Ico]
    omega
  have hcard : ((Finset.Ico (A - M) (A + Up)).card : ℝ≥0∞)
      ≤ ENNReal.ofReal (K * x ^ 16) := by
    have hcast : (((M + Up : ℕ)) : ℝ) = (M : ℝ) + (Up : ℝ) := by push_cast; ring
    have hle : (((Finset.Ico (A - M) (A + Up)).card : ℕ) : ℝ) ≤ K * x ^ 16 := by
      rw [hcardval, hcast, hxe]
      exact hMU
    rw [← ENNReal.ofReal_natCast ((Finset.Ico (A - M) (A + Up)).card)]
    exact ENNReal.ofReal_le_ofReal hle
  refine le_trans (mul_le_mul' hcard le_rfl) ?_
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : (K * x ^ 16) * ((N : ℝ) * (C * Real.exp (-(c * x))))
      = ((N : ℝ) * K * C) * x ^ 16 * Real.exp (-(c * x)) := by ring
  rw [h2]
  simpa [hxdef] using hL₁ L hLge1

/-- **The wide `(locmax)` bound for `h_j` and `G_j` together** (the paper's `(locmax)`).  Union
of `WideRepair.array_locmax_bound_wide` and `WideRepair.array_locmax_G_wide` at the common rate
`min c_h c_G`, which loses only the factor `2`, absorbed by `x = L^(1/16) ≥ 2·log 2 / c`. -/
theorem array_locmax_hG_wide {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (K : ℝ) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      ((M : ℝ) + (Up : ℝ)) ≤ K * (L : ℝ) →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - M) (A + Up),
            xOf L ≤ hof p (siteMarks p m U j) y ∨ xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨ch, hch, Lh, hh⟩ := array_locmax_bound_wide (N := N) (p := p) hp1 hp2 (m := m) hm K hK
  obtain ⟨cg, hcg, Lg, hg⟩ := array_locmax_G_wide (N := N) (p := p) hp1 hp2 (m := m) hm K hK
  set cmin : ℝ := min ch cg with hcmin
  have hcminpos : 0 < cmin := lt_min hch hcg
  have hev : ∀ᶠ L : ℕ in atTop, max (2 : ℝ) (2 * Real.log 2 / cmin) ≤ xOf L :=
    xOf_tendsto.eventually (eventually_ge_atTop _)
  obtain ⟨Lc, hLc⟩ := eventually_atTop.mp hev
  refine ⟨cmin / 2, by linarith, max Lh (max Lg Lc), ?_⟩
  intro L hL A M Up hMA hMU
  have hLh : Lh ≤ L := le_trans (le_max_left _ _) hL
  have hT2 : max Lg Lc ≤ L := le_trans (le_max_right _ _) hL
  have hLg : Lg ≤ L := le_trans (le_max_left _ _) hT2
  have hLc' : Lc ≤ L := le_trans (le_max_right _ _) hT2
  set x := xOf L with hxdef
  have hx3 : max (2 : ℝ) (2 * Real.log 2 / cmin) ≤ x := by
    simpa [hxdef] using hLc L hLc'
  have hxnn : 0 ≤ x := le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)) hx3
  have hcminh : cmin ≤ ch := min_le_left _ _
  have hcming : cmin ≤ cg := min_le_right _ _
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
  have hset : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
        x ≤ hof p (siteMarks p m U j) y ∨ x ≤ Gsup p (siteMarks p m U j) y}
      ⊆ {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
          x ≤ hof p (siteMarks p m U j) y}
        ∪ {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - M) (A + Up),
          x ≤ Gsup p (siteMarks p m U j) y} := by
    intro U hU
    obtain ⟨j, y, hy, h | h⟩ := hU
    · exact Or.inl ⟨j, y, hy, h⟩
    · exact Or.inr ⟨j, y, hy, h⟩
  refine (measure_mono hset).trans ?_
  refine (measure_union_le _ _).trans ?_
  have b1 : arrayMeasure N {U : Array N | ∃ j : Fin N,
      ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ hof p (siteMarks p m U j) y}
      ≤ ENNReal.ofReal (Real.exp (-ch * x)) :=
    hh L hLh A M Up hMA hMU
  have b2 : arrayMeasure N {U : Array N | ∃ j : Fin N,
      ∃ y ∈ Finset.Ico (A - M) (A + Up), x ≤ Gsup p (siteMarks p m U j) y}
      ≤ ENNReal.ofReal (Real.exp (-cg * x)) :=
    hg L hLg A M Up hMA hMU
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

end WideRepair

namespace WideRepair

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct LocSumR1

variable {N : ℕ}

/-- `array_locmax_G_wide` at the record-window scale `M + Up ≤ (2*T+4)*L`. -/
theorem array_locmax_G_wide_T {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      M + Up ≤ (2 * T + 4) * L →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - M) (A + Up),
            xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  have hK : (0 : ℝ) ≤ 2 * (T : ℝ) + 4 := by positivity
  obtain ⟨c, hc, L₀, h⟩ := array_locmax_G_wide (N := N) (p := p) hp1 hp2 hm
    (2 * (T : ℝ) + 4) hK
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M Up hMA hMU
  refine h L hL A M Up hMA ?_
  have h1 : ((M + Up : ℕ) : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by exact_mod_cast hMU
  push_cast at h1
  linarith

/-- `array_locmax_hG_wide` at the record-window scale `M + Up ≤ (2*T+4)*L`. -/
theorem array_locmax_hG_wide_T {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ (A M Up : ℕ), M ≤ A →
      M + Up ≤ (2 * T + 4) * L →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - M) (A + Up),
            xOf L ≤ hof p (siteMarks p m U j) y ∨ xOf L ≤ Gsup p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  have hK : (0 : ℝ) ≤ 2 * (T : ℝ) + 4 := by positivity
  obtain ⟨c, hc, L₀, h⟩ := array_locmax_hG_wide (N := N) (p := p) hp1 hp2 hm
    (2 * (T : ℝ) + 4) hK
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL A M Up hMA hMU
  refine h L hL A M Up hMA ?_
  have h1 : ((M + Up : ℕ) : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by exact_mod_cast hMU
  push_cast at h1
  linarith

end

end WideRepair
