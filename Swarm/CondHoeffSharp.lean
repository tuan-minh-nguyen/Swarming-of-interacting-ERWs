/-
# Sharp conditional Hoeffding lemma (every `t`, constant `t²c²/2`)

The accepted `CondHoeffding.lean` proves the conditional MGF bound
`μ[exp (t·Y) | m] ≤ᵐ exp (t²c²)` only under the side condition `|t|·c ≤ 1`, and with the crude
(non-sharp) exponent `t²c²`.  That side condition is exactly what forces the paper-scale window
restriction `L ≤ t-s` in `LocMoveCompose`/`PaperScale`: at `ε = L^(3/4)`, `B = L^(1/16)` the
required `ε ≤ 4(t-s)B` fails for short windows.

This file removes the restriction at its source: the sharp Hoeffding bound holds for *every*
`t > 0`,

  `|Y| ≤ c` a.s., `μ[Y | m] = 0`  ⟹  `μ[exp (t·Y) | m] ≤ᵐ exp (t² c² / 2)`.

Chord bound: for `|y| ≤ c`, `a = (c-y)/(2c)`, `b = (y+c)/(2c)`, convexity of `exp` between the
points `-tc` and `tc` gives `exp (t y) ≤ exp (-tc) + b (exp (tc) - exp (-tc))`, affine in `y`.
Taking `μ[·|m]`, using `μ[Y|m] = 0`, gives `cosh (tc)`, and `cosh u ≤ exp (u²/2)`.

No `sorry`, no new axiom.  Scope: this is the MGF input of the maximal Azuma step; it produces no
carrier probability, defect profile or invariant law by itself.
-/
import Swarm.Imports
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace WCJFSharp

/-- **Chord bound for `exp` across `±t c`.**  For `c > 0` and `|y| ≤ c`, `exp (t y)` is at most
the affine interpolation between `exp (-(t c))` and `exp (t c)` at `y`. -/
theorem exp_chord_of_abs_le {t c y : ℝ} (hc : 0 < c) (hy : |y| ≤ c) :
    Real.exp (t * y) ≤
      Real.exp (-(t * c)) + ((y + c) / (2 * c)) * (Real.exp (t * c) - Real.exp (-(t * c))) := by
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  set a : ℝ := (c - y) / (2 * c) with ha
  set b : ℝ := (y + c) / (2 * c) with hb
  have hcy : -c ≤ y := neg_le_of_abs_le hy
  have hyc : y ≤ c := le_of_abs_le hy
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hc2.le
  have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg (by linarith) hc2.le
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hmid : a * (-(t * c)) + b * (t * c) = t * y := by rw [ha, hb]; field_simp; ring
  have h := convexOn_exp.2 (Set.mem_univ (-(t * c))) (Set.mem_univ (t * c)) ha0 hb0 hab
  have h' : Real.exp (a * (-(t * c)) + b * (t * c))
      ≤ a * Real.exp (-(t * c)) + b * Real.exp (t * c) := by
    simpa only [smul_eq_mul] using h
  have halin : a = 1 - b := by linarith
  rw [hmid] at h'
  calc Real.exp (t * y)
      ≤ a * Real.exp (-(t * c)) + b * Real.exp (t * c) := h'
    _ = Real.exp (-(t * c)) + b * (Real.exp (t * c) - Real.exp (-(t * c))) := by
        rw [halin]; ring

/-- **Conditional Hoeffding lemma, sharp and unconditional in `t`.**  If `|Y| ≤ c` a.s. and the
conditional mean of `Y` given `m` vanishes, then for every `t > 0` the conditional MGF of `Y` is at
most `exp (t² c² / 2)` almost surely. -/
theorem condExp_exp_mul_le_half {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {Y : Ω → ℝ} {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (hY : AEMeasurable Y μ) (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ c) (hmean : μ[Y | m] =ᵐ[μ] 0) :
    μ[fun ω => Real.exp (t * Y ω) | m] ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c ^ 2 / 2) := by
  letI : MeasurableSpace Ω := m0
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- degenerate case `c = 0`: `Y = 0` a.e.
    have hY0 : Y =ᵐ[μ] 0 := by
      filter_upwards [hb] with ω hω
      have h1 : |Y ω| ≤ 0 := by simpa only [← hc0] using hω
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hcongr : (fun ω => Real.exp (t * Y ω)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [hY0] with ω hω
      simp [hω]
    have h1 : μ[fun ω => Real.exp (t * Y ω) | m] =ᵐ[μ] fun _ => (1 : ℝ) :=
      (condExp_congr_ae hcongr).trans (EventuallyEq.of_eq (condExp_const hm (1 : ℝ)))
    refine h1.trans_le ?_
    filter_upwards with _
    simp only [← hc0]
    norm_num
  · -- main case `c > 0`
    set K : ℝ := Real.exp (t * c) - Real.exp (-(t * c)) with hK
    set g : Ω → ℝ :=
      (K / (2 * c)) • Y + fun _ => (Real.exp (-(t * c)) + K / 2) with hg
    have hfg : (fun ω => Real.exp (t * Y ω)) ≤ᵐ[μ] g := by
      filter_upwards [hb] with ω hω
      have h := exp_chord_of_abs_le (t := t) hcpos hω
      simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine le_trans h (le_of_eq ?_)
      field_simp
      ring
    have hYm : AEStronglyMeasurable Y μ := hY.aestronglyMeasurable
    have hYint : Integrable Y μ := by
      refine Integrable.of_bound hYm c ?_
      filter_upwards [hb] with ω hω using hω
    have hfint : Integrable (fun ω => Real.exp (t * Y ω)) μ := by
      refine Integrable.of_bound
        (Real.continuous_exp.comp_aestronglyMeasurable (hYm.const_mul t)) (Real.exp (t * c)) ?_
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      have h2 : t * |Y ω| ≤ t * c := mul_le_mul_of_nonneg_left hω ht.le
      calc t * Y ω ≤ |t * Y ω| := le_abs_self _
        _ = t * |Y ω| := by rw [abs_mul, abs_of_pos ht]
        _ ≤ t * c := h2
    have hsm : Integrable ((K / (2 * c)) • Y) μ := hYint.smul (K / (2 * c))
    have hcn : Integrable (fun _ : Ω => (Real.exp (-(t * c)) + K / 2)) μ := integrable_const _
    have hgint : Integrable g μ := hsm.add hcn
    have hmono := condExp_mono (m := m) hfint hgint hfg
    have hsplit : μ[g | m] =ᵐ[μ]
        μ[(K / (2 * c)) • Y | m] + μ[fun _ => (Real.exp (-(t * c)) + K / 2) | m] :=
      condExp_add hsm hcn m
    have h1 : μ[(K / (2 * c)) • Y | m] =ᵐ[μ] (K / (2 * c)) • μ[Y | m] :=
      condExp_smul (K / (2 * c)) Y m
    have h2 : μ[fun _ : Ω => (Real.exp (-(t * c)) + K / 2) | m]
        = fun _ => (Real.exp (-(t * c)) + K / 2) :=
      condExp_const hm _
    have hstep : μ[(K / (2 * c)) • Y | m] + μ[fun _ => (Real.exp (-(t * c)) + K / 2) | m]
        =ᵐ[μ] (K / (2 * c)) • μ[Y | m] + fun _ => (Real.exp (-(t * c)) + K / 2) := by
      filter_upwards [h1] with ω hω
      simp only [Pi.add_apply]
      rw [h2, hω]
    have hcosh : μ[g | m] =ᵐ[μ] fun _ => Real.cosh (t * c) := by
      refine hsplit.trans (hstep.trans ?_)
      filter_upwards [hmean] with ω hω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hω]
      simp only [Pi.zero_apply, mul_zero, zero_add]
      rw [Real.cosh_eq, hK]
      field_simp
      ring
    refine hmono.trans ?_
    refine hcosh.trans_le ?_
    filter_upwards with _
    have harg : (t * c) ^ 2 / 2 = t ^ 2 * c ^ 2 / 2 := by ring
    rw [← harg]
    exact Real.cosh_le_exp_half_sq (t * c)

end WCJFSharp
