/-
  **`locsum`, layer 3: the uniform first and second moments of the truncations.**

  From the exact recursions of layer 2 we obtain, uniformly in the site `x` and the depth
  `k <= x`,

      E[Q p k x] <= L,        E[Q p k x ^ 2] <= M,

  with `L = (1+a)/(1-a)` and `M` a constant depending only on `p` and `q`.  `L` is exactly
  the paper's `(1+a)/(1-a)` (`Linf`), and `M` plays the role of `sup_x E[h^*(x)^2] < oo`.
-/
import Swarm.Imports
import Swarm.L2Moments

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocSum

noncomputable section

open SwarmMarks SwarmSpatial

/-- The paper's limit `(1+a)/(1-a)`. -/
def Lb (p q : ℝ) : ℝ := (1 + aC p q) / (1 - aC p q)

/-- The constant of the second-moment recursion. -/
def Cb (p q : ℝ) : ℝ := 1 + 2 * aC p q * (1 + Lb p q) + bC p q * (1 + 2 * Lb p q)

/-- A uniform bound for the second moments of the truncations. -/
def Mb (p q : ℝ) : ℝ := max 1 (Cb p q / (1 - bC p q))

lemma one_sub_aC_pos {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    0 < 1 - aC p q := by
  have := aC_lt_one hp1 hp2 hq; linarith

lemma one_sub_bC_pos {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    0 < 1 - bC p q := by
  have := bC_lt_one hp1 hp2 hq; linarith

lemma Lb_mul {p q : ℝ} (h : 1 - aC p q ≠ 0) : Lb p q * (1 - aC p q) = 1 + aC p q := by
  unfold Lb; field_simp

lemma one_le_Lb {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q)
    (hq1 : q ≤ 1) : 1 ≤ Lb p q := by
  have ha0 := aC_nonneg hp1 hp2 hq.le hq1
  have ha1 := aC_lt_one hp1 hp2 hq
  unfold Lb
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma Cb_nonneg {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ Cb p q := by
  have ha0 := aC_nonneg hp1 hp2 hq.le hq1
  have hb0 := bC_nonneg hp1 hp2 hq.le hq1
  have hL1 := one_le_Lb hp1 hp2 hq hq1
  have hL0 : 0 ≤ Lb p q := by linarith
  have h1 : 0 ≤ 2 * aC p q * (1 + Lb p q) := by positivity
  have h2 : 0 ≤ bC p q * (1 + 2 * Lb p q) := by positivity
  simp only [Cb]; linarith

lemma Cb_le_Mb {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    Cb p q ≤ Mb p q * (1 - bC p q) := by
  have hb1 := bC_lt_one hp1 hp2 hq
  have hne : 1 - bC p q ≠ 0 := by linarith
  have hid : Cb p q / (1 - bC p q) * (1 - bC p q) = Cb p q := div_mul_cancel₀ _ hne
  have hle : Cb p q / (1 - bC p q) ≤ Mb p q := le_max_right _ _
  calc Cb p q = Cb p q / (1 - bC p q) * (1 - bC p q) := hid.symm
    _ ≤ Mb p q * (1 - bC p q) := by
      apply mul_le_mul_of_nonneg_right hle (by linarith)

lemma one_le_Mb {p q : ℝ} : 1 ≤ Mb p q := le_max_left _ _

/-! ### Integrability of the squared truncations -/

lemma integrable_Q_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) :
    Integrable (fun ω : ℕ → Bool => (Q p k x ω) ^ 2) (markMeasure (boolMeasure q)) := by
  refine integrable_of_bound h0 h1 (fun ω : ℕ → Bool => (Q p k x ω) ^ 2)
    ((2 * (k : ℝ) + 1) ^ 2) ((measurable_Q p k x).pow_const 2).aestronglyMeasurable ?_
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := Q_abs_le hp1 hp2 k x ω
  have h1' : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
  nlinarith [abs_nonneg (Q p k x ω), sq_abs (Q p k x ω)]

/-! ### The first-moment recursion and its uniform bound -/

/-- `E[Q (k+1) x] = 1 + a (1 + E[Q k (x-1)])`. -/
lemma integral_Q_succ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (hx : 0 < x) :
    ∫ ω, Q p (k + 1) x ω ∂(markMeasure (boolMeasure q))
      = 1 + aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  have hpt : ∀ ω : ℕ → Bool, Q p (k + 1) x ω = 1 + rat p ω x * (1 + Q p k (x - 1) ω) :=
    fun ω => Q_succ p k x ω
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add (integrable_const 1) (integrable_rat_mul h0 h1 hp1 hp2 k (x - 1) x)]
  simp only [integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have hfac : ∫ ω, rat p ω x * (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q))
      = (∫ ω, rat p ω x ∂(markMeasure (boolMeasure q)))
        * (∫ ω, (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q))) :=
    (indepFun_rat_one_add_Q h0 h1 p k x hx).integral_fun_mul_eq_mul_integral
      (measurable_rat p x).aestronglyMeasurable
      ((measurable_const.add (measurable_Q p k (x - 1))).aestronglyMeasurable)
  rw [hfac, integral_rat h0 h1 p x,
    integral_add (integrable_const 1) (integrable_Q h0 h1 hp1 hp2 k (x - 1)), integral_const]
  simp

/-- **Uniform first moment**: `E[Q k x] <= L` for every `k <= x`. -/
theorem integral_Q_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    ∀ (k x : ℕ), k ≤ x →
      ∫ ω, Q p k x ω ∂(markMeasure (boolMeasure q)) ≤ Lb p q := by
  intro k
  induction k with
  | zero =>
    intro x _
    haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
    haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
    have hpt : (fun ω : ℕ → Bool => Q p 0 x ω) = fun _ => (-1 : ℝ) := by
      funext ω; simp
    rw [hpt, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have := one_le_Lb hp1 hp2 hq h1
    linarith
  | succ k ih =>
    intro x hx
    have hk : k ≤ x - 1 := by omega
    have hxpos : 0 < x := by omega
    rw [integral_Q_succ h0 h1 hp1 hp2 k x hxpos]
    have hm := ih (x - 1) hk
    have ha0 := aC_nonneg hp1 hp2 h0 h1
    have hLm := Lb_mul (p := p) (q := q) (ne_of_gt (one_sub_aC_pos hp1 hp2 hq))
    have hstep : 1 + aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q)))
        ≤ 1 + aC p q * (1 + Lb p q) := by
      have : aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q)))
          ≤ aC p q * (1 + Lb p q) := by
        apply mul_le_mul_of_nonneg_left _ ha0
        linarith
      linarith
    refine hstep.trans ?_
    nlinarith [hLm]

/-! ### The second-moment recursion and its uniform bound -/

lemma integral_sq_split {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (hx : 0 < x) :
    ∫ ω, (Q p (k + 1) x ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = 1 + 2 * (∫ ω, rat p ω x * (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q)))
        + ∫ ω, (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2
            ∂(markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  have hpt : ∀ ω : ℕ → Bool, (Q p (k + 1) x ω) ^ 2
      = 1 + 2 * (rat p ω x * (1 + Q p k (x - 1) ω))
        + (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2 := by
    intro ω
    have h := Q_succ p k x ω
    rw [h]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have iA : Integrable (fun ω : ℕ → Bool => 2 * (rat p ω x * (1 + Q p k (x - 1) ω)))
      (markMeasure (boolMeasure q)) :=
    (integrable_rat_mul h0 h1 hp1 hp2 k (x - 1) x).const_mul 2
  have iB : Integrable (fun ω : ℕ → Bool =>
      (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2) (markMeasure (boolMeasure q)) :=
    integrable_rat_sq_mul_sq h0 h1 hp1 hp2 k (x - 1) x
  rw [integral_add (f := fun ω : ℕ → Bool => 1 + 2 * (rat p ω x * (1 + Q p k (x - 1) ω)))
      (g := fun ω : ℕ → Bool => (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2)
      ((integrable_const 1).add iA) iB,
    integral_add (f := fun ω : ℕ → Bool => 1)
      (g := fun ω : ℕ → Bool => 2 * (rat p ω x * (1 + Q p k (x - 1) ω)))
      (integrable_const 1) iA,
    integral_const, integral_const_mul]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  try ring

/-- `E[(Q (k+1) x)^2] = 1 + 2a(1 + E Y) + b(1 + 2 E Y + E[Y^2])` with `Y = Q k (x-1)`. -/
lemma integral_Q_sq_succ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) (hx : 0 < x) :
    ∫ ω, (Q p (k + 1) x ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = 1 + 2 * aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q)))
        + bC p q * (1 + 2 * ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))
          + ∫ ω, (Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
  rw [integral_sq_split h0 h1 hp1 hp2 k x hx]
  have h1fac : ∫ ω, rat p ω x * (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q))
      = aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))) := by
    rw [show ∫ ω, rat p ω x * (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q))
        = (∫ ω, rat p ω x ∂(markMeasure (boolMeasure q)))
          * (∫ ω, (1 + Q p k (x - 1) ω) ∂(markMeasure (boolMeasure q))) from
      (indepFun_rat_one_add_Q h0 h1 p k x hx).integral_fun_mul_eq_mul_integral
        (measurable_rat p x).aestronglyMeasurable
        ((measurable_const.add (measurable_Q p k (x - 1))).aestronglyMeasurable)]
    rw [integral_rat h0 h1 p x,
      integral_add (integrable_const 1) (integrable_Q h0 h1 hp1 hp2 k (x - 1)), integral_const]
    simp
  have h2fac : ∫ ω, (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2
        ∂(markMeasure (boolMeasure q))
      = bC p q * ∫ ω, (1 + Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q)) := by
    rw [show ∫ ω, (rat p ω x) ^ 2 * (1 + Q p k (x - 1) ω) ^ 2
          ∂(markMeasure (boolMeasure q))
        = (∫ ω, (rat p ω x) ^ 2 ∂(markMeasure (boolMeasure q)))
          * (∫ ω, (1 + Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))) from
      (indepFun_rat_sq_Q_sq h0 h1 p k x hx).integral_fun_mul_eq_mul_integral
        ((measurable_rat p x).pow_const 2).aestronglyMeasurable
        ((measurable_const.add (measurable_Q p k (x - 1))).pow_const 2).aestronglyMeasurable]
    rw [integral_rat_sq h0 h1 p x]
  have hsq : ∫ ω, (1 + Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = 1 + 2 * ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))
        + ∫ ω, (Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q)) := by
    have hpt : ∀ ω : ℕ → Bool, (1 + Q p k (x - 1) ω) ^ 2
        = 1 + 2 * Q p k (x - 1) ω + (Q p k (x - 1) ω) ^ 2 := fun ω => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_add (f := fun ω : ℕ → Bool => 1 + 2 * Q p k (x - 1) ω)
      (g := fun ω : ℕ → Bool => (Q p k (x - 1) ω) ^ 2)
      ((integrable_const 1).add ((integrable_Q h0 h1 hp1 hp2 k (x - 1)).const_mul 2))
      (integrable_Q_sq h0 h1 hp1 hp2 k (x - 1)),
      integral_add (f := fun ω : ℕ → Bool => 1)
        (g := fun ω : ℕ → Bool => 2 * Q p k (x - 1) ω)
        (integrable_const 1) ((integrable_Q h0 h1 hp1 hp2 k (x - 1)).const_mul 2),
      integral_const_mul, integral_const]
    simp
  rw [h1fac, h2fac, hsq]
  ring

/-- **Uniform second moment**: `E[Q k x ^ 2] <= M` for every `k <= x`. -/
theorem integral_Q_sq_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    ∀ (k x : ℕ), k ≤ x →
      ∫ ω, (Q p k x ω) ^ 2 ∂(markMeasure (boolMeasure q)) ≤ Mb p q := by
  intro k
  induction k with
  | zero =>
    intro x _
    haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
    haveI : IsProbabilityMeasure (markMeasure (boolMeasure q)) := inferInstance
    have hpt : (fun ω : ℕ → Bool => (Q p 0 x ω) ^ 2) = fun _ => (1 : ℝ) := by
      funext ω; simp
    rw [hpt, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    exact one_le_Mb
  | succ k ih =>
    intro x hx
    have hk : k ≤ x - 1 := by omega
    have hxpos : 0 < x := by omega
    rw [integral_Q_sq_succ h0 h1 hp1 hp2 k x hxpos]
    have hme := ih (x - 1) hk
    have hm1 := integral_Q_le h0 h1 hp1 hp2 hq k (x - 1) hk
    have ha0 := aC_nonneg hp1 hp2 h0 h1
    have hb0 := bC_nonneg hp1 hp2 h0 h1
    have hb1 := bC_lt_one hp1 hp2 hq
    have hC := Cb_le_Mb hp1 hp2 hq h1
    have hCnn := Cb_nonneg hp1 hp2 hq h1
    have hkey : 1 + 2 * aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q)))
        + bC p q * (1 + 2 * ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))
          + ∫ ω, (Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q)))
        ≤ Cb p q + bC p q * Mb p q := by
      simp only [Cb]
      have h2a : 2 * aC p q * (1 + ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q)))
          ≤ 2 * aC p q * (1 + Lb p q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h3 : bC p q * (1 + 2 * ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))
          + ∫ ω, (Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q)))
          ≤ bC p q * (1 + 2 * Lb p q) + bC p q * Mb p q := by
        have h4 : bC p q * (1 + 2 * ∫ ω, Q p k (x - 1) ω ∂(markMeasure (boolMeasure q))
            + ∫ ω, (Q p k (x - 1) ω) ^ 2 ∂(markMeasure (boolMeasure q)))
            ≤ bC p q * (1 + 2 * Lb p q + Mb p q) := by
          apply mul_le_mul_of_nonneg_left _ hb0
          linarith
        nlinarith [h4]
      linarith
    refine hkey.trans ?_
    have hMb0 : 0 ≤ Mb p q := by linarith [one_le_Mb (p := p) (q := q)]
    have hbMb : 0 ≤ Mb p q * bC p q := mul_nonneg hMb0 hb0
    linarith [hC]

end

end LocSum
