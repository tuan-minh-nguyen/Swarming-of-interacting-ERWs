/-
  `SpatialData.lean` : the two-valued site data of the paper's marked-site layer,
  and the exact stationary mean algebra.

  In `main_1d_revised.tex` (Proposition `spatial`) the site data are

      B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}   i.i.d. Bernoulli(q),  q = (1-p)^{m-1},
      omega_j(x) = 1/2 + (p - 1/2) B_j(x)          (= p if the site is marked, 1/2 otherwise),
      a = E[(1 - omega_j(0))/omega_j(0)] = 1 - (2p-1)(1-p)^{m-1}/p.

  This file proves the exact two-valued mean identities behind (projh)/(projH):

  * `aOf p q = 1 - (2p-1) q / p`                        (`aOf_eq`)
  * `1/2 < 1 - q <= a < 1`                              (`half_lt_aOf`, `aOf_lt_one`)
  * `bOf p q = E[((1-omega)/omega)^2] < 1`              (`bOf_lt_one`)
  * `cOf p q = E[1/omega] = 1 + a`                      (`cOf_eq_one_add_a`)
-/
import Swarm.Imports

open MeasureTheory
open scoped ENNReal Topology

namespace SwarmSpatial

noncomputable section

/-! ### The one-site data -/

/-- The paper's `omega_j(x) = 1/2 + (p - 1/2) B_j(x)`: `p` at a marked site, `1/2` elsewhere. -/
def omegaOf (p : ℝ) (b : Bool) : ℝ := if b then p else 1 / 2

/-- The paper's ratio `(1 - omega_j(x)) / omega_j(x)`. -/
def rhoOf (p : ℝ) (b : Bool) : ℝ := (1 - omegaOf p b) / omegaOf p b

@[simp] lemma omegaOf_true (p : ℝ) : omegaOf p true = p := rfl

@[simp] lemma omegaOf_false (p : ℝ) : omegaOf p false = 1 / 2 := rfl

@[simp] lemma rhoOf_true (p : ℝ) : rhoOf p true = (1 - p) / p := by
  simp [rhoOf]

@[simp] lemma rhoOf_false (p : ℝ) : rhoOf p false = 1 := by
  rw [rhoOf, omegaOf_false]; norm_num

/-- The paper's stationary mean `a = E[(1-omega)/omega]` for a mark of success probability `q`. -/
def aOf (p q : ℝ) : ℝ := (1 - q) * 1 + q * ((1 - p) / p)

/-- The second moment `E[((1-omega)/omega)^2]`. -/
def bOf (p q : ℝ) : ℝ := (1 - q) * 1 ^ 2 + q * ((1 - p) / p) ^ 2

/-- `E[1/omega]`, which the paper records as `1 + a`. -/
def cOf (p q : ℝ) : ℝ := (1 - q) * 2 + q * (1 / p)

/-- **The paper's constant.** `a = 1 - (2p-1) q / p`. -/
lemma aOf_eq {p q : ℝ} (hp : p ≠ 0) :
    aOf p q = 1 - (2 * p - 1) * q / p := by
  have h : (1 - p) / p = 1 - (2 * p - 1) / p := by field_simp; ring
  simp only [aOf, h]; field_simp; ring

/-- `E[1/omega] = 1 + a`. -/
lemma cOf_eq_one_add_a {p q : ℝ} (hp : p ≠ 0) : cOf p q = 1 + aOf p q := by
  have h : 1 / p = 1 + (1 - p) / p := by field_simp; ring
  simp only [cOf, aOf, h]; ring

/-- `b = E[rho^2]` as a quadratic expression in `q`. -/
lemma bOf_eq (p q : ℝ) : bOf p q = (1 - q) + q * ((1 - p) / p) ^ 2 := by
  simp [bOf]

/-- `rho` is nonnegative. -/
lemma rhoOf_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (b : Bool) :
    0 ≤ rhoOf p b := by
  cases b with
  | false => simp
  | true =>
      simp only [rhoOf_true]
      have : 0 < p := by linarith
      positivity

/-- `rho <= 1`, with equality at an unmarked site. -/
lemma rhoOf_le_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (b : Bool) :
    rhoOf p b ≤ 1 := by
  cases b with
  | false => simp
  | true =>
      simp only [rhoOf_true]
      have hp0 : 0 < p := by linarith
      rw [div_le_one hp0]; linarith

/-- `(1-p)/p < 1` for `p > 1/2`. -/
lemma rho_true_lt_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) : (1 - p) / p < 1 := by
  have hp0 : 0 < p := by linarith
  rw [div_lt_one hp0]; linarith

/-- `a >= 1 - q`. -/
lemma one_sub_q_le_aOf {p q : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p ≤ 1) (hq0 : 0 ≤ q) :
    1 - q ≤ aOf p q := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ (1 - p) / p := by positivity
  have h : aOf p q = (1 - q) + q * ((1 - p) / p) := by simp [aOf]
  rw [h]
  have : 0 ≤ q * ((1 - p) / p) := mul_nonneg hq0 hr
  linarith

/-- `a < 1` for `q > 0`. -/
lemma aOf_lt_one {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    aOf p q < 1 := by
  have hp0 : 0 < p := by linarith
  have hr : (1 - p) / p < 1 := rho_true_lt_one hp1
  have hr0 : 0 ≤ (1 - p) / p := by positivity
  have h : aOf p q = (1 - q) + q * ((1 - p) / p) := by simp [aOf]
  rw [h]
  nlinarith

/-- `a >= 0` for `0 <= q <= 1`. -/
lemma aOf_nonneg {p q : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : 0 ≤ aOf p q := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ (1 - p) / p := by positivity
  have h : aOf p q = (1 - q) + q * ((1 - p) / p) := by simp [aOf]
  rw [h]
  have h1 : 0 ≤ 1 - q := by linarith
  have h2 : 0 ≤ q * ((1 - p) / p) := mul_nonneg hq0 hr
  linarith

/-- `1/2 < a` in the paper's range: `q = (1-p)^{m-1} <= 1-p < 1/2`. -/
lemma half_lt_aOf {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - p) : (1 : ℝ) / 2 < aOf p q := by
  have h1 : 1 - q ≤ aOf p q := one_sub_q_le_aOf (le_of_lt hp1) (le_of_lt hp2) hq0
  have h2 : (1 : ℝ) / 2 < 1 - q := by linarith
  linarith

/-- `b < 1` (all terms `<= 1` and the marked term is `< 1`). -/
lemma bOf_lt_one {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq : 0 < q) :
    bOf p q < 1 := by
  have hp0 : 0 < p := by linarith
  have hr : (1 - p) / p < 1 := rho_true_lt_one hp1
  have hr0 : 0 ≤ (1 - p) / p := by positivity
  have hsq : ((1 - p) / p) ^ 2 < 1 := by nlinarith
  have h : bOf p q = (1 - q) + q * ((1 - p) / p) ^ 2 := bOf_eq p q
  rw [h]
  nlinarith

/-- `0 <= b`. -/
lemma bOf_nonneg {p q : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : 0 ≤ bOf p q := by
  have hr : 0 ≤ (1 - p) / p := by
    have : 0 < p := by linarith
    positivity
  have h : bOf p q = (1 - q) + q * ((1 - p) / p) ^ 2 := bOf_eq p q
  rw [h]
  have h1 : 0 ≤ 1 - q := by linarith
  have h2 : 0 ≤ q * ((1 - p) / p) ^ 2 := by positivity
  linarith

/-- The paper's `q = (1-p)^{m-1}` for `m >= 2` is positive. -/
lemma q_paper_pos {p : ℝ} (hp2 : p < 1) {m : ℕ} : 0 < (1 - p) ^ (m - 1) := by
  have h : 0 < 1 - p := by linarith
  positivity

lemma q_paper_lt_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    (1 - p) ^ (m - 1) < 1 := by
  have h0 : 0 < 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  have h2 : m - 1 ≠ 0 := by omega
  exact pow_lt_one₀ (le_of_lt h0) h1 h2

lemma q_paper_le_one_sub_p {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) : (1 - p) ^ (m - 1) ≤ 1 - p := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ 1 := by linarith
  have h2 : 1 ≤ m - 1 := by omega
  calc (1 - p) ^ (m - 1) ≤ (1 - p) ^ 1 := pow_le_pow_of_le_one h0 h1 h2
    _ = 1 - p := pow_one _

/-! ### The one-site law -/

/-- The Bernoulli law with success probability `q` on `Bool`. -/
def markLaw (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

lemma markLaw_univ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : markLaw q Set.univ = 1 := by
  simp only [markLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith), show q + (1 - q) = 1 by ring, ENNReal.ofReal_one]

lemma isProbabilityMeasure_markLaw {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (markLaw q) :=
  ⟨markLaw_univ h0 h1⟩

/-- Integration against the two-point law: the two-branch mean. -/
lemma integral_markLaw {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(markLaw q) = q * f true + (1 - q) * f false := by
  have hd1 : Integrable f (Measure.dirac true) := Integrable.of_finite
  have hd0 : Integrable f (Measure.dirac false) := Integrable.of_finite
  have hA : Integrable f (ENNReal.ofReal q • Measure.dirac true) :=
    hd1.smul_measure ENNReal.ofReal_ne_top
  have hB : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac false) :=
    hd0.smul_measure ENNReal.ofReal_ne_top
  rw [markLaw, integral_add_measure hA hB,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    smul_eq_mul, smul_eq_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]

/-- **`E[rho] = a`** for a single site with mark probability `q`. -/
lemma integral_rhoOf {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∫ b, rhoOf p b ∂(markLaw q) = aOf p q := by
  rw [integral_markLaw h0 h1, rhoOf_true, rhoOf_false, aOf]
  ring

/-- **`E[rho^2] = b`**. -/
lemma integral_rhoOf_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) :
    ∫ b, (rhoOf p b) ^ 2 ∂(markLaw q) = bOf p q := by
  rw [integral_markLaw h0 h1, rhoOf_true, rhoOf_false, bOf]
  ring

/-- **`E[1/omega] = 1 + a`** (the paper's display in the proof of Proposition `ball`). -/
lemma integral_inv_omegaOf {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ} (hp : p ≠ 0) :
    ∫ b, (omegaOf p b)⁻¹ ∂(markLaw q) = 1 + aOf p q := by
  rw [integral_markLaw h0 h1, omegaOf_true, omegaOf_false]
  simp only [one_div, inv_inv]
  rw [aOf]
  field_simp
  ring

end

end SwarmSpatial
