/-
  The i.i.d. site-mark space, and the general two-valued independence lemma used to integrate
  the one-step recursion.

  In the paper the marks are `B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}`, i.i.d. Bernoulli with
  success probability `q = (1-p)^{m-1}`.  Here we model a *general* two-point mark law on `Bool`
  (`μB`), and the i.i.d. product `markMeasure μB` on `ℕ → Bool`; specialising `μB = boolMeasure q`
  gives the paper's Bernoulli marks, with `P(B(x) = 1) = q` (`markMeasure_true` below).
-/
import Swarm.Imports
import Swarm.RecursionCore

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

/-! ### The two-point law on `Bool` -/

/-- The Bernoulli law with success probability `q` on `Bool`. -/
def boolMeasure (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

@[simp] lemma boolMeasure_true (q : ℝ) : boolMeasure q {true} = ENNReal.ofReal q := by
  simp [boolMeasure]

@[simp] lemma boolMeasure_false (q : ℝ) : boolMeasure q {false} = ENNReal.ofReal (1 - q) := by
  simp [boolMeasure]

lemma boolMeasure_univ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : boolMeasure q Set.univ = 1 := by
  simp only [boolMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith), show q + (1 - q) = 1 by ring, ENNReal.ofReal_one]

lemma isProbabilityMeasure_boolMeasure {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsProbabilityMeasure (boolMeasure q) :=
  ⟨boolMeasure_univ h0 h1⟩

/-! ### The mark space -/

/-- The law of an i.i.d. family of `Bool`-valued site marks with one-site law `μB`. -/
def markMeasure (μB : Measure Bool) : Measure (ℕ → Bool) := Measure.infinitePi fun _ => μB

instance instIsProbabilityMeasureMarkMeasure {μB : Measure Bool} [IsProbabilityMeasure μB] :
    IsProbabilityMeasure (markMeasure μB) := by
  unfold markMeasure
  infer_instance

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

lemma measurable_eval (x : ℕ) : Measurable (fun ω : ℕ → Bool => ω x) := measurable_pi_apply x

/-- **The site marks are independent.** -/
lemma iIndepFun_eval : iIndepFun (fun (x : ℕ) (ω : ℕ → Bool) => ω x) (markMeasure μB) := by
  unfold markMeasure
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) (b : Bool) => b) (by fun_prop)

/-- **The site-mark probability**: a marked site has probability `q`. -/
lemma markMeasure_true {q : ℝ} (hμ : μB {true} = ENNReal.ofReal q) (x : ℕ) :
    markMeasure μB {ω : ℕ → Bool | ω x = true} = ENNReal.ofReal q := by
  have hmap : (markMeasure μB).map (fun ω : ℕ → Bool => ω x) = μB := by
    unfold markMeasure
    exact Measure.infinitePi_map_eval (fun _ : ℕ => μB) x
  have hm : Measurable fun ω : ℕ → Bool => ω x := measurable_pi_apply x
  have h1 := Measure.map_apply hm (measurableSet_singleton true) (μ := markMeasure μB)
  rw [hmap] at h1
  have h2 : markMeasure μB ((fun ω : ℕ → Bool => ω x) ⁻¹' {true}) = ENNReal.ofReal q := by
    rw [← h1]; exact hμ
  exact h2

/-- The probability that a site is unmarked. -/
lemma markMeasure_false {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hμ : μB {true} = ENNReal.ofReal q) (x : ℕ) :
    markMeasure μB {ω : ℕ → Bool | ω x = false} = ENNReal.ofReal (1 - q) := by
  have hcompl : (fun ω : ℕ → Bool => ω x) ⁻¹' {false}
      = ((fun ω : ℕ → Bool => ω x) ⁻¹' {true})ᶜ := by
    ext ω; simp
  have hm : MeasurableSet ((fun ω : ℕ → Bool => ω x) ⁻¹' {true}) :=
    measurable_pi_apply x (measurableSet_singleton true)
  have htrue : markMeasure μB ((fun ω : ℕ → Bool => ω x) ⁻¹' {true}) = ENNReal.ofReal q := by
    have := markMeasure_true (μB := μB) hμ x
    exact this
  have key : markMeasure μB ((fun ω : ℕ → Bool => ω x) ⁻¹' {false}) = ENNReal.ofReal (1 - q) := by
    rw [hcompl, measure_compl hm (measure_ne_top _ _), htrue, measure_univ,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0]
  exact key

/-! ### Integration against an independent `Bool`-valued variable -/

/-- **Two-valued independence.**  If `B` is a `Bool`-valued variable independent of `Y`, then the
expectation of `F (B ω) (Y ω)` splits into the two branches weighted by the probabilities
`P(B = true)`, `P(B = false)`.  This is the step that turns the one-step recursion into a
recursion for the exponential moments. -/
lemma lintegral_bool_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : Ω → Bool} {Y : Ω → ℝ}
    (hB : Measurable B) (hY : Measurable Y) (hind : IndepFun B Y P)
    (F : Bool → ℝ → ℝ≥0∞) (hF : ∀ b, Measurable (F b)) :
    ∫⁻ ω, F (B ω) (Y ω) ∂P
      = (∫⁻ ω, F true (Y ω) ∂P) * P (B ⁻¹' {true})
        + (∫⁻ ω, F false (Y ω) ∂P) * P (B ⁻¹' {false}) := by
  have hFm : Measurable (fun z : Bool × ℝ => F z.1 z.2) := by
    have h1 : Measurable fun z : Bool × ℝ => F true z.2 := (hF true).comp measurable_snd
    have h2 : Measurable fun z : Bool × ℝ => F false z.2 := (hF false).comp measurable_snd
    have h3 : MeasurableSet {z : Bool × ℝ | z.1 = true} :=
      measurable_fst (measurableSet_singleton true)
    have heq : (fun z : Bool × ℝ => F z.1 z.2)
        = fun z => if z.1 = true then F true z.2 else F false z.2 := by
      funext z
      obtain ⟨b, y⟩ := z
      cases b <;> simp
    rw [heq]
    exact Measurable.ite h3 h1 h2
  have hpair : Measurable fun ω => (B ω, Y ω) := hB.prodMk hY
  calc ∫⁻ ω, F (B ω) (Y ω) ∂P
      = ∫⁻ z : Bool × ℝ, F z.1 z.2 ∂(P.map fun ω => (B ω, Y ω)) := by
        rw [lintegral_map hFm hpair]
    _ = ∫⁻ z : Bool × ℝ, F z.1 z.2 ∂((P.map B).prod (P.map Y)) := by
        rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable]
    _ = ∫⁻ b, ∫⁻ y, F b y ∂(P.map Y) ∂(P.map B) := by
        rw [lintegral_prod _ hFm.aemeasurable]
    _ = ∫⁻ b, ∫⁻ ω, F b (Y ω) ∂P ∂(P.map B) := by
        exact lintegral_congr fun b => lintegral_map (hF b) hY
    _ = (∫⁻ ω, F true (Y ω) ∂P) * (P.map B) {true}
          + (∫⁻ ω, F false (Y ω) ∂P) * (P.map B) {false} := by
        rw [lintegral_fintype, Fintype.sum_bool]
    _ = (∫⁻ ω, F true (Y ω) ∂P) * P (B ⁻¹' {true})
          + (∫⁻ ω, F false (Y ω) ∂P) * P (B ⁻¹' {false}) := by
        rw [Measure.map_apply hB (measurableSet_singleton true),
          Measure.map_apply hB (measurableSet_singleton false)]

end

end SwarmMarks
