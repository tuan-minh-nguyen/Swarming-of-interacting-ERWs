/-
  **The generic shifted-seed recursion instantiated at the paper's mark law.**

  `ShiftRecCore.condExp_shiftRec_of_filtration` is abstract: it asks for an increasing family of
  enlargements `Kf g`, an `Kf g`-measurable potential `X g`, a fresh factor `Y (g+1)` independent
  of `Kf g` with mean `a`.  This file discharges *every* hypothesis in the paper's own mark model:
  the i.i.d. site marks `ω : ℕ → Bool` with law `markMeasure (boolMeasure q)`, the potential
  `hof p ω (r + g)` at the sites `r, r+1, …` of a **deterministic** record `r`, the one-site
  multiplier `rhoOf p (ω (r+g+1))`, and the enlargement family

      `Kf g = σ(ω 0, …, ω (r+g))`,   `K = σ(ω 0, …, ω r)`.

  The conclusion is the projected recursion at the deterministic record `r`

      `E[ h(r+g) | σ(ω 0..ω r) ] =ᵐ shiftRec a (h r) g`,   `a = ∫ rhoOf p d(boolMeasure q)`,

  with the seed entering as the conditional mean of `h(r)`.  This is the deterministic-record
  shifted recursion (the same statement S14 reaches by a bespoke induction), obtained here as a
  corollary of the generic API; it certifies that the API's hypotheses are satisfiable.

  **What is *not* here.**  `r` is deterministic.  The interacting array needs `r = M_n^j` random
  and `σ(ω 0..ω r)` replaced by the enlarged filtration (plus the record site's mark); the
  fresh-block statement for that random set is *not* proved here (direction B's target).
-/
import Swarm.Imports
import Swarm.MarkMoments
import Swarm.ShiftRecCore

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace SwarmShiftMarks

open SwarmMarks SwarmShift

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

/-! ### The prefix σ-algebra `σ(ω 0, …, ω n)` -/

/-- `σ(ω 0, …, ω n)` as the comap of the prefix projection. -/
@[reducible] def Gf (n : ℕ) : MeasurableSpace (ℕ → Bool) :=
  MeasurableSpace.comap (fun (ω : ℕ → Bool) (i : Fin (n + 1)) => ω i)
    (inferInstance : MeasurableSpace (Fin (n + 1) → Bool))

lemma measurable_prefix (n : ℕ) :
    Measurable (fun (ω : ℕ → Bool) (i : Fin (n + 1)) => ω i) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

lemma gf_le (n : ℕ) : Gf n ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  (measurable_prefix n).comap_le

/-- `σ(ω 0, …, ω r)` grows with `r`. -/
lemma gf_mono {a b : ℕ} (h : a ≤ b) : Gf  a ≤ Gf  b := by
  intro s hs
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  refine MeasurableSpace.measurableSet_comap.2
    ⟨(fun (v : Fin (b + 1) → Bool) (i : Fin (a + 1)) => v ⟨i.1, by omega⟩) ⁻¹' B, ?_, ?_⟩
  · exact hB.preimage (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  · ext ω
    rfl

/-- `hof p ω n` is a function of the prefix `ω 0, …, ω n`. -/
lemma measurable_hof_gf {p : ℝ} (hp0 : p ≠ 0) (n : ℕ) :
    Measurable[Gf n] (fun ω : ℕ → Bool => hof p ω n) := by
  have hfac : (fun ω : ℕ → Bool => hof p ω n)
      = (Hfun p n) ∘ (fun (ω : ℕ → Bool) (i : Fin (n + 1)) => ω i) := by
    funext ω
    exact hof_eq_Hfun p n ω
  rw [hfac]
  exact (measurable_Hfun hp0 n).comp (comap_measurable _)

/-! ### Bounds and integrability for the one-site multiplier and the potential -/

lemma abs_rhoOf_le_one' {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (b : Bool) :
    |rhoOf p b| ≤ 1 := by
  cases b with
  | false => simp [rhoOf]
  | true =>
      rw [rhoOf_true, abs_of_nonneg (by positivity), div_le_one (by linarith)]
      linarith

lemma int_rhoOf {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (n : ℕ) :
    Integrable (fun ω : ℕ → Bool => rhoOf p (ω n)) (markMeasure μB) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_rhoOf p).comp (measurable_pi_apply n)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_rhoOf_le_one' hp1 hp2 _

/-- One step of the potential grows the absolute value by at most `2`. -/
lemma abs_hstep_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (b : Bool) (h : ℝ) : |hstep p b h| ≤ |h| + 2 := by
  rw [hstep_eq_rho hp0]
  have hr : |rhoOf p b| ≤ 1 := abs_rhoOf_le_one' hp1 hp2 b
  have h1 : |1 + h| ≤ 1 + |h| := by simpa using abs_add_le (1 : ℝ) h
  calc |1 + rhoOf p b * (1 + h)| ≤ 1 + |rhoOf p b * (1 + h)| := by
        simpa using abs_add_le (1 : ℝ) (rhoOf p b * (1 + h))
    _ = 1 + |rhoOf p b| * |1 + h| := by rw [abs_mul]
    _ ≤ 1 + 1 * (1 + |h|) := by
        have h0 : (0 : ℝ) ≤ |rhoOf p b| := abs_nonneg _
        have h0' : (0 : ℝ) ≤ |1 + h| := abs_nonneg _
        nlinarith [mul_le_mul hr h1 h0' zero_le_one]
    _ = |h| + 2 := by ring

lemma abs_hof_le' {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (ω : ℕ → Bool) (n : ℕ) : |hof p ω n| ≤ 2 * (n : ℝ) + 3 := by
  induction n with
  | zero =>
      rw [hof_zero]
      have h := abs_hstep_le hp1 hp2 hp0 (ω 0) (1 : ℝ)
      rw [abs_one] at h
      push_cast
      linarith
  | succ k ih =>
      rw [hof_succ]
      have h := abs_hstep_le hp1 hp2 hp0 (ω (k + 1)) (hof p ω k)
      push_cast
      linarith

lemma int_hof' {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0) (n : ℕ) :
    Integrable (fun ω : ℕ → Bool => hof p ω n) (markMeasure μB) := by
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3))
    (measurable_hof hp0 n).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_hof_le' hp1 hp2 hp0 ω n

/-- The mean of a one-site function under the i.i.d. marks. -/
lemma integral_eval' {μB : Measure Bool} [IsProbabilityMeasure μB] (f : Bool → ℝ) (n : ℕ) :
    ∫ ω : ℕ → Bool, f (ω n) ∂(markMeasure μB) = ∫ b, f b ∂μB := by
  have hm : Measurable (fun ω : ℕ → Bool => ω n) := measurable_pi_apply n
  have hmap : (markMeasure μB).map (fun ω : ℕ → Bool => ω n) = μB := by
    unfold markMeasure
    exact Measure.infinitePi_map_eval (fun _ : ℕ => μB) n
  have key := integral_map (φ := fun ω : ℕ → Bool => ω n) (μ := markMeasure μB) (f := f)
    hm.aemeasurable (by fun_prop)
  rw [hmap] at key
  exact key.symm

/-! ### The instantiated recursion -/

/-- **The projected recursion at a deterministic record, from the generic API.**
For the paper's i.i.d. site marks and every deterministic `r`, the conditional means of the
potential at the sites `r, r+1, …` follow the shifted recursion started at `h(r)`. -/
theorem condExp_hof_shift {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : ℕ) :
    haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
    ∀ g : ℕ,
      condExp (Gf  r) (markMeasure (boolMeasure q))
          (fun ω : ℕ → Bool => hof p ω (r + g))
        =ᵐ[markMeasure (boolMeasure q)]
          shiftRec (∫ b, rhoOf p b ∂(boolMeasure q)) (fun ω => hof p ω r) g := by
  have : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  set a : ℝ := ∫ b, rhoOf p b ∂(boolMeasure q) with ha
  -- the potential sequence at the shifted sites
  set X : ℕ → (ℕ → Bool) → ℝ := fun g ω => hof p ω (r + g) with hX
  set Y : ℕ → (ℕ → Bool) → ℝ := fun k ω => rhoOf p (ω (r + k)) with hY
  have hXm : ∀ g, Measurable[Gf (r + g)] (X g) := by
    intro g
    exact measurable_hof_gf hp0 (r + g)
  have hXi : ∀ g, Integrable (X g) (markMeasure (boolMeasure q)) := fun g => int_hof' hp1 hp2 hp0 _
  have hrec : ∀ g, X (g + 1) = fun ω => 1 + Y (g + 1) ω * (1 + X g ω) := by
    intro g
    funext ω
    simp only [hX, hY, Nat.add_succ, hof_succ, hstep_eq_rho hp0]
  have hYi : ∀ g, Integrable (Y (g + 1)) (markMeasure (boolMeasure q)) := fun g => int_rhoOf hp1 hp2 _
  have hYm : ∀ g, Measurable (Y (g + 1)) := fun g =>
    (measurable_rhoOf p).comp (measurable_pi_apply (r + (g + 1)))
  have hYmean : ∀ g, ∫ ω, Y (g + 1) ω ∂(markMeasure (boolMeasure q)) = a := by
    intro g
    rw [hY, ha]
    simpa using integral_eval' (μB := boolMeasure q) (fun b => rhoOf p b) (r + (g + 1))
  have hind : ∀ g, Indep (MeasurableSpace.comap (Y (g + 1))
      (inferInstance : MeasurableSpace ℝ)) (Gf (r + g))
      (markMeasure (boolMeasure q)) := by
    intro g
    have hbase := indep_eval_succ (μB := boolMeasure q) (r + g)
    have hc := hbase.comp (measurable_rhoOf p) measurable_id
    have hc' : (fun ω : ℕ → Bool => rhoOf p (ω (r + g + 1)))
        ⟂ᵢ[markMeasure (boolMeasure q)]
          (fun (ω : ℕ → Bool) (i : Fin (r + g + 1)) => ω i) := by
      simpa [Function.comp_def] using hc
    have hfun : (fun ω : ℕ → Bool => rhoOf p (ω (r + g + 1))) = Y (g + 1) := by
      funext ω
      exact congrArg (fun n => rhoOf p (ω n)) (by omega)
    rw [hfun] at hc'
    have := (IndepFun_iff_Indep (fun ω : ℕ → Bool => Y (g + 1) ω)
      (fun (ω : ℕ → Bool) (i : Fin (r + g + 1)) => ω i) (markMeasure (boolMeasure q))).1 hc'
    simpa [Gf] using this
  have hK : Gf  r ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
    gf_le r
  have hKf : ∀ g, Gf  r ≤ Gf (r + g) :=
    fun g => gf_mono (Nat.le_add_right r g)
  have hKfle : ∀ g, Gf (r + g) ≤
      (inferInstance : MeasurableSpace (ℕ → Bool)) := fun g => gf_le (r + g)
  have hmain := condExp_shiftRec_of_filtration hK hKf hKfle X Y a hXm hXi hrec hYi hYm hYmean hind
  -- the seed is `σ(ω 0..ω r)`-measurable, so its conditional mean is itself
  intro g
  have hseed : condExp (Gf  r) (markMeasure (boolMeasure q))
      (X 0) =ᵐ[markMeasure (boolMeasure q)] (fun ω => hof p ω r) := by
    have hsm : StronglyMeasurable[Gf  r] (fun ω : ℕ → Bool => hof p ω r) :=
      (measurable_hof_gf hp0 r).stronglyMeasurable
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (gf_le r) hsm (hXi 0))
  have hX0 : X 0 = fun ω => hof p ω r := rfl
  rw [hX0] at hmain
  exact (hmain g).trans (shiftRec_congr hseed g)

end SwarmShiftMarks


