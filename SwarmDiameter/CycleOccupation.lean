import SwarmDiameter.ArithmeticRenewal
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Occupation during a renewal interval

An interval has duration `T + 1` and observations `Y t` for `0 ≤ t ≤ T`.
The occupation measure is the sum of the laws of the observations restricted
to those times. Its total mass is the mean duration.
-/

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Swarming.CycleOccupation

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The expected number of observations in each measurable set during one interval. -/
noncomputable def occupationMeasure (μ : Measure Ω) (T : Ω → ℕ) (Y : ℕ → Ω → E)
    (_hT : Measurable T) (_hY : ∀ t, Measurable (Y t)) : Measure E :=
  Measure.sum fun t : ℕ => (μ.restrict {ω | t ≤ T ω}).map (Y t)

theorem occupationMeasure_apply (μ : Measure Ω) {T : Ω → ℕ} {Y : ℕ → Ω → E}
    (hT : Measurable T) (hY : ∀ t, Measurable (Y t)) {A : Set E} (hA : MeasurableSet A) :
    occupationMeasure μ T Y hT hY A = ∑' t : ℕ, μ {ω | t ≤ T ω ∧ Y t ω ∈ A} := by
  rw [occupationMeasure, Measure.sum_apply _ hA]
  congr 1 with t
  rw [Measure.map_apply (hY t) hA, Measure.restrict_apply (hY t hA), Set.inter_comm]
  rfl

theorem occupationMeasure_univ (μ : Measure Ω) {T : Ω → ℕ} {Y : ℕ → Ω → E}
    (hT : Measurable T) (hY : ∀ t, Measurable (Y t)) :
    occupationMeasure μ T Y hT hY univ = ∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ := by
  let A (t : ℕ) := {ω | t ≤ T ω}
  have hA (t : ℕ) : MeasurableSet (A t) := measurableSet_Ici.preimage hT
  have hsum (ω : Ω) : ∑' t : ℕ, (A t).indicator (fun _ => (1 : ℝ≥0∞)) ω =
      ↑(T ω + 1) := by
    rw [tsum_eq_sum (s := range (T ω + 1))]
    · calc
        _ = ∑ _ ∈ range (T ω + 1), (1 : ℝ≥0∞) := by
          apply sum_congr rfl
          intro t ht
          have h : ω ∈ A t := Nat.lt_succ_iff.mp (mem_range.mp ht)
          exact indicator_of_mem h _
        _ = _ := by simp
    · intro t ht
      have h : ω ∉ A t := fun h => ht (mem_range.mpr (Nat.lt_succ_iff.mpr h))
      exact indicator_of_notMem h _
  calc
    _ = ∑' t : ℕ, μ (A t) := by
      simp only [occupationMeasure_apply μ hT hY MeasurableSet.univ, Set.mem_univ, and_true, A]
    _ = ∑' t : ℕ, ∫⁻ ω, (A t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      exact tsum_congr fun t => (lintegral_indicator_one (hA t)).symm
    _ = ∫⁻ ω, ∑' t : ℕ, (A t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
      (lintegral_tsum fun t => (measurable_const.indicator (hA t)).aemeasurable).symm
    _ = _ := lintegral_congr hsum

/-- The occupation measure divided by the finite mean duration. -/
noncomputable def occupationLaw (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → ℕ}
    {Y : ℕ → Ω → E} (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hfin : (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) ≠ ∞) : ProbabilityMeasure E := by
  let κ := occupationMeasure μ T Y hT hY
  have hκ : κ univ ≠ ∞ := by
    simpa only [κ, occupationMeasure_univ] using hfin
  have h₁ : (1 : ℝ≥0∞) ≤ κ univ := by
    change 1 ≤ occupationMeasure μ T Y hT hY univ
    rw [occupationMeasure_univ]
    calc
      _ = ∫⁻ _ : Ω, 1 ∂μ := by simp
      _ ≤ _ := lintegral_mono (fun ω => by simp)
  exact ⟨(κ univ)⁻¹ • κ, ⟨by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (ne_of_gt (zero_lt_one.trans_le h₁)) hκ]⟩⟩

theorem occupationLaw_real_apply (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → ℕ}
    {Y : ℕ → Ω → E} (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hfin : (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) ≠ ∞) {A : Set E} (hA : MeasurableSet A) :
    (occupationLaw μ hT hY hfin).toMeasure.real A =
      (∑' t : ℕ, μ.real {ω | t ≤ T ω ∧ Y t ω ∈ A}) /
        (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ).toReal := by
  change (((occupationMeasure μ T Y hT hY univ)⁻¹ •
    occupationMeasure μ T Y hT hY).real A) = _
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    occupationMeasure_univ, occupationMeasure_apply μ hT hY hA,
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top μ _), div_eq_mul_inv, mul_comm]
  rfl

private theorem tsum_duration_prob (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → ℕ} (hT : Measurable T) : ∑' t : ℕ, μ {ω | T ω = t} = 1 := by
  let A (t : ℕ) := T ⁻¹' {t}
  change ∑' t : ℕ, μ (A t) = 1
  have hdisj : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun ω hi hj => hij ((show T ω = i from hi).symm.trans hj))
  have hu : (⋃ t : ℕ, A t) = univ := by
    ext ω
    simp [A]
  rw [← measure_iUnion hdisj (fun t => (measurableSet_singleton t).preimage hT), hu, measure_univ]

private theorem lintegral_duration (μ : Measure Ω) {T : Ω → ℕ} (hT : Measurable T) :
    (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) = ∑' t : ℕ, ↑(t + 1) * μ {ω | T ω = t} := by
  have h := lintegral_comp (μ := μ)
    (measurable_of_countable (fun t : ℕ => (↑(t + 1) : ℝ≥0∞))) hT
  change lintegral μ ((fun t : ℕ => (↑(t + 1) : ℝ≥0∞)) ∘ T) = _
  rw [h, lintegral_countable']
  refine tsum_congr (fun t => ?_)
  rw [Measure.map_apply hT (measurableSet_singleton t)]
  rfl

/-- The renewal-reward convolution converges to the occupation probability of each
measurable set. The interarrival law and the rewards come from the same interval. -/
theorem renewalReward_tendsto_occupationLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → ℕ} {Y : ℕ → Ω → E} (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hfin : (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) ≠ ∞)
    (h₁ : 0 < μ.real {ω | T ω = 0}) {A : Set E} (hA : MeasurableSet A) :
    Tendsto (fun n => ∑ t ∈ range (n + 1), μ.real {ω | t ≤ T ω ∧ Y t ω ∈ A} *
      ArithmeticRenewal.renewalMass (fun j => μ.real {ω | T ω = j}) (n - t)) atTop
      (𝓝 ((occupationLaw μ hT hY hfin).toMeasure.real A)) := by
  let p (t : ℕ) := μ.real {ω | T ω = t}
  let f (t : ℕ) := μ.real {ω | t ≤ T ω ∧ Y t ω ∈ A}
  have hp (t : ℕ) : 0 ≤ p t := ENNReal.toReal_nonneg
  have hps := tsum_duration_prob μ hT
  have hs : Summable p := ENNReal.summable_toReal (by rw [hps]; exact ENNReal.one_ne_top)
  have hsum : ∑' t, p t = 1 := by
    simpa only [p, measureReal_def, hps, ENNReal.toReal_one] using
      (ENNReal.tsum_toReal_eq (f := fun t => μ {ω | T ω = t})
        (fun _ => measure_ne_top μ _)).symm
  have hmean := lintegral_duration μ hT
  have hmean' : (∑' t : ℕ, (↑(t + 1) : ℝ≥0∞) * μ {ω | T ω = t}) ≠ ∞ := hmean ▸ hfin
  have hcast (t : ℕ) : ((↑(t + 1) : ℝ≥0∞) * μ {ω | T ω = t}).toReal =
      (↑(t + 1) : ℝ) * p t := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, p, measureReal_def]
  have hmean_summable : Summable (fun t : ℕ => ↑(t + 1) * p t) := by
    simpa only [hcast] using ENNReal.summable_toReal hmean'
  have hmean_real : (∑' t : ℕ, ↑(t + 1) * p t) =
      (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ).toReal := by
    rw [hmean, ENNReal.tsum_toReal_eq
      (fun t => ENNReal.mul_ne_top (ENNReal.natCast_ne_top (t + 1)) (measure_ne_top μ _))]
    simp only [hcast]
  have hf₀ : (∑' t : ℕ, μ {ω | t ≤ T ω ∧ Y t ω ∈ A}) ≠ ∞ := by
    rw [← occupationMeasure_apply μ hT hY hA]
    apply ne_top_of_le_ne_top hfin
    rw [← occupationMeasure_univ μ hT hY]
    exact measure_mono (subset_univ _)
  have hf : Summable (fun t => |f t|) := by
    simpa only [f, measureReal_def, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.summable_toReal hf₀
  rw [occupationLaw_real_apply μ hT hY hfin hA, ← hmean_real]
  exact ArithmeticRenewal.renewalReward_tendsto_mean hp h₁ hs hsum hmean_summable hf

end Swarming.CycleOccupation
