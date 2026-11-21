import SwarmDiameter.CycleOccupation
import SwarmDiameter.DelayedRenewal
import SwarmDiameter.FirstInterval

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Swarming.CycleOccupation

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

private theorem observation_prob_eq_first_interval {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} {X : ℕ → Ω → E} (hT : Measurable T) (hX : ∀ t, Measurable (X t))
    {A : Set E} (hA : MeasurableSet A)
    (hfactor : ∀ t k : ℕ, μ.real {ω | T ω = t ∧ X (t + 1 + k) ω ∈ A} =
      μ.real {ω | T ω = t} * μ.real {ω | X k ω ∈ A}) :
    ∀ n, μ.real {ω | X n ω ∈ A} =
      ∑ t ∈ range (n + 1), μ.real {ω | t ≤ T ω ∧ X t ω ∈ A} *
        ArithmeticRenewal.renewalMass (fun j => μ.real {ω | T ω = j}) (n - t) := by
  let p (t : ℕ) := μ.real {ω | T ω = t}
  let f (t : ℕ) := μ.real {ω | t ≤ T ω ∧ X t ω ∈ A}
  let v (t : ℕ) := μ.real {ω | X t ω ∈ A}
  have hzero : v 0 = f 0 := by simp [v, f]
  let S (ω : Ω) := T ω + 1
  have hS : Measurable S := hT.add measurable_const
  have hdelay (t k : ℕ) : μ.real {ω | S ω = t ∧ X (t + k) ω ∈ A} =
      μ.real {ω | S ω = t} * μ.real {ω | X k ω ∈ A} := by
    cases t with
    | zero => simp [S]
    | succ t =>
      have heq (ω : Ω) : S ω = t + 1 ↔ T ω = t := by
        change T ω + 1 = t + 1 ↔ T ω = t
        omega
      simpa only [Nat.succ_eq_add_one, heq] using hfactor t k
  have hu (n : ℕ) : v (n + 1) = f (n + 1) + ∑ t ∈ range (n + 1), p t * v (n - t) := by
    have h := observation_prob_eq_delay hS hX hA hdelay (n + 1)
    have htail : {ω | n + 1 < S ω ∧ X (n + 1) ω ∈ A} =
        {ω | n + 1 ≤ T ω ∧ X (n + 1) ω ∈ A} := by
      ext ω
      simp only [Set.mem_ofPred_eq, S, Nat.lt_succ_iff]
    have hsum (t : ℕ) : μ.real {ω | S ω = t + 1} * v (n + 1 - (t + 1)) =
        p t * v (n - t) := by
      have heq (ω : Ω) : S ω = t + 1 ↔ T ω = t := by
        change T ω + 1 = t + 1 ↔ T ω = t
        omega
      simp only [p, heq, Nat.succ_sub_succ_eq_sub]
    have hz : μ.real {ω | S ω = 0} * v (n + 1 - 0) = 0 := by simp [S]
    change v (n + 1) = μ.real {ω | n + 1 < S ω ∧ X (n + 1) ω ∈ A} +
      ∑ t ∈ range (n + 1 + 1), μ.real {ω | S ω = t} * v (n + 1 - t) at h
    rw [htail, sum_range_succ', hz, add_zero] at h
    simpa only [f, hsum] using h
  exact ArithmeticRenewal.eq_renewalReward_of_first_interval hzero hu

/-- The first-interval factorization is sufficient for the renewal occupation
limit. The first interval has duration `T + 1`. -/
theorem observation_prob_tendsto_of_first_interval {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} {X : ℕ → Ω → E} (hT : Measurable T) (hX : ∀ t, Measurable (X t))
    (hfin : (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) ≠ ∞)
    (h₁ : 0 < μ.real {ω | T ω = 0}) {A : Set E} (hA : MeasurableSet A)
    (hfactor : ∀ t k : ℕ, μ.real {ω | T ω = t ∧ X (t + 1 + k) ω ∈ A} =
      μ.real {ω | T ω = t} * μ.real {ω | X k ω ∈ A}) :
    Tendsto (fun n => μ.real {ω | X n ω ∈ A}) atTop
      (𝓝 ((occupationLaw μ hT hX hfin).toMeasure.real A)) := by
  have heq := observation_prob_eq_first_interval hT hX hA hfactor
  exact (renewalReward_tendsto_occupationLaw μ hT hX hfin h₁ hA).congr (fun n => (heq n).symm)

/-- The expected occupation in the first interval bounds every observation
probability. -/
theorem observation_prob_le_occupation_of_first_interval {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} {X : ℕ → Ω → E} (hT : Measurable T) (hX : ∀ t, Measurable (X t))
    (hfin : (∫⁻ ω, (↑(T ω + 1) : ℝ≥0∞) ∂μ) ≠ ∞) {A : Set E} (hA : MeasurableSet A)
    (hfactor : ∀ t k : ℕ, μ.real {ω | T ω = t ∧ X (t + 1 + k) ω ∈ A} =
      μ.real {ω | T ω = t} * μ.real {ω | X k ω ∈ A}) (n : ℕ) :
    μ.real {ω | X n ω ∈ A} ≤ ∑' t : ℕ, μ.real {ω | t ≤ T ω ∧ X t ω ∈ A} := by
  let f (t : ℕ) := μ.real {ω | t ≤ T ω ∧ X t ω ∈ A}
  let p (t : ℕ) := μ.real {ω | T ω = t}
  have hf₀ : (∑' t : ℕ, μ {ω | t ≤ T ω ∧ X t ω ∈ A}) ≠ ∞ := by
    rw [← occupationMeasure_apply μ hT hX hA]
    apply ne_top_of_le_ne_top hfin
    rw [← occupationMeasure_univ μ hT hX]
    exact measure_mono (subset_univ _)
  have hf : Summable f := ENNReal.summable_toReal hf₀
  have hsum := tsum_duration_prob μ hT
  have hp : Summable p := ENNReal.summable_toReal (by rw [hsum]; exact ENNReal.one_ne_top)
  have hmass : ∑' t, p t = 1 := by
    simpa only [p, measureReal_def, hsum, ENNReal.toReal_one] using
      (ENNReal.tsum_toReal_eq (f := fun t : ℕ => μ {ω | T ω = t})
        (fun _ => measure_ne_top μ _)).symm
  have hb := ArithmeticRenewal.renewalMass_bounds (p := p)
    (fun _ => measureReal_nonneg) hp hmass
  change _ ≤ ∑' t, f t
  calc
    _ = ∑ t ∈ range (n + 1), f t * ArithmeticRenewal.renewalMass p (n - t) :=
      observation_prob_eq_first_interval hT hX hA hfactor n
    _ ≤ ∑ t ∈ range (n + 1), f t := sum_le_sum (fun t _ =>
      mul_le_of_le_one_right (show 0 ≤ f t from measureReal_nonneg) (hb (n - t)).2)
    _ ≤ _ := hf.sum_le_tsum _ (fun _ _ => measureReal_nonneg)

end Swarming.CycleOccupation
