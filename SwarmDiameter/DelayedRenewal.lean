import SwarmDiameter.ArithmeticRenewal
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Swarming.CycleOccupation

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]

private theorem delay_prob_sum {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} (hT : Measurable T) : ∑' t : ℕ, μ {ω | T ω = t} = 1 := by
  let A (t : ℕ) := T ⁻¹' {t}
  change ∑' t : ℕ, μ (A t) = 1
  have hdisj : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun ω hi hj => hij ((show T ω = i from hi).symm.trans hj))
  have hu : (⋃ t : ℕ, A t) = Set.univ := by
    ext ω
    simp [A]
  rw [← measure_iUnion hdisj (fun t => (measurableSet_singleton t).preimage hT), hu, measure_univ]

private theorem measureReal_delay_tail_tendsto {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} (hT : Measurable T) :
    Tendsto (fun n : ℕ => μ.real {ω | n < T ω}) atTop (𝓝 0) := by
  let A (n : ℕ) := {ω | n < T ω}
  have hm (n : ℕ) : MeasurableSet (A n) := measurableSet_Ioi.preimage hT
  have hanti : Antitone A := fun _ _ hab _ h => lt_of_le_of_lt hab h
  have hi : (⋂ n : ℕ, A n) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, A, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => (lt_irrefl (T ω)) (h (T ω))
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hm n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hi, measure_empty] at h
  simpa only [Function.comp_apply, measureReal_def, ENNReal.toReal_zero, A] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- Transfer a limit of event probabilities through a random finite initial delay. -/
theorem observation_prob_tendsto_of_delay {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {T : Ω → ℕ} {X : ℕ → Ω → E}
    {Y : ℕ → Ω' → E} {A : Set E} {c : ℝ}
    (hT : Measurable T) (hX : ∀ n, Measurable (X n)) (hA : MeasurableSet A)
    (hfactor : ∀ t k : ℕ, μ.real {ω | T ω = t ∧ X (t + k) ω ∈ A} =
      μ.real {ω | T ω = t} * ν.real {ω | Y k ω ∈ A})
    (hlim : Tendsto (fun k : ℕ => ν.real {ω | Y k ω ∈ A}) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => μ.real {ω | X n ω ∈ A}) atTop (𝓝 c) := by
  let f (t : ℕ) := μ.real {ω | T ω = t}
  let u (k : ℕ) := ν.real {ω | Y k ω ∈ A}
  have hf : ∑' t : ℕ, μ {ω | T ω = t} = 1 := delay_prob_sum hT
  have hs : Summable (fun t => |f t|) := by
    simpa only [f, measureReal_def, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.summable_toReal (show (∑' t : ℕ, μ {ω | T ω = t}) ≠ ∞ by
        rw [hf]
        exact ENNReal.one_ne_top)
  have hmass : (∑' t : ℕ, f t) = 1 := by
    simpa only [f, measureReal_def, hf, ENNReal.toReal_one] using
      (ENNReal.tsum_toReal_eq (f := fun t : ℕ => μ {ω | T ω = t})
        (fun _ => measure_ne_top _ _)).symm
  have hu : ∀ k, |u k| ≤ 1 := by
    intro k
    rw [abs_of_nonneg (show 0 ≤ u k from measureReal_nonneg)]
    exact measureReal_le_one
  have hconv := ArithmeticRenewal.tendsto_convolution hlim hu hs
  rw [hmass, one_mul] at hconv
  let r (n : ℕ) := μ.real {ω | n < T ω ∧ X n ω ∈ A}
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (measureReal_delay_tail_tendsto hT) (fun _ => measureReal_nonneg)
      (fun n => measureReal_mono (fun _ h => h.1))
  have heq (n : ℕ) : μ.real {ω | X n ω ∈ A} =
      r n + ∑ t ∈ range (n + 1), f t * u (n - t) := by
    let B (t : ℕ) := {ω | T ω = t ∧ X n ω ∈ A}
    have hp : {ω | X n ω ∈ A} =
        {ω | n < T ω ∧ X n ω ∈ A} ∪ ⋃ t ∈ range (n + 1), B t := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Finset.mem_range, B]
      constructor
      · intro h
        by_cases ht : n < T ω
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr ⟨T ω, by omega, rfl, h⟩
      · rintro (⟨_, h⟩ | ⟨t, ht, he, h⟩) <;> exact h
    have hd : Disjoint {ω | n < T ω ∧ X n ω ∈ A}
        (⋃ t ∈ range (n + 1), B t) := by
      apply Set.disjoint_left.mpr
      intro ω hlate hearly
      have hgt : n < T ω := hlate.1
      simp only [Set.mem_iUnion, Finset.mem_range, B, Set.mem_ofPred_eq] at hearly
      obtain ⟨t, ht, heq, _⟩ := hearly
      omega
    have hm (t : ℕ) : MeasurableSet (B t) :=
      (measurableSet_singleton t).preimage hT |>.inter (hX n hA)
    have hdisj : PairwiseDisjoint (↑(range (n + 1))) B := by
      intro t _ v _ hne
      exact Set.disjoint_left.mpr (fun ω ht hv => hne (ht.1.symm.trans hv.1))
    have hmeas : MeasurableSet (⋃ t ∈ range (n + 1), B t) :=
      MeasurableSet.iUnion (fun t => MeasurableSet.iUnion (fun _ => hm t))
    rw [hp, measureReal_union hd hmeas, measureReal_biUnion_finset hdisj (fun t _ => hm t)]
    refine congrArg (r n + ·) (sum_congr rfl fun t ht => ?_)
    have htn : t ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht
    have htadd : t + (n - t) = n := by omega
    simpa only [B, htadd, f, u] using hfactor t (n - t)
  simpa only [← heq, zero_add] using hr.add hconv

/-- Setwise convergence of observation laws entails convergence in distribution. -/
theorem tendstoInDistribution_of_observation_prob_tendsto [TopologicalSpace E]
    [OpensMeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {ν : ProbabilityMeasure E} (hX : ∀ n, Measurable (X n))
    (h : ∀ A : Set E, MeasurableSet A →
      Tendsto (fun n => μ.real {ω | X n ω ∈ A}) atTop (𝓝 (ν.toMeasure.real A))) :
    TendstoInDistribution X atTop (id : E → E) (fun _ => μ) ν.toMeasure := by
  let μs (n : ℕ) : ProbabilityMeasure E :=
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  have hid : AEMeasurable (id : E → E) ν.toMeasure := measurable_id.aemeasurable
  refine ⟨fun n => (hX n).aemeasurable, hid, ?_⟩
  change Tendsto μs atTop (𝓝 (⟨ν.toMeasure.map id,
    Measure.isProbabilityMeasure_map hid⟩ : ProbabilityMeasure E))
  rw [show (⟨ν.toMeasure.map id, Measure.isProbabilityMeasure_map hid⟩ :
    ProbabilityMeasure E) = ν from Subtype.ext Measure.map_id]
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro A hA
  have hprob (n : ℕ) : (μs n).toMeasure.real A = μ.real {ω | X n ω ∈ A} := by
    change (μ.map (X n)).real A = _
    rw [measureReal_def, Measure.map_apply (hX n) hA.measurableSet]
    rfl
  have hreal : Tendsto (fun n => (μs n).toMeasure.real A) atTop (𝓝 (ν.toMeasure.real A)) :=
    (h A hA.measurableSet).congr (fun n => (hprob n).symm)
  have hlim : Tendsto (fun n => (μs n).toMeasure A) atTop (𝓝 (ν.toMeasure A)) := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.tendsto_ofReal hreal
  rw [hlim.liminf_eq]

end Swarming.CycleOccupation
