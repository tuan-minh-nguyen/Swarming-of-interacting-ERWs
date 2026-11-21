import SwarmDiameter.CycleOccupation
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.IdentDistrib

/-!
# Renewal times and observations from independent intervals

Each interval is sampled from the same law. Its duration is positive and its
observation at an integer age is a measurable function of that interval.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Swarming.CycleOccupation

variable {Ω S E : Type*}

/-- The start time of interval `k`, with interval durations `T (Z j ω) + 1`. -/
def renewalTime (Z : ℕ → Ω → S) (T : S → ℕ) (k : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ range k, (T (Z j ω) + 1)

@[simp] theorem renewalTime_zero (Z : ℕ → Ω → S) (T : S → ℕ) (ω : Ω) :
    renewalTime Z T 0 ω = 0 := by simp [renewalTime]

theorem renewalTime_succ (Z : ℕ → Ω → S) (T : S → ℕ) (k : ℕ) (ω : Ω) :
    renewalTime Z T (k + 1) ω = renewalTime Z T k ω + (T (Z k ω) + 1) :=
  sum_range_succ _ _

theorem le_renewalTime (Z : ℕ → Ω → S) (T : S → ℕ) (k : ℕ) (ω : Ω) :
    k ≤ renewalTime Z T k ω := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [renewalTime_succ]
    omega

variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace E]

private theorem measurable_renewalTime {Z : ℕ → Ω → S} {T : S → ℕ}
    (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T) (k : ℕ) :
    Measurable (renewalTime Z T k) := by
  change Measurable (fun ω => ∑ j ∈ range k, (T (Z j ω) + 1))
  exact Finset.measurable_sum _ (fun j _ => (hT.comp (hZ j)).add measurable_const)

private theorem indepFun_renewalTime_cycle {μ : Measure Ω} {Z : ℕ → Ω → S}
    {T : S → ℕ} (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T)
    (hind : iIndepFun Z μ) (k : ℕ) :
    IndepFun (renewalTime Z T k) (Z k) μ := by
  let I := range k
  let J : Finset ℕ := {k}
  have hIJ : Disjoint I J := by simp [I, J]
  have h := iIndepFun.indepFun_finset I J hIJ hind hZ
  let F (x : I → S) := ∑ i : I, (T (x i) + 1)
  let G (x : J → S) := x ⟨k, by simp [J]⟩
  have hF : Measurable F :=
    Finset.measurable_sum _ (fun i _ => (hT.comp (measurable_pi_apply i)).add measurable_const)
  have hG : Measurable G := measurable_pi_apply _
  have e : (F ∘ (fun ω i => Z i ω)) = renewalTime Z T k := by
    funext ω
    exact sum_attach I (fun j => T (Z j ω) + 1)
  have e' : (G ∘ (fun ω i => Z i ω)) = Z k := rfl
  simpa only [e, e'] using h.comp hF hG

private theorem measureReal_inter_of_indepFun {μ : Measure Ω} {A : Type*}
    [MeasurableSpace A] {X : Ω → A} {Y : Ω → S}
    (h : IndepFun X Y μ) {s : Set A} {t : Set S} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    μ.real (X ⁻¹' s ∩ Y ⁻¹' t) = μ.real (X ⁻¹' s) * μ.real (Y ⁻¹' t) := by
  simp only [measureReal_def, h.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]

private theorem renewalTime_succ_prob {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {T : S → ℕ} (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T)
    (hind : iIndepFun Z μ) (hid : ∀ k, IdentDistrib (Z k) (Z 0) μ μ) (k n : ℕ) :
    μ.real {ω | renewalTime Z T (k + 1) ω = n + 1} =
      ∑ t ∈ range (n + 1), μ.real {ω | T (Z 0 ω) = t} *
        μ.real {ω | renewalTime Z T k ω = n - t} := by
  let A (t : ℕ) := {ω | renewalTime Z T k ω = n - t ∧ T (Z k ω) = t}
  have hsets : {ω | renewalTime Z T (k + 1) ω = n + 1} =
      ⋃ t ∈ range (n + 1), A t := by
    ext ω
    simp only [mem_ofPred_eq, renewalTime_succ, mem_iUnion, Finset.mem_range, A]
    constructor
    · intro h
      exact ⟨T (Z k ω), by omega, by omega, rfl⟩
    · rintro ⟨t, ht, h₁, h₂⟩
      omega
  have hdisj : PairwiseDisjoint (↑(range (n + 1))) A := by
    intro s _ t _ hst
    exact Set.disjoint_left.mpr (fun ω hs ht => hst (hs.2.symm.trans ht.2))
  have hm (t : ℕ) : MeasurableSet (A t) :=
    ((measurableSet_singleton (n - t)).preimage (measurable_renewalTime hZ hT k)).inter
      ((measurableSet_singleton t).preimage (hT.comp (hZ k)))
  rw [hsets, measureReal_biUnion_finset hdisj (fun t _ => hm t)]
  refine sum_congr rfl (fun t _ => ?_)
  have ht : MeasurableSet (T ⁻¹' {t}) := (measurableSet_singleton t).preimage hT
  have hprob := measureReal_inter_of_indepFun (indepFun_renewalTime_cycle hZ hT hind k)
    (measurableSet_singleton (n - t)) ht
  have heq := congrArg ENNReal.toReal ((hid k).measure_mem_eq ht)
  change μ.real {ω | T (Z k ω) = t} = μ.real {ω | T (Z 0 ω) = t} at heq
  calc
    _ = μ.real {ω | renewalTime Z T k ω = n - t} * μ.real {ω | T (Z k ω) = t} := hprob
    _ = _ := by rw [heq, mul_comm]

omit [MeasurableSpace S] in
private theorem sum_renewalTime_prob_eq {μ : Measure Ω}
    {Z : ℕ → Ω → S} {T : S → ℕ} {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ range (n + 1), μ.real {ω | renewalTime Z T k ω = n} =
      ∑ k ∈ range (m + 1), μ.real {ω | renewalTime Z T k ω = n} := by
  refine sum_subset (range_mono (by omega)) (fun k _ hk => ?_)
  have hz : {ω | renewalTime Z T k ω = n} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, Finset.mem_range, not_lt] at hk ⊢
    have hle := le_renewalTime Z T k ω
    omega
  rw [hz, measureReal_empty]

/-- The recurrence-defined renewal mass equals the sum of the arrival probabilities. -/
theorem renewalMass_eq_sum_renewalTime_prob {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {T : S → ℕ} (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T)
    (hind : iIndepFun Z μ) (hid : ∀ k, IdentDistrib (Z k) (Z 0) μ μ) (n : ℕ) :
    ArithmeticRenewal.renewalMass (fun t => μ.real {ω | T (Z 0 ω) = t}) n =
      ∑ k ∈ range (n + 1), μ.real {ω | renewalTime Z T k ω = n} := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [measureReal_def]
    | succ n =>
      rw [ArithmeticRenewal.renewalMass_succ, sum_range_succ'
        (fun k => μ.real {ω | renewalTime Z T k ω = n + 1})]
      have hz : {ω | renewalTime Z T 0 ω = n + 1} = ∅ := by
        ext ω
        simp
      rw [hz, measureReal_empty, add_zero]
      simp_rw [renewalTime_succ_prob hZ hT hind hid]
      rw [sum_comm]
      simp only [← mul_sum]
      refine sum_congr rfl (fun t ht => ?_)
      rw [ih (n - t) (by omega)]
      rw [sum_renewalTime_prob_eq (Nat.sub_le n t)]

omit [MeasurableSpace Ω] [MeasurableSpace S] in
private theorem strictMono_renewalTime (Z : ℕ → Ω → S) (T : S → ℕ) (ω : Ω) :
    StrictMono (fun k => renewalTime Z T k ω) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  rw [renewalTime_succ]
  omega

omit [MeasurableSpace Ω] [MeasurableSpace S] in
private theorem exists_renewalInterval (Z : ℕ → Ω → S) (T : S → ℕ) (n : ℕ) (ω : Ω) :
    ∃ k, renewalTime Z T k ω ≤ n ∧ n < renewalTime Z T (k + 1) ω := by
  have h : ∃ k, n < renewalTime Z T (k + 1) ω :=
    ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_renewalTime Z T (n + 1) ω)⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  cases hk : Nat.find h with
  | zero => simp
  | succ k =>
    exact Nat.le_of_not_gt (Nat.find_min h (by omega : k < Nat.find h))

omit [MeasurableSpace Ω] [MeasurableSpace S] in
private theorem renewalInterval_unique {Z : ℕ → Ω → S} {T : S → ℕ}
    {n k l : ℕ} {ω : Ω} (hk₀ : renewalTime Z T k ω ≤ n)
    (hk₁ : n < renewalTime Z T (k + 1) ω) (hl₀ : renewalTime Z T l ω ≤ n)
    (hl₁ : n < renewalTime Z T (l + 1) ω) : k = l := by
  apply le_antisymm
  · by_contra! h
    have hle := (strictMono_renewalTime Z T ω).monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hle.trans hk₀)) hl₁
  · by_contra! h
    have hle := (strictMono_renewalTime Z T ω).monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hle.trans hl₀)) hk₁

/-- The distribution at time `n` is obtained by summing over the last renewal time. -/
theorem observation_prob_eq_renewalReward {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {T : S → ℕ} {Y : ℕ → S → E} {X : ℕ → Ω → E}
    (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hind : iIndepFun Z μ) (hid : ∀ k, IdentDistrib (Z k) (Z 0) μ μ)
    (hX : ∀ n k, ∀ᵐ ω ∂μ, renewalTime Z T k ω ≤ n →
      n < renewalTime Z T (k + 1) ω → X n ω = Y (n - renewalTime Z T k ω) (Z k ω))
    (n : ℕ) {A : Set E} (hA : MeasurableSet A) :
    μ.real {ω | X n ω ∈ A} =
      ∑ t ∈ range (n + 1), μ.real {ω | t ≤ T (Z 0 ω) ∧ Y t (Z 0 ω) ∈ A} *
        ArithmeticRenewal.renewalMass (fun t => μ.real {ω | T (Z 0 ω) = t}) (n - t) := by
  let R (t : ℕ) := {z | t ≤ T z ∧ Y t z ∈ A}
  let B (q : ℕ × ℕ) := {ω | renewalTime Z T q.2 ω = n - q.1 ∧ Z q.2 ω ∈ R q.1}
  let K := (range (n + 1)).product (range (n + 1))
  have hR (t : ℕ) : MeasurableSet (R t) :=
    (measurableSet_Ici.preimage hT).inter (hY t hA)
  have hB (q : ℕ × ℕ) : MeasurableSet (B q) :=
    ((measurableSet_singleton _).preimage (measurable_renewalTime hZ hT _)).inter (hZ _ (hR _))
  have hwindow {q : ℕ × ℕ} {ω : Ω} (hq : q ∈ K) (h : ω ∈ B q) :
      renewalTime Z T q.2 ω ≤ n ∧ n < renewalTime Z T (q.2 + 1) ω := by
    have ht := Finset.mem_range.mp (Finset.mem_product.mp hq).1
    obtain ⟨h₁, h₂ : q.1 ≤ T (Z q.2 ω) ∧ Y q.1 (Z q.2 ω) ∈ A⟩ := h
    rw [renewalTime_succ, h₁]
    omega
  have hdisj : PairwiseDisjoint (↑K) B := by
    intro q hq q' hq' hne
    refine Set.disjoint_left.mpr (fun ω h h' => hne ?_)
    obtain ⟨hl, hu⟩ := hwindow hq h
    obtain ⟨hl', hu'⟩ := hwindow hq' h'
    have he := renewalInterval_unique hl hu hl' hu'
    have h₁ : renewalTime Z T q.2 ω = n - q.1 := h.1
    have h₂ : renewalTime Z T q'.2 ω = n - q'.1 := h'.1
    have ht := Finset.mem_range.mp (Finset.mem_product.mp hq).1
    have ht' := Finset.mem_range.mp (Finset.mem_product.mp hq').1
    rw [he] at h₁
    exact Prod.ext (by omega) he
  have hsets : {ω | X n ω ∈ A} =ᵐ[μ] ⋃ q ∈ K, B q := by
    filter_upwards [ae_all_iff.mpr (hX n)] with ω h
    apply propext
    change X n ω ∈ A ↔ ω ∈ ⋃ q ∈ K, B q
    simp only [mem_iUnion]
    constructor
    · intro hmem
      obtain ⟨k, hl, hu⟩ := exists_renewalInterval Z T n ω
      have hk := le_renewalTime Z T k ω
      have ht : n - renewalTime Z T k ω ≤ T (Z k ω) := by
        rw [renewalTime_succ] at hu
        omega
      rw [h k hl hu] at hmem
      refine ⟨(n - renewalTime Z T k ω, k), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
      refine ⟨?_, ht, hmem⟩
      change renewalTime Z T k ω = n - (n - renewalTime Z T k ω)
      omega
    · rintro ⟨q, hq, hmem⟩
      obtain ⟨hl, hu⟩ := hwindow hq hmem
      have ht := Finset.mem_range.mp (Finset.mem_product.mp hq).1
      have ha : n - renewalTime Z T q.2 ω = q.1 := by
        have h₁ : renewalTime Z T q.2 ω = n - q.1 := hmem.1
        omega
      rw [h _ hl hu, ha]
      exact hmem.2.2
  have hprod (t k : ℕ) : μ.real (B (t, k)) =
      μ.real {ω | t ≤ T (Z 0 ω) ∧ Y t (Z 0 ω) ∈ A} *
        μ.real {ω | renewalTime Z T k ω = n - t} := by
    have hprob := measureReal_inter_of_indepFun (indepFun_renewalTime_cycle hZ hT hind k)
      (measurableSet_singleton (n - t)) (hR t)
    have heq := congrArg ENNReal.toReal ((hid k).measure_mem_eq (hR t))
    change μ.real (Z k ⁻¹' R t) = μ.real (Z 0 ⁻¹' R t) at heq
    calc
      _ = μ.real (renewalTime Z T k ⁻¹' {n - t}) * μ.real (Z k ⁻¹' R t) := hprob
      _ = _ := by rw [heq, mul_comm]; rfl
  rw [measureReal_congr hsets, measureReal_biUnion_finset hdisj (fun q _ => hB q)]
  calc
    _ = ∑ t ∈ range (n + 1), ∑ k ∈ range (n + 1), μ.real (B (t, k)) :=
      Finset.sum_product (range (n + 1)) (range (n + 1)) (fun q => μ.real (B q))
    _ = _ := by
      simp only [hprod, ← mul_sum]
      refine sum_congr rfl (fun t _ => ?_)
      rw [renewalMass_eq_sum_renewalTime_prob hZ hT hind hid,
        sum_renewalTime_prob_eq (Nat.sub_le n t)]

/-- The observation probabilities converge to the occupation law on every
measurable set. -/
theorem observation_prob_tendsto {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {T : S → ℕ} {Y : ℕ → S → E} {X : ℕ → Ω → E}
    (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hind : iIndepFun Z μ) (hid : ∀ k, IdentDistrib (Z k) (Z 0) μ μ)
    (hcycle : ∀ n k, ∀ᵐ ω ∂μ, renewalTime Z T k ω ≤ n →
      n < renewalTime Z T (k + 1) ω → X n ω = Y (n - renewalTime Z T k ω) (Z k ω))
    (hfin : (∫⁻ ω, (↑(T (Z 0 ω) + 1) : ℝ≥0∞) ∂μ) ≠ ∞)
    (h₁ : 0 < μ.real {ω | T (Z 0 ω) = 0}) {A : Set E} (hA : MeasurableSet A) :
    Tendsto (fun n => μ.real {ω | X n ω ∈ A}) atTop
      (𝓝 ((occupationLaw μ (hT.comp (hZ 0)) (fun t => (hY t).comp (hZ 0)) hfin).toMeasure.real
        A)) := by
  rw [funext fun n => observation_prob_eq_renewalReward hZ hT hY hind hid hcycle n hA]
  exact renewalReward_tendsto_occupationLaw μ (hT.comp (hZ 0))
    (fun t => (hY t).comp (hZ 0)) hfin h₁ hA

/-- Convergence in distribution to the normalized occupation measure. -/
theorem tendstoInDistribution_occupationLaw [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → S} {T : S → ℕ} {Y : ℕ → S → E} {X : ℕ → Ω → E}
    (hZ : ∀ i, Measurable (Z i)) (hT : Measurable T) (hY : ∀ t, Measurable (Y t))
    (hind : iIndepFun Z μ) (hid : ∀ k, IdentDistrib (Z k) (Z 0) μ μ)
    (hX : ∀ n, Measurable (X n))
    (hcycle : ∀ n k, ∀ᵐ ω ∂μ, renewalTime Z T k ω ≤ n →
      n < renewalTime Z T (k + 1) ω → X n ω = Y (n - renewalTime Z T k ω) (Z k ω))
    (hfin : (∫⁻ ω, (↑(T (Z 0 ω) + 1) : ℝ≥0∞) ∂μ) ≠ ∞)
    (h₁ : 0 < μ.real {ω | T (Z 0 ω) = 0}) :
    TendstoInDistribution X atTop (id : E → E) (fun _ => μ)
      (occupationLaw μ (hT.comp (hZ 0)) (fun t => (hY t).comp (hZ 0)) hfin).toMeasure := by
  let ν := occupationLaw μ (hT.comp (hZ 0)) (fun t => (hY t).comp (hZ 0)) hfin
  let μs (n : ℕ) : ProbabilityMeasure E :=
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  have hid' : AEMeasurable (id : E → E) ν.toMeasure := measurable_id.aemeasurable
  refine ⟨fun n => (hX n).aemeasurable, hid', ?_⟩
  change Tendsto μs atTop (𝓝 (⟨ν.toMeasure.map id,
    Measure.isProbabilityMeasure_map hid'⟩ : ProbabilityMeasure E))
  rw [show (⟨ν.toMeasure.map id, Measure.isProbabilityMeasure_map hid'⟩ :
    ProbabilityMeasure E) = ν from Subtype.ext Measure.map_id]
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro A hA
  have hp := observation_prob_tendsto hZ hT hY hind hid hcycle hfin h₁ hA.measurableSet
  have hprob (n : ℕ) : (μs n).toMeasure.real A = μ.real {ω | X n ω ∈ A} := by
    change (μ.map (X n)).real A = _
    rw [measureReal_def, Measure.map_apply (hX n) hA.measurableSet]
    rfl
  have hreal : Tendsto (fun n => (μs n).toMeasure.real A) atTop (𝓝 (ν.toMeasure.real A)) :=
    hp.congr (fun n => (hprob n).symm)
  have hlim : Tendsto (fun n => (μs n).toMeasure A) atTop (𝓝 (ν.toMeasure A)) := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.tendsto_ofReal hreal
  rw [hlim.liminf_eq]

end Swarming.CycleOccupation
