import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

open Finset MeasureTheory Set
open scoped ENNReal

namespace Swarming.Diameter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Sum the integrated bound over the time fibres of an integer-valued stopping time. -/
theorem stopped_trial_mass_ge (S : Ω → ℕ) {G : Set Ω} {B : ℕ → Set Ω}
    {q : ℝ} (hq : 0 ≤ q) (hG : ∀ s, MeasurableSet (G ∩ {ω | S ω = s}))
    (hB : ∀ s, MeasurableSet (B s))
    (htrial : ∀ s, q * μ.real (G ∩ {ω | S ω = s}) ≤
      μ.real (G ∩ {ω | S ω = s} ∩ B s)) :
    q * μ.real G ≤ μ.real (G ∩ {ω | ω ∈ B (S ω)}) := by
  let A (s : ℕ) := G ∩ {ω | S ω = s}
  have hA : (⋃ s, A s) = G := by ext ω; simp [A, ← Set.inter_iUnion]
  have hAB : (⋃ s, A s ∩ B s) = G ∩ {ω | ω ∈ B (S ω)} := by
    ext ω
    constructor
    · intro h
      obtain ⟨s, ⟨⟨hω, hs⟩, hb⟩⟩ := Set.mem_iUnion.mp h
      refine ⟨hω, ?_⟩
      change S ω = s at hs
      change ω ∈ B (S ω)
      rwa [hs]
    · rintro ⟨hω, hb⟩
      exact Set.mem_iUnion.mpr ⟨S ω, ⟨⟨hω, rfl⟩, hb⟩⟩
  have hd : Pairwise (fun s t => Disjoint (A s) (A t)) := by
    intro s t hne
    exact Set.disjoint_left.mpr fun _ hs ht => hne (hs.2.symm.trans ht.2)
  have hd' : Pairwise (fun s t => Disjoint (A s ∩ B s) (A t ∩ B t)) :=
    fun _ _ hne => (hd hne).mono Set.inter_subset_left Set.inter_subset_left
  have hsum : ENNReal.ofReal q * μ G ≤ μ (G ∩ {ω | ω ∈ B (S ω)}) := by
    rw [← hAB, ← hA, measure_iUnion hd hG, measure_iUnion hd' (fun t => (hG t).inter (hB t)),
      ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro t
    have ht := ENNReal.ofReal_le_ofReal (htrial t)
    simpa only [ENNReal.ofReal_mul hq, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)] using ht
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq, measureReal_def] using
    ENNReal.toReal_mono (measure_ne_top μ _) hsum

/-- The record times in the inclusive integer interval from `a` to `b`. -/
noncomputable def recordTimes (R : ℕ → Set Ω) (a b : ℕ) (ω : Ω) : Finset ℕ := by
  classical
  exact (Finset.Icc a b).filter fun t => ω ∈ R t

omit [MeasurableSpace Ω] in
theorem mem_recordTimes {R : ℕ → Set Ω} {a b t : ℕ} {ω : Ω} :
    t ∈ recordTimes R a b ω ↔ (a ≤ t ∧ t ≤ b) ∧ ω ∈ R t := by
  classical
  simp only [recordTimes, Finset.mem_filter, Finset.mem_Icc]

private def firstRecord (R : ℕ → Set Ω) (a t : ℕ) : Set Ω :=
  R t ∩ ⋂ s ∈ Finset.Ico a t, (R s)ᶜ

private theorem measurableSet_firstRecord {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {R : ℕ → Set Ω} (hR : ∀ t, MeasurableSet[ℱ t] (R t)) (a t : ℕ) :
    MeasurableSet[ℱ t] (firstRecord R a t) := by
  refine (hR t).inter (MeasurableSet.iInter (fun s => MeasurableSet.iInter (fun hs => ?_)))
  exact (ℱ.mono (Finset.mem_Ico.mp hs).2.le _ (hR s)).compl

omit [MeasurableSpace Ω] in
private theorem disjoint_firstRecord (R : ℕ → Set Ω) (a : ℕ) :
    Set.PairwiseDisjoint (Set.Ici a) (firstRecord R a) := by
  intro s hs t ht hne
  change Disjoint (firstRecord R a s) (firstRecord R a t)
  rw [Set.disjoint_left]
  rintro ω ⟨hωs, hs'⟩ ⟨hωt, ht'⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact Set.mem_iInter₂.mp ht' s (Finset.mem_Ico.mpr ⟨hs, h⟩) hωs
  · exact Set.mem_iInter₂.mp hs' t (Finset.mem_Ico.mpr ⟨ht, h⟩) hωt

omit [MeasurableSpace Ω] in
private theorem card_recordTimes_le {R : ℕ → Set Ω} {a b t : ℕ} (d : ℕ) {ω : Ω}
    (h : ω ∈ firstRecord R a t) :
    (recordTimes R a b ω).card ≤ d + (recordTimes R (t + d) b ω).card := by
  have hsub : recordTimes R a b ω ⊆ Finset.Ico t (t + d) ∪ recordTimes R (t + d) b ω := by
    intro s hs
    obtain ⟨⟨has, hsb⟩, hR⟩ := mem_recordTimes.mp hs
    have hts : t ≤ s := by
      by_contra! hh
      exact Set.mem_iInter₂.mp h.2 s (Finset.mem_Ico.mpr ⟨has, hh⟩) hR
    rw [Finset.mem_union]
    obtain hsd | hsd := lt_or_ge s (t + d)
    · exact Or.inl (Finset.mem_Ico.mpr ⟨hts, hsd⟩)
    · exact Or.inr (mem_recordTimes.mpr ⟨⟨hsd, hsb⟩, hR⟩)
  calc
    _ ≤ (Finset.Ico t (t + d) ∪ recordTimes R (t + d) b ω).card := Finset.card_le_card hsub
    _ ≤ _ := by simpa [Nat.card_Ico] using (Finset.card_union_le (Finset.Ico t (t + d)) _)

/-- For each record time `t`, a trial is resolved at `t + d` and has conditional
success probability at least `q`. On an interval with at least `k * d` records,
the probability of failure at every eligible time is bounded by `(1 - q)^k`. -/
theorem no_success_prob_le_pow {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {R B : ℕ → Set Ω} {d : ℕ} (hd : 0 < d) {q : ℝ} (hq₁ : q ≤ 1)
    (hR : ∀ t, MeasurableSet[ℱ t] (R t)) (hB : ∀ t, MeasurableSet[ℱ (t + d)] (B t))
    (htrial : ∀ t {G}, MeasurableSet[ℱ t] G → G ⊆ R t →
      q * μ.real G ≤ μ.real (G ∩ B t))
    (k a b : ℕ) {G : Set Ω} (hG : MeasurableSet[ℱ a] G) :
    μ.real {ω | ω ∈ G ∧ (∀ t ∈ Finset.Icc a b, ω ∉ B t) ∧
      k * d ≤ (recordTimes R a b ω).card} ≤ (1 - q) ^ k * μ.real G := by
  classical
  induction k generalizing a b G with
  | zero => simpa only [pow_zero, one_mul] using
      (measureReal_mono (fun _ h => h.1) (measure_ne_top μ G))
  | succ k ih =>
    let A (t : ℕ) := G ∩ firstRecord R a t
    let C (t : ℕ) := {ω | ω ∈ A t \ B t ∧ (∀ s ∈ Finset.Icc (t + d) b, ω ∉ B s) ∧
      k * d ≤ (recordTimes R (t + d) b ω).card}
    have hA (t : ℕ) (ht : t ∈ Finset.Icc a b) : MeasurableSet[ℱ t] (A t) :=
      (ℱ.mono (Finset.mem_Icc.mp ht).1 _ hG).inter (measurableSet_firstRecord hR a t)
    have hA₀ (t : ℕ) (ht : t ∈ Finset.Icc a b) : MeasurableSet (A t) := (ℱ.le t) _ (hA t ht)
    have hsub : {ω | ω ∈ G ∧ (∀ t ∈ Finset.Icc a b, ω ∉ B t) ∧
        (k + 1) * d ≤ (recordTimes R a b ω).card} ⊆ ⋃ t ∈ Finset.Icc a b, C t := by
      intro ω hω
      have hcard : (k + 1) * d ≤ (recordTimes R a b ω).card := hω.2.2
      have hne : (recordTimes R a b ω).Nonempty :=
        Finset.card_pos.mp ((Nat.mul_pos (by omega) hd).trans_le hcard)
      let t := (recordTimes R a b ω).min' hne
      have ht : t ∈ recordTimes R a b ω := Finset.min'_mem _ _
      obtain ⟨ht', htR⟩ := mem_recordTimes.mp ht
      have htF : ω ∈ firstRecord R a t := by
        refine ⟨htR, Set.mem_iInter₂.mpr (fun s hs hRs => ?_)⟩
        obtain ⟨has, hst⟩ := Finset.mem_Ico.mp hs
        have hs' : s ∈ recordTimes R a b ω := mem_recordTimes.mpr ⟨⟨has, hst.le.trans ht'.2⟩, hRs⟩
        exact (not_lt_of_ge (Finset.min'_le _ _ hs')) hst
      refine Set.mem_iUnion₂.mpr ⟨t, Finset.mem_Icc.mpr ht', ⟨⟨⟨hω.1, htF⟩, ?_⟩, ?_, ?_⟩⟩
      · exact hω.2.1 t (Finset.mem_Icc.mpr ht')
      · intro s hs
        obtain ⟨hts, hsb⟩ := Finset.mem_Icc.mp hs
        exact hω.2.1 s (Finset.mem_Icc.mpr ⟨ht'.1.trans (by omega), hsb⟩)
      · have hle := card_recordTimes_le d htF (b := b)
        rw [Nat.succ_mul] at hcard
        omega
    have hfail (t : ℕ) (ht : t ∈ Finset.Icc a b) :
        μ.real (A t \ B t) ≤ (1 - q) * μ.real (A t) := by
      have hb : MeasurableSet (B t) := (ℱ.le (t + d)) _ (hB t)
      have hprob := htrial t (hA t ht) (fun _ h => h.2.1)
      nlinarith [measureReal_sdiff_add_inter (s := A t) hb (measure_ne_top μ (A t))]
    have hs : (∑ t ∈ Finset.Icc a b, μ.real (A t)) ≤ μ.real G := by
      rw [← measureReal_biUnion_finset (s := Finset.Icc a b) (f := A)
        (fun s hs t ht hne => (disjoint_firstRecord R a (Finset.mem_Icc.mp hs).1
          (Finset.mem_Icc.mp ht).1 hne).mono Set.inter_subset_right Set.inter_subset_right)
        hA₀ (fun _ _ => measure_ne_top μ _)]
      exact measureReal_mono (by
        intro ω hω
        obtain ⟨t, _, ht⟩ := Set.mem_iUnion₂.mp hω
        exact ht.1)
    calc
      _ ≤ μ.real (⋃ t ∈ Finset.Icc a b, C t) := measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ ∑ t ∈ Finset.Icc a b, μ.real (C t) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ t ∈ Finset.Icc a b, (1 - q) ^ k * μ.real (A t \ B t) := by
        apply Finset.sum_le_sum
        intro t ht
        exact ih (a := t + d) (b := b) (((ℱ.mono (by omega : t ≤ t + d)) _ (hA t ht)).diff (hB t))
      _ ≤ ∑ t ∈ Finset.Icc a b, (1 - q) ^ (k + 1) * μ.real (A t) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [pow_succ, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hfail t ht) (pow_nonneg (sub_nonneg.mpr hq₁) _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hs (pow_nonneg (sub_nonneg.mpr hq₁) _)

end Swarming.Diameter
