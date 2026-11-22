import SwarmDiameter.SpatialGapSums

open Finset MeasureTheory
open SwarmMarks
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

private theorem prod_Ico_eq_prod_intervals {f : ℕ → ℝ≥0∞} {s : ℕ → ℕ}
    (h : Monotone s) (n : ℕ) :
    (∏ x ∈ Ico (s 0) (s n), f x) =
      ∏ j ∈ range n, ∏ x ∈ Ico (s j) (s (j + 1)), f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← ih]
    exact (prod_Ico_consecutive _ (h (Nat.zero_le n)) (h (Nat.le_succ n))).symm

/-- The probability of a prescribed finite sequence of gaps between marked
sites. The integer `g j` counts unmarked sites before the next mark, and
`s j` is the first site of that interval. -/
theorem measure_prescribed_marked_gaps (q : ℝ) (b n : ℕ) (g : ℕ → ℕ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    let s (j : ℕ) := b + ∑ i ∈ range j, (g i + 1)
    markMeasure (boolMeasure q)
      {ω | ∀ j < n, ω (s (j + 1) - 1) = true ∧
        ∀ x : ℕ, s j ≤ x → x < s (j + 1) - 1 → ω x = false} =
      ∏ j ∈ range n, ENNReal.ofReal (1 - q) ^ (g j) * ENNReal.ofReal q := by
  classical
  let _ : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq₀ hq₁
  let s (j : ℕ) := b + ∑ i ∈ range j, (g i + 1)
  have hsucc (j : ℕ) : s (j + 1) = s j + g j + 1 := by simp only [s, sum_range_succ]; omega
  have hs : StrictMono s := strictMono_nat_of_lt_succ fun j => by rw [hsucc]; omega
  let w (x : ℕ) : Bool := decide (∃ j < n, x = s (j + 1) - 1)
  have hterm (j : ℕ) (hj : j < n) :
      w (s (j + 1) - 1) = true := by
    simp only [w, decide_eq_true_eq]
    exact ⟨j, hj, rfl⟩
  have hinner (j x : ℕ) (h₁ : s j ≤ x) (h₂ : x < s (j + 1) - 1) : w x = false := by
    simp only [w, decide_eq_false_iff_not]
    rintro ⟨i, _, hi⟩
    by_cases hij : i < j
    · have hle := hs.monotone (show i + 1 ≤ j by omega)
      have hpos : 0 < s (i + 1) := by rw [hsucc]; omega
      omega
    · have hle := hs.monotone (show j + 1 ≤ i + 1 by omega)
      omega
  let A : Set (ℕ → Bool) := {ω | ∀ j < n, ω (s (j + 1) - 1) = true ∧
    ∀ x : ℕ, s j ≤ x → x < s (j + 1) - 1 → ω x = false}
  have hA : A = Set.pi (↑(Ico (s 0) (s n)) : Set ℕ) (fun x => {w x}) := by
    ext ω
    change (∀ j < n, ω (s (j + 1) - 1) = true ∧
      ∀ x : ℕ, s j ≤ x → x < s (j + 1) - 1 → ω x = false) ↔ _
    constructor
    · intro h x hx
      obtain ⟨hx₁, hx₂⟩ := Finset.mem_Ico.mp hx
      have he : ∃ j, j < n ∧ x < s (j + 1) := ⟨n - 1, by
        have hn : n ≠ 0 := by rintro rfl; omega
        omega, by
        have hn : n ≠ 0 := by rintro rfl; omega
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
        exact hx₂⟩
      let j := Nat.find he
      have hj : j < n := (Nat.find_spec he).1
      have hxj : x < s (j + 1) := (Nat.find_spec he).2
      have hl : s j ≤ x := by
        by_contra hnot
        have hlt := lt_of_not_ge hnot
        have hj₀ : 0 < j := by
          by_contra hn₀
          have hz : j = 0 := by omega
          rw [hz] at hlt
          exact (not_lt_of_ge hx₁) hlt
        have hn := Nat.find_min he (show j - 1 < j by omega)
        apply hn
        exact ⟨by omega, by rwa [Nat.sub_add_cancel (by omega : 1 ≤ j)]⟩
      change ω x = w x
      by_cases ht : x = s (j + 1) - 1
      · rw [ht, hterm j hj, (h j hj).1]
      · have hlt : x < s (j + 1) - 1 := by
          have hpos : 0 < s (j + 1) := by rw [hsucc]; omega
          omega
        rw [hinner j x hl hlt, (h j hj).2 x hl hlt]
    · intro h j hj
      have hspan (x : ℕ) (hl : s j ≤ x) (hr : x < s (j + 1)) : ω x = w x :=
        h x (mem_Ico.mpr ⟨(hs.monotone (Nat.zero_le j)).trans hl,
          hr.trans_le (hs.monotone (by omega))⟩)
      have hmark : s j ≤ s (j + 1) - 1 := by rw [hsucc]; omega
      have ht : s (j + 1) - 1 < s (j + 1) := by rw [hsucc]; omega
      refine ⟨(hspan _ hmark ht).trans (hterm j hj), ?_⟩
      intro x hl hr
      exact (hspan x hl (hr.trans ht)).trans (hinner j x hl hr)
  change markMeasure (boolMeasure q) A = _
  rw [hA, markMeasure, Measure.infinitePi_pi (fun _ => boolMeasure q) (fun i _ => measurableSet_singleton (w i)),
    prod_Ico_eq_prod_intervals hs.monotone]
  apply prod_congr rfl
  intro j hj
  have hle : s j ≤ s (j + 1) - 1 := by rw [hsucc]; omega
  have hend : s (j + 1) = (s (j + 1) - 1) + 1 := by rw [hsucc]; omega
  rw [hend, prod_Ico_succ_top hle, hterm j (mem_range.mp hj), boolMeasure_true]
  congr 1
  calc
    _ = ∏ _ ∈ Ico (s j) (s (j + 1) - 1), ENNReal.ofReal (1 - q) := by
      apply prod_congr rfl
      intro x hx
      obtain ⟨h₁, h₂⟩ := mem_Ico.mp hx
      rw [hinner j x h₁ h₂, boolMeasure_false]
    _ = _ := by
      rw [prod_const, Nat.card_Ico, hsucc]
      congr 1
      omega

/-- The first site after the first `j` prescribed marks for `j ≤ n`. -/
private noncomputable def markedGapEndpoint {n : ℕ} (b : ℕ) (g : Fin n → ℕ) (j : ℕ) : ℕ :=
  b + ∑ i ∈ range j, ((if hi : i < n then g ⟨i, hi⟩ else 0) + 1)

/-- The event that the first `n` gaps starting at site `b` have the prescribed
numbers of unmarked sites. -/
def markedGapEvent {n : ℕ} (b : ℕ) (g : Fin n → ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ j < n, ω (markedGapEndpoint b g (j + 1) - 1) = true ∧
    ∀ x : ℕ, markedGapEndpoint b g j ≤ x → x < markedGapEndpoint b g (j + 1) - 1 → ω x = false}

theorem measurableSet_markedGapEvent {n : ℕ} (b : ℕ) (g : Fin n → ℕ) :
    MeasurableSet (markedGapEvent b g) := by
  apply (Measurable.forall (ι := ℕ) (fun j => ?_)).setOf
  apply Measurable.imp measurable_const
  refine Measurable.and ?_ ?_
  · exact measurableSet_setOfPred.mp
      (measurable_eval (markedGapEndpoint b g (j + 1) - 1) (measurableSet_singleton true))
  · apply Measurable.forall (ι := ℕ)
    intro x
    exact measurable_const.imp (measurable_const.imp (measurableSet_setOfPred.mp
      (measurable_eval x (measurableSet_singleton false))))

private theorem disjoint_markedGapEvent {n : ℕ} (b : ℕ) :
    Pairwise (fun g h : Fin n → ℕ => Disjoint (markedGapEvent b g) (markedGapEvent b h)) := by
  intro g h hne
  rw [Set.disjoint_left]
  intro ω hg hh
  apply hne
  have heq : ∀ j : ℕ, ∀ i < j, ∀ hi : i < n, g ⟨i, hi⟩ = h ⟨i, hi⟩ := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro i hij hi
      rcases (show i < j ∨ i = j by omega) with hlt | hij'
      · exact ih i hlt hi
      subst i
      have hbefore : markedGapEndpoint b g j = markedGapEndpoint b h j := by
        unfold markedGapEndpoint
        congr 1
        apply sum_congr rfl
        intro k hk
        have hkj := mem_range.mp hk
        have hkn : k < n := hkj.trans hi
        rw [dif_pos hkn, dif_pos hkn, ih k hkj hkn]
      have hnext (r : Fin n → ℕ) : markedGapEndpoint b r (j + 1) - 1 =
          markedGapEndpoint b r j + r ⟨j, hi⟩ := by
        unfold markedGapEndpoint
        simp only [sum_range_succ, dif_pos hi]
        omega
      rcases lt_trichotomy (g ⟨j, hi⟩) (h ⟨j, hi⟩) with hl | he | hr
      · have ht := (hg j hi).1
        have hf := (hh j hi).2 (markedGapEndpoint b g (j + 1) - 1)
          (by rw [hnext, hbefore]; omega) (by rw [hnext, hnext, hbefore]; omega)
        rw [hf] at ht
        exact Bool.noConfusion ht
      · exact he
      · have ht := (hh j hi).1
        have hf := (hg j hi).2 (markedGapEndpoint b h (j + 1) - 1)
          (by rw [hnext, ← hbefore]; omega) (by rw [hnext, hnext, hbefore]; omega)
        rw [hf] at ht
        exact Bool.noConfusion ht
  funext i
  exact heq n i i.isLt i.isLt

/-- The prescribed-gap events assign the product geometric probability to
every set of finite gap vectors. The geometric law on the number of failures
is specified by its singleton probabilities. -/
theorem measure_union_markedGapEvent {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (hν : ∀ k, ν {k} = ENNReal.ofReal (1 - q) ^ k * ENNReal.ofReal q)
    (b n : ℕ) (A : Set (Fin n → ℕ)) :
    markMeasure (boolMeasure q) (⋃ g : A, markedGapEvent b g.1) =
      Measure.pi (fun _ : Fin n => ν) A := by
  have hE (g : Fin n → ℕ) :
      markMeasure (boolMeasure q) (markedGapEvent b g) =
        (Measure.pi (fun _ : Fin n => ν)) {g} := by
    let f (j : ℕ) := if hj : j < n then g ⟨j, hj⟩ else 0
    have hm := measure_prescribed_marked_gaps q b n f hq₀ hq₁
    change markMeasure (boolMeasure q) (markedGapEvent b g) = _ at hm
    rw [hm, Measure.pi_singleton, ← Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro i _
    rw [hν]
    simp [f, i.isLt]
  have hA : A = ⋃ g : A, ({g.1} : Set (Fin n → ℕ)) := by
    ext g
    simp
  conv_rhs => rw [hA]
  rw [measure_iUnion, measure_iUnion (fun i j hij =>
    Set.disjoint_singleton.mpr (fun h => hij (Subtype.ext h))) (fun _ => measurableSet_singleton _)]
  · exact tsum_congr (fun g => hE g.1)
  · exact fun i j hij => disjoint_markedGapEvent b (fun h => hij (Subtype.ext h))
  · exact fun g => measurableSet_markedGapEvent b g.1

/-- The deterministic spatial sum bound on a prescribed-gap event. -/
theorem sum_hof_pow_le_of_mem_markedGapEvent {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b L : ℕ) (g : Fin L → ℕ) (ω : ℕ → Bool), ω ∈ markedGapEvent b g →
        (∑ x ∈ Ico b (b + L), hof p ω x ^ q) ≤
          C * ((if b = 0 then 1 else hof p ω (b - 1)) ^ (q + 1) +
            ∑ j : Fin L, ((g j : ℝ) + 1) ^ (q + 1)) := by
  obtain ⟨C, hC, hsum⟩ := sum_hof_pow_le_marked_gaps hp₀ hp₁ q
  refine ⟨C, hC, fun b L g ω hω => ?_⟩
  let s := markedGapEndpoint b g
  have hzero : s 0 = b := by simp [s, markedGapEndpoint]
  have hsucc (j : ℕ) (hj : j < L) : s (j + 1) = s j + g ⟨j, hj⟩ + 1 := by
    simp only [s, markedGapEndpoint, sum_range_succ, dif_pos hj]
    omega
  have h := hsum ω s L (fun j hj => by rw [hsucc j hj]; omega)
    (fun j hj => (hω j hj).1)
  rw [hzero] at h
  have he : (∑ j ∈ range L, ((s (j + 1) - s j : ℕ) : ℝ) ^ (q + 1)) =
      ∑ j : Fin L, ((g j : ℝ) + 1) ^ (q + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro j _
    have hj : s ((j : ℕ) + 1) - s j = g j + 1 := by
      rw [hsucc j j.isLt]
      have hjval : (⟨j.val, j.isLt⟩ : Fin L) = j := Fin.ext rfl
      rw [hjval]
      omega
    rw [hj, Nat.cast_add, Nat.cast_one]
  rwa [he] at h

end Swarming.Diameter
