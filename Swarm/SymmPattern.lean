import Swarm.SymmLetterSum

open MeasureTheory ProbabilityTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

namespace Swarming.FairWalk

/-- The letters whose first bit is fixed have total mass `1/2`. -/
lemma sum_letterLaw_fst (p : ℝ) (b : Bool) :
    ∑ l : Bool × Bool, (if l.1 = b then letterLaw p l else 0) = 1 / 2 := by
  rw [Fintype.sum_prod_type]
  simp only [letterLaw, letterSet_eq_cell, Fintype.sum_bool, Prod.fst]
  cases b
  · simpa using cell_add p false
  · simpa using cell_add p true

/-- Letters producing either possible integer sign have total mass `1/2`. -/
lemma sum_letterLaw_lsgn (p : ℝ) {z : ℤ} (hz : z = 1 ∨ z = -1) :
    ∑ l : Bool × Bool, (if lsgn l = z then letterLaw p l else 0) = 1 / 2 := by
  rcases hz with rfl | rfl
  · simpa [lsgn] using sum_letterLaw_fst p true
  · have hsign : ∀ l : Bool × Bool, lsgn l = -1 ↔ l.1 = false := by
      intro l
      cases h : l.1 <;> simp [lsgn, h]
    simp_rw [hsign]
    exact sum_letterLaw_fst p false

/-- Move the compatibility condition into each time-walker factor. -/
lemma goodPattern_factor {N : ℕ} (p : ℝ) {r : ℕ} (i : Fin N) (ε : Fin r → ℤ)
    (q : Fin r → Fin N → Bool × Bool) :
    (if goodPattern r i ε q then ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0) =
      ∏ ni : Fin r × Fin N,
        (if ni.2 = i → lsgn (q ni.1 ni.2) = ε ni.1 then letterLaw p (q ni.1 ni.2) else 0) := by
  classical
  change (if (∀ n : Fin r, lsgn (q n i) = ε n) then
    ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0) = _
  by_cases hq : ∀ n : Fin r, lsgn (q n i) = ε n
  · rw [if_pos hq]
    apply Finset.prod_congr rfl
    rintro ⟨n, j⟩ _
    by_cases hji : j = i
    · subst j
      simp [hq n]
    · simp [hji]
  · rw [if_neg hq]
    push_neg at hq
    obtain ⟨n, hn⟩ := hq
    symm
    apply Finset.prod_eq_zero (i := (n, i)) (Finset.mem_univ _)
    split_ifs with hh
    · exact (hn (hh rfl)).elim
    · rfl

/-- Evaluate the finite sum over compatible words with a valid `±1` sign pattern. -/
theorem sum_goodPattern_of_signs {N : ℕ} (p : ℝ) {r : ℕ} (i : Fin N) (ε : Fin r → ℤ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    (∑ q : Fin r → Fin N → Bool × Bool,
      if goodPattern r i ε q then ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0) =
      (1 / 2 : ℝ≥0∞) ^ r := by
  classical
  calc
    _ = ∑ q : Fin r → Fin N → Bool × Bool, ∏ n : Fin r, ∏ j : Fin N,
        (if j = i → lsgn (q n j) = ε n then letterLaw p (q n j) else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      have hw : (∏ ni : Fin r × Fin N,
          if ni.2 = i → lsgn (q ni.1 ni.2) = ε ni.1 then letterLaw p (q ni.1 ni.2) else 0) =
          ∏ n : Fin r, ∏ j : Fin N,
            (if j = i → lsgn (q n j) = ε n then letterLaw p (q n j) else 0) := Fintype.prod_prod_type _
      exact (goodPattern_factor p i ε q).trans hw
    _ = ∏ n : Fin r, ∑ g : Fin N → Bool × Bool, ∏ j : Fin N,
        (if j = i → lsgn (g j) = ε n then letterLaw p (g j) else 0) := by
      exact (Fintype.prod_sum (ι := Fin r) (κ := fun _ : Fin r => Fin N → Bool × Bool)
        (fun n g => ∏ j : Fin N,
          if j = i → lsgn (g j) = ε n then letterLaw p (g j) else 0)).symm
    _ = ∏ n : Fin r, ∏ j : Fin N, ∑ l : Bool × Bool,
        (if j = i → lsgn l = ε n then letterLaw p l else 0) := by
      apply Finset.prod_congr rfl
      intro n _
      exact (Fintype.prod_sum (κ := fun _ : Fin N => Bool × Bool)
        (fun j l => if j = i → lsgn l = ε n then letterLaw p l else 0)).symm
    _ = ∏ n : Fin r, ∏ j : Fin N, if j = i then (1 / 2 : ℝ≥0∞) else 1 := by
      apply Finset.prod_congr rfl
      intro n _
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · simp only [hji, if_true, true_implies]
        exact sum_letterLaw_lsgn p (hε n)
      · simp only [hji, if_false, false_implies, if_true]
        exact letterLaw_sum p
    _ = ∏ _n : Fin r, (1 / 2 : ℝ≥0∞) := by simp
    _ = (1 / 2 : ℝ≥0∞) ^ r := by simp

/-- The complete sum is zero for an impossible pattern and `2⁻ʳ` otherwise. -/
theorem sum_goodPattern {N : ℕ} (p : ℝ) {r : ℕ} (i : Fin N) (ε : Fin r → ℤ) :
    (∑ q : Fin r → Fin N → Bool × Bool,
      if goodPattern r i ε q then ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0) =
      if (∀ n, ε n = 1 ∨ ε n = -1) then (1 / 2 : ℝ≥0∞) ^ r else 0 := by
  classical
  by_cases hε : ∀ n, ε n = 1 ∨ ε n = -1
  · simpa [hε] using sum_goodPattern_of_signs p i ε hε
  · simp only [hε, if_false]
    apply Finset.sum_eq_zero
    intro q _
    push_neg at hε
    obtain ⟨n, hn1, hn2⟩ := hε
    have hq : ¬goodPattern r i ε q := by
      intro hq
      have hh := hq n
      unfold lsgn at hh
      by_cases hb : (q n i).1
      · simp [hb] at hh
        exact hn1 hh.symm
      · simp [hb] at hh
        exact hn2 hh.symm
    simp [hq]

/-- **The arbitrary-horizon fair increment law of the actual symmetric walk.**
An admissible sequence of signs has probability `2⁻ʳ`; an impossible pattern has probability zero. -/
theorem measure_symmInc_pattern {N : ℕ} (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    arrayMeasure N {ω : Array N | ∀ n : Fin r, symmInc p m ω i n = ε n} =
      if (∀ n, ε n = 1 ∨ ε n = -1) then (1 / 2 : ℝ≥0∞) ^ r else 0 := by
  rw [symmetricWalk_pattern_mass, sum_goodPattern]

/-- Boolean parametric form, directly suitable for the reflection transport. -/
theorem measure_symmInc_pattern_bool {N : ℕ} (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N)
    (ε : Fin r → Bool) :
    arrayMeasure N {ω : Array N |
      ∀ n : Fin r, symmInc p m ω i n = if ε n then 1 else -1} = (1 / 2 : ℝ≥0∞) ^ r := by
  rw [measure_symmInc_pattern, if_pos (fun n => by
    cases h : ε n <;> simp [h])]

end Swarming.FairWalk


