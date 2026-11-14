/-
Boolean sign and driver cells for the actual auxiliary walk's uniform array.
Each driver threshold splits a sign cell in half. This module also gives the
finite-cylinder product law, including extension by a fresh coordinate.
-/
import Swarm.Trajectory
import Swarm.FreshIndependence

open MeasureTheory ProbabilityTheory Set
open Swarming.Uniform
open Swarming.Model
open scoped ENNReal

namespace Swarming.FairWalk

variable {N : ℕ}

/-! ### Single-coordinate sign and driver cells -/

/-- The `±1` value attached to a Boolean bit. -/
def sv (b : Bool) : ℤ := if b then 1 else -1

/-- The set of coordinate values whose symmetrised sign is `sv b`. -/
def sgnSet (b : Bool) : Set ℝ := {u : ℝ | symmetricStep u = sv b}

/-- The set of coordinate values producing driver bit `b` at right probability `q`. -/
def drvSet (q : ℝ) (b : Bool) : Set ℝ := {u : ℝ | drivenStep u q = sv b}

/-- The joint cell: driver bit `bb` and symmetrised sign `ss`. -/
def cell (q : ℝ) (bb ss : Bool) : Set ℝ := drvSet q bb ∩ sgnSet ss

lemma symmetricStep_eq_one_iff (u : ℝ) : symmetricStep u = 1 ↔ u ≤ 1 / 2 := by
  unfold symmetricStep
  by_cases h : 2 * u ≤ 1
  · rw [if_pos h]
    constructor <;> intro _ <;> linarith
  · rw [if_neg h]
    constructor
    · intro hc; exact absurd hc (by norm_num)
    · intro hc; linarith

lemma symmetricStep_eq_neg_one_iff (u : ℝ) : symmetricStep u = -1 ↔ 1 / 2 < u := by
  unfold symmetricStep
  by_cases h : 2 * u ≤ 1
  · rw [if_pos h]
    constructor
    · intro hc; exact absurd hc (by norm_num)
    · intro hc; linarith
  · rw [if_neg h]
    constructor <;> intro _ <;> linarith

lemma sgnSet_true : sgnSet true = Iic (1 / 2 : ℝ) := by
  ext u
  simp only [sgnSet, mem_ofPred_eq, sv, if_true]
  exact symmetricStep_eq_one_iff u

lemma sgnSet_false : sgnSet false = Ioi (1 / 2 : ℝ) := by
  ext u
  simp only [sgnSet, mem_ofPred_eq, sv, if_false]
  exact symmetricStep_eq_neg_one_iff u

lemma sgnSet_measurable (b : Bool) : MeasurableSet (sgnSet b) := by
  cases b
  · rw [sgnSet_false]; exact measurableSet_Ioi
  · rw [sgnSet_true]; exact measurableSet_Iic

/-- A single coordinate has fair symmetrised sign. -/
theorem uniform01_sgnSet (b : Bool) : uniform01 (sgnSet b) = (1 / 2 : ℝ≥0∞) := by
  cases b
  · rw [sgnSet_false, uniform01_Ioi (by norm_num) (by norm_num),
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  · rw [sgnSet_true, uniform01_Iic (by norm_num) (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num

/-- Membership in a driver cell is the corresponding driver bit. -/
lemma mem_drvSet_iff (q : ℝ) (b : Bool) (u : ℝ) : u ∈ drvSet q b ↔ decide (u ≤ q) = b := by
  by_cases hq : u ≤ q
  · rw [decide_eq_true hq]
    cases b <;> simp [drvSet, sv, drivenStep, hq]
  · rw [decide_eq_false hq]
    cases b <;> simp [drvSet, sv, drivenStep, hq] <;> linarith

lemma drvSet_true (q : ℝ) : drvSet q true = Iic q := by
  ext u
  rw [mem_drvSet_iff, mem_Iic]
  exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

lemma drvSet_false (q : ℝ) : drvSet q false = Ioi q := by
  ext u
  rw [mem_drvSet_iff, mem_Ioi]
  exact ⟨fun h => not_le.mp (decide_eq_false_iff_not.mp h),
    fun h => decide_eq_false_iff_not.mpr (not_le.mpr h)⟩

lemma drvSet_measurable (q : ℝ) (b : Bool) : MeasurableSet (drvSet q b) := by
  cases b
  · rw [drvSet_false]; exact measurableSet_Ioi
  · rw [drvSet_true]; exact measurableSet_Iic

lemma cell_measurable (q : ℝ) (bb ss : Bool) : MeasurableSet (cell q bb ss) :=
  (drvSet_measurable q bb).inter (sgnSet_measurable ss)

lemma mem_sgnSet_iff (b : Bool) (u : ℝ) : u ∈ sgnSet b ↔ symmetricStep u = sv b := Iff.rfl

/-- The two driver cells at a threshold partition the line. -/
lemma drvSet_union (q : ℝ) : drvSet q true ∪ drvSet q false = univ := by
  rw [drvSet_true, drvSet_false, Iic_union_Ioi]

lemma drvSet_disjoint (q : ℝ) : Disjoint (drvSet q true) (drvSet q false) := by
  rw [drvSet_true, drvSet_false]
  exact Iic_disjoint_Ioi le_rfl

/-- The two driver cells at one threshold split any sign cell in half. -/
lemma cell_add (q : ℝ) (ss : Bool) :
    uniform01 (cell q true ss) + uniform01 (cell q false ss) = (1 / 2 : ℝ≥0∞) := by
  have hunion : cell q true ss ∪ cell q false ss = sgnSet ss := by
    simp only [cell, ← Set.union_inter_distrib_right, drvSet_union, univ_inter]
  have hdisj : Disjoint (cell q true ss) (cell q false ss) :=
    (drvSet_disjoint q).mono inter_subset_left inter_subset_left
  rw [← measure_union hdisj (cell_measurable q false ss), hunion, uniform01_sgnSet]

/-! ### Finite cylinder product law -/

/-- Product law for finitely many distinct coordinate constraints. -/
theorem cylinder_measure {r : ℕ} {a : Fin r → Fin N × ℤ × ℕ} (ha : Function.Injective a)
    (E : Fin r → Set ℝ) (hE : ∀ k, MeasurableSet (E k)) :
    arrayMeasure N (⋂ k : Fin r, (fun U : Array N => U (a k)) ⁻¹' E k) =
      ∏ k : Fin r, uniform01 (E k) := by
  have hind : iIndepFun (fun c (U : Array N) => U c) (arrayMeasure N) := array_independent N
  have h := SwarmIID.indep_iInter_comp (μ := arrayMeasure N) hind ha E hE
  rw [h]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  exact arrayMeasure_preimage_set N (a k) (E k) (hE k)

/-- Adding one fresh coordinate multiplies the cylinder probability. -/
theorem cylinder_measure_fresh {r : ℕ} {a : Fin r → Fin N × ℤ × ℕ} (ha : Function.Injective a)
    {b : Fin N × ℤ × ℕ} (hb : ∀ k, a k ≠ b)
    (E : Fin r → Set ℝ) (hE : ∀ k, MeasurableSet (E k))
    (I : Set ℝ) (hI : MeasurableSet I) :
    arrayMeasure N ((⋂ k : Fin r, (fun U : Array N => U (a k)) ⁻¹' E k) ∩
        (fun U : Array N => U b) ⁻¹' I) =
      (∏ k : Fin r, uniform01 (E k)) * uniform01 I := by
  classical
  set a' : Fin (r + 1) → Fin N × ℤ × ℕ := Fin.lastCases b a with ha'
  have ha'inj : Function.Injective a' := by
    intro x y hxy
    have hlast : a' (Fin.last r) = b := Fin.lastCases_last
    have hcast : ∀ k : Fin r, a' k.castSucc = a k := fun k => Fin.lastCases_castSucc k
    by_cases hx : x = Fin.last r
    · subst hx
      by_cases hy : y = Fin.last r
      · rw [hy]
      · rw [← Fin.castSucc_castPred y hy, hcast, hlast] at hxy
        exact absurd hxy.symm (hb (y.castPred hy))
    · by_cases hy : y = Fin.last r
      · subst hy
        rw [← Fin.castSucc_castPred x hx, hcast, hlast] at hxy
        exact absurd hxy (hb (x.castPred hx))
      · rw [← Fin.castSucc_castPred x hx, ← Fin.castSucc_castPred y hy, hcast, hcast] at hxy
        have hh : x.castPred hx = y.castPred hy := ha hxy
        rw [← Fin.castSucc_castPred x hx, ← Fin.castSucc_castPred y hy, hh]
  set E' : Fin (r + 1) → Set ℝ := Fin.lastCases I E with hE'
  have hE'meas : ∀ k, MeasurableSet (E' k) := by
    intro k
    by_cases hk : k = Fin.last r
    · subst hk; simpa [E'] using hI
    · rw [(Fin.castSucc_castPred k hk).symm]
      simpa only [E', Fin.lastCases_castSucc] using hE (k.castPred hk)
  have hset : (⋂ k : Fin r, (fun U : Array N => U (a k)) ⁻¹' E k) ∩
      (fun U : Array N => U b) ⁻¹' I =
      ⋂ k : Fin (r + 1), (fun U : Array N => U (a' k)) ⁻¹' E' k := by
    ext U
    simp only [mem_inter_iff, mem_iInter, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = Fin.last r
      · subst hk; simpa [E', a'] using h2
      · rw [(Fin.castSucc_castPred k hk).symm]
        simpa only [E', a', Fin.lastCases_castSucc] using h1 (k.castPred hk)
    · intro h
      refine ⟨fun k => ?_, ?_⟩
      · have := h (Fin.castSucc k); simpa [E', a'] using this
      · have := h (Fin.last r); simpa [E', a'] using this
  rw [hset, cylinder_measure ha'inj E' hE'meas, Fin.prod_univ_castSucc]
  simp only [E', a', Fin.lastCases_last, Fin.lastCases_castSucc]

end Swarming.FairWalk
