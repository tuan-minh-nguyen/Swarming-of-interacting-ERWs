/-
  **Joint freshness of the next departure and the next site above a record.**
-/
import Swarm.RecSeed
import Swarm.EnlRight
import Swarm.GenFresh

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

-- Membership in row coordinates is controlled below by the distinct walker indices.

/-- The next departure of `i` is fresh for the record information of the *different* walker `j`. -/
lemma fr_notMem_recInfo {m : ℕ} {n : ℕ} (γ : Pref N n) {i j : Fin N} (hij : i ≠ j)
    (g : ℕ) :
    fr n γ i ∉ recInfo (N := N) m j g γ := by
  intro hmem
  rw [recInfo, Finset.mem_union] at hmem
  rcases hmem with h | h
  · rw [recRead, Finset.mem_union] at h
    rcases h with h | h
    · exact fr_notMem_prefRead n γ i h
    · obtain ⟨k, _, heq⟩ := mem_recRow.mp h
      exact hij (congrArg (fun c : Fin N × ℤ × ℕ => c.1) heq)
  · rw [Finset.mem_biUnion] at h
    obtain ⟨k, hk, hrow⟩ := h
    obtain ⟨l, hl, heq⟩ := mem_recRow.mp hrow
    exact hij (congrArg (fun c : Fin N × ℤ × ℕ => c.1) heq)

/-- The next ready coordinate of walker `i` against fixed walker `i`'s probability threshold has
exact conditional mass `α`, even when the base environment is enlarged. -/
theorem fresh_stepUp_gen (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} (γ : Pref N n) (i : Fin N)
    (S : Finset (Fin N × ℤ × ℕ)) (hS : prefRead n γ ⊆ S)
    (hnot : fr n γ i ∉ S) {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) S] B) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ stepUp p m n i) =
      ENNReal.ofReal (alphaOf p m n γ i) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  have hset : prefAgree p m γ ∩ B ∩ stepUp p m n i =
      prefAgree p m γ ∩ B ∩ {U : Array N | U (fr n γ i) ∈ Set.Iic (alphaOf p m n γ i)} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic]
    constructor
    · rintro ⟨⟨hp, hb⟩, hu⟩
      refine ⟨⟨hp, hb⟩, ?_⟩
      exact (rightJump_iff_on_prefix p m hp i).mp hu
    · rintro ⟨⟨hp, hb⟩, hu⟩
      exact ⟨⟨hp, hb⟩, (rightJump_iff_on_prefix p m hp i).mpr hu⟩
  have hbase := fresh_block_gen p m n γ S hS hB
    (α := fun _ : Fin 1 => fr n γ i)
    (fun a b _ => Subsingleton.elim a b)
    (fun _ => hnot) (fun _ => Set.Iic (alphaOf p m n γ i)) (fun _ => measurableSet_Iic)
  have hset' : prefAgree p m γ ∩ B ∩ stepUp p m n i =
      prefAgree p m γ ∩ B ∩
        (⋂ _ : Fin 1, {U : Array N | U (fr n γ i) ∈ Set.Iic (alphaOf p m n γ i)}) := by
    rw [hset]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_one]
  rw [hset', hbase]
  congr 1
  simp only [Finset.univ_unique, Finset.prod_singleton]
  apply uniform01_Iic
  · linarith [le_alphaOf p m γ i hp0.le]
  · exact alphaOf_lt_one p m γ i hp0.le hp1

/-- The step set is exactly its coordinate box on a fixed prefix, including any base event. -/
lemma stepUp_inter_box (p : ℝ) (m n : ℕ) (γ : Pref N n) (i : Fin N)
    {B : Set (Array N)} :
    prefAgree p m γ ∩ B ∩ stepUp p m n i =
      prefAgree p m γ ∩ B ∩ {U : Array N | U (fr n γ i) ∈ Set.Iic (alphaOf p m n γ i)} := by
  ext U
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic]
  exact and_congr_right (fun hU => rightJump_iff_on_prefix p m hU.1 i)


/-- Joint conditional mass of the next up-jump and the mark at a fresh site. -/
theorem fresh_up_siteMark_gen (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} (γ : Pref N n) (S : Finset (Fin N × ℤ × ℕ))
    (hS : prefRead n γ ⊆ S) {i j : Fin N} (i0 : Fin N) (x : ℤ)
    (hfr : fr n γ i0 ∉ S)
    (hfresh : ∀ k ∈ Finset.Icc 1 (m - 1), (j, x, k) ∉ S)
    (hij : i0 ≠ j) {B : Set (Array N)} (hB : MeasurableSet[cylAt (N := N) S] B) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ stepUp p m n i0 ∩ {U : Array N | SiteMark p m U j x}) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * ENNReal.ofReal (alphaOf p m n γ i0) *
        arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  let α : Option ↥(Finset.Icc 1 (m - 1)) → Fin N × ℤ × ℕ
    | none => fr n γ i0
    | some k => (j, x, k.1)
  let I : Option ↥(Finset.Icc 1 (m - 1)) → Set ℝ
    | none => Set.Iic (alphaOf p m n γ i0)
    | some _ => Set.Ioi p
  have hαinj : Function.Injective α := by
    rintro (a | a) (b | b) hab
    · rfl
    · have h := congrArg (fun c : Fin N × ℤ × ℕ => c.1) hab
      simp only [α] at h
      exact (hij h).elim
    · have h := congrArg (fun c : Fin N × ℤ × ℕ => c.1) hab
      simp only [α] at h
      exact (hij h.symm).elim
    · have hv := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) hab
      exact congrArg some (Subtype.ext hv)
  have hfreshα : ∀ c, α c ∉ S := by
    intro c
    cases c with
    | none => exact hfr
    | some k => exact hfresh k.1 k.2
  have hI : ∀ c, MeasurableSet (I c) := by
    intro c
    cases c <;> simp only [I, measurableSet_Iic, measurableSet_Ioi]
  have hbase := fresh_block_gen p m n γ S hS hB α hαinj hfreshα I hI
  have hset : prefAgree p m γ ∩ B ∩ stepUp p m n i0 ∩ {U : Array N | SiteMark p m U j x} =
      prefAgree p m γ ∩ B ∩ ⋂ c, {U : Array N | U (α c) ∈ I c} := by
    ext U
    rw [stepUp_inter_box p m n (B := B) γ i0]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Iic, Set.mem_Ioi]
    constructor
    · intro h
      have hp : U ∈ prefAgree p m γ := h.1.1.1
      have hb : U ∈ B := h.1.1.2
      have hu : U (fr n γ i0) ≤ alphaOf p m n γ i0 := h.1.2
      have hmark : SiteMark p m U j x := h.2
      refine ⟨h.1.1, fun c => ?_⟩
      cases c with
      | none => exact hu
      | some k => exact hmark k.1 k.2
    · intro h
      simp_all only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Iic,
        Set.mem_Ioi, rightJump_iff_on_prefix]
      apply And.intro
      · apply And.intro
        · trivial
        · exact h.2 none

      · intro k hk
        exact h.2 (some ⟨k, hk⟩)
  rw [hset, hbase]
  have hprod : (∏ c, uniform01 (I c)) =
      (ENNReal.ofReal (1 - p)) ^ (m - 1) * ENNReal.ofReal (alphaOf p m n γ i0) := by
    have hprod_const : (∏ _i : ↥(Finset.Icc 1 (m - 1)), ENNReal.ofReal (1 - p)) =
        (ENNReal.ofReal (1 - p)) ^ (m - 1) := by simp
    rw [Fintype.prod_option]
    simp only [I, uniform01_Ioi (by linarith : (0 : ℝ) < p) hp1]
    rw [hprod_const, uniform01_Iic]
    · ring
    · linarith [le_alphaOf p m γ i0 hp0.le]
    · exact alphaOf_lt_one p m γ i0 hp0.le hp1
  rw [hprod]

end Swarming.Enl


