import SwarmDiameter.BoundedSpatial
import Swarm.PaperBlock

open Finset Filter MeasureTheory Set
open Swarming.Uniform Swarming.Enl Swarming.Trajectory SwarmRecordMeas.Actual
open LocSum LocSumAct LocGroupSimul SepGroup.Model SwarmLogRatio

namespace Swarming.Diameter

set_option autoImplicit false

/-- The paper's group comparison function with slopes bounded by `K`. -/
noncomputable def boundedHA {N : ℕ} (p : ℝ) (m : ℕ) (K : ℝ) (U : Array N)
    (n : ℕ) (A : Finset (Fin N)) (x : ℤ) : ℝ :=
  boundedPotential K (wA p m U n A) x

private noncomputable def rareSites {N : ℕ} (p : ℝ) (m k a b : ℕ) (U : Array N) (i : Fin N) : Finset ℕ :=
  (Finset.Ico a b).filter fun x => 1 / 2 < Pz p x k (siteMarks p m U i)

private noncomputable def adjacentSites (ℓ y : ℕ) : Finset ℤ :=
  Finset.Icc ((y : ℤ) - (ℓ : ℤ) - 1) ((y : ℤ) + (ℓ : ℤ) + 1)

/-- Sites within distance `ℓ + 1` of a site where some finite comparison
slope can exceed the cutoff for unit drift. -/
noncomputable def boundedExceptionSites {N : ℕ} (p : ℝ) (m k ℓ a b : ℕ) (U : Array N) : Finset ℤ :=
  (Finset.univ.biUnion fun i : Fin N =>
    (rareSites p m k a b U i).biUnion (adjacentSites ℓ)) ∩ Finset.Icc (a : ℤ) (b : ℤ)

theorem boundedExceptionSites_subset {N : ℕ} (p : ℝ) (m k ℓ a b : ℕ) (U : Array N) :
    boundedExceptionSites p m k ℓ a b U ⊆ Finset.Icc (a : ℤ) (b : ℤ) :=
  Finset.inter_subset_right

theorem mem_boundedExceptionSites {N : ℕ} {p : ℝ} {m k ℓ a b : ℕ} {U : Array N}
    {x : ℤ} (hx : x ∈ Finset.Icc (a : ℤ) (b : ℤ)) (i : Fin N) {y : ℕ}
    (hy : y ∈ Finset.Ico a b) (hclose : |x - (y : ℤ)| ≤ (ℓ : ℤ) + 1)
    (hP : 1 / 2 < Pz p y k (siteMarks p m U i)) :
    x ∈ boundedExceptionSites p m k ℓ a b U := by
  have hA : x ∈ adjacentSites ℓ y := by
    rw [adjacentSites, Finset.mem_Icc]
    have h := abs_le.mp hclose
    omega
  exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
    Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hP⟩, hA⟩⟩, hx⟩

private theorem card_adjacentSites (ℓ y : ℕ) : (adjacentSites ℓ y).card = 2 * ℓ + 3 := by
  rw [adjacentSites, Int.card_Icc]
  omega

private theorem card_rareSites_le {N : ℕ} {p : ℝ} {m k a b : ℕ} {U : Array N} (i : Fin N) :
    ((rareSites p m k a b U i).card : ℝ) ≤ 4 *
      ∑ x ∈ Finset.Ico a b, (Pz p x k (siteMarks p m U i)) ^ 2 := by
  unfold rareSites
  rw [Finset.mul_sum]
  calc
    _ = ∑ _ ∈ (Finset.Ico a b).filter (fun x => 1 / 2 < Pz p x k (siteMarks p m U i)), (1 : ℝ) := by simp
    _ = ∑ x ∈ Finset.Ico a b, (if 1 / 2 < Pz p x k (siteMarks p m U i) then (1 : ℝ) else 0) :=
      Finset.sum_filter ..
    _ ≤ _ := Finset.sum_le_sum fun x _ => by
      split
      · rename_i h
        nlinarith only [h, sq_nonneg (Pz p x k (siteMarks p m U i) - 1 / 2)]
      · positivity

theorem card_boundedExceptionSites_le {N : ℕ} {p : ℝ} {m k ℓ a b : ℕ} {U : Array N} {B : ℝ}
    (hP : ∀ i : Fin N, ∑ x ∈ Finset.Ico a b, (Pz p x k (siteMarks p m U i)) ^ 2 ≤ B) :
    ((boundedExceptionSites p m k ℓ a b U).card : ℝ) ≤ (4 * (N : ℝ) * (2 * (ℓ : ℝ) + 3)) * B := by
  have hi (i : Fin N) : ((rareSites p m k a b U i).biUnion (adjacentSites ℓ)).card ≤
      (rareSites p m k a b U i).card * (2 * ℓ + 3) :=
    Finset.card_biUnion_le.trans (by simp [card_adjacentSites])
  have hcard : (boundedExceptionSites p m k ℓ a b U).card ≤
      ∑ i : Fin N, (rareSites p m k a b U i).card * (2 * ℓ + 3) :=
    (Finset.card_le_card Finset.inter_subset_left).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _ => hi i)))
  calc
    _ ≤ ∑ i : Fin N, ((rareSites p m k a b U i).card : ℝ) * (2 * (ℓ : ℝ) + 3) := by
      exact_mod_cast hcard
    _ ≤ ∑ _i : Fin N, 4 * B * (2 * (ℓ : ℝ) + 3) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        ((card_rareSites_le i).trans (mul_le_mul_of_nonneg_left (hP i) (by norm_num))) (by positivity))
    _ = _ := by simp; ring

theorem boundedHA_sub_le_of_Q_sum {N : ℕ} {p : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m n k a b : ℕ} (hk : 1 ≤ k) (hka : k ≤ a)
    {U : Array N} {A : Finset (Fin N)} (hA : A.Nonempty) (hab : a ≤ b)
    (hb : (b : ℤ) ≤ runMaxA p m U hA n) {D : ℝ}
    (hQ : ∀ i : Fin N, ∑ x ∈ Finset.Ico a b, Q p k x (siteMarks p m U i) ≤ D) :
    boundedHA p m (8 * (k : ℝ)) U n A (b : ℤ) - boundedHA p m (8 * (k : ℝ)) U n A (a : ℤ)
      ≤ 10 * D := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' hA (fun i => runMax p m U i n)
  change runMaxA p m U hA n = runMax p m U i n at hmax
  have hK : (1 : ℝ) ≤ 8 * (k : ℝ) := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold boundedHA
  rw [boundedPotential_sub_nat _ _ hab]
  calc
    _ ≤ ∑ x ∈ Finset.Ico a b, 10 * Q p k x (siteMarks p m U i) := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' := Finset.mem_Ico.mp hx
      have hxM : (x : ℤ) < runMax p m U i n :=
        (by exact_mod_cast hx'.2 : (x : ℤ) < b).trans_le (hb.trans_eq hmax)
      exact (boundedSlope_wA_le_finiteSlope hK hp₀ hp₁ hi (hka.trans hx'.1) hxM).trans
        (finiteSlope_le_ten_Q hp₀ hp₁ hk x _)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hQ i) (by norm_num)

end Swarming.Diameter
