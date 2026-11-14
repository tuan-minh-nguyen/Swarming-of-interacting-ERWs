/-
Deterministic regeneration geometry of the actual selected-block indices.

The fallback in `SwarmFB.blkFun` is never called a genuine block here.  All
statements about block geometry are made on the corresponding `Achain` event.
-/
import Swarm.FBLaw

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NeutralRegen

open SwarmFB SwarmSelInd

variable {N : ℕ}

/-- A genuine selected block at a positive level has positive duration.  This
uses only the zero initial position and the record at the endpoint. -/
theorem one_le_time_of_firstRegen (hN : 0 < N) {X : ℕ → Fin N → ℤ}
    (hX0 : ∀ i, X 0 i = 0) {t : ℕ} {d : ℤ} (hd : 1 ≤ d)
    (h : X ∈ SwarmSel.firstRegen (N := N) t d) : 1 ≤ t := by
  by_contra ht
  have ht0 : t = 0 := by omega
  subst t
  have hC : X ∈ SwarmSel.Cpath (N := N) 0 d :=
    (SwarmSel.mem_firstRegen_iff.mp h).1
  have hrec : SwarmChain.pathRec 0 d X := hC.1
  let i : Fin N := ⟨0, hN⟩
  have heq := hrec.2 i
  rw [hX0 i] at heq
  omega

/-- Every coordinate of a genuine specified selected chain has positive time. -/
theorem one_le_time_of_mem_Hidx (hN : 0 < N) {L : List (ℕ × ℤ)}
    (hL : ∀ q ∈ L, 1 ≤ q.2) {X : ℕ → Fin N → ℤ}
    (hX : X ∈ SwarmSelInd.Hidx (N := N) L Set.univ) {q : ℕ × ℤ}
    (hq : q ∈ L) : 1 ≤ q.1 := by
  induction L generalizing X with
  | nil => simp at hq
  | cons a rest ih =>
      obtain ⟨t, d⟩ := a
      rw [SwarmSelInd.mem_Hidx_cons] at hX
      rcases List.mem_cons.mp hq with rfl | hq
      · exact one_le_time_of_firstRegen hN
          (SwarmFresh.mem_strictPos.mp hX.1).1
          (hL (t, d) (by simp)) hX.2.1
      · exact ih (fun r hr => hL r (by simp [hr])) hX.2.2 hq

/-- After a specified selected chain, re-basing at the cumulative time and level
leaves the strict seed followed by the prescribed tail event. -/
theorem tail_mem_of_mem_Hidx {L : List (ℕ × ℤ)}
    (hL : ∀ q ∈ L, 1 ≤ q.2) {B : Set (ℕ → Fin N → ℤ)}
    {X : ℕ → Fin N → ℤ} (hX : X ∈ SwarmSelInd.Hidx (N := N) L B) :
    SwarmChain.pathRel (L.map (fun q => q.1)).sum (L.map (fun q => q.2)).sum X ∈
      SwarmSelInd.seed (N := N) ∩ B := by
  induction L generalizing X with
  | nil =>
      rw [SwarmSelInd.mem_Hidx_nil] at hX
      have hrel : SwarmChain.pathRel 0 0 X = X := by
        funext n i
        simp [SwarmChain.pathRel]
      simpa only [List.map_nil, List.sum_nil, hrel, Set.mem_inter_iff] using hX
  | cons a rest ih =>
      obtain ⟨t, d⟩ := a
      rw [SwarmSelInd.mem_Hidx_cons] at hX
      have htail := ih (fun q hq => hL q (by simp [hq])) hX.2.2
      rw [SwarmChain.pathRel_pathRel] at htail
      simpa only [List.map_cons, List.sum_cons] using htail

/-- On the `n`-chain event, the selected vector determines a cumulative
simultaneous record of the literal actual trajectory. -/
theorem cumulative_record_blkFun (hN : 0 < N) (p : ℝ) (m : ℕ) (n : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) :
    SwarmChain.pathRec
      (∑ i : Fin n, (SwarmFB.blkFun (p := p) (m := m) (N := N) n U i).1)
      (∑ i : Fin n, SwarmFB.blkLevel
        (SwarmFB.blkFun (p := p) (m := m) (N := N) n U i))
      (SwarmRestart.posPath p m U) := by
  have h := SwarmFB.cumulative_record (p := p) (m := m) hN n hU
  exact h

/-- On the same event, the future after the cumulative selected record is
strictly positive.  This is the no-return input for `Sandwich`. -/
theorem cumulative_tail_blkFun (hN : 0 < N) (p : ℝ) (m : ℕ) (n : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) :
    SwarmChain.pathRel
      (∑ i : Fin n, (SwarmFB.blkFun (p := p) (m := m) (N := N) n U i).1)
      (∑ i : Fin n, SwarmFB.blkLevel
        (SwarmFB.blkFun (p := p) (m := m) (N := N) n U i))
      (SwarmRestart.posPath p m U) ∈ SwarmSelInd.seed (N := N) := by
  have hU' : U ∈ ⋃ L : Fin n → ℕ × ℕ,
      SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    rw [SwarmFB.iUnion_atom_eq]
    exact hU
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  have ht := tail_mem_of_mem_Hidx (N := N) (L := SwarmFB.idxList L)
    (SwarmFB.idxList_pos L) hL
  simp only [Set.inter_univ] at ht
  rw [SwarmFB.blkFun_of_mem (p := p) (m := m) hN hL]
  simpa only [SwarmFB.idxList, List.map_ofFn, List.sum_ofFn,
    Function.comp_def] using ht

/-- On the `(k+1)`-chain event the `k`-th selected duration is positive. -/
theorem one_le_time_Z (hN : 0 < N) (p : ℝ) (m : ℕ) (k : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N (k + 1) Set.univ) :
    1 ≤ (SwarmFB.Z (p := p) (m := m) (N := N) k U).1 := by
  have hU' : U ∈ ⋃ L : Fin (k + 1) → ℕ × ℕ,
      SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    rw [SwarmFB.iUnion_atom_eq]
    exact hU
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hmem : ((L i).1, SwarmFB.blkLevel (L i)) ∈ SwarmFB.idxList L := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have ht := one_le_time_of_mem_Hidx hN (SwarmFB.idxList_pos L) hL hmem
  have hz := SwarmFB.Z_eq_of_mem_atom (p := p) (m := m) hN L hL i
  change 1 ≤ (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1
  rw [hz]
  exact ht

/-- The `Z` form of the cumulative record. -/
theorem cumulative_record_Z (hN : 0 < N) (p : ℝ) (m : ℕ) (n : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) :
    SwarmChain.pathRec
      (∑ i : Fin n, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1)
      (∑ i : Fin n, SwarmFB.blkLevel
        (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U))
      (SwarmRestart.posPath p m U) := by
  have h := cumulative_record_blkFun hN p m n hU
  rw [← SwarmFB.jointZ_eq_blkFun (p := p) (m := m) hN n hU] at h
  exact h

/-- The `Z` form of the strict cumulative tail. -/
theorem cumulative_tail_Z (hN : 0 < N) (p : ℝ) (m : ℕ) (n : ℕ)
    {U : Array N} (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) :
    SwarmChain.pathRel
      (∑ i : Fin n, (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U).1)
      (∑ i : Fin n, SwarmFB.blkLevel
        (SwarmFB.Z (p := p) (m := m) (N := N) i.1 U))
      (SwarmRestart.posPath p m U) ∈ SwarmSelInd.seed (N := N) := by
  have h := cumulative_tail_blkFun hN p m n hU
  rw [← SwarmFB.jointZ_eq_blkFun (p := p) (m := m) hN n hU] at h
  exact h

end NeutralRegen
