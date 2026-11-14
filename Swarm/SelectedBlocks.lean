/-
Measurable selected-block indices from the actual regenerated-chain atoms.

The default branch is only a totalisation outside a completed finite chain.
The atom identities below keep that branch separate; no default value is
interpreted as a regeneration block.  Probability laws are added only after
these deterministic and measurability facts.
-/
import Swarm.Induction
import Swarm.RegenIid

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace SwarmSelectedBlock

open SwarmSelInd

variable {N : ℕ}

/-- A selected block is a time and a positive regeneration level. -/
abbrev BlockIndex := {q : ℕ × ℤ // 1 ≤ q.2}

/-- Exactly `n` selected block indices. -/
abbrev IndexList (n : ℕ) :=
  {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2}

/-- Countable index lists use the discrete measurable structure. -/
instance indexListMeasurableSpace (n : ℕ) : MeasurableSpace (IndexList n) := ⊤

instance indexListMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (IndexList n) := ⟨fun _ => trivial⟩

/-- The never-observed fallback list used to totalise selection. -/
def defaultIndexList (n : ℕ) : IndexList n :=
  ⟨List.replicate n ((0 : ℕ), (1 : ℤ)), by simp, by
    intro q hq
    have : q = ((0 : ℕ), (1 : ℤ)) := List.eq_of_mem_replicate hq
    simp [this]⟩

/-- Select the unique valid list atom containing the path, with an explicit
fallback outside every such atom. -/
noncomputable def selectedList (n : ℕ) (X : ℕ → Fin N → ℤ) : IndexList n :=
  if h : ∃ L : IndexList n, X ∈ Hidx L.1 Set.univ then Classical.choose h
  else defaultIndexList n

/-- On the existence branch the selected list is genuinely a chain atom. -/
theorem selectedList_mem {n : ℕ} {X : ℕ → Fin N → ℤ}
    (h : ∃ L : IndexList n, X ∈ Hidx L.1 Set.univ) :
    X ∈ Hidx (selectedList n X).1 Set.univ := by
  rw [selectedList, dif_pos h]
  exact Classical.choose_spec h

/-- Equal-length valid `Hidx` atoms determine one list. -/
theorem indexList_eq_of_mem (hN : 0 < N) {n : ℕ} {X : ℕ → Fin N → ℤ}
    {L K : IndexList n}
    (hL : X ∈ Hidx L.1 Set.univ) (hK : X ∈ Hidx K.1 Set.univ) : L = K := by
  apply Subtype.ext
  have hp := Hidx_prefix_or (N := N) hN L.1 L.2.2 (L' := K.1) K.2.2 hL hK
  rcases hp with hp | hp
  · exact hp.eq_of_length (L.2.1.trans K.2.1.symm)
  · exact (hp.eq_of_length (K.2.1.trans L.2.1.symm)).symm

/-- A path in a valid atom is assigned that atom. -/
theorem selectedList_eq_of_mem (hN : 0 < N) {n : ℕ} {X : ℕ → Fin N → ℤ}
    {L : IndexList n} (hL : X ∈ Hidx L.1 Set.univ) :
    selectedList n X = L := by
  have h : ∃ K : IndexList n, X ∈ Hidx K.1 Set.univ := ⟨L, hL⟩
  exact indexList_eq_of_mem hN (selectedList_mem h) hL

/-- The preimage of a valid list is its genuine atom union a separated part
of the no-chain fallback. -/
theorem selectedList_preimage_singleton (hN : 0 < N) (n : ℕ) (L : IndexList n) :
    selectedList (N := N) n ⁻¹' {L} =
      Hidx L.1 Set.univ ∪
        ((⋃ K : IndexList n, Hidx K.1 Set.univ)ᶜ ∩
          {X : ℕ → Fin N → ℤ | defaultIndexList n = L}) := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iUnion, not_exists, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro hsel
    by_cases h : ∃ K : IndexList n, X ∈ Hidx K.1 Set.univ
    · left
      have hm := selectedList_mem h
      rwa [hsel] at hm
    · right
      refine ⟨?_, ?_⟩
      · intro K hK
        exact h ⟨K, hK⟩
      · simpa only [selectedList, dif_neg h] using hsel
  · rintro (hL | ⟨hnone, hdefault⟩)
    · exact selectedList_eq_of_mem hN hL
    · have h : ¬ ∃ K : IndexList n, X ∈ Hidx K.1 Set.univ := by
        simpa only [not_exists] using hnone
      simp only [selectedList, dif_neg h, hdefault]

/-- Every fiber, hence the total selected-list map, is measurable. -/
theorem measurable_selectedList (hN : 0 < N) (n : ℕ) :
    Measurable (selectedList (N := N) n) := by
  refine measurable_to_countable' (fun L => ?_)
  rw [selectedList_preimage_singleton hN n L]
  apply MeasurableSet.union (measurableSet_Hidx L.1 MeasurableSet.univ)
  apply MeasurableSet.inter
  · exact (MeasurableSet.iUnion fun K : IndexList n =>
      measurableSet_Hidx K.1 MeasurableSet.univ).compl
  · by_cases h : defaultIndexList n = L
    · simpa [h] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℕ → Fin N → ℤ)))
    · simpa [h] using (MeasurableSet.empty : MeasurableSet (∅ : Set (ℕ → Fin N → ℤ)))

/-- Convert a vector of genuine block indices to a valid index list. -/
def listOfVector {n : ℕ} (v : Fin n → BlockIndex) : IndexList n :=
  ⟨List.ofFn (fun i => (v i).1), List.length_ofFn, by
    intro q hq
    rw [List.mem_ofFn'] at hq
    obtain ⟨i, rfl⟩ := hq
    exact (v i).2⟩

/-- Read a valid list as a vector of genuine block indices. -/
def vectorOfList {n : ℕ} (L : IndexList n) : Fin n → BlockIndex :=
  fun i =>
    ⟨L.1.get (Fin.cast L.2.1.symm i),
      L.2.2 _ (List.get_mem L.1 (Fin.cast L.2.1.symm i))⟩

/-- The two representations of a valid list are inverse. -/
theorem listOfVector_vectorOfList {n : ℕ} (L : IndexList n) :
    listOfVector (vectorOfList L) = L := by
  apply Subtype.ext
  change List.ofFn (fun i => (vectorOfList L i).1) = L.1
  have h := List.ofFn_congr (α := ℕ × ℤ) L.2.1 L.1.get
  simpa only [List.ofFn_get, vectorOfList] using h.symm

/-- In the other direction conversion is pointwise definition equality. -/
theorem vectorOfList_listOfVector {n : ℕ} (v : Fin n → BlockIndex) :
    vectorOfList (listOfVector v) = v := by
  funext i
  apply Subtype.ext
  simp only [vectorOfList, listOfVector, List.get_ofFn]
  congr 2

/-- The selected finite block vector. -/
noncomputable def selectedBlocks (n : ℕ) (X : ℕ → Fin N → ℤ) : Fin n → BlockIndex :=
  vectorOfList (selectedList n X)

/-- Measurability of the finite selected vector. -/
theorem measurable_selectedBlocks (hN : 0 < N) (n : ℕ) :
    Measurable (selectedBlocks (N := N) n) := by
  apply measurable_pi_lambda
  intro i
  refine measurable_to_countable' (fun q => ?_)
  have hfiber : (fun X => selectedBlocks n X i) ⁻¹' {q} =
      ⋃ L : {L : IndexList n // vectorOfList L i = q},
        selectedList (N := N) n ⁻¹' {L.1} := by
    ext X
    constructor
    · intro h
      change selectedBlocks n X i = q at h
      apply Set.mem_iUnion.mpr
      refine ⟨⟨selectedList n X, h⟩, ?_⟩
      exact Set.mem_singleton (selectedList n X)
    · intro h
      obtain ⟨L, hsel⟩ := Set.mem_iUnion.mp h
      have hEq : selectedList n X = L.1 := hsel
      change vectorOfList (selectedList n X) i = q
      rw [hEq]
      exact L.2
  rw [hfiber]
  exact MeasurableSet.iUnion fun L =>
    measurable_selectedList hN n (measurableSet_singleton L.1)

end SwarmSelectedBlock
