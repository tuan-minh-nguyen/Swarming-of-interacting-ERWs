/-
Normalized selected-block laws from the actual array and its `Hidx` atoms.
-/
import Swarm.SelectedBlocks

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace SwarmSelectedBlockLaw

open SwarmSelInd SwarmSelectedBlock

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- The seed-conditioned array law, normalized by the actual strict-path mass. -/
noncomputable def seedLaw (p : ℝ) (m N : ℕ) : Measure (Array N) :=
  ((arrayMeasure N) {U : Array N | posPath p m U ∈ seed})⁻¹ •
    (arrayMeasure N).restrict (Achain p m N 0 Set.univ)

/-- A probability instance has exactly the strict-seed nonzero premise. -/
theorem isProbabilityMeasure_seedLaw
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0) :
    IsProbabilityMeasure (seedLaw p m N) := by
  refine ⟨?_⟩
  rw [seedLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Achain_zero_univ,
    ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)]

/-- The selected positive indices are equivalent to the `ℕ × ℕ` indexing used
by `selTotal`, by a level shift of one. -/
def blockIndexEquiv : BlockIndex ≃ (ℕ × ℕ) where
  toFun q := (q.1.1, (q.1.2 - 1).toNat)
  invFun i := ⟨(i.1, (i.2 : ℤ) + 1), by omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have hq := q.2
      omega
  right_inv i := by
    apply Prod.ext <;> simp

/-- The actual atomic law of one selected block. -/
noncomputable def blockLaw (p : ℝ) (m N : ℕ) : Measure BlockIndex :=
  Measure.sum fun q : BlockIndex =>
    blockMassAt p m N q.1.1 q.1.2 • Measure.dirac q

/-- Evaluation of the atomic block law on a singleton. -/
theorem blockLaw_singleton (p : ℝ) (m N : ℕ) (q : BlockIndex) :
    blockLaw p m N {q} = blockMassAt p m N q.1.1 q.1.2 := by
  exact Measure.sum_smul_dirac_singleton

/-- Reindexing `selTotal` over genuine positive block indices. -/
theorem selTotal_eq_tsum_blockIndex (p : ℝ) (m N : ℕ) :
    selTotal p m N =
      ∑' q : BlockIndex, blockMassAt p m N q.1.1 q.1.2 := by
  have h := blockIndexEquiv.symm.tsum_eq
    (fun q : BlockIndex => blockMassAt p m N q.1.1 q.1.2)
  change (∑' i : ℕ × ℕ, selMass p m N i) = _
  rw [← h]
  apply tsum_congr
  intro i
  rfl

/-- The one-stage normalization is exactly what makes the atomic block law a
probability law. -/
theorem isProbabilityMeasure_blockLaw (htot : selTotal p m N = 1) :
    IsProbabilityMeasure (blockLaw p m N) := by
  refine ⟨?_⟩
  rw [blockLaw, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem,
    Set.mem_univ, mul_one]
  rw [← selTotal_eq_tsum_blockIndex, htot]

/-- Vector/list conversion preserves the product of one-block masses. -/
theorem listOfVector_prod_blockMass (p : ℝ) (m N : ℕ) {n : ℕ}
    (v : Fin n → BlockIndex) :
    ((listOfVector v).1.map
      (fun q => blockMassAt p m N q.1 q.2)).prod =
      ∏ i, blockMassAt p m N (v i).1.1 (v i).1.2 := by
  change (List.map (fun q => blockMassAt p m N q.1 q.2)
    (List.ofFn (fun i => (v i).1))).prod = _
  rw [← List.ofFn_comp', List.prod_ofFn]

/-- Under the one-stage full-chain premise, the joint law of any finite number
of actual selected indices is the product of the one-block law. -/
theorem map_selectedBlocks_seedLaw (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0)
    (n : ℕ) :
    (seedLaw p m N).map (fun U => selectedBlocks n (posPath p m U)) =
      Measure.pi (fun _ : Fin n => blockLaw p m N) := by
  letI : IsProbabilityMeasure (seedLaw p m N) := isProbabilityMeasure_seedLaw hpos
  letI : IsProbabilityMeasure (blockLaw p m N) := isProbabilityMeasure_blockLaw htot
  apply Measure.ext_of_singleton
  intro v
  have hmeas : Measurable (fun U : Array N => selectedBlocks n (posPath p m U)) :=
    (measurable_selectedBlocks hN n).comp (measurable_posPath p m N)
  have hseedmeas : MeasurableSet (Achain p m N 0 Set.univ) :=
    measurableSet_Achain 0 MeasurableSet.univ
  have hae : ∀ᵐ U ∂((arrayMeasure N).restrict (Achain p m N 0 Set.univ)),
      ∀ k : ℕ, posPath p m U ∈ Hpath (N := N) k Set.univ := by
    rw [ae_restrict_iff' hseedmeas]
    filter_upwards [ae_Hpath_all (p := p) (m := m) hN htot] with U hU hU0
    apply hU
    rwa [Achain_zero_univ] at hU0
  let S : Set (Array N) :=
    (fun U => selectedBlocks n (posPath p m U)) ⁻¹' {v}
  let H : Set (Array N) := AchainIdx p m N (listOfVector v).1 Set.univ
  have hset : S =ᵐ[((arrayMeasure N).restrict (Achain p m N 0 Set.univ))] H := by
    filter_upwards [hae] with U hU
    apply propext
    change (U ∈ S ↔ U ∈ H)
    have hchain : posPath p m U ∈ Hpath (N := N) n Set.univ := hU n
    have hex : ∃ K : IndexList n, posPath p m U ∈ Hidx K.1 Set.univ := by
      change U ∈ Achain p m N n Set.univ at hchain
      rw [Achain_eq_iUnion_idx] at hchain
      obtain ⟨K, hK⟩ := Set.mem_iUnion.mp hchain
      exact ⟨K, hK⟩
    constructor
    · intro hs
      change vectorOfList (selectedList n (posPath p m U)) = v at hs
      have hl : selectedList n (posPath p m U) = listOfVector v := by
        calc
          selectedList n (posPath p m U) =
              listOfVector (vectorOfList (selectedList n (posPath p m U))) :=
            (listOfVector_vectorOfList _).symm
          _ = listOfVector v := congrArg listOfVector hs
      have hm := selectedList_mem hex
      change posPath p m U ∈ Hidx (listOfVector v).1 Set.univ
      rw [← hl]
      exact hm
    · intro hh
      change posPath p m U ∈ Hidx (listOfVector v).1 Set.univ at hh
      have hs := selectedList_eq_of_mem hN hh
      change selectedBlocks n (posPath p m U) = v
      rw [selectedBlocks, hs]
      exact vectorOfList_listOfVector v
  have hrestr : (arrayMeasure N).restrict (Achain p m N 0 Set.univ) S =
      (arrayMeasure N).restrict (Achain p m N 0 Set.univ) H :=
    measure_congr hset
  have hHsub : H ⊆ Achain p m N 0 Set.univ := by
    intro U hU
    rw [Achain_zero_univ]
    exact Hidx_subset_seed hU
  have hrestrH : (arrayMeasure N).restrict (Achain p m N 0 Set.univ) H =
      (arrayMeasure N) H := by
    rw [Measure.restrict_apply (show MeasurableSet H by
      dsimp only [H]
      exact measurableSet_AchainIdx _ MeasurableSet.univ),
      Set.inter_eq_left.mpr hHsub]
  rw [Measure.map_apply hmeas (measurableSet_singleton v), Measure.pi_singleton]
  change seedLaw p m N S = _
  simp_rw [blockLaw_singleton]
  calc
    seedLaw p m N S =
        ((arrayMeasure N) {U : Array N | posPath p m U ∈ seed})⁻¹ *
          ((arrayMeasure N).restrict (Achain p m N 0 Set.univ) H) := by
      rw [seedLaw, Measure.smul_apply, smul_eq_mul, hrestr]
    _ = ((arrayMeasure N) {U : Array N | posPath p m U ∈ seed})⁻¹ *
        (((listOfVector v).1.map
          (fun q => blockMassAt p m N q.1 q.2)).prod *
            (arrayMeasure N) {U : Array N | posPath p m U ∈ seed}) := by
      dsimp only [H] at hrestrH ⊢
      rw [hrestrH, measure_AchainIdx_univ (p := p) (m := m) hN (listOfVector v).1
        (listOfVector v).2.2]
    _ = ((listOfVector v).1.map
          (fun q => blockMassAt p m N q.1 q.2)).prod :=
      SwarmChain.inv_mul_mul_cancel hpos (measure_ne_top _ _)
    _ = ∏ i, blockMassAt p m N (v i).1.1 (v i).1.2 :=
      listOfVector_prod_blockMass p m N v

/-! ### Finite-family independence and common marginals -/

/-- Every coordinate of the selected vector has the actual one-block law. -/
theorem map_coordinate_seedLaw (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0)
    {n : ℕ} (i : Fin n) :
    (seedLaw p m N).map (fun U => selectedBlocks n (posPath p m U) i) =
      blockLaw p m N := by
  letI : IsProbabilityMeasure (blockLaw p m N) := isProbabilityMeasure_blockLaw htot
  have hmeas : Measurable (fun U : Array N => selectedBlocks n (posPath p m U)) :=
    (measurable_selectedBlocks hN n).comp (measurable_posPath p m N)
  calc
    (seedLaw p m N).map (fun U => selectedBlocks n (posPath p m U) i) =
        (seedLaw p m N).map ((fun x => x i) ∘
          (fun U => selectedBlocks n (posPath p m U))) := rfl
    _ = ((seedLaw p m N).map
        (fun U => selectedBlocks n (posPath p m U))).map (fun x => x i) :=
      (Measure.map_map (measurable_pi_apply i) hmeas).symm
    _ = (Measure.pi (fun _ : Fin n => blockLaw p m N)).map (fun x => x i) := by
      rw [map_selectedBlocks_seedLaw hN htot hpos n]
    _ = blockLaw p m N :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin n => blockLaw p m N) i).map_eq

/-- The coordinates of each actual finite selected-block vector are mutually
independent with the common one-block law. -/
theorem iIndepFun_selectedBlocks_seedLaw (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0)
    (n : ℕ) :
    iIndepFun (fun i U => selectedBlocks n (posPath p m U) i) (seedLaw p m N) := by
  letI : IsProbabilityMeasure (seedLaw p m N) := isProbabilityMeasure_seedLaw hpos
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · rw [map_selectedBlocks_seedLaw hN htot hpos n]
    congr 1
    funext i
    exact (map_coordinate_seedLaw hN htot hpos i).symm
  · intro i
    exact ((measurable_pi_apply i).comp
      ((measurable_selectedBlocks hN n).comp (measurable_posPath p m N))).aemeasurable

/-- Any two coordinates of a selected vector are identically distributed. -/
theorem identDistrib_selectedBlocks_seedLaw (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0)
    {n : ℕ} (i j : Fin n) :
    IdentDistrib (fun U => selectedBlocks n (posPath p m U) i)
      (fun U => selectedBlocks n (posPath p m U) j) (seedLaw p m N) (seedLaw p m N) := by
  have hi : Measurable (fun U : Array N => selectedBlocks n (posPath p m U) i) :=
    (measurable_pi_apply i).comp
      ((measurable_selectedBlocks hN n).comp (measurable_posPath p m N))
  have hj : Measurable (fun U : Array N => selectedBlocks n (posPath p m U) j) :=
    (measurable_pi_apply j).comp
      ((measurable_selectedBlocks hN n).comp (measurable_posPath p m N))
  exact IdentDistrib.mk hi.aemeasurable hj.aemeasurable
    ((map_coordinate_seedLaw hN htot hpos i).trans
      (map_coordinate_seedLaw hN htot hpos j).symm)

/-- Actual model parameters.  The only remaining structural premise is the
existing one-stage full-selection statement `hfull`; seed positivity is proved
from the model, and full selected chains follow from the accepted recursion. -/
theorem map_selectedBlocks_seedLaw_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN2 : 2 ≤ N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N | posPath p m U ∈ seed})
    (n : ℕ) :
    (seedLaw p m N).map (fun U => selectedBlocks n (posPath p m U)) =
      Measure.pi (fun _ : Fin n => blockLaw p m N) := by
  have hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN2
  have htot : selTotal p m N = 1 :=
    (full_iff_totalMass_one (p := p) (m := m) (by omega) hpos
      (measure_ne_top (arrayMeasure N) _)).mp hfull
  exact map_selectedBlocks_seedLaw (by omega) htot hpos n

end SwarmSelectedBlockLaw
