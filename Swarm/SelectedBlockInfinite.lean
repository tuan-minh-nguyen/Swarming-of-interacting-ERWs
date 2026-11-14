/-
Coherent infinite selected-block indices from the finite selected vectors.

The only stochastic input is the same one-stage `hfull` used by the finite
product-law package. On a genuine `n`-chain event, `selectedBlocks n` is the
length-`n` prefix of one infinite sequence on the actual array. The sequence
has `KacFormula.FreshBlocks` law under `seedLaw`; no fallback value is called a
regeneration block.
-/
import Swarm.SelectedBlockLaw
import Swarm.FBLaw

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace SwarmSelectedBlockInfinite

open SwarmSelInd SwarmSelectedBlock SwarmSelectedBlockLaw

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- The normalized seed measures used by the old and new packages are equal. -/
theorem seedLaw_eq_seedCond :
    seedLaw p m N = SwarmFB.seedCond (p := p) (m := m) (N := N) := by
  rw [seedLaw, SwarmFB.seedCond, ProbabilityTheory.cond,
    SwarmSelInd.Achain_zero_univ]
  rfl

/-- Reindexing a genuine positive block and restoring its level is the identity. -/
theorem blockIndexEquiv_raw (q : BlockIndex) :
    ((blockIndexEquiv q).1, SwarmFB.blkLevel (blockIndexEquiv q)) = q.1 := by
  apply Prod.ext
  · rfl
  · dsimp [blockIndexEquiv, SwarmFB.blkLevel]
    have hq := q.2
    omega

/-- The old atom list of the reindexed finite vector is the new package's list. -/
theorem idxList_map_blockIndexEquiv {n : ℕ} (v : Fin n → BlockIndex) :
    SwarmFB.idxList (fun i => blockIndexEquiv (v i)) = (listOfVector v).1 := by
  unfold SwarmFB.idxList listOfVector
  congr 1
  funext i
  exact blockIndexEquiv_raw (v i)

/-- On a genuine finite chain, the accepted finite selected vector is exactly
the corresponding prefix of the older coherent infinite index sequence. -/
theorem selectedBlocks_eq_jointZ (hN : 0 < N) {n : ℕ} {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) (i : Fin n) :
    blockIndexEquiv (selectedBlocks n (posPath p m U) i) =
      SwarmFB.jointZ (p := p) (m := m) (N := N) n U i := by
  let L : Fin n → ℕ × ℕ := fun j => blockIndexEquiv (selectedBlocks n (posPath p m U) j)
  have hchain : posPath p m U ∈ SwarmSelInd.Hpath (N := N) n Set.univ := hU
  rw [SwarmSelInd.Hpath_eq_iUnion_Hidx] at hchain
  obtain ⟨K, hK⟩ := Set.mem_iUnion.mp hchain
  have hex : ∃ K : IndexList n, posPath p m U ∈ SwarmSelInd.Hidx K.1 Set.univ :=
    ⟨K, hK⟩
  have hlist : SwarmFB.idxList L = (selectedList n (posPath p m U)).1 := by
    change SwarmFB.idxList (fun j => blockIndexEquiv
      (vectorOfList (selectedList n (posPath p m U)) j)) = _
    rw [idxList_map_blockIndexEquiv]
    exact congrArg Subtype.val
      (listOfVector_vectorOfList (selectedList n (posPath p m U)))
  have hAtom : U ∈ SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    change posPath p m U ∈ SwarmSelInd.Hidx (SwarmFB.idxList L) Set.univ
    rw [hlist]
    exact selectedList_mem hex
  exact (SwarmFB.Z_eq_of_mem_atom (p := p) (m := m) hN L hAtom i).symm

/-- One coherent infinite sequence with the new positive-level index type. -/
noncomputable def positiveSeq (k : ℕ) (U : Array N) : BlockIndex :=
  blockIndexEquiv.symm (SwarmFB.Z (p := p) (m := m) (N := N) k U)

/-- The initial segment of the coherent sequence. -/
noncomputable def positiveJoint (n : ℕ) (U : Array N) : Fin n → BlockIndex :=
  fun i => positiveSeq (p := p) (m := m) i.1 U

/-- Every genuine finite selected vector is a prefix of `positiveSeq`. -/
theorem positiveJoint_eq_selectedBlocks (hN : 0 < N) {n : ℕ} {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N n Set.univ) :
    positiveJoint (p := p) (m := m) n U = selectedBlocks n (posPath p m U) := by
  funext i
  apply blockIndexEquiv.injective
  simp only [positiveJoint, positiveSeq, Equiv.apply_symm_apply]
  exact selectedBlocks_eq_jointZ (p := p) (m := m) hN hU i |>.symm

/-- The coherent coordinates are measurable. -/
theorem measurable_positiveSeq (hN : 0 < N) (k : ℕ) :
    Measurable (positiveSeq (p := p) (m := m) (N := N) k) := by
  exact (measurable_of_countable blockIndexEquiv.symm).comp
    (SwarmFB.measurable_Z (p := p) (m := m) hN k)

/-- The two atomic block laws are identified by the positive-level equivalence. -/
theorem map_Q_blockIndexEquiv :
    (SwarmFB.Q (p := p) (m := m) (N := N)).map blockIndexEquiv.symm =
      blockLaw p m N := by
  apply Measure.ext_of_singleton
  intro q
  have he : Measurable (blockIndexEquiv.symm) := measurable_of_countable _
  rw [Measure.map_apply he (measurableSet_singleton q)]
  have hpre : blockIndexEquiv.symm ⁻¹' {q} = {blockIndexEquiv q} := by
    ext i
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hi
      have := congrArg blockIndexEquiv hi
      simpa only [Equiv.apply_symm_apply] using this
    · intro hi
      rw [hi]
      exact blockIndexEquiv.symm_apply_apply q
  rw [hpre]
  change SwarmFB.Q (p := p) (m := m) (N := N) {blockIndexEquiv q} = _
  rw [SwarmFB.Q_apply (measurableSet_singleton (blockIndexEquiv q))]
  simp only [tsum_singleton]
  rw [blockLaw_singleton, SwarmFB.bm_eq]
  exact congrArg (fun d : ℤ => SwarmSelInd.blockMassAt p m N q.1.1 d)
    (congrArg Prod.snd (blockIndexEquiv_raw q))

/-- Under the one-stage normalization, the fallback cannot affect the prefix
identity: every finite selected vector agrees almost surely with the coherent
sequence on the genuine chain event. -/
theorem ae_positiveJoint_eq_selectedBlocks (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0) (n : ℕ) :
    (fun U => positiveJoint (p := p) (m := m) n U) =ᵐ[seedLaw p m N]
      (fun U => selectedBlocks n (posPath p m U)) := by
  rw [seedLaw_eq_seedCond]
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) hpos
  have hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) := by
    apply (SwarmSelInd.full_iff_totalMass_one (p := p) (m := m) hN hpos
      (measure_ne_top (arrayMeasure N) _)).mpr
    exact htot
  have hchain : SwarmFB.seedCond (p := p) (m := m) (N := N)
      (SwarmSelInd.Achain p m N n Set.univ) = 1 :=
    SwarmFB.seedCond_chain (p := p) (m := m) hN hfull hpos n
  have hae : ∀ᵐ U ∂(SwarmFB.seedCond (p := p) (m := m) (N := N)),
      U ∈ SwarmSelInd.Achain p m N n Set.univ :=
    (mem_ae_iff_prob_eq_one (SwarmSelInd.measurableSet_Achain n MeasurableSet.univ)).mpr hchain
  filter_upwards [hae] with U hU
  exact positiveJoint_eq_selectedBlocks (p := p) (m := m) hN hU

/-- Almost every seed path carries all finite prefixes simultaneously: the
coherent sequence really is an infinite actual selected-block sequence a.e. -/
theorem ae_positiveJoint_eq_selectedBlocks_all (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0) :
    ∀ᵐ U ∂(seedLaw p m N), ∀ n : ℕ,
      positiveJoint (p := p) (m := m) n U = selectedBlocks n (posPath p m U) := by
  exact MeasureTheory.ae_all_iff.2 (fun n =>
    ae_positiveJoint_eq_selectedBlocks (p := p) (m := m) hN htot hpos n)

/-- Every finite prefix of the coherent sequence has exactly the accepted
finite-dimensional product law. -/
theorem map_positiveJoint (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0) (n : ℕ) :
    (seedLaw p m N).map (fun U => positiveJoint (p := p) (m := m) n U) =
      Measure.pi (fun _ : Fin n => blockLaw p m N) := by
  calc
    (seedLaw p m N).map (fun U => positiveJoint (p := p) (m := m) n U) =
        (seedLaw p m N).map (fun U => selectedBlocks n (posPath p m U)) :=
      Measure.map_congr (ae_positiveJoint_eq_selectedBlocks (p := p) (m := m) hN htot hpos n)
    _ = Measure.pi (fun _ : Fin n => blockLaw p m N) :=
      map_selectedBlocks_seedLaw (p := p) (m := m) hN htot hpos n

/-- Transport of the `FreshBlocks` interface through a measurable equivalence
of block-index types. -/
theorem freshBlocks_map_equiv {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : ℕ → Ω → S} {Q : Measure S}
    (h : KacFormula.FreshBlocks μ Z Q) (e : S ≃ T) (he : Measurable e) :
    KacFormula.FreshBlocks μ (fun k ω => e (Z k ω)) (Q.map e) := by
  refine ⟨fun k => he.comp (h.1 k), ?_⟩
  intro n E C hE hC
  let E' : Set (Fin n → S) := (fun L i => e (L i)) ⁻¹' E
  have hmap : Measurable (fun (L : Fin n → S) (i : Fin n) => e (L i)) :=
    measurable_pi_lambda _ (fun i => he.comp (measurable_pi_apply i))
  have hE' : MeasurableSet E' := hmap hE
  change μ (KacFormula.joint (fun k ω => e (Z k ω)) n ⁻¹' E ∩
    (fun ω => e (Z n ω)) ⁻¹' C) =
      μ (KacFormula.joint (fun k ω => e (Z k ω)) n ⁻¹' E) * (Q.map e) C
  rw [show KacFormula.joint (fun k ω => e (Z k ω)) n ⁻¹' E =
      KacFormula.joint Z n ⁻¹' E' from rfl,
    show (fun ω => e (Z n ω)) ⁻¹' C = Z n ⁻¹' (e ⁻¹' C) from rfl,
    Measure.map_apply he hC]
  exact h.2 n E' (e ⁻¹' C) hE' (he hC)

/-- The coherent positive-index sequence has the `FreshBlocks` product law
under the new package's actual seed law. -/
theorem freshBlocks_positiveSeq (hN : 0 < N) (htot : selTotal p m N = 1)
    (hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0) :
    KacFormula.FreshBlocks (seedLaw p m N)
      (fun k U => positiveSeq (p := p) (m := m) k U) (blockLaw p m N) := by
  rw [seedLaw_eq_seedCond, ← map_Q_blockIndexEquiv]
  letI : IsProbabilityMeasure (SwarmFB.seedCond (p := p) (m := m) (N := N)) :=
    SwarmFB.seedCond_isProbabilityMeasure (p := p) (m := m) hpos
  have hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) (SwarmFB.seedSet (p := p) (m := m) (N := N)) := by
    apply (SwarmSelInd.full_iff_totalMass_one (p := p) (m := m) hN hpos
      (measure_ne_top (arrayMeasure N) _)).mpr
    exact htot
  letI : IsProbabilityMeasure (SwarmFB.Q (p := p) (m := m) (N := N)) :=
    SwarmFB.Q_isProbabilityMeasure (p := p) (m := m) hN hfull hpos
  exact freshBlocks_map_equiv
    (SwarmFB.freshBlocks (p := p) (m := m) hN hfull hpos)
    blockIndexEquiv.symm (measurable_of_countable _)

/-- Actual-model form: strict-seed positivity is discharged and the only
remaining stochastic premise is the genuine one-stage fullness statement. -/
theorem freshBlocks_positiveSeq_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN2 : 2 ≤ N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ) =
      (arrayMeasure N) {U : Array N | posPath p m U ∈ seed}) :
    KacFormula.FreshBlocks (seedLaw p m N)
      (fun k U => positiveSeq (p := p) (m := m) k U) (blockLaw p m N) := by
  have hpos : (arrayMeasure N) {U : Array N | posPath p m U ∈ seed} ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN2
  have htot : selTotal p m N = 1 :=
    (SwarmSelInd.full_iff_totalMass_one (p := p) (m := m) (by omega) hpos
      (measure_ne_top (arrayMeasure N) _)).mp hfull
  exact freshBlocks_positiveSeq (p := p) (m := m) (by omega) htot hpos

end SwarmSelectedBlockInfinite
