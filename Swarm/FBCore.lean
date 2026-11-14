/-
# Sequence-space `FreshBlocks` packaging of the recursive selected blocks

## The objects

* `blkLevel i` for a block index `i = (t, g) : ℕ × ℕ` is the positive level `g + 1`; this is
  exactly the indexing of `SwarmSelInd.selMass` (`i` is not a `(D, time)` pair of unrelated
  type: it is the selected block, whose time is `i.1` and whose level increment is
  `blkLevel i`).
* `bm i = SwarmSelInd.selMass p m N i` is the mass of the block `i`.
* `Q = ∑ᵢ bm i • δᵢ` is the block index law; it is a probability measure under the one-step
  hypothesis (`Q_isProbabilityMeasure`), and `bm` is then a probability mass function.
* `Atom L` for `L : Fin n → ℕ × ℕ` is the array event "the first `n` selected blocks are exactly
  `L`" — literally `SwarmSelInd.AchainIdx` of the corresponding block list.
* `blkFun n U : Fin n → ℕ × ℕ` is the family of the first `n` selected block indices of the array
  `U`, defined by *unique* selection on the atoms, with the single explicitly specified
  measurable default `(0, 0)` on the (null, cf. `measure_compl_iUnion_atom`) complement of the
  `n`-chain event.  `Z k U` is the `k`-th block index (zero-based), `jointZ n U` its initial
  segment.

## What is proved here

`iUnion_atom_eq`, `atom_disjoint`, `atom_mass`, `measure_atom`, `atom_prefix`,
`jointZ_eq_blkFun`, `measurable_Z`: the atoms partition the chain event, carry the product of
the block masses, and the sequence is a measurable function of the array whose initial segments
are the atoms.

## What is *not* here

`SwarmSelInd.selTotal = 1` (the paper's `D < ∞` at one step, a.k.a. `hfull`) is **not** proved;
it is an explicit hypothesis of the law computations in `FBLaw.lean`.  Nothing here proves the
invariant record law, `(ED)`, tightness, regeneration or `MainClaim`.
-/
import Swarm.Induction
import Mathlib.Data.Fin.Tuple.Take
import Swarm.RegenIid

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SwarmFB

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### The block index space, the block mass and the block law -/

/-- The level of the block index `(t, g)`: the selected block sits at level `g + 1 ≥ 1`.
This is the indexing already used by `SwarmSelInd.selMass`. -/
def blkLevel (i : ℕ × ℕ) : ℤ := (i.2 : ℤ) + 1

theorem blkLevel_pos (i : ℕ × ℕ) : 1 ≤ blkLevel i := by
  unfold blkLevel; omega

/-- The mass of the selected block with index `i` under the array measure. -/
noncomputable def bm (i : ℕ × ℕ) : ℝ≥0∞ := SwarmSelInd.selMass p m N i

/-- `bm` is the block mass at the level `blkLevel i` (definitional). -/
theorem bm_eq (i : ℕ × ℕ) :
    bm (p := p) (m := m) (N := N) i = SwarmSelInd.blockMassAt p m N i.1 (blkLevel i) := rfl

/-- The total selected block mass (defective unless the one-step hypothesis holds). -/
noncomputable def selTotal : ℝ≥0∞ := SwarmSelInd.selTotal p m N

/-- **The block index law**: the selected block mass as a measure on the index space.  Under
`selTotal = 1` it is a probability measure (`Q_isProbabilityMeasure`). -/
noncomputable def Q : Measure (ℕ × ℕ) :=
  Measure.sum fun i => bm (p := p) (m := m) (N := N) i • Measure.dirac i

/-! ### The seed event and the seed-conditioned measure -/

/-- The paper's seed event `V` on the array: the position path is strictly positive after time
`0` and starts at `0`. -/
def seedSet : Set (Array N) :=
  {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed (N := N)}

theorem measurableSet_seedSet : MeasurableSet (seedSet (p := p) (m := m) (N := N)) :=
  (SwarmRestart.measurable_posPath p m N) SwarmFresh.measurableSet_strictPos

/-- **The seed-conditioned array measure** `P^*`: the array measure conditioned on the seed
event.  This is the measure under which the block index law is a probability law; it is a
probability measure as soon as the seed has positive mass (`seedCond_isProbabilityMeasure`). -/
noncomputable def seedCond : Measure (Array N) :=
  ProbabilityTheory.cond (arrayMeasure N) (seedSet (p := p) (m := m) (N := N))

theorem seedCond_isProbabilityMeasure (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
  ProbabilityTheory.cond_isProbabilityMeasure h0

theorem seedCond_apply {s : Set (Array N)}
    (hs : MeasurableSet (seedSet (p := p) (m := m) (N := N))) :
    seedCond (p := p) (m := m) (N := N) s
      = ((arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))⁻¹ *
          (arrayMeasure N) (seedSet (p := p) (m := m) (N := N) ∩ s) :=
  ProbabilityTheory.cond_apply hs (arrayMeasure N) s

/-! ### The atoms: the first `n` selected block indices -/

/-- The block list of a family of block indices: `(t, g) ↦ (t, g+1)`, i.e. time and level. -/
def idxList {n : ℕ} (L : Fin n → ℕ × ℕ) : List (ℕ × ℤ) :=
  List.ofFn fun i => ((L i).1, blkLevel (L i))

theorem idxList_length {n : ℕ} (L : Fin n → ℕ × ℕ) : (idxList L).length = n := by
  simp [idxList]

theorem idxList_pos {n : ℕ} (L : Fin n → ℕ × ℕ) : ∀ q ∈ idxList L, 1 ≤ q.2 := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact blkLevel_pos _

theorem idxList_injective {n : ℕ} : Function.Injective (idxList (n := n)) := by
  intro L L' h
  have h2 := List.ofFn_inj.mp h
  funext i
  have hi := congrFun h2 i
  simp only [Prod.mk.injEq, blkLevel] at hi
  exact Prod.ext hi.1 (by omega)

/-- The product of the block masses of a family of block indices. -/
noncomputable def blkProd {n : ℕ} (L : Fin n → ℕ × ℕ) : ℝ≥0∞ :=
  ∏ i, bm (p := p) (m := m) (N := N) (L i)

/-- The mass of the block list, in the shape produced by `Induction.measure_AchainIdx`. -/
theorem blkProd_eq_list_prod {n : ℕ} (L : Fin n → ℕ × ℕ) :
    ((idxList L).map (fun q => SwarmSelInd.blockMassAt p m N q.1 q.2)).prod
      = blkProd (p := p) (m := m) (N := N) L := by
  unfold idxList blkProd
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- **The atom of the block family `L`**: the array's first `n` selected blocks are exactly `L`.
This is `SwarmSelInd.AchainIdx` of the corresponding list, so all of the recursion's
finite-dimensional identities apply to it verbatim. -/
noncomputable def Atom {n : ℕ} (L : Fin n → ℕ × ℕ) : Set (Array N) :=
  SwarmSelInd.AchainIdx p m N (idxList L) univ

theorem measurableSet_atom {n : ℕ} (L : Fin n → ℕ × ℕ) :
    MeasurableSet (Atom (p := p) (m := m) (N := N) L) :=
  SwarmSelInd.measurableSet_AchainIdx _ MeasurableSet.univ

/-- Different block families of the same length are disjoint. -/
theorem atom_disjoint (hN : 0 < N) {n : ℕ} {L L' : Fin n → ℕ × ℕ} (hne : L ≠ L') :
    Disjoint (Atom (p := p) (m := m) (N := N) L) (Atom (p := p) (m := m) (N := N) L') := by
  refine SwarmSelInd.AchainIdx_disjoint (p := p) (m := m) hN (idxList_pos L) (idxList_pos L')
    ?_ ?_ _ _
  · rw [idxList_length, idxList_length]
  · intro h; exact hne (idxList_injective h)

/-- **Uniqueness of the selected block family**: at most one block family of length `n` occurs. -/
theorem atom_unique (hN : 0 < N) {n : ℕ} {L L' : Fin n → ℕ × ℕ} {U : Array N}
    (h : U ∈ Atom (p := p) (m := m) (N := N) L)
    (h' : U ∈ Atom (p := p) (m := m) (N := N) L') : L = L' := by
  by_contra hne
  exact Set.disjoint_left.mp (atom_disjoint (p := p) (m := m) hN hne) h h'

/-- **The atom mass**: the product of the block masses times the seed mass.  This is the
`Induction` finite-dimensional block law transported to the index space `ℕ × ℕ`. -/
theorem atom_mass (hN : 0 < N) {n : ℕ} (L : Fin n → ℕ × ℕ) :
    (arrayMeasure N) (Atom (p := p) (m := m) (N := N) L)
      = blkProd (p := p) (m := m) (N := N) L *
          (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) := by
  have h := SwarmSelInd.measure_AchainIdx_univ (p := p) (m := m) hN (idxList L) (idxList_pos L)
  rw [← blkProd_eq_list_prod]
  exact h

/-- **The atoms exhaust the chain event**: the `n`-chain event is exactly the disjoint union of
the block families of length `n`. -/
theorem iUnion_atom_eq (n : ℕ) :
    (⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L)
      = SwarmSelInd.Achain p m N n univ := by
  rw [SwarmSelInd.Achain_eq_iUnion_idx]
  apply le_antisymm
  · intro U hU
    obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU
    exact Set.mem_iUnion.mpr ⟨⟨idxList L, idxList_length L, idxList_pos L⟩, hL⟩
  · intro U hU
    obtain ⟨⟨M, hlen, hpos⟩, hM⟩ := Set.mem_iUnion.mp hU
    subst hlen
    have hfun : (fun i : Fin M.length =>
        ((M.get i).1, blkLevel ((M.get i).1, ((M.get i).2 - 1).toNat))) = M.get := by
      funext i
      have hp : 1 ≤ (M.get i).2 := hpos (M.get i) (List.get_mem M i)
      have hcast : ((((M.get i).2 - 1).toNat : ℤ)) = (M.get i).2 - 1 :=
        Int.toNat_of_nonneg (by omega)
      refine Prod.ext rfl ?_
      simp only [blkLevel]
      omega
    refine Set.mem_iUnion.mpr ⟨fun i : Fin M.length => ((M.get i).1, ((M.get i).2 - 1).toNat), ?_⟩
    have hidx : idxList (fun i : Fin M.length => ((M.get i).1, ((M.get i).2 - 1).toNat)) = M := by
      unfold idxList
      rw [hfun, List.ofFn_get]
    show U ∈ SwarmSelInd.AchainIdx p m N (idxList _) univ
    rw [hidx]
    exact hM

/-! ### The block index sequence of one array -/

/-- **The first `n` selected block indices of an array**, by unique selection on the atoms.

Off the `n`-chain event this takes the explicitly specified default value `(0, 0)`
(`fun _ => (0, 0)`); by `measure_compl_iUnion_atom` that set is null for the seed-conditioned
measure under the one-step hypothesis, so the default never contributes to the law. -/
noncomputable def blkFun (n : ℕ) (U : Array N) : Fin n → ℕ × ℕ :=
  if h : ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L then
    Classical.choose h
  else fun _ => (0, 0)

/-- **The `k`-th selected block index of an array** (zero-based): the last entry of the first
`k+1` selected blocks.  Its time is `(Z k U).1` and its level is `blkLevel (Z k U)`. -/
noncomputable def Z (k : ℕ) (U : Array N) : ℕ × ℕ :=
  blkFun (p := p) (m := m) (N := N) (k + 1) U ⟨k, Nat.lt_succ_self k⟩

/-- The initial segment of the block index sequence. -/
noncomputable def jointZ (n : ℕ) (U : Array N) : Fin n → ℕ × ℕ :=
  fun i => Z (p := p) (m := m) (N := N) i.1 U

theorem blkFun_of_mem (hN : 0 < N) {n : ℕ} {L : Fin n → ℕ × ℕ} {U : Array N}
    (h : U ∈ Atom (p := p) (m := m) (N := N) L) :
    blkFun (p := p) (m := m) (N := N) n U = L := by
  have hex : ∃ L' : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L' := ⟨L, h⟩
  rw [blkFun, dif_pos hex]
  exact atom_unique (p := p) (m := m) hN (Classical.choose_spec hex) h

/-- The level points of `blkFun` are measurable: on each atom the value is fixed, and the atoms
are measurable. -/
theorem measurable_blkFun_eq (hN : 0 < N) (n : ℕ) (L : Fin n → ℕ × ℕ) :
    MeasurableSet {U : Array N | blkFun (p := p) (m := m) (N := N) n U = L} := by
  have hUnion : MeasurableSet {U : Array N | ∃ L' : Fin n → ℕ × ℕ,
      U ∈ Atom (p := p) (m := m) (N := N) L'} := by
    rw [show {U : Array N | ∃ L' : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L'}
        = ⋃ L' : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L' from by
      ext U; simp]
    exact MeasurableSet.iUnion fun L' => measurableSet_atom L'
  have hcompl : MeasurableSet {U : Array N | ¬ ∃ L' : Fin n → ℕ × ℕ,
      U ∈ Atom (p := p) (m := m) (N := N) L'} := hUnion.compl
  rcases eq_or_ne L (fun _ => (0, 0)) with hL | hL
  · have hset : {U : Array N | blkFun (p := p) (m := m) (N := N) n U = L}
        = Atom (p := p) (m := m) (N := N) L ∪
          {U : Array N | ¬ ∃ L' : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L'} := by
      ext U
      by_cases hex : ∃ L' : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L'
      · have hch := Classical.choose_spec hex
        have hb : blkFun (p := p) (m := m) (N := N) n U = Classical.choose hex := by
          rw [blkFun, dif_pos hex]
        constructor
        · intro hU
          refine Or.inl ?_
          have hU' : blkFun (p := p) (m := m) (N := N) n U = L := hU
          have hchL : Classical.choose hex = L := by rw [← hb]; exact hU'

          rw [← hchL]
          exact hch
        · rintro (h | h)
          · show blkFun (p := p) (m := m) (N := N) n U = L
            rw [hb]
            exact atom_unique (p := p) (m := m) hN hch h
          · exact absurd hex h
      · have hb : blkFun (p := p) (m := m) (N := N) n U = fun _ => (0, 0) := by
          rw [blkFun, dif_neg hex]
        constructor
        · intro _
          exact Or.inr hex
        · intro _
          show blkFun (p := p) (m := m) (N := N) n U = L
          rw [hb, ← hL]
    rw [hset]
    exact (measurableSet_atom (p := p) (m := m) (N := N) L).union hcompl
  · have hset : {U : Array N | blkFun (p := p) (m := m) (N := N) n U = L}
        = Atom (p := p) (m := m) (N := N) L := by
      ext U
      by_cases hex : ∃ L' : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L'
      · have hch := Classical.choose_spec hex
        have hb : blkFun (p := p) (m := m) (N := N) n U = Classical.choose hex := by
          rw [blkFun, dif_pos hex]
        constructor
        · intro hU
          have hU' : blkFun (p := p) (m := m) (N := N) n U = L := hU
          have hchL : Classical.choose hex = L := by rw [← hb]; exact hU' 
          rw [← hchL]
          exact hch
        · intro h
          show blkFun (p := p) (m := m) (N := N) n U = L
          rw [hb]
          exact atom_unique (p := p) (m := m) hN hch h
      · have hb : blkFun (p := p) (m := m) (N := N) n U = fun _ => (0, 0) := by
          rw [blkFun, dif_neg hex]
        constructor
        · intro hU
          have hU' : blkFun (p := p) (m := m) (N := N) n U = L := hU
          exact absurd (by rw [hb] at hU'; exact hU'.symm) hL
        · intro hU
          exact absurd ⟨L, hU⟩ hex
    rw [hset]
    exact measurableSet_atom (p := p) (m := m) (N := N) L

theorem measurable_blkFun_apply (hN : 0 < N) (n : ℕ) (i : Fin n) :
    Measurable fun U : Array N => blkFun (p := p) (m := m) (N := N) n U i := by
  set f : Array N → ℕ × ℕ := fun U => blkFun (p := p) (m := m) (N := N) n U i with hf
  refine measurable_to_countable' (f := f) fun y => ?_
  have hset : f ⁻¹' {y}
      = ⋃ L : {L : Fin n → ℕ × ℕ // L i = y},
          {U : Array N | blkFun (p := p) (m := m) (N := N) n U = L.1} := by
    ext U
    simp only [hf, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Subtype.exists,
      exists_prop]
    constructor
    · intro h
      exact ⟨blkFun (p := p) (m := m) (N := N) n U, h, rfl⟩
    · rintro ⟨L, hL, hLU⟩
      have hLU' : blkFun (p := p) (m := m) (N := N) n U = L := hLU
      rw [hLU']
      exact hL
  rw [hset]
  exact MeasurableSet.iUnion fun L => measurable_blkFun_eq (p := p) (m := m) hN n L.1

theorem measurable_blkFun (hN : 0 < N) (n : ℕ) :
    Measurable (blkFun (p := p) (m := m) (N := N) n) :=
  measurable_pi_iff.mpr fun i => measurable_blkFun_apply (p := p) (m := m) hN n i

theorem measurable_Z (hN : 0 < N) (k : ℕ) :
    Measurable (Z (p := p) (m := m) (N := N) k) :=
  (measurable_pi_iff.mp (measurable_blkFun (p := p) (m := m) hN (k + 1))) ⟨k, Nat.lt_succ_self k⟩

/-! ### Prefixes: the first `k` blocks of a selected chain are the selected chain -/

/-- **Appending blocks refines the chain event**: a chain of `L₁ ++ L₂` blocks is a chain of
`L₁` blocks followed by *some* seed path. -/
theorem mem_Hidx_nil_univ {X : ℕ → Fin N → ℤ} :
    X ∈ SwarmSelInd.Hidx (N := N) [] univ ↔ X ∈ SwarmSelInd.seed (N := N) := by
  rw [SwarmSelInd.mem_Hidx_nil]
  simp

theorem Hidx_append_subset : ∀ (L₁ L₂ : List (ℕ × ℤ)) {B : Set (ℕ → Fin N → ℤ)},
    SwarmSelInd.Hidx (N := N) (L₁ ++ L₂) B ⊆ SwarmSelInd.Hidx (N := N) L₁ univ
  | [], L₂, B => by
      intro X hX
      rw [mem_Hidx_nil_univ]
      exact SwarmSelInd.Hidx_subset_seed hX
  | (t, d) :: rest, L₂, B => by
      intro X hX
      rw [List.cons_append] at hX
      rw [SwarmSelInd.mem_Hidx_cons] at hX
      rw [SwarmSelInd.mem_Hidx_cons]
      exact ⟨hX.1, hX.2.1, Hidx_append_subset rest L₂ hX.2.2⟩

theorem AchainIdx_append_subset (L₁ L₂ : List (ℕ × ℤ)) (B : Set (ℕ → Fin N → ℤ)) :
    SwarmSelInd.AchainIdx p m N (L₁ ++ L₂) B ⊆ SwarmSelInd.AchainIdx p m N L₁ univ :=
  fun _ hU => Hidx_append_subset L₁ L₂ hU

theorem idxList_take {n : ℕ} (L : Fin n → ℕ × ℕ) {k : ℕ} (hk : k ≤ n) :
    idxList (Fin.take k hk L) = (idxList L).take k := by
  unfold idxList
  rw [← Fin.ofFn_take_eq_take_ofFn hk (fun i => ((L i).1, blkLevel (L i)))]
  rfl

/-- **A prefix of a selected chain is the selected chain of the prefix terms.** -/
theorem atom_prefix {n : ℕ} (L : Fin n → ℕ × ℕ) {k : ℕ} (hk : k ≤ n) :
    Atom (p := p) (m := m) (N := N) L ⊆ Atom (p := p) (m := m) (N := N) (Fin.take k hk L) := by
  intro U hU
  rw [Atom] at hU ⊢
  rw [idxList_take]
  rw [show idxList L = (idxList L).take k ++ (idxList L).drop k from
    (List.take_append_drop k (idxList L)).symm] at hU
  exact AchainIdx_append_subset _ _ _ hU

/-- **The block index sequence is the sequence of atoms**: on the `n`-chain event the initial
segment `jointZ n` of `Z` is exactly the unique block family selected by the atoms. -/
theorem jointZ_eq_blkFun (hN : 0 < N) (n : ℕ) {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N n univ) :
    jointZ (p := p) (m := m) (N := N) n U = blkFun (p := p) (m := m) (N := N) n U := by
  have hU' : U ∈ ⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L := by
    rw [iUnion_atom_eq]; exact hU
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  have hbf : blkFun (p := p) (m := m) (N := N) n U = L := blkFun_of_mem (p := p) (m := m) hN hL
  have hmem : U ∈ Atom (p := p) (m := m) (N := N) (blkFun (p := p) (m := m) (N := N) n U) := by
    rw [hbf]; exact hL
  funext i
  have hk : i.1 + 1 ≤ n := i.2
  have hpre : U ∈ Atom (p := p) (m := m) (N := N)
      (Fin.take (i.1 + 1) hk (blkFun (p := p) (m := m) (N := N) n U)) :=
    atom_prefix _ hk hmem
  have hbf2 : blkFun (p := p) (m := m) (N := N) (i.1 + 1) U
      = Fin.take (i.1 + 1) hk (blkFun (p := p) (m := m) (N := N) n U) :=
    blkFun_of_mem (p := p) (m := m) hN hpre
  show Z (p := p) (m := m) (N := N) i.1 U = blkFun (p := p) (m := m) (N := N) n U i
  rw [Z, hbf2]
  rfl

end SwarmFB
