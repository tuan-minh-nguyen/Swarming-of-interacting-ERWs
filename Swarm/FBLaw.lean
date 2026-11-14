/-
# The block index law and the `FreshBlocks` packaging

## Hypotheses, named and explicit

* `hN : 0 < N` (at least one walker, used by the selection's uniqueness);
* `hfull` — **the one-step fullness hypothesis**: the mass of the union of the selected blocks
  equals the seed mass, i.e. a.e. seed path carries a selected block.  This is the paper's
  `D < ∞` at one step; it is *not* proved here and is *not* implied by anything above
  (`SwarmSelInd.full_iff_noRegen_null` identifies it with the nullity of the explicit
  no-positive-level-regeneration event, `SwarmSelInd.recursion_summary` records the exact
  defect when it fails).  From it we only derive `selTotal = 1`.
* `h0` — the seed has positive mass (for the actual paper range discharged by
  `SwarmSeed.strictPos_measure_ne_zero`, see `freshBlocks_actual`).

## Conclusions

`freshBlocks` : `KacFormula.FreshBlocks (seedCond) Z Q`, where `Q` is the block index law
`∑ᵢ bm i • δᵢ`.  With it, `KacFormula.prod_initial`, `iid_marginal`, `indep_of_fresh`,
`ident_distrib_of_fresh` and `renewal_block_hypotheses` all apply verbatim to the selected
block indices — in particular the durations `k ↦ (Z k U).1` are pairwise independent and
identically distributed (`renewal_duration_hypotheses`), with the integrability of the duration
as the only extra hypothesis.

`measure_jointZ` is the finite-dimensional law on an *arbitrary* measurable set of block
families; `tsum_blkProd_univ` is the independent consistency check that the family law is a
probability law; `atom_cumulative` connects the block indices to the actual cumulative
`(time, level)` records of the array.

Nothing here proves the invariant record law, `(ED)`, tightness, regeneration or `MainClaim`.
-/
import Swarm.FBCore

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace SwarmFB

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### The block index law as a measure -/

theorem selTotal_eq_tsum : selTotal (p := p) (m := m) (N := N) = ∑' i, bm (p := p) (m := m) (N := N) i :=
  tsum_congr fun i => rfl

/-- The value of the block index law on a measurable set of indices. -/
theorem Q_apply {C : Set (ℕ × ℕ)} (hC : MeasurableSet C) :
    Q (p := p) (m := m) (N := N) C = ∑' j : {j : ℕ × ℕ // j ∈ C}, bm (p := p) (m := m) (N := N) j.1 := by
  rw [Q, Measure.sum_apply _ hC]
  have hterm : ∀ i : ℕ × ℕ,
      (bm (p := p) (m := m) (N := N) i • Measure.dirac i) C
        = C.indicator (fun i => bm (p := p) (m := m) (N := N) i) i := by
    intro i
    rw [Measure.smul_apply, Measure.dirac_apply' _ hC, Set.indicator_apply, smul_eq_mul]
    by_cases hi : i ∈ C
    · simp [hi]
    · simp [hi]
  rw [tsum_congr hterm, ← tsum_subtype C (fun i => bm (p := p) (m := m) (N := N) i)]

/-- The total mass of the block index law is the total selected block mass. -/
theorem Q_univ : Q (p := p) (m := m) (N := N) univ = selTotal (p := p) (m := m) (N := N) := by
  rw [Q_apply MeasurableSet.univ, tsum_subtype univ (fun i => bm (p := p) (m := m) (N := N) i),
    selTotal_eq_tsum]
  simp

/-! ### The one-step hypothesis gives `selTotal = 1` -/

theorem selTotal_eq_one (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    selTotal (p := p) (m := m) (N := N) = 1 :=
  (SwarmSelInd.full_iff_totalMass_one (p := p) (m := m) hN h0
    (measure_ne_top (arrayMeasure N) _)).mp hfull

/-- **The block index law is a probability measure** under the one-step fullness and positive
seed hypotheses: its total mass is `selTotal = 1`. -/
theorem Q_isProbabilityMeasure (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) :=
  ⟨by rw [Q_univ, selTotal_eq_one (p := p) (m := m) hN hfull h0]⟩

/-! ### The atoms under the seed-conditioned measure -/

theorem atom_subset_seedSet {n : ℕ} (L : Fin n → ℕ × ℕ) :
    Atom (p := p) (m := m) (N := N) L ⊆ seedSet (p := p) (m := m) (N := N) := by
  intro U hU
  rw [Atom] at hU
  exact SwarmSelInd.Hidx_subset_seed hU

/-- The mass of a union of atoms: disjointness plus the atom mass. -/
theorem measure_iUnion_atom (hN : 0 < N) {n : ℕ} {C : Set (Fin n → ℕ × ℕ)} :
    (arrayMeasure N) (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ C}, Atom (p := p) (m := m) (N := N) L.1)
      = (∑' L : {L : Fin n → ℕ × ℕ // L ∈ C}, blkProd (p := p) (m := m) (N := N) L.1) *
          (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) := by
  have hdisj : Pairwise (fun a a' : {K : Fin n → ℕ × ℕ // K ∈ C} =>
      Disjoint (Atom (p := p) (m := m) (N := N) a.1)
        (Atom (p := p) (m := m) (N := N) a'.1)) := by
    intro a a' hne
    rw [Set.disjoint_left]
    intro U h1 h2
    exact hne (Subtype.ext (atom_unique (p := p) (m := m) (N := N) hN h1 h2))
  have hmeas : ∀ a : {K : Fin n → ℕ × ℕ // K ∈ C},
      MeasurableSet (Atom (p := p) (m := m) (N := N) a.1) := fun a => measurableSet_atom a.1
  rw [measure_iUnion hdisj hmeas]
  exact (tsum_congr fun (L : {K : Fin n → ℕ × ℕ // K ∈ C}) =>
    atom_mass (p := p) (m := m) (N := N) hN L.1).trans ENNReal.tsum_mul_right

/-- **The block family law under the seed-conditioned measure**: for any set of block families
of length `n`, the mass is the sum of the products of the block masses. -/
theorem seedCond_iUnion_atom (hN : 0 < N)
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0)
    {n : ℕ} {C : Set (Fin n → ℕ × ℕ)} :
    seedCond (p := p) (m := m) (N := N)
        (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ C}, Atom (p := p) (m := m) (N := N) L.1)
      = ∑' L : {L : Fin n → ℕ × ℕ // L ∈ C}, blkProd (p := p) (m := m) (N := N) L.1 := by
  rw [seedCond_apply (p := p) (m := m) (N := N) measurableSet_seedSet]
  rw [show seedSet (p := p) (m := m) (N := N)
        ∩ (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ C}, Atom (p := p) (m := m) (N := N) L.1)
      = (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ C}, Atom (p := p) (m := m) (N := N) L.1) from
    Set.inter_eq_right.mpr (Set.iUnion_subset fun L => atom_subset_seedSet L.1)]
  rw [measure_iUnion_atom (p := p) (m := m) hN]
  rw [mul_comm (∑' L : {L : Fin n → ℕ × ℕ // L ∈ C}, blkProd (p := p) (m := m) (N := N) L.1)
      ((arrayMeasure N) (seedSet (p := p) (m := m) (N := N))), ← mul_assoc,
    ENNReal.inv_mul_cancel h0 (measure_ne_top (arrayMeasure N) _), one_mul]

/-- Under the one-step hypothesis the `n`-chain event has full seed-conditioned mass. -/
theorem seedCond_chain (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (n : ℕ) :
    seedCond (p := p) (m := m) (N := N) (SwarmSelInd.Achain p m N n univ) = 1 := by
  have htot : selTotal (p := p) (m := m) (N := N) = 1 := selTotal_eq_one (p := p) (m := m) hN hfull h0
  rw [seedCond_apply (p := p) (m := m) (N := N) measurableSet_seedSet]
  rw [show seedSet (p := p) (m := m) (N := N) ∩ SwarmSelInd.Achain p m N n univ
      = SwarmSelInd.Achain p m N n univ from
    Set.inter_eq_right.mpr (SwarmSelInd.Achain_subset_seed (p := p) (m := m) n)]
  rw [SwarmSelInd.measure_Achain_of_total (p := p) (m := m) hN htot n]
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top (arrayMeasure N) _)

/-- The complement of the `n`-chain event is null for the seed-conditioned measure: this is
exactly the statement that the default value of `blkFun` never contributes to the law. -/
theorem seedCond_residual (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (n : ℕ) :
    seedCond (p := p) (m := m) (N := N)
      {U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L} = 0 := by
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  have hset : {U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L}
      = (⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L)ᶜ := by
    ext U; simp
  have hmeas : MeasurableSet (SwarmSelInd.Achain p m N n univ) := by
    rw [← show (⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L)
        = SwarmSelInd.Achain p m N n univ from iUnion_atom_eq (p := p) (m := m) (N := N) n]
    exact MeasurableSet.iUnion fun L => measurableSet_atom (p := p) (m := m) (N := N) L
  rw [hset, show (⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L)
      = SwarmSelInd.Achain p m N n univ from iUnion_atom_eq (p := p) (m := m) (N := N) n,
    measure_compl hmeas (measure_ne_top _ _), measure_univ,
    seedCond_chain (p := p) (m := m) hN hfull h0 n, tsub_self]

/-! ### The finite-dimensional law of the block index sequence -/

/-- **The law of the first `n` selected block indices** on an arbitrary measurable set of block
families: the sum of the products of the block masses.  The atoms are measurable and disjoint,
they exhaust the `n`-chain event, and the rest is null for the seed-conditioned measure. -/
theorem measure_jointZ (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (n : ℕ)
    {E : Set (Fin n → ℕ × ℕ)} (hE : MeasurableSet E) :
    seedCond (p := p) (m := m) (N := N) (jointZ (p := p) (m := m) (N := N) n ⁻¹' E)
      = ∑' L : {L : Fin n → ℕ × ℕ // L ∈ E}, blkProd (p := p) (m := m) (N := N) L.1 := by
  have hset : jointZ (p := p) (m := m) (N := N) n ⁻¹' E
      = (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1)
        ∪ ({U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L}
            ∩ jointZ (p := p) (m := m) (N := N) n ⁻¹' E) := by
    ext U
    constructor
    · intro hU
      by_cases hres : ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L
      · obtain ⟨L, hL⟩ := hres
        have hUA : U ∈ SwarmSelInd.Achain p m N n univ := by
          rw [← iUnion_atom_eq (p := p) (m := m) (N := N)]
          exact Set.mem_iUnion.mpr ⟨L, hL⟩
        have hjeq : jointZ (p := p) (m := m) (N := N) n U = L := by
          rw [jointZ_eq_blkFun (p := p) (m := m) hN n hUA,
            blkFun_of_mem (p := p) (m := m) hN hL]
        refine Or.inl (Set.mem_iUnion.mpr ⟨⟨L, ?_⟩, hL⟩)
        rw [← hjeq]
        exact hU
      · exact Or.inr ⟨hres, hU⟩
    · rintro (hU | ⟨-, hU⟩)
      · obtain ⟨⟨L, hLE⟩, hL⟩ := Set.mem_iUnion.mp hU
        have hUA : U ∈ SwarmSelInd.Achain p m N n univ := by
          rw [← iUnion_atom_eq (p := p) (m := m) (N := N)]
          exact Set.mem_iUnion.mpr ⟨L, hL⟩
        have hjeq : jointZ (p := p) (m := m) (N := N) n U = L := by
          rw [jointZ_eq_blkFun (p := p) (m := m) hN n hUA,
            blkFun_of_mem (p := p) (m := m) hN hL]
        show jointZ (p := p) (m := m) (N := N) n U ∈ E
        rw [hjeq]
        exact hLE
      · exact hU
  rw [hset]
  have hnull : seedCond (p := p) (m := m) (N := N)
      {U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L} = 0 :=
    seedCond_residual (p := p) (m := m) hN hfull h0 n
  have hle : seedCond (p := p) (m := m) (N := N)
      ((⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1)
        ∪ ({U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L}
            ∩ jointZ (p := p) (m := m) (N := N) n ⁻¹' E)) ≤
      seedCond (p := p) (m := m) (N := N)
        (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1) := by
    calc seedCond (p := p) (m := m) (N := N)
          ((⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1)
            ∪ ({U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ,
                U ∈ Atom (p := p) (m := m) (N := N) L}
              ∩ jointZ (p := p) (m := m) (N := N) n ⁻¹' E))
        ≤ seedCond (p := p) (m := m) (N := N)
            (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1) +
          seedCond (p := p) (m := m) (N := N)
            ({U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L}
              ∩ jointZ (p := p) (m := m) (N := N) n ⁻¹' E) := measure_union_le _ _
      _ = seedCond (p := p) (m := m) (N := N)
            (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1) + 0 := by
          rw [measure_mono_null (Set.inter_subset_left) hnull]
      _ = _ := add_zero _
  have hEq : seedCond (p := p) (m := m) (N := N)
        ((⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1)
          ∪ ({U : Array N | ¬ ∃ L : Fin n → ℕ × ℕ, U ∈ Atom (p := p) (m := m) (N := N) L}
              ∩ jointZ (p := p) (m := m) (N := N) n ⁻¹' E))
      = seedCond (p := p) (m := m) (N := N)
          (⋃ L : {L : Fin n → ℕ × ℕ // L ∈ E}, Atom (p := p) (m := m) (N := N) L.1) :=
    le_antisymm hle (measure_mono (Set.subset_union_left))
  rw [hEq, seedCond_iUnion_atom (p := p) (m := m) hN h0]

/-- **Consistency**: the length-`n` block index law is a probability law, computed from the
atom sum alone (independently of `Induction.measure_Achain`). -/
theorem tsum_blkProd_univ (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (n : ℕ) :
    (∑' L : Fin n → ℕ × ℕ, blkProd (p := p) (m := m) (N := N) L) = 1 := by
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  have h := measure_jointZ (p := p) (m := m) hN hfull h0 n
    (E := univ) MeasurableSet.univ
  rw [Set.preimage_univ, measure_univ] at h
  rw [h, tsum_subtype univ (fun L => blkProd (p := p) (m := m) (N := N) L)]
  simp

/-! ### The next block: the exact `FreshBlocks` step -/

/-- The joint constraint on the first `n+1` blocks: the first `n` lie in `E`, the last in `C`. -/
def nextSet {n : ℕ} (E : Set (Fin n → ℕ × ℕ)) (C : Set (ℕ × ℕ)) : Set (Fin (n + 1) → ℕ × ℕ) :=
  {K | Fin.init K ∈ E ∧ K (Fin.last n) ∈ C}

theorem measurableSet_nextSet {n : ℕ} {E : Set (Fin n → ℕ × ℕ)} {C : Set (ℕ × ℕ)}
    (hE : MeasurableSet E) (hC : MeasurableSet C) : MeasurableSet (nextSet E C) := by
  have hinit : Measurable (fun K : Fin (n + 1) → ℕ × ℕ => Fin.init K) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (Fin.castSucc i)
  exact (hinit hE).inter (measurable_pi_apply (Fin.last n) hC)

theorem jointZ_succ_preimage {n : ℕ} (E : Set (Fin n → ℕ × ℕ)) (C : Set (ℕ × ℕ)) :
    jointZ (p := p) (m := m) (N := N) (n + 1) ⁻¹' nextSet E C
      = jointZ (p := p) (m := m) (N := N) n ⁻¹' E
        ∩ Z (p := p) (m := m) (N := N) n ⁻¹' C := rfl

/-- The bijection between the first `n+1` blocks and the pair (first `n` blocks, next block). -/
noncomputable def snocEquiv {n : ℕ} (E : Set (Fin n → ℕ × ℕ)) (C : Set (ℕ × ℕ)) :
    {K : Fin (n + 1) → ℕ × ℕ // K ∈ nextSet E C} ≃
      {L : Fin n → ℕ × ℕ // L ∈ E} × {j : ℕ × ℕ // j ∈ C} where
  toFun K := (⟨Fin.init K.1, K.2.1⟩, ⟨K.1 (Fin.last n), K.2.2⟩)
  invFun q := ⟨Fin.snoc (α := fun _ => ℕ × ℕ) q.1.1 q.2.1, by
    refine ⟨?_, ?_⟩
    · simpa [Fin.init_snoc] using q.1.2
    · simpa [Fin.snoc_last] using q.2.2⟩
  left_inv K := by
    refine Subtype.ext ?_
    exact Fin.snoc_init_self (α := fun _ => ℕ × ℕ) K.1
  right_inv q := by
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      exact Fin.init_snoc (α := fun _ => ℕ × ℕ) q.2.1 q.1.1
    · refine Subtype.ext ?_
      exact Fin.snoc_last (α := fun _ => ℕ × ℕ) q.2.1 q.1.1

/-- The product of the block masses splits at the last block. -/
theorem blkProd_snoc {n : ℕ} (L : Fin n → ℕ × ℕ) (j : ℕ × ℕ) :
    blkProd (p := p) (m := m) (N := N) (Fin.snoc (α := fun _ => ℕ × ℕ) L j)
      = blkProd (p := p) (m := m) (N := N) L * bm (p := p) (m := m) (N := N) j := by
  unfold blkProd
  rw [Fin.prod_univ_castSucc (f := fun i : Fin (n + 1) =>
    bm (p := p) (m := m) (N := N) (Fin.snoc (α := fun _ => ℕ × ℕ) L j i))]
  have h1 : (∏ i : Fin n, bm (p := p) (m := m) (N := N)
        ((Fin.snoc (α := fun _ => ℕ × ℕ) L j) i.castSucc))
      = ∏ i : Fin n, bm (p := p) (m := m) (N := N) (L i) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Fin.snoc_castSucc (α := fun _ => ℕ × ℕ)]
  rw [h1, Fin.snoc_last (α := fun _ => ℕ × ℕ)]

/-- A double sum of products of nonnegative terms factorises. -/
theorem tsum_prod_factor {A B : Type*} (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) :
    (∑' q : A × B, f q.1 * g q.2) = (∑' a, f a) * (∑' b, g b) := by
  have h1 : (∑' q : A × B, f q.1 * g q.2) = ∑' a : A, ∑' b : B, f a * g b :=
    ENNReal.tsum_prod (f := fun a b => f a * g b)
  rw [h1]
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

/-- **The next-block sum identity**: summing the products over all `n+1` block families with the
first `n` in `E` and the last in `C` factorises into the past mass times the next-block mass. -/
theorem tsum_blkProd_snoc {n : ℕ} (E : Set (Fin n → ℕ × ℕ)) (C : Set (ℕ × ℕ)) :
    (∑' K : {K : Fin (n + 1) → ℕ × ℕ // K ∈ nextSet E C},
        blkProd (p := p) (m := m) (N := N) K.1)
      = (∑' L : {L : Fin n → ℕ × ℕ // L ∈ E}, blkProd (p := p) (m := m) (N := N) L.1) *
        (∑' j : {j : ℕ × ℕ // j ∈ C}, bm (p := p) (m := m) (N := N) j.1) := by
  have hstep : (∑' q : {L : Fin n → ℕ × ℕ // L ∈ E} × {j : ℕ × ℕ // j ∈ C},
        blkProd (p := p) (m := m) (N := N)
          ((snocEquiv (E := E) (C := C)).symm q).1)
      = ∑' q : {L : Fin n → ℕ × ℕ // L ∈ E} × {j : ℕ × ℕ // j ∈ C},
          blkProd (p := p) (m := m) (N := N) q.1.1 * bm (p := p) (m := m) (N := N) q.2.1 := by
    refine tsum_congr fun q => ?_
    obtain ⟨⟨L, hL⟩, ⟨j, hj⟩⟩ := q
    exact blkProd_snoc L j
  rw [show (∑' K : {K : Fin (n + 1) → ℕ × ℕ // K ∈ nextSet E C},
        blkProd (p := p) (m := m) (N := N) K.1)
      = ∑' q : {L : Fin n → ℕ × ℕ // L ∈ E} × {j : ℕ × ℕ // j ∈ C},
          blkProd (p := p) (m := m) (N := N)
            ((snocEquiv (E := E) (C := C)).symm q).1 from
    (Equiv.tsum_eq (snocEquiv (E := E) (C := C)).symm
      (fun K : {K : Fin (n + 1) → ℕ × ℕ // K ∈ nextSet E C} =>
        blkProd (p := p) (m := m) (N := N) K.1)).symm]
  rw [hstep]
  exact tsum_prod_factor (fun L : {L : Fin n → ℕ × ℕ // L ∈ E} =>
      blkProd (p := p) (m := m) (N := N) L.1)
    (fun j : {j : ℕ × ℕ // j ∈ C} => bm (p := p) (m := m) (N := N) j.1)

/-! ### The main theorem: `FreshBlocks` -/

/-- **The selected block indices are a `FreshBlocks` sequence** under the seed-conditioned array
measure, with block index law `Q`: for every `n`, every measurable set `E` of initial segments
and every measurable set `C` of next block indices,
`P^*(first n blocks ∈ E ∧ block n ∈ C) = P^*(first n blocks ∈ E) · Q C`. -/
theorem freshBlocks (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    KacFormula.FreshBlocks (seedCond (p := p) (m := m) (N := N))
      (Z (p := p) (m := m) (N := N)) (Q (p := p) (m := m) (N := N)) := by
  refine ⟨fun k => measurable_Z (p := p) (m := m) hN k, ?_⟩
  intro n E C hE hC
  have hkey2 : KacFormula.joint (Z (p := p) (m := m) (N := N)) n
      = jointZ (p := p) (m := m) (N := N) n := rfl
  rw [hkey2, ← jointZ_succ_preimage (p := p) (m := m) (N := N) E C,
    measure_jointZ (p := p) (m := m) hN hfull h0 (n + 1)
      (measurableSet_nextSet hE hC),
    measure_jointZ (p := p) (m := m) hN hfull h0 n hE,
    Q_apply (p := p) (m := m) (N := N) hC]
  exact tsum_blkProd_snoc E C

/-- **The finite-prefix product law** in product-cylinder form: the initial block indices are
independent with the block index law `Q`.  This is `RegenIid.prod_initial` instantiated at the
selected blocks of the actual array. -/
theorem measure_prefix_product (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (n : ℕ) (t : ℕ → Set (ℕ × ℕ)) (ht : ∀ i, MeasurableSet (t i)) :
    seedCond (p := p) (m := m) (N := N)
        (⋂ i ∈ Finset.range n, Z (p := p) (m := m) (N := N) i ⁻¹' t i)
      = ∏ i ∈ Finset.range n, Q (p := p) (m := m) (N := N) (t i) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) := Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.prod_initial (freshBlocks (p := p) (m := m) hN hfull h0) t ht n

/-- **The normalised index law**: each block index is distributed as `Q` under `P^*`. -/
theorem map_Z (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (k : ℕ) :
    (seedCond (p := p) (m := m) (N := N)).map (Z (p := p) (m := m) (N := N) k)
      = Q (p := p) (m := m) (N := N) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) := Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.iid_marginal (freshBlocks (p := p) (m := m) hN hfull h0) k

/-- Distinct block indices are independent. -/
theorem indep_of_fresh (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0)
    {i j : ℕ} (hij : i ≠ j) :
    IndepFun (Z (p := p) (m := m) (N := N) i) (Z (p := p) (m := m) (N := N) j)
      (seedCond (p := p) (m := m) (N := N)) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) := Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.indep_of_fresh (freshBlocks (p := p) (m := m) hN hfull h0) hij

/-- Distinct block indices are identically distributed. -/
theorem ident_distrib_of_fresh (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0) (i j : ℕ) :
    IdentDistrib (Z (p := p) (m := m) (N := N) i) (Z (p := p) (m := m) (N := N) j)
      (seedCond (p := p) (m := m) (N := N)) (seedCond (p := p) (m := m) (N := N)) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) := Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.ident_distrib_of_fresh (freshBlocks (p := p) (m := m) hN hfull h0) i j

/-- **The rebased stage**: on the atom of a block family `L : Fin (n+1) → ℕ × ℕ`, the position
path rebased at the first selected block carries the tail of the family.  This is the recursion
of `Induction.Hpath` read on the atoms: each block index is the unique selected block of the
path rebased at the previous one. -/
theorem atom_succ_rebase {n : ℕ} (L : Fin (n + 1) → ℕ × ℕ) {U : Array N}
    (hU : U ∈ Atom (p := p) (m := m) (N := N) L) :
    SwarmChain.pathRel (L 0).1 (blkLevel (L 0)) (SwarmRestart.posPath p m U)
      ∈ SwarmSelInd.Hidx (N := N) (idxList (Fin.tail L)) univ := by
  have hidx : idxList L = ((L 0).1, blkLevel (L 0)) :: idxList (Fin.tail L) := by
    unfold idxList
    rw [List.ofFn_succ]
    rfl
  rw [Atom, hidx] at hU
  exact (SwarmSelInd.mem_Hidx_cons.mp hU).2.2

/-- **The sequence is the atom's family**: on the atom of `L`, the `k`-th selected block index of
the array is exactly `L k`.  Together with `atom_succ_rebase` this says that `Z` is the
deterministic sequence of selected blocks of the recursion: at every rebased stage the next
entry is the unique selected block there. -/
theorem Z_eq_of_mem_atom (hN : 0 < N) {n : ℕ} (L : Fin n → ℕ × ℕ) {U : Array N}
    (hU : U ∈ Atom (p := p) (m := m) (N := N) L) (i : Fin n) :
    Z (p := p) (m := m) (N := N) i.1 U = L i := by
  have hUA : U ∈ SwarmSelInd.Achain p m N n univ := by
    rw [← iUnion_atom_eq (p := p) (m := m) (N := N)]
    exact Set.mem_iUnion.mpr ⟨L, hU⟩
  have h1 : jointZ (p := p) (m := m) (N := N) n U = blkFun (p := p) (m := m) (N := N) n U :=
    jointZ_eq_blkFun (p := p) (m := m) hN n hUA
  have h2 : blkFun (p := p) (m := m) (N := N) n U = L := blkFun_of_mem (p := p) (m := m) hN hU
  calc Z (p := p) (m := m) (N := N) i.1 U = jointZ (p := p) (m := m) (N := N) n U i := rfl
    _ = blkFun (p := p) (m := m) (N := N) n U i := by rw [h1]
    _ = L i := by rw [h2]

/-- **Product law on an arbitrary finite set of block indices** (not necessarily an initial
segment): the corresponding selected blocks are independent with law `Q`. -/
theorem measure_finset_product (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (s : Finset ℕ) (t : ℕ → Set (ℕ × ℕ)) (ht : ∀ i, MeasurableSet (t i)) :
    seedCond (p := p) (m := m) (N := N)
        (⋂ i ∈ s, Z (p := p) (m := m) (N := N) i ⁻¹' t i)
      = ∏ i ∈ s, Q (p := p) (m := m) (N := N) (t i) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) :=
    Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.prod_finset (freshBlocks (p := p) (m := m) hN hfull h0) s t ht

/-! ### Block indices and durations -/

/-- The duration (time increment) of a block: the time coordinate of its index. -/
def blkTime (i : ℕ × ℕ) : ℝ := (i.1 : ℝ)

/-- The distance (level increment) of a block: the level of its index, `g + 1 ≥ 1`. -/
def blkLevelR (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) + 1

theorem measurable_blkTime : Measurable (blkTime) := measurable_of_countable _

theorem measurable_blkLevelR : Measurable (blkLevelR) := measurable_of_countable _

/-- **The block indices are the cumulative simultaneous records of the array**: for any block
family `L`, an array in the atom `L` has a simultaneous record of its position path at the
cumulative `(Σ time, Σ level)` — the blocks tile the horizon with no gap, so the block indices
are exactly the durations/distances of the successive selected blocks. -/
theorem atom_cumulative (hN : 0 < N) {n : ℕ} (L : Fin n → ℕ × ℕ) {U : Array N}
    (hU : U ∈ Atom (p := p) (m := m) (N := N) L) :
    SwarmChain.pathRec (∑ i, (L i).1) (∑ i, blkLevel (L i))
      (SwarmRestart.posPath p m U) := by
  have h := SwarmSelInd.AchainIdx_cumulative (N := N) hN (idxList L) (idxList_pos L)
    (B := univ) hU
  simpa only [idxList, List.map_ofFn, List.sum_ofFn, Function.comp_def] using h

/-- **The block times are the durations of the selected blocks**: on the `n`-chain event, the
position path of the array has a simultaneous record at the cumulative time and level given by
the sums of the block index coordinates.  This is the honest identification of the block index
`(time, level-1)` with the duration and distance of the block; nothing is transported between
unrelated types. -/
theorem cumulative_record (hN : 0 < N) (n : ℕ) {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N n univ) :
    SwarmChain.pathRec (∑ i : Fin n, (blkFun (p := p) (m := m) (N := N) n U i).1)
      (∑ i : Fin n, blkLevel (blkFun (p := p) (m := m) (N := N) n U i))
      (SwarmRestart.posPath p m U) := by
  have hU' : U ∈ ⋃ L : Fin n → ℕ × ℕ, Atom (p := p) (m := m) (N := N) L := by
    rw [iUnion_atom_eq]; exact hU
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  have hbf : blkFun (p := p) (m := m) (N := N) n U = L := blkFun_of_mem (p := p) (m := m) hN hL
  rw [hbf]
  exact atom_cumulative (p := p) (m := m) hN L hL

/-- **The renewal hypotheses for the block durations.**  Given the integrability of the duration
under the block law (a genuine extra input: the mean regeneration time), the durations of the
selected blocks are pairwise independent, identically distributed and integrable — exactly the
`hTindep`/`hTid`/`hTint` hypotheses of `RenewalStrongLaw.renewal_strong_law`. -/
theorem renewal_duration_hypotheses (hN : 0 < N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)))
    (h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (hint : Integrable (blkTime) (Q (p := p) (m := m) (N := N))) :
    (Pairwise fun i j => IndepFun (fun U => blkTime (Z (p := p) (m := m) (N := N) i U))
        (fun U => blkTime (Z (p := p) (m := m) (N := N) j U))
        (seedCond (p := p) (m := m) (N := N))) ∧
      (∀ i, IdentDistrib (fun U => blkTime (Z (p := p) (m := m) (N := N) i U))
        (fun U => blkTime (Z (p := p) (m := m) (N := N) 0 U))
        (seedCond (p := p) (m := m) (N := N)) (seedCond (p := p) (m := m) (N := N))) ∧
      Integrable (fun U => blkTime (Z (p := p) (m := m) (N := N) 0 U))
        (seedCond (p := p) (m := m) (N := N)) := by
  haveI : IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) := Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0
  haveI : IsProbabilityMeasure (seedCond (p := p) (m := m) (N := N)) :=
    seedCond_isProbabilityMeasure (p := p) (m := m) h0
  exact KacFormula.renewal_block_hypotheses (freshBlocks (p := p) (m := m) hN hfull h0)
    (blkTime) measurable_blkTime hint

/-! ### The actual parameter range -/

/-- **The packaging on the paper's parameter range.**  Here the positive seed mass is the
integrated `SeedPos` theorem, so the *only* remaining hypothesis is the one-step fullness
`hfull` (the paper's `D < ∞` at one step); actual recurrence is not assumed anywhere. -/
theorem freshBlocks_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hfull : (arrayMeasure N)
      (⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) (seedSet (p := p) (m := m) (N := N))) :
    selTotal (p := p) (m := m) (N := N) = 1 ∧
      IsProbabilityMeasure (Q (p := p) (m := m) (N := N)) ∧
      KacFormula.FreshBlocks (seedCond (p := p) (m := m) (N := N))
        (Z (p := p) (m := m) (N := N)) (Q (p := p) (m := m) (N := N)) := by
  have hN : 0 < N := by omega
  have h0 : (arrayMeasure N) (seedSet (p := p) (m := m) (N := N)) ≠ 0 := by
    unfold seedSet
    exact SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN2
  exact ⟨selTotal_eq_one (p := p) (m := m) hN hfull h0,
    Q_isProbabilityMeasure (p := p) (m := m) hN hfull h0,
    freshBlocks (p := p) (m := m) hN hfull h0⟩

end SwarmFB
