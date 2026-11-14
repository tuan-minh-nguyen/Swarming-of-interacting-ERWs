/-
# Recursive selected regeneration blocks: the n-fold fresh law and a.s. exhausted chains

## What was open

`areas/kac/SELECTION.md` §"The exact remaining gap" and `areas/kac/CHAIN_FACTOR.md`
§"The exact remaining gap" both record the same missing step:

* `Swarm/Selection.lean` proves, for the actual array measure `arrayMeasure N`, the
  selected-block disjointness, the exhaustion *of one block* (`firstRegen_union`), the
  fresh law of one selected block (`measure_selSet`), its countable summation over the
  selection (`tsum_selMass`) and the two-successive-block product form
  (`tsum_selMass_two`), plus the normalisation `tsum_selMass_eq_one` **under** the
  hypothesis that almost every seed path has a selected block.
* `Swarm/ChainFactor.lean` proves the `k`-fold product **for a fixed index list**.

What is missing in both is the *recursion*: iterating the countable selection sum to
`n` blocks, and the statement that the selection exhausts itself at every stage — i.e.
that the one-step a.s. existence hypothesis is already enough for a.s. chains of
arbitrary length.

## What is proved here (namespace `SwarmSelInd`)

`Hpath n B` is the path-level recursion ("`n` successive selected blocks, then the
fresh tail in `B`"), with `seed = strictPos` the paper's `V`, and `Achain n B` its
image on the array.  Then:

* `measurableSet_Hpath`, `measurableSet_Achain` — measurability of the recursion;
* `Achain_succ_eq_iUnion` — the recursion is exactly one more countable selection sum;
* `measure_Achain_succ`, `measure_Achain` — **the n-fold fresh law**
  `ν(Achain n B) = (∑ᵢ blockMass i)^n · ν{posPath ∈ seed ∩ B}`
  (`ν = arrayMeasure N`); this is the iteration of `Selection.tsum_selMass_eq_iUnion`;
* `Achain_antitone`, `measure_iInter_Achain` — the chain events decrease, so with
  normalisation the intersection has full seed mass;
* `ae_Hpath_all` — **a.s. arbitrarily long selected chains** follow from the *one-step*
  a.s. existence of a selected block (`selTotal = 1`), not from an assumed recursion;
* `full_iff_totalMass_one` — the a.s. one-step existence is *equivalent* to the
  normalisation `∑ᵢ blockMass i = 1`;
* `seed_measure_eq_chain_add_defect` — the **exact defect**, ratio-free:
  `ν(seed) = (∑ᵢ blockMass i)^n · ν(seed) + ν(seed \ Achain n univ)` for every `n`;
  no invented tightness and no `D < ∞` assumed;
* `Hpath_two_records` — the two selected blocks of a chain are literally successive
  simultaneous records of the one array at cumulative `(t, d)`, so consecutive blocks
  share a boundary time and the horizon is tiled with no gap.

## What is *not* claimed (honest remaining inputs)

1. `selTotal = 1` (equivalently `ν(⋃ᵢ selSet i univ) = ν{seed}`, i.e. a.e. seed path has
   a selected block) is **not proved**: that is the paper's `D < ∞` / Kac input, and it is
   a named hypothesis of `ae_Hpath_all`/`ae_Hpath_all_of_full`.
2. The assembly into `RegenIid.FreshBlocks` on a sequence space requires the block
   *contents* as a random element of a measurable space together with the law `Q` of one
   block; the identities here give the finite-dimensional product masses needed for the
   Induction Lemma, but the sequence-space construction and the identification of `Q`
   are not carried out here.
3. No claim about `(ED)`, tightness, `MainClaim`, `Ballistic`, `(locmart)`/`(lococc)`/
   `(locgroup)`, `LeaderRange` or any terminal-window covariance.
-/
import Swarm.Selection
import Swarm.ChainFactor

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal Topology

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SwarmSelInd

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- The paper's seed set of strictly positive re-based futures (`V`). -/
abbrev seed : Set (ℕ → Fin N → ℤ) := SwarmFresh.strictPos

/-! ### The path-level recursion -/

/-- **`n` successive selected blocks followed by the fresh-tail event `B`.**

`Hpath 0 B` is the seed event intersected with `B`; the step adjoins one selected block
`(t,d)` (a `firstRegen` at a positive level) and re-bases at it, requiring the re-based
future to itself carry the remaining `n` selected blocks and the tail `B`.  The seed
conjunct is kept at every stage, so `Hpath n B ⊆ seed` for every `n`. -/
def Hpath : ℕ → Set (ℕ → Fin N → ℤ) → Set (ℕ → Fin N → ℤ)
  | 0, B => seed ∩ B
  | (n + 1), B => seed ∩ ⋃ (t : ℕ), ⋃ (d : {d : ℤ // 1 ≤ d}),
      (SwarmSel.firstRegen t d.1 ∩ SwarmChain.pathRel t d.1 ⁻¹' Hpath n B)

theorem mem_Hpath_zero {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ} :
    X ∈ Hpath (N := N) 0 B ↔ X ∈ seed ∧ X ∈ B := Iff.rfl

theorem mem_Hpath_succ {n : ℕ} {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ} :
    X ∈ Hpath (N := N) (n + 1) B ↔
      X ∈ seed ∧ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ X ∈ SwarmSel.firstRegen t d ∧
        SwarmChain.pathRel t d X ∈ Hpath (N := N) n B := by
  simp only [Hpath, Set.mem_inter_iff, Set.mem_iUnion, Subtype.exists, exists_prop,
    Set.mem_preimage]

theorem Hpath_subset_seed {n : ℕ} {B : Set (ℕ → Fin N → ℤ)} :
    Hpath (N := N) n B ⊆ seed := by
  cases n with
  | zero => exact Set.inter_subset_left
  | succ n => exact Set.inter_subset_left

theorem measurableSet_Hpath : ∀ (n : ℕ) {B : Set (ℕ → Fin N → ℤ)},
    MeasurableSet B → MeasurableSet (Hpath (N := N) n B)
  | 0, B, hB => SwarmFresh.measurableSet_strictPos.inter hB
  | (n + 1), B, hB => SwarmFresh.measurableSet_strictPos.inter
      (MeasurableSet.iUnion fun t : ℕ => MeasurableSet.iUnion fun d : {d : ℤ // 1 ≤ d} =>
        (SwarmSel.measurableSet_firstRegen t d.1).inter
          ((SwarmChain.measurable_pathRel t d.1) (measurableSet_Hpath n hB)))

/-! ### The recursion on the actual array -/

/-- The array-level chain event: the position path carries `n` selected blocks and the tail
`B`. -/
def Achain (p : ℝ) (m : ℕ) (N : ℕ) (n : ℕ) (B : Set (ℕ → Fin N → ℤ)) : Set (Array N) :=
  {U | SwarmRestart.posPath p m U ∈ Hpath (N := N) n B}

theorem Achain_zero (B : Set (ℕ → Fin N → ℤ)) :
    Achain p m N 0 B = {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ B} := rfl

theorem measurableSet_Achain (n : ℕ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (Achain p m N n B) :=
  (SwarmRestart.measurable_posPath p m N) (measurableSet_Hpath n hB)

theorem Achain_subset_seed (n : ℕ) {B : Set (ℕ → Fin N → ℤ)} :
    Achain p m N n B ⊆ {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
  fun _ hU => Hpath_subset_seed hU

/-- Inserting the trivial tail `univ` does not change the seed preimage. -/
theorem seed_preimage_univ :
    {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ univ}
      = {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  ext U
  simp

/-- The block mass of the selection index `(t, g)`, i.e. level `g + 1` at time `t` — the
single summand of `Selection.tsum_selMass`. -/
noncomputable def selMass (p : ℝ) (m : ℕ) (N : ℕ) (i : ℕ × ℕ) : ℝ≥0∞ :=
  (arrayMeasure N) (SwarmSeg.recordPastSet p m i.1 ((i.2 : ℤ) + 1)
    (SwarmSel.selPrefix i.1 ((i.2 : ℤ) + 1)))

/-- The total selected block mass `∑ᵢ selMass i` (a defective law; `= 1` exactly under the
one-step a.s. existence of a selected block, see `full_iff_totalMass_one`). -/
noncomputable def selTotal (p : ℝ) (m : ℕ) (N : ℕ) : ℝ≥0∞ :=
  ∑' i : ℕ × ℕ, selMass p m N i

theorem selTotal_eq_tsum (p : ℝ) (m : ℕ) (N : ℕ) :
    selTotal p m N = ∑' i : ℕ × ℕ, selMass p m N i := rfl

/-- The seed condition is automatic on the chain event, so inserting it into the fresh tail
does not change the event. -/
theorem seed_inter_Hpath (n : ℕ) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ Hpath (N := N) n B}
      = Achain p m N n B := by
  ext U
  simp only [Achain, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h => h.2, fun h => ⟨Hpath_subset_seed h, h⟩⟩

/-- **One more selected block.**  The `(n+1)`-chain event is exactly the countable union of
the selected blocks of `Selection.selSet` over the `n`-chain event as the fresh tail. -/
theorem Achain_succ_eq_iUnion (n : ℕ) (B : Set (ℕ → Fin N → ℤ)) :
    Achain p m N (n + 1) B
      = ⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1)
          (Hpath (N := N) n B) := by
  ext U
  rw [Set.mem_iUnion]
  constructor
  · -- the chain at the array gives one more selected block
    intro hU
    change SwarmRestart.posPath p m U ∈ Hpath (N := N) (n + 1) B at hU
    rw [mem_Hpath_succ] at hU
    obtain ⟨-, t, d, hd, hfr, hr⟩ := hU
    obtain ⟨g, hg⟩ : ∃ g : ℕ, ((g : ℤ) + 1) = d := ⟨(d - 1).toNat, by omega⟩
    refine ⟨(t, g), ?_⟩
    change U ∈ SwarmSel.selSet (p := p) (m := m) t ((g : ℤ) + 1) (Hpath (N := N) n B)
    rw [SwarmSel.selSet_eq_firstRegen_tail, hg]
    exact ⟨hfr, Hpath_subset_seed hr, hr⟩
  · -- one more selected block extends the chain
    rintro ⟨⟨t, g⟩, hU⟩
    change SwarmRestart.posPath p m U ∈ Hpath (N := N) (n + 1) B
    rw [SwarmSel.selSet_eq_firstRegen_tail] at hU
    obtain ⟨hfr, -, hr⟩ := hU
    rw [mem_Hpath_succ]
    exact ⟨SwarmSel.firstRegen_subset_strictPos (fun i => SwarmFresh.posPath_zero p m U i)
      (by omega) hfr, t, (g : ℤ) + 1, by omega, hfr, hr⟩

/-- **The n-fold mass recursion, one step.**  Adjoining one selected block multiplies the
chain mass by the total selected block mass and by nothing else. -/
theorem measure_Achain_succ (hN : 0 < N) (n : ℕ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) (Achain p m N (n + 1) B)
      = selTotal p m N * (arrayMeasure N) (Achain p m N n B) := by
  rw [Achain_succ_eq_iUnion,
    SwarmSel.tsum_selMass_eq_iUnion (p := p) (m := m) hN
      (B := Hpath (N := N) n B) (measurableSet_Hpath n hB),
    seed_inter_Hpath]
  simp only [selTotal, selMass]

/-- **The n-fold fresh law.**  For every `n` and measurable tail `B`, the mass of "`n`
successive selected blocks exist and the fresh tail lies in `B`" is the `n`-th power of the
total selected block mass times the seed mass of `B`. -/
theorem measure_Achain (hN : 0 < N) (n : ℕ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) (Achain p m N n B)
      = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ B} := by
  induction n with
  | zero => simp [Achain, Hpath]
  | succ n ih =>
      rw [measure_Achain_succ (p := p) (m := m) hN n hB, ih, pow_succ', mul_assoc]

/-! ### The chain events decrease: exact defect and a.s. exhaustion -/

theorem Hpath_succ_subset_univ (n : ℕ) :
    Hpath (N := N) (n + 1) univ ⊆ Hpath (N := N) n univ := by
  induction n with
  | zero =>
      intro X hX
      rw [mem_Hpath_zero]
      exact ⟨Hpath_subset_seed hX, Set.mem_univ X⟩
  | succ n ih =>
      intro X hX
      rw [mem_Hpath_succ] at hX ⊢
      obtain ⟨hs, t, d, hd, hfr, hr⟩ := hX
      exact ⟨hs, t, d, hd, hfr, ih hr⟩

theorem Achain_antitone : Antitone (fun n => Achain p m N n univ) := by
  apply antitone_nat_of_succ_le
  intro n
  exact fun U hU => Hpath_succ_subset_univ n hU

theorem Achain_zero_univ :
    Achain p m N 0 univ = {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  rw [Achain_zero, Set.inter_univ]

/-- **Continuity of the chain masses.**  Under the normalisation `∑ᵢ blockMass i = 1` the
intersection of all chain events has the full seed mass: the recursion does not lose mass. -/
theorem measure_iInter_Achain (hN : 0 < N) (htot : selTotal p m N = 1) :
    (arrayMeasure N) (⋂ n, Achain p m N n univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  have hnull : ∀ n : ℕ, NullMeasurableSet (Achain p m N n univ) (arrayMeasure N) :=
    fun n => (measurableSet_Achain n MeasurableSet.univ).nullMeasurableSet
  have htend := tendsto_measure_iInter_atTop (μ := arrayMeasure N)
    (s := fun n => Achain p m N n univ) hnull Achain_antitone
    ⟨0, measure_ne_top (arrayMeasure N) _⟩
  have hconst : ∀ n : ℕ, (arrayMeasure N) (Achain p m N n univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
    intro n
    rw [measure_Achain hN n MeasurableSet.univ, htot, one_pow, one_mul,
      seed_preimage_univ]
  have hlim : Tendsto (fun n => (arrayMeasure N) (Achain p m N n univ)) atTop
      (𝓝 ((arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed})) := by
    have : (fun n => (arrayMeasure N) (Achain p m N n univ))
        = fun _ => (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
      funext hconst
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique htend hlim

/-- **The exact defect, ratio-free.**  For every `n` the seed mass splits into the mass of
the `n`-chain and the mass of the seed paths on which the `n`-th selected block fails.  No
`D < ∞` and no tightness is assumed: the defect is whatever it is. -/
theorem seed_measure_eq_chain_add_defect (hN : 0 < N) (n : ℕ) :
    (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
        + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed}
            \ Achain p m N n univ) := by
  have hsub : Achain p m N n univ ⊆ {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
    Achain_subset_seed n
  have hsplit : (arrayMeasure N)
        ({U : Array N | SwarmRestart.posPath p m U ∈ seed} ∩ Achain p m N n univ)
      + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed}
          \ Achain p m N n univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
    measure_inter_add_sdiff _ (measurableSet_Achain n MeasurableSet.univ)
  have hinter : {U : Array N | SwarmRestart.posPath p m U ∈ seed} ∩ Achain p m N n univ
      = Achain p m N n univ := Set.inter_eq_right.mpr hsub
  rw [hinter] at hsplit
  rw [measure_Achain hN n MeasurableSet.univ, seed_preimage_univ] at hsplit
  exact hsplit.symm

/-- **A.s. arbitrarily long selected chains.**  If a.e. seed path has a selected block
(`selTotal = 1`), then a.e. seed path carries `n` successive selected blocks for *every*
`n` simultaneously.  This is the recursion: only the one-step a.s. existence is assumed. -/
theorem ae_Hpath_all (hN : 0 < N) (htot : selTotal p m N = 1) :
    ∀ᵐ U ∂(arrayMeasure N), SwarmRestart.posPath p m U ∈ seed →
      ∀ n : ℕ, SwarmRestart.posPath p m U ∈ Hpath (N := N) n univ := by
  have hmeas : MeasurableSet (⋂ n, Achain p m N n univ) :=
    MeasurableSet.iInter fun n => measurableSet_Achain n MeasurableSet.univ
  have hzero : (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed}
      \ ⋂ n, Achain p m N n univ) = 0 := by
    have h1 : (arrayMeasure N) (⋂ n, Achain p m N n univ)
        = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
      measure_iInter_Achain (p := p) (m := m) hN htot
    have h2 := measure_sdiff (μ := arrayMeasure N)
      (Set.iInter_subset_of_subset 0 (by rw [Achain_zero_univ])) hmeas.nullMeasurableSet
      (measure_ne_top (arrayMeasure N) _)
    rw [h1, tsub_self] at h2
    exact h2
  refine (ae_iff (μ := arrayMeasure N)).mpr ?_
  refine measure_mono_null ?_ hzero
  intro U hU
  simp only [Set.mem_ofPred_eq, not_forall, Set.mem_sdiff, Set.mem_iInter, Achain] at hU ⊢
  obtain ⟨h1, h2⟩ := hU
  exact ⟨h1, h2⟩

/-! ### The normalisation is exactly one-step a.s. existence -/

theorem full_iff_totalMass_one (hN : 0 < N)
    (h0 : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ 0)
    (htop : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ ⊤) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
    ↔ selTotal p m N = 1 := by
  constructor
  · intro hfull
    exact SwarmSel.tsum_selMass_eq_one (p := p) (m := m) hN hfull h0 htop
  · intro htot
    have hsum : (∑' i : ℕ × ℕ, (arrayMeasure N)
        (SwarmSeg.recordPastSet p m i.1 ((i.2 : ℤ) + 1)
          (SwarmSel.selPrefix i.1 ((i.2 : ℤ) + 1)))) = 1 := by
      simpa only [selTotal, selMass] using htot
    have h := SwarmSel.tsum_selMass_univ (p := p) (m := m) hN
    rw [hsum, one_mul] at h
    exact h.symm

/-- **The one-step hypothesis suffices.**  A.e. existence of a *single* selected block
(`hfull`) already gives a.e. arbitrarily long chains of selected blocks. -/
theorem ae_Hpath_all_of_full (hN : 0 < N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed})
    (h0 : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ 0)
    (htop : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ ⊤) :
    ∀ᵐ U ∂(arrayMeasure N), SwarmRestart.posPath p m U ∈ seed →
      ∀ n : ℕ, SwarmRestart.posPath p m U ∈ Hpath (N := N) n univ :=
  ae_Hpath_all hN ((full_iff_totalMass_one hN h0 htop).mp hfull)

/-- **The total selected mass is at most one**, and the defect is the mass of the seed paths
with no selected block. -/
theorem selTotal_mul_seed_le (hN : 0 < N) :
    selTotal p m N * (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      ≤ (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  have h := SwarmSel.tsum_selMass_mul_le (p := p) (m := m) hN
  simpa only [selTotal, selMass] using h

/-- **Two selected blocks are literally successive simultaneous records of the one array**:
the second block's record sits at the cumulative `(t + s, d + e)`, so consecutive blocks
share a boundary time and the horizon up to the last record is tiled without a gap. -/
theorem Hpath_two_records {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ}
    (hX : X ∈ Hpath (N := N) 2 B) :
    ∃ (t : ℕ) (d : ℤ) (s : ℕ) (e : ℤ), 1 ≤ d ∧ 1 ≤ e ∧ SwarmChain.pathRec t d X ∧
      SwarmChain.pathRec (t + s) (d + e) X ∧
      SwarmChain.pathRel (t + s) (d + e) X ∈ Hpath (N := N) 0 B := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, mem_Hpath_succ] at hX
  obtain ⟨-, t, d, hd, hfr, hr⟩ := hX
  rw [mem_Hpath_succ] at hr
  obtain ⟨-, s, e, he, hfr', hr'⟩ := hr
  have hrec : SwarmChain.pathRec t d X := (SwarmSel.mem_firstRegen_iff.mp hfr).2.1
  have hrec' : SwarmChain.pathRec s e (SwarmChain.pathRel t d X) :=
    (SwarmSel.mem_firstRegen_iff.mp hfr').2.1
  have he0 : (0 : ℤ) ≤ e := by omega
  refine ⟨t, d, s, e, hd, he, hrec, ?_, ?_⟩
  · exact (SwarmChain.pathRec_pathRel t s d e X he0 hrec).mp hrec'
  · rw [← SwarmChain.pathRel_pathRel]
    exact hr'

/-! ### Specified index lists: the block-index law and the cumulative record

`measure_Achain` sums the block indices out at every stage.  The complementary statement —
the mass of the chain carrying a *specified* list of selected blocks — is what makes the
block-index process an i.i.d. sequence with law `Q = blockMass / selTotal`; neither
`Swarm/ChainFactor.lean` (bare records, no selection) nor `Swarm/Selection.lean`
(`n ≤ 2`) provides it for the *selected* blocks at every `n`. -/

/-- The block mass at level `d` at time `t`, indexed by the level itself. -/
noncomputable def blockMassAt (p : ℝ) (m : ℕ) (N : ℕ) (t : ℕ) (d : ℤ) : ℝ≥0∞ :=
  (arrayMeasure N) (SwarmSeg.recordPastSet p m t d (SwarmSel.selPrefix t d))

theorem selMass_eq_blockMassAt (i : ℕ × ℕ) :
    selMass p m N i = blockMassAt p m N i.1 ((i.2 : ℤ) + 1) := rfl

/-- The chain carrying a *specified* list of selected blocks, then the fresh tail `B`. -/
def Hidx : List (ℕ × ℤ) → Set (ℕ → Fin N → ℤ) → Set (ℕ → Fin N → ℤ)
  | [], B => seed ∩ B
  | (t, d) :: rest, B =>
      seed ∩ (SwarmSel.firstRegen t d ∩ SwarmChain.pathRel t d ⁻¹' Hidx rest B)

theorem mem_Hidx_nil {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ} :
    X ∈ Hidx (N := N) [] B ↔ X ∈ seed ∧ X ∈ B := Iff.rfl

theorem mem_Hidx_cons {t : ℕ} {d : ℤ} {rest : List (ℕ × ℤ)}
    {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ} :
    X ∈ Hidx (N := N) ((t, d) :: rest) B ↔
      X ∈ seed ∧ X ∈ SwarmSel.firstRegen t d ∧ SwarmChain.pathRel t d X ∈ Hidx (N := N) rest B := by
  simp only [Hidx, Set.mem_inter_iff, Set.mem_preimage]

theorem Hidx_subset_seed {L : List (ℕ × ℤ)} {B : Set (ℕ → Fin N → ℤ)} :
    Hidx (N := N) L B ⊆ seed := by
  cases L with
  | nil => intro X hX; exact hX.1
  | cons p rest =>
      obtain ⟨t, d⟩ := p
      intro X hX
      exact (mem_Hidx_cons.mp hX).1

theorem measurableSet_Hidx : ∀ (L : List (ℕ × ℤ)) {B : Set (ℕ → Fin N → ℤ)},
    MeasurableSet B → MeasurableSet (Hidx (N := N) L B)
  | [], B, hB => SwarmFresh.measurableSet_strictPos.inter hB
  | (t, d) :: rest, B, hB => SwarmFresh.measurableSet_strictPos.inter
      ((SwarmSel.measurableSet_firstRegen t d).inter
        ((SwarmChain.measurable_pathRel t d) (measurableSet_Hidx rest hB)))

/-- The array-level specified-index chain event. -/
def AchainIdx (p : ℝ) (m : ℕ) (N : ℕ) (L : List (ℕ × ℤ))
    (B : Set (ℕ → Fin N → ℤ)) : Set (Array N) :=
  {U | SwarmRestart.posPath p m U ∈ Hidx (N := N) L B}

theorem measurableSet_AchainIdx (L : List (ℕ × ℤ)) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) : MeasurableSet (AchainIdx p m N L B) :=
  (SwarmRestart.measurable_posPath p m N) (measurableSet_Hidx L hB)

/-- One specified block on top of a specified chain is exactly the selected-block event
`Selection.selSet` with the rest of the chain as the fresh tail. -/
theorem AchainIdx_cons_eq_selSet (t : ℕ) (d : ℤ) (hd : 1 ≤ d) (L : List (ℕ × ℤ))
    (B : Set (ℕ → Fin N → ℤ)) :
    AchainIdx p m N ((t, d) :: L) B
      = SwarmSel.selSet (p := p) (m := m) t d (Hidx (N := N) L B) := by
  ext U
  change SwarmRestart.posPath p m U ∈ Hidx (N := N) ((t, d) :: L) B ↔
    U ∈ SwarmSel.selSet (p := p) (m := m) t d (Hidx (N := N) L B)
  rw [mem_Hidx_cons, SwarmSel.selSet_eq_firstRegen_tail]
  constructor
  · rintro ⟨-, hfr, htail⟩
    exact ⟨hfr, Hidx_subset_seed htail, htail⟩
  · rintro ⟨hfr, -, htail⟩
    exact ⟨SwarmSel.firstRegen_subset_strictPos (fun i => SwarmFresh.posPath_zero p m U i) hd hfr,
      hfr, htail⟩

/-- **The block-index law.**  For a specified list `L` of positive-level blocks and a
measurable fresh tail `B`, the mass of the selected chain at exactly `L` is the product of the
block masses times the seed mass of the tail: the successive selected blocks are independent
with the same block law, at every `n` and for the *selected* blocks. -/
theorem measure_AchainIdx (hN : 0 < N) : ∀ (L : List (ℕ × ℤ)), (∀ q ∈ L, 1 ≤ q.2) →
    ∀ {B : Set (ℕ → Fin N → ℤ)}, MeasurableSet B →
      (arrayMeasure N) (AchainIdx p m N L B)
        = (L.map (fun q => blockMassAt p m N q.1 q.2)).prod *
            (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ B}
  | [], _, B, _ => by
      simp only [AchainIdx, Hidx, List.map_nil, List.prod_nil, one_mul]
  | (t, d) :: rest, hL, B, hB => by
      have hd : 1 ≤ d := hL (t, d) (by simp)
      have hL' : ∀ q ∈ rest, 1 ≤ q.2 := fun q hq => hL q (by simp [hq])
      have hrest := measure_AchainIdx hN rest hL' (B := B) hB
      rw [AchainIdx_cons_eq_selSet t d hd rest B,
        SwarmSel.measure_selSet (p := p) (m := m) t d (measurableSet_Hidx rest hB)]
      have hseed : {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ Hidx (N := N) rest B}
          = AchainIdx p m N rest B := by
        ext U
        simp only [AchainIdx, Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact ⟨fun h => h.2, fun h => ⟨Hidx_subset_seed h, h⟩⟩
      rw [hseed, hrest, List.map_cons, List.prod_cons, mul_assoc]
      simp only [blockMassAt]

/-- A list of positive levels has nonnegative level sum. -/
theorem list_sum_level_nonneg {L : List (ℕ × ℤ)} (hL : ∀ q ∈ L, 1 ≤ q.2) :
    (0 : ℤ) ≤ (L.map (fun q => q.2)).sum := by
  induction L with
  | nil => simp
  | cons q rest ih =>
      rw [List.map_cons, List.sum_cons]
      have h1 : 1 ≤ q.2 := hL q (by simp)
      have h2 : ∀ r ∈ rest, 1 ≤ r.2 := fun r hr => hL r (by simp [hr])
      have := ih h2
      omega

/-- **Successive selected blocks are successive records of the one array.**  A specified chain
of `n` selected blocks in the re-based coordinates is a simultaneous record of the array at the
cumulative time and cumulative level: the `(k+1)`-th block starts exactly at the time the
`k`-th block ends, so the blocks tile the horizon `[0, τ_n]` with no gap. -/
theorem AchainIdx_cumulative (hN : 0 < N) : ∀ (L : List (ℕ × ℤ)), (∀ q ∈ L, 1 ≤ q.2) →
    ∀ {B : Set (ℕ → Fin N → ℤ)} {X : ℕ → Fin N → ℤ}, X ∈ Hidx (N := N) L B →
      SwarmChain.pathRec (L.map (fun q => q.1)).sum (L.map (fun q => q.2)).sum X
  | [], _, B, X, hX => by
      rw [mem_Hidx_nil] at hX
      have h0 : ∀ i, X 0 i = 0 := (SwarmFresh.mem_strictPos.mp hX.1).1
      simp only [List.map_nil, List.sum_nil]
      exact ⟨fun s hs => absurd hs (Nat.not_lt_zero s), h0⟩
  | (t, d) :: rest, hL, B, X, hX => by
      rw [mem_Hidx_cons] at hX
      obtain ⟨-, hfr, htail⟩ := hX
      have hd : 1 ≤ d := hL (t, d) (by simp)
      have hL' : ∀ q ∈ rest, 1 ≤ q.2 := fun q hq => hL q (by simp [hq])
      have hrec : SwarmChain.pathRec t d X := (SwarmSel.mem_firstRegen_iff.mp hfr).2.1
      have ih := AchainIdx_cumulative hN rest hL' htail
      have hnonneg : (0 : ℤ) ≤ (rest.map (fun q => q.2)).sum := list_sum_level_nonneg hL'
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      exact (SwarmChain.pathRec_pathRel t (rest.map (fun q => q.1)).sum d
        (rest.map (fun q => q.2)).sum X hnonneg hrec).mp ih


/-! ### The selected block is well defined: uniqueness of the selection index -/

/-- **At most one selected block on a path.**  Two selected blocks of one path at positive
levels coincide, so the selection index is a deterministic function of the path. -/
theorem firstRegen_unique (hN : 0 < N) {X : ℕ → Fin N → ℤ} {t t' : ℕ} {d d' : ℤ}
    (hd : 1 ≤ d) (hd' : 1 ≤ d') (h : X ∈ SwarmSel.firstRegen t d)
    (h' : X ∈ SwarmSel.firstRegen t' d') : (t, d) = (t', d') := by
  by_contra hne
  exact Set.disjoint_left.mp (SwarmSel.firstRegen_disjoint hN hd hd' hne) h h'

/-- **The block map is well defined.**  On an `(n+1)`-chain event there is a *unique* selected
block index carrying the first block and the `n`-chain tail; this is the recursion step that
lets the block sequence be iterated as a deterministic function of the array. -/
theorem exists_unique_selected_block (hN : 0 < N) {n : ℕ} {X : ℕ → Fin N → ℤ}
    (hX : X ∈ Hpath (N := N) (n + 1) univ) :
    ∃! p : {p : ℕ × ℤ // 1 ≤ p.2}, X ∈ SwarmSel.firstRegen p.1.1 p.1.2 ∧
      SwarmChain.pathRel p.1.1 p.1.2 X ∈ Hpath (N := N) n univ := by
  obtain ⟨-, t, d, hd, hfr, hr⟩ := mem_Hpath_succ.mp hX
  refine ⟨⟨(t, d), hd⟩, ⟨hfr, hr⟩, ?_⟩
  rintro ⟨⟨t', d'⟩, hd'⟩ ⟨hfr', hr'⟩
  exact Subtype.ext (firstRegen_unique (t := t) (t' := t') (d := d) (d' := d') hN hd hd' hfr hfr').symm

/-! ### The one-step hypothesis in a.e. form, and the normalised chain mass -/

/-- **The a.s. form of the one-step hypothesis.**  `ν(⋃ selSet) = ν(seed)` says exactly that
a.e. seed path has a selected block — the paper's `D < ∞` at one step. -/
theorem full_iff_ae_exists (hN : 0 < N) :
    ((arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed})
    ↔ ∀ᵐ U ∂(arrayMeasure N), SwarmRestart.posPath p m U ∈ seed →
        ∃ i : ℕ × ℕ,
          U ∈ SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ := by
  set Sel : Set (Array N) := ⋃ i : ℕ × ℕ,
    SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ with hSel
  have hmeas : MeasurableSet Sel :=
    MeasurableSet.iUnion fun i => SwarmSel.measurableSet_selSet i.1 _ MeasurableSet.univ
  have hsub : Sel ⊆ {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
    SwarmSel.iUnion_selSet_subset univ
  have hset : {U : Array N | ¬ (SwarmRestart.posPath p m U ∈ seed → ∃ i : ℕ × ℕ,
        U ∈ SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)}
      = {U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Sel := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_iUnion, Classical.not_imp,
      not_exists, hSel]
  constructor
  · intro hfull
    rw [ae_iff, hset]
    have h1 := measure_sdiff (μ := arrayMeasure N) hsub hmeas.nullMeasurableSet
      (measure_ne_top (arrayMeasure N) _)
    rw [hfull, tsub_self] at h1
    exact h1
  · intro hae
    rw [ae_iff, hset] at hae
    have hsplit : (arrayMeasure N)
          ({U : Array N | SwarmRestart.posPath p m U ∈ seed} ∩ Sel)
        + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Sel)
        = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
      measure_inter_add_sdiff _ hmeas
    rw [Set.inter_eq_right.mpr hsub, hae, add_zero] at hsplit
    exact hsplit

/-- Under the normalisation every `n`-chain has the full seed mass. -/
theorem measure_Achain_of_total (hN : 0 < N) (htot : selTotal p m N = 1) (n : ℕ) :
    (arrayMeasure N) (Achain p m N n univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  rw [measure_Achain hN n MeasurableSet.univ, htot, one_pow, one_mul, seed_preimage_univ]


/-! ### Disjointness of different index lists: the block-index process is well defined -/

/-- **Two chains on one path are prefix-comparable.**  Because the first selected block is
unique (`firstRegen_unique`), two specified selected chains of one path must agree block by
block until one of them runs out. -/
theorem Hidx_prefix_or (hN : 0 < N) : ∀ (L : List (ℕ × ℤ)), (∀ q ∈ L, 1 ≤ q.2) →
    ∀ {L' : List (ℕ × ℤ)}, (∀ q ∈ L', 1 ≤ q.2) → ∀ {B B' : Set (ℕ → Fin N → ℤ)}
      {X : ℕ → Fin N → ℤ}, X ∈ Hidx (N := N) L B → X ∈ Hidx (N := N) L' B' →
      L <+: L' ∨ L' <+: L
  | [], _, L', _, B, B', X, _, _ => Or.inl List.nil_prefix
  | (t, d) :: rest, hL, L', hL', B, B', X, h, h' => by
      cases L' with
      | nil => exact Or.inr List.nil_prefix
      | cons p rest' =>
          obtain ⟨t', d'⟩ := p
          rw [mem_Hidx_cons] at h h'
          obtain ⟨-, hfr, htail⟩ := h
          obtain ⟨-, hfr', htail'⟩ := h'
          have hd : 1 ≤ d := hL (t, d) (by simp)
          have hd' : 1 ≤ d' := hL' (t', d') (by simp)
          have hp : (t, d) = (t', d') :=
            firstRegen_unique (t := t) (t' := t') (d := d) (d' := d') hN hd hd' hfr hfr'
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hp
          have hrest : ∀ q ∈ rest, 1 ≤ q.2 := fun q hq => hL q (by simp [hq])
          have hrest' : ∀ q ∈ rest', 1 ≤ q.2 := fun q hq => hL' q (by simp [hq])
          rcases Hidx_prefix_or hN rest hrest hrest' htail htail' with h1 | h1
          · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)
          · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)

/-- **Different index lists of the same length cannot both occur.**  Two specified selected
chains of equal length on one array are either the same list or mutually exclusive. -/
theorem AchainIdx_disjoint (hN : 0 < N) {L L' : List (ℕ × ℤ)}
    (hL : ∀ q ∈ L, 1 ≤ q.2) (hL' : ∀ q ∈ L', 1 ≤ q.2) (hlen : L.length = L'.length)
    (hne : L ≠ L') (B B' : Set (ℕ → Fin N → ℤ)) :
    Disjoint (AchainIdx p m N L B) (AchainIdx p m N L' B') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  have hp := Hidx_prefix_or (N := N) hN L hL hL' h1 h2
  rcases hp with hp | hp
  · exact hne (hp.eq_of_length hlen)
  · exact hne (hp.eq_of_length hlen.symm).symm

/-- **The block-index law.**  For a specified list of positive-level blocks the mass of the
chain is the product of the block masses times the seed mass: the successive selected blocks are
independent with the same (defective) block law. -/
theorem measure_AchainIdx_univ (hN : 0 < N) (L : List (ℕ × ℤ))
    (hL : ∀ q ∈ L, 1 ≤ q.2) :
    (arrayMeasure N) (AchainIdx p m N L univ)
      = (L.map (fun q => blockMassAt p m N q.1 q.2)).prod *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  rw [measure_AchainIdx (p := p) (m := m) hN L hL MeasurableSet.univ, seed_preimage_univ]

/-- **Two successive specified selected blocks.**  The concrete two-block instance of the
block-index law, with the two block masses and the seed mass. -/
theorem measure_two_selected_blocks (hN : 0 < N) (t : ℕ) (d : ℤ) (s : ℕ) (e : ℤ)
    (hd : 1 ≤ d) (he : 1 ≤ e) :
    (arrayMeasure N) (AchainIdx p m N [(t, d), (s, e)] univ)
      = blockMassAt p m N t d * blockMassAt p m N s e *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  rw [measure_AchainIdx_univ (p := p) (m := m) hN [(t, d), (s, e)]
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> assumption)]
  simp [mul_assoc]


/-! ### The exact event on which the selection stops

The defect of the recursion has an exact description: a seed path fails to have a selected block
iff it never returns to any positive level from which it stays strictly above.  This is the
paper's `D = ∞` event at the first stage, and it is *not* assumed to be null. -/

/-- The selected-block event is monotone in the fresh tail. -/
theorem selSet_mono {B₁ B₂ : Set (ℕ → Fin N → ℤ)} (h : B₁ ⊆ B₂) (t : ℕ) (d : ℤ) :
    SwarmSel.selSet (p := p) (m := m) t d B₁ ⊆ SwarmSel.selSet (p := p) (m := m) t d B₂ := by
  intro U hU
  exact ⟨hU.1, hU.2.1, h hU.2.2⟩

/-- The first-stage chain event is exactly the union of the selected blocks. -/
theorem Achain_one_eq_iUnion :
    Achain p m N 1 univ
      = ⋃ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ := by
  rw [Achain_succ_eq_iUnion 0 univ]
  have h : ∀ i : ℕ × ℕ, SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1)
        (Hpath (N := N) 0 univ)
      = SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ := by
    intro i
    ext U
    simp only [SwarmSel.selSet, Set.mem_ofPred_eq, Hpath, Set.mem_inter_iff, Set.mem_univ,
      and_true]
    tauto
  simp only [h]

/-- **The exact stopping event.**  A seed path has no selected block iff it has no regeneration
at a positive level at all. -/
theorem seed_diff_chain_one_eq_noRegen (hN : 0 < N) :
    {U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Achain p m N 1 univ
      = {U : Array N | SwarmRestart.posPath p m U ∈ seed ∧
          ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d (SwarmRestart.posPath p m U)} := by
  ext U
  simp only [Achain, Set.mem_sdiff, Set.mem_ofPred_eq, mem_Hpath_succ]
  constructor
  · rintro ⟨hs, hnot⟩
    refine ⟨hs, ?_⟩
    rintro ⟨t, d, hd, hreg⟩
    obtain ⟨t', d', hd', hfr⟩ := SwarmSel.exists_firstRegen hN hs hd hreg
    have hrel : SwarmChain.pathRel t' d' (SwarmRestart.posPath p m U) ∈ seed :=
      ((SwarmSel.isRegen_iff_relFuture t' d' (SwarmRestart.posPath p m U)).mp
        (SwarmSel.mem_firstRegen_iff.mp hfr).2).2
    exact hnot ⟨hs, t', d', hd', hfr, hrel, Set.mem_univ _⟩
  · rintro ⟨hs, hnot⟩
    refine ⟨hs, ?_⟩
    rintro ⟨-, t, d, hd, hfr, -⟩
    exact hnot ⟨t, d, hd, (SwarmSel.mem_firstRegen_iff.mp hfr).2⟩

/-- **The one-step a.s. existence in exact-event form.**  The hypothesis that a.e. seed path has
a selected block is exactly the statement that the explicit "no positive-level regeneration"
event is null. -/
theorem full_iff_noRegen_null (hN : 0 < N) :
    ((arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed})
    ↔ (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed ∧
          ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d (SwarmRestart.posPath p m U)} = 0 := by
  set Sel : Set (Array N) := ⋃ i : ℕ × ℕ,
    SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ with hSel
  have hsub : Sel ⊆ {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
    SwarmSel.iUnion_selSet_subset univ
  have hmeas : MeasurableSet Sel :=
    MeasurableSet.iUnion
      (fun i : ℕ × ℕ =>
        SwarmSel.measurableSet_selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1)
          MeasurableSet.univ)
  have hkey : {U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Achain p m N 1 univ
      = {U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Sel := by
    rw [Achain_one_eq_iUnion, hSel]
  have e1 : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed ∧
        ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d (SwarmRestart.posPath p m U)}
      = (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Sel) := by
    rw [← seed_diff_chain_one_eq_noRegen (p := p) (m := m) hN, hkey]
  rw [hSel, e1]
  constructor
  · intro hfull
    have h1 := measure_sdiff (μ := arrayMeasure N) hsub hmeas.nullMeasurableSet
      (measure_ne_top (arrayMeasure N) _)
    rw [hfull, tsub_self] at h1
    exact h1
  · intro hzero
    have hsplit : (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed} ∩ Sel)
        + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed} \ Sel)
        = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
      measure_inter_add_sdiff _ hmeas
    rw [Set.inter_eq_right.mpr hsub, hzero, add_zero] at hsplit
    exact hsplit

/-! ### The next block is independent of the past: the `FreshBlocks` step -/

/-- **The next selected block's law does not depend on the past.**  For every specification `L`
of the first selected blocks and every positive-level next block `j`, the mass of the longer
chain is the mass of the shorter one times the block mass of `j`: the ratio-free form of
"conditionally on the past, the next block has law `blockMass`" — `RegenIid.FreshBlocks` with
the block index as the block content. -/
theorem next_block_law (hN : 0 < N) (L : List (ℕ × ℤ)) (hL : ∀ q ∈ L, 1 ≤ q.2)
    (j : ℕ × ℤ) (hj : 1 ≤ j.2) :
    (arrayMeasure N) (AchainIdx p m N (L ++ [j]) univ)
      = (arrayMeasure N) (AchainIdx p m N L univ) * blockMassAt p m N j.1 j.2 := by
  have hLj : ∀ q ∈ L ++ [j], 1 ≤ q.2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hL q hq
    · simp only [List.mem_singleton] at hq
      subst hq
      exact hj
  rw [measure_AchainIdx_univ (p := p) (m := m) hN (L ++ [j]) hLj,
    measure_AchainIdx_univ (p := p) (m := m) hN L hL, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil]
  ring

/-- **The fresh tail is independent of the past.**  Ratio-free: for every specification `L` of
the first blocks and every measurable fresh tail `B`, the joint mass times the seed mass equals
the product of the marginal masses — the tail law equals the seed law whatever the past is. -/
theorem tail_independent_of_past (hN : 0 < N) (L : List (ℕ × ℤ))
    (hL : ∀ q ∈ L, 1 ≤ q.2) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (AchainIdx p m N L B) *
        (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = (arrayMeasure N) (AchainIdx p m N L univ) *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed ∩ B} := by
  rw [measure_AchainIdx_univ (p := p) (m := m) hN L hL,
    measure_AchainIdx (p := p) (m := m) hN L hL hB]
  ring


/-! ### The next block's law with an arbitrary measurable set of indices -/

/-- The block-mass measure on the index space: `Qblock C = ∑_{j ∈ C, j positive} blockMass j`.
Under the normalisation `selTotal = 1` this is a probability law on the selected block indices. -/
noncomputable def Qblock (p : ℝ) (m : ℕ) (N : ℕ) (C : Set (ℕ × ℤ)) : ℝ≥0∞ :=
  ∑' j : {j : ℕ × ℤ // 1 ≤ j.2 ∧ j ∈ C}, blockMassAt p m N j.1.1 j.1.2

/-- **The next block has law `Qblock` whatever the past is.**  For every specification `L` of the
first selected blocks and every set `C` of possible next indices,
`ν(past = L ∧ next ∈ C) = ν(past = L) · Qblock C`: the ratio-free `FreshBlocks` step with an
arbitrary (not merely one-point) set of next block indices. -/
theorem next_block_measure (hN : 0 < N) (L : List (ℕ × ℤ)) (hL : ∀ q ∈ L, 1 ≤ q.2)
    (C : Set (ℕ × ℤ)) :
    (arrayMeasure N) (⋃ j : {j : ℕ × ℤ // 1 ≤ j.2 ∧ j ∈ C},
        AchainIdx p m N (L ++ [j.1]) univ)
      = (arrayMeasure N) (AchainIdx p m N L univ) * Qblock p m N C := by
  have hdisj : Pairwise (fun j j' : {j : ℕ × ℤ // 1 ≤ j.2 ∧ j ∈ C} =>
      Disjoint (AchainIdx p m N (L ++ [j.1]) univ) (AchainIdx p m N (L ++ [j'.1]) univ)) := by
    intro j j' hne
    refine AchainIdx_disjoint (p := p) (m := m) hN ?_ ?_ ?_ ?_ _ _
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hL q hq
      · simp only [List.mem_singleton] at hq; subst hq; exact j.2.1
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hL q hq
      · simp only [List.mem_singleton] at hq; subst hq; exact j'.2.1
    · rw [List.length_append, List.length_append]; simp
    · intro h
      refine hne (Subtype.ext ?_)
      have := List.append_cancel_left h
      simpa using this
  have hmeas : ∀ j : {j : ℕ × ℤ // 1 ≤ j.2 ∧ j ∈ C},
      MeasurableSet (AchainIdx p m N (L ++ [j.1]) univ) := fun j =>
    measurableSet_AchainIdx _ MeasurableSet.univ
  rw [Qblock, ← ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
  exact tsum_congr (fun j => next_block_law (p := p) (m := m) hN L hL j.1 j.2.1)


/-! ### Summary: one-step a.s. existence is enough -/

/-- **The recursion, packaged.**  From the *one-step* a.s. existence of a selected block (the
paper's `D < ∞` at one step, in the exact form `hfull`) on the actual array measure:

1. the total selected block mass is exactly `1` (the normalised block mass is a probability law);
2. every `n`-chain has the full seed mass, so no mass is lost by the recursion;
3. a.e. seed path carries `n` successive selected blocks for every `n` simultaneously;
4. and unconditionally (for every `n`) the seed mass splits into the `n`-chain mass and the
   explicit defect.

No further hypothesis (no `D < ∞` for later blocks, no independence postulate, no tightness) is
used. -/
theorem recursion_summary (hN : 0 < N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed})
    (h0 : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ 0)
    (htop : (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} ≠ ⊤) :
    selTotal p m N = 1 ∧
    (∀ n : ℕ, (arrayMeasure N) (Achain p m N n univ)
        = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}) ∧
    (∀ᵐ U ∂(arrayMeasure N), SwarmRestart.posPath p m U ∈ seed →
        ∀ n : ℕ, SwarmRestart.posPath p m U ∈ Hpath (N := N) n univ) ∧
    (∀ n : ℕ, (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
        + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed}
            \ Achain p m N n univ)) := by
  have htot : selTotal p m N = 1 := (full_iff_totalMass_one (p := p) (m := m) hN h0 htop).mp hfull
  exact ⟨htot, fun n => measure_Achain_of_total (p := p) (m := m) hN htot n,
    ae_Hpath_all_of_full (p := p) (m := m) hN hfull h0 htop,
    fun n => seed_measure_eq_chain_add_defect (p := p) (m := m) hN n⟩


/-- **The recursion on the paper's parameter range.**  Here the seed positivity is discharged by
the integrated `areas/kac/SeedPos.strictPos_measure_ne_zero`, so the *only* remaining hypothesis
is the one-step a.s. existence `hfull` (the paper's `D < ∞` at one step). -/
theorem recursion_summary_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN2 : 2 ≤ N)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}) :
    selTotal p m N = 1 ∧
    (∀ n : ℕ, (arrayMeasure N) (Achain p m N n univ)
        = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}) ∧
    (∀ᵐ U ∂(arrayMeasure N), SwarmRestart.posPath p m U ∈ seed →
        ∀ n : ℕ, SwarmRestart.posPath p m U ∈ Hpath (N := N) n univ) ∧
    (∀ n : ℕ, (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
        + (arrayMeasure N) ({U : Array N | SwarmRestart.posPath p m U ∈ seed}
            \ Achain p m N n univ)) :=
  recursion_summary (p := p) (m := m) (by omega) hfull
    (SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN2)
    (measure_ne_top (arrayMeasure N) _)


/-! ### An arbitrary set of index lists

The last finite-dimensional ingredient of `RegenIid.FreshBlocks`: the block-index atoms over an
arbitrary set of length-`n` index lists carry the product of the block masses, so the law of the
first `n` block indices is the product law. -/

/-- **The product law over an arbitrary set of length-`n` index lists.**  For any set `C` of
positive-level index lists of length `n`, the mass of the corresponding union of chain atoms is
the sum of the products of the block masses; the atoms are pairwise disjoint because two
different index lists of one length cannot both occur on one array. -/
theorem measure_index_atoms (hN : 0 < N) (n : ℕ) (C : Set (List (ℕ × ℤ))) :
    (arrayMeasure N)
        (⋃ L : {L : List (ℕ × ℤ) // L.length = n ∧ (∀ q ∈ L, 1 ≤ q.2) ∧ L ∈ C},
          AchainIdx p m N L.1 univ)
      = ∑' L : {L : List (ℕ × ℤ) // L.length = n ∧ (∀ q ∈ L, 1 ≤ q.2) ∧ L ∈ C},
          (L.1.map (fun q => blockMassAt p m N q.1 q.2)).prod *
            (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  have hdisj : Pairwise (fun L L' :
      {L : List (ℕ × ℤ) // L.length = n ∧ (∀ q ∈ L, 1 ≤ q.2) ∧ L ∈ C} =>
      Disjoint (AchainIdx p m N L.1 univ) (AchainIdx p m N L'.1 univ)) := by
    intro L L' hne
    exact AchainIdx_disjoint (p := p) (m := m) hN L.2.2.1 L'.2.2.1
      (by rw [L.2.1, L'.2.1]) (fun h => hne (Subtype.ext h)) _ _
  have hmeas : ∀ L : {L : List (ℕ × ℤ) // L.length = n ∧ (∀ q ∈ L, 1 ≤ q.2) ∧ L ∈ C},
      MeasurableSet (AchainIdx p m N L.1 univ) := fun L =>
    measurableSet_AchainIdx _ MeasurableSet.univ
  rw [measure_iUnion hdisj hmeas]
  exact tsum_congr (fun L => measure_AchainIdx_univ (p := p) (m := m) hN L.1 L.2.2.1)


/-! ### The chain event is the disjoint union of its index atoms -/

/-- **Enumeration of the recursion by index lists.**  The `n`-chain event is exactly the union of
the specified-index atoms over all positive-level lists of length `n`.  Together with
`AchainIdx_disjoint` this is a genuine partition of the chain event, so the length-`n` block-index
law is a probability law on the index lists (its total is `selTotal^n · ν(seed)` by
`measure_Achain`). -/
theorem Hpath_eq_iUnion_Hidx : ∀ (n : ℕ) (B : Set (ℕ → Fin N → ℤ)),
    Hpath (N := N) n B
      = ⋃ L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2}, Hidx (N := N) L.1 B
  | 0, B => by
      ext X
      simp only [Hpath, Set.mem_inter_iff, Set.mem_iUnion, Subtype.exists, exists_prop]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨[], ⟨rfl, by simp⟩, h1, h2⟩
      · rintro ⟨L, ⟨hlen, -⟩, hX⟩
        have hnil : L = [] := List.length_eq_zero_iff.mp hlen
        subst hnil
        exact hX
  | (n + 1), B => by
      ext X
      rw [mem_Hpath_succ]
      constructor
      · rintro ⟨hs, t, d, hd, hfr, htail⟩
        rw [Hpath_eq_iUnion_Hidx n B, Set.mem_iUnion] at htail
        obtain ⟨L, hL⟩ := htail
        refine Set.mem_iUnion.mpr ⟨⟨(t, d) :: L.1, ?_⟩, ?_⟩
        · refine ⟨by simp [L.2.1], ?_⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hd
          · exact L.2.2 q hq
        · rw [mem_Hidx_cons]
          exact ⟨hs, hfr, hL⟩
      · intro h
        rw [Set.mem_iUnion] at h
        obtain ⟨L, hX⟩ := h
        have hlen : L.1.length = n + 1 := L.2.1
        have hpos : ∀ q ∈ L.1, 1 ≤ q.2 := L.2.2
        cases hL1 : L.1 with
        | nil => simp [hL1] at hlen
        | cons p rest =>
            obtain ⟨t, d⟩ := p
            have hX' : X ∈ Hidx (N := N) ((t, d) :: rest) B := by
              rw [← hL1]; exact hX
            rw [mem_Hidx_cons] at hX'
            obtain ⟨hs, hfr, htail⟩ := hX'
            have hd : 1 ≤ d := hpos (t, d) (by rw [hL1]; simp)
            have hrest : ∀ q ∈ rest, 1 ≤ q.2 := fun q hq => hpos q (by rw [hL1]; simp [hq])
            have hlen' : rest.length = n := by
              rw [hL1] at hlen
              simpa using hlen
            refine ⟨hs, t, d, hd, hfr, ?_⟩
            rw [Hpath_eq_iUnion_Hidx n B]
            exact Set.mem_iUnion.mpr ⟨⟨rest, hlen', hrest⟩, htail⟩

/-- The array-level enumeration identity. -/
theorem Achain_eq_iUnion_idx (n : ℕ) (B : Set (ℕ → Fin N → ℤ)) :
    Achain p m N n B
      = ⋃ L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
          AchainIdx p m N L.1 B := by
  ext U
  simp only [Achain, AchainIdx, Set.mem_iUnion, Set.mem_ofPred_eq, Hpath_eq_iUnion_Hidx]


/-- **The length-`n` index law is exhaustive.**  The products of the block masses over *all*
positive-level index lists of length `n` sum to `selTotal^n`, times the seed mass.  This is
computed independently of `measure_Achain` (through the enumeration identity
`Achain_eq_iUnion_idx` and the atom masses `measure_AchainIdx_univ`), so it is a consistency
statement for the whole recursion: the enumeration is disjoint and exhaustive. -/
theorem tsum_index_atom_mass (hN : 0 < N) (n : ℕ) :
    (∑' L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
        (L.1.map (fun q => blockMassAt p m N q.1 q.2)).prod)
        * (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
  have hdisj : Pairwise (fun L L' : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2} =>
      Disjoint (AchainIdx p m N L.1 univ) (AchainIdx p m N L'.1 univ)) := by
    intro L L' hne
    exact AchainIdx_disjoint (p := p) (m := m) hN L.2.2 L'.2.2
      (by rw [L.2.1, L'.2.1]) (fun h => hne (Subtype.ext h)) _ _
  have hmeas : ∀ L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
      MeasurableSet (AchainIdx p m N L.1 univ) := fun L =>
    measurableSet_AchainIdx _ MeasurableSet.univ
  calc (∑' L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
          (L.1.map (fun q => blockMassAt p m N q.1 q.2)).prod)
        * (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed}
      = ∑' L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
          (L.1.map (fun q => blockMassAt p m N q.1 q.2)).prod *
            (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} :=
        ENNReal.tsum_mul_right.symm
    _ = ∑' L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
          (arrayMeasure N) (AchainIdx p m N L.1 univ) :=
        tsum_congr fun L =>
          (measure_AchainIdx_univ (p := p) (m := m) hN L.1 L.2.2).symm
    _ = (arrayMeasure N) (⋃ L : {L : List (ℕ × ℤ) // L.length = n ∧ ∀ q ∈ L, 1 ≤ q.2},
          AchainIdx p m N L.1 univ) := (measure_iUnion hdisj hmeas).symm
    _ = (arrayMeasure N) (Achain p m N n univ) := by
        rw [Achain_eq_iUnion_idx]
    _ = (selTotal p m N) ^ n *
          (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ seed} := by
        rw [measure_Achain (p := p) (m := m) hN n MeasurableSet.univ, seed_preimage_univ]


end SwarmSelInd
