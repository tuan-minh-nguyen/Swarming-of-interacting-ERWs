/-
# Successive regeneration blocks of the actual array: the k-fold chain factorisation

The integrated tree proves the one-block factorisation `(factor)` of the paper
(`Swarm/FirstRegen.lean`, `Swarm/SegmentLaw.lean`, `freshlaw_past_of_subset`), and a
`k`-fold version only for the *band* notion (`areas/kac/M4KBlock.lean`), which
`areas/kac/SelCollapse.lean` shows is degenerate (`BandPath e s` forces `BandPath 1 1`, so the
band selection is a Dirac mass at the trivial band).  This file supplies the `k`-fold chain
factorisation for the *actual* record/regeneration shapes `RecordAt` + `relFuture ∈ S` with no band
condition — the shape `areas/kac/SEL_COLLAPSE.md` says a repaired selection has to use.

Content:

* `pathRec`, `pathRel`, `chainRel` — the block structure as a predicate on the position path, so
  that "the future after a regeneration" can itself be tested for regeneration blocks;
* `chainMass_step`: adjoining one block multiplies the chain mass by the block mass and by
  nothing else (the ratio-free form of "the next block is independent of the past with a fixed
  law"), which is where the *dependence across the boundary* is confined to the prefix factor;
* `chainMass_eq_prod`: the `k`-fold product with an arbitrary measurable tail `B`;
* `chain_factor`: the same statement on the actual array with an arbitrary measurable prefix
  event `A` at the first block;
* `two_block_abs`: the concrete two-block form in terms of the array's own simulation records
  `RecordAt (t + s) (d + e)`, i.e. successive regenerations of the one array.
-/
import Swarm.SegmentLaw
import Swarm.SeedPos

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg
open scoped ENNReal

set_option warn.classDefReducibility false

namespace SwarmChain

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### Path-level block structure -/

/-- `pathRec t d X`: the path `X` sits at level `d` at time `t` and strictly below it before —
the path-level form of `RecordAt`. -/
def pathRec (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) : Prop :=
  (∀ s, s < t → ∀ i, X s i < d) ∧ ∀ i, X t i = d

/-- The path re-based at `(t, d)`. -/
def pathRel (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) : ℕ → Fin N → ℤ :=
  fun n i => X (t + n) i - d

/-- The prefix of a path up to time `t`, in the shape of `SwarmSeg.pastProj`. -/
def pathFst (t : ℕ) (X : ℕ → Fin N → ℤ) : Fin (t + 1) → Fin N → ℤ :=
  fun s i => X (s : ℕ) i

theorem pathRec_iff (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    RecordAt p m U t d ↔ pathRec t d (posPath p m U) := Iff.rfl

theorem pathRel_relFuture (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    relFuture p m U t d = pathRel t d (posPath p m U) := rfl

theorem pastProj_eq_pathFst (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) :
    pastProj p m t U = pathFst t (posPath p m U) := rfl

/-- `chainRel S L B`: the position path carries the list `L` of successive blocks and then the
tail condition `B`.  Block `(s, e)` requires a record at time `s` and level `e` and a re-based
future in `S`; the tail after the last block is `B`. -/
def chainRel (S : Set (ℕ → Fin N → ℤ)) : List (ℕ × ℤ) → Set (ℕ → Fin N → ℤ) →
    Set (ℕ → Fin N → ℤ)
  | [], Tail => Tail
  | (s, e) :: rest, Tail => {X | pathRec s e X ∧ pathRel s e X ∈ S ∩ chainRel S rest Tail}

/-! ### Measurability -/

theorem measurable_pathRec (t : ℕ) (d : ℤ) :
    MeasurableSet {X : ℕ → Fin N → ℤ | pathRec t d X} := by
  have h1 : {X : ℕ → Fin N → ℤ | ∀ s, s < t → ∀ i, X s i < d}
      = ⋂ (s : Fin t), ⋂ (i : Fin N), {X : ℕ → Fin N → ℤ | X (s : ℕ) i < d} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h s i; exact h s s.2 i
    · intro h s hs i; exact h ⟨s, hs⟩ i
  have h2 : {X : ℕ → Fin N → ℤ | ∀ i, X t i = d}
      = ⋂ (i : Fin N), {X : ℕ → Fin N → ℤ | X t i = d} := by
    ext X; simp
  have hsplit : {X : ℕ → Fin N → ℤ | pathRec t d X}
      = {X : ℕ → Fin N → ℤ | ∀ s, s < t → ∀ i, X s i < d}
        ∩ {X : ℕ → Fin N → ℤ | ∀ i, X t i = d} := rfl
  rw [hsplit, h1, h2]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X (s : ℕ) i) measurableSet_Iio
  · refine MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X t i)
      (measurableSet_singleton d)

theorem measurable_pathRel (t : ℕ) (d : ℤ) :
    Measurable (pathRel (N := N) t d) := by
  refine measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun i => ?_
  exact ((by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X (t + n) i)).sub_const d

theorem measurable_pathFst (t : ℕ) :
    Measurable (pathFst (N := N) t) := by
  refine measurable_pi_iff.mpr fun s => measurable_pi_iff.mpr fun i => ?_
  exact (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X (s : ℕ) i)

theorem measurableSet_chainRel (S : Set (ℕ → Fin N → ℤ)) (hS : MeasurableSet S) :
    ∀ (L : List (ℕ × ℤ)) {B : Set (ℕ → Fin N → ℤ)}, MeasurableSet B →
      MeasurableSet (chainRel S L B)
  | [], B, hB => hB
  | (s, e) :: rest, B, hB => by
      exact (measurable_pathRec s e).inter
        ((measurable_pathRel s e) (hS.inter (measurableSet_chainRel S hS rest hB)))

/-! ### The two concrete seed sets and their prefixes -/

/-- Prefix condition: the path is nonnegative up to time `s`. -/
def prefixNonneg (s : ℕ) : Set (Fin (s + 1) → Fin N → ℤ) :=
  {q | ∀ (n : Fin (s + 1)) i, 0 ≤ q n i}

/-- Prefix condition: the path is zero at time `0` and strictly positive up to time `s`. -/
def prefixStrict (s : ℕ) : Set (Fin (s + 1) → Fin N → ℤ) :=
  {q | (∀ i, q 0 i = 0) ∧ ∀ (n : Fin s) i, 0 < q ⟨(n : ℕ) + 1, Nat.succ_lt_succ n.2⟩ i}

theorem measurableSet_prefixNonneg (s : ℕ) : MeasurableSet (prefixNonneg (N := N) s) := by
  have h1 : prefixNonneg (N := N) s
      = ⋂ (n : Fin (s + 1)), ⋂ (i : Fin N), {q : Fin (s + 1) → Fin N → ℤ | 0 ≤ q n i} := by
    ext q; simp only [prefixNonneg, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h1]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
  exact (by fun_prop : Measurable fun q : Fin (s + 1) → Fin N → ℤ => q n i)
    measurableSet_Ici

theorem measurableSet_prefixStrict (s : ℕ) : MeasurableSet (prefixStrict (N := N) s) := by
  have h1 : {q : Fin (s + 1) → Fin N → ℤ | ∀ i, q 0 i = 0}
      = ⋂ (i : Fin N), {q : Fin (s + 1) → Fin N → ℤ | q 0 i = 0} := by
    ext q; simp
  have h2 : {q : Fin (s + 1) → Fin N → ℤ |
        ∀ (n : Fin s) i, 0 < q ⟨(n : ℕ) + 1, by omega⟩ i}
      = ⋂ (n : Fin s), ⋂ (i : Fin N),
          {q : Fin (s + 1) → Fin N → ℤ | 0 < q ⟨(n : ℕ) + 1, Nat.succ_lt_succ n.2⟩ i} := by
    ext q; simp
  have hsplit : prefixStrict (N := N) s
      = {q : Fin (s + 1) → Fin N → ℤ | ∀ i, q 0 i = 0}
        ∩ {q : Fin (s + 1) → Fin N → ℤ |
            ∀ (n : Fin s) i, 0 < q ⟨(n : ℕ) + 1, Nat.succ_lt_succ n.2⟩ i} := rfl
  rw [hsplit, h1, h2]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (s + 1) → Fin N → ℤ => q 0 i)
      (measurableSet_singleton 0)
  · refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
    exact (by fun_prop :
      Measurable fun q : Fin (s + 1) → Fin N → ℤ => q ⟨(n : ℕ) + 1, Nat.succ_lt_succ n.2⟩ i)
      measurableSet_Ioi

theorem mem_prefixNonneg_iff (s : ℕ) (X : ℕ → Fin N → ℤ) :
    pathFst (N := N) s X ∈ prefixNonneg s ↔ ∀ n, n ≤ s → ∀ i, 0 ≤ X n i := by
  constructor
  · intro h n hn i
    exact h ⟨n, Nat.lt_succ_iff.mpr hn⟩ i
  · intro h n i
    exact h (n : ℕ) (Nat.lt_succ_iff.mp n.2) i

theorem mem_prefixStrict_iff (s : ℕ) (X : ℕ → Fin N → ℤ) :
    pathFst (N := N) s X ∈ prefixStrict s ↔
      (∀ i, X 0 i = 0) ∧ ∀ n, 0 < n → n ≤ s → ∀ i, 0 < X n i := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun n hn hn' i => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    exact h ⟨k, by omega⟩ i
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun n i => ?_⟩
    exact h ((n : ℕ) + 1) (by omega) (by omega) i

/-- The seed condition on the whole path is the prefix condition, once the re-based future
already lies in the seed set and the re-basing level is nonnegative. -/
theorem nonnegPath_iff_prefix (s : ℕ) (e : ℤ) (he : 0 ≤ e) (X : ℕ → Fin N → ℤ)
    (hrel : pathRel s e X ∈ nonnegPath (N := N)) :
    X ∈ nonnegPath (N := N) ↔ ∀ n, n ≤ s → ∀ i, 0 ≤ X n i := by
  constructor
  · intro h n _ i; exact h n i
  · intro h n i
    rcases Nat.lt_or_ge s n with hn | hn
    · have h1 : 0 ≤ pathRel s e X (n - s) i := hrel (n - s) i
      have hsplit : s + (n - s) = n := Nat.add_sub_cancel' (le_of_lt hn)
      simp only [pathRel, hsplit] at h1
      omega
    · exact h n hn i

theorem strictPos_iff_prefix (s : ℕ) (e : ℤ) (he : 0 ≤ e) (X : ℕ → Fin N → ℤ)
    (hrel : pathRel s e X ∈ strictPos (N := N)) :
    X ∈ strictPos (N := N) ↔
      (∀ i, X 0 i = 0) ∧ ∀ n, 0 < n → n ≤ s → ∀ i, 0 < X n i := by
  constructor
  · intro hX
    obtain ⟨h0, h⟩ := mem_strictPos.mp hX
    exact ⟨h0, fun n hn _ i => h n hn i⟩
  · rintro ⟨h0, h⟩
    refine mem_strictPos.mpr ⟨h0, fun n hn i => ?_⟩
    rcases Nat.lt_or_ge s n with hn' | hn'
    · obtain ⟨-, hpos⟩ := mem_strictPos.mp hrel
      have h1 : 0 < pathRel s e X (n - s) i := hpos (n - s) (by omega) i
      have hsplit : s + (n - s) = n := Nat.add_sub_cancel' (le_of_lt hn')
      simp only [pathRel, hsplit] at h1
      omega
    · exact h n hn hn' i


/-! ### The general chain mass recursion

`S` is the seed set of allowed re-based futures (`nonnegPath` or `strictPos` in the paper) and
`pfx` is its prefix form: the set of prefix paths satisfying the seed condition up to the block
start.  `hstep` says exactly that the seed condition on the whole path is the prefix condition,
given that the re-based future is already in the seed set. -/

section General

variable {S : Set (ℕ → Fin N → ℤ)} {pfx : ∀ s : ℕ, Set (Fin (s + 1) → Fin N → ℤ)}

/-- The mass of one block: a record at `(s, e)` whose prefix path satisfies the seed prefix
condition. -/
noncomputable def blockMass (p : ℝ) (m : ℕ) (pfx : ∀ s : ℕ, Set (Fin (s + 1) → Fin N → ℤ)) (s : ℕ) (e : ℤ) :
    ℝ≥0∞ :=
  (arrayMeasure N) (recordPastSet p m s e (pfx s))

/-- The mass of the seed condition together with an arbitrary tail condition `B`. -/
noncomputable def pathSeedMass (p : ℝ) (m : ℕ) (N : ℕ) (S : Set (ℕ → Fin N → ℤ))
    (B : Set (ℕ → Fin N → ℤ)) : ℝ≥0∞ :=
  (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B}

/-- The mass of a chain of blocks followed by the tail condition `B`. -/
noncomputable def chainMass (p : ℝ) (m : ℕ) (N : ℕ) (S : Set (ℕ → Fin N → ℤ)) (L : List (ℕ × ℤ))
    (B : Set (ℕ → Fin N → ℤ)) : ℝ≥0∞ :=
  (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ chainRel S L B}

variable (hS : MeasurableSet S) (hsub : S ⊆ nonnegPath (N := N))
  (hpfx : ∀ s : ℕ, MeasurableSet (pfx s))
  (hstep : ∀ (s : ℕ) (e : ℤ), 0 ≤ e → ∀ X : ℕ → Fin N → ℤ,
    pathRel s e X ∈ S → (X ∈ S ↔ pathFst s X ∈ pfx s))

include hS hsub hpfx hstep in
/-- **One block adjoined multiplies the chain mass by the block mass and nothing else.** -/
theorem chainMass_step (s : ℕ) (e : ℤ) (he : 0 ≤ e) {L : List (ℕ × ℤ)}
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    chainMass p m N S ((s, e) :: L) B = blockMass p m pfx s e * chainMass p m N S L B := by
  have hset : {U : Array N | posPath p m U ∈ S ∩ chainRel S ((s, e) :: L) B}
      = {U : Array N | RecordAt p m U s e ∧ pastProj p m s U ∈ pfx s ∧
          relFuture p m U s e ∈ S ∩ chainRel S L B} := by
    ext U
    constructor
    · rintro ⟨hS1, hchain⟩
      obtain ⟨hrec, hrel⟩ := hchain
      have hrel' : pathRel s e (posPath p m U) ∈ S ∩ chainRel S L B := hrel
      exact ⟨hrec, (hstep s e he (posPath p m U) hrel'.1).mp hS1, hrel'⟩
    · rintro ⟨hrec, hpre, hrel⟩
      have hrel' : pathRel s e (posPath p m U) ∈ S ∩ chainRel S L B := hrel
      exact ⟨(hstep s e he (posPath p m U) hrel'.1).mpr hpre, hrec, hrel'⟩
  rw [chainMass, hset, blockMass, chainMass]
  exact freshlaw_past_of_subset p m s e hS hsub (hpfx s) (measurableSet_chainRel S hS L hB)

include hS hsub hpfx hstep in
/-- **The `k`-fold product**: a chain of blocks has mass equal to the product of the block masses
times the seed-tail mass. -/
theorem chainMass_eq_prod (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 ≤ se.2)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    chainMass p m N S L B = (L.map (fun se => blockMass p m pfx se.1 se.2)).prod
      * pathSeedMass p m N S B := by
  induction L with
  | nil =>
      rw [chainMass, pathSeedMass, List.map_nil, List.prod_nil, one_mul]
      simp only [chainRel]
  | cons se rest ih =>
      obtain ⟨s, e⟩ := se
      have he : 0 ≤ e := hL (s, e) (by simp)
      have hL' : ∀ se ∈ rest, 0 ≤ se.2 := fun se hse => hL se (List.mem_cons_of_mem _ hse)
      rw [chainMass_step (S := S) (pfx := pfx) hS hsub hpfx hstep s e he hB, ih hL',
        List.map_cons, List.prod_cons, mul_assoc]

include hS hsub hpfx hstep in
/-- **The `k`-fold chain factorisation on the actual array.**  For an arbitrary measurable prefix
event `A` at the first block and an arbitrary measurable tail `B`, the mass of the chain is the
product of one factor per block and one seed-tail factor.  No band condition, no independence
postulate, no invariant law: every factor is an explicit `arrayMeasure` of an explicit set. -/
theorem chain_factor (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 ≤ se.2) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ S ∩ chainRel S L B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (L.map (fun se => blockMass p m pfx se.1 se.2)).prod * pathSeedMass p m N S B := by
  rw [freshlaw_past_of_subset p m t d hS hsub hA (measurableSet_chainRel S hS L hB)]
  have hprod := chainMass_eq_prod (p := p) (m := m) (S := S) (pfx := pfx)
    hS hsub hpfx hstep L hL hB
  simp only [chainMass] at hprod
  rw [hprod, mul_assoc]

end General

/-! ### The two instantiations used by the paper -/

/-- Nonnegative seed (`nonnegPath`), with its prefix form. -/
theorem chain_factor_nonneg (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 ≤ se.2)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ nonnegPath (N := N) ∩ chainRel (nonnegPath (N := N)) L B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (L.map (fun se => blockMass p m (prefixNonneg (N := N)) se.1 se.2)).prod
        * pathSeedMass p m N (nonnegPath (N := N)) B := by
  refine chain_factor (S := nonnegPath (N := N)) (pfx := fun s => prefixNonneg (N := N) s)
    measurableSet_nonnegPath (subset_refl _) (fun s => measurableSet_prefixNonneg s) ?_ _ _ hA L hL hB
  intro s e he X hrel
  exact (nonnegPath_iff_prefix s e he X hrel).trans (mem_prefixNonneg_iff s X).symm

/-- Strict seed (the paper's `V`, `strictPos`), with its prefix form. -/
theorem chain_factor_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 < se.2)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N) ∩ chainRel (strictPos (N := N)) L B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (L.map (fun se => blockMass p m (prefixStrict (N := N)) se.1 se.2)).prod
        * pathSeedMass p m N (strictPos (N := N)) B := by
  refine chain_factor (S := strictPos (N := N)) (pfx := fun s => prefixStrict (N := N) s)
    measurableSet_strictPos strictPos_subset_nonnegPath (fun s => measurableSet_prefixStrict s)
    ?_ _ _ hA L (fun se hse => le_of_lt (hL se hse)) hB
  intro s e he X hrel
  exact (strictPos_iff_prefix s e he X hrel).trans (mem_prefixStrict_iff s X).symm


/-! ### Re-basing twice, and the chain read on the single array

The block structure above is stated on an abstract position path.  These lemmas show that a block
of the *re-based* path is literally a further simultaneous record of the same array, which is what
makes `chain_factor` a statement about successive regenerations of the one array rather than an
abstract iteration. -/

theorem pathRel_pathRel (t s : ℕ) (d e : ℤ) (X : ℕ → Fin N → ℤ) :
    pathRel s e (pathRel t d X) = pathRel (t + s) (d + e) X := by
  funext n i
  simp only [pathRel]
  rw [show t + (s + n) = t + s + n from by omega]
  ring

/-- The record condition of the re-based path is the record condition at the re-based level. -/
theorem pathRec_pathRel (t s : ℕ) (d e : ℤ) (X : ℕ → Fin N → ℤ) (he : 0 ≤ e)
    (hrec : pathRec t d X) :
    pathRec s e (pathRel t d X) ↔ pathRec (t + s) (d + e) X := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro u hu i
      rcases Nat.lt_or_ge u t with h | h
      · have h3 := hrec.1 u h i; omega
      · obtain ⟨k, rfl⟩ : ∃ k, u = t + k := ⟨u - t, by omega⟩
        have hk : k < s := by omega
        have h3 : X (t + k) i - d < e := h1 k hk i
        omega
    · intro i
      have h3 : X (t + s) i - d = e := h2 i
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro k hk i
      have h3 := h1 (t + k) (by omega) i
      show X (t + k) i - d < e
      omega
    · intro i
      have h3 := h2 i
      show X (t + s) i - d = e
      omega

/-- **The second block is the next simultaneous record.**  On a record of the array at `(t, d)`,
a record of the re-based path at relative `(s, e)` is a record of the same array at `(t + s, d + e)`,
and the re-based future after it is the absolute relative future. -/
theorem two_block_iff (U : Array N) (t s : ℕ) (d e : ℤ) (he : 0 ≤ e)
    (hrec : RecordAt p m U t d) {R : Set (ℕ → Fin N → ℤ)} :
    relFuture p m U t d ∈ {X | pathRec s e X ∧ pathRel s e X ∈ R}
      ↔ (RecordAt p m U (t + s) (d + e) ∧ relFuture p m U (t + s) (d + e) ∈ R) := by
  have hrec' : pathRec t d (posPath p m U) := hrec
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(pathRec_pathRel t s d e (posPath p m U) he hrec').mp h1, ?_⟩
    show pathRel (t + s) (d + e) (posPath p m U) ∈ R
    rw [← pathRel_pathRel]
    exact h2
  · rintro ⟨h1, h2⟩
    have h2' : pathRel (t + s) (d + e) (posPath p m U) ∈ R := h2
    rw [← pathRel_pathRel] at h2'
    exact ⟨(pathRec_pathRel t s d e (posPath p m U) he hrec').mpr h1, h2'⟩

/-- **The two-block chain on the actual array.**  Two successive blocks of the paper's strict
regeneration type, written with the array's own records: the mass is the first block's prefix
mass, times the second block's prefix mass, times the seed-tail mass. -/
theorem two_block_factor_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (s : ℕ) (e : ℤ) (he : 0 < e) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N) ∧ RecordAt p m U (t + s) (d + e) ∧
        relFuture p m U (t + s) (d + e) ∈ strictPos (N := N) ∩ B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (arrayMeasure N) (recordPastSet p m s e (prefixStrict (N := N) s))
        * pathSeedMass p m N (strictPos (N := N)) B := by
  have hset : {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N) ∧ RecordAt p m U (t + s) (d + e) ∧
        relFuture p m U (t + s) (d + e) ∈ strictPos (N := N) ∩ B}
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈
            strictPos (N := N) ∩ chainRel (strictPos (N := N)) [(s, e)] B} := by
    ext U
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, ?_⟩
      exact (two_block_iff U t s d e (le_of_lt he) h1).mpr ⟨h4, h5⟩
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨h5, h6⟩ := (two_block_iff U t s d e (le_of_lt he) h1).mp h4
      exact ⟨h1, h2, h3, h5, h6⟩
  rw [hset]
  have hL : ∀ se ∈ [(s, e)], 0 < se.2 := by
    intro se hse
    rw [List.mem_singleton] at hse
    rw [hse]
    exact he
  have h := chain_factor_strict (p := p) (m := m) t d hA [(s, e)] hL hB
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, blockMass]
    using h

/-- **Multiplicativity, ratio-free.**  Under the paper's seed conditioning the two blocks are
independent and identically distributed: the conditioned mass of "block one and block two" is the
product of the conditioned masses, and no division by the seed mass is performed. -/
theorem renewal_cross_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (s : ℕ) (e : ℤ) (he : 0 < e) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N) ∧ RecordAt p m U (t + s) (d + e) ∧
        relFuture p m U (t + s) (d + e) ∈ strictPos (N := N) ∩ B}
      * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
      = (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ strictPos (N := N)}
        * (arrayMeasure N) {U : Array N | RecordAt p m U s e ∧
            pastProj p m s U ∈ prefixStrict (N := N) s ∧
            relFuture p m U s e ∈ strictPos (N := N) ∩ B} := by
  rw [two_block_factor_strict (p := p) (m := m) t d hA s e he hB]
  have hfirst : (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
      relFuture p m U t d ∈ strictPos (N := N)}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    have h := freshlawStrict_past p m t d (A := A) hA (B := univ) MeasurableSet.univ
    simpa only [Set.inter_univ, pathSeedMass] using h
  have hsecond : (arrayMeasure N) {U : Array N | RecordAt p m U s e ∧
      pastProj p m s U ∈ prefixStrict (N := N) s ∧
      relFuture p m U s e ∈ strictPos (N := N) ∩ B}
      = (arrayMeasure N) (recordPastSet p m s e (prefixStrict (N := N) s))
        * pathSeedMass p m N (strictPos (N := N)) B := by
    have h := freshlawStrict_past p m s e (A := prefixStrict (N := N) s)
      (measurableSet_prefixStrict s) (B := B) hB
    simpa only [pathSeedMass] using h
  rw [hfirst, hsecond]
  ring

/-! ### The `k`-fold chain as successive records of the one array

`absChain S t d L B` reads the list `L` of *relative* blocks as records of the single array at the
cumulative times and levels, with the seed condition (no return below the level) at each scale.
`chainRel_abs` identifies it with the abstract `chainRel` on the re-based position path, so
`chain_factor_abs` below is the statement that `k` successive regenerations of the one array have
mass equal to the product of the block masses. -/

/-- The cumulative record chain of the one array. -/
def absChain (p : ℝ) (m : ℕ) (N : ℕ) (S : Set (ℕ → Fin N → ℤ)) (t : ℕ) (d : ℤ) :
    List (ℕ × ℤ) → Set (ℕ → Fin N → ℤ) → Set (Array N)
  | [], Tail => {U | relFuture p m U t d ∈ S ∩ Tail}
  | (s, e) :: rest, Tail =>
      {U | relFuture p m U t d ∈ S ∧ RecordAt p m U (t + s) (d + e) ∧
        relFuture p m U (t + s) (d + e) ∈ S ∧
        U ∈ absChain p m N S (t + s) (d + e) rest Tail}

/-- **The abstract chain is the cumulative record chain of the one array.** -/
theorem chainRel_abs (S : Set (ℕ → Fin N → ℤ)) (L : List (ℕ × ℤ))
    (hL : ∀ se ∈ L, 0 ≤ se.2) :
    ∀ (t : ℕ) (d : ℤ) (Tail : Set (ℕ → Fin N → ℤ)),
      {U : Array N | RecordAt p m U t d ∧ relFuture p m U t d ∈ S ∩ chainRel S L Tail}
        = {U : Array N | RecordAt p m U t d ∧ U ∈ absChain p m N S t d L Tail} := by
  induction L with
  | nil =>
      intro t d Tail
      rfl
  | cons se rest ih =>
      intro t d Tail
      obtain ⟨s, e⟩ := se
      have he : 0 ≤ e := hL (s, e) (by simp)
      have hL' : ∀ se ∈ rest, 0 ≤ se.2 := fun se hse => hL se (List.mem_cons_of_mem _ hse)
      have hIH := ih hL' (t + s) (d + e) Tail
      ext U
      constructor
      · rintro ⟨hrec, hS1, hchain⟩
        obtain ⟨h1, h2⟩ := hchain
        obtain ⟨hrec2, hrel2⟩ :=
          (two_block_iff U t s d e he hrec).mp (show relFuture p m U t d ∈
            {X : ℕ → Fin N → ℤ | pathRec s e X ∧
              pathRel s e X ∈ S ∩ chainRel S rest Tail} from ⟨h1, h2⟩)
        refine ⟨hrec, hS1, hrec2, hrel2.1, ?_⟩
        exact ((Set.ext_iff.mp hIH U).mp ⟨hrec2, hrel2⟩).2
      · rintro ⟨hrec, hS1, hrec2, hrel2, hrest⟩
        have hmem : U ∈ {U : Array N | RecordAt p m U (t + s) (d + e) ∧
            relFuture p m U (t + s) (d + e) ∈ S ∩ chainRel S rest Tail} :=
          ⟨hrec2, ((Set.ext_iff.mp hIH U).mpr ⟨hrec2, hrest⟩).2⟩
        obtain ⟨hrec2', hrel2'⟩ := hmem
        obtain ⟨h1, h2⟩ :=
          (two_block_iff U t s d e he hrec).mpr ⟨hrec2', hrel2'⟩
        exact ⟨hrec, hS1, h1, h2⟩

/-- **`k` successive regenerations of the one array**: cumulative records at the running levels,
each followed by a strictly-positive (or nonnegative) re-based future, and then the tail. -/
theorem chain_factor_abs (S : Set (ℕ → Fin N → ℤ)) (pfx : ∀ s : ℕ,
      Set (Fin (s + 1) → Fin N → ℤ))
    (hS : MeasurableSet S) (hsub : S ⊆ nonnegPath (N := N)) (hpfx : ∀ s, MeasurableSet (pfx s))
    (hstp : ∀ (s : ℕ) (e : ℤ), 0 ≤ e → ∀ X : ℕ → Fin N → ℤ,
      pathRel s e X ∈ S → (X ∈ S ↔ pathFst s X ∈ pfx s))
    (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 ≤ se.2) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        U ∈ absChain p m N S t d L B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (L.map (fun se => blockMass p m pfx se.1 se.2)).prod * pathSeedMass p m N S B := by
  have hset : {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        U ∈ absChain p m N S t d L B}
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ S ∩ chainRel S L B} := by
    ext U
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, ((Set.ext_iff.mp (chainRel_abs S L hL t d B) U).mpr ⟨h1, h3⟩).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, ((Set.ext_iff.mp (chainRel_abs S L hL t d B) U).mp ⟨h1, h3⟩).2⟩
  rw [hset, chain_factor (p := p) (m := m) (S := S) (pfx := pfx) hS hsub hpfx hstp
    t d hA L hL hB]

/-- The strict (`V`) instance of `chain_factor_abs` with the paper's `strictPos` seed and its
prefix condition. -/
theorem chain_factor_abs_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 < se.2)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        U ∈ absChain p m N (strictPos (N := N)) t d L B}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (L.map (fun se => blockMass p m (prefixStrict (N := N)) se.1 se.2)).prod
        * pathSeedMass p m N (strictPos (N := N)) B := by
  refine chain_factor_abs (S := strictPos (N := N)) (pfx := fun s => prefixStrict (N := N) s)
    measurableSet_strictPos strictPos_subset_nonnegPath (fun s => measurableSet_prefixStrict s) ?_
    t d hA L (fun se hse => le_of_lt (hL se hse)) hB
  intro s e he X hrel
  exact (strictPos_iff_prefix s e he X hrel).trans (mem_prefixStrict_iff s X).symm

/-! ### The conditional form: two successive blocks are independent under the seed conditioning

`condMass S Z` is the paper's `P^*(Z)` written without division.  `condMass_two_block_strict` is
the ratio-free content of the paper's "the successive distance and duration increments are
independent and identically distributed": the conditioned mass of two successive blocks is the
product of the conditioned masses. -/

/-- The seed-conditioned mass of an array event, i.e. the paper's `P^*` in ratio-free form. -/
noncomputable def condMass (p : ℝ) (m : ℕ) (N : ℕ) (S : Set (ℕ → Fin N → ℤ))
    (Z : Set (Array N)) : ℝ≥0∞ :=
  ((arrayMeasure N) {U : Array N | posPath p m U ∈ S})⁻¹ * (arrayMeasure N) Z

theorem inv_mul_mul_cancel {a b : ℝ≥0∞} (h0 : a ≠ 0) (ht : a ≠ ⊤) : a⁻¹ * (b * a) = b := by
  rw [mul_comm b a, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- **The first block under the seed conditioning** has the raw record-prefix mass. -/
theorem condMass_block_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A)
    (hne : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hnt : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    condMass p m N (strictPos (N := N))
        {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ strictPos (N := N)}
      = (arrayMeasure N) (recordPastSet p m t d A) := by
  have h := freshlawStrict_past p m t d (A := A) hA (B := univ) MeasurableSet.univ
  simp only [Set.inter_univ] at h
  rw [condMass, h]
  exact inv_mul_mul_cancel hne hnt

/-- **Two successive blocks are conditionally independent and identically distributed.** -/
theorem condMass_two_block_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (s : ℕ) (e : ℤ) (he : 0 < e) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B)
    (hne : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hnt : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    condMass p m N (strictPos (N := N))
        {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ strictPos (N := N) ∧ RecordAt p m U (t + s) (d + e) ∧
          relFuture p m U (t + s) (d + e) ∈ strictPos (N := N) ∩ B}
      = condMass p m N (strictPos (N := N))
          {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
            relFuture p m U t d ∈ strictPos (N := N)}
        * condMass p m N (strictPos (N := N))
          {U : Array N | RecordAt p m U s e ∧ pastProj p m s U ∈ prefixStrict (N := N) s ∧
            relFuture p m U s e ∈ strictPos (N := N) ∩ B} := by
  have h2 := two_block_factor_strict (p := p) (m := m) t d hA s e he hB
  have h1 : (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
      relFuture p m U t d ∈ strictPos (N := N)}
      = (arrayMeasure N) (recordPastSet p m t d A)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    have h := freshlawStrict_past p m t d (A := A) hA (B := univ) MeasurableSet.univ
    simpa only [Set.inter_univ] using h
  have h3 : (arrayMeasure N) {U : Array N | RecordAt p m U s e ∧
      pastProj p m s U ∈ prefixStrict (N := N) s ∧
      relFuture p m U s e ∈ strictPos (N := N) ∩ B}
      = (arrayMeasure N) (recordPastSet p m s e (prefixStrict (N := N) s))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
    freshlawStrict_past p m s e (A := prefixStrict (N := N) s)
      (measurableSet_prefixStrict s) (B := B) hB
  simp only [condMass]
  rw [h2, h1, h3]
  simp only [pathSeedMass]
  rw [inv_mul_mul_cancel hne hnt]
  ring

/-- **The two-block conditional independence in the paper's own parameter range.**  The two seed
positivity hypotheses are discharged by the integrated `SwarmSeed.strictPos_measure_ne_zero`, so
the only hypotheses are the paper's parameter range, measurability of the prefix and tail events
and `0 < e`. -/
theorem condMass_two_block_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)} (hA : MeasurableSet A)
    (s : ℕ) (e : ℤ) (he : 0 < e) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    condMass p m N (strictPos (N := N))
        {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          relFuture p m U t d ∈ strictPos (N := N) ∧ RecordAt p m U (t + s) (d + e) ∧
          relFuture p m U (t + s) (d + e) ∈ strictPos (N := N) ∩ B}
      = condMass p m N (strictPos (N := N))
          {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
            relFuture p m U t d ∈ strictPos (N := N)}
        * condMass p m N (strictPos (N := N))
          {U : Array N | RecordAt p m U s e ∧ pastProj p m s U ∈ prefixStrict (N := N) s ∧
            relFuture p m U s e ∈ strictPos (N := N) ∩ B} :=
  condMass_two_block_strict t d hA s e he hB
    (SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN) (measure_ne_top _ _)

/-! ### The record times at a fixed level are unique: the block masses are a defective law

The `k`-fold factorisation above is an identity along a *specified* list of blocks.  To turn it into
a law on block data one has to sum over the possible next blocks.  The elementary half of that is
here: at any fixed level there is at most one record time, so the raw record masses (and hence the
block masses) are summable and total at most one.  The remaining half — a selection rule across
levels, so that the block events for different levels are disjoint — is not proved here. -/

/-- **At most one record time at a fixed level.** -/
theorem recordAt_disjoint (hN : 0 < N) {d : ℤ} {t t' : ℕ} (h : t ≠ t') :
    Disjoint {U : Array N | RecordAt p m U t d} {U : Array N | RecordAt p m U t' d} := by
  rw [Set.disjoint_left]
  intro U h1 h2
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hN
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · have hlt' := h2.1 t hlt i
    have heq := h1.2 i
    omega
  · have hlt' := h1.1 t' hlt i
    have heq := h2.2 i
    omega

/-- **The record masses at a fixed level are summable and total at most one.** -/
theorem tsum_recordSet_le_one (hN : 0 < N) (d : ℤ) :
    (∑' t, (arrayMeasure N) (recordSet (N := N) p m t d)) ≤ 1 := by
  have hmeas : ∀ t, MeasurableSet (recordSet (N := N) p m t d) := fun t =>
    measurableSet_recordSet p m t d
  have hdisj : Pairwise fun t t' =>
      AEDisjoint (arrayMeasure N) (recordSet (N := N) p m t d) (recordSet (N := N) p m t' d) := by
    intro t t' h
    exact (recordAt_disjoint hN h).aedisjoint
  have h := MeasureTheory.tsum_measure_le_measure_univ (μ := arrayMeasure N)
    (fun t => (hmeas t).nullMeasurableSet) hdisj
  rwa [measure_univ] at h

/-- A product of `a⁻¹ * (b * a)` factors is the product of the `b` factors. -/
theorem prod_inv_mul_mul_cancel {a : ℝ≥0∞} {ι : Type*} (L : List ι) (b : ι → ℝ≥0∞)
    (h0 : a ≠ 0) (ht : a ≠ ⊤) :
    (L.map (fun z => a⁻¹ * (b z * a))).prod = (L.map b).prod := by
  induction L with
  | nil => simp
  | cons z rest ih =>
      rw [List.map_cons, List.prod_cons, ih,
        List.map_cons, List.prod_cons, inv_mul_mul_cancel h0 ht]

/-- **`k` successive blocks are conditionally independent and identically distributed.**  Under
the seed conditioning `P^*`, the mass of the whole chain is the product of one conditioned mass per
block and one for the tail — the finite-dimensional content of the paper's "by iteration, the
successive distance and duration increments are independent and identically distributed". -/
theorem condMass_chain_abs_strict (t : ℕ) (d : ℤ) {A : Set (Fin (t + 1) → Fin N → ℤ)}
    (hA : MeasurableSet A) (L : List (ℕ × ℤ)) (hL : ∀ se ∈ L, 0 < se.2)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B)
    (hne : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hnt : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    condMass p m N (strictPos (N := N))
        {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
          U ∈ absChain p m N (strictPos (N := N)) t d L B}
      = condMass p m N (strictPos (N := N))
          {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
            relFuture p m U t d ∈ strictPos (N := N)}
        * (L.map (fun se => condMass p m N (strictPos (N := N))
            {U : Array N | RecordAt p m U se.1 se.2 ∧
              pastProj p m se.1 U ∈ prefixStrict (N := N) se.1 ∧
              relFuture p m U se.1 se.2 ∈ strictPos (N := N)})).prod
        * condMass p m N (strictPos (N := N)) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have hch := chain_factor_abs_strict (p := p) (m := m) t d hA L hL hB
  -- the first factor and every block factor are conditioned block masses
  have h1 : condMass p m N (strictPos (N := N))
      {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ A ∧
        relFuture p m U t d ∈ strictPos (N := N)}
      = ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹ *
        ((arrayMeasure N) (recordPastSet p m t d A) *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) := by
    have h := freshlawStrict_past p m t d (A := A) hA (B := univ) MeasurableSet.univ
    simp only [Set.inter_univ] at h
    simp only [condMass]
    rw [h]
  have h2 : ∀ se ∈ L, condMass p m N (strictPos (N := N))
      {U : Array N | RecordAt p m U se.1 se.2 ∧
        pastProj p m se.1 U ∈ prefixStrict (N := N) se.1 ∧
        relFuture p m U se.1 se.2 ∈ strictPos (N := N)}
      = ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹ *
        (blockMass p m (prefixStrict (N := N)) se.1 se.2 *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) := by
    intro se _
    have h := freshlawStrict_past p m se.1 se.2 (A := prefixStrict (N := N) se.1)
      (measurableSet_prefixStrict se.1) (B := univ) MeasurableSet.univ
    simp only [Set.inter_univ] at h
    simp only [condMass, blockMass]
    rw [h]
  simp only [condMass] at h1 h2
  simp only [blockMass] at h2 hch
  simp only [condMass]
  rw [hch, h1, List.map_congr_left (fun z hz => h2 z hz)]
  rw [prod_inv_mul_mul_cancel L
    (fun z => (arrayMeasure N) (recordPastSet p m z.1 z.2 (prefixStrict (N := N) z.1)))
    hne hnt, inv_mul_mul_cancel hne hnt]
  simp only [pathSeedMass]
  ring_nf

end SwarmChain
