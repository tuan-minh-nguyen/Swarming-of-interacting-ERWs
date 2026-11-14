/-
# the actual array word / cylinder decomposition

This file works **only on the array side** of the finite-horizon comparison.  Its object is the
i.i.d. uniform array's own jump-word enumeration: for each finite horizon `k` the array space
`Array N` is cut into the finitely many *jump boxes* `jbox p m k q` (`q : Fin k → JumpVec N`), one
per possible word of the first `k` jumps.  Everything below is a statement about the actual
probability measure `arrayMeasure N` and the actual trajectory `trajectory p m U`.

Contents.

* §1  The word map `jumpWord`, its boxes and the **partition**: distinct words have disjoint
      boxes, the boxes cover the whole space, every box is measurable, and the mass of a finite
      union over a word predicate is the sum of the exact box masses `pathW p k q (startState m)`.
      This yields the **transfer principle** `arrayMeasure N {U | P (jumpWord U)} = ∑_q [P q] ·
      ofReal (pathW p k q startState)`, which turns every finite-horizon event that is a *word
      predicate* into a finite word sum with the correct array measures.

* §2  Instantiation at the horizon event used by the `hstruct` reduction: the
      `finStrict K ∩ pathPat⁻¹ C` cylinder.  On the box of `q` the array's path pattern *is*
      `patOf q`, and strict positivity up to `K` *is* `PosSeqFin q`; hence
      `arrayMeasure (finStrict K ∩ pathPat⁻¹ C) = ∑_q [PosSeqFin q ∧ patOf q ∈ C] ·
      ofReal (pathW p K q startState)`, for an **arbitrary** (not necessarily measurable) pattern
      cylinder `C`.  Measurability of the cylinder is a by-product.

* §3  Instantiation at the first-record cylinder `arrayFirstRecordCyl p m k`: it is the word set
      `{U | FirstRecord (extendPath (jumpWord U)) k (ofRecState y)}` for `y ∈ srSet`, so its mass
      is a finite sum over **all** first-record words of length `k`, each with the array's own box
      mass.  Different `k` give disjoint cylinders, so the first positive excursion up to a horizon
      `L` has mass `∑_{k=1}^{L} ∑_{q first-record at k} ofReal (pathW p k q startState)` — the
      multi-word, varying-length decomposition.  Non-vacuity at `k = 1` is proved.

* §4  The successor-word weight: `pathWFun` splits at a block boundary into the first block's
      weight times the weight of the remaining word measured from the *word-determined* successor
      state `evolveFun u k1 (startState m)`.  On the array this is the exact statement that the
      continuation weight after the first block is a function of the first word alone (no fresh
      independence and no state average is used or claimed).

* §5  Scope / audit.  `FirstRecord` and `PosSeqFin` are *incompatible* for `k ≥ 2` (they
      contradict each other at time `1`), so the earlier single-word bridge
      `FreshArrayBridge.array_jbox_mass_eq_segKpos`, whose hypotheses are exactly that
      conjunction, is non-vacuous only at `k = 1`.  The array-side first-record mass proved here
      is a sum of `pathW · startState`; the chain-side segment atoms carry
      `hitW = pathW · ofRecState y`.  Those two weight families coincide on `PosSeqFin` words
      (`pathW_startState_eq`) and on nothing else is a coincidence claimed here.  No `hstruct`,
      invariant `π`, stationarity, regeneration or speed statement is made.
-/
import Swarm.FinHorizonHstruct

open MeasureTheory Set
open scoped ENNReal BigOperators
open Classical

attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmArrayWords

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump SimJump.Record
open SwarmRec SwarmFreshPos SwarmFreshCyl SwarmFreshArray SwarmFinHorizon SwarmRestart
  SwarmFresh

variable {N : ℕ}

/-! ## 1. The word map and the partition of the array space by jump boxes -/

/-- The word of the first `k` actual jumps of the array. -/
noncomputable def jumpWord (p : ℝ) (m : ℕ) (k : ℕ) (U : Array N) : Fin k → JumpVec N :=
  fun n i => nextJumpVec p m U (n : ℕ) i

/-- The jump box of `q` is exactly the level set of `jumpWord` at `q`. -/
theorem mem_jbox_iff (p : ℝ) (m k : ℕ) (q : Fin k → JumpVec N) (U : Array N) :
    U ∈ jbox p m k q ↔ jumpWord p m k U = q := by
  constructor
  · intro h
    funext n i
    exact h n i
  · intro h n i
    exact congrFun (congrFun h n) i

/-- Every array lies in the box of its own word (the boxes cover). -/
theorem mem_jbox_jumpWord (p : ℝ) (m k : ℕ) (U : Array N) :
    U ∈ jbox p m k (jumpWord p m k U) :=
  (mem_jbox_iff p m k _ U).mpr rfl

/-- Distinct words have disjoint boxes. -/
theorem disjoint_jbox {p : ℝ} {m k : ℕ} {q q' : Fin k → JumpVec N} (h : q ≠ q') :
    Disjoint (jbox p m k q) (jbox p m k q') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  have h1' : jumpWord p m k U = q := (mem_jbox_iff p m k q U).mp h1
  have h2' : jumpWord p m k U = q' := (mem_jbox_iff p m k q' U).mp h2
  exact h (h1'.symm.trans h2')

/-- The boxes of all words of length `k` cover the array space. -/
theorem iUnion_jbox (p : ℝ) (m k : ℕ) :
    (⋃ q : Fin k → JumpVec N, jbox p m k q) = univ := by
  ext U
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨jumpWord p m k U, mem_jbox_jumpWord p m k U⟩

/-- A jump box is a cylinder over the word's own read coordinates, hence measurable. -/
theorem measurableSet_jbox (p : ℝ) (m k : ℕ) (q : Fin k → JumpVec N) :
    MeasurableSet (jbox p m k q) := by
  rw [jbox_eq_cyl_prod]
  exact MeasurableSet.iInter fun ni =>
    measurable_pi_apply (jcoord p m (extendPath q) (ni.1 : ℕ) ni.2)
      (measurableSet_jumpSet (q ni.1 ni.2) (jalpha p m (extendPath q) (ni.1 : ℕ) ni.2))

/-- The event "the word of the first `k` jumps satisfies `P`" is a finite union of boxes. -/
theorem wordSet_eq_biUnion (p : ℝ) (m k : ℕ) (P : (Fin k → JumpVec N) → Prop) [DecidablePred P] :
    {U : Array N | P (jumpWord p m k U)} = ⋃ q ∈ Finset.univ.filter P, jbox p m k q := by
  ext U
  simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hP
    exact ⟨jumpWord p m k U, hP, mem_jbox_jumpWord p m k U⟩
  · rintro ⟨q, hP, hbox⟩
    have hq : jumpWord p m k U = q := (mem_jbox_iff p m k q U).mp hbox
    rw [hq]
    exact hP

/-- **The exact mass of a finite word cylinder**: a finite union of boxes over a decidable word
predicate has, under the actual array law, the mass of the sum of the exact box masses. -/
theorem mass_biUnion_jbox (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (P : (Fin k → JumpVec N) → Prop) [DecidablePred P] :
    (arrayMeasure N) (⋃ q ∈ Finset.univ.filter P, jbox p m k q)
      = ∑ q : Fin k → JumpVec N,
          if P q then ENNReal.ofReal (pathW p k q (startState (N := N) m)) else 0 := by
  rw [measure_biUnion_finset (fun a _ b _ hab => disjoint_jbox hab)
    (fun b _ => measurableSet_jbox p m k b), Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · exact mass_jbox_pathW hp0 hp1 m k q
  · rfl

/-- **Transfer principle.**  The array mass of an event that depends only on the first `k` jumps
through a word predicate `P` is the finite word sum of the exact box masses.  No independence,
stationarity or record input is used; the identity is the box partition plus `mass_jbox_pathW`. -/
theorem mass_wordSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (P : (Fin k → JumpVec N) → Prop) [DecidablePred P] :
    (arrayMeasure N) {U : Array N | P (jumpWord p m k U)}
      = ∑ q : Fin k → JumpVec N,
          if P q then ENNReal.ofReal (pathW p k q (startState (N := N) m)) else 0 := by
  rw [wordSet_eq_biUnion, mass_biUnion_jbox p hp0 hp1 m k P]

/-- Word-predicate cylinders of the array are measurable. -/
theorem measurableSet_wordSet (p : ℝ) (m k : ℕ) (P : (Fin k → JumpVec N) → Prop)
    [DecidablePred P] :
    MeasurableSet {U : Array N | P (jumpWord p m k U)} := by
  rw [wordSet_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun b _ => measurableSet_jbox p m k b

/-! ## 2. The horizon cylinder `finStrict K ∩ pathPat⁻¹ C`

`finStrict K` is the `K`-horizon strict positivity event of `FinHorizonHstruct`; `pathPat K` is the
first `K+1` positions of a path.  On the box of a word `q` both are read off `q` alone. -/

/-- The array position path is the position component of the trajectory. -/
theorem posPath_apply (p : ℝ) (m n : ℕ) (U : Array N) (i : Fin N) :
    posPath p m U n i = (trajectory p m U n).pos i := rfl

/-- On the box of `q`, the array's finite path pattern is `patOf q`. -/
theorem pathPat_posPath_eq_patOf (p : ℝ) (m k : ℕ) (q : Fin k → JumpVec N) {U : Array N}
    (hbox : U ∈ jbox p m k q) :
    pathPat (N := N) k (posPath p m U) = patOf (N := N) q := by
  funext n i
  show (trajectory p m U (n : ℕ)).pos i = posAt (seqOf q) (n : ℕ) i
  rw [array_trajectory_pos_eq_wordCyl p m q hbox (by have := n.2; omega),
    posAt_seqOf_eq_extendPath q (n : ℕ) i (by have := n.2; omega)]

/-- On the box of `q`, `finStrict k` is exactly the word condition `PosSeqFin q`. -/
theorem posPath_mem_finStrict_iff (p : ℝ) (m k : ℕ) (q : Fin k → JumpVec N) {U : Array N}
    (hbox : U ∈ jbox p m k q) :
    posPath p m U ∈ finStrict (N := N) k ↔ PosSeqFin (N := N) q := by
  rw [mem_finStrict, posWord_iff]
  constructor
  · rintro ⟨-, h⟩ n hn1 hnk i
    have h' := h n hn1 hnk i
    rw [posPath_apply, array_trajectory_pos_eq_wordCyl p m q hbox hnk i] at h'
    exact h'
  · intro h
    refine ⟨fun i => posPath_zero p m U i, fun n hn1 hnk i => ?_⟩
    have h' := h n hn1 hnk i
    rw [posPath_apply, array_trajectory_pos_eq_wordCyl p m q hbox hnk i]
    exact h'

/-- The `finStrict K ∩ pathPat⁻¹ C` cylinder is a word-predicate cylinder of the first `K` jumps,
for **every** pattern set `C`. -/
theorem finStrict_pattern_eq_wordSet (p : ℝ) (m K : ℕ)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C}
      = {U : Array N | PosSeqFin (N := N) (jumpWord p m K U)
          ∧ patOf (N := N) (jumpWord p m K U) ∈ C} := by
  ext U
  have hbox := mem_jbox_jumpWord p m K U
  have hpat := pathPat_posPath_eq_patOf p m K (jumpWord p m K U) hbox
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [hpat, posPath_mem_finStrict_iff p m K _ hbox]

/-- **The finite-horizon array mass as an exact finite word sum.**  For every `K` and every
(not necessarily measurable) pattern cylinder `C`, the actual array mass of the horizon event
`finStrict K ∩ pathPat⁻¹ C` is the sum, over all words `q` of length `K` whose walkers stay
strictly above the level and whose position pattern lies in `C`, of the array's own box mass
`ofReal (pathW p K q (startState m))`. -/
theorem arrayMeasure_finStrict_pattern (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C}
      = ∑ q : Fin K → JumpVec N,
          if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
            then ENNReal.ofReal (pathW p K q (startState (N := N) m)) else 0 := by
  rw [finStrict_pattern_eq_wordSet,
    mass_wordSet p hp0 hp1 m K
      (fun q => PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C)]

/-- Measurability of the horizon cylinder, in the same generality: no measurability of `C` is
assumed. -/
theorem measurableSet_finStrict_pattern (p : ℝ) (m K : ℕ)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    MeasurableSet
      {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  rw [finStrict_pattern_eq_wordSet]
  exact measurableSet_wordSet p m K
    (fun q => PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C)

/-- The `C = univ` case: the horizon strict-positivity mass is the sum of the positive words'
box masses. -/
theorem arrayMeasure_finStrict (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m K : ℕ) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K}
      = ∑ q : Fin K → JumpVec N,
          if PosSeqFin (N := N) q
            then ENNReal.ofReal (pathW p K q (startState (N := N) m)) else 0 := by
  have hset : {U : Array N | posPath p m U ∈ finStrict (N := N) K}
      = {U : Array N | PosSeqFin (N := N) (jumpWord p m K U)} := by
    ext U
    exact posPath_mem_finStrict_iff p m K _ (mem_jbox_jumpWord p m K U)
  rw [hset, mass_wordSet p hp0 hp1 m K (fun q => PosSeqFin (N := N) q)]

/-! ## 3. First-record cylinders: the varying-length word decomposition -/

/-- The first-record cylinder, read through its definition. -/
theorem mem_arrayFirstRecordCyl_iff (N : ℕ) (p : ℝ) (m k : ℕ) (U : Array N) :
    U ∈ arrayFirstRecordCyl (N := N) p m k ↔
      (∃ i, posPath p m U k i = 1) ∧ ∀ t < k, ∀ i, posPath p m U t i ≤ 0 :=
  Iff.rfl

/-- **The first-record cylinder is the word set of the first-record words.**  For `y ∈ srSet`, the
actual array event "some walker is at level `1` at time `k` and nobody is above the level before
`k`" is literally the event that the array's own first `k` jumps form a word `q` with
`FirstRecord (extendPath q) k (ofRecState y)`. -/
theorem arrayFirstRecordCyl_eq_wordSet (N : ℕ) {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    (p : ℝ) (k : ℕ) :
    arrayFirstRecordCyl (N := N) p m k
      = {U : Array N |
          FirstRecord (extendPath (jumpWord p m k U)) k (ofRecState y)} := by
  ext U
  exact jbox_firstRecord_iff p hy (jumpWord p m k U) (mem_jbox_jumpWord p m k U)

/-- The first-record word condition is a word-level one: the word's own path reaches `1` at time
`k` and never exceeds `0` before. -/
theorem firstRecord_extendPath_iff (k : ℕ) (q : Fin k → JumpVec N)
    {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m) :
    FirstRecord (extendPath q) k (ofRecState y) ↔
      (∃ i, posAt (extendPath q) k i = 1) ∧
        ∀ t < k, ∀ i, posAt (extendPath q) t i ≤ 0 :=
  firstRecord_iff_posAt hy (extendPath q) k

/-- **The exact array mass of the first-record cylinder at time `k`**: a finite sum over *all*
first-record words of length `k`, each carrying the array's own box mass.  This is the multi-word
replacement of the single-word bridge. -/
theorem arrayMeasure_arrayFirstRecordCyl (N : ℕ) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m) (k : ℕ) :
    (arrayMeasure N) (arrayFirstRecordCyl (N := N) p m k)
      = ∑ q : Fin k → JumpVec N,
          if FirstRecord (extendPath q) k (ofRecState y)
            then ENNReal.ofReal (pathW p k q (startState (N := N) m)) else 0 := by
  rw [arrayFirstRecordCyl_eq_wordSet N hy p k,
    mass_wordSet p hp0 hp1 m k (fun q => FirstRecord (extendPath q) k (ofRecState y))]

/-- First-record cylinders at different times are disjoint: a walker at level `1` at time `k`
forbids the "nobody above the level" clause at any later time. -/
theorem disjoint_arrayFirstRecordCyl (N : ℕ) (p : ℝ) (m : ℕ) {k k' : ℕ} (h : k < k') :
    Disjoint (arrayFirstRecordCyl (N := N) p m k) (arrayFirstRecordCyl (N := N) p m k') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  obtain ⟨-, hle⟩ := (mem_arrayFirstRecordCyl_iff N p m k' U).mp h2
  obtain ⟨⟨i, hi⟩, -⟩ := (mem_arrayFirstRecordCyl_iff N p m k U).mp h1
  have := hle k h i
  omega

theorem measurableSet_arrayFirstRecordCyl (N : ℕ) {m : ℕ} {y : RecState N m}
    (hy : y ∈ srSet N m) (p : ℝ) (k : ℕ) :
    MeasurableSet (arrayFirstRecordCyl (N := N) p m k) := by
  rw [arrayFirstRecordCyl_eq_wordSet N hy p k]
  exact measurableSet_wordSet p m k (fun q => FirstRecord (extendPath q) k (ofRecState y))

/-- **The first positive excursion up to the horizon `L`, as a double word sum.**  The cylinders
of first record at times `1, …, L` are disjoint, so their union's array mass is the sum of the
per-`k` word sums of §3.  Words of different lengths appear in different summands: this is the
varying-length decomposition, not a fixed-`k` clamp. -/
theorem arrayMeasure_firstRecord_upto (N : ℕ) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m) (L : ℕ) :
    (arrayMeasure N) (⋃ k ∈ Finset.Icc 1 L, arrayFirstRecordCyl (N := N) p m k)
      = ∑ k ∈ Finset.Icc 1 L,
          ∑ q : Fin k → JumpVec N,
            if FirstRecord (extendPath q) k (ofRecState y)
              then ENNReal.ofReal (pathW p k q (startState (N := N) m)) else 0 := by
  rw [measure_biUnion_finset
    (fun a _ b _ hab => by
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact disjoint_arrayFirstRecordCyl N p m hlt
      · exact absurd heq hab
      · exact (disjoint_arrayFirstRecordCyl N p m hgt).symm)
    (fun b _ => measurableSet_arrayFirstRecordCyl N hy p b)]
  exact Finset.sum_congr rfl fun k _ => arrayMeasure_arrayFirstRecordCyl N hp0 hp1 hy k

/-! ### Non-vacuity of the first-record sum at `k = 1` -/

/-- The box mass of a word is positive at every `1/2 < p < 1`. -/
theorem pathW_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (q : Fin k → JumpVec N) : 0 < pathW p k q (startState (N := N) m) := by
  have hge := pathWFun_ge p (extendPath q) (le_of_lt hp0) (le_of_lt hp1) k
    (startState (N := N) m)
  rw [← pathW_eq_pathWFun_ext p m k q] at hge
  have hbase : (0 : ℝ) < 1 - p := by linarith
  have hpos : (0 : ℝ) < (1 - p) ^ (N * k) := pow_pos hbase _
  linarith

/-- **Non-vacuity: the first-record sum at `k = 1` is strictly positive.**  The one-letter
all-right word contributes a positive term, and it is a first-record word from every
`y ∈ srSet`.  So the decomposition of §3 is not an empty sum (contrast §5). -/
theorem arrayMeasure_arrayFirstRecordCyl_one_pos (N : ℕ) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m) (i₀ : Fin N) :
    0 < (arrayMeasure N) (arrayFirstRecordCyl (N := N) p m 1) := by
  rw [arrayMeasure_arrayFirstRecordCyl N hp0 hp1 hy 1]
  have hsingle := Finset.single_le_sum
    (f := fun q : Fin 1 → JumpVec N =>
      if FirstRecord (extendPath q) 1 (ofRecState y)
        then ENNReal.ofReal (pathW p 1 q (startState (N := N) m)) else 0)
    (s := Finset.univ)
    (fun i _ => by split_ifs <;> simp)
    (Finset.mem_univ (fun _ : Fin 1 => (fun _ => true : JumpVec N)))
  rw [if_pos (firstRecord_one_allRight hy i₀)] at hsingle
  have hterm : (0 : ℝ≥0∞) <
      ENNReal.ofReal (pathW p 1 (fun _ => (fun _ => true : JumpVec N)) (startState (N := N) m)) :=
    ENNReal.ofReal_pos.mpr (pathW_pos hp0 hp1 m 1 _)
  exact lt_of_lt_of_le hterm hsingle

/-! ## 4. The successor-word weight: splitting `pathWFun` at a block boundary -/

/-- Following a jump sequence for `k1 + k2` steps is following it for `k1` steps and then the
shifted sequence for `k2` steps. -/
theorem evolveFun_shift (m : ℕ) (u : ℕ → JumpVec N) (k1 : ℕ) :
    ∀ (k2 : ℕ) (s : State N m),
      evolveFun u (k1 + k2) s = evolveFun (fun n => u (k1 + n)) k2 (evolveFun u k1 s) := by
  intro k2
  induction k2 with
  | zero => intro s; rw [Nat.add_zero]; rfl
  | succ k2 ih =>
      intro s
      have h1 : k1 + (k2 + 1) = (k1 + k2) + 1 := Nat.add_succ k1 k2
      rw [h1, evolveFun_succ, ih, evolveFun_succ]

/-- **The successor-word weight identity.**  The weight of a word of length `k1 + k2` is the
weight of its first block times the weight of the shifted remainder measured from the successor
state `evolveFun u k1 s`, which is *determined by the first block alone*.  No independence and no
state average is used: this is the exact deterministic factorisation of the array's word mass. -/
theorem pathWFun_add (p : ℝ) (m : ℕ) (u : ℕ → JumpVec N) (k1 : ℕ) :
    ∀ (k2 : ℕ) (s : State N m),
      pathWFun p u (k1 + k2) s
        = pathWFun p u k1 s
          * pathWFun p (fun n => u (k1 + n)) k2 (evolveFun u k1 s) := by
  intro k2
  induction k2 with
  | zero =>
      intro s
      rw [Nat.add_zero]
      rw [show pathWFun p (fun n => u (k1 + n)) 0 (evolveFun u k1 s) = 1 from rfl, mul_one]
  | succ k2 ih =>
      intro s
      have h1 : k1 + (k2 + 1) = (k1 + k2) + 1 := Nat.add_succ k1 k2
      rw [h1, pathWFun_succ, ih, pathWFun_succ, evolveFun_shift m]
      ring

/-! ## 5. Scope: the single-word bridge is a one-step statement -/

/-- **`FirstRecord` and `PosSeqFin` are incompatible for `k ≥ 2`.**  A first-record word at time
`k ≥ 2` puts every walker at or below the level at time `1`, whereas a strictly positive word keeps
every walker strictly above the level at every time `1 ≤ n ≤ k`.  Consequently the joint
hypotheses of `FreshArrayBridge.array_jbox_mass_eq_segKpos` (and of
`array_jbox_mass_eq_hitW`, `arrayFirstRecordCyl_mass_eq_segKpos`) are satisfiable only for
`k = 1`; the earlier "single first-record word" identity is a genuine one-step statement and
cannot be summed over `k` to produce the varying-length decomposition. -/
theorem not_firstRecord_and_posSeqFin {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (hk : 2 ≤ k) (q : Fin k → JumpVec N) :
    ¬ (FirstRecord (extendPath q) k (ofRecState y) ∧ PosSeqFin (N := N) q) := by
  rintro ⟨hfr, hpos⟩
  cases N with
  | zero =>
      obtain ⟨i, -⟩ := hfr.1
      exact i.elim0
  | succ n =>
      obtain ⟨-, hle⟩ := (firstRecord_iff_posAt hy (extendPath q) k).mp hfr
      have h1 := hle 1 (by omega) ⟨0, Nat.succ_pos n⟩
      have h2 := (posWord_iff q).mp hpos 1 le_rfl (by omega) ⟨0, Nat.succ_pos n⟩
      omega

/-- The `k = 1` compatibility, as the exact scope of the single-word bridge: `FirstRecord` and
`PosSeqFin` do have a common instance precisely at one step. -/
theorem exists_firstRecord_and_posSeqFin (_hN : 0 < N) {m : ℕ} (hm : 1 ≤ m) (i₀ : Fin N) :
    ∃ (y : RecState N m) (q : Fin 1 → JumpVec N),
      y ∈ srSet N m ∧ FirstRecord (extendPath q) 1 (ofRecState y) ∧ PosSeqFin (N := N) q := by
  exact ⟨zeroRecState N m hm i₀, fun _ => (fun _ => true : JumpVec N),
    zeroRecState_mem_srSet N m hm i₀,
    firstRecord_one_allRight (zeroRecState_mem_srSet N m hm i₀) i₀,
    posSeqFin_one_allRight⟩

/-! ## 6. The right-hand side numbers of the finite-horizon residual, in word-sum form

`FinHorizonHstruct.FinHorizonFamily (★ K)` is the identity

`μ (Φ ⁻¹' (finStrict K ∩ B)) = π(F) · arrayMeasure {U | posPath U ∈ finStrict K ∩ B}`.

The two statements below compute the **array side** of `(★ K)` — the number on the right — as a
finite word sum with the array's own box masses, and then as the `π`-average over `srSet` that
appears in the `∫⁻`-form of `hstruct`.  Nothing here says anything about the chain side `μ`. -/

/-- The `π(F)`-multiple of the array horizon mass, as a word sum. -/
theorem pi_mul_arrayMeasure_finStrict_pattern {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (π : Measure (RecState N m)) (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    π (srSet N m)
        * (arrayMeasure N) {U : Array N |
            posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C}
      = π (srSet N m) * ∑ q : Fin K → JumpVec N,
          if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
            then ENNReal.ofReal (pathW p K q (startState (N := N) m)) else 0 := by
  rw [arrayMeasure_finStrict_pattern p hp0 hp1 m K C]

/-- **The array side of `(★ K)` in word-sum form**, already `π`-averaged over `F = srSet`:
the `π`-integral of the per-state horizon-`K` fresh masses (`FinHorizonHstruct.
finHorizon_mass_integral_srSet`) equals `π(F)` times the finite word sum of the array's own box
masses over the strictly positive words with pattern in `C`.  This is the exact number the
chain-side identity of `FinHorizonFamily` has to reproduce, with no measurability assumption on
`C`. -/
theorem finHorizon_mass_integral_srSet_wordSum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 1 ≤ m) (π : Measure (RecState N m)) (K : ℕ)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
          trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C} ∂π
      = π (srSet N m) * ∑ q : Fin K → JumpVec N,
          if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
            then ENNReal.ofReal (pathW p K q (startState (N := N) m)) else 0 := by
  rw [finHorizon_mass_integral_srSet hm p π K C,
    arrayMeasure_finStrict_pattern p hp0 hp1 m K C]

end SwarmArrayWords

/-! ## Axiom audit -/


