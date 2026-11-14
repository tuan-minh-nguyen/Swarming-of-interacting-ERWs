/-
# The genuine first regeneration: `(factor)` for the initial hit

`SegmentLaw.lean` proves the paper's `(freshlaw)` for a **fixed** regeneration point `(t,d)`:
given a regeneration at `(t,d)`, the post-regeneration segment is independent of the past with
law `P^*`.  The paper's initial-regeneration step uses something slightly different: the
*first* regeneration is at a *random* time and level, and `(factor)` must hold for that
random event, i.e. summed over `(d,t)`.

The point of this file is that the sum goes through, because the "no earlier regeneration"
refinement is itself a **low-block** condition at the record level.  Concretely, on
`RegenAt p m U t d` every walker is below `d` before `t` and equal to `d` at `t`, so:

* an earlier candidate `RegenAt p m U t' d'` with `t' < t` has `d' ≤ d`, and its no-return
  clause `∀ n, d' ≤ X_{t'+n}` is implied for `n ≥ t - t'` by the *later* record's own
  no-return clause `∀ m, d ≤ X_{t+m}` together with `d' ≤ d`;
* hence "no earlier regeneration" reduces to a condition on the positions at times `≤ t`
  only, i.e. to the low block `{levels < d}` — exactly the block on which the record event
  lives.

That is `NoEarlier` below, and the resulting factorisation is `freshlaw_first_of_subset`.
Summing the pairwise disjoint first-hit events then gives the paper's conditional statement
for the *random* first regeneration, `firstRegen_factor`.

Everything is for the actual i.i.d.-uniform array law `arrayMeasure`.  The only residual
hypothesis is the seed positivity `0 < P(posPath ∈ nonnegPath)` (paper `P(V) > 0`).
-/
import Swarm.SegmentLaw

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

set_option warn.classDefReducibility false
set_option linter.unusedVariables false

namespace SwarmSeg

variable {N : ℕ}

/-! ### "No earlier regeneration" is a condition on the prefix -/

/-- The positions up to time `t`, read as a total function of time (junk after `t`). -/
noncomputable def pastExtend (t : ℕ) (Y : Fin (t + 1) → Fin N → ℤ) : ℕ → Fin N → ℤ :=
  fun n i => if h : n ≤ t then Y ⟨n, Nat.lt_succ_of_le h⟩ i else 0

theorem pastExtend_apply {t : ℕ} {Y : Fin (t + 1) → Fin N → ℤ} {n : ℕ} (hn : n ≤ t)
    (i : Fin N) : pastExtend t Y n i = Y ⟨n, Nat.lt_succ_of_le hn⟩ i := by
  simp only [pastExtend, dif_pos hn]

theorem pastExtend_pastProj (p : ℝ) (m : ℕ) (t : ℕ) (U : Array N) {n : ℕ} (hn : n ≤ t)
    (i : Fin N) :
    pastExtend t (pastProj p m t U) n i = (trajectory p m U n).pos i := by
  rw [pastExtend_apply hn i]
  rfl

/-- The record condition, as a predicate on a path. -/
def RecordFun (X : ℕ → Fin N → ℤ) (t' : ℕ) (d' : ℤ) : Prop :=
  (∀ s, s < t' → ∀ i, X s i < d') ∧ ∀ i, X t' i = d'

/-- The bounded no-return condition: at the times `t' ≤ n ≤ t` the path is at least `d'`. -/
def BoundedStay (X : ℕ → Fin N → ℤ) (t' t : ℕ) (d' : ℤ) : Prop :=
  ∀ n, t' ≤ n → n ≤ t → ∀ i, d' ≤ X n i

theorem recordFun_iff (X : ℕ → Fin N → ℤ) (t' : ℕ) (d' : ℤ) :
    RecordFun X t' d' ↔ ((∀ s, s < t' → ∀ i, X s i < d') ∧ ∀ i, X t' i = d') :=
  Iff.rfl

theorem recordAt_iff_fun (p : ℝ) (m : ℕ) (U : Array N) (t' : ℕ) (d' : ℤ) :
    RecordAt p m U t' d' ↔ RecordFun (fun n i => (trajectory p m U n).pos i) t' d' :=
  Iff.rfl

/-- "No earlier regeneration", as a condition on a path.  Only the values at times `≤ t` are
read, so on a record at `(t,d)` this is a low-block condition at level `d`. -/
def NoEarlierFun (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) : Prop :=
  ∀ (t' : ℕ), t' < t → ∀ (d' : ℤ), ¬ (RecordFun X t' d' ∧ BoundedStay X t' t d')

/-- "No earlier regeneration" for the actual trajectory. -/
def NoEarlier (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (U : Array N) : Prop :=
  ∀ (t' : ℕ), t' < t → ∀ (d' : ℤ),
    ¬ (RecordFun (fun n i => (trajectory p m U n).pos i) t' d'
      ∧ BoundedStay (fun n i => (trajectory p m U n).pos i) t' t d')

theorem noEarlier_iff_fun (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (U : Array N) :
    NoEarlier p m t d U ↔ NoEarlierFun (N := N) t d (pastExtend t (pastProj p m t U)) := by
  constructor
  · intro h t' ht' d' hh
    obtain ⟨h1, h2⟩ := hh
    obtain ⟨h1a, h1b⟩ := h1
    refine h t' ht' d' ⟨⟨fun s hs i => ?_, fun i => ?_⟩, fun n hn1 hn2 i => ?_⟩
    · have hh := h1a s hs i
      rwa [pastExtend_pastProj p m t U (le_trans (le_of_lt hs) (le_of_lt ht')) i] at hh
    · have hh := h1b i
      rwa [pastExtend_pastProj p m t U (le_of_lt ht') i] at hh
    · have hh := h2 n hn1 hn2 i
      rwa [pastExtend_pastProj p m t U hn2 i] at hh
  · intro h t' ht' d' hh
    obtain ⟨h1, h2⟩ := hh
    obtain ⟨h1a, h1b⟩ := h1
    refine h t' ht' d' ⟨⟨fun s hs i => ?_, fun i => ?_⟩, fun n hn1 hn2 i => ?_⟩
    · rw [pastExtend_pastProj p m t U (le_trans (le_of_lt hs) (le_of_lt ht')) i]
      exact h1a s hs i
    · rw [pastExtend_pastProj p m t U (le_of_lt ht') i]
      exact h1b i
    · rw [pastExtend_pastProj p m t U hn2 i]
      exact h2 n hn1 hn2 i

/-- **On a regeneration, "no earlier regeneration" is literally "no earlier regeneration".**
The only point is that the no-return clause of an earlier candidate is implied, beyond the
later record's time, by the later record's own no-return clause and `d' ≤ d`. -/
theorem noEarlier_iff_regen {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (h : RegenAt p m U t d) :
    NoEarlier p m t d U ↔ ∀ (t' : ℕ), t' < t → ∀ (d' : ℤ), ¬ RegenAt p m U t' d' := by
  constructor
  · rintro hN t' ht' d' hreg
    obtain ⟨hr1, hr2⟩ := (recordFun_iff (fun n i => (trajectory p m U n).pos i) t' d').mp
      ((recordAt_iff_fun p m U t' d').mp (regenAt_recordAt hreg))
    have hbnd : BoundedStay (fun n i => (trajectory p m U n).pos i) t' t d' := by
      intro mm hm1 _ i
      have hstep := hreg.2.2 (mm - t') i
      rwa [Nat.add_sub_cancel' hm1] at hstep
    exact hN t' ht' d' ⟨(recordFun_iff _ t' d').mpr ⟨hr1, hr2⟩, hbnd⟩
  · rintro hN t' ht' d' hh
    obtain ⟨hh1, hh2⟩ := hh
    obtain ⟨h1, h2⟩ := (recordFun_iff (fun n i => (trajectory p m U n).pos i) t' d').mp hh1
    have hreg : RegenAt p m U t' d' := by
      refine ⟨h1, h2, fun n i => ?_⟩
      by_cases hn : t' + n ≤ t
      · exact hh2 (t' + n) (Nat.le_add_right _ _) hn i
      · have hle := hh2 t (le_of_lt ht') (le_refl t) i
        have hdd : d' ≤ d := by
          simpa [h.2.1 i] using hle
        have hge : d ≤ (trajectory p m U (t' + n)).pos i := by
          have hn' : t' + n = t + (t' + n - t) := by omega
          rw [hn']
          exact h.2.2 (t' + n - t) i
        omega
    exact hN t' ht' d' hreg

/-- Measurability of the bounded no-return condition. -/
theorem measurableSet_boundedAt (p : ℝ) (m : ℕ) (t : ℕ) (t' : ℕ) (d' : ℤ) :
    MeasurableSet {U : Array N | ∀ n, t' ≤ n → n ≤ t → ∀ i, d' ≤ (trajectory p m U n).pos i} := by
  have hset : {U : Array N | ∀ n, t' ≤ n → n ≤ t → ∀ i, d' ≤ (trajectory p m U n).pos i}
      = ⋂ (n : {n : ℕ // t' ≤ n ∧ n ≤ t}), ⋂ i : Fin N,
          {U : Array N | d' ≤ (trajectory p m U n.1).pos i} := by
    ext U
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h n i => h n.1 n.2.1 n.2.2 i, fun h n hn1 hn2 i => h ⟨n, hn1, hn2⟩ i⟩
  rw [hset]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun i =>
    (measurable_posPath_apply p m N n.1 i) (measurableSet_Ici (a := d'))))

/-- Measurability of "no earlier regeneration". -/
theorem measurableSet_noEarlier (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet {U : Array N | NoEarlier p m t d U} := by
  have hset : {U : Array N | NoEarlier p m t d U}
      = ⋂ x : {t' : ℕ // t' < t} × ℤ,
          {U : Array N | ¬ (RecordFun (fun n i => (trajectory p m U n).pos i) x.1.1 x.2 ∧
            BoundedStay (fun n i => (trajectory p m U n).pos i) x.1.1 t x.2)} := by
    ext U
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h x => h x.1.1 x.1.2 x.2, fun h t' ht' d' => h ⟨⟨t', ht'⟩, d'⟩⟩
  rw [hset]
  refine MeasurableSet.iInter (fun x => ?_)
  have hEq : {U : Array N | ¬ (RecordFun (fun n i => (trajectory p m U n).pos i) x.1.1 x.2 ∧
        BoundedStay (fun n i => (trajectory p m U n).pos i) x.1.1 t x.2)}
      = {U : Array N | RecordAt p m U x.1.1 x.2}ᶜ ∪
        {U : Array N | ∀ n, x.1.1 ≤ n → n ≤ t → ∀ i, x.2 ≤ (trajectory p m U n).pos i}ᶜ := by
    ext U
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_cases hA : RecordFun (fun n i => (trajectory p m U n).pos i) x.1.1 x.2
      · right
        intro hB
        exact h ⟨hA, hB⟩
      · left
        rw [recordAt_iff_fun]
        exact hA
    · rintro (h | h) hcon
      · exact h hcon.1
      · exact h hcon.2
  rw [hEq]
  exact (measurableSet_recordSet p m x.1.1 x.2).compl.union
    (measurableSet_boundedAt p m t x.1.1 x.2).compl

/-! ### The first-regeneration event as a low-block set -/

/-- The first regeneration, as a condition on the low block. -/
def lowFirstSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) : Set (lowSet (N := N) d → ℝ) :=
  {V | RecordAt p m (lowExtend (N := N) d V) t d ∧
    NoEarlier p m t d (lowExtend (N := N) d V)}

theorem mem_lowFirstSet {p : ℝ} {m : ℕ} {t : ℕ} {d : ℤ} {U : Array N} :
    (lowSet d).domRestrict U ∈ lowFirstSet (N := N) p m t d ↔
      RecordAt p m U t d ∧ NoEarlier p m t d U := by
  have hle := lowExtend_domRestrict_agree (N := N) d U
  have hles : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d →
      U (i, x, k) = lowExtend (N := N) d ((lowSet d).domRestrict U) (i, x, k) :=
    fun i x k hx => (hle i x k hx).symm
  constructor
  · rintro ⟨hrec, hN⟩
    refine ⟨(recordAt_congr (p := p) (m := m) (t := t) (d := d)
      (U := lowExtend (N := N) d ((lowSet d).domRestrict U)) (U' := U) hle).mp hrec, ?_⟩
    rw [noEarlier_iff_fun] at hN ⊢
    rw [pastProj_congr_of_low (U := lowExtend (N := N) d ((lowSet d).domRestrict U))
      (U' := U) hle hrec] at hN
    exact hN
  · rintro ⟨hrec, hN⟩
    refine ⟨(recordAt_congr (p := p) (m := m) (t := t) (d := d)
      (U := U) (U' := lowExtend (N := N) d ((lowSet d).domRestrict U)) hles).mp hrec, ?_⟩
    rw [noEarlier_iff_fun] at hN ⊢
    rw [← pastProj_congr_of_low (U := U) (U' := lowExtend (N := N) d ((lowSet d).domRestrict U))
      hles hrec]
    exact hN

theorem measurableSet_lowFirstSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet (lowFirstSet (N := N) p m t d) :=
  (measurable_lowExtend d) ((measurableSet_recordSet p m t d).inter
    (measurableSet_noEarlier p m t d))

/-- The event "record at `(t,d)`, no earlier regeneration, segment in `S ∩ B`", as a low-block
set intersected with a high-block set. -/
theorem firstRegen_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {S : Set (ℕ → Fin N → ℤ)}
    (hSsub : S ⊆ nonnegPath (N := N)) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U ∧ relFuture p m U t d ∈ S ∩ B}
      = (lowSet d).domRestrict ⁻¹' lowFirstSet (N := N) p m t d
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d (S ∩ B) := by
  rw [highFuture_eq p m d (S ∩ B)]
  ext U
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hrec, hN, hS1, hB1⟩
    have hnon : relFuture p m U t d ∈ nonnegPath (N := N) := hSsub hS1
    simp only [nonnegPath, Set.mem_ofPred_eq, relFuture] at hnon
    have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
      intro n i; have := hnon n i; omega
    have heq : relFuture p m U t d = posPath p m (levelShift d U) :=
      relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
    rw [heq] at hS1 hB1
    exact ⟨mem_lowFirstSet.mpr ⟨hrec, hN⟩, hSsub hS1, hS1, hB1⟩
  · rintro ⟨hL, hnon, hS1, hB1⟩
    obtain ⟨hrec, hN⟩ := mem_lowFirstSet.mp hL
    have hreg : RegenAt p m U t d := (regenAt_iff p m U t d).mpr ⟨hrec, hnon⟩
    have heq : relFuture p m U t d = posPath p m (levelShift d U) := relFuture_eq p m U hreg
    refine ⟨hrec, hN, ?_⟩
    rw [heq]
    exact ⟨hS1, hB1⟩

/-- **`(freshlaw)` at the first regeneration point**: for every `(t,d)`, conditioned on the
record at `(t,d)` and on there being no earlier regeneration, the segment law is the fresh
law restricted to `S`. -/
theorem freshlaw_first_of_subset (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {S : Set (ℕ → Fin N → ℤ)} (hS : MeasurableSet S) (hSsub : S ⊆ nonnegPath (N := N))
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U ∧
        relFuture p m U t d ∈ S ∩ B}
      = (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hstep : {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U ∧
        relFuture p m U t d ∈ S ∩ B}
      = (lowSet d).domRestrict ⁻¹' lowFirstSet (N := N) p m t d
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d (S ∩ B) :=
    firstRegen_eq p m t d hSsub B
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) (measurableSet_lowFirstSet p m t d)
    (measurableSet_highFutureSet (N := N) p m d (hS.inter hB))
  have hhigh := highFuture_measure p m d (hS.inter hB)
  have hset : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ (S ∩ B)}
      = {U : Array N | posPath p m U ∈ S ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨hSsub h1, h1, h2⟩
  have hlow : {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U}
      = (lowSet d).domRestrict ⁻¹' lowFirstSet (N := N) p m t d := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact (mem_lowFirstSet (p := p) (m := m) (t := t) (d := d) (U := U)).symm
  rw [hP, hstep, hblock, ← hlow, ← hP, hhigh, hset]


/-! ### The first regeneration, and the sum over the disjoint first-hit points -/

/-- The first regeneration event: a regeneration, and none before it. -/
def FirstRegen (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (U : Array N) : Prop :=
  RegenAt p m U t d ∧ NoEarlier p m t d U

theorem measurableSet_firstRegen (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet {U : Array N | FirstRegen p m t d U} :=
  (measurableSet_regenSet p m t d).inter (measurableSet_noEarlier p m t d)

/-- The first regeneration with its segment in `B`, in the shape produced by the block
factorisation. -/
def firstSegSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (B : Set (ℕ → Fin N → ℤ)) : Set (Array N) :=
  {U | RecordAt p m U t d ∧ NoEarlier p m t d U ∧
    relFuture p m U t d ∈ nonnegPath (N := N) ∩ B}

theorem measurableSet_firstSegSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (firstSegSet (N := N) p m t d B) := by
  have hEq : firstSegSet (N := N) p m t d B
      = recordSet (N := N) p m t d ∩ {U | NoEarlier p m t d U} ∩
        (fun U => relFuture p m U t d) ⁻¹' (nonnegPath (N := N) ∩ B) := by
    ext U
    simp only [firstSegSet, recordSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hEq]
  exact ((measurableSet_recordSet p m t d).inter (measurableSet_noEarlier p m t d)).inter
    ((measurable_relFuture p m t d N) (measurableSet_nonnegPath.inter hB))

/-- The first-regeneration event, in the "segment in `B`" form of `firstSegSet`. -/
theorem firstSegSet_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    firstSegSet (N := N) p m t d B
      = {U : Array N | FirstRegen p m t d U ∧ relFuture p m U t d ∈ B} := by
  ext U
  constructor
  · rintro ⟨hrec, hN, hB1, hB2⟩
    have hnon : posPath p m (levelShift d U) ∈ nonnegPath (N := N) := by
      have h := hB1
      simp only [nonnegPath, Set.mem_ofPred_eq, relFuture] at h
      have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
        intro n i; have := h n i; omega
      have heq : relFuture p m U t d = posPath p m (levelShift d U) :=
        relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
      rw [← heq]; exact hB1
    have hreg : RegenAt p m U t d := (regenAt_iff p m U t d).mpr ⟨hrec, hnon⟩
    exact ⟨⟨hreg, hN⟩, hB2⟩
  · rintro ⟨⟨hreg, hN⟩, hB⟩
    have hiff := (regenAt_iff p m U t d).mp hreg
    have heq : relFuture p m U t d = posPath p m (levelShift d U) := relFuture_eq p m U hreg
    exact ⟨regenAt_recordAt hreg, hN, by rw [heq]; exact hiff.2, hB⟩

/-- The first-regeneration event is `firstSegSet` with the segment unconstrained. -/
theorem firstRegenSet_eq_firstSegSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    {U : Array N | FirstRegen p m t d U} = firstSegSet (N := N) p m t d univ := by
  rw [firstSegSet_eq]
  ext U
  simp

/-- **First-hit points are pairwise disjoint.** -/
theorem disjoint_firstSegSet (p : ℝ) (m : ℕ) (B : Set (ℕ → Fin N → ℤ)) (hN : 0 < N)
    {x y : ℕ × ℤ} (h : x ≠ y) :
    Disjoint (firstSegSet (N := N) p m x.1 x.2 B) (firstSegSet (N := N) p m y.1 y.2 B) := by
  rw [Set.disjoint_left]
  intro U h1 h2
  rw [firstSegSet_eq] at h1 h2
  obtain ⟨⟨hreg1, hN1⟩, -⟩ := h1
  obtain ⟨⟨hreg2, hN2⟩, -⟩ := h2
  obtain ⟨t, d⟩ := x
  obtain ⟨t', d'⟩ := y
  rcases lt_trichotomy t t' with htt | htt | htt
  · exact ((noEarlier_iff_regen hreg2).mp hN2 t htt d) hreg1
  · subst htt
    have h1' : (trajectory p m U t).pos (⟨0, hN⟩ : Fin N) = d := hreg1.2.1 _
    have h2' : (trajectory p m U t).pos (⟨0, hN⟩ : Fin N) = d' := hreg2.2.1 _
    have hdd : d = d' := by omega
    exact h (by simp [hdd])
  · exact ((noEarlier_iff_regen hreg1).mp hN1 t' htt d') hreg2

/-- **Mass of the first regeneration.** -/
theorem firstRegen_mass (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    (arrayMeasure N) {U : Array N | FirstRegen p m t d U}
      = (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ NoEarlier p m t d U}
        * (arrayMeasure N) (seedSet p m N) := by
  have h := freshlaw_first_of_subset (N := N) p m t d measurableSet_nonnegPath (subset_refl _)
    (B := univ) MeasurableSet.univ
  have hset : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ univ} = seedSet p m N := by
    ext U; simp [seedSet]
  rw [hset] at h
  rw [firstRegenSet_eq_firstSegSet]
  exact h

/-- **The paper's `(factor)` for the initial regeneration.**  Summing the pairwise disjoint
first-hit points, the law of the segment after the *random* first regeneration is `P^*`:

  `P(first regeneration, segment ∈ B) = P(first regeneration) · P^*(B)`,
-/
theorem firstRegen_factor (p : ℝ) (m : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ x : ℕ × ℤ, firstSegSet (N := N) p m x.1 x.2 B)
      = (arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U})
        * Pstar p m N B := by
  have htop := seedSet_ne_top p m N
  set s0 := (arrayMeasure N) (seedSet p m N) with hs0
  have hseg : ∀ x : ℕ × ℤ, (arrayMeasure N) (firstSegSet (N := N) p m x.1 x.2 B)
      = (arrayMeasure N) {U : Array N | RecordAt p m U x.1 x.2 ∧ NoEarlier p m x.1 x.2 U}
        * (arrayMeasure N) (seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B) := by
    intro x
    have h := freshlaw_first_of_subset (N := N) p m x.1 x.2 measurableSet_nonnegPath
      (subset_refl _) hB
    have hset : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B}
        = seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B := by
      ext U; simp [seedSet]
    rw [hset] at h
    exact h
  have hmass : ∀ x : ℕ × ℤ, (arrayMeasure N) {U : Array N | FirstRegen p m x.1 x.2 U}
      = (arrayMeasure N) {U : Array N | RecordAt p m U x.1 x.2 ∧ NoEarlier p m x.1 x.2 U}
        * s0 := by
    intro x
    have h := firstRegen_mass (N := N) p m x.1 x.2
    rw [hs0]
    exact h
  have hdisj : Pairwise (fun x y : ℕ × ℤ =>
      Disjoint (firstSegSet (N := N) p m x.1 x.2 B) (firstSegSet (N := N) p m y.1 y.2 B)) :=
    fun x y hxy => disjoint_firstSegSet p m B hN hxy
  have hdisj' : Pairwise (fun x y : ℕ × ℤ =>
      Disjoint {U : Array N | FirstRegen p m x.1 x.2 U}
        {U : Array N | FirstRegen p m y.1 y.2 U}) := by
    intro x y hxy
    rw [firstRegenSet_eq_firstSegSet, firstRegenSet_eq_firstSegSet]
    exact disjoint_firstSegSet p m univ hN hxy
  have hmeas : ∀ x : ℕ × ℤ, MeasurableSet (firstSegSet (N := N) p m x.1 x.2 B) :=
    fun x => measurableSet_firstSegSet p m x.1 x.2 hB
  have hmeas' : ∀ x : ℕ × ℤ, MeasurableSet {U : Array N | FirstRegen p m x.1 x.2 U} :=
    fun x => measurableSet_firstRegen p m x.1 x.2
  rw [MeasureTheory.measure_iUnion hdisj hmeas, MeasureTheory.measure_iUnion hdisj' hmeas']
  simp only [hseg, hmass]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
  have hQ : Pstar p m N B
      = s0⁻¹ * ((arrayMeasure N) (seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B)) := by
    rw [Pstar, Measure.smul_apply, freshLaw, Measure.map_apply (measurable_posPath p m N) hB,
      Measure.restrict_apply ((measurable_posPath p m N) hB), smul_eq_mul, Set.inter_comm]
  rw [hQ]
  have halg : ∀ (A Q : ℝ≥0∞), A * Q = A * s0 * (s0⁻¹ * Q) := by
    intro A Q
    rw [mul_assoc A s0 (s0⁻¹ * Q), ← mul_assoc s0 s0⁻¹ Q,
      ENNReal.mul_inv_cancel hV htop, one_mul]
  exact halg _ _


/-! ### The paper's `(factor)` in the user-facing shape -/

/-- **The paper's conditional statement for the initial regeneration**, in the exact
`A ∩ Φ⁻¹ B` shape used by the Kac formula: the first regeneration, with the segment in `B`,
has mass `P(first regeneration) · P^*(B)`. -/
theorem firstRegen_hfac (p : ℝ) (m : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ x : ℕ × ℤ,
        {U : Array N | FirstRegen p m x.1 x.2 U ∧ relFuture p m U x.1 x.2 ∈ B})
      = (arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U})
        * Pstar p m N B := by
  have hset : (⋃ x : ℕ × ℤ,
      {U : Array N | FirstRegen p m x.1 x.2 U ∧ relFuture p m U x.1 x.2 ∈ B})
      = ⋃ x : ℕ × ℤ, firstSegSet (N := N) p m x.1 x.2 B := by
    refine Set.iUnion_congr fun x => ?_
    exact (firstSegSet_eq p m x.1 x.2 B).symm
  rw [hset]
  exact firstRegen_factor p m hN hV hB

/-- The first regeneration happens at most once, almost surely: the first-hit points are
pairwise disjoint. -/
theorem firstRegen_pairwise_disjoint_sets (p : ℝ) (m : ℕ) (hN : 0 < N)
    {x y : ℕ × ℤ} (h : x ≠ y) :
    Disjoint {U : Array N | FirstRegen p m x.1 x.2 U}
      {U : Array N | FirstRegen p m y.1 y.2 U} := by
  rw [firstRegenSet_eq_firstSegSet, firstRegenSet_eq_firstSegSet]
  exact disjoint_firstSegSet p m univ hN h


/-- **Mass of the first-regeneration event**, as a sum over the disjoint first-hit points. -/
theorem firstRegenSet_mass (p : ℝ) (m : ℕ) (hN : 0 < N) :
    (arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U})
      = (∑' x : ℕ × ℤ, (arrayMeasure N) {U : Array N |
          RecordAt p m U x.1 x.2 ∧ NoEarlier p m x.1 x.2 U})
        * (arrayMeasure N) (seedSet p m N) := by
  have hdisj' : Pairwise (fun x y : ℕ × ℤ =>
      Disjoint {U : Array N | FirstRegen p m x.1 x.2 U}
        {U : Array N | FirstRegen p m y.1 y.2 U}) :=
    fun x y hxy => firstRegen_pairwise_disjoint_sets p m hN hxy
  have hmeas' : ∀ x : ℕ × ℤ, MeasurableSet {U : Array N | FirstRegen p m x.1 x.2 U} :=
    fun x => measurableSet_firstRegen p m x.1 x.2
  rw [MeasureTheory.measure_iUnion hdisj' hmeas']
  simp only [firstRegen_mass]
  rw [ENNReal.tsum_mul_right]

/-- **The paper's `P(X ∈ B | A) = P^*(B)` for the initial regeneration**, in divided form. -/
theorem firstRegen_cond_law (p : ℝ) (m : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0)
    (hA : (arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U}) ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    ((arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U}))⁻¹ *
        ((arrayMeasure N) (⋃ x : ℕ × ℤ,
          {U : Array N | FirstRegen p m x.1 x.2 U ∧ relFuture p m U x.1 x.2 ∈ B}))
      = Pstar p m N B := by
  have htop : (arrayMeasure N) (⋃ x : ℕ × ℤ, {U : Array N | FirstRegen p m x.1 x.2 U}) ≠ ⊤ :=
    measure_ne_top _ _
  rw [firstRegen_hfac p m hN hV hB, ← mul_assoc, ENNReal.inv_mul_cancel hA htop, one_mul]


/-- **`(factor)` at a fixed regeneration point, in the unconditional `P^*` form**: for every
`(t,d)` and every measurable set `B` of segments,

  `P(regeneration at (t,d), segment ∈ B) = P(regeneration at (t,d)) · P^*(B)`.

This is the `hfac` shape consumed by the Kac formula, with no conditioning and no division. -/
theorem cond_regen_hfac (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (hV : (arrayMeasure N) (seedSet p m N) ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | RegenAt p m U t d} * Pstar p m N B := by
  have htop := seedSet_ne_top p m N
  set s0 := (arrayMeasure N) (seedSet p m N) with hs0
  have hset : {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ univ ∧
          relFuture p m U t d ∈ nonnegPath (N := N) ∩ B} := by
    rw [← regenPast_set_eq p m t d univ B]
    ext U
    simp
  have hrec : recordPastSet (N := N) p m t d univ = recordSet (N := N) p m t d := by
    ext U; simp [recordPastSet, recordSet]
  have hQ : Pstar p m N B
      = s0⁻¹ * ((arrayMeasure N) (seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B)) := by
    rw [Pstar, Measure.smul_apply, freshLaw, Measure.map_apply (measurable_posPath p m N) hB,
      Measure.restrict_apply ((measurable_posPath p m N) hB), smul_eq_mul, Set.inter_comm]
  have hseed : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B}
      = seedSet p m N ∩ (fun U : Array N => posPath p m U) ⁻¹' B := by
    ext U; simp [seedSet]
  have hfac := freshlaw_past (N := N) p m t d (A := univ) MeasurableSet.univ hB
  have hsEq : (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} = s0 := by
    rw [hs0]; rfl
  have halg : ∀ (A Q : ℝ≥0∞), A * Q = A * s0 * (s0⁻¹ * Q) := by
    intro A Q
    rw [mul_assoc A s0 (s0⁻¹ * Q), ← mul_assoc s0 s0⁻¹ Q,
      ENNReal.mul_inv_cancel hV htop, one_mul]
  rw [hset, hfac, hrec, hseed, hQ, regenAt_measure_factor (N := N) p m t d, hsEq]
  exact halg _ _

end SwarmSeg
