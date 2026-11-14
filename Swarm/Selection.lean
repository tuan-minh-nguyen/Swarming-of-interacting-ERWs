/-
Stage 1: the path-level selector and pairwise disjointness.
-/
import Swarm.ChainFactor
import Swarm.PaperV

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg SwarmChain
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace SwarmSel

variable {N : ℕ}

/-- **A regeneration at `(t,d)`**: the path sits at level `d` at time `t`, strictly below before,
and never returns to `d` or below afterwards. -/
def isRegen (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) : Prop :=
  pathRec t d X ∧ ∀ n, t < n → ∀ i, d < X n i

/-- `isRegen` agrees with the re-based future lying in the strict seed set `strictPos`. -/
theorem isRegen_iff_relFuture (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) :
    isRegen t d X ↔ pathRec t d X ∧ pathRel t d X ∈ strictPos (N := N) := by
  constructor
  · rintro ⟨hrec, hstay⟩
    refine ⟨hrec, ?_, ?_⟩
    · intro i
      show X (t + 0) i - d = 0
      rw [Nat.add_zero]
      have := hrec.2 i
      omega
    · intro n i
      show 0 < X (t + (n + 1)) i - d
      have := hstay (t + (n + 1)) (by omega) i
      omega
  · rintro ⟨hrec, hpos⟩
    obtain ⟨-, hpos'⟩ := mem_strictPos.mp hpos
    refine ⟨hrec, fun n hn i => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = t + (m + 1) := ⟨n - t - 1, by omega⟩
    have h := hpos' (m + 1) (by omega) i
    simp only [pathRel] at h
    omega

/-- **No earlier regeneration.** Every simultaneous record at a positive level `e < d` at a time
`u < t` is followed by a return to `≤ e` at some time in `(u, t]`. -/
def noEarlyRegen (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) : Prop :=
  ∀ e : ℤ, 1 ≤ e → e < d → ∀ u : ℕ, u < t → pathRec u e X →
    ∃ n : ℕ, u < n ∧ n ≤ t ∧ ∃ i, X n i ≤ e

/-- The paper's `C_{d,t}`: a simultaneous record at `(t,d)`, a strictly positive prefix up to `t`,
and no earlier positive regeneration level. -/
def Cpath (t : ℕ) (d : ℤ) : Set (ℕ → Fin N → ℤ) :=
  {X | pathRec t d X ∧ (∀ n, 0 < n → n ≤ t → ∀ i, 0 < X n i) ∧ noEarlyRegen t d X}

/-- **The selected first regeneration block**: `C_{d,t} ∩ V_{d,t}` of the paper. -/
def firstRegen (t : ℕ) (d : ℤ) : Set (ℕ → Fin N → ℤ) :=
  Cpath t d ∩ {X | pathRel t d X ∈ strictPos (N := N)}

theorem mem_firstRegen_iff {t : ℕ} {d : ℤ} {X : ℕ → Fin N → ℤ} :
    X ∈ firstRegen t d ↔ X ∈ Cpath t d ∧ isRegen t d X := by
  rw [firstRegen, Set.mem_inter_iff, Set.mem_ofPred_eq, Cpath, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hrec, h1, h2⟩, h3⟩
    exact ⟨⟨hrec, h1, h2⟩, (isRegen_iff_relFuture t d X).mpr ⟨hrec, h3⟩⟩
  · rintro ⟨⟨hrec, h1, h2⟩, h3⟩
    exact ⟨⟨hrec, h1, h2⟩, ((isRegen_iff_relFuture t d X).mp h3).2⟩

/-- At a fixed level a simultaneous record has a unique time. -/
theorem pathRec_time_unique (hN : 0 < N) {t t' : ℕ} {d : ℤ} {X : ℕ → Fin N → ℤ}
    (h : pathRec t d X) (h' : pathRec t' d X) : t = t' := by
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hN
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · have h1 := h'.1 t hlt i
    have h2 := h.2 i
    omega
  · exact heq
  · have h1 := h.1 t' hgt i
    have h2 := h'.2 i
    omega

/-- At a fixed time a simultaneous record has a unique level. -/
theorem pathRec_level_unique (hN : 0 < N) {t : ℕ} {d d' : ℤ} {X : ℕ → Fin N → ℤ}
    (h : pathRec t d X) (h' : pathRec t d' X) : d = d' := by
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hN
  have h1 := h.2 i
  have h2 := h'.2 i
  omega

/-- **Pairwise disjointness of the selected blocks at positive levels.**  Two distinct pairs
`(t,d)`, `(t',d')` of positive levels cannot both be the selected first block of one path. -/
theorem firstRegen_disjoint (hN : 0 < N) {t t' : ℕ} {d d' : ℤ} (hd : 1 ≤ d) (hd' : 1 ≤ d')
    (hne : (t, d) ≠ (t', d')) :
    Disjoint (firstRegen (N := N) t d) (firstRegen (N := N) t' d') := by
  rw [Set.disjoint_left]
  rintro X hx hx'
  rw [mem_firstRegen_iff] at hx hx'
  obtain ⟨⟨hrec, -, hno⟩, -, hstay⟩ := hx
  obtain ⟨⟨hrec', -, hno'⟩, -, hstay'⟩ := hx'
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hN
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · -- the later block at `d'` must return to `≤ d` before its own record
    rcases lt_trichotomy t t' with htt | htt | htt
    · obtain ⟨n, hn1, -, j, hle⟩ := hno' d hd hlt t htt hrec
      have := hstay n hn1 j
      omega
    · subst htt
      exact absurd (pathRec_level_unique hN hrec hrec') (by omega)
    · have h1 := hrec.1 t' htt i
      have h2 := hrec'.2 i
      omega
  · subst heq
    exact absurd (by simp [pathRec_time_unique hN hrec hrec']) hne
  · -- symmetric, with `d' < d`
    rcases lt_trichotomy t' t with htt | htt | htt
    · obtain ⟨n, hn1, -, j, hle⟩ := hno d' hd' hgt t' htt hrec'
      have := hstay' n hn1 j
      omega
    · subst htt
      exact absurd (pathRec_level_unique hN hrec hrec') (by omega)
    · have h1 := hrec'.1 t htt i
      have h2 := hrec.2 i
      omega


/-- The levels at which the path regenerates. -/
def regenLevels (X : ℕ → Fin N → ℤ) : Set ℤ := {e | ∃ t, isRegen t e X}

theorem isRegen.regenLevel {t : ℕ} {d : ℤ} {X : ℕ → Fin N → ℤ} (h : isRegen t d X) :
    d ∈ regenLevels X := ⟨t, h⟩

/-- **The selected first block is a `C_{d,t} ∩ V_{d,t}` block.** -/
theorem firstRegen_subset_strictPos {X : ℕ → Fin N → ℤ} (hX0 : ∀ i, X 0 i = 0)
    {t : ℕ} {d : ℤ} (hd : 1 ≤ d) (h : X ∈ firstRegen t d) : X ∈ strictPos (N := N) := by
  rw [firstRegen, Set.mem_inter_iff, Cpath, Set.mem_ofPred_eq] at h
  obtain ⟨⟨-, hpos, -⟩, hrel⟩ := h
  exact (strictPos_iff_prefix t d (by omega) X hrel).mpr ⟨hX0, hpos⟩

/-- **Exhaustion: the least regeneration level gives the selected block.**  A path in the seed set
`V` that regenerates at *some* positive level has a selected first block, namely at the least
positive regeneration level. -/
theorem exists_firstRegen (hN : 0 < N) {X : ℕ → Fin N → ℤ} (hV : X ∈ strictPos (N := N))
    {t : ℕ} {d : ℤ} (hd : 1 ≤ d) (hreg : isRegen t d X) :
    ∃ t' d', 1 ≤ d' ∧ X ∈ firstRegen t' d' := by
  classical
  obtain ⟨-, hpos⟩ := mem_strictPos.mp hV
  -- the least positive regeneration level
  have hex : ∃ k : ℕ, ((k : ℤ) + 1) ∈ regenLevels X := by
    refine ⟨(d.toNat - 1), ?_⟩
    have hd' : ((d.toNat - 1 : ℕ) : ℤ) + 1 = d := by
      have : (d.toNat : ℤ) = d := by omega
      omega
    rw [hd']
    exact hreg.regenLevel
  set k := Nat.find hex with hk
  have hspec : ((k : ℤ) + 1) ∈ regenLevels X := Nat.find_spec hex
  have hmin : ∀ j : ℕ, j < k → ((j : ℤ) + 1) ∉ regenLevels X := fun j hj => Nat.find_min hex hj
  obtain ⟨t', hreg'⟩ := hspec
  refine ⟨t', (k : ℤ) + 1, by omega, mem_firstRegen_iff.mpr ⟨⟨hreg'.1, ?_, ?_⟩, hreg'⟩⟩
  · -- strictly positive prefix
    intro n hn _ i
    exact hpos n hn i
  · -- no earlier regeneration
    intro e he1 hed u hu hrecu
    have hej : ((e - 1).toNat : ℤ) + 1 = e := by omega
    have hjk : (e - 1).toNat < k := by omega
    have hnot : ¬ ∃ s, isRegen s e X := by
      intro hs
      refine hmin _ hjk ?_
      rw [hej]
      exact hs
    have hnotstay : ¬ ∀ n, u < n → ∀ i, e < X n i := by
      intro hstay
      exact hnot ⟨u, hrecu, hstay⟩
    push Not at hnotstay
    obtain ⟨n, hn1, i, hni⟩ := hnotstay
    have hnle : n ≤ t' := by
      by_contra hcon
      have hlt : t' < n := by omega
      have := hreg'.2 n hlt i
      omega
    exact ⟨n, hn1, hnle, i, hni⟩

/-- **Exhaustion, union form**: over positive levels, the selected blocks are exactly the
simultaneous records from which the path never returns (existence of the next block). -/
theorem firstRegen_union (hN : 0 < N) {X : ℕ → Fin N → ℤ} (hV : X ∈ strictPos (N := N)) :
    (∃ t d, 1 ≤ d ∧ X ∈ firstRegen t d) ↔ (∃ t d, 1 ≤ d ∧ isRegen t d X) := by
  constructor
  · rintro ⟨t, d, hd, h⟩
    exact ⟨t, d, hd, (mem_firstRegen_iff.mp h).2⟩
  · rintro ⟨t, d, hd, h⟩
    exact exists_firstRegen hN hV hd h


/-! ### The selector on a prefix

`selPrefix t d` is the set of prefixes `q : Fin (t+1) → Fin N → ℤ` that extend to a path in
`Cpath t d`; `mem_selPrefix_iff` says that the extension condition is exactly `Cpath t d`, so
`selPrefix` is the `A` slot of `freshlaw_past_of_subset` for the selected block. -/

/-- A simultaneous record at level `e` at time `u`, read on a prefix `t > u`. -/
def recPrefix (t : ℕ) (q : Fin (t+1) → Fin N → ℤ) (u : Fin t) (e : ℤ) : Prop :=
  (∀ s : Fin t, s < u → ∀ i, q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < e) ∧
    ∀ i, q ⟨u.1, Nat.lt_succ_of_lt u.2⟩ i = e

/-- The paper's `C_{d,t}` read on the prefix. -/
def selPrefix (t : ℕ) (d : ℤ) : Set (Fin (t+1) → Fin N → ℤ) :=
  {q | (∀ s : Fin t, ∀ i, q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < d)
     ∧ (∀ i, q ⟨t, Nat.lt_succ_self t⟩ i = d)
     ∧ (∀ n : Fin t, ∀ i, 0 < q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i)
     ∧ ∀ e : {e : ℤ // 1 ≤ e ∧ e < d}, ∀ u : Fin t, recPrefix t q u e.1 →
         ∃ n : Fin t, u ≤ n ∧ ∃ i, q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i ≤ e.1}

/-- Conversion of a bounded `ℕ`-quantifier to a `Fin`-quantifier. -/
theorem forall_fin_iff {P : ℕ → Prop} {t : ℕ} :
    (∀ s : Fin t, P s.1) ↔ ∀ s, s < t → P s :=
  ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩

theorem forall_fin_succ_iff {P : ℕ → Prop} {t : ℕ} :
    (∀ n : Fin t, P (n.1 + 1)) ↔ ∀ n, 0 < n → n ≤ t → P n := by
  constructor
  · intro h n hn hn'
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact h ⟨m, by omega⟩
  · intro h n
    exact h (n.1 + 1) (by omega) (by omega)

/-- The prefix record condition is the path record condition at the same time. -/
theorem recPrefix_iff (t : ℕ) (u : Fin t) (e : ℤ) (X : ℕ → Fin N → ℤ) :
    recPrefix t (pathFst t X) u e ↔ pathRec u.1 e X := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i => h2 i⟩
    intro s hs i
    exact h1 ⟨s, lt_trans hs u.2⟩ hs i
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun i => h2 i⟩
    intro s hs i
    exact h1 s.1 hs i

/-- **The prefix set of the selected block is exactly `Cpath t d`.** -/
theorem mem_selPrefix_iff (t : ℕ) (d : ℤ) (X : ℕ → Fin N → ℤ) :
    pathFst t X ∈ selPrefix t d ↔ X ∈ Cpath t d := by
  simp only [selPrefix, Set.mem_ofPred_eq, Cpath, pathFst, pathRec]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨forall_fin_iff.mp h1, h2⟩,
      (forall_fin_succ_iff (P := fun n => ∀ i, 0 < X n i)).mp h3, ?_⟩
    intro e he1 he2 u hu hrec
    obtain ⟨n, hn1, i, hni⟩ := h4 ⟨e, he1, he2⟩ ⟨u, hu⟩ ((recPrefix_iff t ⟨u, hu⟩ e X).mpr hrec)
    have hn3 : u < n.1 + 1 := by
      have h2 : u ≤ n.1 := hn1
      omega
    have hn4 : n.1 + 1 ≤ t := by have := n.2; omega
    exact ⟨n.1 + 1, hn3, hn4, i, hni⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨forall_fin_iff.mpr h1, h2,
      (forall_fin_succ_iff (P := fun n => ∀ i, 0 < X n i)).mpr h3, ?_⟩
    rintro ⟨e, he1, he2⟩ u hrec
    obtain ⟨n, hn1, hn2, i, hni⟩ :=
      h4 e he1 he2 u.1 u.2 ((recPrefix_iff t u e X).mp hrec)
    have hm : 0 < n := by omega
    have hmt : n - 1 < t := by omega
    have hmu : u ≤ (⟨n - 1, hmt⟩ : Fin t) := by
      show u.1 ≤ n - 1
      omega
    have hval : ((⟨n - 1, hmt⟩ : Fin t).1 + 1) = n := by
      show n - 1 + 1 = n
      omega
    refine ⟨⟨n - 1, hmt⟩, hmu, i, ?_⟩
    rw [hval]
    exact hni


/-! ### Measurability of the selector on a prefix -/

/-- The record condition on a prefix is measurable. -/
theorem measurableSet_recPrefix (t : ℕ) (u : Fin t) (e : ℤ) :
    MeasurableSet {q : Fin (t+1) → Fin N → ℤ | recPrefix t q u e} := by
  have hm1 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ |
      ∀ s : Fin t, s < u → ∀ i, q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < e} := by
    have h1 : {q : Fin (t+1) → Fin N → ℤ | ∀ s : Fin t, s < u → ∀ i,
          q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < e}
        = ⋂ (s : {s : Fin t // s < u}), ⋂ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | q ⟨s.1.1, Nat.lt_succ_of_lt s.1.2⟩ i < e} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h s i => h s.1 s.2 i, fun h s hs i => h ⟨s, hs⟩ i⟩
    rw [h1]
    refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨s.1.1, Nat.lt_succ_of_lt s.1.2⟩ i) measurableSet_Iio
  have hm2 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ |
      ∀ i, q ⟨u.1, Nat.lt_succ_of_lt u.2⟩ i = e} := by
    have h2 : {q : Fin (t+1) → Fin N → ℤ | ∀ i, q ⟨u.1, Nat.lt_succ_of_lt u.2⟩ i = e}
        = ⋂ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | q ⟨u.1, Nat.lt_succ_of_lt u.2⟩ i = e} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h2]
    refine MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨u.1, Nat.lt_succ_of_lt u.2⟩ i) (measurableSet_singleton e)
  exact hm1.inter hm2

/-- **The selector set on the prefix is measurable.** -/
theorem measurableSet_selPrefix (t : ℕ) (d : ℤ) : MeasurableSet (selPrefix (N := N) t d) := by
  have hm1 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ | ∀ s : Fin t, ∀ i,
      q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < d} := by
    have h1 : {q : Fin (t+1) → Fin N → ℤ | ∀ s : Fin t, ∀ i,
          q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < d}
        = ⋂ (s : Fin t), ⋂ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i < d} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h1]
    refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨s.1, Nat.lt_succ_of_lt s.2⟩ i) measurableSet_Iio
  have hm2 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ | ∀ i, q ⟨t, Nat.lt_succ_self t⟩ i = d} := by
    have h2 : {q : Fin (t+1) → Fin N → ℤ | ∀ i, q ⟨t, Nat.lt_succ_self t⟩ i = d}
        = ⋂ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | q ⟨t, Nat.lt_succ_self t⟩ i = d} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h2]
    refine MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨t, Nat.lt_succ_self t⟩ i) (measurableSet_singleton d)
  have hm3 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ | ∀ n : Fin t, ∀ i,
      0 < q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i} := by
    have h3 : {q : Fin (t+1) → Fin N → ℤ | ∀ n : Fin t, ∀ i,
          0 < q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i}
        = ⋂ (n : Fin t), ⋂ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | 0 < q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h3]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i) measurableSet_Ioi
  have hm4 : MeasurableSet {q : Fin (t+1) → Fin N → ℤ |
      ∀ e : {e : ℤ // 1 ≤ e ∧ e < d}, ∀ u : Fin t, recPrefix t q u e.1 →
        ∃ n : Fin t, u ≤ n ∧ ∃ i, q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i ≤ e.1} := by
    have h4 : {q : Fin (t+1) → Fin N → ℤ |
          ∀ e : {e : ℤ // 1 ≤ e ∧ e < d}, ∀ u : Fin t, recPrefix t q u e.1 →
            ∃ n : Fin t, u ≤ n ∧ ∃ i, q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i ≤ e.1}
        = ⋂ (e : {e : ℤ // 1 ≤ e ∧ e < d}), ⋂ (u : Fin t),
            ({q : Fin (t+1) → Fin N → ℤ | recPrefix t q u e.1}ᶜ ∪
              {q : Fin (t+1) → Fin N → ℤ |
                ∃ n : Fin t, u ≤ n ∧ ∃ i, q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i ≤ e.1}) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · intro h e u
        by_cases hc : recPrefix t q u e.1
        · exact Or.inr (h e u hc)
        · exact Or.inl hc
      · intro h e u hc
        rcases h e u with h' | h'
        · exact absurd hc h'
        · exact h'
    rw [h4]
    refine MeasurableSet.iInter fun e => MeasurableSet.iInter fun u => ?_
    refine MeasurableSet.union (measurableSet_recPrefix t u e.1).compl ?_
    have h5 : {q : Fin (t+1) → Fin N → ℤ |
          ∃ n : Fin t, u ≤ n ∧ ∃ i, q ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ i ≤ e.1}
        = ⋃ (n : {n : Fin t // u ≤ n}), ⋃ (i : Fin N),
            {q : Fin (t+1) → Fin N → ℤ | q ⟨n.1.1 + 1, Nat.succ_lt_succ n.1.2⟩ i ≤ e.1} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun ⟨n, hn, i, hi⟩ => ⟨⟨n, hn⟩, i, hi⟩, fun ⟨⟨n, hn⟩, i, hi⟩ => ⟨n, hn, i, hi⟩⟩
    rw [h5]
    refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun i => ?_
    exact (by fun_prop : Measurable fun q : Fin (t+1) → Fin N → ℤ =>
      q ⟨n.1.1 + 1, Nat.succ_lt_succ n.1.2⟩ i) measurableSet_Iic
  exact hm1.inter (hm2.inter (hm3.inter hm4))


/-- `Cpath t d` is a path-level measurable set (it is the preimage of the selector prefix). -/
theorem measurableSet_Cpath (t : ℕ) (d : ℤ) : MeasurableSet (Cpath (N := N) t d) := by
  have h : Cpath (N := N) t d = pathFst t ⁻¹' selPrefix t d := by
    ext X
    exact (mem_selPrefix_iff t d X).symm
  rw [h]
  exact (measurable_pathFst t) (measurableSet_selPrefix t d)

/-- The selected first block is a path-level measurable set. -/
theorem measurableSet_firstRegen (t : ℕ) (d : ℤ) :
    MeasurableSet (firstRegen (N := N) t d) :=
  (measurableSet_Cpath t d).inter ((measurable_pathRel t d) measurableSet_strictPos)

/-! ### The selection on the actual array measure -/

section Array

variable {p : ℝ} {m : ℕ}

/-- The array-level event: the selected first block sits at `(t,d)` and the fresh path after it lies
in `B`. -/
def selSet (t : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) : Set (Array N) :=
  {U | pastProj p m t U ∈ selPrefix t d ∧
    relFuture p m U t d ∈ strictPos (N := N) ∩ B}

/-- The same event with the record condition written out — the shape `freshlaw_past_of_subset`
consumes. -/
theorem selSet_eq (t : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    selSet (N := N) (p := p) (m := m) t d B
      = {U : Array N | RecordAt p m U t d ∧ pastProj p m t U ∈ selPrefix t d ∧
          relFuture p m U t d ∈ strictPos (N := N) ∩ B} := by
  ext U
  simp only [selSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  have hpp := pastProj_eq_pathFst (N := N) p m U t
  constructor
  · rintro ⟨h1, h2⟩
    have hC : posPath p m U ∈ Cpath t d :=
      (mem_selPrefix_iff t d (posPath p m U)).mp (by rw [← hpp]; exact h1)
    simp only [Cpath, Set.mem_ofPred_eq] at hC
    exact ⟨(pathRec_iff p m U t d).mpr hC.1, h1, h2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

theorem measurableSet_selSet (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (selSet (N := N) (p := p) (m := m) t d B) := by
  have h1 : MeasurableSet {U : Array N | pastProj p m t U ∈ selPrefix t d} :=
    (measurable_pastProj p m t N) (measurableSet_selPrefix t d)
  have h2 : MeasurableSet {U : Array N |
      relFuture p m U t d ∈ strictPos (N := N) ∩ B} :=
    (measurable_relFuture p m t d N) (measurableSet_strictPos.inter hB)
  exact h1.inter h2

/-- **`freshlaw` for the selected block**: the mass of one selected block times the mass of the
fresh-tail event equals the mass of their joint occurrence. -/
theorem measure_selSet (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (selSet (N := N) (p := p) (m := m) t d B)
      = (arrayMeasure N) (recordPastSet (N := N) p m t d (selPrefix t d))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  rw [selSet_eq]
  exact freshlaw_past_of_subset p m t d measurableSet_strictPos strictPos_subset_nonnegPath
    (measurableSet_selPrefix t d) hB

/-- **Two different selected blocks cannot occur on the same array.** -/
theorem selSet_disjoint (hN : 0 < N) {t t' : ℕ} {d d' : ℤ} (hd : 1 ≤ d) (hd' : 1 ≤ d')
    (hne : (t, d) ≠ (t', d')) (B B' : Set (ℕ → Fin N → ℤ)) :
    Disjoint (selSet (N := N) (p := p) (m := m) t d B) (selSet (N := N) (p := p) (m := m) t' d' B') := by
  rw [Set.disjoint_left]
  rintro U ⟨h1, h2⟩ ⟨h1', h2'⟩
  have hpp := pastProj_eq_pathFst (N := N) p m U t
  have hpp' := pastProj_eq_pathFst (N := N) p m U t'
  have hmem : posPath p m U ∈ firstRegen t d ∩ firstRegen t' d' := by
    refine ⟨⟨(mem_selPrefix_iff t d _).mp ?_, ?_⟩,
      ⟨(mem_selPrefix_iff t' d' _).mp ?_, ?_⟩⟩
    · rw [← hpp]; exact h1
    · show pathRel t d (posPath p m U) ∈ strictPos (N := N)
      rw [← pathRel_relFuture p m U]
      exact h2.1
    · rw [← hpp']; exact h1'
    · show pathRel t' d' (posPath p m U) ∈ strictPos (N := N)
      rw [← pathRel_relFuture p m U]
      exact h2'.1
  exact Set.disjoint_left.mp (firstRegen_disjoint hN hd hd' hne) hmem.1 hmem.2

/-- The index `(t,g) ↦ (t, g+1)` of the selected blocks is injective. -/
theorem selIndex_injective : Function.Injective
    (fun i : ℕ × ℕ => (i.1, (i.2 : ℤ) + 1)) := by
  rintro ⟨t, g⟩ ⟨t', g'⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (by omega)

/-- **The selected block masses, summed over the selection.** -/
theorem tsum_selMass (hN : 0 < N) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (∑' i : ℕ × ℕ,
        (arrayMeasure N) (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1)))
          * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B})
      = (arrayMeasure N) (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B) := by
  have hdisj : Pairwise fun i j : ℕ × ℕ =>
      Disjoint (selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B)
        (selSet (N := N) (p := p) (m := m) j.1 ((j.2 : ℤ) + 1) B) := by
    rintro ⟨t, g⟩ ⟨t', g'⟩ hne
    refine selSet_disjoint hN (by omega) (by omega) ?_ _ _
    intro h
    exact hne (selIndex_injective h)
  have hmeas : ∀ i : ℕ × ℕ,
      MeasurableSet (selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B) := fun i =>
    measurableSet_selSet i.1 ((i.2 : ℤ) + 1) hB
  rw [measure_iUnion (f := fun i : ℕ × ℕ =>
    selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B) hdisj hmeas]
  exact tsum_congr fun i => (measure_selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) hB).symm

/-- The union of the selected blocks is the event "there is a selected block whose fresh path lies
in `B`". -/
theorem mem_iUnion_selSet {B : Set (ℕ → Fin N → ℤ)} {U : Array N} :
    U ∈ (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B)
      ↔ ∃ (t : ℕ) (g : ℕ), pastProj p m t U ∈ selPrefix t ((g : ℤ) + 1) ∧
          relFuture p m U t ((g : ℤ) + 1) ∈ strictPos (N := N) ∩ B := by
  simp only [Set.mem_iUnion, selSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨t, g⟩, h⟩
    exact ⟨t, g, h⟩
  · rintro ⟨t, g, h⟩
    exact ⟨(t, g), h⟩

/-- **The fresh law after the selected block**: the union is contained in the seed event. -/
theorem iUnion_selSet_subset (B : Set (ℕ → Fin N → ℤ)) :
    (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B)
      ⊆ {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  intro U hU
  obtain ⟨t, g, h1, h2⟩ := (mem_iUnion_selSet (p := p) (m := m)).mp hU
  have hpp := pastProj_eq_pathFst (N := N) p m U t
  have hC : posPath p m U ∈ Cpath t ((g : ℤ) + 1) :=
    (mem_selPrefix_iff t ((g : ℤ) + 1) _).mp (by rw [← hpp]; exact h1)
  have hreg : posPath p m U ∈ firstRegen t ((g : ℤ) + 1) := by
    refine ⟨hC, ?_⟩
    show pathRel t ((g : ℤ) + 1) (posPath p m U) ∈ strictPos (N := N)
    rw [← pathRel_relFuture p m U]
    exact h2.1
  exact firstRegen_subset_strictPos (fun i => posPath_zero p m U i) (by omega) hreg

/-- **The union form of `tsum_selMass`**: the total selected block mass times the seed mass is the
mass of the seed on which a selected block exists. -/
theorem tsum_selMass_univ (hN : 0 < N) :
    (∑' i : ℕ × ℕ,
        (arrayMeasure N) (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
      = (arrayMeasure N) (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ) := by
  rw [← ENNReal.tsum_mul_right]
  simpa only [Set.inter_univ] using tsum_selMass (p := p) (m := m) hN (B := univ) MeasurableSet.univ

/-- **The total selected mass is at most one** — the defect is exactly the mass of the seed event on
which no selected block exists. -/
theorem tsum_selMass_mul_le (hN : 0 < N) :
    (∑' i : ℕ × ℕ,
        (arrayMeasure N) (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
      ≤ (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  rw [tsum_selMass_univ hN]
  exact measure_mono (iUnion_selSet_subset univ)

/-- **The single selected block is literally `firstRegen t d` of the position path.** -/
theorem selSet_eq_firstRegen (t : ℕ) (d : ℤ) :
    selSet (N := N) (p := p) (m := m) t d univ
      = {U : Array N | posPath p m U ∈ firstRegen t d} := by
  ext U
  simp only [selSet, Set.mem_ofPred_eq, Set.inter_univ, firstRegen, Set.mem_inter_iff]
  have hpp := pastProj_eq_pathFst (N := N) p m U t
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_selPrefix_iff t d _).mp (by rw [← hpp]; exact h1), ?_⟩
    show pathRel t d (posPath p m U) ∈ strictPos (N := N)
    rw [← pathRel_relFuture p m U]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [hpp]; exact (mem_selPrefix_iff t d _).mpr h1, ?_⟩
    show relFuture p m U t d ∈ strictPos (N := N)
    rw [pathRel_relFuture p m U]
    exact h2

/-- **Re-basing at the selected block does not change the array measure**: the selected block
together with an arbitrary fresh-tail event is the path-level event "the path is selected at
`(t,d)` and its re-based future lies in `B`".  This is the self-similarity that makes the law of
the next block the same as the law of the first. -/
theorem selSet_eq_firstRegen_tail (t : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    selSet (N := N) (p := p) (m := m) t d B
      = {U : Array N | posPath p m U ∈ firstRegen t d ∧
          pathRel t d (posPath p m U) ∈ strictPos (N := N) ∩ B} := by
  ext U
  simp only [selSet, Set.mem_ofPred_eq, firstRegen, Set.mem_inter_iff]
  have hpp := pastProj_eq_pathFst (N := N) p m U t
  constructor
  · rintro ⟨h1, h2⟩
    have hC : posPath p m U ∈ Cpath t d :=
      (mem_selPrefix_iff t d _).mp (by rw [← hpp]; exact h1)
    have hS : relFuture p m U t d ∈ strictPos (N := N) := h2.1
    have hB : relFuture p m U t d ∈ B := h2.2
    refine ⟨⟨hC, ?_⟩, hS, ?_⟩
    · show pathRel t d (posPath p m U) ∈ strictPos (N := N)
      rw [← pathRel_relFuture p m U]
      exact hS
    · show pathRel t d (posPath p m U) ∈ B
      rw [← pathRel_relFuture p m U]
      exact hB
  · rintro ⟨⟨h1, h2⟩, -, h4⟩
    refine ⟨by rw [hpp]; exact (mem_selPrefix_iff t d _).mpr h1, ?_, ?_⟩
    · show relFuture p m U t d ∈ strictPos (N := N)
      rw [pathRel_relFuture p m U]
      exact h2
    · show relFuture p m U t d ∈ B
      rw [pathRel_relFuture p m U]
      exact h4

/-- **The block law is the same on the fresh path**: the mass of the selected block at `(t,d)`
together with the seed condition is the block mass times the seed mass.  This is the one-step
multiplication of `RegenIid.FreshBlocks` with the block index `(t,d)`. -/
theorem selMass_firstRegen (t : ℕ) (d : ℤ) (hd : 1 ≤ d) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ firstRegen t d}
      = (arrayMeasure N) (recordPastSet (N := N) p m t d (selPrefix t d))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have hset : {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ firstRegen t d}
      = selSet (N := N) (p := p) (m := m) t d univ := by
    rw [selSet_eq_firstRegen]
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨firstRegen_subset_strictPos (fun i => posPath_zero p m U i) hd h, h⟩
  rw [hset, measure_selSet (p := p) (m := m) t d MeasurableSet.univ, Set.inter_univ]

/-- **Exhaustion at the array level**: if the position path of the array regenerates at some
positive level, then the array lies in one of the selected blocks. -/
theorem exists_selSet_of_isRegen (hN : 0 < N) {U : Array N}
    (hV : posPath p m U ∈ strictPos (N := N))
    {t : ℕ} {d : ℤ} (hd : 1 ≤ d) (hreg : isRegen t d (posPath p m U)) :
    ∃ (t' : ℕ) (d' : ℤ), 1 ≤ d' ∧ U ∈ selSet (N := N) (p := p) (m := m) t' d' univ := by
  obtain ⟨t', d', hd', hfr⟩ := exists_firstRegen hN hV hd hreg
  refine ⟨t', d', hd', ?_⟩
  rw [selSet_eq_firstRegen]
  exact hfr

/-- **The summed selection identity for a general fresh-tail event**: the mass of "the selected
block exists and the fresh path after it lies in `B`" is the total block mass times the mass of
`strictPos ∩ B`. -/
theorem tsum_selMass_eq_iUnion (hN : 0 < N) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) B)
      = (∑' i : ℕ × ℕ,
          (arrayMeasure N)
            (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  rw [← tsum_selMass (p := p) (m := m) hN hB, ENNReal.tsum_mul_right]

/-- **Two successive selected blocks.**  The mass of "a selected first block exists and, after it, a
selected block at `(s,e)` whose own fresh future lies in `B`" is the total first-block mass times
the block mass at `(s,e)` times the seed-tail mass: the multiplicative form of `FreshBlocks` for two
successive blocks, with the same block-mass functional at both stages. -/
theorem tsum_selMass_two (hN : 0 < N) (s : ℕ) (e : ℤ) (he : 1 ≤ e)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1)
        {X : ℕ → Fin N → ℤ | X ∈ firstRegen s e ∧ pathRel s e X ∈ strictPos (N := N) ∩ B})
      = (∑' i : ℕ × ℕ, (arrayMeasure N)
            (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
        * ((arrayMeasure N) (recordPastSet (N := N) p m s e (selPrefix s e))
            * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B}) := by
  have hB' : MeasurableSet {X : ℕ → Fin N → ℤ |
      X ∈ firstRegen s e ∧ pathRel s e X ∈ strictPos (N := N) ∩ B} :=
    (measurableSet_firstRegen s e).inter
      ((measurable_pathRel s e) (measurableSet_strictPos.inter hB))
  rw [tsum_selMass_eq_iUnion (p := p) (m := m) hN hB']
  congr 1
  have hset : {U : Array N | posPath p m U ∈ strictPos (N := N) ∩
        {X : ℕ → Fin N → ℤ | X ∈ firstRegen s e ∧ pathRel s e X ∈ strictPos (N := N) ∩ B}}
      = {U : Array N | posPath p m U ∈ firstRegen s e ∧
          pathRel s e (posPath p m U) ∈ strictPos (N := N) ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨firstRegen_subset_strictPos (fun i => posPath_zero p m U i) he h1, h1, h2⟩
  rw [hset, ← selSet_eq_firstRegen_tail s e B, measure_selSet (p := p) (m := m) s e hB]

/-- **The normalisation the `FreshBlocks` interface needs.**  If almost every seed path has a
selected block (the downstream `D < ∞`), then the selected block masses sum to one, so the
normalised block mass is a probability law. -/
theorem tsum_selMass_eq_one (hN : 0 < N)
    (hfull : (arrayMeasure N)
        (⋃ i : ℕ × ℕ, selSet (N := N) (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) univ)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})
    (hne : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hnt : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    (∑' i : ℕ × ℕ,
        (arrayMeasure N) (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
      = 1 := by
  have h := tsum_selMass_univ (p := p) (m := m) hN
  rw [hfull] at h
  have h2 : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} *
        (∑' i : ℕ × ℕ, (arrayMeasure N)
          (recordPastSet (N := N) p m i.1 ((i.2 : ℤ) + 1) (selPrefix i.1 ((i.2 : ℤ) + 1))))
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} * 1 := by
    rw [mul_comm ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}), mul_one]
    exact h
  exact (ENNReal.mul_right_inj hne hnt).mp h2

end Array

end SwarmSel
