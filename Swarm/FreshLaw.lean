/-
# The independence half of `(freshlaw)`: the record event is a low-block event

`Swarm/RestartRecord.lean` (accepted, verified) proves the *deterministic*
translated-segment theorem: on the regeneration event `RegenAt p m U t d` the relative future
`n ↦ (X^i_{t+n} - d)` **is** the fresh position path driven by the level-shifted array
`levelShift d U`.  It also isolates the two facts that a probabilistic `(freshlaw)` needs:

* the record part `RecordAt p m U t d` depends only on the array coordinates of level `< d`;
* the relative future depends only on the coordinates of level `≥ d`.

What was missing is the measure-theoretic separation of those two blocks.  This file supplies
it, using `SwarmBlock.block_measure_inter` (countable block independence for the exact
infinite-product array law `Swarming.Uniform.arrayMeasure`).

## Main results

For the actual array law `P = arrayMeasure N` on `Fin N × ℤ × ℕ → ℝ`:

* `regenAt_iff`: `RegenAt p m U t d ↔ RecordAt p m U t d ∧ posPath p m (levelShift d U) ∈ nonnegPath`
  (the no-return condition is *exactly* "the fresh path stays nonnegative");
* `regenSet_eq`: the regeneration event is `lowProj ⁻¹' record ∩ highProj ⁻¹' (fresh path in
  `nonnegPath ∩ B`)` — a product of a low-block and a high-block set;
* `freshlaw`: the **unconditional product factorization**
  `P(RegenAt ∧ relFuture ∈ B) = P(RecordAt) * P(posPath ∈ nonnegPath ∩ B)`;
* `regenAt_measure_factor`: `P(RegenAt) = P(RecordAt) * P(posPath ∈ nonnegPath)`;
* `restrict_regen_map`: the conditioned law of the translated future,
  `(P ↾ {RegenAt}).map relFuture = P(RecordAt) • ((P ↾ nonnegPath).map posPath)`,
  which is the paper's "given a regeneration the translated future has the fresh law",
  stated without dividing;
* `freshlaw_hfac`: the paper's `(factor)` for a single record time, given the seed probability
  `P(posPath ∈ nonnegPath) ≠ 0`.

Residual hypothesis, stated exactly: `0 < P(posPath ∈ nonnegPath)`.  That positivity is the
paper's `P(V) > 0`; it is *not* proved here (it is the seed-probability problem).  Everything
else in `(freshlaw)` is unconditional.

No proof holes and no user-declared axioms: see `FreshLawAudit.lean`.
-/
import Swarm.BlockIndep
import Swarm.RestartRecord

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart
open scoped ENNReal

set_option warn.classDefReducibility false

namespace SwarmFresh

variable {N : ℕ}

/-! ### The two blocks of array coordinates -/

/-- The low block: array coordinates of lattice level strictly below `d`. -/
def lowSet (d : ℤ) : Set (Fin N × ℤ × ℕ) := {p | p.2.1 < d}

/-- The high block: array coordinates of lattice level at least `d`. -/
def highSet (d : ℤ) : Set (Fin N × ℤ × ℕ) := {p | d ≤ p.2.1}

theorem disjoint_lowSet_highSet (d : ℤ) :
    Disjoint (lowSet (N := N) d) (highSet (N := N) d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  simp only [lowSet, highSet, Set.mem_ofPred_eq] at hp hq
  omega

/-! ### Junk extensions of the two blocks

Both extensions fill the complementary block with `0`; the junk is never read on the event of
interest (`agreeBelow_traj` for the record, `posPath_shift_congr` for the future). -/

/-- Extend a function of the low block to the whole array, filling the high coordinates with `0`. -/
noncomputable def lowExtend (d : ℤ) (V : lowSet (N := N) d → ℝ) : Array N :=
  fun p => if h : p.2.1 < d then V ⟨p, h⟩ else 0

/-- Extend a function of the high block to the whole array, filling the low coordinates with `0`. -/
noncomputable def highExtend (d : ℤ) (W : highSet (N := N) d → ℝ) : Array N :=
  fun p => if h : d ≤ p.2.1 then W ⟨p, h⟩ else 0

/-- The low extension agrees with the array at every low coordinate. -/
theorem lowExtend_domRestrict_agree (d : ℤ) (U : Array N) :
    ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d →
      lowExtend (N := N) d ((lowSet d).domRestrict U) (i, x, k) = U (i, x, k) := by
  intro i x k hx
  simp only [lowExtend, dif_pos hx]
  rfl

/-- The high extension agrees with the array at every high coordinate. -/
theorem highExtend_domRestrict_agree (d : ℤ) (U : Array N) :
    ∀ (i : Fin N) (x : ℤ) (k : ℕ), d ≤ x →
      highExtend (N := N) d ((highSet d).domRestrict U) (i, x, k) = U (i, x, k) := by
  intro i x k hx
  simp only [highExtend, dif_pos hx]
  rfl

/-! ### Measurability of the extensions -/

theorem measurable_lowExtend (d : ℤ) : Measurable (lowExtend (N := N) d) := by
  refine measurable_pi_iff.mpr (fun p => ?_)
  by_cases h : p.2.1 < d
  · have hp : (fun V : lowSet (N := N) d → ℝ => lowExtend d V p) = fun V => V ⟨p, h⟩ := by
      funext V; simp only [lowExtend, dif_pos h]
    rw [hp]
    exact measurable_pi_apply _
  · have hp : (fun V : lowSet (N := N) d → ℝ => lowExtend d V p) = fun _ => (0 : ℝ) := by
      funext V; simp only [lowExtend, dif_neg h]
    rw [hp]
    exact measurable_const

theorem measurable_highExtend (d : ℤ) : Measurable (highExtend (N := N) d) := by
  refine measurable_pi_iff.mpr (fun p => ?_)
  by_cases h : d ≤ p.2.1
  · have hp : (fun W : highSet (N := N) d → ℝ => highExtend d W p) = fun W => W ⟨p, h⟩ := by
      funext W; simp only [highExtend, dif_pos h]
    rw [hp]
    exact measurable_pi_apply _
  · have hp : (fun W : highSet (N := N) d → ℝ => highExtend d W p) = fun _ => (0 : ℝ) := by
      funext W; simp only [highExtend, dif_neg h]
    rw [hp]
    exact measurable_const

/-! ### Coordinate measurability -/

theorem measurable_posPath_apply (p : ℝ) (m : ℕ) (N : ℕ) (n : ℕ) (i : Fin N) :
    Measurable fun U : Array N => (posPath p m U) n i := by
  have h1 : Measurable fun X : ℕ → Fin N → ℤ => X n i := by fun_prop
  exact h1.comp (measurable_posPath p m N)

/-! ### The path `nonnegPath`, and its measurability -/

/-- The fresh path never goes below the starting level. -/
def nonnegPath : Set (ℕ → Fin N → ℤ) := {X | ∀ n i, 0 ≤ X n i}

theorem nonnegPath_eq :
    nonnegPath (N := N) = ⋂ n, ⋂ i, {X : ℕ → Fin N → ℤ | 0 ≤ X n i} := by
  ext X
  simp only [nonnegPath, Set.mem_ofPred_eq, Set.mem_iInter]

theorem measurableSet_nonnegPath : MeasurableSet (nonnegPath (N := N)) := by
  rw [nonnegPath_eq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => ?_
  exact (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X n i) (measurableSet_Ici (a := 0))

/-! ### The record event depends only on the low block -/

/-- Two trajectories driven by arrays that agree at every level below `d` agree below `d` as long
as the first one stays strictly below `d` (a `k < n` version of `agreeBelow_of_agree`). -/
theorem agreeBelow_traj {p : ℝ} {m : ℕ} {d : ℤ} {U U' : Array N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k)) :
    ∀ n, (∀ k, k < n → ∀ i, (trajectory p m U k).pos i < d) →
      AgreeBelow d (trajectory p m U n) (trajectory p m U' n) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨fun i => by simp, fun i x _ => by simp [initialWalkState]⟩
  | succ n ih =>
      intro hlt
      have hprev : ∀ k, k < n → ∀ i, (trajectory p m U k).pos i < d :=
        fun k hk i => hlt k (by omega) i
      have hstep := nextWalkState_agreeBelow (p := p) (m := m) harr (ih hprev)
        (fun i => hlt n (by omega) i)
      rw [trajectory_succ, trajectory_succ]
      exact hstep

/-- **`RecordAt` reads only the low block.** -/
theorem recordAt_congr {p : ℝ} {m : ℕ} {d : ℤ} {U U' : Array N} {t : ℕ}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k)) :
    RecordAt p m U t d ↔ RecordAt p m U' t d := by
  have hsym : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U' (i, x, k) = U (i, x, k) :=
    fun i x k hx => (harr i x k hx).symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs i => ?_, fun i => ?_⟩
    · have h := (agreeBelow_traj (U := U) (U' := U') harr s
          (fun k hk i => h1 k (lt_trans hk hs) i)).1 i
      rw [← h]; exact h1 s hs i
    · have h := (agreeBelow_traj (U := U) (U' := U') harr t h1).1 i
      rw [← h]; exact h2 i
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs i => ?_, fun i => ?_⟩
    · have h := (agreeBelow_traj (U := U') (U' := U) hsym s
          (fun k hk i => h1 k (lt_trans hk hs) i)).1 i
      rw [← h]; exact h1 s hs i
    · have h := (agreeBelow_traj (U := U') (U' := U) hsym t h1).1 i
      rw [← h]; exact h2 i

/-! ### The no-return condition is exactly "the fresh path stays nonnegative" -/

/-- While the shifted path stays nonnegative, the actual trajectory stays in `ShiftAgree` with it.
This is the local (non-circular) form of `restart_agreement`, and is what makes the
"no return" clause of `RegenAt` a function of the *fresh* path. -/
theorem shiftAgree_while_nonneg (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d) :
    ∀ n, (∀ k ≤ n, ∀ i, 0 ≤ (trajectory p m (levelShift d U) k).pos i) →
      ShiftAgree d (trajectory p m U (t + n)) (trajectory p m (levelShift d U) n) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using shiftAgree_record p m U hbefore hat
  | succ n ih =>
      intro hnn
      have hn : ∀ k ≤ n, ∀ i, 0 ≤ (trajectory p m (levelShift d U) k).pos i :=
        fun k hk => hnn k (by omega)
      have ihn := ih hn
      have hge : ∀ i, d ≤ (trajectory p m U (t + n)).pos i := by
        intro i
        rw [ihn.1 i]
        have hk : 0 ≤ (trajectory p m (levelShift d U) n).pos i := hnn n (by omega) i
        omega
      have hstep := nextWalkState_shiftAgree (p := p) (m := m) (U := U) (d := d)
        (s := trajectory p m U (t + n)) (s' := trajectory p m (levelShift d U) n) ihn hge
      rw [show t + (n + 1) = (t + n) + 1 from by omega, trajectory_succ, trajectory_succ]
      exact hstep

/-- **`RegenAt` is `RecordAt` plus nonnegativity of the fresh path.** -/
theorem regenAt_iff (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    RegenAt p m U t d ↔
      RecordAt p m U t d ∧ posPath p m (levelShift d U) ∈ nonnegPath (N := N) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun n i => ?_⟩
    have h := restart_pos p m U h1 h2 h3 n i
    have hk : d ≤ (trajectory p m U (t + n)).pos i := h3 n i
    show 0 ≤ (trajectory p m (levelShift d U) n).pos i
    omega
  · rintro ⟨⟨h1, h2⟩, hn⟩
    refine ⟨h1, h2, fun n i => ?_⟩
    have hsa := shiftAgree_while_nonneg (N := N) p m U h1 h2 n (fun k _ => hn k)
    have h := hsa.1 i
    have hk : 0 ≤ (trajectory p m (levelShift d U) n).pos i := hn n i
    show d ≤ (trajectory p m U (t + n)).pos i
    omega

/-! ### Measurability of the events -/

/-- The record part of the regeneration event, as a set of arrays. -/
def recordSet (p : ℝ) (m t : ℕ) (d : ℤ) : Set (Array N) := {U | RecordAt p m U t d}

theorem recordSet_eq (p : ℝ) (m t : ℕ) (d : ℤ) :
    recordSet (N := N) p m t d =
      (⋂ s ∈ Finset.range t, ⋂ i, {U : Array N | (posPath p m U) s i < d}) ∩
        ⋂ i, {U : Array N | (posPath p m U) t i = d} := by
  ext U
  simp only [recordSet, RecordAt, posPath, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
    Set.mem_ofPred_eq]

theorem measurableSet_recordSet (p : ℝ) (m t : ℕ) (d : ℤ) :
    MeasurableSet (recordSet (N := N) p m t d) := by
  rw [recordSet_eq]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter (fun i => ?_))
  · refine Finset.measurableSet_biInter _ (fun s _ => MeasurableSet.iInter (fun i => ?_))
    exact (measurable_posPath_apply p m N s i) measurableSet_Iio
  · exact (measurable_posPath_apply p m N t i) (measurableSet_singleton d)

/-- The record event as a condition on the low block, with the high coordinates filled by `0`. -/
def lowRecordSet (p : ℝ) (m t : ℕ) (d : ℤ) : Set (lowSet (N := N) d → ℝ) :=
  {V | RecordAt p m (lowExtend d V) t d}

theorem recordSet_eq_low (p : ℝ) (m t : ℕ) (d : ℤ) :
    recordSet (N := N) p m t d =
      (lowSet d).domRestrict ⁻¹' lowRecordSet (N := N) p m t d := by
  ext U
  simp only [recordSet, Set.mem_preimage, Set.mem_ofPred_eq, lowRecordSet]
  exact (recordAt_congr (lowExtend_domRestrict_agree d U)).symm

theorem measurableSet_lowRecordSet (p : ℝ) (m t : ℕ) (d : ℤ) :
    MeasurableSet (lowRecordSet (N := N) p m t d) :=
  (measurable_lowExtend d) (measurableSet_recordSet p m t d)

/-- The future event as a condition on the high block.  The array is rebuilt from the high block
by `highExtend` and then shifted down by `d`; the junk below level `d` is never read because the
event itself forces the path to stay nonnegative. -/
def highFutureSet (p : ℝ) (m : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    Set (highSet (N := N) d → ℝ) :=
  {W | posPath p m (levelShift d (highExtend d W)) ∈ nonnegPath (N := N) ∩ B}

theorem measurableSet_highFutureSet (p : ℝ) (m : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) : MeasurableSet (highFutureSet (N := N) p m d B) := by
  have hS : MeasurableSet (nonnegPath (N := N) ∩ B) :=
    measurableSet_nonnegPath.inter hB
  have hΦ : Measurable fun U : Array N => posPath p m (levelShift d U) :=
    (measurable_posPath p m N).comp (measurable_levelShift N d)
  have hset : highFutureSet (N := N) p m d B
      = highExtend (N := N) d ⁻¹'
          {U : Array N | posPath p m (levelShift d U) ∈ nonnegPath (N := N) ∩ B} := by
    ext W
    simp only [highFutureSet, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hset]
  exact (measurable_highExtend d) (hΦ hS)

/-- **The future event is a high-block event.**  The two arrays `levelShift d U` and
`levelShift d (highExtend d (highProj U))` agree at every coordinate of level `≥ d`, so by
`posPath_shift_congr` their position paths agree as long as one of them stays nonnegative —
which is exactly what the event asserts. -/
theorem highFuture_eq (p : ℝ) (m : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d B
      = {U : Array N | posPath p m (levelShift d U) ∈ nonnegPath (N := N) ∩ B} := by
  ext U
  simp only [highFutureSet, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hstay : ∀ n i,
        0 ≤ (trajectory p m (levelShift d (highExtend (N := N) d
          ((highSet d).domRestrict U))) n).pos i := h1
    have heq := posPath_shift_congr (p := p) (m := m) (d := d)
      (U := highExtend (N := N) d ((highSet d).domRestrict U)) (U' := U)
      (fun i x k hx => highExtend_domRestrict_agree d U i x k hx) hstay
    rw [← heq]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hstay : ∀ n i, 0 ≤ (trajectory p m (levelShift d U) n).pos i := h1
    have heq := posPath_shift_congr (p := p) (m := m) (d := d)
      (U := U) (U' := highExtend (N := N) d ((highSet d).domRestrict U))
      (fun i x k hx => (highExtend_domRestrict_agree d U i x k hx).symm) hstay
    rw [← heq]
    exact ⟨h1, h2⟩

/-- The relative future after a record at `(t, d)`. -/
noncomputable def relFuture (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    ℕ → Fin N → ℤ :=
  fun n i => (trajectory p m U (t + n)).pos i - d

theorem measurable_relFuture (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (N : ℕ) :
    Measurable (fun U : Array N => relFuture p m U t d) := by
  refine measurable_pi_iff.mpr (fun n => measurable_pi_iff.mpr (fun i => ?_))
  have h : Measurable fun U : Array N => (trajectory p m U (t + n)).pos i :=
    measurable_posPath_apply p m N (t + n) i
  have h2 : Measurable fun U : Array N => (trajectory p m U (t + n)).pos i - d :=
    h.sub measurable_const
  simpa only [relFuture] using h2

/-! ### The set identity: the regeneration event is a product of the two blocks -/

/-- **The regeneration event, with the future in `B`, is a low-block set intersected with a
high-block set.**  This is the set-theoretic form of `(freshlaw)`'s independence step. -/
theorem regenSet_eq (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (lowSet d).domRestrict ⁻¹' lowRecordSet (N := N) p m t d
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d B := by
  rw [highFuture_eq p m d B]
  ext U
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, lowRecordSet]
  constructor
  · rintro ⟨hreg, hB⟩
    have hrec : RecordAt p m U t d := regenAt_recordAt hreg
    have hiff := (regenAt_iff p m U t d).mp hreg
    refine ⟨(recordAt_congr (lowExtend_domRestrict_agree d U)).mpr hrec, hiff.2, ?_⟩
    have hB' : (fun n i => (trajectory p m U (t + n)).pos i - d) ∈ B := hB
    rwa [relFuture_eq p m U hreg] at hB'
  · rintro ⟨hrec, hnonneg, hB⟩
    have hrec' : RecordAt p m U t d :=
      (recordAt_congr (U := lowExtend (N := N) d ((lowSet d).domRestrict U)) (U' := U)
        (lowExtend_domRestrict_agree d U)).mp hrec
    have hreg : RegenAt p m U t d := (regenAt_iff p m U t d).mpr ⟨hrec', hnonneg⟩
    refine ⟨hreg, ?_⟩
    show (fun n i => (trajectory p m U (t + n)).pos i - d) ∈ B
    rw [relFuture_eq p m U hreg]
    exact hB

theorem measurableSet_regenSet (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet {U : Array N | RegenAt p m U t d} := by
  have h : {U : Array N | RegenAt p m U t d}
      = (lowSet d).domRestrict ⁻¹' lowRecordSet (N := N) p m t d
        ∩ (highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d univ := by
    rw [← regenSet_eq p m t d univ]
    ext U
    simp
  rw [h]
  exact ((Set.measurable_restrict (lowSet (N := N) d))
      (measurableSet_lowRecordSet p m t d)).inter
    ((Set.measurable_restrict (highSet (N := N) d))
      (measurableSet_highFutureSet p m d MeasurableSet.univ))

/-! ### The law of the future after a regeneration is the law of the fresh model -/

/-- The law of the fresh position path is invariant under the level shift: the event
`{posPath ∘ levelShift d ∈ S}` has the same mass as `{posPath ∈ S}`. -/
theorem measure_posPath_levelShift (p : ℝ) (m : ℕ) (N : ℕ) (d : ℤ)
    {S : Set (ℕ → Fin N → ℤ)} (hS : MeasurableSet S) :
    (arrayMeasure N) ((fun U : Array N => posPath p m (levelShift d U)) ⁻¹' S)
      = (arrayMeasure N) ((fun U : Array N => posPath p m U) ⁻¹' S) := by
  have h1 : Measurable fun U : Array N => posPath p m (levelShift d U) :=
    (measurable_posPath p m N).comp (measurable_levelShift N d)
  have h2 : Measurable fun U : Array N => posPath p m U := measurable_posPath p m N
  rw [← Measure.map_apply h1 hS, ← Measure.map_apply h2 hS, map_posPath_levelShift]

/-- The second factor of `freshlaw`, in the coordinate form of the block computation. -/
theorem highFuture_measure (p : ℝ) (m : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) ((highSet d).domRestrict ⁻¹' highFutureSet (N := N) p m d B)
      = (arrayMeasure N) {U | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  rw [highFuture_eq p m d B]
  exact measure_posPath_levelShift p m N d (measurableSet_nonnegPath.inter hB)

/-- **`(freshlaw)`, unconditional product form.**  The probability of a regeneration at level `d`
at time `t` with the relative future in `B` factorises into the probability of the record event
and the probability that the *fresh* path stays nonnegative and lies in `B`. -/
theorem freshlaw (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
  have hP : (arrayMeasure N) = Measure.infinitePi (fun _ : Fin N × ℤ × ℕ => uniform01) := rfl
  have hblock := SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01)
    (disjoint_lowSet_highSet (N := N) d) (measurableSet_lowRecordSet p m t d)
    (measurableSet_highFutureSet (N := N) p m d hB)
  rw [hP, regenSet_eq p m t d B, hblock, ← recordSet_eq_low, ← hP, highFuture_measure p m d hB]

/-- **The mass of the regeneration event.** -/
theorem regenAt_measure_factor (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} := by
  have h := freshlaw (N := N) p m t d (B := univ) MeasurableSet.univ
  simpa using h

/-- **Conditional law of the translated future.**  Restricted to the regeneration event, the law
of the relative future is the fresh path law restricted to `nonnegPath`, scaled by the mass of the
record event.  Dividing by `P(RegenAt) = P(RecordAt)·P(nonnegPath)` gives the paper's `P^*(B)`;
this is `(freshlaw)` with the division kept out of the statement. -/
theorem restrict_regen_map (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    (Measure.restrict (arrayMeasure N) {U : Array N | RegenAt p m U t d}).map
        (fun U => relFuture p m U t d)
      = (arrayMeasure N) (recordSet (N := N) p m t d) •
          (Measure.restrict (arrayMeasure N)
            {U : Array N | posPath p m U ∈ nonnegPath (N := N)}).map
            (fun U => posPath p m U) := by
  refine Measure.ext fun B hB => ?_
  have hΦ : Measurable fun U : Array N => relFuture p m U t d := measurable_relFuture p m t d N
  have hΨ : Measurable fun U : Array N => posPath p m U := measurable_posPath p m N
  have hA : (fun U => relFuture p m U t d) ⁻¹' B ∩ {U : Array N | RegenAt p m U t d}
      = {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B} := by
    ext U; simp [and_comm]
  have hV : (Measure.restrict (arrayMeasure N)
        {U : Array N | posPath p m U ∈ nonnegPath (N := N)})
        ((fun U => posPath p m U) ⁻¹' B)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
    rw [Measure.restrict_apply (hΨ hB)]
    congr 1
    ext U; simp [and_comm]
  rw [Measure.map_apply hΦ hB, Measure.restrict_apply (hΦ hB), Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hΨ hB, hA, hV]
  exact freshlaw p m t d hB

/-- **The paper's `(factor)` for a single record time**, given the seed probability
`P(posPath ∈ nonnegPath) ≠ 0`.  With `P^*` the fresh law conditioned on `nonnegPath`, the
translated future is independent of the past: the exact `hfac` shape consumed by
`KacFormula.kac_paper_bound`. -/
theorem freshlaw_hfac (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} ≠ ⊤)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | RegenAt p m U t d}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹
          * ((Measure.restrict (arrayMeasure N)
              {U : Array N | posPath p m U ∈ nonnegPath (N := N)}).map
              (fun U => posPath p m U)) B) := by
  have hVeq : (Measure.restrict (arrayMeasure N)
        {U : Array N | posPath p m U ∈ nonnegPath (N := N)})
        ((fun U => posPath p m U) ⁻¹' B)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ B} := by
    rw [Measure.restrict_apply ((measurable_posPath p m N) hB)]
    congr 1
    ext U; simp [and_comm]
  have halg : ∀ Q : ℝ≥0∞,
      (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹ * Q) = Q := by
    intro Q
    calc (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)}
          * (((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹ * Q)
        = (((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹ * Q)
            * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} :=
          mul_comm _ _
      _ = ((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹
            * (Q * (arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)}) :=
          mul_assoc _ _ _
      _ = ((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)})⁻¹
            * ((arrayMeasure N) {U : Array N | posPath p m U ∈ nonnegPath (N := N)} * Q) := by
          rw [mul_comm Q]
      _ = Q := ENNReal.inv_mul_cancel_left hV hVtop
  rw [Measure.map_apply (measurable_posPath p m N) hB, hVeq, regenAt_measure_factor, mul_assoc,
    halg, freshlaw p m t d hB]

/-! ### The paper's strict regeneration event

`RegenPath.V` (the paper's `V`) is *strict*: `X^i_n > 0` for every `n ≥ 1`, whereas `RegenAt`
uses `d ≤`.  Both fit the same block argument, because the extra requirement only restricts the
*high* block; `strictPos` is the corresponding set of fresh paths, and it still lies inside
`nonnegPath` (a path starts at `0`). -/

/-- The paper's `V`: strictly positive after time `0`.  Stated with the shift `n + 1` so that it
is visibly a countable intersection of measurable sets. -/
def strictPos : Set (ℕ → Fin N → ℤ) := {X | (∀ i, X 0 i = 0) ∧ ∀ n i, 0 < X (n + 1) i}

theorem mem_strictPos {X : ℕ → Fin N → ℤ} :
    X ∈ strictPos (N := N) ↔ (∀ i, X 0 i = 0) ∧ ∀ n, 0 < n → ∀ i, 0 < X n i := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun n hn i => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact h m i
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun n i => h (n + 1) (by omega) i⟩

theorem measurableSet_strictPos : MeasurableSet (strictPos (N := N)) := by
  have h1 : {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0} = ⋂ i, {X : ℕ → Fin N → ℤ | X 0 i = 0} := by
    ext X; simp
  have h2 : {X : ℕ → Fin N → ℤ | ∀ n i, 0 < X (n + 1) i}
      = ⋂ n, ⋂ i, {X : ℕ → Fin N → ℤ | 0 < X (n + 1) i} := by
    ext X; simp
  have hsplit : strictPos (N := N)
      = {X : ℕ → Fin N → ℤ | ∀ i, X 0 i = 0}
        ∩ {X : ℕ → Fin N → ℤ | ∀ n i, 0 < X (n + 1) i} := rfl
  rw [hsplit, h1, h2]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i =>
      (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X 0 i) (measurableSet_singleton 0)
  · exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun i =>
      (by fun_prop : Measurable fun X : ℕ → Fin N → ℤ => X (n + 1) i) measurableSet_Ioi

theorem strictPos_subset_nonnegPath : strictPos (N := N) ⊆ nonnegPath (N := N) := by
  intro X hX
  obtain ⟨h0, h⟩ := mem_strictPos.mp hX
  intro n i
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, h0 i]
  · exact le_of_lt (h n hn i)

/-- The paper's regeneration event: a simultaneous record at time `t` at level `d` from which
every walker stays *strictly* above `d`. -/
def RegenAtStrict (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) : Prop :=
  RecordAt p m U t d ∧ ∀ n, 0 < n → ∀ i, d < (trajectory p m U (t + n)).pos i

/-- **`RegenAtStrict` is `RecordAt` plus a strictly positive fresh path.**  This is purely
arithmetic: the relative future at time `t + n` is `X^i_{t+n} - d`. -/
theorem regenAtStrict_iff (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    RegenAtStrict p m U t d ↔
      RecordAt p m U t d ∧ relFuture p m U t d ∈ strictPos (N := N) := by
  rw [RegenAtStrict, mem_strictPos]
  constructor
  · rintro ⟨hrec, hstrict⟩
    refine ⟨hrec, fun i => ?_, fun n hn i => ?_⟩
    · show (trajectory p m U (t + 0)).pos i - d = 0
      rw [Nat.add_zero, hrec.2 i, sub_self]
    · have h := hstrict n hn i
      show 0 < (trajectory p m U (t + n)).pos i - d
      omega
  · rintro ⟨hrec, -, hstrict⟩
    refine ⟨hrec, fun n hn i => ?_⟩
    have h : 0 < (trajectory p m U (t + n)).pos i - d := hstrict n hn i
    show d < (trajectory p m U (t + n)).pos i
    omega

/-- **The factorization for an arbitrary set `S ⊆ nonnegPath` of allowed fresh paths.**  For
`S = nonnegPath` this is `freshlaw`; for `S = strictPos` it is the paper's strict version. -/
theorem freshlaw_of_subset (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {S B : Set (ℕ → Fin N → ℤ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ nonnegPath (N := N)) (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RecordAt p m U t d ∧ relFuture p m U t d ∈ S ∩ B}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ S ∩ B} := by
  have h := freshlaw p m t d (hS.inter hB)
  have h1 : {U : Array N | RegenAt p m U t d ∧ relFuture p m U t d ∈ S ∩ B}
      = {U : Array N | RecordAt p m U t d ∧ relFuture p m U t d ∈ S ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hreg, hin, hB'⟩
      exact ⟨regenAt_recordAt hreg, hin, hB'⟩
    · rintro ⟨hrec, hin, hB'⟩
      have hnon : relFuture p m U t d ∈ nonnegPath (N := N) := hSsub hin
      simp only [nonnegPath, Set.mem_ofPred_eq, relFuture] at hnon
      have hstay : ∀ n i, d ≤ (trajectory p m U (t + n)).pos i := by
        intro n i; have := hnon n i; omega
      have heq := relFuture_eq p m U ⟨hrec.1, hrec.2, hstay⟩
      refine ⟨(regenAt_iff p m U t d).mpr ⟨hrec, ?_⟩, hin, hB'⟩
      rw [← heq]
      exact hSsub hin
  have h2 : {U : Array N | posPath p m U ∈ nonnegPath (N := N) ∩ (S ∩ B)}
      = {U : Array N | posPath p m U ∈ S ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨hS', hB'⟩; exact ⟨hSsub hS', hS', hB'⟩
  rw [h1, h2] at h
  exact h

/-- **The paper's `(freshlaw)` for the strict regeneration event `V`.** -/
theorem freshlawStrict (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) {B : Set (ℕ → Fin N → ℤ)}
    (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have h := freshlaw_of_subset p m t d measurableSet_strictPos strictPos_subset_nonnegPath hB
  have h1 : {U : Array N | RegenAtStrict p m U t d ∧ relFuture p m U t d ∈ B}
      = {U : Array N | RecordAt p m U t d ∧
            relFuture p m U t d ∈ strictPos (N := N) ∩ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [regenAtStrict_iff]
    constructor
    · rintro ⟨⟨hrec, hin⟩, hB'⟩
      exact ⟨hrec, hin, hB'⟩
    · rintro ⟨hrec, hin, hB'⟩
      exact ⟨⟨hrec, hin⟩, hB'⟩
  rw [h1, h]

/-- The mass identity for the strict event. -/
theorem regenAtStrict_measure_factor (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d}
      = (arrayMeasure N) (recordSet (N := N) p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have h := freshlawStrict (N := N) p m t d (B := univ) MeasurableSet.univ
  simpa using h

/-- **The paper's `(factor)` in the strict form used by `RegenPath.V`**, i.e. the `hfac` of
`KacFormula.kac_paper_bound` with `P` the seed probability `P(posPath ∈ strictPos)`. -/
theorem freshlawStrict_hfac (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d ∧ relFuture p m U t d ∈ B}
      = (arrayMeasure N) {U : Array N | RegenAtStrict p m U t d}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
          * ((Measure.restrict (arrayMeasure N)
              {U : Array N | posPath p m U ∈ strictPos (N := N)}).map
              (fun U => posPath p m U)) B) := by
  have hVeq : (Measure.restrict (arrayMeasure N)
        {U : Array N | posPath p m U ∈ strictPos (N := N)})
        ((fun U => posPath p m U) ⁻¹' B)
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
    rw [Measure.restrict_apply ((measurable_posPath p m N) hB)]
    congr 1
    ext U; simp [and_comm]
  have halg : ∀ Q : ℝ≥0∞,
      (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹ * Q) = Q := by
    intro Q
    calc (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
          * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹ * Q)
        = (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹ * Q)
            * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := mul_comm _ _
      _ = ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
            * (Q * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}) :=
          mul_assoc _ _ _
      _ = ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
            * ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} * Q) := by
          rw [mul_comm Q]
      _ = Q := ENNReal.inv_mul_cancel_left hV hVtop
  rw [Measure.map_apply (measurable_posPath p m N) hB, hVeq, regenAtStrict_measure_factor,
    mul_assoc, halg, freshlawStrict p m t d hB]

end SwarmFresh
