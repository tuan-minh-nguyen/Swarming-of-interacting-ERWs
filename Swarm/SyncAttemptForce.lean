/-
# Bounded-defect synchronisation force for the *canonical strict attempt*

`DefectSyncFirstHit.defect_sync_force_first_hit` proves the array-level first-passage force

  `(1-p)^((2K+1)N) * mu G
     <= mu (G ∩ {no walker above ℓ before n+2K+1} ∩ {all walkers at ℓ+1 at n+2K+1})`

for an `enlMeas p m n`-measurable past event `G` whose every point has positions
`ℓ - 2 e_i` with `e_i ≤ K`.  Nothing in the tree connected that event to the campaign's
*canonical strict attempt* `RawStrictAttemptTower.StrictAttempt`, i.e. to the actual record
clock `recTimeA` and to the strict regeneration `RegenAtStrict` (every walker *strictly* above
the record level at *all* later times).  The difference matters: the landing event is a
low-level event of the array, while `RegenAtStrict` also contains the whole strict future,
which in the `(freshlaw)` factorization carries the seed factor
`P(V) = mu {posPath ∈ strictPos}`.

This file closes exactly that interface and nothing more.

## Main results, in order

* `evWord_eq_steps` — the existing word event `evWord` is *exactly* the set of arrays whose
  position path takes the prescribed steps (the nontrivial direction takes the prefix
  `prefOf p m n U` itself).  This is what makes "word event" a property of the prefix path.
* `syncWordSet` — the word event with the defect sector, `∃ e, sector(e) ∧ word(e)`.
* `syncWordSet_mass_ge` — **the force on the word event itself**, i.e. the intermediate step of
  `defect_sync_force_first_hit`'s sector computation, exported: the landing event used there is
  not a prefix event, the word event is.
* `sync_landing_of_steps`, `wordPiece_subset_record`, `recTimeA_of_landing` — the landing is a
  simultaneous record at a *known* strict record time: positions `≤ r` up to `n+2K`, all at
  `r+1` at `n+2K+1`, hence `runMax (actX) (n+2K+1) = (r:ℤ)+1` for the first time, hence
  `recTimeA p m U (r+1) = n+2K+1` on `ReachAll`.
* `wordPiece_fresh` — `freshlawStrict_past` applied to the *prefix* description of a word
  piece: `mu (piece ∩ strict future) = mu piece * P(V)`.  The strict future after the landing
  is independent of the whole prefix, with the seed factor `P(V)`.
* `strictAttempt_mass_ge` — **the main result**: for `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, every
  `K`, `n`, `r` and every `enlMeas p m n`-measurable `G` whose positions at time `n` have defect
  `≤ 2K` below level `r`,

  `ofReal (1-p)^((2K+1)N) * P(V) * mu G ≤ mu {U | StrictAttempt p m U r}`.

## Scope, stated exactly

* The constant is `(1-p)^((2K+1)N) * P(V)` with `P(V) > 0`
  (`SwarmSeed.strictPos_measure_ne_zero`) but **not uniform in `K`**, and the hypothesis on `G`
  is the bounded-defect sector.  That is precisely (N1) of the current frontier with its exact
  domain; no uniform-in-defect, no `sum' FirstSuccessCell = 1`, no `D = ⊤` nullity and no
  invariant law is claimed or implied.
* The conclusion is `mu {StrictAttempt r}` rather than `mu (G ∩ {StrictAttempt r})`: this is not
  a weakening by choice.  `enlMeas` is *not* determined by the position prefix (two arrays with
  the same position prefix may differ at a read coordinate on the same side of the threshold),
  so `G ∩ (word piece)` is not a prefix event and `(freshlaw)` cannot be applied to it.  The
  sector decomposition is what transfers the force from `G` to the prefix events.
-/
import Swarm.DefectSyncFirstHit
import Swarm.SegmentLaw
import Swarm.SeedDischarge
import Swarm.RawStrictAttemptTower
import Swarm.ActualRecordGeometry

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace SyncAttemptForce

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRestart SwarmFresh SwarmSeg DefectSync
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### 1. The word event is a condition on the position path -/

/-- Projection of the prescribed word event: the walkers of `A` take the prescribed step. -/
theorem evWord_step_of_mem {p : ℝ} {m n : ℕ} {A : Finset (Fin N)} {ε : ℕ → Fin N → ℤ}
    {k : ℕ} {U : Array N} (hU : U ∈ evWord p m n A ε k) {u : ℕ} (hu : u < k) {i : Fin N}
    (hi : i ∈ A) :
    (trajectory p m U (n + u + 1)).pos i = (trajectory p m U (n + u)).pos i + ε u i := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [evWord_succ] at hU
      obtain ⟨h1, h2⟩ := hU
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
      · exact ih h1 hlt
      · subst heq
        have hstep := h2 i hi
        simpa [Nat.add_assoc] using hstep

/-- **The word event is exactly the set of arrays whose position path takes the prescribed
steps.**  The nontrivial direction uses the prefix `prefOf p m n U` itself. -/
theorem evWord_eq_steps (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) (k : ℕ) :
    evWord p m n A ε k =
      {U : Array N | ∀ u < k, ∀ i ∈ A,
        (trajectory p m U (n + u + 1)).pos i = (trajectory p m U (n + u)).pos i + ε u i} := by
  classical
  ext U
  constructor
  · intro hU u hu i hi
    exact evWord_step_of_mem hU hu hi
  · intro h
    refine Set.mem_iUnion.mpr ⟨prefOf p m n U, ?_⟩
    induction k with
    | zero => exact prefAgree_prefOf U
    | succ k ih =>
        exact ⟨ih (fun u hu i hi => h u (by omega) i hi), fun i hi => h k (by omega) i hi⟩

/-! ### 2. The synchronisation word event with the defect sector -/

/-- One sector of the word event: defect sector `e` at time `n`, then the compensating word
`syncWord K e` for `2K+1` steps. -/
noncomputable def wordPiece (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) : Set (Array N) :=
  syncSector p m n (r : ℤ) (fun i => (e i : ℕ)) ∩
    evWord p m n (Finset.univ : Finset (Fin N)) (syncWord K (fun i => (e i : ℕ))) (2 * K + 1)

/-- The synchronisation word event: "the swarm is in some defect sector `≤ 2K` below level `r`
at time `n` and then follows the compensating word for `2K+1` steps". -/
noncomputable def syncWordSet (p : ℝ) (m n K r : ℕ) : Set (Array N) :=
  ⋃ e : (Fin N → Fin (K + 1)), wordPiece p m n K r e

theorem syncWordSet_eq_iUnion (p : ℝ) (m n K r : ℕ) :
    syncWordSet p m n K r = ⋃ e : (Fin N → Fin (K + 1)), wordPiece p m n K r e := rfl

/-- Two distinct defect sectors are disjoint. -/
theorem disjoint_wordPiece (p : ℝ) (m n K r : ℕ) {e e' : Fin N → Fin (K + 1)} (hne : e ≠ e') :
    Disjoint (wordPiece p m n K r e) (wordPiece p m n K r e') := by
  rw [Set.disjoint_left]
  intro U hU hU'
  apply hne
  funext i
  have h2 : (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ) := hU.1 i
  have h3 : (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e' i : ℕ) : ℤ) := hU'.1 i
  have hv : ((e i : ℕ) : ℤ) = ((e' i : ℕ) : ℤ) := by rw [h2] at h3; linarith
  exact Fin.ext (Nat.cast_injective hv)

/-! ### 3. The force on the word event itself -/

/-- **Bounded-defect synchronisation force on the word event.**  This is the sector computation
of `DefectSyncFirstHit.defect_sync_force_first_hit` with the landing event replaced by the word
event, so that the conclusion is a prefix event. -/
theorem syncWordSet_mass_ge_sum (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1)
    (m n K r : ℕ) {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * (arrayMeasure N) G ≤
      ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (G ∩ wordPiece p m n K r e) := by
  classical
  have hsec_meas : ∀ e : Fin N → Fin (K + 1),
      MeasurableSet[enlMeas p m n]
        (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := fun e =>
    hG.inter (measurableSet_syncSector_enl p m n (r : ℤ) (fun i => (e i : ℕ)))
  have hsec_amb : ∀ e : Fin N → Fin (K + 1),
      MeasurableSet (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := fun e =>
    enlMeas_le p m n _ (hsec_meas e)
  have hdisj : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' →
      Disjoint (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ)))
        (G ∩ syncSector p m n (r : ℤ) (fun i => (e' i : ℕ))) := by
    intro e e' hne
    rw [Set.disjoint_left]
    intro U hU hU'
    apply hne
    funext i
    have h2 : (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ) := hU.2 i
    have h3 : (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e' i : ℕ) : ℤ) := hU'.2 i
    have hv : ((e i : ℕ) : ℤ) = ((e' i : ℕ) : ℤ) := by rw [h2] at h3; linarith
    exact Fin.ext (Nat.cast_injective hv)
  have hcover : G = ⋃ e : (Fin N → Fin (K + 1)),
      (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun e => Set.inter_subset_left)
    intro U hU
    obtain ⟨e, he⟩ := hsec U hU
    exact Set.mem_iUnion.mpr ⟨e, hU, he⟩
  have hforce : ∀ e : Fin N → Fin (K + 1),
      ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
          (arrayMeasure N) (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) ≤
        (arrayMeasure N) (G ∩ wordPiece p m n K r e) := by
    intro e
    have h := evWord_mass_ge_univ (N := N) p hp0 hp1 m n
      (syncWord K (fun i => (e i : ℕ))) (syncWord_unit K (fun i => (e i : ℕ)))
      (hsec_meas e) (2 * K + 1)
    have hset : G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ)) ∩
        evWord p m n (Finset.univ : Finset (Fin N))
          (syncWord K (fun i => (e i : ℕ))) (2 * K + 1)
        = G ∩ wordPiece p m n K r e := by
      rw [wordPiece, Set.inter_assoc]
    rwa [hset] at h
  have hμG : (arrayMeasure N) G = ∑ e : (Fin N → Fin (K + 1)),
      (arrayMeasure N) (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := by
    conv_lhs => rw [hcover]
    rw [measure_iUnion (μ := arrayMeasure N) hdisj hsec_amb, tsum_fintype]
  have hμW : (arrayMeasure N) (⋃ e : (Fin N → Fin (K + 1)),
      (G ∩ wordPiece p m n K r e)) =
      ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (G ∩ wordPiece p m n K r e) := by
    have hd : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' →
        Disjoint (G ∩ wordPiece p m n K r e) (G ∩ wordPiece p m n K r e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      intro U h1 h2
      exact Set.disjoint_left.mp (disjoint_wordPiece p m n K r hne) h1.2 h2.2
    have hm : ∀ e : Fin N → Fin (K + 1), MeasurableSet (G ∩ wordPiece p m n K r e) := by
      intro e
      have h1 : MeasurableSet (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := hsec_amb e
      have h2 : MeasurableSet (evWord p m n (Finset.univ : Finset (Fin N))
          (syncWord K (fun i => (e i : ℕ))) (2 * K + 1)) :=
        enlMeas_le p m (n + (2 * K + 1)) _ (measurableSet_evWord_enl p m n _ _ (2 * K + 1))
      have he : G ∩ wordPiece p m n K r e =
          (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) ∩
            evWord p m n (Finset.univ : Finset (Fin N))
              (syncWord K (fun i => (e i : ℕ))) (2 * K + 1) := by
        rw [wordPiece, Set.inter_assoc]
      rw [he]
      exact h1.inter h2
    rw [measure_iUnion (μ := arrayMeasure N) hd hm, tsum_fintype]
  have hsub : (⋃ e : (Fin N → Fin (K + 1)), (G ∩ wordPiece p m n K r e)) ⊆
      syncWordSet p m n K r :=
    Set.iUnion_subset fun e =>
      Set.Subset.trans Set.inter_subset_right (Set.subset_iUnion (wordPiece p m n K r) e)
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * (arrayMeasure N) G
      = ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
          ∑ e : (Fin N → Fin (K + 1)),
            (arrayMeasure N) (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) := by
        rw [hμG]
    _ = ∑ e : (Fin N → Fin (K + 1)),
          ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
            (arrayMeasure N) (G ∩ syncSector p m n (r : ℤ) (fun i => (e i : ℕ))) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (G ∩ wordPiece p m n K r e) :=
        Finset.sum_le_sum fun e _ => hforce e

theorem measurableSet_wordPiece (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    MeasurableSet (wordPiece p m n K r e) := by
  refine MeasurableSet.inter ?_ ?_
  · exact enlMeas_le p m n _ (measurableSet_syncSector_enl p m n (r : ℤ) (fun i => (e i : ℕ)))
  · exact enlMeas_le p m (n + (2 * K + 1)) _
      (measurableSet_evWord_enl p m n _ _ (2 * K + 1))

theorem measure_iUnion_wordPiece (p : ℝ) (m n K r : ℕ) :
    (arrayMeasure N) (⋃ e : (Fin N → Fin (K + 1)), wordPiece p m n K r e) =
      ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (wordPiece p m n K r e) := by
  rw [measure_iUnion (μ := arrayMeasure N) (fun e e' hne => disjoint_wordPiece p m n K r hne)
    (fun e => measurableSet_wordPiece p m n K r e), tsum_fintype]

/-- **Bounded-defect synchronisation force on the word event.**  This is the sector computation
of `DefectSyncFirstHit.defect_sync_force_first_hit` with the landing event replaced by the word
event, so that the conclusion is a prefix event. -/
theorem syncWordSet_mass_ge (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1)
    (m n K r : ℕ) {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * (arrayMeasure N) G ≤
      (arrayMeasure N) (syncWordSet p m n K r) := by
  refine le_trans (syncWordSet_mass_ge_sum p hp0 hp1 m n K r hG hsec) ?_
  calc ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (G ∩ wordPiece p m n K r e)
      ≤ ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (wordPiece p m n K r e) :=
        Finset.sum_le_sum fun e _ => measure_mono Set.inter_subset_right
    _ = (arrayMeasure N) (syncWordSet p m n K r) := (measure_iUnion_wordPiece p m n K r).symm

/-! ### 4. The word lands at the next level for the first time -/

/-- **The compensating word lands at the next level for the first time.**  The deterministic
content of `DefectSyncFirstHit.evWord_sync_first_hit`, stated with the step condition rather
than `evWord` so that it applies to `wordPiece`. -/
theorem sync_landing_of_steps {p : ℝ} {m n K r : ℕ} {e : Fin N → ℕ} {U : Array N}
    (he : ∀ i, e i ≤ K)
    (hstart : ∀ i, (trajectory p m U n).pos i = (r : ℤ) - 2 * (e i : ℤ))
    (hstep : ∀ u, u < 2 * K + 1 → ∀ i,
      (trajectory p m U (n + u + 1)).pos i =
        (trajectory p m U (n + u)).pos i + syncWord K e u i) :
    (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ (r : ℤ)) ∧
      (∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = (r : ℤ) + 1) := by
  constructor
  · intro u hu i
    have htel : (trajectory p m U (n + u)).pos i =
        (trajectory p m U n).pos i + ∑ v ∈ Finset.range u, syncWord K e v i :=
      pos_add_sum (p := p) (m := m) (n := n) (ε := syncWord K e) (L := u) (U := U)
        (fun v hv => hstep v (Nat.lt_trans hv hu)) i
    rw [htel, hstart i]
    by_cases hcase : u ≤ 2 * K - 2 * e i
    · have hle := sum_syncWord_prefix_le K e i hcase
      have hnn : (0 : ℤ) ≤ 2 * (e i : ℤ) := by positivity
      linarith
    · push Not at hcase
      have hj : 2 * K - 2 * e i ≤ u := le_of_lt hcase
      rw [sum_syncWord_of_le K e i hj]
      have hek : 2 * e i ≤ 2 * K := by have := he i; omega
      have hnat : u - (2 * K - 2 * e i) ≤ 2 * e i := by omega
      have hcast : ((u - (2 * K - 2 * e i) : ℕ) : ℤ) ≤ 2 * (e i : ℤ) := by
        exact_mod_cast hnat
      have hrew : (u : ℤ) - ((2 * K - 2 * e i : ℕ) : ℤ) =
          ((u - (2 * K - 2 * e i) : ℕ) : ℤ) := by
        rw [Nat.cast_sub hj]
      rw [hrew]
      linarith
  · intro i
    have htel : (trajectory p m U (n + (2 * K + 1))).pos i =
        (trajectory p m U n).pos i + ∑ v ∈ Finset.range (2 * K + 1), syncWord K e v i :=
      pos_add_sum (p := p) (m := m) (n := n) (ε := syncWord K e) (L := 2 * K + 1) (U := U)
        hstep i
    rw [htel, hstart i, sum_syncWord K e i (he i)]
    ring

/-- A word piece lands at the next level: no walker above `r` before `n+2K`, all at `r+1`
at `n+2K+1`. -/
theorem wordPiece_landing (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) {U : Array N}
    (hU : U ∈ wordPiece p m n K r e) :
    (∀ u, u < 2 * K + 1 → ∀ i, (trajectory p m U (n + u)).pos i ≤ (r : ℤ)) ∧
      (∀ i, (trajectory p m U (n + (2 * K + 1))).pos i = (r : ℤ) + 1) := by
  obtain ⟨hsec, hword⟩ := hU
  rw [evWord_eq_steps] at hword
  exact sync_landing_of_steps (p := p) (m := m) (n := n) (K := K) (r := r)
    (e := fun i => (e i : ℕ)) (U := U)
    (fun i => Nat.lt_succ_iff.mp (e i).isLt)
    (fun i => hsec i)
    (fun u hu i => hword u hu i (Finset.mem_univ i))


/-! ### 5. The attempt window as a prefix event, and its strict record time -/

/-- The synchronisation word event, as a condition on the position prefix of length `t+1`,
`t = n + (2K+1)`.  It also records that no walker stood above level `r` before the window
opens, which is what makes `n+2K+1` the *first* time the swarm reaches level `r+1`. -/
noncomputable def syncPast (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    Set (Pref N (n + (2 * K + 1))) :=
  {π | (∀ (j : ℕ) (_ : j < n) (i : Fin N), π ⟨j, by omega⟩ i ≤ (r : ℤ)) ∧
    (∀ i, π ⟨n, by omega⟩ i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)) ∧
    (∀ (u : ℕ) (_ : u < 2 * K + 1) (i : Fin N),
      π ⟨n + u + 1, by omega⟩ i = π ⟨n + u, by omega⟩ i +
        syncWord K (fun i => (e i : ℕ)) u i)}

/-- Any set of position prefixes is measurable: `Pref N t` is countable. -/
theorem measurableSet_syncPast (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    MeasurableSet (syncPast p m n K r e) :=
  Set.Countable.measurableSet (Set.countable_univ.mono (Set.subset_univ _))

/-- The prefix description agrees with the array description of a word piece. -/
theorem pastProj_mem_syncPast {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)} {U : Array N}
    (hprev : ∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ)) :
    pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e ↔ U ∈ wordPiece p m n K r e := by
  constructor
  · rintro ⟨-, hsec, hstep⟩
    refine ⟨hsec, ?_⟩
    rw [evWord_eq_steps]
    intro u hu i _
    exact hstep u hu i
  · rintro ⟨hsec, hword⟩
    refine ⟨hprev, hsec, fun u hu i => ?_⟩
    rw [evWord_eq_steps] at hword
    exact hword u hu i (Finset.mem_univ i)

/-- A prefix in `syncPast` has no walker above `r` before `n+2K+1`. -/
theorem syncPast_prev {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)} {U : Array N}
    (hU : pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e) :
    ∀ j, j < n + (2 * K + 1) → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ) := by
  obtain ⟨hprev, hsec, hstep⟩ := hU
  have hland := sync_landing_of_steps (p := p) (m := m) (n := n) (K := K) (r := r)
    (e := fun i => (e i : ℕ)) (U := U) (fun i => Nat.lt_succ_iff.mp (e i).isLt)
    (fun i => hsec i) (fun u hu i => hstep u hu i)
  intro j hj i
  rcases lt_or_ge j n with h | h
  · exact hprev j h i
  · obtain ⟨u, rfl⟩ : ∃ u, j = n + u := ⟨j - n, by omega⟩
    exact hland.1 u (by omega) i

/-- **A prefix in `syncPast` is a simultaneous record at level `r+1` at time `n+2K+1`.** -/
theorem recordAt_of_syncPast {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)} {U : Array N}
    (hU : pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e) :
    RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) := by
  obtain ⟨hprev, hsec, hstep⟩ := hU
  have hland := sync_landing_of_steps (p := p) (m := m) (n := n) (K := K) (r := r)
    (e := fun i => (e i : ℕ)) (U := U) (fun i => Nat.lt_succ_iff.mp (e i).isLt)
    (fun i => hsec i) (fun u hu i => hstep u hu i)
  refine ⟨fun s hs i => ?_, fun i => hland.2 i⟩
  rcases lt_or_ge s n with h | h
  · have h1 : (trajectory p m U s).pos i ≤ (r : ℤ) := hprev s h i
    omega
  · obtain ⟨u, rfl⟩ : ∃ u, s = n + u := ⟨s - n, by omega⟩
    have h1 : (trajectory p m U (n + u)).pos i ≤ (r : ℤ) := hland.1 u (by omega) i
    omega

/-- **The canonical record clock fires exactly at the landing time.**  On `ReachAll`, the
first time the running maximum of the actual positions equals `r+1` is `n+2K+1`. -/
theorem recTimeA_of_landing {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)} {U : Array N}
    (hreach : U ∈ ReachAll p m)
    (hU : pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e) :
    recTimeA p m U (r + 1) = n + (2 * K + 1) := by
  obtain ⟨hprev, hsec, hstep⟩ := hU
  have hland := sync_landing_of_steps (p := p) (m := m) (n := n) (K := K) (r := r)
    (e := fun i => (e i : ℕ)) (U := U) (fun i => Nat.lt_succ_iff.mp (e i).isLt)
    (fun i => hsec i) (fun u hu i => hstep u hu i)
  have hlev : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  refine (recTimeA_eq_iff (N := N) p m U (r + 1) (n + (2 * K + 1)) hreach).mpr ⟨?_, ?_⟩
  · rw [hlev]
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ fun i _ => ?_
      show (trajectory p m U (n + (2 * K + 1))).pos i ≤ (r : ℤ) + 1
      rw [hland.2 i]
    · have h := le_runMax (X := actX p m U) (n := n + (2 * K + 1))
        (i := Classical.arbitrary (Fin N))
      have hx : actX p m U (Classical.arbitrary (Fin N)) (n + (2 * K + 1)) = (r : ℤ) + 1 :=
        hland.2 (Classical.arbitrary (Fin N))
      rw [hx] at h
      exact h
  · intro j hj hcontra
    rw [hlev] at hcontra
    have hle : runMax (actX p m U) j ≤ (r : ℤ) := by
      refine Finset.sup'_le _ _ fun i _ => ?_
      rcases lt_or_ge j n with h | h
      · have h1 : (trajectory p m U j).pos i ≤ (r : ℤ) := hprev j h i
        simpa [actX] using h1
      · obtain ⟨u, rfl⟩ : ∃ u, j = n + u := ⟨j - n, by omega⟩
        have h1 : (trajectory p m U (n + u)).pos i ≤ (r : ℤ) := hland.1 u (by omega) i
        simpa [actX] using h1
    omega

/-! ### 6. The strict future after the landing is independent of the prefix -/

/-- The strict piece of one defect sector: the prefix lies in `syncPast`, and the whole future
after the landing is strictly above the record level. -/
noncomputable def strictPiece (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) : Set (Array N) :=
  {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} ∩
    {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}

theorem measurableSet_strictPiece (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    MeasurableSet (strictPiece p m n K r e) := by
  refine MeasurableSet.inter ?_ ?_
  · exact (measurable_pastProj p m (n + (2 * K + 1)) N) (measurableSet_syncPast p m n K r e)
  · exact (measurable_relFuture p m (n + (2 * K + 1)) ((r : ℤ) + 1) N) measurableSet_strictPos

/-- A prefix in `syncPast` is in the corresponding word piece (its own previous-maximum clause
supplies the hypothesis of `pastProj_mem_syncPast`). -/
theorem syncPast_subset_wordPiece {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)}
    {U : Array N} (hU : pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e) :
    U ∈ wordPiece p m n K r e := by
  obtain ⟨-, hsec, hstep⟩ := hU
  refine ⟨hsec, ?_⟩
  rw [evWord_eq_steps]
  intro u hu i _
  exact hstep u hu i

theorem strictPiece_subset_wordPiece (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    strictPiece p m n K r e ⊆ wordPiece p m n K r e := fun _ hU => syncPast_subset_wordPiece hU.1

/-- **The `(freshlaw)` strict factor for an arbitrary prefix sub-event of `syncPast`.**  This is
the general form: for any measurable `A ⊆ syncPast p m n K r e`, the strict future after the
landing factorises with the seed factor `P(V)`. -/
theorem fresh_of_syncPast_subset (p : ℝ) (m n K r : ℕ) {e : Fin N → Fin (K + 1)}
    {A : Set (Pref N (n + (2 * K + 1)))} (hA : MeasurableSet A)
    (hAsub : A ⊆ syncPast p m n K r e) :
    (arrayMeasure N) ({U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ A} ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
      (arrayMeasure N) {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ A} *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} := by
  have hrec : ∀ U : Array N, pastProj p m (n + (2 * K + 1)) U ∈ A →
      RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) :=
    fun U hU => recordAt_of_syncPast (hAsub hU)
  have hmain := freshlawStrict_past (N := N) p m (n + (2 * K + 1)) ((r : ℤ) + 1)
    (A := A) hA (B := univ) MeasurableSet.univ
  have hF : recordPastSet p m (n + (2 * K + 1)) ((r : ℤ) + 1) A =
      {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ A} := by
    ext U
    simp only [recordPastSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨hrec U h, h⟩
  have hQ : {U : Array N | posPath p m U ∈ strictPos ∩ univ} =
      {U : Array N | posPath p m U ∈ strictPos} := by
    ext U; simp
  have hmain' : (arrayMeasure N) {U : Array N |
        RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∧
        pastProj p m (n + (2 * K + 1)) U ∈ A ∧
        relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos ∩ univ} =
      (arrayMeasure N) {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ A} *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} := by
    simp only [hF, hQ] at hmain
    exact hmain
  have hE : ({U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ A} ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
      {U : Array N | RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∧
        pastProj p m (n + (2 * K + 1)) U ∈ A ∧
        relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos ∩ univ} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hrec U h1, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [hE]
  exact hmain'

/-- **The `(freshlaw)` strict factor, for one word piece.**  The strict future after the
landing carries the seed factor `P(V) = mu {posPath ∈ strictPos}`, independently of the whole
prefix path (hence of the defect sector, the word, and the past of the window). -/
theorem wordPiece_fresh (p : ℝ) (m n K r : ℕ) (e : Fin N → Fin (K + 1)) :
    (arrayMeasure N) (strictPiece p m n K r e) =
      (arrayMeasure N) {U : Array N |
          pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} := by
  show (arrayMeasure N) ({U : Array N |
          pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} ∩
        {U : Array N |
          relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) = _
  have hmain := freshlawStrict_past (N := N) p m (n + (2 * K + 1)) ((r : ℤ) + 1)
    (A := syncPast p m n K r e) (measurableSet_syncPast p m n K r e)
    (B := univ) MeasurableSet.univ
  have hF : recordPastSet p m (n + (2 * K + 1)) ((r : ℤ) + 1) (syncPast p m n K r e) =
      {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} := by
    ext U
    simp only [recordPastSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨recordAt_of_syncPast h, h⟩
  have hQ : {U : Array N | posPath p m U ∈ strictPos ∩ univ} =
      {U : Array N | posPath p m U ∈ strictPos} := by
    ext U
    simp
  have hmain' : (arrayMeasure N) {U : Array N | RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∧
        pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e ∧
        relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos ∩ univ} =
      (arrayMeasure N) {U : Array N |
          pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} := by
    simp only [hF, hQ] at hmain
    exact hmain
  have hE : ({U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
      {U : Array N | RecordAt p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∧
        pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e ∧
        relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos ∩ univ} := by
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨recordAt_of_syncPast h1, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [hE]
  exact hmain'


/-! ### 7. The canonical strict attempt -/

/-- On `ReachAll`, a prefix in `syncPast` whose future is strictly above the landing level *is*
the canonical strict attempt of level `r+1`.  This is the interface step that was missing: it
identifies the word landing with `StrictAttempt` at the *actual* record clock `recTimeA`. -/
theorem strictAttempt_of_syncPast {p : ℝ} {m n K r : ℕ} {e : Fin N → Fin (K + 1)} {U : Array N}
    (hreach : U ∈ ReachAll p m)
    (hU : pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e)
    (hstrict : relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos) :
    RawStrictAttemptTower.StrictAttempt p m U r := by
  have hrec := recTimeA_of_landing (p := p) (m := m) (e := e) hreach hU
  have hreg : RegenAtStrict p m U (n + (2 * K + 1)) ((r : ℤ) + 1) := by
    refine ⟨recordAt_of_syncPast hU, fun k hk i => ?_⟩
    have h := (mem_strictPos.mp hstrict).2 k hk i
    have h2 : relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) k i =
        (trajectory p m U (n + (2 * K + 1) + k)).pos i - ((r : ℤ) + 1) := rfl
    rw [h2] at h
    linarith
  show RegenAtStrict p m U (recTimeA p m U (r + 1)) ((r + 1 : ℕ) : ℤ)
  rw [hrec]
  have hcast : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rw [hcast]
  exact hreg

/-- The strict pieces of all defect sectors are contained in the canonical strict attempt. -/
theorem iUnion_strictPiece_subset (p : ℝ) (m n K r : ℕ) :
    (⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) ∩ ReachAll p m ⊆
      {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} := by
  rintro U ⟨hU, hreach⟩
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
  exact strictAttempt_of_syncPast hreach he.1 he.2

/-- **Bounded-defect synchronisation force for the canonical strict attempt.**

For `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, every `K`, `n`, `r` and every `enlMeas p m n`-measurable
`G` that sits in a defect sector `≤ 2K` below level `r` at time `n` and has no walker above `r`
before `n`,

  `ofReal (1-p)^((2K+1)N) * P(posPath ∈ strictPos) * mu G ≤ mu {StrictAttempt r}`.

The defect bound and the past-maximum clause are exactly the hypotheses of the word construction;
the seed factor `P(V)` is `SwarmSeed.strictPos_measure_ne_zero`-positive, and it is not dropped. -/
theorem strictAttempt_mass_ge (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (n K r : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ G, ∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} * (arrayMeasure N) G ≤
      (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} := by
  classical
  have hforce := syncWordSet_mass_ge_sum p (le_of_lt hp0) hp1 m n K r hG hsec
  have hstep1 : ∀ e : Fin N → Fin (K + 1),
      (arrayMeasure N) (G ∩ wordPiece p m n K r e) ≤
        (arrayMeasure N) {U : Array N |
          pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} := by
    intro e
    refine measure_mono ?_
    intro U hU
    refine ⟨hprev U hU.1, hU.2.1, ?_⟩
    have hword := hU.2.2
    rw [evWord_eq_steps] at hword
    exact fun u hu i => hword u hu i (Finset.mem_univ i)
  have hdisj : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' →
      Disjoint (strictPiece p m n K r e) (strictPiece p m n K r e') := by
    intro e e' hne
    exact Set.disjoint_of_subset_right (strictPiece_subset_wordPiece p m n K r e')
      (Set.disjoint_of_subset_left (strictPiece_subset_wordPiece p m n K r e)
        (disjoint_wordPiece p m n K r hne))
  have hunion : (arrayMeasure N) (⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) =
      ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (strictPiece p m n K r e) := by
    rw [measure_iUnion (μ := arrayMeasure N) hdisj
      (fun e => measurableSet_strictPiece p m n K r e), tsum_fintype]
  have hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ ReachAll p m := M4RecordGeom.ae_reachAll hp0 hp1 hm hN
  have hcongr : (arrayMeasure N) ((⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) ∩
        ReachAll p m) =
      (arrayMeasure N) (⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) := by
    refine MeasureTheory.measure_congr ?_
    filter_upwards [hae] with U hU
    exact propext ⟨fun h => h.1, fun h => ⟨h, hU⟩⟩
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} * (arrayMeasure N) G
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          (ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * (arrayMeasure N) G) := by
        ring
    _ ≤ (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (G ∩ wordPiece p m n K r e) := by
        simpa [mul_comm] using mul_le_mul_left hforce
          ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos})
    _ = ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          (arrayMeasure N) (G ∩ wordPiece p m n K r e) := Finset.mul_sum _ _ _
    _ ≤ ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          (arrayMeasure N) {U : Array N |
            pastProj p m (n + (2 * K + 1)) U ∈ syncPast p m n K r e} :=
        Finset.sum_le_sum fun e _ => by
          simpa [mul_comm] using mul_le_mul_left (hstep1 e)
            ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos})
    _ = ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (strictPiece p m n K r e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [wordPiece_fresh p m n K r e, mul_comm]
    _ = (arrayMeasure N) (⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) := hunion.symm
    _ = (arrayMeasure N) ((⋃ e : (Fin N → Fin (K + 1)), strictPiece p m n K r e) ∩
          ReachAll p m) := hcongr.symm
    _ ≤ (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} :=
        measure_mono (iUnion_strictPiece_subset p m n K r)


/-! ### 8. The canonical defect window, and non-degeneracy -/

/-- The canonical attempt window at a *fixed* time `n`: no walker above level `r` before `n`,
and at time `n` the defect below level `r` is at most `2K`.  This is a genuine
`enlMeas p m n`-event of the actual model, not a hypothesis placeholder. -/
noncomputable def defectWindow {N : ℕ} (p : ℝ) (m n K r : ℕ) : Set (Array N) :=
  {U : Array N | (∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ)) ∧
    ∃ e : Fin N → Fin (K + 1),
      ∀ i, (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)}

theorem measurableSet_defectWindow (p : ℝ) (m n K r : ℕ) :
    MeasurableSet[enlMeas p m n] (defectWindow (N := N) p m n K r) := by
  have h1 : MeasurableSet[enlMeas p m n]
      {U : Array N | ∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ)} := by
    have hset : {U : Array N | ∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ)} =
        ⋂ j ∈ Finset.range n, ⋂ i : Fin N,
          {U : Array N | (trajectory p m U j).pos i ≤ (r : ℤ)} := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
    rw [hset]
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun j hj => ?_
    exact MeasurableSet.iInter fun i =>
      (enl_pos_measurable p m n (le_of_lt (Finset.mem_range.mp hj)) i) measurableSet_Iic
  have h2 : MeasurableSet[enlMeas p m n]
      {U : Array N | ∃ e : Fin N → Fin (K + 1),
        ∀ i, (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)} := by
    have hset : {U : Array N | ∃ e : Fin N → Fin (K + 1),
        ∀ i, (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ)} =
        ⋃ e : (Fin N → Fin (K + 1)), syncSector p m n (r : ℤ) (fun i => (e i : ℕ)) := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, syncSector]
    rw [hset]
    exact MeasurableSet.iUnion fun e => measurableSet_syncSector_enl p m n (r : ℤ) _
  exact h1.inter h2

/-- **The force at the canonical defect window.**  Fully explicit, with no free event: for
`1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, every `K`, every time `n` and every level `r`,

  `ofReal (1-p)^((2K+1)N) * P(V) * mu (defectWindow n K r) ≤ mu {StrictAttempt r}`.

The constant depends only on `K`, `p`, `m`, `N` — not on `n` or `r`. -/
theorem strictAttempt_mass_ge_window (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (n K r : ℕ) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
        (arrayMeasure N) (defectWindow (N := N) p m n K r) ≤
      (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} :=
  strictAttempt_mass_ge p hp0 hp1 hm hN n K r (measurableSet_defectWindow p m n K r)
    (fun _ hU => hU.2) (fun _ hU => hU.1)

/-- The force constant is non-degenerate: `(1-p)^((2K+1)N) * P(V) ≠ 0`.  This is the only
positivity of the estimate; it is **not** uniform in `K`, because the exponent grows with the
defect bound `K` (and `0 < 1-p < 1`). -/
theorem strictAttempt_force_ne_zero (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (K : ℕ) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
      (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ ?_)
    (SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN)
  exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)

/-- **Conditional form.**  For any attempt window `G` of positive, finite mass, the conditional
probability of the canonical strict attempt at level `r+1` is at least
`(1-p)^((2K+1)N) * P(V)`. -/
theorem strictAttempt_cond_ge (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (n K r : ℕ) {G : Set (Array N)}
    (hG : MeasurableSet[enlMeas p m n] G)
    (hsec : ∀ U ∈ G, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ G, ∀ j, j < n → ∀ i, (trajectory p m U j).pos i ≤ (r : ℤ))
    (hG0 : (arrayMeasure N) G ≠ 0) (hGtop : (arrayMeasure N) G ≠ ⊤) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} ≤
      ((arrayMeasure N) G)⁻¹ *
        (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} := by
  have hmain := strictAttempt_mass_ge p hp0 hp1 hm hN n K r hG hsec hprev
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos}
      = 1 * (ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos}) := (one_mul _).symm
    _ = (((arrayMeasure N) G)⁻¹ * (arrayMeasure N) G) *
          (ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
            (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos}) := by
        rw [ENNReal.inv_mul_cancel hG0 hGtop]
    _ = ((arrayMeasure N) G)⁻¹ *
          ((ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
            (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos}) * (arrayMeasure N) G) := by
        ring
    _ ≤ ((arrayMeasure N) G)⁻¹ *
          (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r} := by
        simpa [mul_comm] using mul_le_mul_left hmain ((arrayMeasure N) G)⁻¹


/-- **The zero window is everything.**  At time `0` all walkers are at the origin, level `0`, so
the defect is `0 = 2·0` and there is no past to constrain. -/
theorem defectWindow_zero (p : ℝ) (m : ℕ) :
    defectWindow (N := N) p m 0 0 0 = univ := by
  ext U
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ⟨fun _ => 0, fun i => ?_⟩⟩
    simp

/-- **A fully unconditional positive-probability strict attempt.**  For `1/2 < p < 1`, `2 ≤ m`,
`2 ≤ N`, the *first* canonical strict attempt (`r = 0`, at the actual record time of level `1`)
has mass at least `(1-p)^N * P(V) > 0`:

  `ofReal (1-p)^N * mu {posPath ∈ strictPos} ≤ mu {StrictAttempt 0}`.

No invariant law, no nullity, no defect hypothesis: the window at time `0` is the whole space,
so the bounded-defect force applies with `K = 0`. -/
theorem firstAttempt_mass_ge (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ENNReal.ofReal (1 - p) ^ N *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} ≤
      (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U 0} := by
  have h := strictAttempt_mass_ge_window (N := N) p hp0 hp1 hm hN 0 0 0
  rw [defectWindow_zero, measure_univ, mul_one] at h
  simpa using h

/-- **The first canonical strict attempt is not a null event.** -/
theorem firstAttempt_mass_ne_zero (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U 0} ≠ 0 := by
  intro hzero
  have h := firstAttempt_mass_ge (N := N) p hp0 hp1 hm hN
  rw [hzero] at h
  have hc := strictAttempt_force_ne_zero (N := N) p hp0 hp1 hm hN 0
  have h2 : ENNReal.ofReal (1 - p) ^ ((2 * 0 + 1) * N) = ENNReal.ofReal (1 - p) ^ N := by norm_num
  rw [h2] at hc
  exact hc (nonpos_iff_eq_zero.mp h)


/-! ### 9. The conditional force: the attempt window on both sides

`strictAttempt_mass_ge` has the window `G` only on the left, because a general `enlMeas` event is
not a prefix event and `(freshlaw)` cannot be applied to `G ∩ piece`.  An *actual* attempt window
is prefix-determined (`{prefOf p m n U ∈ A₀}`), and then the whole piece `G ∩ wordPiece e` is a
single prefix event: the conditions "no walker above `r` before `n`", "defect `≤ 2K` at `n`" and
"the word is followed" are all path conditions.  The force then sharpens to a genuine
conditional bound with `G` on both sides. -/

/-- The prefix event of length `t = n+(2K+1)`: the window prefix lies in `A₀` and the
synchronising word of sector `e` is followed. -/
noncomputable def syncPastOf (p : ℝ) (m n K r : ℕ) (A₀ : Set (Pref N n))
    (e : Fin N → Fin (K + 1)) : Set (Pref N (n + (2 * K + 1))) :=
  syncPast p m n K r e ∩ {π | (fun s : Fin (n + 1) => π ⟨s.1, by omega⟩) ∈ A₀}

theorem measurableSet_syncPastOf (p : ℝ) (m n K r : ℕ) (A₀ : Set (Pref N n))
    (e : Fin N → Fin (K + 1)) : MeasurableSet (syncPastOf p m n K r A₀ e) :=
  Set.Countable.measurableSet (Set.countable_univ.mono (Set.subset_univ _))

/-- A prefix-determined window is `enlMeas`-measurable at time `n`. -/
theorem measurableSet_prefWindow (p : ℝ) (m n : ℕ) (A₀ : Set (Pref N n)) :
    MeasurableSet[enlMeas p m n] {U : Array N | prefOf p m n U ∈ A₀} := by
  have hEq : {U : Array N | prefOf p m n U ∈ A₀} = ⋃ γ ∈ A₀, prefAgree p m γ := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨prefOf p m n U, h, prefAgree_prefOf U⟩,
      fun ⟨γ, hγ, hU⟩ => by rw [prefOf_eq_of_mem_prefAgree hU]; exact hγ⟩
  rw [hEq]
  exact MeasurableSet.biUnion (Set.countable_univ.mono (Set.subset_univ A₀))
    (fun γ _ => enl_prefAgree_measurable p m n γ)

/-- The window meets word piece `e` in exactly the prefix event `syncPastOf`. -/
theorem prefWindow_inter_wordPiece (p : ℝ) (m n K r : ℕ) (A₀ : Set (Pref N n))
    (e : Fin N → Fin (K + 1))
    (hprev : ∀ U ∈ {U : Array N | prefOf p m n U ∈ A₀}, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) :
    {U : Array N | pastProj p m (n + (2 * K + 1)) U ∈ syncPastOf p m n K r A₀ e} =
      ({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) := by
  ext U
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, syncPast_subset_wordPiece h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(pastProj_mem_syncPast (hprev U h1)).mpr h2, h1⟩

/-- **The attempt force with the window on both sides.**  For `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`,
every `K`, `n`, level `r` and every set `A₀` of position prefixes at time `n` whose window lies
in a defect sector `≤ 2K` below `r` and has no walker above `r` before `n`,

  `ofReal (1-p)^((2K+1)N) * P(V) * μ G ≤ μ (G ∩ {StrictAttempt r})`,  `G = {prefOf p m n U ∈ A₀}`,

i.e. on the attempt window `G` the canonical strict attempt of level `r+1` succeeds with
conditional probability at least `ofReal (1-p)^((2K+1)N) * P(V)`. -/
theorem strictAttempt_mass_ge_prefix (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (n K r : ℕ) {A₀ : Set (Pref N n)}
    (hsec : ∀ U ∈ {U : Array N | prefOf p m n U ∈ A₀},
      ∃ e : Fin N → Fin (K + 1), ∀ i,
        (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ {U : Array N | prefOf p m n U ∈ A₀}, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
        (arrayMeasure N) {U : Array N | prefOf p m n U ∈ A₀} ≤
      (arrayMeasure N) ({U : Array N | prefOf p m n U ∈ A₀} ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r}) := by
  classical
  have hGmeas : MeasurableSet[enlMeas p m n] {U : Array N | prefOf p m n U ∈ A₀} :=
    measurableSet_prefWindow p m n A₀
  have hforce := syncWordSet_mass_ge_sum p (le_of_lt hp0) hp1 m n K r hGmeas hsec
  -- the fresh factor on each piece
  have hfresh : ∀ e : Fin N → Fin (K + 1),
      (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
        (arrayMeasure N) ({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} := by
    intro e
    have h := fresh_of_syncPast_subset (p := p) (m := m) (n := n) (K := K) (r := r) (e := e)
      (A := syncPastOf p m n K r A₀ e) (measurableSet_syncPastOf p m n K r A₀ e)
      Set.inter_subset_left
    rw [prefWindow_inter_wordPiece p m n K r A₀ e hprev] at h
    exact h
  -- the measure of the windowed word event
  have hunion : (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩
        syncWordSet p m n K r) ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
      ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩
        wordPiece p m n K r e) ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
    have hd : ∀ e e' : Fin N → Fin (K + 1), e ≠ e' →
        Disjoint (({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) ∩
            {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos})
          (({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e') ∩
            {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
      intro e e' hne
      rw [Set.disjoint_left]
      intro U h1 h2
      exact Set.disjoint_left.mp (disjoint_wordPiece p m n K r hne) h1.1.2 h2.1.2
    have hm : ∀ e : Fin N → Fin (K + 1),
        MeasurableSet (({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
      intro e
      refine (MeasurableSet.inter ?_ (measurableSet_wordPiece p m n K r e)).inter ?_
      · exact enlMeas_le p m n _ hGmeas
      · exact (measurable_relFuture p m (n + (2 * K + 1)) ((r : ℤ) + 1) N) measurableSet_strictPos
    have hEq : (({U : Array N | prefOf p m n U ∈ A₀} ∩ syncWordSet p m n K r) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) =
        ⋃ e : (Fin N → Fin (K + 1)), (({U : Array N | prefOf p m n U ∈ A₀} ∩
          wordPiece p m n K r e) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
      rw [syncWordSet_eq_iUnion, Set.inter_iUnion, Set.iUnion_inter]
    rw [hEq, measure_iUnion (μ := arrayMeasure N) hd hm, tsum_fintype]
  -- the union is inside the canonical strict attempt
  have hsubset : (({U : Array N | prefOf p m n U ∈ A₀} ∩ syncWordSet p m n K r) ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) ∩
        ReachAll p m ⊆
      ({U : Array N | prefOf p m n U ∈ A₀} ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r}) := by
    rintro U ⟨⟨⟨hG, hSW⟩, hS⟩, hreach⟩
    refine ⟨hG, ?_⟩
    have hSW' : U ∈ ⋃ e : (Fin N → Fin (K + 1)), wordPiece p m n K r e := hSW
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hSW'
    exact strictAttempt_of_syncPast hreach ((pastProj_mem_syncPast (hprev U hG)).mpr he) hS
  have hae : ∀ᵐ U ∂(arrayMeasure N), U ∈ ReachAll p m := M4RecordGeom.ae_reachAll hp0 hp1 hm hN
  have hcongr : (arrayMeasure N) ((({U : Array N | prefOf p m n U ∈ A₀} ∩
        syncWordSet p m n K r) ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) ∩
        ReachAll p m) =
      (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩ syncWordSet p m n K r) ∩
        {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
    refine MeasureTheory.measure_congr ?_
    filter_upwards [hae] with U hU
    exact propext ⟨fun h => h.1, fun h => ⟨h, hU⟩⟩
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
        (arrayMeasure N) {U : Array N | prefOf p m n U ∈ A₀}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          (ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
            (arrayMeasure N) {U : Array N | prefOf p m n U ∈ A₀}) := by ring
    _ ≤ (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          ∑ e : (Fin N → Fin (K + 1)),
            (arrayMeasure N) ({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) := by
        simpa [mul_comm] using mul_le_mul_left hforce
          ((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos})
    _ = ∑ e : (Fin N → Fin (K + 1)), (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
          (arrayMeasure N) ({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) :=
        Finset.mul_sum _ _ _
    _ = ∑ e : (Fin N → Fin (K + 1)),
          (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩ wordPiece p m n K r e) ∩
            {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hfresh e, mul_comm]
    _ = (arrayMeasure N) (({U : Array N | prefOf p m n U ∈ A₀} ∩ syncWordSet p m n K r) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) :=
        hunion.symm
    _ = (arrayMeasure N) ((({U : Array N | prefOf p m n U ∈ A₀} ∩ syncWordSet p m n K r) ∩
          {U : Array N | relFuture p m U (n + (2 * K + 1)) ((r : ℤ) + 1) ∈ strictPos}) ∩
          ReachAll p m) := hcongr.symm
    _ ≤ (arrayMeasure N) ({U : Array N | prefOf p m n U ∈ A₀} ∩
          {U : Array N | RawStrictAttemptTower.StrictAttempt p m U r}) :=
        measure_mono hsubset

end SyncAttemptForce
