/-
# Row-level strict escape: the fresh factor summed over the record time of a level

`SwarmStoppedPast.stopped_escape` is the *fixed-time* stopped-past factorisation.  The paper's
adaptive attempt row conditions on the whole past event `{Q ≥ q}` and then sums the identity over
the possible row times and levels ("applying `(freshlaw)` on each event `{S_q = t, r_q = d}` and
summing over `d,t`").  This file performs that sum for one level `d`, at the level of an
**arbitrary measurable past event `A` that is pinned by the position prefix on every record cell
of level `d`** — which is exactly the form in which the adaptive row past is available.

Main results:

* `recordAt_unique` — at most one record time per level (re-proved here from the `RecordAt`
  clauses alone, so no private build of `FreshRecordStrict` is needed);
* `measure_record_strictFut` — for every measurable `A` pinned by the prefix on the level-`d`
  record cells,
  `μ(A ∩ ⋃_t (record_d(t) ∩ strictFut(t,d))) = P(V) * μ(A ∩ ⋃_t record_d(t))`.
  The constant `P(V)` is the same for every level, time and past.

Not claimed: the adaptive tower `S_q, T_q, Q`, the geometric tail, `μ{InfiniteFailure} = 0`.
-/
import Swarm.StoppedPast

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

namespace SwarmStoppedPast

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## Uniqueness of the record time at a level -/

/-- At most one record time at a fixed level: a record at `(t,d)` forces every walker to be at
`d` at time `t` and strictly below `d` at every earlier time, so an earlier record at the same
level contradicts it. -/
theorem recordAt_unique {p : ℝ} {m : ℕ} {U : Array N} {t t' : ℕ} {d : ℤ}
    (h : RecordAt p m U t d) (h' : RecordAt p m U t' d) : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exfalso
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have h1 : (trajectory p m U t).pos i < d := h'.1 t hlt i
    have h2 : (trajectory p m U t).pos i = d := h.2 i
    omega
  · exact heq
  · exfalso
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have h1 : (trajectory p m U t').pos i < d := h.1 t' hgt i
    have h2 : (trajectory p m U t').pos i = d := h'.2 i
    omega

/-- The strict future after a record at `(t,d)`: no walker ever returns to level `≤ d`. -/
def strictFut (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) : Set (Array N) :=
  {U | relFuture p m U t d ∈ strictPos (N := N)}

theorem measurableSet_strictFut (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ) :
    MeasurableSet (strictFut (N := N) p m t d) :=
  (measurable_relFuture p m t d N) measurableSet_strictPos

/-- On a record at `(t,d)`, the strict future is exactly "the row does not return". -/
theorem strictFut_iff_noReturn {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (hrec : RecordAt p m U t d) :
    U ∈ strictFut (N := N) p m t d ↔ ∀ n, t < n → ∀ i, d < (trajectory p m U n).pos i :=
  (noReturn_iff_strictPos hrec).symm

/-! ## The summed escape at a level -/

/-- **Row-level escape.**  Let `A` be a measurable past event that, on the record cells of level
`d`, is pinned by the position prefix (hypothesis `hpin`: on `recordSet t d` the event `A` agrees
with a prefix condition `C t`).  Then the mass of "past in `A`, a level-`d` record whose future
never returns" is `P(V)` times the mass of "past in `A` and a level-`d` record".  This is the
paper's "sum over `t`" step at one level, in the exact form the adaptive tower consumes. -/
theorem measure_record_strictFut {p : ℝ} {m : ℕ} {d : ℤ}
    {A : Set (Array N)} (hA : MeasurableSet A)
    (C : (t : ℕ) → Set (Pfx N t)) (hC : ∀ t, MeasurableSet (C t))
    (hpin : ∀ t, A ∩ recordSet p m t d
      = {U : Array N | pfxOf (N := N) p m t U ∈ C t} ∩ recordSet p m t d) :
    (arrayMeasure N) (A ∩ ⋃ t, (recordSet p m t d ∩ strictFut (N := N) p m t d))
      = (arrayMeasure N) (A ∩ ⋃ t, recordSet p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  classical
  set ν := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} with hν
  -- the cell `A ∩ record ∩ strictFut` is the prefix condition together with the strict record
  have hcell : ∀ t, A ∩ (recordSet p m t d ∩ strictFut (N := N) p m t d)
      = {U : Array N | pfxOf (N := N) p m t U ∈ C t ∧ RecordAt p m U t d ∧
          relFuture p m U t d ∈ strictPos (N := N)} := by
    intro t
    rw [← Set.inter_assoc, hpin t]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, strictFut, recordSet]
    tauto
  -- the prefix condition alone is the past event on the record cell
  have hpast : ∀ t, {U : Array N | pfxOf (N := N) p m t U ∈ C t ∧ RecordAt p m U t d}
      = A ∩ recordSet p m t d := by
    intro t
    rw [hpin t]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, recordSet]
  have hdisj : Pairwise (fun t t' => Disjoint
      (A ∩ (recordSet p m t d ∩ strictFut (N := N) p m t d))
      (A ∩ (recordSet p m t' d ∩ strictFut (N := N) p m t' d))) := by
    intro t t' hne
    rw [Set.disjoint_left]
    rintro U ⟨-, ⟨h1, -⟩⟩ ⟨-, ⟨h2, -⟩⟩
    exact hne (recordAt_unique h1 h2)
  have hmeas : ∀ t, MeasurableSet (A ∩ (recordSet p m t d ∩ strictFut (N := N) p m t d)) :=
    fun t => hA.inter ((measurableSet_recordSet p m t d).inter (measurableSet_strictFut p m t d))
  have hEq : A ∩ ⋃ t, (recordSet p m t d ∩ strictFut (N := N) p m t d)
      = ⋃ t, A ∩ (recordSet p m t d ∩ strictFut (N := N) p m t d) := by
    rw [Set.inter_iUnion]
  -- the pointwise fresh factor
  have hterm : ∀ t, (arrayMeasure N) (A ∩ (recordSet p m t d ∩ strictFut (N := N) p m t d))
      = ν * (arrayMeasure N) (A ∩ recordSet p m t d) := by
    intro t
    rw [hcell t, stopped_escape (N := N) (p := p) (m := m) (t := t) (d := d)
      (C := C t) (hC t), hpast t]
    exact mul_comm _ _
  -- the sums
  have hdisj2 : Pairwise (fun t t' => Disjoint (A ∩ recordSet p m t d)
      (A ∩ recordSet p m t' d)) := by
    intro t t' hne
    rw [Set.disjoint_left]
    rintro U ⟨-, h1⟩ ⟨-, h2⟩
    exact hne (recordAt_unique h1 h2)
  have hmeas2 : ∀ t, MeasurableSet (A ∩ recordSet p m t d) :=
    fun t => hA.inter (measurableSet_recordSet p m t d)
  have hsum2 : (∑' t : ℕ, (arrayMeasure N) (A ∩ recordSet p m t d))
      = (arrayMeasure N) (A ∩ ⋃ t, recordSet p m t d) := by
    rw [← measure_iUnion hdisj2 hmeas2, ← Set.inter_iUnion]
  rw [hEq, measure_iUnion hdisj hmeas, tsum_congr hterm, ENNReal.tsum_mul_left, hsum2,
    mul_comm]

/-- **The unconditioned per-level escape.**  For every level `d`, the mass of the level-`d`
records whose future never returns to `d` is exactly `P(V)` times the total mass of the
level-`d` records.  No `ReachAll`, clock or `m`/`N` restriction enters: the statement is the
literal level-summed `(freshlaw)`. -/
theorem measure_strictFut_tsum {p : ℝ} {m : ℕ} {d : ℤ} :
    (arrayMeasure N) (⋃ t, (recordSet p m t d ∩ strictFut (N := N) p m t d))
      = (arrayMeasure N) (⋃ t, recordSet p m t d)
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have h := measure_record_strictFut (N := N) (p := p) (m := m) (d := d)
    (A := univ) MeasurableSet.univ (C := fun _ => univ) (fun _ => MeasurableSet.univ)
    (fun t => by simp)
  simpa using h

end SwarmStoppedPast
