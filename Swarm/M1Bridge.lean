/-
# The zero-to-positive bridge for the literal strict-attempt tower

Context.  `Swarm/RowTail.lean` (`SwarmRowTail`) proves, from the genuine R1
transfer at the forced Dirac start, that almost every array has a *regeneration at a canonical
record time*:

  `∀ᵐ U, ∃ r : ℕ, RegenAtStrict p m U (recTimeA p m U r) ((r : ℤ))`,

and hence the dichotomy `∃ r, StrictAttempt p m U r ∨ RegenAtStrict p m U 0 0`.  The second
alternative is the *level-zero* regeneration: the tower's row `0` starts at level `0`, and if it
never returns then no later row is started, so the canonical positive-level attempt
`StrictAttempt r = RegenAtStrict U (recTimeA (r+1)) (r+1)` need not exist.  Level-zero
strictness does **not** by itself produce a positive level: the path may return to level `1`
forever after.

This file closes that gap in the one place where it is genuinely closable, using a *different*
input, not a level substitution: the one-stage fullness identity of
`Swarm/Induction.lean` (`SwarmSelInd.full_iff_noRegen_null`), which
`Swarm/HfullBridge.lean` derives from a genuine invariant stopped-record law, itself derived
from the stated record tightness.  Fullness says exactly

  `arrayMeasure {posPath ∈ V ∧ no positive-level regeneration} = 0`,

where `V = strictPos`, and the level-zero alternative *is* `posPath ∈ V`
(`mem_seed_iff_levelZero`).  So the pathological "keeps above the origin but returns below every
level it reaches" histories are null, hence a.e. a positive-level strict attempt exists.

None of this replaces tightness by invariance: the invariant law is only used through its Kac
consequence, and the actual array measure is never identified with a stationary law.
-/
import Swarm.RowTail
import Swarm.HfullBridge

open MeasureTheory Set ProbabilityTheory Filter Topology Classical
open MeasureTheory.Filtration
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open SwarmAttemptTower SwarmStoppedPast
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw RecordoSupply SwarmRec
open SimJump SimJump.RecKernel
open WCJF.ActPath
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace M1Bridge

variable {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} {U : Array N}

/-! ## 1. The three dictionary entries between the tower and the path language -/

/-- `posPath` is the position path, coordinate for coordinate (definitional). -/
theorem posPath_apply_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    SwarmRestart.posPath p m U n i = (trajectory p m U n).pos i := rfl

/-- **The level-zero alternative is exactly the seed event.**  `RegenAtStrict p m U 0 0` says
that at time `0` all walkers sit at the origin (which is automatic,
`SwarmFresh.posPath_zero`) and that every walker is strictly above `0` from time `1` on; that is
literally `posPath p m U ∈ seed = SwarmFresh.strictPos`. -/
theorem mem_seed_iff_levelZero (p : ℝ) (m : ℕ) (U : Array N) :
    SwarmRestart.posPath p m U ∈ SwarmSelInd.seed ↔ RegenAtStrict p m U 0 0 := by
  rw [SwarmSelInd.seed, mem_strictPos, RegenAtStrict]
  constructor
  · rintro ⟨-, hpos⟩
    refine ⟨⟨fun s hs => absurd hs (Nat.not_lt_zero s), fun i => SwarmFresh.posPath_zero p m U i⟩,
      fun n hn i => ?_⟩
    simpa only [Nat.zero_add, posPath_apply_eq] using hpos n hn i
  · rintro ⟨-, hpos⟩
    refine ⟨fun i => SwarmFresh.posPath_zero p m U i, fun n hn i => ?_⟩
    simpa only [Nat.zero_add, posPath_apply_eq] using hpos n hn i

/-- **Path-language and array-language strict regeneration agree.**  `SwarmSel.isRegen` is
`pathRec` plus a strictly positive future; `RecordAt` is `pathRec` for `posPath`
(`SwarmChain.pathRec_iff`), and the future clauses differ only by the shift `t + n`. -/
theorem isRegen_posPath_iff (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) :
    SwarmSel.isRegen t d (SwarmRestart.posPath p m U) ↔ RegenAtStrict p m U t d := by
  rw [SwarmSel.isRegen, RegenAtStrict, SwarmChain.pathRec_iff]
  constructor
  · rintro ⟨hrec, hstay⟩
    refine ⟨hrec, fun n hn i => ?_⟩
    simpa only [posPath_apply_eq] using hstay (t + n) (by omega) i
  · rintro ⟨hrec, hstay⟩
    refine ⟨hrec, fun n hn i => ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, n = t + k := ⟨n - t, by omega⟩
    subst hk
    simpa only [posPath_apply_eq] using hstay k (by omega) i

/-- **Positive-level regeneration is a literal strict attempt.**  A strict regeneration at
level `1 ≤ d` in the actual array sits at the running maximum `d` at the simultaneous record
time `t`, and is strictly below `d` before it; therefore `t` is the *canonical* first time the
running maximum reaches `d` (`recTimeA p m U d.toNat`), and the level is positive, so the
canonical attempt index `d.toNat - 1` succeeds.  `ReachAll` is needed only to make `recTimeA`
the genuine first-hit time, and it holds almost surely (`M4RecordGeom.ae_reachAll`). -/
theorem exists_strictAttempt_of_regenAtStrict (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hR : U ∈ ReachAll p m) (hd : 1 ≤ d) (hreg : RegenAtStrict p m U t d) :
    ∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r := by
  have hrec : RecordAt p m U t d := hreg.1
  set r : ℕ := d.toNat with hr
  have hdr : ((r : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hrpos : 0 < r := by omega
  have hmax : RecordDefect.runMax (actX p m U) t = (r : ℤ) := by
    rw [SwarmRowTail.recordAt_runMax_eq hrec, hdr]
  have hne : ∀ j < t, RecordDefect.runMax (actX p m U) j ≠ (r : ℤ) := by
    intro j hj
    have h := SwarmRowTail.recordAt_runMax_lt hrec j hj
    omega
  have htime : recTimeA p m U r = t := (recTimeA_eq_iff p m U r t hR).mpr ⟨hmax, hne⟩
  exact ⟨r - 1, SwarmRowTail.strictAttempt_of_pos_level hrpos (by rw [htime, hdr]; exact hreg)⟩

/-- The reverse dictionary entry: a strict attempt is a positive-level strict regeneration. -/
theorem exists_posRegen_of_strictAttempt (p : ℝ) (m : ℕ) (U : Array N) {r : ℕ}
    (h : RawStrictAttemptTower.StrictAttempt p m U r) :
    ∃ t : ℕ, ∃ d : ℤ, 1 ≤ d ∧ RegenAtStrict p m U t d :=
  ⟨recTimeA p m U (r + 1), ((r + 1 : ℕ) : ℤ), by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r),
    h⟩

/-- **The exact equivalence, on `ReachAll`, between the tower's success event and the path
language's "raw first positive regeneration level is finite".**  This is the direct
selected-cell-to-`StrictAttempt` map: it does not use any selected-block law, only that a
positive-level strict regeneration has a canonical time. -/
theorem exists_strictAttempt_iff_posRegen (p : ℝ) (m : ℕ) (U : Array N)
    (hR : U ∈ ReachAll p m) :
    (∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r) ↔
      ∃ t : ℕ, ∃ d : ℤ, 1 ≤ d ∧ RegenAtStrict p m U t d := by
  constructor
  · rintro ⟨r, hr⟩
    exact exists_posRegen_of_strictAttempt p m U hr
  · rintro ⟨t, d, hd, hreg⟩
    exact exists_strictAttempt_of_regenAtStrict p m U hR hd hreg

/-- **The same equivalence in the raw `D ≠ ⊤` form used by the selection files.**  On
`ReachAll`, the tower reaches a positive level strictly iff the raw first-regeneration level
`RegenPath.D` of the position path is finite. -/
theorem exists_strictAttempt_iff_rawD_ne_top (p : ℝ) (m : ℕ) (U : Array N)
    (hR : U ∈ ReachAll p m) :
    (∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r) ↔
      RegenPath.D (SwarmRestart.posPath p m U) ≠ ⊤ := by
  rw [exists_strictAttempt_iff_posRegen p m U hR]
  rw [SwarmActualHfull.raw_D_ne_top_iff_exists_isRegen (SwarmRestart.posPath p m U)
    (SwarmFresh.posPath_zero p m U) (fun n i => SwarmFresh.posPath_step p m U n i)]
  constructor
  · rintro ⟨t, d, hd, hreg⟩
    exact ⟨t, d, hd, (isRegen_posPath_iff p m U t d).mpr hreg⟩
  · rintro ⟨t, d, hd, hreg⟩
    exact ⟨t, d, hd, (isRegen_posPath_iff p m U t d).mp hreg⟩


/-! ## 2. The bridge: full selection kills the level-zero-only branch -/

/-- **The null set on which the level-zero branch hides.**  `Z` is exactly the event on which
the swarm stays strictly above the origin forever after time `0` (so `posPath ∈ seed`) but never
regenerates at any positive level.  This is null under the one-stage fullness identity
(`SwarmSelInd.full_iff_noRegen_null`), and it contains every history on which the tower produces
no positive-level strict attempt. -/
def levelZeroOnly (N : ℕ) (p : ℝ) (m : ℕ) : Set (Array N) :=
  {U | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed ∧
    ¬ ∃ (t : ℕ) (d : ℤ), 1 ≤ d ∧ SwarmSel.isRegen t d (SwarmRestart.posPath p m U)}

/-- Pointwise core: on `ReachAll`, a history with no positive-level strict attempt is either off
the seed or is a `levelZeroOnly` history.  The dichotomy
`StrictAttempt ∨ RegenAtStrict 0 0` supplies the seed membership in the second case, and the
canonical-time reduction (`exists_strictAttempt_of_regenAtStrict`) forbids any positive-level
regeneration in the first case. -/
theorem mem_levelZeroOnly_of_not_strictAttempt (p : ℝ) (m : ℕ) (U : Array N)
    (hR : U ∈ ReachAll p m)
    (hdich : (∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r) ∨
      RegenAtStrict p m U 0 0)
    (hcon : ¬ ∃ r : ℕ, RawStrictAttemptTower.StrictAttempt p m U r) :
    U ∈ levelZeroOnly N p m := by
  refine ⟨?_, ?_⟩
  · rcases hdich with h | h
    · exact absurd h hcon
    · exact (mem_seed_iff_levelZero p m U).mpr h
  · rintro ⟨t, d, hd, hreg⟩
    exact hcon (exists_strictAttempt_of_regenAtStrict p m U hR hd ((isRegen_posPath_iff p m U t d).mp hreg))

/-- **The zero-to-positive bridge.**  From (i) the genuine row-recurrence input, (ii) `ReachAll`
a.e. and (iii) the one-stage fullness identity for the *actual* array measure, almost every
array has a literal positive-level strict attempt.

Nothing here conditions on the seed and nothing identifies the array law with a stationary law:
`full_iff_noRegen_null` is applied to the raw measure `arrayMeasure N` and the raw event
`posPath ∈ seed`, and the null event `Z` is an honest array event.  No level substitution is
used: the level-zero branch is not promoted, it is *excluded*, because it forces `posPath ∈ seed`
and hence would have to be a positive-measure subset of the null set `Z`. -/
theorem ae_exists_strictAttempt_of_fullSelection (p : ℝ) (m : ℕ)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (hrec : ∀ᵐ U ∂(arrayMeasure N), U ∈ SwarmRowTail.RowRecurrence p m)
    (hfull : (arrayMeasure N) (⋃ i : ℕ × ℕ,
        SwarmSel.selSet (p := p) (m := m) i.1 ((i.2 : ℤ) + 1) Set.univ)
      = (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ SwarmSelInd.seed}) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ r, RawStrictAttemptTower.StrictAttempt p m U r := by
  have hNpos : 0 < N := by omega
  have hν : 0 < (arrayMeasure N) {U : Array N | SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos} :=
    SwarmRowTail.strictPos_measure_lt_top_pos hp0 hp1 hm hN
  have hdich := SwarmRowTail.ae_exists_strictAttempt_or_levelZero (N := N) hp0 hp1 hm hN hrec hν
  have hreach := M4RecordGeom.ae_reachAll (N := N) (p := p) (m := m) hp0 hp1 hm hN
  have hnull : (arrayMeasure N) (levelZeroOnly N p m) = 0 :=
    (SwarmSelInd.full_iff_noRegen_null hNpos).mp hfull
  have haez : ∀ᵐ U ∂(arrayMeasure N), U ∉ levelZeroOnly N p m := by
    rw [MeasureTheory.ae_iff]
    simpa only [levelZeroOnly, Set.mem_setOf_eq, not_not] using hnull
  filter_upwards [haez, hreach, hdich] with U hZ hRU hdichU
  by_contra hcon
  exact hZ (mem_levelZeroOnly_of_not_strictAttempt p m U hRU hdichU hcon)

end M1Bridge
