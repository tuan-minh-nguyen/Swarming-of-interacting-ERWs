/-
# Finite-index strict-attempt epochs from one defect-qualified window

`Swarm/SyncAttemptForce.lean` proves the bounded-defect synchronisation force
**once**, at a fixed attempt window: for a position-prefix window `G` at time `n`
whose walkers sit in an even-defect sector `≤ 2K` below level `r` (and never above
`r` before `n`),

  `ofReal (1-p)^((2K+1)N) * P(V) * μ G ≤ μ (G ∩ {StrictAttempt r})`.

`areas/kac/ClockOccupation.lean` proves a *tower of landings* along the actual record
clock, `q_K * (ofReal (1-p)^N)^j * μ G ≤ μ(...)`, but it stops at the landing and
carries no strict future; it records explicitly that "the strict-future factor `P(V)`
is still required for `RegenAtStrict`" and that the geometric tower cannot prove
infinite-attempt success.

This file closes exactly the composition gap between those two results: it iterates
the *two-sided* (past carried on both sides) synchronisation force along a finite
block of consecutive level-advance epochs, and attaches the strict future only at
the **last** link.  The reason the order is forced is deterministic: the strict
future `strictPos` says every walker is strictly above the landing level at every
later time, which makes any further landing at a *higher* level impossible.  So the
seed factor has to be paid on the last epoch, and the epoch chain has to be built
with the low-level (non-strict) force.

Main results, in order.

* `window`, `landing` — the position-prefix window at horizon `n`, and the
  synchronisation landing window one epoch later.
* `prefOf_eq_pastProj` — the two prefix maps of the campaign agree definitionally.
* `window_landing` — the landing window is exactly the old window together with the
  synchronisation word set: `win(n+2K+1) = win(n) ∩ syncWordSet`.
* `epoch_force` — the one-epoch force `q_K * μ G ≤ μ G'` on the actual array, with
  the new window explicitly *inside* the old one, and the two deterministic facts
  that make the chain iterable: no walker above `r+1` before the new horizon, and
  every walker exactly at `r+1` there (defect zero, so the next epoch may be run at
  `K = 0` for the price `(1-p)^N`).
* `epoch_tower` — the `j`-fold chain: one window at level `r+1+j`, inside the
  original window, whose walkers are all exactly at `r+1+j`, with product constant
  `((1-p)^N)^j`.
* `tower_force` — **the finite-index strict-attempt estimate**: for every `j`,
  `q_K * ((1-p)^N)^(j+1) * P(V) * μ(band) ≤ μ(band ∩ {StrictAttempt (r+1+j)})`,
  i.e. one and the same past window forces genuine strict regeneration at the
  shifted level `r+1+j`, with the seed factor paid once.

Honest scope: this is a finite-index block estimate.  The constants are geometric
with ratio `(1-p)^N < 1`, so the tower gives no uniform-in-`j` positive lower bound,
no `∑' FirstSuccessCell = 1`, no nullity of `D = ⊤`, no invariant law and no
`MainClaim`.  What it does give is a *positive* lower bound for the canonical strict
attempt of every index `L ≥ r+1` from one fixed window event, which the one-epoch
force cannot produce because that needs a window at the attempt's own level.
-/
import Swarm.SyncAttemptForce

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarm.StrictEpoch

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRestart SwarmFresh SwarmSeg DefectSync
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. Windows, and the landing window one epoch later -/

/-- The position-prefix window at horizon `n`: the set of arrays whose position
prefix of horizon `n` lies in `A`. -/
noncomputable def window (p : ℝ) (m n : ℕ) (A : Set (Pref N n)) : Set (Array N) :=
  {U | prefOf p m n U ∈ A}

theorem window_mono {p : ℝ} {m n : ℕ} {A B : Set (Pref N n)} (h : A ⊆ B) :
    window (N := N) p m n A ⊆ window (N := N) p m n B :=
  fun _ hU => h hU

/-- The campaign's two prefix maps agree definitionally: `prefOf` is `pastProj`. -/
theorem prefOf_eq_pastProj (p : ℝ) (m n : ℕ) (U : Array N) :
    prefOf p m n U = pastProj p m n U := rfl

/-- The window one synchronisation epoch later: the union over defect sectors of the
prefix event "the sector at `n` was `e`, no walker above `r` before `n`, and the
compensating word was followed". -/
noncomputable def landing (p : ℝ) (m n K r : ℕ) (A : Set (Pref N n)) :
    Set (Pref N (n + (2 * K + 1))) :=
  ⋃ e : Fin N → Fin (K + 1), SyncAttemptForce.syncPastOf p m n K r A e

/-- The landing window at one defect sector, identified with the old window together
with that sector's synchronisation word piece (`prefWindow_inter_wordPiece` of
`SyncAttemptForce`, restated in terms of `window`). -/
theorem window_inter_piece (p : ℝ) (m n K r : ℕ) {A : Set (Pref N n)}
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ))
    (e : Fin N → Fin (K + 1)) :
    window (N := N) p m (n + (2 * K + 1)) (SyncAttemptForce.syncPastOf p m n K r A e) =
      window (N := N) p m n A ∩ SyncAttemptForce.wordPiece p m n K r e := by
  simp only [window, prefOf_eq_pastProj]
  exact SyncAttemptForce.prefWindow_inter_wordPiece p m n K r A e hprev

/-- **The landing window is the old window together with the synchronisation word
set.**  This is the identification that lets the force be stated with the past on
both sides. -/
theorem window_landing (p : ℝ) (m n K r : ℕ) {A : Set (Pref N n)}
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) :
    window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A) =
      window (N := N) p m n A ∩ SyncAttemptForce.syncWordSet p m n K r := by
  ext U
  constructor
  · intro hU
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
    have hmem : U ∈ window (N := N) p m (n + (2 * K + 1))
        (SyncAttemptForce.syncPastOf p m n K r A e) := he
    rw [window_inter_piece (N := N) p m n K r hprev e] at hmem
    exact ⟨hmem.1, Set.mem_iUnion.mpr ⟨e, hmem.2⟩⟩
  · rintro ⟨hA, hW⟩
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hW
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    have hmem : U ∈ window (N := N) p m (n + (2 * K + 1))
        (SyncAttemptForce.syncPastOf p m n K r A e) := by
      rw [window_inter_piece (N := N) p m n K r hprev e]
      exact ⟨hA, he⟩
    exact hmem

/-! ## 2. The one-epoch force, with the past on both sides -/

/-- **One epoch of synchronisation, with the past carried into the conclusion.**
For a window at time `n` in the even-defect sector `≤ 2K` below level `r` with no
walker above `r` before `n`, the synchronisation word lands every walker exactly at
`r+1` at time `n + 2K+1`, and

  `ofReal (1-p)^((2K+1)N) * μ G ≤ μ G'`,  `G = window n`,  `G' = window (n+2K+1)`.

`G'` is a *window* (a prefix event), which is what makes the epoch iterable: the
`(freshlaw)` factor of the campaign can be applied to a prefix event, but not to a
general `enlMeas` past. -/
theorem epoch_force (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m n K r : ℕ)
    {A : Set (Pref N n)}
    (hsec : ∀ U ∈ window (N := N) p m n A, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) (window (N := N) p m n A) ≤
      (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
        (landing (N := N) p m n K r A)) := by
  classical
  set G : Set (Array N) := window (N := N) p m n A with hG
  have hGmeas : MeasurableSet[enlMeas p m n] G :=
    SyncAttemptForce.measurableSet_prefWindow p m n A
  have hforce := SyncAttemptForce.syncWordSet_mass_ge_sum p hp0 hp1 m n K r hGmeas hsec
  have hdisj : Pairwise (Function.onFun Disjoint
      fun e : Fin N → Fin (K + 1) => G ∩ SyncAttemptForce.wordPiece p m n K r e) := by
    intro e e' hne
    rw [Function.onFun, Set.disjoint_left]
    exact fun _ h1 h2 =>
      Set.disjoint_left.mp (SyncAttemptForce.disjoint_wordPiece p m n K r hne) h1.2 h2.2
  have hmeas : ∀ e : Fin N → Fin (K + 1), MeasurableSet
      (G ∩ SyncAttemptForce.wordPiece p m n K r e) := fun e =>
    (enlMeas_le p m n _ hGmeas).inter (SyncAttemptForce.measurableSet_wordPiece p m n K r e)
  have hcover : (⋃ e : Fin N → Fin (K + 1),
        G ∩ SyncAttemptForce.wordPiece p m n K r e) =
      window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A) := by
    rw [window_landing p m n K r hprev]
    rw [SyncAttemptForce.syncWordSet_eq_iUnion, Set.inter_iUnion]
  have hmeasure : (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
        (landing (N := N) p m n K r A)) =
      ∑ e : (Fin N → Fin (K + 1)),
        (arrayMeasure N) (G ∩ SyncAttemptForce.wordPiece p m n K r e) := by
    rw [← hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  calc ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (arrayMeasure N) (window (N := N) p m n A)
      = ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) * (arrayMeasure N) G := by rw [hG]
    _ ≤ ∑ e : (Fin N → Fin (K + 1)),
          (arrayMeasure N) (G ∩ SyncAttemptForce.wordPiece p m n K r e) := hforce
    _ = (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
          (landing (N := N) p m n K r A)) := hmeasure.symm

/-- **Iterability of an epoch.**  The landing window is *inside* the epoch's own
window; before the new horizon no walker exceeds `r+1`; and at the new horizon every
walker sits exactly at `r+1`, i.e. in the even-defect sector at level `r+1` with
defect zero.  Hence the next epoch may be run at `K = 0`, for the price `(1-p)^N`. -/
theorem epoch_iterable (p : ℝ) (m n K r : ℕ) {A : Set (Pref N n)}
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) :
    window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A) ⊆
        window (N := N) p m n A ∧
      (∀ U ∈ window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A),
        ∀ j, j < n + (2 * K + 1) → ∀ i, (trajectory p m U j).pos i ≤ ((r + 1 : ℕ) : ℤ)) ∧
      (∀ U ∈ window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A),
        ∃ e : Fin N → Fin (0 + 1), ∀ i,
          (trajectory p m U (n + (2 * K + 1))).pos i =
            ((r + 1 : ℕ) : ℤ) - 2 * ((e i : ℕ) : ℤ)) := by
  classical
  have hland := window_landing p m n K r hprev
  have hup : (r : ℤ) ≤ ((r + 1 : ℕ) : ℤ) := by push_cast; omega
  refine ⟨hland ▸ Set.inter_subset_left, ?_, ?_⟩
  · intro U hU j hj i
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
    have hpast : pastProj p m (n + (2 * K + 1)) U ∈
        SyncAttemptForce.syncPast p m n K r e := he.1
    exact le_trans (SyncAttemptForce.syncPast_prev hpast j hj i) hup
  · intro U hU
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
    have hpiece : U ∈ SyncAttemptForce.wordPiece p m n K r e :=
      SyncAttemptForce.syncPast_subset_wordPiece (e := e) he.1
    have hlanding := SyncAttemptForce.wordPiece_landing p m n K r e hpiece
    refine ⟨fun _ => 0, fun i => ?_⟩
    have h := hlanding.2 i
    have hcast : ((r + 1 : ℕ) : ℤ) - 2 * ((((0 : Fin (0 + 1)) : ℕ)) : ℤ) = (r : ℤ) + 1 := by
      norm_num
    rw [hcast]
    exact h

/-! ## 3. The epoch tower -/

/-- **The `j`-fold epoch tower.**  Starting from the first landing window at level
`r+1` (all walkers exactly at `r+1`), `j` further epochs at `K = 0` advance the level
to `r+1+j`, at the price `((1-p)^N)^j`, and produce one single window at that level,
contained in the first landing window, on which every walker is exactly at `r+1+j`
at the new horizon and never above `r+1+j` before it. -/
theorem epoch_tower (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m n K r : ℕ)
    {A : Set (Pref N n)}
    (hsec : ∀ U ∈ window (N := N) p m n A, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) (j : ℕ) :
    ∃ A' : Set (Pref N (n + (2 * K + 1) + j)),
      (ENNReal.ofReal (1 - p) ^ N) ^ j *
          (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
            (landing (N := N) p m n K r A)) ≤
        (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A') ∧
      window (N := N) p m (n + (2 * K + 1) + j) A' ⊆
          window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A) ∧
      (∀ U ∈ window (N := N) p m (n + (2 * K + 1) + j) A', ∀ t,
        t < n + (2 * K + 1) + j → ∀ i,
          (trajectory p m U t).pos i ≤ ((r + 1 + j : ℕ) : ℤ)) ∧
      (∀ U ∈ window (N := N) p m (n + (2 * K + 1) + j) A',
        ∃ e : Fin N → Fin (0 + 1), ∀ i,
          (trajectory p m U (n + (2 * K + 1) + j)).pos i =
            ((r + 1 + j : ℕ) : ℤ) - 2 * ((e i : ℕ) : ℤ)) := by
  classical
  induction j with
  | zero =>
      exact ⟨landing (N := N) p m n K r A, by simp,
        subset_rfl, (epoch_iterable p m n K r hprev).2.1,
        (epoch_iterable p m n K r hprev).2.2⟩
  | succ j ih =>
      obtain ⟨A', hμ, hsub, hprev', hsec'⟩ := ih
      have hstep := epoch_force p hp0 hp1 m (n + (2 * K + 1) + j) 0 (r + 1 + j)
        (A := A') hsec' hprev'
      have hit := epoch_iterable p m (n + (2 * K + 1) + j) 0 (r + 1 + j) (A := A') hprev'
      refine ⟨landing (N := N) p m (n + (2 * K + 1) + j) 0 (r + 1 + j) A', ?_,
        Set.Subset.trans hit.1 hsub, hit.2.1, hit.2.2⟩
      have hstep' : ENNReal.ofReal (1 - p) ^ N *
            (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A') ≤
          (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j + (2 * 0 + 1))
            (landing (N := N) p m (n + (2 * K + 1) + j) 0 (r + 1 + j) A')) := by
        simpa using hstep
      calc (ENNReal.ofReal (1 - p) ^ N) ^ (j + 1) *
            (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
              (landing (N := N) p m n K r A))
          = ENNReal.ofReal (1 - p) ^ N *
              ((ENNReal.ofReal (1 - p) ^ N) ^ j *
                (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1))
                  (landing (N := N) p m n K r A))) := by
            rw [pow_succ', mul_assoc]
        _ ≤ ENNReal.ofReal (1 - p) ^ N *
              (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A') :=
            mul_le_mul' le_rfl hμ
        _ ≤ (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j + (2 * 0 + 1))
              (landing (N := N) p m (n + (2 * K + 1) + j) 0 (r + 1 + j) A')) := hstep'

/-- **The finite-index strict-attempt estimate.**  For `1/2 < p < 1`, `2 ≤ m`,
`2 ≤ N`, every level `r`, defect bound `K`, horizon `n` and offset `j`, and every
position-prefix window at time `n` in the even-defect sector `≤ 2K` below `r` with no
walker above `r` before `n`,

  `q_K * ((1-p)^N)^(j+1) * P(V) * μ G
     ≤ μ (G ∩ {StrictAttempt (r+1+j)})`,  `q_K = ofReal (1-p)^((2K+1)N)`,

i.e. one and the same past window forces the canonical strict attempt of index
`r+1+j` (its record level is `r+2+j`) on the actual array, with the seed factor `P(V)`
paid exactly once (it cannot be paid earlier: `strictPos` forbids every later landing
above the level at which it is paid).  The level index is exact: the tower lands at
level `r+1+j`, and one further `(1-p)^N` epoch produces the strict future. -/
theorem tower_force {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (n K r : ℕ) {A : Set (Pref N n)}
    (hsec : ∀ U ∈ window (N := N) p m n A, ∃ e : Fin N → Fin (K + 1), ∀ i,
      (trajectory p m U n).pos i = (r : ℤ) - 2 * ((e i : ℕ) : ℤ))
    (hprev : ∀ U ∈ window (N := N) p m n A, ∀ j, j < n → ∀ i,
      (trajectory p m U j).pos i ≤ (r : ℤ)) (j : ℕ) :
    ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) *
        (ENNReal.ofReal (1 - p) ^ N) ^ (j + 1) *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} *
        (arrayMeasure N) (window (N := N) p m n A) ≤
      (arrayMeasure N) (window (N := N) p m n A ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) := by
  classical
  have hp_le : ENNReal.ofReal (1 - p) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set qK : ℝ≥0∞ := ENNReal.ofReal (1 - p) ^ ((2 * K + 1) * N) with hqK
  set a : ℝ≥0∞ := ENNReal.ofReal (1 - p) ^ N with ha
  set P : ℝ≥0∞ := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} with hP
  obtain ⟨A', hμ, hsub, hprev', hsec'⟩ :=
    epoch_tower (N := N) p (le_of_lt hp0) hp1 m n K r hsec hprev j
  have hfirst := epoch_force (N := N) p (le_of_lt hp0) hp1 m n K r hsec hprev
  rw [← hqK] at hfirst
  rw [← ha] at hμ
  have hlast := SyncAttemptForce.strictAttempt_mass_ge_prefix (N := N) p hp0 hp1 hm hN
    (n + (2 * K + 1) + j) 0 (r + 1 + j) (A₀ := A') hsec' hprev'
  rw [← hP] at hlast
  have hlast' : a * P * (arrayMeasure N)
        (window (N := N) p m (n + (2 * K + 1) + j) A') ≤
      (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A' ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) := by
    simpa [← ha, window] using hlast
  have hG₁sub : window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A) ⊆
      window (N := N) p m n A := by
    rw [window_landing p m n K r hprev]
    exact Set.inter_subset_left
  have hmono : (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A' ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) ≤
      (arrayMeasure N) (window (N := N) p m n A ∩
        {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) := by
    refine measure_mono ?_
    rintro U ⟨h1, h2⟩
    exact ⟨hG₁sub (hsub h1), h2⟩
  have heq : qK * a ^ (j + 1) * P * (arrayMeasure N) (window (N := N) p m n A) =
      (a * P) * (a ^ j * (qK * (arrayMeasure N) (window (N := N) p m n A))) := by
    rw [pow_succ']; ring
  calc qK * a ^ (j + 1) * P * (arrayMeasure N) (window (N := N) p m n A)
      = (a * P) * (a ^ j * (qK * (arrayMeasure N) (window (N := N) p m n A))) := heq
    _ ≤ (a * P) * (a ^ j * (arrayMeasure N)
          (window (N := N) p m (n + (2 * K + 1)) (landing (N := N) p m n K r A))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hfirst)
    _ ≤ (a * P) * (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A') :=
        mul_le_mul' le_rfl hμ
    _ ≤ (arrayMeasure N) (window (N := N) p m (n + (2 * K + 1) + j) A' ∩
          {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) := hlast'
    _ ≤ (arrayMeasure N) (window (N := N) p m n A ∩
          {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (r + 1 + j)}) := hmono

/-- **Non-vacuity: the initial window forces strict attempts at every level.**
At time `0` every walker stands at the origin, so the sector and no-prior-above
hypotheses hold with `n = 0`, `K = 0`, `r = 0` on the whole space.  The tower then
gives a strictly positive lower bound for the canonical strict attempt of every index
`1+j`, `j ≥ 0` (record levels `≥ 2`; index `0` is already covered by
`SyncAttemptForce.firstAttempt_mass_ge`):

  `(1-p)^(N(j+2)) * P(V) ≤ μ {StrictAttempt (1+j)}`.

The bound decays geometrically in `j`; it is not uniform in the level, and this file
proves nothing about the sum over `j` or about `D = ⊤`. -/
theorem tower_force_initial {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (j : ℕ) :
    ENNReal.ofReal (1 - p) ^ N * (ENNReal.ofReal (1 - p) ^ N) ^ (j + 1) *
        (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos} ≤
      (arrayMeasure N) {U : Array N | RawStrictAttemptTower.StrictAttempt p m U (1 + j)} := by
  have h := tower_force (N := N) hp0 hp1 hm hN 0 0 0 (A := Set.univ) ?_ ?_ j
  · simpa [window] using h
  · intro U _
    exact ⟨fun _ => 0, fun i => by simp⟩
  · intro U _ j' hj'
    omega

end Swarm.StrictEpoch
