/-
# The stopped next-record map of the capped-step record chain

This file isolates the *state-only* stopping rule of the record chain of
`main_1d_revised.tex` §3.1 ("we stop when the maximum position first reaches `1`"),
identifies it with the existing history-dependent `SimJump.Record.FirstRecord` predicate
(`Swarm/RecordStop.lean`), and produces the compact record state `RecState N m`
(`Swarm/RecordState.lean`) at the stopping time via
`SimJump.Record.toRecState` (`Swarm/Bridge.lean`).

Main results:

* `pos_nonpos_of_no_rec` : before the first time some walker sits at `1`, every walker is
  at `≤ 0`.  Hence the state-only stopping rule agrees with `FirstRecord`.
* `firstRecord_of_isRec` : the two notions of "first record time" coincide.
* `out_mem_srSet` : if the finite path `q` is a simultaneous-record path (`HitsFAt`, i.e. the
  paper's set `F`), the resulting compact record state lies in `SwarmRec.srSet`.

No measure theory and no probability kernel is asserted in this file; it is the deterministic
part of the stopped record law and is used by `StoppedKernel.lean`.
-/
import Swarm.Bridge
import Swarm.Force
import Swarm.KrylovBogoliubov

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SimJump.RecKernel

variable {N m : ℕ}

/-! ### The state-only record predicate -/

/-- Some walker sits exactly at the new record level `1`. -/
def IsRec (s : State N m) : Prop := ∃ i, s.pos i = 1

lemma isRec_iff (s : State N m) : IsRec s ↔ ∃ i, s.pos i = 1 := Iff.rfl

/-- **Before the first record time no walker is positive.**  Positions move by `±1` and start
at `≤ 0`, so a walker can only become positive by sitting at `1` first. -/
theorem pos_nonpos_of_no_rec {u : ℕ → JumpVec N} {s : State N m} (hs : ∀ i, s.pos i ≤ 0) :
    ∀ (t : ℕ), (∀ n ≤ t, ¬ IsRec (evolveFun (m := m) u n s)) →
      ∀ i, (evolveFun (m := m) u t s).pos i ≤ 0 := by
  intro t
  induction t with
  | zero =>
      intro _ i
      simpa [evolveFun, evolve] using hs i
  | succ t ih =>
      intro ht i
      have hprev : (evolveFun (m := m) u t s).pos i ≤ 0 :=
        ih (fun n hn => ht n (Nat.le_trans hn (Nat.le_succ t))) i
      have hstep : (evolveFun (m := m) u (t + 1) s).pos i =
          (evolveFun (m := m) u t s).pos i + (if u t i = true then (1 : ℤ) else -1) := by
        rw [evolveFun_succ, step_pos, stepPos]
      have hstep' : (evolveFun (m := m) u (t + 1) s).pos i =
          (evolveFun (m := m) u t s).pos i + (if u t i = true then (1 : ℤ) else -1) := hstep
      by_contra hpos
      push Not at hpos
      rw [hstep'] at hpos
      have hle : (evolveFun (m := m) u t s).pos i +
          (if u t i = true then (1 : ℤ) else -1) ≤ 1 := by
        split_ifs <;> omega
      have hone : (evolveFun (m := m) u (t + 1) s).pos i = 1 := by
        rw [hstep']; omega
      exact ht (t + 1) (le_refl (t + 1)) ⟨i, hone⟩

/-- The state-only stopping rule produces a genuine `FirstRecord` path. -/
theorem firstRecord_of_isRec {u : ℕ → JumpVec N} {s : State N m} {k : ℕ}
    (hs : ∀ i, s.pos i ≤ 0)
    (h : IsRec (evolveFun (m := m) u k s) ∧
      ∀ n < k, ¬ IsRec (evolveFun (m := m) u n s)) :
    Record.FirstRecord u k s :=
  ⟨h.1, fun t ht i =>
    pos_nonpos_of_no_rec hs t (fun n hn => h.2 n (lt_of_le_of_lt hn ht)) i⟩

/-- **The two stopping rules agree.**  If every walker starts at `≤ 0` and `k` is the first
time at which some walker sits at `1`, then `k` is a first-record time in the sense of
`Swarm/RecordStop.lean`. -/
theorem firstRecord_iff_isRec {u : ℕ → JumpVec N} {s : State N m} (hs : ∀ i, s.pos i ≤ 0)
    {k : ℕ} :
    Record.FirstRecord u k s ↔
      IsRec (evolveFun (m := m) u k s) ∧
        ∀ n < k, ¬ IsRec (evolveFun (m := m) u n s) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun n hn hcontra => ?_⟩
    obtain ⟨i, hi⟩ := hcontra
    have := h2 n hn i
    omega
  · exact firstRecord_of_isRec hs

/-! ### The local-time cap is nondegenerate at a record state -/

/-- The paper's truncation level satisfies `m ≥ 1` at every record state: the current site of
walker `i` carries capped local time at least `1`, and capped local times are at most `m`. -/
lemma one_le_of_recordStart {s : State N m} (hs : Record.RecordStart s) : 1 ≤ m := by
  obtain ⟨i, _⟩ := hs.exists_zero
  have h1 : 1 ≤ s.eta i (s.pos i) := hs.eta_pos i
  have h2 : s.eta i (s.pos i) ≤ m := s.hcap i (s.pos i)
  omega

/-- The truncation level hypothesis is intrinsic to the paper's setting (`m ≥ 2` there); it is
needed because the record-state constraint `η_i(-d_i) ≥ 1` is vacuous at `m = 0`. -/
lemma one_le_of_ne_zero (hm : m ≠ 0) : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm

/-! ### The compact record state at the stopping time -/

/-- The compact record state produced by the finite path `q` at a first-record time `k`,
shown at the existing `Record.toRecState` construction. -/
noncomputable def recState (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) (hm : 1 ≤ m)
    (h : Record.FirstRecord u k s) (hs : Record.RecordStart s) : SwarmRec.RecState N m :=
  Record.toRecState u k s hm h hs

lemma recState_val (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) (hm : 1 ≤ m)
    (h : Record.FirstRecord u k s) (hs : Record.RecordStart s) :
    (recState u k s hm h hs).val = Record.toRecordAmb (evolveFun (m := m) u k s) := rfl

end SimJump.RecKernel


namespace SimJump.RecKernel

open SwarmRec

/-! ### The stopped record map with a junk value on non-record paths -/

/-- The compact record state reached from `y` along the finite path `q` at time `k`, provided
`q` is a first-record path for the continuation `Record.extendPath q`; the junk value `y` is
used otherwise.  The junk branch carries zero weight in `hitK` below, so it never contributes
mass; it only makes the map total. -/
noncomputable def out (hm : 1 ≤ m) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m) :
    RecState N m := by
  classical
  exact if h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y) then
    recState (Record.extendPath q) k (Record.ofRecState y) hm h
      (Record.ofRecState_recordStart y hm)
  else y

lemma out_of_firstRecord (hm : 1 ≤ m) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m)
    (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    out hm q y = recState (Record.extendPath q) k (Record.ofRecState y) hm h
      (Record.ofRecState_recordStart y hm) := by
  classical
  rw [out]
  exact dif_pos h

lemma out_of_not_firstRecord (hm : 1 ≤ m) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m)
    (h : ¬ Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    out hm q y = y := by
  classical
  rw [out]
  exact dif_neg h

/-- **A simultaneous-record path lands in the paper's set `F`.**  If `q` is a path on which
every walker reaches `1` at time `k` for the first time, the stopped record state is the
simultaneous record state `d_i = 0` for all `i`, i.e. an element of `srSet`. -/
theorem out_mem_srSet (hm : 1 ≤ m) (hN : 0 < N) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m) (hq : HitsFAt q (Record.ofRecState y)) :
    out hm q y ∈ srSet N m := by
  rw [out_of_firstRecord hm q y (Record.firstRecord_extendPath hN q (Record.ofRecState y) hq)]
  exact Record.toRecState_mem_srSet_of_hits hN q y hm hq

end SimJump.RecKernel


