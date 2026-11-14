/-This file closes the geometric input that `M6Aggr.joint_law_of_block_stat` and
`M6Aggr.path_law_of_block_stat` take as hypotheses (`hdisj`, `hcover`, `hS`), at the actual
array from the Dirac start law, for **every** block count `r`.

The one substantive repair: the `r`-block box of a tuple `w` is
`jbox p m (totLen r w) (concatF r w)`, and for `r ≥ 2` these boxes are *not* pairwise disjoint —
a tuple and its one-block extension have nested boxes, so the `hdisj` field of
`M6Aggr.joint_law_of_block_stat` is false as stated at `r ≥ 2` (see `jbox_eq_of_prefix`,
`not_pairwise_disjoint_boxes`).  The correct disjoint family is the same box intersected with
the level-`r` record-time event:

  `rbox w = jbox p m (totLen r w) (concatF r w) ∩ {U | recTimeA p m U r = totLen r w}`.

Because `recTimeA p m U r = 0` off `ReachAll p m` and `r ≤ recTimeA p m U r` on it, this
intersection is *contained* in `ReachAll` and therefore needs no off-`ReachAll` totalisation of
the record state.  On it the whole record decomposition is determined by the finite prefix.

Main declarations (namespace `M7Block`):

* `preLen`, `preLen_eq_totLen`, `JumpAgree`;
* `evolveFun_ofRecState_eq_trans_capState` — along a prescribed jump window the capped chain
  state from the actual compact record state is the level-translated actual capped state;
* `blockLen_eq_of_nat_find`, `runMax_shiftX_eq`, `blockLen_eq_of_firstRecord` — the actual block
  length *is* the prescribed block's length;
* `detAux` / `box_det` — **determination**: on a first-record chain box intersected with the
  level-`r` record-time event, the actual record times and compact record states are the
  cumulative lengths and the nested `out` chain of the prescribed tuple;
* `rbox_disjoint`, `rbox_covered`, `rbox_stat`, `rbox_ae_eq_jbox` — the repaired geometric
  hypotheses, all theorems;
* `actual_block_law` — the unconditional law of `(actRecState r, recTimeA r)` at the actual array
  equals the `r`-fold iterate of the lifted stopped-record kernel from `(zeroState, 0)`;
* `actual_blockPath_law` — the same for the whole `Fin (r+1)`-path of partial endpoints.

Nothing here proves or refutes `Swarm.Ballistic`, `RegenAvailable`, `MainClaim`, `(diam)`,
`Bridge.JointLawIdentity` (the *infinite* record sequence on the stopped-path space), or the
existence of a common speed.
-/
import Swarm.BlockAggregate
import Swarm.ActualRecordGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M7Block

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec M5FirstBlock M6Aggr
open SwarmRecordMeas SwarmRecordMeas.Actual RecordDefect

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### Prefix lengths of a tuple of blocks -/

/-- The total number of jumps in the first `i` blocks of a tuple (`0` if `i > r`). -/
noncomputable def preLen {N : ℕ} : (r : ℕ) → (Fin r → Word N) → ℕ → ℕ
  | 0, _, _ => 0
  | r + 1, w, 0 => 0
  | r + 1, w, (i + 1) => (w 0).1 + preLen r (fun j => w j.succ) i

@[simp] theorem preLen_zero_right (r : ℕ) (w : Fin r → Word N) : preLen r w 0 = 0 := by
  cases r <;> rfl

@[simp] theorem preLen_succ (r : ℕ) (w : Fin (r + 1) → Word N) (i : ℕ) :
    preLen (r + 1) w (i + 1) = (w 0).1 + preLen r (fun j => w j.succ) i := rfl

/-- At the full length the prefix length is the total length. -/
theorem preLen_eq_totLen : ∀ (r : ℕ) (w : Fin r → Word N), preLen r w r = totLen r w
  | 0, _ => rfl
  | r + 1, w => by
      rw [preLen_succ, preLen_eq_totLen r (fun j => w j.succ)]
      rfl

/-- The nested stopped-record chain of a tuple at level `i` (`i = 0` gives the start state).  This
is `runOutF` with the level index in `ℕ`, so that the intermediate states of a tuple can be
addressed without re-typing the tuple to a shorter length. -/
noncomputable def recStateF {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) :
    (r : ℕ) → (Fin r → Word N) → ℕ → RecState N m
  | 0, _, _ => y
  | _ + 1, _, 0 => y
  | r + 1, w, (i + 1) =>
      recStateF hm (SimJump.RecKernel.out hm (w 0).2 y) r (fun j => w j.succ) i

@[simp] theorem recStateF_zero (hm : 1 ≤ m) (y : RecState N m) (r : ℕ) (w : Fin r → Word N) :
    recStateF hm y r w 0 = y := by
  cases r <;> rfl

@[simp] theorem recStateF_succ {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (w : Fin (r + 1) → Word N) (i : ℕ) :
    recStateF hm y (r + 1) w (i + 1)
      = recStateF hm (SimJump.RecKernel.out hm (w 0).2 y) r (fun j => w j.succ) i := rfl

/-- At the full length the nested chain is `runOutF`. -/
theorem recStateF_self {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (w : Fin r → Word N), recStateF hm y r w r = runOutF hm y r w
  | 0, y, _ => rfl
  | r + 1, y, w => by
      rw [recStateF_succ, recStateF_self hm r, runOutF_succ]

/-- The actual array's jumps agree with the prescribed sequence `u` on the window
`[τ, τ + L)`. -/
def JumpAgree (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (τ : ℕ) (u : ℕ → JumpVec N)
    (L : ℕ) : Prop :=
  ∀ t, t < L → ∀ i : Fin N, nextJumpVec p m U (τ + t) i = u t i

/-! ### The capped chain state along a prescribed window -/

/-- **Along a prescribed jump window, the record chain started at the actual compact record state
is the level-translated actual capped state.**  This is the identity that makes the *actual*
record decomposition computable from a finite jump prefix: positions are the actual positions
shifted down by the current level, local times are the actual local times shifted by the current
level. -/
theorem evolveFun_ofRecState_eq_trans_capState {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (j : ℕ) (y : RecState N m)
    (hy : y = M4RecordGeom.actRecState p m U hm hU j) (q : ℕ → JumpVec N) {L : ℕ}
    (hagree : JumpAgree p m U (recTimeA p m U j) q L) :
    ∀ t, t ≤ L → SimJump.evolveFun q t (SimJump.Record.ofRecState y)
      = M4RecordGeom.trans j
          (M5FirstBlock.capState m (trajectory p m U (recTimeA p m U j + t))) := by
  intro t ht
  subst hy
  rw [M4RecordGeom.ofRecState_actRecState hm hU j]
  show SimJump.evolveFun q t (M4RecordGeom.transRecordState p m U j) = _
  rw [M4RecordGeom.transRecordState, M4RecordGeom.evolveFun_trans]
  congr 1
  have hkey : SimJump.evolveFun q t
      (M5FirstBlock.capState m (trajectory p m U (recTimeA p m U j)))
      = M5FirstBlock.capState m (trajectory p m U (recTimeA p m U j + t)) := by
    rw [← M4RecordGeom.currentRecordState_eq_capState p m U (recTimeA p m U j),
      M5FirstBlock.evolveFun_congr
        (fun s hs => by funext i; exact (hagree s (lt_of_lt_of_le hs ht) i).symm),
      M4RecordGeom.evolveFun_currentRecordState p m U (recTimeA p m U j) t,
      M4RecordGeom.currentRecordState_eq_capState]
  exact hkey

/-- The position form of the previous identity: the actual position is the chain position plus
the current level. -/
theorem actX_eq_evolveFun_add {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (j : ℕ) (y : RecState N m)
    (hy : y = M4RecordGeom.actRecState p m U hm hU j) (q : ℕ → JumpVec N) {L : ℕ}
    (hagree : JumpAgree p m U (recTimeA p m U j) q L) :
    ∀ t, t ≤ L → ∀ i : Fin N,
      actX p m U i (recTimeA p m U j + t)
        = (SimJump.evolveFun q t (SimJump.Record.ofRecState y)).pos i + (j : ℤ) := by
  intro t ht i
  have h := congrArg (fun s : SimJump.State N m => s.pos i)
    (evolveFun_ofRecState_eq_trans_capState hm hU j y hy q hagree t ht)
  simp only [M4RecordGeom.trans_pos] at h
  have h2 : (M5FirstBlock.capState m (trajectory p m U (recTimeA p m U j + t))).pos i
      = (trajectory p m U (recTimeA p m U j + t)).pos i :=
    congrFun (M5FirstBlock.capState_pos m (trajectory p m U (recTimeA p m U j + t))) i
  show (trajectory p m U (recTimeA p m U j + t)).pos i = _
  linarith

/-- The shifted running maximum of the actual array at block `j` equals the running maximum of the
prescribed chain state. -/
theorem runMax_shiftX_eq {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (j : ℕ) (y : RecState N m)
    (hy : y = M4RecordGeom.actRecState p m U hm hU j) (q : ℕ → JumpVec N) {L : ℕ}
    (hagree : JumpAgree p m U (recTimeA p m U j) q L) {t : ℕ} (ht : t ≤ L) :
    runMax (M4RecordGeom.shiftX p m U j) t
      = runMax (fun i _ => (SimJump.evolveFun q t (SimJump.Record.ofRecState y)).pos i) 0 := by
  have hfun : (fun i : Fin N => M4RecordGeom.shiftX p m U j i t)
      = fun i => (SimJump.evolveFun q t (SimJump.Record.ofRecState y)).pos i := by
    funext i
    simp only [M4RecordGeom.shiftX]
    have h := actX_eq_evolveFun_add hm hU j y hy q hagree t ht i
    linarith
  rw [RecordDefect.runMax, RecordDefect.runMax, hfun]

/-! ### The actual block length is the prescribed block's length -/

/-- **`Nat.find` form of the block length**: if `k` satisfies the level-`1` hit of the shifted
actual maximum and no smaller time does, then the actual block length is `k`. -/
theorem blockLen_eq_of_nat_find {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hU : U ∈ ReachAll p m) (j k : ℕ)
    (hspec : runMax (M4RecordGeom.shiftX p m U j) k = 1)
    (hmin : ∀ n, n < k → runMax (M4RecordGeom.shiftX p m U j) n ≠ 1) :
    M4RecordGeom.blockLen p m U j = k := by
  rw [M4RecordGeom.blockLen_eq_find hU j, Nat.find_eq_iff]
  exact ⟨hspec, hmin⟩

/-- **The actual block length equals the length of a prescribed first-record block** whose jumps
the actual array follows on the block window. -/
theorem blockLen_eq_of_firstRecord {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (j : ℕ) (y : RecState N m)
    (hy : y = M4RecordGeom.actRecState p m U hm hU j)
    {k : ℕ} {q : ℕ → JumpVec N}
    (hFR : Record.FirstRecord q k (Record.ofRecState y))
    (hagree : JumpAgree p m U (recTimeA p m U j) q k) :
    M4RecordGeom.blockLen p m U j = k := by
  have heven : ∀ i : Fin N, Even ((Record.ofRecState y).pos i) := by
    intro i
    exact ⟨-((y.val.1 i : ℤ)), by simp only [Record.ofRecState]; ring⟩
  refine blockLen_eq_of_nat_find hU j k ?_ ?_
  · rw [runMax_shiftX_eq hm hU j y hy q hagree le_rfl]
    refine le_antisymm ?_ ?_
    · rw [RecordDefect.runMax, Finset.sup'_le_iff]
      intro i _
      have h := Record.firstRecord_pos_le_one q k (Record.ofRecState y) heven hFR i
      simpa using h
    · obtain ⟨i, hi⟩ := hFR.1
      rw [RecordDefect.runMax]
      have h := Finset.le_sup' (f := fun i => (SimJump.evolveFun q k (Record.ofRecState y)).pos i)
        (Finset.mem_univ i)
      rw [hi] at h
      exact h
  · intro n hn
    rw [runMax_shiftX_eq hm hU j y hy q hagree (le_of_lt hn), RecordDefect.runMax]
    have hle : Finset.univ.sup' Finset.univ_nonempty
        (fun i => (SimJump.evolveFun q n (Record.ofRecState y)).pos i) ≤ 0 := by
      rw [Finset.sup'_le_iff]
      intro i _
      exact hFR.2 n hn i
    omega


/-- Restricting a jump sequence to its first `k` entries preserves the first-record property. -/
theorem firstRecord_extJump_restrict {m : ℕ} {s : SimJump.State N m} {k : ℕ}
    {q : ℕ → JumpVec N} (h : Record.FirstRecord q k s) :
    Record.FirstRecord (extJump k (fun t : Fin k => q t)) k s := by
  refine (M5FirstBlock.FirstRecord_congr (u := q)
    (u' := extJump k (fun t : Fin k => q t)) (fun t ht => ?_)).mp h
  exact (extJump_apply (fun t : Fin k => q t) ht).symm

/-! ### The successor compact record state from a prescribed block -/

/-- **The compact record state one block later is the stopped-record output of the prescribed
block**, provided the actual array follows that block's jumps on the block window. -/
theorem actRecState_succ_of_word {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (j : ℕ) (y : RecState N m)
    (hy : y = M4RecordGeom.actRecState p m U hm hU j) {k : ℕ} {q : ℕ → JumpVec N}
    (hFR : Record.FirstRecord q k (Record.ofRecState y))
    (hagree : JumpAgree p m U (recTimeA p m U j) q k) :
    M4RecordGeom.actRecState p m U hm hU (j + 1)
      = SimJump.RecKernel.out hm (fun t : Fin k => q t) y := by
  have hbl := blockLen_eq_of_firstRecord hm hU j y hy hFR hagree
  have hτ : recTimeA p m U (j + 1) = recTimeA p m U j + k := by
    rw [← M4RecordGeom.recTimeA_add_blockLen hU j, hbl]
  have hFR' : Record.FirstRecord (Record.extendPath (fun t : Fin k => q t)) k
      (Record.ofRecState y) := by
    rw [← extJump_eq_extendPath]
    exact firstRecord_extJump_restrict hFR
  have hagree' : JumpAgree p m U (recTimeA p m U j) (extJump k (fun t : Fin k => q t)) k :=
    fun t ht i => by
      rw [extJump_apply (fun t : Fin k => q t) ht]
      exact hagree t ht i
  refine M4RecordGeom.ofRecState_injective ?_
  rw [M4RecordGeom.ofRecState_actRecState hm hU (j + 1)]
  simp only [M4RecordGeom.transRecordState]
  rw [hτ, M5FirstBlock.ofRecState_out hm (fun t : Fin k => q t) y hFR',
    ← extJump_eq_extendPath]
  rw [← M4RecordGeom.trans_one_eq_normalize,
    evolveFun_ofRecState_eq_trans_capState hm hU j y hy _ hagree' k le_rfl,
    M4RecordGeom.trans_add, Nat.add_comm 1 j]


/-- **Determination along an actual run.**  If the actual array sits at its own level-`j` compact
record state `y` at its level-`j` record time, and its next `totLen r w` jumps are the
concatenation of a first-record chain `w` from `y`, then the following `r` record times are the
cumulative lengths of `w` and the following compact record states are the nested `out` chain. -/
theorem detAux (hm : 1 ≤ m) (p : ℝ) :
    ∀ (r : ℕ) (U : Swarming.Uniform.Array N) (hU : U ∈ ReachAll p m)
      (j : ℕ) (y : RecState N m), y = M4RecordGeom.actRecState p m U hm hU j →
      ∀ (w : Fin r → Word N), FRChainF hm y r w →
      JumpAgree p m U (recTimeA p m U j) (extJump (totLen r w) (concatF r w)) (totLen r w) →
      ∀ i, i ≤ r →
        recTimeA p m U (j + i) = recTimeA p m U j + preLen r w i ∧
        M4RecordGeom.actRecState p m U hm hU (j + i) = recStateF hm y r w i := by
  intro r
  induction r with
  | zero =>
      intro U hU j y hy w _ _ i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      refine ⟨by simp, ?_⟩
      rw [Nat.add_zero]
      exact hy.symm
  | succ r ih =>
      intro U hU j y hy w hFR hagree i hi
      obtain ⟨hFRhead, hFRtail⟩ := (frChainF_succ hm y r w).mp hFR
      have hlen : totLen (r + 1) w = (w 0).1 + totLen r (fun i => w i.succ) := rfl
      have hhead : JumpAgree p m U (recTimeA p m U j) (extJump (w 0).1 (w 0).2) (w 0).1 := by
        intro t ht i'
        rw [← extJump_concatF_head r w ht]
        exact hagree t (by omega) i'
      have hFRhead' : Record.FirstRecord (extJump (w 0).1 (w 0).2) (w 0).1
          (Record.ofRecState y) := by
        rw [extJump_eq_extendPath]
        exact hFRhead
      have hbl : M4RecordGeom.blockLen p m U j = (w 0).1 :=
        blockLen_eq_of_firstRecord hm hU j y hy hFRhead' hhead
      have hτ1 : recTimeA p m U (j + 1) = recTimeA p m U j + (w 0).1 := by
        rw [← M4RecordGeom.recTimeA_add_blockLen hU j, hbl]
      have hstate : M4RecordGeom.actRecState p m U hm hU (j + 1)
          = SimJump.RecKernel.out hm (w 0).2 y := by
        have h := actRecState_succ_of_word hm hU j y hy hFRhead' hhead
        rw [show (fun t : Fin (w 0).1 => extJump (w 0).1 (w 0).2 t) = (w 0).2 from
          funext fun t => extJump_apply (w 0).2 t.2] at h
        exact h
      have htail : JumpAgree p m U (recTimeA p m U (j + 1))
          (extJump (totLen r (fun i => w i.succ)) (concatF r (fun i => w i.succ)))
          (totLen r (fun i => w i.succ)) := by
        intro t ht i'
        rw [hτ1, show recTimeA p m U j + (w 0).1 + t
          = recTimeA p m U j + (t + (w 0).1) from by omega,
          hagree (t + (w 0).1) (by omega) i']
        exact congrFun (congrFun (M6Aggr.extJump_concatF_shift r w) t) i'
      rcases i with _ | i
      · refine ⟨by simp, ?_⟩
        rw [Nat.add_zero]
        exact hy.symm
      · obtain ⟨ihτ, ihσ⟩ := ih U hU (j + 1) (SimJump.RecKernel.out hm (w 0).2 y)
          hstate.symm (fun i => w i.succ) hFRtail htail i (by omega)
        refine ⟨?_, ?_⟩
        · rw [preLen_succ, show (j : ℕ) + (i + 1) = j + 1 + i from by omega, ihτ, hτ1]
          omega
        · rw [show (j : ℕ) + (i + 1) = j + 1 + i from by omega, ihσ]
          rfl

/-- **The block box determines the actual record decomposition.**  On the first-record chain box
of a tuple `w`, the actual level-`i` record time is the cumulative length `preLen r w i` and the
actual compact record state is the nested `out` chain of `w`, for every `i ≤ r`. -/
theorem box_det {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) {r : ℕ} {w : Fin r → Word N}
    (hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w)
    (hbox : U ∈ jbox p m (totLen r w) (concatF r w)) :
    ∀ i, i ≤ r →
      recTimeA p m U i = preLen r w i ∧
      M4RecordGeom.actRecState p m U hm hU i
        = recStateF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w i := by
  intro i hi
  obtain ⟨h1, h2⟩ := detAux (N := N) hm p r U hU 0 (SwarmRecordMeas.StartLaw.zeroState hm)
    (M4RecordGeom.actRecState_zero hm hU).symm w hFR (by
      intro t ht i'
      rw [recTimeA_zero, Nat.zero_add, extJump_apply (concatF r w) ht]
      exact hbox ⟨t, ht⟩ i') i hi
  rw [Nat.zero_add] at h1
  rw [Nat.zero_add] at h2
  rw [recTimeA_zero, Nat.zero_add] at h1
  exact ⟨h1, h2⟩


/-! ### Positivity of the lengths of a first-record chain -/

/-- Off `ReachAll` the canonical record time is `0` (the `Nat.find` is totalised there). -/
theorem recTimeA_eq_zero_off {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (h : U ∉ ReachAll p m) (r : ℕ) : recTimeA p m U r = 0 := by
  rw [recTimeA, firstHit_eq]
  refine (Nat.find_eq_iff _).2 ⟨Or.inl h, ?_⟩
  intro n hn
  omega

/-- A first-record block from a compact record state has positive length. -/
theorem firstRecord_len_pos {m : ℕ} (hm : 1 ≤ m) {y : RecState N m} {k : ℕ}
    {q : ℕ → JumpVec N} (h : Record.FirstRecord q k (Record.ofRecState y)) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    obtain ⟨i, hi⟩ := h.1
    subst hk
    have hpos := (Record.ofRecState_recordStart y hm).nonpos i
    rw [show (SimJump.evolveFun q 0 (Record.ofRecState y)).pos i
      = (Record.ofRecState y).pos i from rfl] at hi
    omega
  · exact hk

/-- Every block of a first-record chain has positive length. -/
theorem frChain_len_pos {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (w : Fin r → Word N), FRChainF hm y r w →
      ∀ i : Fin r, 0 < (w i).1 := by
  intro r
  induction r with
  | zero => intro y w _ i; exact i.elim0
  | succ r ih =>
      intro y w hFR i
      obtain ⟨hhead, htail⟩ := (frChainF_succ hm y r w).mp hFR
      rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, hj⟩
      · subst h0
        exact firstRecord_len_pos hm (by rwa [← extJump_eq_extendPath] at hhead)
      · subst hj
        exact ih (SimJump.RecKernel.out hm (w 0).2 y) (fun j => w j.succ) htail j

/-- A nonempty first-record chain has positive total length. -/
theorem totLen_pos_of_frChain {m : ℕ} (hm : 1 ≤ m) {r : ℕ} {y : RecState N m}
    {w : Fin r → Word N} (hFR : FRChainF hm y r w) (hr : 0 < r) : 0 < totLen r w := by
  cases r with
  | zero => exact absurd hr (Nat.lt_irrefl 0)
  | succ r =>
      have h1 : 0 < (w 0).1 := frChain_len_pos hm (r + 1) y w hFR 0
      rw [totLen_succ]
      omega

/-! ### The repaired block family -/

/-- The actual jump word of block `i` of the array. -/
noncomputable def actWord (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : ℕ) : Word N :=
  ⟨M4RecordGeom.blockLen p m U i, M4RecordGeom.blockWord p m U i⟩

/-- **The repaired first-record block family.**  The `r`-block box of a tuple, intersected with the
event that the tuple's total length *is* the actual level-`r` record time.  Unlike the bare box,
this family is pairwise disjoint at every `r ≥ 1`, and each member is contained in `ReachAll`. -/
noncomputable def rbox (p : ℝ) (m : ℕ) (r : ℕ) (w : Fin r → Word N) : Set (Array N) :=
  jbox p m (totLen r w) (concatF r w) ∩ {U : Array N | recTimeA p m U r = totLen r w}

theorem rbox_subset_jbox {p : ℝ} {m : ℕ} {r : ℕ} {w : Fin r → Word N} :
    rbox p m r w ⊆ jbox p m (totLen r w) (concatF r w) := fun _ h => h.1

/-- A member of the repaired family lies in `ReachAll`. -/
theorem rbox_subset_reach {p : ℝ} {m : ℕ} {r : ℕ} {y : RecState N m} {w : Fin r → Word N}
    (hm : 1 ≤ m) (hFR : FRChainF hm y r w) (hr : 0 < r) : rbox p m r w ⊆ ReachAll p m := by
  intro U hU
  by_contra hcon
  have h0 := recTimeA_eq_zero_off hcon r
  have hpos := totLen_pos_of_frChain hm hFR hr
  have h2 : totLen r w = 0 := by rw [← hU.2, h0]
  omega


/-! ### Extracting blocks from a concatenation -/

/-- The first block of a concatenation, as a function value. -/
theorem concatF_head_apply {r : ℕ} {w : Fin (r + 1) → Word N} {t : ℕ} (ht : t < (w 0).1)
    {hL : t < totLen (r + 1) w} :
    concatF (r + 1) w ⟨t, hL⟩ = (w 0).2 ⟨t, ht⟩ := by
  rw [concatF_succ]
  simp only [catWord, dif_pos ht]

/-- The first block of a concatenation, in `extJump` form. -/
theorem extJump_concatF_head_apply {r : ℕ} (w : Fin (r + 1) → Word N) {t : ℕ}
    (ht : t < (w 0).1) :
    extJump (totLen (r + 1) w) (concatF (r + 1) w) t = (w 0).2 ⟨t, ht⟩ := by
  have hL : t < totLen (r + 1) w := by
    rw [totLen_succ]; omega
  rw [extJump_apply _ hL]
  exact concatF_head_apply ht

/-- **Injectivity of the tuple-to-word map on first-record chains.**  Two first-record chains with
the same block-boundary prefix lengths (equivalently the same record times on any array that
follows them) and the same concatenated jump sequence are equal. -/
theorem tuple_ext {m : ℕ} {y : RecState N m} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (w w' : Fin r → Word N),
      FRChainF hm y r w → FRChainF hm y r w' →
      (∀ i, i ≤ r → preLen r w i = preLen r w' i) →
      extJump (totLen r w) (concatF r w) = extJump (totLen r w') (concatF r w') →
      w = w'
  | 0, w, w', _, _, _, _ => by
      funext i
      exact i.elim0
  | r + 1, w, w', hFR, hFR', hpre, hword => by
      obtain ⟨hFRh, hFRt⟩ := (frChainF_succ hm y r w).mp hFR
      obtain ⟨hFRh', hFRt'⟩ := (frChainF_succ hm y r w').mp hFR'
      have hk : (w 0).1 = (w' 0).1 := by
        have h := hpre 1 (by omega)
        rw [preLen_succ, preLen_succ, preLen_zero_right, preLen_zero_right] at h
        simpa using h
      have hL : totLen (r + 1) w = totLen (r + 1) w' := by
        rw [← preLen_eq_totLen, ← preLen_eq_totLen]
        exact hpre (r + 1) le_rfl
      have hhead : w 0 = w' 0 := by
        refine Sigma.ext hk ?_
        rw [Fin.heq_fun_iff hk]
        intro t
        have ht' : (t : ℕ) < (w' 0).1 := by rw [← hk]; exact t.2
        calc (w 0).2 t
            = extJump (totLen (r + 1) w) (concatF (r + 1) w) (t : ℕ) := by
              rw [extJump_concatF_head_apply w t.2]
          _ = extJump (totLen (r + 1) w') (concatF (r + 1) w') (t : ℕ) := by rw [hword]
          _ = (w' 0).2 ⟨(t : ℕ), ht'⟩ := extJump_concatF_head_apply w' ht'
      have htail : extJump (totLen r (fun i => w i.succ)) (concatF r (fun i => w i.succ))
          = extJump (totLen r (fun i => w' i.succ)) (concatF r (fun i => w' i.succ)) := by
        rw [← M6Aggr.extJump_concatF_shift r w, ← M6Aggr.extJump_concatF_shift r w']
        rw [hhead, hword]
      have hpre' : ∀ i, i ≤ r → preLen r (fun j => w j.succ) i
          = preLen r (fun j => w' j.succ) i := by
        intro i hi
        have h := hpre (i + 1) (by omega)
        rw [preLen_succ, preLen_succ] at h
        omega
      rw [← hhead] at hFRt'
      have htail_eq : (fun i : Fin r => w i.succ) = (fun i : Fin r => w' i.succ) :=
        tuple_ext hm r (fun i : Fin r => w i.succ) (fun i : Fin r => w' i.succ) hFRt hFRt' hpre' htail
      funext i
      cases i using Fin.cases with
      | zero => exact hhead
      | succ j => exact congrFun htail_eq j

/-! ### The actual block words are the actual jumps -/

/-- The prefix length of the actual block words is the actual record time. -/
theorem preLen_actWord {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hU : U ∈ ReachAll p m) :
    ∀ (i r b : ℕ), i ≤ r →
      recTimeA p m U b + preLen r (fun j : Fin r => actWord p m U (b + j)) i
        = recTimeA p m U (b + i) := by
  intro i
  induction i with
  | zero => intro r b _; simp
  | succ i ih =>
      intro r b hi
      cases r with
      | zero => omega
      | succ r =>
          rw [preLen_succ]
          have hfun : (fun j : Fin r => (fun j : Fin (r + 1) => actWord p m U (b + j)) j.succ)
              = (fun j : Fin r => actWord p m U ((b + 1) + j)) := by
            funext j
            exact congrArg (actWord p m U) (by rw [Fin.val_succ]; omega)
          rw [hfun]
          have h0 : ((fun j : Fin (r + 1) => actWord p m U (b + j)) 0).1
              = M4RecordGeom.blockLen p m U b := rfl
          rw [h0]
          have h2 : recTimeA p m U b + M4RecordGeom.blockLen p m U b = recTimeA p m U (b + 1) :=
            M4RecordGeom.recTimeA_add_blockLen hU b
          have h3 := ih r (b + 1) (by omega)
          have hbi : b + 1 + i = b + (i + 1) := by rw [Nat.add_right_comm, Nat.add_assoc]
          rw [← Nat.add_assoc, h2, h3, hbi]

/-- **The block words of an actual record decomposition reproduce the actual jump sequence.** -/
theorem extJump_concatF_of_blockJumps {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} :
    ∀ (r b : ℕ) (w : Fin r → Word N),
      (∀ (i : Fin r) (t : Fin (w i).1),
        (w i).2 t = nextJumpVec p m U (b + preLen r w i + (t : ℕ))) →
      ∀ n, n < totLen r w →
        extJump (totLen r w) (concatF r w) n = nextJumpVec p m U (b + n) := by
  intro r
  induction r with
  | zero => intro b w _ n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ r ih =>
      intro b w hw n hn
      have hnL : n < (w 0).1 + totLen r (fun i => w i.succ) := hn
      rcases Nat.lt_or_ge n (w 0).1 with hlt | hge
      · rw [extJump_concatF_head_apply w hlt, hw 0 ⟨n, hlt⟩]
        have hidx : b + preLen (r + 1) w (0 : Fin (r + 1)) + ((⟨n, hlt⟩ : Fin (w 0).1) : ℕ)
            = b + n := by
          have h0 : ((0 : Fin (r + 1)) : ℕ) = 0 := rfl
          rw [h0, preLen_zero_right]
          simp
        rw [hidx]
      · obtain ⟨n', hn'⟩ : ∃ n', n = (w 0).1 + n' := ⟨n - (w 0).1, by omega⟩
        have hn'' : n' < totLen r (fun i => w i.succ) := by omega
        have hshift := congrFun (M6Aggr.extJump_concatF_shift r w) n'
        rw [hn', Nat.add_comm (w 0).1 n', hshift]
        have hw' : ∀ (i : Fin r) (t : Fin ((fun i => w i.succ) i).1),
            ((fun i => w i.succ) i).2 t
              = nextJumpVec p m U ((b + (w 0).1) + preLen r (fun i => w i.succ) i + (t : ℕ)) := by
          intro i t
          have h := hw i.succ t
          rw [show preLen (r + 1) w (↑(i.succ) : ℕ)
              = (w 0).1 + preLen r (fun i => w i.succ) (↑i) from preLen_succ r w ↑i] at h
          rw [h]
          congr 1
          omega
        rw [ih (b + (w 0).1) (fun i => w i.succ) hw' n' hn'',
          show (b + (w 0).1) + n' = b + (n' + (w 0).1) from by
            rw [Nat.add_right_comm, Nat.add_assoc]]

/-- The actual jump sequence is the concatenation of the actual block words. -/
theorem extJump_concatF_actWord {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hU : U ∈ ReachAll p m) (r : ℕ) {n : ℕ} (hn : n < totLen r (fun i => actWord p m U i)) :
    extJump (totLen r (fun i => actWord p m U i)) (concatF r (fun i => actWord p m U i)) n
      = nextJumpVec p m U n := by
  have h := extJump_concatF_of_blockJumps (p := p) (m := m) (U := U) r 0
    (fun i => actWord p m U i) ?_ n hn
  · simpa using h
  · intro i t
    have h2 := preLen_actWord (p := p) (m := m) hU i r 0 (le_of_lt i.2)
    rw [recTimeA_zero, Nat.zero_add] at h2
    have h3 : preLen r (fun j : Fin r => actWord p m U (0 + j)) (i : ℕ)
        = preLen r (fun j : Fin r => actWord p m U j) (i : ℕ) := by
      congr 2
      funext j
      rw [Nat.zero_add]
    rw [← h3]
    show M4RecordGeom.blockWord p m U i t = _
    rw [Nat.zero_add, h2, Nat.zero_add]
    rfl

/-- **The actual block words form a first-record chain.** -/
theorem frChain_actWord {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}
    (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) :
    ∀ (r j : ℕ), FRChainF hm (M4RecordGeom.actRecState p m U hm hU j) r
      (fun i : Fin r => actWord p m U (j + i)) := by
  intro r
  induction r with
  | zero => intro j; trivial
  | succ r ih =>
      intro j
      have hhead : Record.FirstRecord
          (Record.extendPath ((fun i : Fin (r + 1) => actWord p m U (j + i)) 0).2)
          ((fun i : Fin (r + 1) => actWord p m U (j + i)) 0).1
          (Record.ofRecState (M4RecordGeom.actRecState p m U hm hU j)) := by
        simpa [actWord] using M4RecordGeom.firstRecord_blockWord hm hU j
      refine (frChainF_succ hm _ r _).mpr ⟨hhead, ?_⟩
      have hstate : SimJump.RecKernel.out hm
          ((fun i : Fin (r + 1) => actWord p m U (j + i)) 0).2
          (M4RecordGeom.actRecState p m U hm hU j)
          = M4RecordGeom.actRecState p m U hm hU (j + 1) := by
        rw [M4RecordGeom.actRecState_succ hm hU j]
        rfl
      rw [hstate]
      have h := ih (j + 1)
      convert h using 2
      exact congrArg (actWord p m U) (by rw [Fin.val_succ]; omega)


/-! ### The repaired family: determination, disjointness, covering, mass -/

/-- Totalised actual compact record state: the actual state on `ReachAll`, the all-at-the-record
state off it.  Off `ReachAll` the record time is `0`, so at level `0` the totalisation is exact
(`actRecStateT_zero`). -/
noncomputable def actRecStateT (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (hm : 1 ≤ m)
    (r : ℕ) : RecState N m :=
  if h : U ∈ ReachAll p m then M4RecordGeom.actRecState p m U hm h r
    else SwarmRecordMeas.StartLaw.zeroState hm

theorem actRecStateT_of_reach {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} (hm : 1 ≤ m)
    (h : U ∈ ReachAll p m) (r : ℕ) :
    actRecStateT p m U hm r = M4RecordGeom.actRecState p m U hm h r := by
  rw [actRecStateT, dif_pos h]

/-- The totalised state at level `0` is the all-at-the-record state, pointwise. -/
theorem actRecStateT_zero {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} (hm : 1 ≤ m) :
    actRecStateT p m U hm 0 = SwarmRecordMeas.StartLaw.zeroState hm := by
  rw [actRecStateT]
  split
  · next h => rw [M4RecordGeom.actRecState_zero hm h]
  · next h => rfl

theorem measurableSet_rbox {p : ℝ} {m : ℕ} {r : ℕ} {w : Fin r → Word N} :
    MeasurableSet (rbox p m r w) :=
  (measurableSet_jbox p m (totLen r w) (concatF r w)).inter
    ((measurable_recTimeA p m r) (measurableSet_singleton (totLen r w)))

/-- **Determination on the repaired family**: on `rbox w` the actual record time and compact record
state at level `r` are the tuple's total length and its nested `out` chain. -/
theorem rbox_stat {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} (hm : 1 ≤ m) {r : ℕ}
    {w : Fin r → Word N} (hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w)
    (hU : U ∈ ReachAll p m) (hbox : U ∈ rbox p m r w) :
    recTimeA p m U r = totLen r w ∧
      M4RecordGeom.actRecState p m U hm hU r
        = runOutF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w := by
  obtain ⟨h1, h2⟩ := box_det hm hU hFR hbox.1 r le_rfl
  rw [preLen_eq_totLen] at h1
  rw [recStateF_self] at h2
  exact ⟨h1, h2⟩

/-- **The repaired family is pairwise disjoint.** -/
theorem rbox_disjoint {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    Pairwise (fun w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (rbox p m r w.1) (rbox p m r w'.1)) := by
  intro w w' hne
  rw [Set.disjoint_left]
  intro U hU hU'
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact hne (Subsingleton.elim w w')
  · have hreach : U ∈ ReachAll p m := rbox_subset_reach hm w.2 hr hU
    have hreach' : U ∈ ReachAll p m := rbox_subset_reach hm w'.2 hr hU'
    have hpre : ∀ i, i ≤ r → preLen r w.1 i = preLen r w'.1 i := by
      intro i hi
      rw [← (box_det hm hreach w.2 hU.1 i hi).1,
        ← (box_det hm hreach' w'.2 hU'.1 i hi).1]
    have hL : totLen r w.1 = totLen r w'.1 := by
      rw [← preLen_eq_totLen, ← preLen_eq_totLen]
      exact hpre r le_rfl
    have hword : extJump (totLen r w.1) (concatF r w.1)
        = extJump (totLen r w'.1) (concatF r w'.1) := by
      funext t
      by_cases ht : t < totLen r w.1
      · rw [extJump_apply _ ht, extJump_apply _ (by omega)]
        funext i
        exact (hU.1 ⟨t, ht⟩ i).symm.trans (hU'.1 ⟨t, by omega⟩ i)
      · rw [extJump, dif_neg ht, extJump, dif_neg (by omega)]
    exact hne (Subtype.ext (tuple_ext hm r w.1 w'.1 w.2 w'.2 hpre hword))

/-- **The repaired family covers almost every array**: the actual block decomposition of every
`U ∈ ReachAll` produces a first-record chain whose repaired box contains `U`. -/
theorem rbox_covered {p : ℝ} {m : ℕ} (hm : 1 ≤ m) (r : ℕ) {U : Swarming.Uniform.Array N}
    (hU : U ∈ ReachAll p m) :
    ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, U ∈ rbox p m r w.1 := by
  have hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r
      (fun i : Fin r => actWord p m U i) := by
    have h := frChain_actWord (p := p) (m := m) hm hU r 0
    rw [M4RecordGeom.actRecState_zero hm hU] at h
    simpa using h
  refine ⟨⟨fun i => actWord p m U i, hFR⟩, ?_, ?_⟩
  · intro n i
    have hn : (n : ℕ) < totLen r (fun i => actWord p m U i) := n.2
    have h := extJump_concatF_actWord (p := p) (m := m) hU r hn
    rw [extJump_apply _ hn] at h
    exact congrFun h.symm i
  · have h := preLen_actWord (p := p) (m := m) hU r r 0 le_rfl
    rw [recTimeA_zero, Nat.zero_add, Nat.zero_add] at h
    rw [preLen_eq_totLen] at h
    have hw : (fun j : Fin r => actWord p m U (0 + j)) = (fun j : Fin r => actWord p m U j) := by
      funext j
      rw [Nat.zero_add]
    rw [hw] at h
    exact h.symm

/-- **The repaired box has the same mass as the bare box**, hence the exact product mass. -/
theorem measure_rbox {p : ℝ} {m : ℕ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hm1 : 1 ≤ m) (hm2 : 2 ≤ m) (hN : 2 ≤ N) {r : ℕ} {w : Fin r → Word N}
    (hFR : FRChainF hm1 (SwarmRecordMeas.StartLaw.zeroState hm1) r w) :
    (arrayMeasure N) (rbox p m r w)
      = ENNReal.ofReal (blockProdF p hm1 (SwarmRecordMeas.StartLaw.zeroState hm1) r w) := by
  have hiff : (rbox p m r w) =ᵐ[arrayMeasure N] jbox p m (totLen r w) (concatF r w) := by
    filter_upwards [M4RecordGeom.ae_reachAll (N := N) hp0 hp1 hm2 hN] with U hU
    apply propext
    constructor
    · exact fun h => h.1
    · intro hbox
      refine ⟨hbox, ?_⟩
      show recTimeA p m U r = totLen r w
      rw [(box_det hm1 hU hFR hbox r le_rfl).1, preLen_eq_totLen]
  rw [measure_congr hiff, mass_jbox_concatF hp0 hp1 hm1 r w hFR]


/-! ### The unconditional actual finite record-state law -/

/-- **Determination as an identity of statistics**: on the repaired box of `w` the totalised
actual `(state, time)` pair is exactly `w`'s block endpoint. -/
theorem rbox_stat_pair {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {r : ℕ} {w : Fin r → Word N}
    (hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w)
    {U : Swarming.Uniform.Array N} (hU : U ∈ rbox p m r w) :
    (actRecStateT p m U hm r, recTimeA p m U r)
      = endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [actRecStateT_zero, M6Aggr.endptF, recTimeA_zero]
    exact Prod.ext rfl rfl
  · have hreach : U ∈ ReachAll p m := rbox_subset_reach hm hFR hr hU
    obtain ⟨h1, h2⟩ := rbox_stat hm hFR hreach hU
    rw [actRecStateT_of_reach hm hreach r, h1, h2, M6Aggr.endptF]
    simp

/-- The array piece of the repaired family on which the block endpoint falls in `A`. -/
noncomputable def rpiece {m : ℕ} (hm : 1 ≤ m) (p : ℝ) (r : ℕ)
    (A : Set (RecState N m × ℕ)) (w : Fin r → Word N) : Set (Array N) :=
  if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A then rbox p m r w else ∅

theorem measurableSet_rpiece {m : ℕ} (hm : 1 ≤ m) {p : ℝ} {r : ℕ}
    {A : Set (RecState N m × ℕ)} (w : Fin r → Word N) :
    MeasurableSet (rpiece (N := N) hm p r A w) := by
  rw [rpiece]
  split
  · exact measurableSet_rbox
  · exact MeasurableSet.empty

theorem actual_block_law {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (hm2 : 2 ≤ m) (hN : 2 ≤ N) (r : ℕ)
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | (actRecStateT p m U hm r, recTimeA p m U r) ∈ A}
      = ((SwarmKB.step (hitKKernelT p hm))^[r]
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState hm, 0))) A := by
  classical
  have hpiece_sub : ∀ w : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      rpiece hm p r A w.1 ⊆
        {U : Array N | (actRecStateT p m U hm r, recTimeA p m U r) ∈ A} := by
    intro w U hU
    simp only [rpiece] at hU
    by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · rw [if_pos hmem] at hU
      show (actRecStateT p m U hm r, recTimeA p m U r) ∈ A
      rw [rbox_stat_pair hm w.2 hU]
      exact hmem
    · rw [if_neg hmem] at hU
      exact absurd hU (Set.notMem_empty U)
  have hdisj : Pairwise (fun w w' : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (rpiece hm p r A w.1) (rpiece hm p r A w'.1)) := by
    intro w w' hne
    simp only [rpiece]
    by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · by_cases hmem' : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_pos hmem, if_pos hmem']
        exact rbox_disjoint (p := p) (m := m) hm r hne
      · rw [if_pos hmem, if_neg hmem']
        exact disjoint_bot_right
    · rw [if_neg hmem]
      exact disjoint_bot_left
  have hae : {U : Array N | (actRecStateT p m U hm r, recTimeA p m U r) ∈ A}
      =ᵐ[arrayMeasure N] ⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, rpiece hm p r A w.1 := by
    filter_upwards [M4RecordGeom.ae_reachAll (N := N) hp0 hp1 hm2 hN] with U hU
    apply propext
    constructor
    · intro hSA
      obtain ⟨w, hw⟩ := rbox_covered hm r hU
      refine Set.mem_iUnion.mpr ⟨w, ?_⟩
      simp only [rpiece]
      by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
      · rw [if_pos hmem]
        exact hw
      · rw [if_neg hmem]
        exact absurd (by rw [← rbox_stat_pair hm w.2 hw]; exact hSA) hmem
    · intro hmem
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
      exact hpiece_sub w hw
  have hcard : ∀ w : {w : Fin r → Word N //
      FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      (arrayMeasure N) (rpiece hm p r A w.1)
        = (arrayMeasure N) (jbox p m (totLen r w.1) (concatF r w.1)) *
            (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0) := by
    intro w
    simp only [rpiece]
    by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · rw [if_pos hmem, if_pos hmem, mul_one,
        measure_rbox hp0 hp1 hm hm2 hN w.2, mass_jbox_concatF hp0 hp1 hm r w.1 w.2]
    · rw [if_neg hmem, if_neg hmem, measure_empty, mul_zero]
  calc (arrayMeasure N) {U : Array N | (actRecStateT p m U hm r, recTimeA p m U r) ∈ A}
      = (arrayMeasure N) (⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          rpiece hm p r A w.1) := measure_congr hae
    _ = ∑' w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          (arrayMeasure N) (rpiece hm p r A w.1) :=
        measure_iUnion hdisj (fun w => measurableSet_rpiece hm w.1)
    _ = ∑' w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          (arrayMeasure N) (jbox p m (totLen r w.1) (concatF r w.1)) *
            (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0) :=
        tsum_congr hcard
    _ = ((SwarmKB.step (hitKKernelT p hm))^[r]
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState hm, 0))) A :=
        tsum_block_mass_eq_iterate hp0 hp1 hm r hA

end M7Block
