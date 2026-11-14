/-
# Direction E, stage 2: the actual array's first stopped-record iterate

`M5JumpBox.mass_jbox_pathW` gives the exact probability, in the actual array, of any prescribed
finite jump word, in exactly the weight `pathW` used by the stopped record kernel
`SimJump.RecKernel.hitKKernelT`.  This file identifies the *first record*.

* `hit1` is the first time some walker of the actual array sits at `1` (total, value `0` when it
  never does); `hit1_spec`/`hit1_min` come from the fixed-instance `Nat.find` toolkit of
  `RecordMeas`, so they are usable in rewrites.
* `hit1_firstRecord`: on the jump box of a first-record word `q` of length `k`, the hit time is
  exactly `k`.  This uses `StoppedState.pos_nonpos_of_no_rec` (a walker must sit at `1` before it
  can be positive) and the trajectory identification `trajectory_eq_runJ_ext`.
* `recAtHit1`: the compact record state at the hit time, as `out` of the hit block, so the
  identification with `hitKInfT`'s atom `out q y₀` is `rfl`-level after unfolding.
* `ae_hit1_exists`: the actual array does hit level `1` almost surely (from the proved
  one-walker ballistic bound, at every parameter in `1/2 < p < 1`, `m ≥ 2`).
* `first_iterate_law`: for every measurable `A` of the stopped-record state space, the actual
  probability that the first record state and time lie in `A` equals `hitKInfT p hm (y₀,0) A`,
  the **first iterate of the stopped record kernel** from the compatible start law
  `dirac (y₀, 0)` of `RecordStartLaw`.

The residual beyond this file is exactly the *later* blocks: from the second block on, the
coordinates read after the record time are still fresh but the conditioning event is the past
record data, so the transfer needs the strong Markov property at the record times.  Nothing here
asserts that, nor `Swarm.Ballistic`, `RegenAvailable`, `MainClaim` or a common speed.
-/
import Swarm.ActualJumpBox
import Swarm.ChainLink

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M5FirstBlock

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState

open SwarmRec

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### The finite word used by the stopped record chain

`extJump` of `M5JumpBox` and `SimJump.Record.extendPath` are the same continuation. -/

theorem extJump_eq_extendPath (r : ℕ) (q : Fin r → JumpVec N) :
    extJump r q = Record.extendPath q := by
  funext n
  by_cases h : n < r <;> simp [extJump, Record.extendPath, h]

/-! ### The first level-`1` hit time of the actual array -/

/-- The level-`1` hit predicate, totalised in the style of `RecordMeas.hitPred`: off the hitting
event it holds at `n = 0`. -/
def hitPred1 (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : Prop :=
  (¬ ∃ (n' : ℕ) (i : Fin N), actX p m U i n' = (1 : ℤ)) ∨ (∃ i : Fin N, actX p m U i n = (1 : ℤ))

theorem hitPred1_exists (p : ℝ) (m : ℕ) (U : Array N) : ∃ n, hitPred1 p m U n := by
  by_cases h : ∃ (n' : ℕ) (i : Fin N), actX p m U i n' = (1 : ℤ)
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inr hn⟩
  · exact ⟨0, Or.inl h⟩

/-- **The first time some walker of the actual array sits at `1`** (value `0` if never). -/
noncomputable def hit1 (p : ℝ) (m : ℕ) (U : Array N) : ℕ :=
  SwarmRecordMeas.firstHit (hitPred1 p m) (hitPred1_exists p m) U

theorem hit1_spec (p : ℝ) (m : ℕ) (U : Array N) : hitPred1 p m U (hit1 p m U) :=
  SwarmRecordMeas.firstHit_spec (hitPred1 p m) (hitPred1_exists p m) U

theorem hit1_min (p : ℝ) (m : ℕ) (U : Array N) {n : ℕ} (hn : n < hit1 p m U) :
    ¬ hitPred1 p m U n :=
  SwarmRecordMeas.firstHit_min (hitPred1 p m) (hitPred1_exists p m) U hn

/-- On a genuine first hit, `hit1` is that hit time. -/
theorem hit1_eq_of_first (p : ℝ) (m : ℕ) (U : Array N) {k : ℕ}
    (h : ∃ i : Fin N, actX p m U i k = (1 : ℤ))
    (hmin : ∀ n : ℕ, n < k → ¬ ∃ i : Fin N, actX p m U i n = (1 : ℤ)) :
    hit1 p m U = k := by
  have hex : ∃ (n' : ℕ) (i : Fin N), actX p m U i n' = (1 : ℤ) := ⟨k, h⟩
  have hspec : ∃ i : Fin N, actX p m U i (hit1 p m U) = (1 : ℤ) := by
    rcases hit1_spec p m U with hcontra | hhit
    · exact absurd hex hcontra
    · exact hhit
  refine le_antisymm ?_ ?_
  · exact SwarmRecordMeas.firstHit_min' (hitPred1 p m) (hitPred1_exists p m) U (Or.inr h)
  · by_contra hlt
    push Not at hlt
    exact hmin (hit1 p m U) hlt hspec

/-! ### The record state at the first hit -/

/-- The compact record state at the first hit time: the stopped record update `out` of the
array's own hit block. -/
noncomputable def recAtHit1 (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (U : Array N) :
    SwarmRec.RecState N m :=
  out hm (fun t : Fin (hit1 p m U) => nextJumpVec p m U (t : ℕ))
    (SwarmRecordMeas.StartLaw.zeroState hm)

/-! ### Congruence lemmas for the chain algebra -/

theorem evolveFun_congr {m : ℕ} {u u' : ℕ → JumpVec N} {k : ℕ}
    (h : ∀ t, t < k → u t = u' t) (s : SimJump.State N m) :
    SimJump.evolveFun u k s = SimJump.evolveFun u' k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [SimJump.evolveFun_succ, SimJump.evolveFun_succ,
        ih (fun t ht => h t (Nat.lt_trans ht (Nat.lt_succ_self k))),
        h k (Nat.lt_succ_self k)]

theorem FirstRecord_congr {m : ℕ} {u u' : ℕ → JumpVec N} {k : ℕ} {s : SimJump.State N m}
    (h : ∀ t, t < k → u t = u' t) :
    Record.FirstRecord u k s ↔ Record.FirstRecord u' k s := by
  unfold Record.FirstRecord
  rw [evolveFun_congr h s]
  have hprev : ∀ t, t < k → SimJump.evolveFun u t s = SimJump.evolveFun u' t s :=
    fun t ht => evolveFun_congr (fun t' ht' => h t' (Nat.lt_trans ht' ht)) s
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht i => by rw [← hprev t ht]; exact h2 t ht i⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht i => by rw [hprev t ht]; exact h2 t ht i⟩

/-! ### The first-record identification on a jump box -/

/-- On the box of a first-record word, the array's hit time is the word's length. -/
theorem hit1_eq_of_box (p : ℝ) (m : ℕ) (hm : 1 ≤ m) {k : ℕ} {q : Fin k → JumpVec N}
    (hFR : Record.FirstRecord (extJump k q)
      k (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)))
    {U : Array N} (hbox : U ∈ jbox p m k q) :
    hit1 p m U = k := by
  have hword : ∀ t : ℕ, t < k → ∀ i : Fin N, nextJumpVec p m U t i = extJump k q t i := by
    intro t ht i
    rw [extJump_apply q ht]
    exact hbox ⟨t, ht⟩ i
  -- the actual trajectory agrees with the chain state at every time up to `k`
  have hpos : ∀ t : ℕ, t ≤ k → ∀ i : Fin N,
      actX p m U i t = (SimJump.evolveFun (extJump k q) t
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))).pos i := by
    intro t ht i
    have htr : trajectory p m U t = runJ m (extJump k q) t := by
      refine trajectory_eq_runJ_of_prefix p m U (fun t' ht' j => ?_)
      rw [extJump_apply q (lt_of_lt_of_le ht' ht)]
      exact hbox ⟨t', lt_of_lt_of_le ht' ht⟩ j
    have hev : SimJump.evolveFun (extJump k q) t
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))
        = capState m (runJ m (extJump k q) t) := by
      rw [ofRecState_zeroState m hm, startState, evolveFun_capState]
    show (trajectory p m U t).pos i = _
    rw [hev, capState_pos]
    exact congrArg (fun s => s.pos i) htr
  refine hit1_eq_of_first p m U ?_ ?_
  · obtain ⟨i, hi⟩ := hFR.1
    refine ⟨i, ?_⟩
    rw [hpos k le_rfl i, hi]
  · intro n hn
    rintro ⟨i, hi⟩
    have hle : (SimJump.evolveFun (extJump k q) n
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))).pos i ≤ 0 :=
      hFR.2 n hn i
    rw [hpos n (le_of_lt hn) i] at hi
    omega


/-! ### Almost sure existence of the level-`1` hit -/

theorem ae_hit1_exists {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ (n : ℕ) (i : Fin N), actX p m U i n = (1 : ℤ) := by
  obtain ⟨κ, hκ, hspeed⟩ := RecordoSupply.speed_actual hp0 hp1 hm
  filter_upwards [hspeed N hN] with U hU
  have hspd := hU (Classical.arbitrary (Fin N))
  obtain ⟨n, hn⟩ := RecordoSupply.exists_runMax_ge (actX p m U) hκ hspd 1
  obtain ⟨k, -, hk⟩ := RecordoSupply.exists_runMax_eq (actX p m U) (actX_step p m U)
    (actX_zero p m U) hn
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  rw [RecordDefect.runMax, SwarmRecordMeas.finset_sup'_eq_iff hne] at hk
  obtain ⟨i, -, hi⟩ := hk.2
  exact ⟨k, i, hi⟩

/-! ### The record state at the hit time is the stopped-record update of the block -/

theorem recAtHit1_eq_out (p : ℝ) (m : ℕ) (hm : 1 ≤ m) {k : ℕ} {q : Fin k → JumpVec N}
    (hFR : Record.FirstRecord (extJump k q) k
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)))
    {U : Array N} (hbox : U ∈ jbox p m k q) :
    recAtHit1 p m hm U = out hm q (SwarmRecordMeas.StartLaw.zeroState hm) := by
  have hhit : hit1 p m U = k := hit1_eq_of_box p m hm hFR hbox
  have hwords : ∀ t : ℕ, t < k → Record.extendPath q t
      = Record.extendPath (fun t : Fin k => nextJumpVec p m U (t : ℕ)) t := by
    intro t ht
    simp only [Record.extendPath, ht, dif_pos]
    funext i
    exact (hbox ⟨t, ht⟩ i).symm
  have hFR' : Record.FirstRecord
      (Record.extendPath (fun t : Fin k => nextJumpVec p m U (t : ℕ))) k
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)) :=
    (FirstRecord_congr (u := Record.extendPath q)
      (u' := Record.extendPath (fun t : Fin k => nextJumpVec p m U (t : ℕ))) hwords).mp
      (by rw [← extJump_eq_extendPath]; exact hFR)
  unfold recAtHit1
  rw [hhit, out_of_firstRecord hm (fun t : Fin k => nextJumpVec p m U (t : ℕ))
      (SwarmRecordMeas.StartLaw.zeroState hm) hFR',
    out_of_firstRecord hm q (SwarmRecordMeas.StartLaw.zeroState hm)
      (by rw [← extJump_eq_extendPath]; exact hFR)]
  refine Subtype.ext ?_
  rw [recState_val, recState_val]
  exact congrArg Record.toRecordAmb (evolveFun_congr hwords _).symm

/-! ### Measurability, disjointness and the almost sure block covering -/

theorem measurableSet_jbox (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    MeasurableSet (jbox p m r q) := by
  rw [jbox_eq_cyl_prod]
  exact MeasurableSet.iInter fun ni =>
    (measurableSet_jumpSet _ _).preimage (measurable_pi_apply _)

theorem jbox_subset_hit1 (p : ℝ) (m : ℕ) (hm : 1 ≤ m) {k : ℕ} {q : Fin k → JumpVec N}
    (hFR : Record.FirstRecord (extJump k q) k
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))) :
    jbox p m k q ⊆ {U : Array N | hit1 p m U = k} := by
  intro U hU
  exact hit1_eq_of_box p m hm hFR hU

theorem jbox_disjoint (p : ℝ) (m : ℕ) (hm : 1 ≤ m)
    {a b : (k : ℕ) × (Fin k → JumpVec N)}
    (hFRa : Record.FirstRecord (extJump a.1 a.2) a.1
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)))
    (hFRb : Record.FirstRecord (extJump b.1 b.2) b.1
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)))
    (hab : a ≠ b) :
    Disjoint (jbox p m a.1 a.2) (jbox p m b.1 b.2) := by
  obtain ⟨ka, qa⟩ := a
  obtain ⟨kb, qb⟩ := b
  by_cases hk : ka = kb
  · subst hk
    rw [Set.disjoint_left]
    intro U hUa hUb
    have hq : qa = qb := by
      funext t i
      have h1 : nextJumpVec p m U (t : ℕ) i = qa t i := hUa t i
      have h2 : nextJumpVec p m U (t : ℕ) i = qb t i := hUb t i
      rw [h1] at h2
      exact h2
    exact hab (by rw [hq])
  · rw [Set.disjoint_left]
    intro U hUa hUb
    have hka := jbox_subset_hit1 p m hm hFRa hUa
    have hkb := jbox_subset_hit1 p m hm hFRb hUb
    exact hk (hka.symm.trans hkb)


/-! ### The trajectory identification used for the covering -/

theorem actX_eq_evolveFun (p : ℝ) (m : ℕ) (hm : 1 ≤ m) {k : ℕ} {q : Fin k → JumpVec N}
    {U : Array N} (hbox : U ∈ jbox p m k q) {t : ℕ} (ht : t ≤ k) (i : Fin N) :
    actX p m U i t = (SimJump.evolveFun (extJump k q) t
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))).pos i := by
  have htr : trajectory p m U t = runJ m (extJump k q) t := by
    refine trajectory_eq_runJ_of_prefix p m U (fun t' ht' j => ?_)
    rw [extJump_apply q (lt_of_lt_of_le ht' ht)]
    exact hbox ⟨t', lt_of_lt_of_le ht' ht⟩ j
  have hev : SimJump.evolveFun (extJump k q) t
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm))
      = capState m (runJ m (extJump k q) t) := by
    rw [ofRecState_zeroState m hm, startState, evolveFun_capState]
  show (trajectory p m U t).pos i = _
  rw [hev, capState_pos]
  exact congrArg (fun s => s.pos i) htr

/-- **On the hit block, the array's first record is a `FirstRecord` path.** -/
theorem firstRecord_hitBlock (p : ℝ) {m : ℕ} (hm1 : 1 ≤ m) {U : Array N}
    (hhit : ∃ (n : ℕ) (i : Fin N), actX p m U i n = (1 : ℤ)) :
    Record.FirstRecord (extJump (hit1 p m U)
        (fun t : Fin (hit1 p m U) => nextJumpVec p m U (t : ℕ)))
      (hit1 p m U) (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) := by
  have hbox : U ∈ jbox p m (hit1 p m U) (fun t : Fin (hit1 p m U) => nextJumpVec p m U (t : ℕ)) :=
    fun _ _ => rfl
  have hspec : ∃ i : Fin N, actX p m U i (hit1 p m U) = (1 : ℤ) := by
    rcases hit1_spec p m U with hcontra | hh
    · exact absurd hhit hcontra
    · exact hh
  have hmin : ∀ n : ℕ, n < hit1 p m U → ¬ ∃ i : Fin N, actX p m U i n = (1 : ℤ) := by
    intro n hn hcon
    exact hit1_min p m U hn (Or.inr hcon)
  have hs : ∀ i : Fin N,
      (SimJump.Record.ofRecState
        (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm1)).pos i ≤ 0 := by
    intro i
    rw [ofRecState_zeroState m hm1]
    exact le_of_eq (startState_pos m i).symm
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hspec
    refine ⟨i, ?_⟩
    rw [actX_eq_evolveFun p m hm1 hbox le_rfl i] at hi
    exact hi
  · intro t ht i
    have hst : ∀ n : ℕ, n ≤ t → ¬ IsRec
        (SimJump.evolveFun (extJump (hit1 p m U)
          (fun t : Fin (hit1 p m U) => nextJumpVec p m U (t : ℕ))) n
          (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1))) := by
      intro n hn hrec
      obtain ⟨j, hj⟩ := hrec
      have h1 := actX_eq_evolveFun p m hm1 hbox (le_trans hn (le_of_lt ht)) j
      have h2 : actX p m U j n = 1 := by rw [h1]; exact hj
      exact hmin n (lt_of_le_of_lt hn ht) ⟨j, h2⟩
    exact pos_nonpos_of_no_rec hs t hst i


/-! ### The almost sure covering by first-record blocks -/

theorem ae_covered (p : ℝ) {m : ℕ} (hm1 : 1 ≤ m) {U : Array N}
    (hhit : ∃ (n : ℕ) (i : Fin N), actX p m U i n = (1 : ℤ)) :
    ∃ pq : (k : ℕ) × (Fin k → JumpVec N),
      Record.FirstRecord (extJump pq.1 pq.2) pq.1
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧
      U ∈ jbox p m pq.1 pq.2 := by
  refine ⟨⟨hit1 p m U, fun t : Fin (hit1 p m U) => nextJumpVec p m U (t : ℕ)⟩,
    firstRecord_hitBlock p hm1 hhit, fun _ _ => rfl⟩

/-! ### The first iterate of the stopped record kernel -/

/-- **The law of the actual array's first record equals the first iterate of the stopped record
kernel from the compatible start law.**  For every measurable `A` of the stopped-record state
space, the actual array probability that (compact record state at the first level-`1` hit, hit
time) lies in `A` equals `hitKInfT p hm (y₀, 0) A`, the first step of the time-extended
stopped record chain started at the all-at-the-record state `y₀ = zeroState` at time `0`.

This is the `r = 1` case of `Bridge.JointLawIdentity`, proved outright: the block masses are the
exact product-measure computation `mass_jbox_pathW`, the blocks are disjoint first-record paths,
and the level-`1` hit exists almost surely. -/
theorem first_iterate_law {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ A : Set (SwarmRec.RecState N m × ℕ), MeasurableSet A →
      (arrayMeasure N) {U : Array N |
          (recAtHit1 p m hm1 U, hit1 p m U) ∈ A}
        = hitKInfT p hm1 (SwarmRecordMeas.StartLaw.zeroState hm1, 0) A := by
  intro A hA
  classical
  have hcov : ∀ᵐ U ∂(arrayMeasure N), ∃ (n : ℕ) (i : Fin N), actX p m U i n = (1 : ℤ) :=
    ae_hit1_exists hp0 hp1 hm2 hN
  set pt : (k : ℕ) × (Fin k → JumpVec N) → SwarmRec.RecState N m × ℕ :=
    fun pq => (out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1), pq.1) with hpt
  set piece : (k : ℕ) × (Fin k → JumpVec N) → Set (Array N) := fun pq =>
    if Record.FirstRecord (extJump pq.1 pq.2) pq.1
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt pq ∈ A
      then jbox p m pq.1 pq.2 else ∅ with hpiece
  have hpiece_meas : ∀ pq, MeasurableSet (piece pq) := by
    intro pq
    by_cases h : Record.FirstRecord (extJump pq.1 pq.2) pq.1
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt pq ∈ A
    · rw [show piece pq = jbox p m pq.1 pq.2 from by simp only [piece, if_pos h]]
      exact measurableSet_jbox p m pq.1 pq.2
    · rw [show piece pq = ∅ from by simp only [piece, if_neg h]]
      exact MeasurableSet.empty
  have hpiece_sub : ∀ pq, piece pq ⊆ {U : Array N | (recAtHit1 p m hm1 U, hit1 p m U) ∈ A} := by
    intro pq U hU
    by_cases h : Record.FirstRecord (extJump pq.1 pq.2) pq.1
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt pq ∈ A
    · have hbox : U ∈ jbox p m pq.1 pq.2 := by
        rwa [show piece pq = jbox p m pq.1 pq.2 from by simp only [piece, if_pos h]] at hU
      have h1 : recAtHit1 p m hm1 U = out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1) :=
        recAtHit1_eq_out p m hm1 h.1 hbox
      have h2 : hit1 p m U = pq.1 := jbox_subset_hit1 p m hm1 h.1 hbox
      show (recAtHit1 p m hm1 U, hit1 p m U) ∈ A
      rw [h1, h2]
      exact h.2
    · rw [show piece pq = ∅ from by simp only [piece, if_neg h]] at hU
      exact absurd hU (by simp)
  have hdisj : Pairwise (fun a b => Disjoint (piece a) (piece b)) := by
    intro a b hab
    by_cases ha : Record.FirstRecord (extJump a.1 a.2) a.1
        (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt a ∈ A
    · by_cases hb : Record.FirstRecord (extJump b.1 b.2) b.1
          (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt b ∈ A
      · rw [show piece a = jbox p m a.1 a.2 from by simp only [piece, if_pos ha],
          show piece b = jbox p m b.1 b.2 from by simp only [piece, if_pos hb]]
        exact jbox_disjoint p m hm1 ha.1 hb.1 hab
      · rw [show piece b = ∅ from by simp only [piece, if_neg hb]]
        exact disjoint_bot_right
    · rw [show piece a = ∅ from by simp only [piece, if_neg ha]]
      exact disjoint_bot_left
  have hEqae : {U : Array N | (recAtHit1 p m hm1 U, hit1 p m U) ∈ A}
      =ᵐ[arrayMeasure N] ⋃ pq, piece pq := by
    filter_upwards [hcov] with U hU
    refine propext ⟨?_, ?_⟩
    · intro hS
      have hS' : (recAtHit1 p m hm1 U, hit1 p m U) ∈ A := hS
      obtain ⟨pq, hFpq, hbox⟩ := ae_covered p hm1 hU
      have h1 : recAtHit1 p m hm1 U = out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1) :=
        recAtHit1_eq_out p m hm1 hFpq hbox
      have h2 : hit1 p m U = pq.1 := jbox_subset_hit1 p m hm1 hFpq hbox
      have hpair : pt pq ∈ A := by
        have heq : (recAtHit1 p m hm1 U, hit1 p m U) = pt pq := by
          simp only [hpt, h1, h2]
        rwa [heq] at hS'
      have hcond : Record.FirstRecord (extJump pq.1 pq.2) pq.1
          (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt pq ∈ A :=
        ⟨hFpq, hpair⟩
      refine Set.mem_iUnion.mpr ⟨pq, ?_⟩
      rw [show piece pq = jbox p m pq.1 pq.2 from by simp only [piece, if_pos hcond]]
      exact hbox
    · intro hU
      obtain ⟨pq, hmem⟩ := Set.mem_iUnion.mp hU
      exact hpiece_sub pq hmem
  have hY : SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)
      = startState (N := N) m := ofRecState_zeroState m hm1
  calc (arrayMeasure N) {U : Array N | (recAtHit1 p m hm1 U, hit1 p m U) ∈ A}
      = (arrayMeasure N) (⋃ pq, piece pq) := measure_congr hEqae
    _ = ∑' pq, (arrayMeasure N) (piece pq) := measure_iUnion hdisj hpiece_meas
    _ = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
          ENNReal.ofReal (hitW p pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1)) *
            (if (out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1), (0 : ℕ) + pq.1) ∈ A
              then 1 else 0) := by
        refine tsum_congr fun pq => ?_
        by_cases h : Record.FirstRecord (extJump pq.1 pq.2) pq.1
            (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) ∧ pt pq ∈ A
        · rw [show piece pq = jbox p m pq.1 pq.2 from by simp only [piece, if_pos h],
            mass_jbox_pathW hp0 hp1 m pq.1 pq.2, ← hY,
            hitW_of_firstRecord p pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1) h.1,
            if_pos (show (out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1), (0 : ℕ) + pq.1)
              ∈ A from by simpa using h.2), mul_one]
        · rw [show piece pq = ∅ from by simp only [piece, if_neg h], measure_empty]
          by_cases hF : Record.FirstRecord (extJump pq.1 pq.2) pq.1
              (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1))
          · have hA' : ¬ pt pq ∈ A := by
              intro hc; exact h ⟨hF, hc⟩
            rw [hitW_of_firstRecord p pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1) hF,
              if_neg (show ¬ ((out hm1 pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1), (0 : ℕ) + pq.1)
                ∈ A) from by simpa using hA'), mul_zero]
          · rw [hitW_of_not_firstRecord p pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1) hF]
            simp
    _ = hitKInfT p hm1 (SwarmRecordMeas.StartLaw.zeroState hm1, 0) A := by
        rw [hitKInfT_apply p hm1 (SwarmRecordMeas.StartLaw.zeroState hm1, 0) hA]


/-! ### The block masses in the stopped-record notation, and their total mass -/

/-- **The first-record block mass is exactly the stopped-record weight `hitW`.** -/
theorem mass_jbox_firstRecord {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) {k : ℕ} {q : Fin k → JumpVec N}
    (hFR : Record.FirstRecord (extJump k q) k
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1))) :
    arrayMeasure N (jbox p m k q)
      = ENNReal.ofReal (hitW p q (SwarmRecordMeas.StartLaw.zeroState hm1)) := by
  rw [mass_jbox_pathW hp0 hp1 m k q, ← ofRecState_zeroState m hm1,
    hitW_of_firstRecord p q (SwarmRecordMeas.StartLaw.zeroState hm1)
      (by rw [← extJump_eq_extendPath]; exact hFR)]

/-- **The first-record block masses form a probability law** (total mass one), the
`univ`-case of `first_iterate_law`, stated directly in terms of `hitW`. -/
theorem tsum_hitW_eq_one {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) :
    ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (hitW p pq.2 (SwarmRecordMeas.StartLaw.zeroState hm1)) = 1 := by
  have h := hitKInfT_univ (N := N) (m := m) p hp0.le hp1.le hm1
    (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm1, (0 : ℕ))
  rw [hitKInfT_apply (N := N) (m := m) p hm1
    (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm1, (0 : ℕ))
    MeasurableSet.univ] at h
  simpa using h

end M5FirstBlock
