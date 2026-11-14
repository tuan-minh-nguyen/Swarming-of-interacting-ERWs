/-
# Actual record geometry: level translations and the compact record state at `recTimeA`

The canonical record time of the actual array (`SwarmRecordMeas.Actual.recTimeA p m U r`) is the
first time the running maximum of the actual positions reaches the integer level `r`.  The
stopped record kernel (`SimJump.Record`, `areas/recordkernel`) instead works in *record
coordinates*: the current record level is always `0`, a block stops when a walker first reaches
`1`, and the compact state `RecState N m` stores half-distances below the record together with
capped local times.

This file supplies the deterministic bridge between the two, which is what turns the one-block
identifications of `ActualJumpBox`/`ActualFirstIterate`/`ActualTwoBlock` into a *k-level*
statement:

* `trans r s` — the level translation of a capped state (positions down by `r`, local-time index
  up by `r`).  `trans 1` is `SimJump.Record.normalize`.  The one-step chain, the one-step
  weights and the path weights are invariant under it (`step_trans`, `evolveFun_trans`,
  `stepW_trans`, `pathWFun_trans`).
* `recTimeA_lt_succ`, `recTimeA_ge_level`, `blockLen_spec`, `blockLen_min`: the record times are
  strictly increasing, `τ_r ≥ r`, and the block length `τ_{r+1} - τ_r` is exactly the first
  hitting time of level `1` by the actual array *shifted to level* `r` and *translated in time*
  to `τ_r`.
* `actRecState`: **the actual compact record state at level `r`**, a genuine element of
  `SwarmRec.RecState N m` built from the actual positions and capped local times at `τ_r`.
* `ofRecState_actRecState`: its expansion is the actual capped state at `τ_r` in record
  coordinates (`trans r`).
* `firstRecord_blockWord`: the actual jump word between `τ_r` and `τ_{r+1}` is a first-record
  path from that state.
* `actRecState_succ`: **the `(r+1)`-st actual compact record state is the stopped-record output**
  `out hm (block r) (actRecState r)`; with `actRecState_zero` and `actRecState_eq_nestOut` this
  identifies `actRecState r` with the `r`-fold iterate of the one-step map `out` applied to the
  all-at-the-record state.

Everything is stated on the measurable event `ReachAll` (where every level is attained and
`recTimeA` is the paper's `τ_r`); off it `recTimeA` is the totalised junk value `0` and no
statement is made.
-/
import Swarm.ActualTwoBlock

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M4RecordGeom

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.Record SwarmRec RecordDefect RecordoSupply
open SwarmRecordMeas SwarmRecordMeas.Actual Swarming.CurrentState M5FirstBlock

set_option autoImplicit false

set_option linter.unusedSectionVars false

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### Level translations of capped record states -/

/-- Translate the record window by `r` levels: positions drop by `r`, the local-time index
shifts by `r`.  For `r = 1` this is `SimJump.Record.normalize`. -/
def trans {m : ℕ} (r : ℕ) (s : SimJump.State N m) : SimJump.State N m where
  pos i := s.pos i - (r : ℤ)
  eta i x := s.eta i (x + (r : ℤ))
  hcap i x := s.hcap i (x + (r : ℤ))

@[simp] theorem trans_pos {m : ℕ} (r : ℕ) (s : SimJump.State N m) (i : Fin N) :
    (trans r s).pos i = s.pos i - (r : ℤ) := rfl

@[simp] theorem trans_eta {m : ℕ} (r : ℕ) (s : SimJump.State N m) (i : Fin N) (x : ℤ) :
    (trans r s).eta i x = s.eta i (x + (r : ℤ)) := rfl

theorem trans_zero {m : ℕ} (s : SimJump.State N m) : trans 0 s = s := by
  refine CurrentState.recordState_ext ?_ ?_
  · funext i; simp
  · funext i x; simp

theorem trans_add {m : ℕ} (r r' : ℕ) (s : SimJump.State N m) :
    trans r (trans r' s) = trans (r + r') s := by
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    simp only [trans_pos, Nat.cast_add]
    ring
  · funext i x
    simp only [trans_eta, Nat.cast_add]
    ring_nf

theorem trans_one_eq_normalize {m : ℕ} (s : SimJump.State N m) :
    trans 1 s = SimJump.Record.normalize s := by
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    rfl
  · funext i x
    rfl

/-! ### Equivariance of the one-step chain and of the path weights -/

theorem otherVisits_trans {m : ℕ} (r : ℕ) (s : SimJump.State N m) (i : Fin N) :
    SimJump.otherVisits (trans r s) i = SimJump.otherVisits s i := by
  unfold SimJump.otherVisits
  refine Finset.sum_congr rfl fun j _ => ?_
  show s.eta j ((s.pos i - (r : ℤ)) + (r : ℤ)) = s.eta j (s.pos i)
  rw [sub_add_cancel]

theorem qRight_trans (p : ℝ) {m : ℕ} (r : ℕ) (s : SimJump.State N m) (i : Fin N) :
    SimJump.qRight p m (trans r s) i = SimJump.qRight p m s i := by
  unfold SimJump.qRight
  rw [otherVisits_trans]

theorem stepW_trans (p : ℝ) {m : ℕ} (r : ℕ) (s : SimJump.State N m) (v : JumpVec N) :
    SimJump.stepW p m (trans r s) v = SimJump.stepW p m s v := by
  unfold SimJump.stepW
  exact Finset.prod_congr rfl fun i _ => by rw [qRight_trans]

theorem step_trans {m : ℕ} (r : ℕ) (s : SimJump.State N m) (v : JumpVec N) :
    SimJump.step m (trans r s) v = trans r (SimJump.step m s v) := by
  have hpos : SimJump.stepPos (trans r s) v = fun i => SimJump.stepPos s v i - (r : ℤ) := by
    funext i
    simp only [SimJump.stepPos, trans_pos]
    ring
  have hposi : ∀ i, SimJump.stepPos (trans r s) v i = SimJump.stepPos s v i - (r : ℤ) :=
    fun i => congrFun hpos i
  have heta : ∀ (i : Fin N) (x : ℤ),
      (SimJump.step m (trans r s) v).eta i x
        = (SimJump.step m s v).eta i (x + (r : ℤ)) := by
    intro i x
    show (if x = SimJump.stepPos (trans r s) v i then
        SimJump.cap m ((trans r s).eta i x + 1) else (trans r s).eta i x) = _
    show _ = (if x + (r : ℤ) = SimJump.stepPos s v i then
        SimJump.cap m (s.eta i (x + (r : ℤ)) + 1) else s.eta i (x + (r : ℤ)))
    by_cases hx : x + (r : ℤ) = SimJump.stepPos s v i
    · have hx' : x = SimJump.stepPos (trans r s) v i := by rw [hposi i]; omega
      rw [if_pos hx', if_pos hx, trans_eta]
    · have hx' : ¬ x = SimJump.stepPos (trans r s) v i := by
        intro hcon
        apply hx
        rw [hcon, hposi i]
        ring
      rw [if_neg hx', if_neg hx, trans_eta]
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    simp only [SimJump.step_pos, trans_pos]
    exact hposi i
  · funext i x
    exact heta i x

theorem evolveFun_trans {m : ℕ} (u : ℕ → JumpVec N) (r : ℕ) :
    ∀ (k : ℕ) (s : SimJump.State N m),
      SimJump.evolveFun u k (trans r s) = trans r (SimJump.evolveFun u k s) := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [SimJump.evolveFun_succ, SimJump.evolveFun_succ, ih, step_trans]

theorem pathWFun_trans (p : ℝ) {m : ℕ} (u : ℕ → JumpVec N) (r : ℕ) :
    ∀ (k : ℕ) (s : SimJump.State N m),
      SimJump.pathWFun p u k (trans r s) = SimJump.pathWFun p u k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [SimJump.pathWFun_succ, SimJump.pathWFun_succ, ih, evolveFun_trans, stepW_trans]

/-- `pathW` (finite words) is invariant under a level translation. -/
theorem pathW_trans (p : ℝ) {m : ℕ} (k : ℕ) (q : Fin k → JumpVec N) (r : ℕ)
    (s : SimJump.State N m) :
    SimJump.pathW p k q (trans r s) = SimJump.pathW p k q s := by
  rw [M5FirstBlock.pathW_eq_pathWFun_ext', M5FirstBlock.pathW_eq_pathWFun_ext',
    pathWFun_trans]

/-! ### The actual record sequence on `ReachAll` -/

section RecordSeq

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- On `ReachAll` the canonical record map `recTimeA` is the paper's `τ_r`. -/
theorem isRecord_recTimeA_of_reach (hU : U ∈ ReachAll p m) :
    IsRecord (actX p m U) (recTimeA p m U) :=
  isRecord_recTimeA p m U hU

/-- The record times are strictly increasing in the level. -/
theorem recTimeA_lt_succ (hU : U ∈ ReachAll p m) (r : ℕ) :
    recTimeA p m U r < recTimeA p m U (r + 1) := by
  have h := isRecord_recTimeA_of_reach hU
  have hmono : recTimeA p m U r ≤ recTimeA p m U (r + 1) := tau_mono h (Nat.le_succ r)
  rcases lt_or_eq_of_le hmono with hlt | heq
  · exact hlt
  · exfalso
    have h1 : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) := (h r).2
    have h2 : runMax (actX p m U) (recTimeA p m U (r + 1)) = ((r + 1 : ℕ) : ℤ) := (h (r + 1)).2
    rw [heq] at h1
    rw [Nat.cast_add, Nat.cast_one, h1] at h2
    omega

theorem recTimeA_le_succ (hU : U ∈ ReachAll p m) (r : ℕ) :
    recTimeA p m U r ≤ recTimeA p m U (r + 1) :=
  le_of_lt (recTimeA_lt_succ hU r)

/-- Before the record time of level `r + 1` the running maximum is below `r + 1`. -/
theorem runMax_lt_of_lt_recTimeA (hU : U ∈ ReachAll p m) {r n : ℕ}
    (hn : n < recTimeA p m U (r + 1)) :
    runMax (actX p m U) n < ((r + 1 : ℕ) : ℤ) :=
  (isRecord_recTimeA_of_reach hU (r + 1)).1 n hn

/-- Every walker is at most at the record level at a record time. -/
theorem actX_le_level (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    actX p m U i (recTimeA p m U r) ≤ (r : ℤ) := by
  refine le_trans (le_runMax (X := actX p m U) (n := recTimeA p m U r) i) (le_of_eq ?_)
  exact (isRecord_recTimeA_of_reach hU r).2

/-- At a record time some walker sits exactly at the record level. -/
theorem exists_actX_eq_level (hU : U ∈ ReachAll p m) (r : ℕ) :
    ∃ i : Fin N, actX p m U i (recTimeA p m U r) = (r : ℤ) := by
  have h2 : runMax (actX p m U) (recTimeA p m U r) = (r : ℤ) :=
    (isRecord_recTimeA_of_reach hU r).2
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun i => actX p m U i (recTimeA p m U r))
  exact ⟨i, hi.symm.trans h2⟩

/-- `τ_r ≥ r`: record times are at least the level. -/
theorem recTimeA_ge_level (hU : U ∈ ReachAll p m) (r : ℕ) : r ≤ recTimeA p m U r :=
  tau_ge (isRecord_recTimeA_of_reach hU) (actX_step p m U) (actX_zero p m U) r

/-- Every walker has the parity of the time: `X_n^i - n` is even. -/
theorem actX_sub_time_two_mul (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N) :
    ∀ n : ℕ, ∃ a : ℤ, actX p m U i n - (n : ℤ) = 2 * a := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp [actX_zero]⟩
  | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      have hstep : actX p m U i (n + 1) - actX p m U i n = 1 ∨
          actX p m U i (n + 1) - actX p m U i n = -1 := by
        have h1 := actX_step p m U i n
        rcases (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).1 h1 with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hstep with h | h
      · refine ⟨a, ?_⟩
        push_cast
        linarith
      · refine ⟨a - 1, ?_⟩
        push_cast
        linarith

/-- At a record time the level offset `X_{τ_r}^i - r` is even. -/
theorem actX_sub_level_two_mul (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    ∃ a : ℤ, actX p m U i (recTimeA p m U r) - (r : ℤ) = 2 * a := by
  obtain ⟨a₁, h₁⟩ := actX_sub_time_two_mul p m U i (recTimeA p m U r)
  obtain ⟨i₀, hi₀⟩ := exists_actX_eq_level hU r
  obtain ⟨a₂, h₂⟩ := actX_sub_time_two_mul p m U i₀ (recTimeA p m U r)
  refine ⟨a₁ - a₂, ?_⟩
  rw [hi₀] at h₂
  linarith

/-! ### The shifted running maximum and the block length -/

/-- A level translation of all walkers shifts the running maximum by the same constant. -/
theorem runMax_sub (X : Fin N → ℕ → ℤ) (r k : ℕ) :
    RecordDefect.runMax (fun i n => X i n - (r : ℤ)) k
      = RecordDefect.runMax X k - (r : ℤ) := by
  unfold RecordDefect.runMax
  refine le_antisymm ?_ ?_
  · rw [Finset.sup'_le_iff]
    intro i _
    have := Finset.le_sup' (fun i => X i k) (Finset.mem_univ i)
    linarith
  · obtain ⟨i, -, hval⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
      (fun i => X i k)
    have h2 : X i k - (r : ℤ)
        ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => X i k - (r : ℤ)) :=
      Finset.le_sup' (fun i => X i k - (r : ℤ)) (Finset.mem_univ i)
    linarith

/-- The actual array shifted to level `r` and translated in time to `τ_r`. -/
noncomputable def shiftX (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) :
    Fin N → ℕ → ℤ :=
  fun i t => actX p m U i (recTimeA p m U r + t) - (r : ℤ)

theorem shiftX_runMax_eq_one_iff (r n : ℕ) :
    runMax (shiftX p m U r) n = 1 ↔
      runMax (actX p m U) (recTimeA p m U r + n) = ((r + 1 : ℕ) : ℤ) := by
  have h : runMax (shiftX p m U r) n = runMax (actX p m U) (recTimeA p m U r + n) - (r : ℤ) :=
    runMax_sub (fun i t => actX p m U i (recTimeA p m U r + t)) r n
  rw [h, Nat.cast_add, Nat.cast_one]
  constructor <;> intro hc <;> linarith

/-- Length of the actual record block starting at level `r`. -/
noncomputable def blockLen (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) : ℕ :=
  recTimeA p m U (r + 1) - recTimeA p m U r

theorem recTimeA_add_blockLen (hU : U ∈ ReachAll p m) (r : ℕ) :
    recTimeA p m U r + blockLen p m U r = recTimeA p m U (r + 1) :=
  Nat.add_sub_cancel' (recTimeA_le_succ hU r)

theorem blockLen_pos (hU : U ∈ ReachAll p m) (r : ℕ) : 0 < blockLen p m U r := by
  have h := recTimeA_lt_succ hU r
  have h2 := recTimeA_add_blockLen hU r
  omega

/-- The block length is a first hitting time: at `τ_r + blockLen` the shifted array reaches
level `1`. -/
theorem blockLen_spec (hU : U ∈ ReachAll p m) (r : ℕ) :
    runMax (shiftX p m U r) (blockLen p m U r) = 1 := by
  rw [shiftX_runMax_eq_one_iff, recTimeA_add_blockLen hU r]
  exact (isRecord_recTimeA_of_reach hU (r + 1)).2

/-- **The block length is the least hitting time of level `1` for the shifted array**: no
strictly smaller time hits it. -/
theorem blockLen_min (hU : U ∈ ReachAll p m) (r : ℕ) {n : ℕ} (hn : n < blockLen p m U r) :
    runMax (shiftX p m U r) n ≠ 1 := by
  intro hcon
  rw [shiftX_runMax_eq_one_iff] at hcon
  have hlt : recTimeA p m U r + n < recTimeA p m U (r + 1) := by
    have := recTimeA_add_blockLen hU r
    omega
  have hcontra := runMax_lt_of_lt_recTimeA hU hlt
  linarith

/-- **The block length as a `Nat.find`** of the shifted hitting predicate: the usable first-hit
form of `blockLen_spec` + `blockLen_min`. -/
theorem blockLen_eq_find (hU : U ∈ ReachAll p m) (r : ℕ) :
    blockLen p m U r
      = Nat.find (p := fun n => runMax (shiftX p m U r) n = 1)
          ⟨blockLen p m U r, blockLen_spec hU r⟩ := by
  refine Eq.symm ?_
  exact (Nat.find_eq_iff _).2 ⟨blockLen_spec hU r, fun j hj => blockLen_min hU r hj⟩

end RecordSeq

/-! ### Local times at record times -/

section LocalTimes

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

theorem ell_self_pos (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (n : ℕ) (i : Fin N) :
    1 ≤ (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
  rw [ell_eq_localTime p m U n i]
  exact (localTime_pos_iff _ _ _).2 ⟨n, le_rfl, rfl⟩

/-- At the record time `τ_r` no walker has ever visited a site strictly above level `r`. -/
theorem ell_eq_zero_above_level (hU : U ∈ ReachAll p m) (r : ℕ) {y : ℤ} (hy : (r : ℤ) < y)
    (i : Fin N) :
    (trajectory p m U (recTimeA p m U r)).ell i y = 0 := by
  rw [ell_eq_localTime p m U (recTimeA p m U r) i, localTime_eq_zero_iff]
  intro t ht hcon
  by_cases hlt : t < recTimeA p m U r
  · have h1 := (isRecord_recTimeA_of_reach hU r).1 t hlt
    have h2 : (trajectory p m U t).pos i ≤ runMax (actX p m U) t := le_runMax t i
    rw [hcon] at h2
    linarith
  · have heq : t = recTimeA p m U r := by omega
    subst heq
    have h1 : (trajectory p m U (recTimeA p m U r)).pos i ≤ (r : ℤ) := actX_le_level hU r i
    rw [hcon] at h1
    linarith

/-- At the record time `τ_r` the level site has been visited at most once. -/
theorem ell_level_le_one (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    (trajectory p m U (recTimeA p m U r)).ell i (r : ℤ) ≤ 1 := by
  rw [ell_eq_localTime p m U (recTimeA p m U r) i]
  have hsub : (Finset.range (recTimeA p m U r + 1)).filter
        (fun t => actX p m U i t = (r : ℤ)) ⊆ {recTimeA p m U r} := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_singleton]
    by_contra hne
    have hlt : t < recTimeA p m U r := by omega
    have h1 := (isRecord_recTimeA_of_reach hU r).1 t hlt
    have h2 : actX p m U i t ≤ runMax (actX p m U) t := le_runMax t i
    rw [ht.2] at h2
    linarith
  calc localTime (fun k => actX p m U i k) (recTimeA p m U r) (r : ℤ)
      = ((Finset.range (recTimeA p m U r + 1)).filter
          (fun t => actX p m U i t = (r : ℤ))).card := rfl
    _ ≤ ({recTimeA p m U r} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- At `τ_r` the level site has positive local time exactly for the walkers sitting on it. -/
theorem ell_level_pos_iff (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    0 < (trajectory p m U (recTimeA p m U r)).ell i (r : ℤ)
      ↔ actX p m U i (recTimeA p m U r) = (r : ℤ) := by
  rw [ell_eq_localTime p m U (recTimeA p m U r) i, localTime_pos_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    by_cases heq : t = recTimeA p m U r
    · rw [heq] at hx
      exact hx
    · exfalso
      have hlt : t < recTimeA p m U r := by omega
      have h1 := (isRecord_recTimeA_of_reach hU r).1 t hlt
      have h2 : (trajectory p m U t).pos i ≤ runMax (actX p m U) t := le_runMax t i
      rw [hx] at h2
      linarith
  · intro hi
    exact ⟨recTimeA p m U r, le_rfl, hi⟩

/-- The capped local time at the level site, at time `τ_r`, is the indicator of sitting there. -/
theorem cap_ell_level (hU : U ∈ ReachAll p m) (hm : 1 ≤ m) (r : ℕ) (i : Fin N) :
    min ((trajectory p m U (recTimeA p m U r)).ell i (r : ℤ)) m
      = if actX p m U i (recTimeA p m U r) = (r : ℤ) then 1 else 0 := by
  by_cases h : actX p m U i (recTimeA p m U r) = (r : ℤ)
  · rw [if_pos h]
    have hpos := (ell_level_pos_iff hU r i).2 h
    have hle := ell_level_le_one hU r i
    omega
  · rw [if_neg h]
    have h0 : ¬ 0 < (trajectory p m U (recTimeA p m U r)).ell i (r : ℤ) :=
      fun hp => h ((ell_level_pos_iff hU r i).1 hp)
    omega

end LocalTimes

/-! ### Half-distances: `halfDist` inverts an even nonpositive offset -/

theorem halfDist_eq_of_two_mul {z a : ℤ} (h : z = 2 * a) (ha : a ≤ 0) :
    SimJump.Record.halfDist z = (-a).toNat := by
  have h2 : (1 - z) / 2 = -a := by rw [h]; omega
  simp only [SimJump.Record.halfDist, h2]

theorem two_mul_halfDist {z a : ℤ} (h : z = 2 * a) (ha : a ≤ 0) :
    -((2 : ℤ) * ((SimJump.Record.halfDist z : ℕ) : ℤ)) = z := by
  rw [halfDist_eq_of_two_mul h ha]
  have h4 : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
  rw [h4]; omega

theorem halfDist_eq_zero_iff {z a : ℤ} (h : z = 2 * a) (ha : a ≤ 0) :
    SimJump.Record.halfDist z = 0 ↔ z = 0 := by
  rw [halfDist_eq_of_two_mul h ha, Int.toNat_eq_zero]
  constructor <;> intro hh <;> omega


/-! ### Trajectory-shaped restatements at record times -/

section TrajForm

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

theorem traj_le_level (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    (trajectory p m U (recTimeA p m U r)).pos i ≤ (r : ℤ) :=
  actX_le_level hU r i

theorem exists_traj_eq_level (hU : U ∈ ReachAll p m) (r : ℕ) :
    ∃ i : Fin N, (trajectory p m U (recTimeA p m U r)).pos i = (r : ℤ) :=
  exists_actX_eq_level hU r

theorem traj_sub_level_two_mul (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    ∃ a : ℤ, (trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ) = 2 * a :=
  actX_sub_level_two_mul hU r i

theorem ell_level_iff_traj (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    (0 < (trajectory p m U (recTimeA p m U r)).ell i (r : ℤ))
      ↔ (trajectory p m U (recTimeA p m U r)).pos i = (r : ℤ) :=
  ell_level_pos_iff hU r i

theorem cap_ell_level' (hU : U ∈ ReachAll p m) (hm : 1 ≤ m) (r : ℕ) (i : Fin N) :
    min ((trajectory p m U (recTimeA p m U r)).ell i (r : ℤ)) m
      = if (trajectory p m U (recTimeA p m U r)).pos i = (r : ℤ) then 1 else 0 :=
  cap_ell_level hU hm r i

end TrajForm

/-! ### The actual compact record state -/

section CompactState

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- The record-start state of the actual array at level `r`: positions down by `r`, capped
local-time index up by `r`. -/
noncomputable def transRecordState (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) :
    SimJump.State N m :=
  trans r (capState m (trajectory p m U (recTimeA p m U r)))

/-- The capped local times of the translated actual state, as `Fin (m+1)`-valued data. -/
noncomputable def transEta (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) :
    Fin N → ℤ → Fin (m + 1) :=
  fun i x => ⟨(transRecordState p m U r).eta i x,
    Nat.lt_succ_of_le ((transRecordState p m U r).hcap i x)⟩

theorem transEta_val (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ)
    (i : Fin N) (x : ℤ) :
    (transEta p m U r i x).val = (transRecordState p m U r).eta i x := rfl

theorem transEta_eq (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ)
    (i : Fin N) (x : ℤ) :
    (transEta p m U r i x).val
      = min ((trajectory p m U (recTimeA p m U r)).ell i (x + (r : ℤ))) m := by
  rw [transEta_val]
  simp only [transRecordState, trans_eta, capState_eta]

/-- **The translated actual state at a record time is a record-start state.** -/
theorem recordStart_transRecordState (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    Record.RecordStart (transRecordState p m U r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := traj_le_level hU r i
    simp only [transRecordState, trans_pos, capState_pos]
    linarith
  · obtain ⟨i, hi⟩ := exists_traj_eq_level hU r
    refine ⟨i, ?_⟩
    simp only [transRecordState, trans_pos, capState_pos]
    rw [hi]; ring
  · intro i
    obtain ⟨a, ha⟩ := traj_sub_level_two_mul hU r i
    refine ⟨a, ?_⟩
    simp only [transRecordState, trans_pos, capState_pos]
    linarith
  · intro i
    simp only [transRecordState, trans_pos, capState_pos, trans_eta, capState_eta]
    rw [sub_add_cancel]
    exact le_min (ell_self_pos p m U _ i) hm
  · intro i x hx
    simp only [transRecordState, trans_eta, capState_eta]
    have hxr : (r : ℤ) < x + (r : ℤ) := by linarith
    rw [ell_eq_zero_above_level hU r hxr i]
    exact min_eq_left (Nat.zero_le m)
  · intro i
    have hpos_eq : (transRecordState p m U r).pos i = 0
        ↔ (trajectory p m U (recTimeA p m U r)).pos i = (r : ℤ) := by
      simp only [transRecordState, trans_pos, capState_pos]
      constructor <;> intro h <;> omega
    have heta_eq : (transRecordState p m U r).eta i 0
        = min ((trajectory p m U (recTimeA p m U r)).ell i (r : ℤ)) m := by
      simp only [transRecordState, trans_eta, capState_eta]
      rw [show (0 : ℤ) + (r : ℤ) = (r : ℤ) from zero_add (r : ℤ)]
    rw [heta_eq, cap_ell_level' hU hm r i]
    by_cases h : (transRecordState p m U r).pos i = 0
    · rw [if_pos h, if_pos (hpos_eq.1 h)]
    · rw [if_neg h, if_neg (fun hc => h (hpos_eq.2 hc))]

/-- The ambient record-state pair of the actual array at level `r`. -/
noncomputable def actRecAmb (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) :
    Amb N m :=
  (fun i => SimJump.Record.halfDist ((trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ)),
    transEta p m U r)

theorem transEta_eq_fin (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ)
    (i : Fin N) (x : ℤ) :
    transEta p m U r i x
      = ⟨min ((trajectory p m U (recTimeA p m U r)).ell i (x + (r : ℤ))) m,
          Nat.lt_succ_of_le (min_le_right _ m)⟩ := by
  refine Fin.ext ?_
  rw [transEta_eq]

/-- **The actual record pair is an admissible compact record state.** -/
theorem actRecAmb_mem (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    actRecAmb p m U r ∈ recSet N m := by
  obtain ⟨i₀, hi₀⟩ := exists_traj_eq_level hU r
  refine ⟨⟨i₀, ?_⟩, ?_, ?_, ?_⟩
  · simp only [actRecAmb, hi₀]
    simp [SimJump.Record.halfDist]
  · intro i x hx
    simp only [actRecAmb]
    rw [transEta_eq_fin]
    refine Fin.ext ?_
    have hxr : (r : ℤ) < x + (r : ℤ) := by linarith
    simp [ell_eq_zero_above_level hU r hxr i]
  · intro i
    obtain ⟨a, ha⟩ := traj_sub_level_two_mul hU r i
    have ha' : a ≤ 0 := by
      have hle := traj_le_level hU r i
      linarith
    have h1 : -((2 : ℤ) * ((SimJump.Record.halfDist
        ((trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ)) : ℕ) : ℤ))
        = (trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ) := two_mul_halfDist ha ha'
    simp only [actRecAmb]
    rw [transEta_eq_fin, Fin.le_def, one_val hm, h1, sub_add_cancel]
    exact le_min (ell_self_pos p m U _ i) hm
  · intro i
    obtain ⟨a, ha⟩ := traj_sub_level_two_mul hU r i
    have ha' : a ≤ 0 := by
      have hle := traj_le_level hU r i
      linarith
    have hiff : (actRecAmb p m U r).1 i = 0
        ↔ (trajectory p m U (recTimeA p m U r)).pos i = (r : ℤ) := by
      have hhalf : (actRecAmb p m U r).1 i
          = SimJump.Record.halfDist ((trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ)) := rfl
      rw [hhalf, halfDist_eq_zero_iff ha ha']
      constructor <;> intro h <;> omega
    have h2 : (actRecAmb p m U r).2 i 0 = transEta p m U r i 0 := rfl
    rw [h2]
    by_cases h : (actRecAmb p m U r).1 i = 0
    · rw [if_pos h]
      refine Fin.ext ?_
      rw [transEta_eq, show (0 : ℤ) + (r : ℤ) = (r : ℤ) from zero_add (r : ℤ),
        cap_ell_level' hU hm r i, if_pos (hiff.1 h), one_val hm]
    · rw [if_neg h]
      refine Fin.ext ?_
      rw [transEta_eq, show (0 : ℤ) + (r : ℤ) = (r : ℤ) from zero_add (r : ℤ),
        cap_ell_level' hU hm r i, if_neg (fun hc => h (hiff.2 hc))]
      rfl

/-- **The actual compact record state at level `r`.** -/
noncomputable def actRecState (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (hm : 1 ≤ m)
    (hU : U ∈ ReachAll p m) (r : ℕ) : RecState N m :=
  ⟨actRecAmb p m U r, actRecAmb_mem hm hU r⟩

/-- **Expanding the actual compact record state gives the actual capped state at `τ_r` in
record coordinates.** -/
theorem ofRecState_actRecState (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    Record.ofRecState (actRecState p m U hm hU r) = transRecordState p m U r := by
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    obtain ⟨a, ha⟩ := traj_sub_level_two_mul hU r i
    have ha' : a ≤ 0 := by
      have hle := traj_le_level hU r i
      linarith
    show -((2 : ℤ) * ((actRecAmb p m U r).1 i : ℤ)) = (transRecordState p m U r).pos i
    simp only [actRecAmb]
    rw [two_mul_halfDist ha ha']
    simp only [transRecordState, trans_pos, capState_pos]
  · funext i x
    rfl

end CompactState

/-! ### The actual jump word of a record block -/

section Block

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- The actual jump word the array takes during the record block from `τ_r` to `τ_{r+1}`. -/
noncomputable def blockWord (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ) :
    Fin (blockLen p m U r) → JumpVec N :=
  fun t => nextJumpVec p m U (recTimeA p m U r + (t : ℕ))

theorem extendPath_blockWord_apply (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (r : ℕ)
    {t : ℕ} (ht : t < blockLen p m U r) :
    Record.extendPath (blockWord p m U r) t = nextJumpVec p m U (recTimeA p m U r + t) := by
  simp only [Record.extendPath, ht, dif_pos]
  rfl

/-- `currentRecordState` is the capped state of the actual trajectory. -/
theorem currentRecordState_eq_capState (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N)
    (n : ℕ) :
    currentRecordState p m U n = capState m (trajectory p m U n) := rfl

/-- The capped record state of the actual array evolves along its own jump word. -/
theorem evolveFun_currentRecordState (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N)
    (n L : ℕ) :
    SimJump.evolveFun (fun t => nextJumpVec p m U (n + t)) L (currentRecordState p m U n)
      = currentRecordState p m U (n + L) := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [SimJump.evolveFun_succ, ih, show n + (L + 1) = n + L + 1 from by omega]
      exact step_currentRecordState p m U (n + L)

/-- **The block evolution of the translated actual state.**  Following the actual jump word of
the block `r` for its whole length transports the actual capped state from `τ_r` to
`τ_{r+1}`, in record coordinates. -/
theorem evolveFun_extendPath_blockWord (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    Record.normalize (SimJump.evolveFun (Record.extendPath (blockWord p m U r))
        (blockLen p m U r) (transRecordState p m U r))
      = transRecordState p m U (r + 1) := by
  rw [← trans_one_eq_normalize]
  simp only [transRecordState]
  rw [evolveFun_trans, trans_add, show 1 + r = r + 1 from by omega]
  congr 1
  rw [← recTimeA_add_blockLen hU r,
    ← currentRecordState_eq_capState, ← currentRecordState_eq_capState,
    ← evolveFun_currentRecordState p m U (recTimeA p m U r) (blockLen p m U r)]
  exact M5FirstBlock.evolveFun_congr
    (fun t ht => extendPath_blockWord_apply p m U r ht) _

/-- The intermediate form of the block evolution, at any prefix of the block. -/
theorem evolveFun_extendPath_blockWord_le (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ)
    {L : ℕ} (hL : L ≤ blockLen p m U r) :
    SimJump.evolveFun (Record.extendPath (blockWord p m U r)) L
        (Record.ofRecState (actRecState p m U hm hU r))
      = trans r (capState m (trajectory p m U (recTimeA p m U r + L))) := by
  rw [ofRecState_actRecState]
  simp only [transRecordState]
  rw [evolveFun_trans]
  congr 1
  rw [← currentRecordState_eq_capState, ← currentRecordState_eq_capState,
    ← evolveFun_currentRecordState p m U (recTimeA p m U r) L]
  exact M5FirstBlock.evolveFun_congr
    (fun t ht => extendPath_blockWord_apply p m U r (lt_of_lt_of_le ht hL)) _

/-- **The actual block word is a first-record path from the actual compact record state.** -/
theorem firstRecord_blockWord (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    Record.FirstRecord (Record.extendPath (blockWord p m U r)) (blockLen p m U r)
      (Record.ofRecState (actRecState p m U hm hU r)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := exists_actX_eq_level hU (r + 1)
    refine ⟨i, ?_⟩
    rw [evolveFun_extendPath_blockWord_le hm hU r le_rfl, recTimeA_add_blockLen hU r]
    simp only [trans_pos, capState_pos]
    have hi' : (trajectory p m U (recTimeA p m U (r + 1))).pos i = ((r + 1 : ℕ) : ℤ) := hi
    rw [hi']
    push_cast
    ring
  · intro t ht i
    have hlt : recTimeA p m U r + t < recTimeA p m U (r + 1) := by
      have := recTimeA_add_blockLen hU r
      omega
    have hle : (trajectory p m U (recTimeA p m U r + t)).pos i
        ≤ runMax (actX p m U) (recTimeA p m U r + t) := le_runMax _ _
    have hrm := runMax_lt_of_lt_recTimeA hU hlt
    have hcast : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
    rw [evolveFun_extendPath_blockWord_le hm hU r (le_of_lt ht)]
    simp only [trans_pos, capState_pos]
    linarith

end Block

/-! ### Injectivity of the compact-state expansion -/

theorem ofRecState_injective {m : ℕ} :
    Function.Injective (Record.ofRecState (N := N) (m := m)) := by
  intro y₁ y₂ h
  have hpos : y₁.val.1 = y₂.val.1 := by
    funext i
    have h1 := congrArg (fun s => s.pos i) h
    simp only [Record.ofRecState] at h1
    have h2 : ((y₁.val.1 i : ℕ) : ℤ) = ((y₂.val.1 i : ℕ) : ℤ) := by omega
    exact_mod_cast h2
  have heta : y₁.val.2 = y₂.val.2 := by
    funext i x
    have h1 := congrArg (fun s => s.eta i x) h
    simp only [Record.ofRecState] at h1
    exact Fin.ext h1
  exact Subtype.ext (Prod.ext hpos heta)

/-! ### The k-level recursion -/

section Recursion

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- **The successor recursion of the actual compact record states.**  The compact record state at
level `r + 1` is exactly the stopped-record output of the actual block word applied to the compact
record state at level `r`. -/
theorem actRecState_succ (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    actRecState p m U hm hU (r + 1)
      = SimJump.RecKernel.out hm (blockWord p m U r) (actRecState p m U hm hU r) := by
  refine ofRecState_injective ?_
  rw [M5FirstBlock.ofRecState_out hm (blockWord p m U r) (actRecState p m U hm hU r)
    (firstRecord_blockWord hm hU r), ofRecState_actRecState, ofRecState_actRecState]
  exact (evolveFun_extendPath_blockWord hm hU r).symm

/-- The compact record state at level `0` is the all-at-the-record state. -/
theorem actRecState_zero (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) :
    actRecState p m U hm hU 0 = SwarmRecordMeas.StartLaw.zeroState hm := by
  refine ofRecState_injective ?_
  rw [ofRecState_actRecState, ofRecState_zeroState m hm]
  simp only [transRecordState]
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    rw [trans_zero, recTimeA_zero]
    rfl
  · funext i x
    rw [trans_zero, recTimeA_zero]
    rfl

/-- The nested stopped-record output: the `r`-fold iterate of the one-step map `out` along the
actual block words, started from the all-at-the-record state. -/
noncomputable def nestOut (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (hm : 1 ≤ m) :
    ℕ → RecState N m
  | 0 => SwarmRecordMeas.StartLaw.zeroState hm
  | r + 1 => SimJump.RecKernel.out hm (blockWord p m U r) (nestOut p m U hm r)

/-- **The actual compact record state at level `r` is the `r`-fold nested stopped-record
output.** -/
theorem actRecState_eq_nestOut (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    actRecState p m U hm hU r = nestOut p m U hm r := by
  induction r with
  | zero => exact actRecState_zero hm hU
  | succ r ih =>
      rw [actRecState_succ hm hU r, ih]
      rfl

end Recursion

/-! ### Cumulative record times -/

section Cumulative

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- **The record time is the sum of the block lengths**: `τ_r = ∑_{j<r} (τ_{j+1} - τ_j)`. -/
theorem recTimeA_eq_sum_blockLen (hU : U ∈ ReachAll p m) (r : ℕ) :
    recTimeA p m U r = ∑ j ∈ Finset.range r, blockLen p m U j := by
  induction r with
  | zero => simp [recTimeA_zero]
  | succ r ih =>
      rw [Finset.sum_range_succ, ← ih, ← recTimeA_add_blockLen hU r]

end Cumulative

/-! ### Measurability of the actual record state -/

section MeasurableRecState

variable {p : ℝ} {m : ℕ}

/-- The actual position at the random record time `τ_r` is measurable. -/
theorem measurable_traj_pos_at_recTime (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) :
    Measurable fun U : Swarming.Uniform.Array N =>
      (trajectory p m U (recTimeA p m U r)).pos i :=
  SwarmRecordMeas.measurable_comp_nat (measurable_recTimeA p m r)
    (g := fun k U => (trajectory p m U k).pos i)
    (fun k => (Swarming.Fair.measurable_trajectory (N := N) p m k).1 i)

/-- The half-distance coordinate of the actual compact record state is measurable. -/
theorem measurable_actRecAmb_fst (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) :
    Measurable fun U : Swarming.Uniform.Array N => (actRecAmb p m U r).1 i := by
  have hf : Measurable fun U : Swarming.Uniform.Array N =>
      (trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ) :=
    (measurable_traj_pos_at_recTime p m r i).sub measurable_const
  have h : (fun U : Swarming.Uniform.Array N => (actRecAmb p m U r).1 i)
      = fun U => SimJump.Record.halfDist
          ((trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ)) := rfl
  rw [h]
  exact (measurable_of_countable (fun z : ℤ => SimJump.Record.halfDist z)).comp hf

theorem measurable_transEta_val (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (x : ℤ) :
    Measurable fun U : Swarming.Uniform.Array N => ((actRecAmb p m U r).2 i x).val := by
  have h : (fun U : Swarming.Uniform.Array N => ((actRecAmb p m U r).2 i x).val)
      = fun U => min ((trajectory p m U (recTimeA p m U r)).ell i (x + (r : ℤ))) m := by
    funext U
    exact transEta_eq p m U r i x
  rw [h]
  exact (SwarmRecordMeas.measurable_comp_nat (measurable_recTimeA p m r)
    (g := fun k U => (trajectory p m U k).ell i (x + (r : ℤ)))
    (fun k => (Swarming.Fair.measurable_trajectory (N := N) p m k).2 i _)).min measurable_const

/-- A component of the capped local-time coordinate is measurable. -/
theorem measurable_actRecAmb_snd (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (x : ℤ) :
    Measurable fun U : Swarming.Uniform.Array N => (actRecAmb p m U r).2 i x := by
  refine measurable_to_countable (fun y => ?_)
  have hval := measurable_transEta_val p m r i x
  have hset : (fun U : Swarming.Uniform.Array N => (actRecAmb p m U r).2 i x) ⁻¹'
        {(actRecAmb p m y r).2 i x}
      = ((fun U : Swarming.Uniform.Array N => ((actRecAmb p m U r).2 i x).val) ⁻¹'
          {((actRecAmb p m y r).2 i x).val}) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  rw [hset]
  exact hval (measurableSet_singleton _)

/-- **The actual compact record state is a measurable function of the array.** -/
theorem measurable_actRecAmb (p : ℝ) (m : ℕ) (r : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => actRecAmb p m U r := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.2 fun i => measurable_actRecAmb_fst p m r i
  · exact measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun x =>
      measurable_actRecAmb_snd p m r i x

/-- **The whole actual compact record-state sequence is measurable in the array.** -/
theorem measurable_actRecSeq (p : ℝ) (m : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => fun r : ℕ => actRecAmb p m U r :=
  measurable_pi_iff.2 fun r => measurable_actRecAmb p m r

end MeasurableRecState

/-! ### The paper's defect `d_r` is twice the `dmax` of the compact record state -/

section DefectBridge

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- `halfDist` is antitone on the nonpositive integers. -/
theorem halfDist_antitone {z z' : ℤ} (h : z ≤ z') (hz' : z' ≤ 0) :
    SimJump.Record.halfDist z' ≤ SimJump.Record.halfDist z := by
  have h1 : (1 - z') / 2 ≤ (1 - z) / 2 := by
    apply Int.ediv_le_ediv (by norm_num : (0 : ℤ) < 2)
    omega
  simp only [SimJump.Record.halfDist]
  exact Int.toNat_le_toNat h1

theorem actRecAmb_fst_le_halfDist_runMin (hU : U ∈ ReachAll p m) (r : ℕ) (i : Fin N) :
    (actRecAmb p m U r).1 i
      ≤ SimJump.Record.halfDist (runMin (actX p m U) (recTimeA p m U r) - (r : ℤ)) := by
  have hbase : runMin (actX p m U) (recTimeA p m U r)
      ≤ (trajectory p m U (recTimeA p m U r)).pos i :=
    runMin_le (X := actX p m U) (recTimeA p m U r) i
  have hle : runMin (actX p m U) (recTimeA p m U r) - (r : ℤ)
      ≤ (trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ) := by
    linarith
  have hz : (trajectory p m U (recTimeA p m U r)).pos i - (r : ℤ) ≤ 0 := by
    have h := traj_le_level hU r i
    linarith
  exact halfDist_antitone hle hz

theorem exists_actRecAmb_fst_eq_halfDist_runMin (hU : U ∈ ReachAll p m) (r : ℕ) :
    ∃ j : Fin N, (actRecAmb p m U r).1 j
      = SimJump.Record.halfDist (runMin (actX p m U) (recTimeA p m U r) - (r : ℤ)) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun i => actX p m U i (recTimeA p m U r))
  refine ⟨j, ?_⟩
  have hpos : (trajectory p m U (recTimeA p m U r)).pos j
      = runMin (actX p m U) (recTimeA p m U r) := hj.symm
  show SimJump.Record.halfDist ((trajectory p m U (recTimeA p m U r)).pos j - (r : ℤ)) = _
  rw [hpos]

/-- **`dmax` of the actual compact record state** is the half-distance of the lowest walker at
`τ_r`. -/
theorem dmax_actRecState (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    SimJump.RecKernel.dmax (actRecState p m U hm hU r)
      = SimJump.Record.halfDist (runMin (actX p m U) (recTimeA p m U r) - (r : ℤ)) := by
  unfold SimJump.RecKernel.dmax SwarmRec.dist2
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun i _ => ?_)
    exact actRecAmb_fst_le_halfDist_runMin hU r i
  · obtain ⟨j, hj⟩ := exists_actRecAmb_fst_eq_halfDist_runMin hU r
    calc SimJump.Record.halfDist (runMin (actX p m U) (recTimeA p m U r) - (r : ℤ))
        = (actRecAmb p m U r).1 j := hj.symm
      _ ≤ Finset.univ.sup (fun i => (actRecAmb p m U r).1 i) :=
          Finset.le_sup (Finset.mem_univ j)

/-- **Source fidelity: the paper's defect `d_r = r - min_i X_{τ_r}^i` is twice the `dmax`
coordinate of the actual compact record state.** -/
theorem defect_eq_two_mul_dmax (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    defect (actX p m U) (recTimeA p m U) r
      = 2 * ((SimJump.RecKernel.dmax (actRecState p m U hm hU r) : ℕ) : ℤ) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun i => actX p m U i (recTimeA p m U r))
  obtain ⟨a, ha⟩ := traj_sub_level_two_mul hU r j
  have hm0 : runMin (actX p m U) (recTimeA p m U r)
      = (trajectory p m U (recTimeA p m U r)).pos j := hj
  have ha' : a ≤ 0 := by
    have hle : (trajectory p m U (recTimeA p m U r)).pos j ≤ (r : ℤ) := traj_le_level hU r j
    linarith
  have hdef : defect (actX p m U) (recTimeA p m U) r
      = (r : ℤ) - (trajectory p m U (recTimeA p m U r)).pos j := by
    rw [defect, hm0]
  rw [hdef, dmax_actRecState hm hU r, hm0]
  have h2 := two_mul_halfDist ha ha'
  linarith

end DefectBridge

/-! ### The block-start state, its weights, and measurability of the block length -/

section BlockStart

variable {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N}

/-- The expansion of the actual compact record state is a record-start state. -/
theorem recordStart_ofRecState_actRecState (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ) :
    Record.RecordStart (Record.ofRecState (actRecState p m U hm hU r)) := by
  rw [ofRecState_actRecState]
  exact recordStart_transRecordState hm hU r

/-- The weight of any prescribed continuation depends on the actual array at `τ_r` only through
the actual compact record state: `pathW` from `ofRecState (actRecState r)` is `pathW` from the
translated actual state. -/
theorem pathW_ofRecState_actRecState (hm : 1 ≤ m) (hU : U ∈ ReachAll p m) (r : ℕ)
    {k : ℕ} (q : Fin k → JumpVec N) :
    SimJump.pathW p k q (Record.ofRecState (actRecState p m U hm hU r))
      = SimJump.pathW p k q (transRecordState p m U r) := by
  rw [ofRecState_actRecState]

/-- The block length is measurable in the array. -/
theorem measurable_blockLen (p : ℝ) (m : ℕ) (r : ℕ) :
    Measurable fun U : Swarming.Uniform.Array N => blockLen p m U r :=
  (measurable_recTimeA p m (r + 1)).sub (measurable_recTimeA p m r)

/-- The event that the level-`r` block has a prescribed length is measurable. -/
theorem measurableSet_blockLen_eq (p : ℝ) (m : ℕ) (r L : ℕ) :
    MeasurableSet {U : Swarming.Uniform.Array N | blockLen p m U r = L} :=
  measurable_blockLen p m r (measurableSet_singleton L)

end BlockStart

/-! ### `ReachAll` holds almost surely for the actual array

This is the capstone that makes every statement above apply on a set of full measure: the record
geometry is stated with the explicit hypothesis `U ∈ ReachAll p m`, and that event carries the
actual array measure for `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`. -/

section AlmostSure

variable {p : ℝ} {m : ℕ}

/-- **`ReachAll` is almost sure** for the actual uniform array. -/
theorem ae_reachAll (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), U ∈ ReachAll p m := by
  filter_upwards [ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN] with U hU r
  exact ⟨recTimeA p m U r, (hU r).2⟩

/-- The almost-sure form of the record geometry: for almost every array, `ReachAll` holds, so the
successor recursion `actRecState_succ`, the first-record characterisation
`firstRecord_blockWord`, the defect bridge `defect_eq_two_mul_dmax` and the cumulative-time
identity all apply at every level. -/
theorem ae_geometry (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ r : ℕ,
      (recTimeA p m U r < recTimeA p m U (r + 1)) ∧
      (recTimeA p m U r = ∑ j ∈ Finset.range r, blockLen p m U j) := by
  filter_upwards [ae_reachAll (N := N) hp0 hp1 hm hN] with U hU r
  exact ⟨recTimeA_lt_succ hU r, recTimeA_eq_sum_blockLen hU r⟩

end AlmostSure

end M4RecordGeom
