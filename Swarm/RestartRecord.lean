/-
# Restart at a simultaneous record: the translated-segment law

The paper's regeneration argument (`main_1d_revised.tex`, proof of Proposition
`regen`, equations `(firstblk)` and `(freshlaw)`) needs the following fact.

*At a simultaneous record time `τ_d = t` with `X_t^i = d` for every walker, all local times at
level `d` equal `1` and all local times at levels strictly above `d` equal `0`.  The first
departure from `d` therefore has the same transition probabilities as the first departure from
`0`, and until a return to `d` or below the transition rules depend only on the translated
positions and on the local times at sites strictly above `d`.  With the same driving uniforms
this gives identical translated paths.*

This file proves that statement for the actual recursive model `Swarming.Trajectory.trajectory`
driven by the actual i.i.d. array `Swarming.Uniform.Array`, in exact form:

* `ell_at_simultaneous_record` — the canonical local-time profile at a record;
* `restart_agreement` — **the translated-segment theorem**: as long as no walker goes below the
  record level, the state of the actual trajectory after the record agrees, site by site and
  local time by local time, with the state of a *fresh* trajectory started at `0` and driven by
  the *level-shifted* array.  The record's local times below the level never matter;
* `measurePreserving_levelShift` — the level shift is measure preserving for `arrayMeasure N`,
  because the array law is an infinite product of one and the same uniform law;
* `restart_law` — hence the law of the segment after a record is the law of the fresh model.

Everything here is deterministic coupling, exactly as in the paper.  What is *not* claimed is the
independence half of `(freshlaw)` (that the coordinates above the record are independent of the
past `F_t`): that is the separate finite-cylinder factorisation statement described at the end.
-/
import Swarm.Trajectory
import Swarm.MeasurableInc

namespace SwarmRestart

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The level-shifted array and the iterated recursion -/

/-- The array with every lattice level shifted by `d`: coordinate `(i, x, k)` of the shifted
array is coordinate `(i, x + d, k)` of the original one.  The departure number `k` is not
shifted, so the shift is a bijection of the coordinate set. -/
def levelShift (d : ℤ) (U : Array N) : Array N :=
  fun c => U (c.1, c.2.1 + d, c.2.2)

@[simp] lemma levelShift_apply (d : ℤ) (U : Array N) (i : Fin N) (x : ℤ) (k : ℕ) :
    levelShift d U (i, x, k) = U (i, x + d, k) := rfl

/-- The state after `n` further steps of the actual one-step recursion, starting from `s`. -/
noncomputable def trajFrom (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ) :
    WalkState N :=
  (nextWalkState p m U)^[n] s

@[simp] lemma trajFrom_zero (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) :
    trajFrom p m U s 0 = s := rfl

lemma trajFrom_succ (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ) :
    trajFrom p m U s (n + 1) = nextWalkState p m U (trajFrom p m U s n) :=
  Function.iterate_succ_apply' _ _ _

lemma trajFrom_add (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (a b : ℕ) :
    trajFrom p m U s (a + b) = trajFrom p m U (trajFrom p m U s a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, trajFrom_succ, ih, trajFrom_succ]

/-- The recursive `trajectory` is the iteration of the one-step map from the initial state. -/
theorem trajectory_eq_trajFrom (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    trajectory p m U n = trajFrom p m U initialWalkState n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory_succ, ih, trajFrom_succ]

/-! ### The translation comparison on states -/

/-- `ShiftAgree d s s'` says that `s` is the state `s'` translated up by the level `d`, at every
site at or above `d` (`0` in primed coordinates).  Sites strictly below `d` are unconstrained:
at a record they are the junk local times that the future never reads. -/
def ShiftAgree (d : ℤ) (s s' : WalkState N) : Prop :=
  (∀ i, s.pos i = d + s'.pos i) ∧
    ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i (d + x) = s'.ell i x

lemma otherVisits_shift {d : ℤ} {ell ell' : LocalTimes N}
    (h : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → ell i (d + x) = ell' i x)
    (i : Fin N) {x : ℤ} (hx : 0 ≤ x) :
    otherVisits ell i (d + x) = otherVisits ell' i x := by
  unfold otherVisits
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, if_false]
    exact h j x hx

/-- **The one-step translation lemma.**  Two states that agree above the level `d`, with the
translated state at or above `d`, make the same jump — the same driving coordinate, the same
right probability — and their successors agree above `d` again. -/
theorem nextWalkState_shiftAgree {p : ℝ} {m : ℕ} {U : Array N} {d : ℤ} {s s' : WalkState N}
    (h : ShiftAgree d s s') (hge : ∀ i, d ≤ s.pos i) :
    ShiftAgree d (nextWalkState p m U s) (nextWalkState p m (levelShift d U) s') := by
  obtain ⟨hpos, hell⟩ := h
  have hnn : ∀ i, 0 ≤ s'.pos i := by
    intro i
    have h1 := hpos i
    have h2 := hge i
    omega
  have hexc : ∀ i, Excited m s.ell i (s.pos i) ↔ Excited m s'.ell i (s'.pos i) := by
    intro i
    have hx := hnn i
    have hp := hpos i
    unfold Excited
    rw [hp] at *
    rw [otherVisits_shift hell i hx]
  have hrp : ∀ i, rightProbability p m s.ell i (s.pos i)
      = rightProbability p m s'.ell i (s'.pos i) := by
    intro i
    unfold rightProbability
    by_cases hE : Excited m s'.ell i (s'.pos i)
    · rw [if_pos ((hexc i).mpr hE), if_pos hE]
    · rw [if_neg (fun hh => hE ((hexc i).mp hh)), if_neg hE]
  have hjump : ∀ i, nextPos p m U s i = d + nextPos p m (levelShift d U) s' i := by
    intro i
    have hx := hnn i
    have hp := hpos i
    have hcoord : U (i, s.pos i, s.ell i (s.pos i))
        = levelShift d U (i, s'.pos i, s'.ell i (s'.pos i)) := by
      rw [levelShift_apply, hp, hell i (s'.pos i) hx, add_comm (s'.pos i) d]
    rw [nextPos, nextPos, hcoord, hrp i, hp]
    omega
  constructor
  · intro i
    exact hjump i
  · intro i x hx
    rw [nextWalkState_ell, nextWalkState_ell, hell i x hx, hjump i]
    by_cases hxy : x = nextPos p m (levelShift d U) s' i
    · have hdx : d + x = d + nextPos p m (levelShift d U) s' i := by rw [hxy]
      rw [if_pos hdx, if_pos hxy]
    · have hdx : ¬ (d + x = d + nextPos p m (levelShift d U) s' i) := by
        intro hh
        exact hxy (by omega)
      rw [if_neg hdx, if_neg hxy]

/-- `trajectory p m U (t + n)` is the `n`-step state started from the state at time `t`. -/
theorem trajectory_add (p : ℝ) (m : ℕ) (U : Array N) (t n : ℕ) :
    trajectory p m U (t + n) = trajFrom p m U (trajectory p m U t) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, trajectory_succ, ih, trajFrom_succ]

/-- **The translated-segment theorem, state form.**  Start from two states that agree above the
level `d`, the first one at or above `d`.  As long as the first trajectory stays at or above
`d`, the two trajectories agree above `d`. -/
theorem restart_agreement_aux (p : ℝ) (m : ℕ) (U : Array N) {d : ℤ} {s s' : WalkState N}
    (h : ShiftAgree d s s')
    (hstay : ∀ k, ∀ i, d ≤ (trajFrom p m U s k).pos i) :
    ∀ n, ShiftAgree d (trajFrom p m U s n) (trajFrom p m (levelShift d U) s' n) := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [trajFrom_succ, trajFrom_succ]
      exact nextWalkState_shiftAgree ih (hstay n)

/-- **The canonical local-time profile at a simultaneous record.**  If no walker has reached
level `d` before time `t` and every walker is at `d` at time `t`, then at time `t` every walker
has local time exactly `1` at `d` and local time `0` at every level strictly above `d`. -/
theorem ell_at_simultaneous_record (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d) :
    (∀ i, (trajectory p m U t).ell i d = 1) ∧
      (∀ i, ∀ x : ℤ, d < x → (trajectory p m U t).ell i x = 0) := by
  have hpath : ∀ (i : Fin N) (x : ℤ), (trajectory p m U t).ell i x
      = ((Finset.range (t + 1)).filter fun k => (trajectory p m U k).pos i = x).card := by
    intro i x
    rw [ell_eq_localTime]
    rfl
  constructor
  · intro i
    rw [hpath, Finset.card_eq_one]
    refine ⟨t, ?_⟩
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hkd⟩
      by_contra hne
      have hkt : k < t := by omega
      have hb := hbefore k hkt i
      omega
    · intro hkt
      subst k
      exact ⟨Nat.lt_succ_self t, hat i⟩
  · intro i x hx
    rw [hpath, Finset.card_eq_zero]
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro k hk hkx
    rw [Finset.mem_range] at hk
    rcases Nat.lt_or_ge k t with h | h
    · have hb := hbefore k h i
      omega
    · have hke : k = t := by omega
      rw [hke, hat i] at hkx
      omega

/-- The state at a simultaneous record is the canonical state, translated up by the level. -/
theorem shiftAgree_record (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d) :
    ShiftAgree d (trajectory p m U t) initialWalkState := by
  obtain ⟨h1, h0⟩ := ell_at_simultaneous_record p m U hbefore hat
  constructor
  · intro i
    rw [hat i]
    simp [initialWalkState]
  · intro i x hx
    have hell : (trajectory p m U t).ell i (d + x)
        = (initialWalkState : WalkState N).ell i x := by
      by_cases hx0 : x = 0
      · subst hx0
        have h1i := h1 i
        have : (initialWalkState : WalkState N).ell i (0 : ℤ) = 1 := by simp [initialWalkState]
        rw [add_zero, h1i, this]
      · have hd : d < d + x := by omega
        have h0i := h0 i (d + x) hd
        have hz : (initialWalkState : WalkState N).ell i x = 0 := by
          simp [initialWalkState, hx0]
        rw [h0i, hz]
    exact hell

/-- **The translated-segment theorem.**  If the actual trajectory has a simultaneous record at
time `t` at level `d` — nobody is at level `d` or above before `t`, and everybody is at `d` at
`t` — and afterwards no walker ever goes below `d`, then for every `n` the state at time `t + n`
is the state of the *fresh* model started at `0` and driven by the level-shifted array,
translated up by `d`, at every site at or above `d` and with the same local times there. -/
theorem restart_agreement (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d)
    (hstay : ∀ n, ∀ i, d ≤ (trajectory p m U (t + n)).pos i) :
    ∀ n, ShiftAgree d (trajectory p m U (t + n)) (trajectory p m (levelShift d U) n) := by
  intro n
  have hstay' : ∀ k, ∀ i, d ≤ (trajFrom p m U (trajectory p m U t) k).pos i := by
    intro k i
    have h := hstay k i
    rwa [trajectory_add] at h
  have key := restart_agreement_aux p m U (d := d)
    (shiftAgree_record p m U hbefore hat) hstay' n
  rwa [← trajectory_add, ← trajectory_eq_trajFrom] at key

/-- Position form of the translated-segment theorem. -/
theorem restart_pos (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d)
    (hstay : ∀ n, ∀ i, d ≤ (trajectory p m U (t + n)).pos i) (n : ℕ) (i : Fin N) :
    (trajectory p m U (t + n)).pos i = d + (trajectory p m (levelShift d U) n).pos i :=
  (restart_agreement p m U hbefore hat hstay n).1 i

/-- Local-time form of the translated-segment theorem. -/
theorem restart_ell (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (hbefore : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d)
    (hat : ∀ i, (trajectory p m U t).pos i = d)
    (hstay : ∀ n, ∀ i, d ≤ (trajectory p m U (t + n)).pos i) (n : ℕ) (i : Fin N)
    (x : ℤ) (hx : 0 ≤ x) :
    (trajectory p m U (t + n)).ell i (d + x) = (trajectory p m (levelShift d U) n).ell i x :=
  (restart_agreement p m U hbefore hat hstay n).2 i x hx

/-! ### The past depends only on the levels below the record -/

/-- `AgreeBelow d s s'`: two states with the same positions and with the same local times at
every level strictly below `d`. -/
def AgreeBelow (d : ℤ) (s s' : WalkState N) : Prop :=
  (∀ i, s.pos i = s'.pos i) ∧ ∀ (i : Fin N) (x : ℤ), x < d → s.ell i x = s'.ell i x

/-- **The one-step lemma below a level.**  If two states agree below the level `d`, are strictly
below `d`, and the two arrays agree at every coordinate of level `< d`, then the successors agree
below `d` as well. -/
theorem nextWalkState_agreeBelow {p : ℝ} {m : ℕ} {U U' : Array N} {d : ℤ} {s s' : WalkState N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k))
    (h : AgreeBelow d s s') (hlt : ∀ i, s.pos i < d) :
    AgreeBelow d (nextWalkState p m U s) (nextWalkState p m U' s') := by
  obtain ⟨hpos, hell⟩ := h
  have hov : ∀ i, otherVisits s.ell i (s.pos i) = otherVisits s'.ell i (s'.pos i) := by
    intro i
    have hp := hpos i
    have hlti : s'.pos i < d := by rw [← hp]; exact hlt i
    unfold otherVisits
    rw [hp]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, if_false]
      exact hell j (s'.pos i) hlti
  have hexc : ∀ i, Excited m s.ell i (s.pos i) ↔ Excited m s'.ell i (s'.pos i) := by
    intro i
    unfold Excited
    rw [hov i]
  have hrp : ∀ i, rightProbability p m s.ell i (s.pos i)
      = rightProbability p m s'.ell i (s'.pos i) := by
    intro i
    unfold rightProbability
    by_cases hE : Excited m s'.ell i (s'.pos i)
    · rw [if_pos ((hexc i).mpr hE), if_pos hE]
    · rw [if_neg (fun hh => hE ((hexc i).mp hh)), if_neg hE]
  have hjump : ∀ i, nextPos p m U s i = nextPos p m U' s' i := by
    intro i
    have hp := hpos i
    have hp' : s.pos i < d := hlt i
    have hcoord : U (i, s.pos i, s.ell i (s.pos i)) = U' (i, s'.pos i, s'.ell i (s'.pos i)) := by
      rw [hp, hell i (s'.pos i) (by omega)]
      exact harr i (s'.pos i) _ (by omega)
    rw [nextPos, nextPos, hcoord, hrp i, hp]
  constructor
  · intro i
    exact hjump i
  · intro i x hx
    rw [nextWalkState_ell, nextWalkState_ell, hell i x hx, hjump i]

/-- **The past depends only on the levels below the record.**  Trajectories driven by two arrays
that agree at every coordinate of level `< d` agree below `d` for as long as they stay below
`d`. -/
theorem agreeBelow_of_agree {p : ℝ} {m : ℕ} {U U' : Array N} {d : ℤ}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k)) :
    ∀ n, (∀ k, k ≤ n → ∀ i, (trajectory p m U k).pos i < d) →
      AgreeBelow d (trajectory p m U n) (trajectory p m U' n) := by
  intro n
  induction n with
  | zero =>
      intro _
      have hpos : ∀ i, (trajectory p m U 0).pos i = (trajectory p m U' 0).pos i :=
        fun i => by simp
      refine ⟨hpos, ?_⟩
      intro i x _
      simp
  | succ n ih =>
      intro hlt
      have hprev : ∀ k, k ≤ n → ∀ i, (trajectory p m U k).pos i < d :=
        fun k hk i => hlt k (by omega) i
      have hstep := nextWalkState_agreeBelow (p := p) (m := m) (d := d) harr (ih hprev)
        (fun i => hlt n (by omega) i)
      have e1 : trajectory p m U (n + 1) = nextWalkState p m U (trajectory p m U n) :=
        trajectory_succ ..
      have e2 : trajectory p m U' (n + 1) = nextWalkState p m U' (trajectory p m U' n) :=
        trajectory_succ ..
      rw [e1, e2]
      exact hstep

/-! ### The level shift is measure preserving, and the segment law -/

open MeasureTheory

/-- The coordinate relabelling `(i, x, k) ↦ (i, x - d, k)` of the array index set.  Its inverse
is the relabelling that `levelShift` performs, so `levelShift d` is a coordinate permutation of
the countable index set. -/
def shiftCoord (N : ℕ) (d : ℤ) : (Fin N × ℤ × ℕ) ≃ (Fin N × ℤ × ℕ) where
  toFun c := (c.1, c.2.1 - d, c.2.2)
  invFun c := (c.1, c.2.1 + d, c.2.2)
  left_inv c := by obtain ⟨i, x, k⟩ := c; simp
  right_inv c := by obtain ⟨i, x, k⟩ := c; simp

theorem measurable_levelShift (N : ℕ) (d : ℤ) : Measurable (levelShift (N := N) d) := by
  refine measurable_pi_iff.mpr (fun c => ?_)
  exact measurable_pi_apply (c.1, c.2.1 + d, c.2.2)

/-- **The level shift preserves the array law.**  The array law is an infinite product of one
and the same uniform law over the countable index set, so any bijection of the index set
preserves it; `levelShift d` is the bijection `(i, x, k) ↦ (i, x + d, k)`. -/
theorem map_levelShift (N : ℕ) (d : ℤ) :
    (arrayMeasure N).map (levelShift (N := N) d) = arrayMeasure N := by
  have h := Measure.infinitePi_map_piCongrLeft
    (fun _ : Fin N × ℤ × ℕ => uniform01) (shiftCoord N d)
  have hcomp : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N × ℤ × ℕ => ℝ) (shiftCoord N d)))
      = levelShift (N := N) d := by
    funext U c
    rw [MeasurableEquiv.coe_piCongrLeft]
    have h3 := Equiv.piCongrLeft_apply_apply
      (P := fun _ : Fin N × ℤ × ℕ => ℝ) (e := shiftCoord N d) U ((shiftCoord N d).symm c)
    rw [show (shiftCoord N d) ((shiftCoord N d).symm c) = c from Equiv.apply_symm_apply _ _] at h3
    rw [h3]
    simp [levelShift, shiftCoord]
  rw [hcomp] at h
  simpa [arrayMeasure] using h

theorem measurePreserving_levelShift (N : ℕ) (d : ℤ) :
    MeasurePreserving (levelShift (N := N) d) (arrayMeasure N) (arrayMeasure N) :=
  ⟨measurable_levelShift N d, map_levelShift N d⟩

/-- The position path of the actual trajectory. -/
noncomputable def posPath (p : ℝ) (m : ℕ) (U : Array N) : ℕ → Fin N → ℤ :=
  fun n i => (trajectory p m U n).pos i

theorem measurable_posPath (p : ℝ) (m : ℕ) (N : ℕ) :
    Measurable (posPath (N := N) p m) := by
  refine measurable_pi_iff.mpr (fun n => ?_)
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact (Swarming.Fair.measurable_trajectory p m n).1 i

/-- **The law of the fresh model is translation invariant.**  Driving the model by the
level-shifted array gives the same position-path law as driving it by the array. -/
theorem map_posPath_levelShift (p : ℝ) (m : ℕ) (N : ℕ) (d : ℤ) :
    (arrayMeasure N).map (fun U : Array N => posPath p m (levelShift d U))
      = (arrayMeasure N).map (fun U : Array N => posPath p m U) := by
  show (arrayMeasure N).map ((fun V : Array N => posPath p m V) ∘ (levelShift (N := N) d))
      = (arrayMeasure N).map (fun V : Array N => posPath p m V)
  rw [← Measure.map_map (measurable_posPath p m N) (measurable_levelShift N d),
    (measurePreserving_levelShift N d).map_eq]

/-! ### The regeneration event at a simultaneous record -/

/-- `RegenAt p m U t d` : the simultaneous record at time `t` at level `d` from which no walker
returns to `d` or below — the paper's regeneration time with regeneration level `d`. -/
def RegenAt (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) : Prop :=
  (∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d) ∧
    (∀ i, (trajectory p m U t).pos i = d) ∧
      (∀ n, ∀ i, d ≤ (trajectory p m U (t + n)).pos i)

/-- **The translated segment is the fresh path.**  On the regeneration event, the future of the
actual trajectory relative to the record level *is* the position path of the fresh model driven
by the shifted array — with no conditioning and no independence input. -/
theorem relFuture_eq (p : ℝ) (m : ℕ) (U : Array N) {t : ℕ} {d : ℤ}
    (h : RegenAt p m U t d) :
    (fun n : ℕ => fun i : Fin N => (trajectory p m U (t + n)).pos i - d)
      = posPath p m (levelShift d U) := by
  obtain ⟨hbefore, hat, hstay⟩ := h
  funext n i
  show (trajectory p m U (t + n)).pos i - d = (trajectory p m (levelShift d U) n).pos i
  rw [restart_pos p m U hbefore hat hstay n i]
  omega

/-- **The event identity behind `(freshlaw)`.**  The event "a regeneration at level `d` at time
`t`, and the relative future segment lies in `B`" is the record event intersected with the
*preimage under the level shift* of the fresh event "the fresh path lies in `B`".  The first
factor is a function of the array coordinates at levels `< d`, the second of the coordinates at
levels `≥ d`; that separation, plus the independence of the two coordinate blocks, is the
remaining input. -/
theorem restart_event_identity (p : ℝ) (m : ℕ) (t : ℕ) (d : ℤ)
    (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | RegenAt p m U t d ∧
        (fun n : ℕ => fun i : Fin N => (trajectory p m U (t + n)).pos i - d) ∈ B}
      = {U : Array N | RegenAt p m U t d ∧ posPath p m (levelShift d U) ∈ B} := by
  ext U
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hB⟩
    rw [← relFuture_eq p m U h]
    exact ⟨h, hB⟩
  · rintro ⟨h, hB⟩
    rw [relFuture_eq p m U h]
    exact ⟨h, hB⟩

/-- The measure of the preimage of a measurable set under the level shift is unchanged. -/
theorem measure_levelShift_preimage (N : ℕ) (d : ℤ) {S : Set (Array N)}
    (hS : MeasurableSet S) :
    (arrayMeasure N) ((levelShift (N := N) d) ⁻¹' S) = (arrayMeasure N) S :=
  (measurePreserving_levelShift N d).measure_preimage hS.nullMeasurableSet

/-! ### The future segment depends only on the levels above the record -/

/-- **The one-step lemma above a level.**  Two states with the same positions, the same local
times at every site `≥ 0`, both at sites `≥ 0`, driven by two arrays that agree at every
coordinate of level `≥ 0`, make the same jump. -/
theorem nextWalkState_agreeAbove {p : ℝ} {m : ℕ} {U U' : Array N} {s s' : WalkState N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), 0 ≤ x → U (i, x, k) = U' (i, x, k))
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (hge : ∀ i, 0 ≤ s.pos i) :
    (∀ i, (nextWalkState p m U s).pos i = (nextWalkState p m U' s').pos i) ∧
      ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
        (nextWalkState p m U s).ell i x = (nextWalkState p m U' s').ell i x := by
  have hov : ∀ i, otherVisits s.ell i (s.pos i) = otherVisits s'.ell i (s'.pos i) := by
    intro i
    have hp := hpos i
    have hpx : 0 ≤ s.pos i := hge i
    unfold otherVisits
    rw [hp]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, if_false]
      exact hell j (s'.pos i) (by rw [← hp]; exact hpx)
  have hexc : ∀ i, Excited m s.ell i (s.pos i) ↔ Excited m s'.ell i (s'.pos i) := by
    intro i
    unfold Excited
    rw [hov i]
  have hrp : ∀ i, rightProbability p m s.ell i (s.pos i)
      = rightProbability p m s'.ell i (s'.pos i) := by
    intro i
    unfold rightProbability
    by_cases hE : Excited m s'.ell i (s'.pos i)
    · rw [if_pos ((hexc i).mpr hE), if_pos hE]
    · rw [if_neg (fun hh => hE ((hexc i).mp hh)), if_neg hE]
  have hjump : ∀ i, nextPos p m U s i = nextPos p m U' s' i := by
    intro i
    have hp := hpos i
    have hpx : 0 ≤ s.pos i := hge i
    have hcoord : U (i, s.pos i, s.ell i (s.pos i)) = U' (i, s'.pos i, s'.ell i (s'.pos i)) := by
      rw [hp, hell i (s'.pos i) (by rw [← hp]; exact hpx)]
      exact harr i (s'.pos i) _ (by rw [← hp]; exact hpx)
    rw [nextPos, nextPos, hcoord, hrp i, hp]
  refine ⟨fun i => hjump i, ?_⟩
  intro i x hx
  rw [nextWalkState_ell, nextWalkState_ell, hell i x hx, hjump i]

/-- **The fresh path depends only on the levels at or above `0`.**  Two arrays that agree at every
coordinate of level `≥ 0`, one of which keeps every walker nonnegative, drive the same position
path. -/
theorem freshAgreeAbove {p : ℝ} {m : ℕ} {U U' : Array N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), 0 ≤ x → U (i, x, k) = U' (i, x, k))
    (hstay : ∀ n, ∀ i, 0 ≤ (trajectory p m U n).pos i) :
    ∀ n, (∀ i, (trajectory p m U n).pos i = (trajectory p m U' n).pos i) ∧
      ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
        (trajectory p m U n).ell i x = (trajectory p m U' n).ell i x := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun i => by simp, ?_⟩
      intro i x _
      simp
  | succ n ih =>
      obtain ⟨ihpos, ihell⟩ := ih
      have hstep := nextWalkState_agreeAbove (p := p) (m := m) harr ihpos ihell
        (fun i => hstay n i)
      have e1 : trajectory p m U (n + 1) = nextWalkState p m U (trajectory p m U n) :=
        trajectory_succ ..
      have e2 : trajectory p m U' (n + 1) = nextWalkState p m U' (trajectory p m U' n) :=
        trajectory_succ ..
      rw [e1, e2]
      exact hstep

/-- **The translated future segment is a function of the record level and of the array
coordinates strictly above it.**  Two arrays that agree at every coordinate of level `≥ d` give
the same fresh position path, hence — through `relFuture_eq` — the same relative future segment
after a regeneration at level `d`. -/
theorem posPath_shift_congr {p : ℝ} {m : ℕ} {U U' : Array N} {d : ℤ}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), d ≤ x → U (i, x, k) = U' (i, x, k))
    (hstay : ∀ n, ∀ i, 0 ≤ (trajectory p m (levelShift d U) n).pos i) :
    posPath p m (levelShift d U) = posPath p m (levelShift d U') := by
  have harr' : ∀ (i : Fin N) (x : ℤ) (k : ℕ), 0 ≤ x →
      levelShift d U (i, x, k) = levelShift d U' (i, x, k) := by
    intro i x k hx
    rw [levelShift_apply, levelShift_apply]
    exact harr i (x + d) k (by omega)
  funext n i
  exact (freshAgreeAbove harr' hstay n).1 i

/-- **The relative future at a regeneration is determined by the levels at or above the record
level.**  This is the separator that the remaining `(freshlaw)` independence step needs: the
future segment is a function of the high block, and `agreeBelow_of_agree` shows the record event
is a function of the low block. -/
theorem relFuture_depends_high {p : ℝ} {m : ℕ} {U U' : Array N} {t : ℕ} {d : ℤ}
    (h : RegenAt p m U t d)
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), d ≤ x → U (i, x, k) = U' (i, x, k)) :
    (fun n : ℕ => fun i : Fin N => (trajectory p m U (t + n)).pos i - d)
      = posPath p m (levelShift d U') := by
  rw [relFuture_eq p m U h]
  refine posPath_shift_congr harr (fun n i => ?_)
  have hstay := h.2.2 n i
  have hpos := restart_pos p m U h.1 h.2.1 h.2.2 n i
  omega

/-! ### Regenerations concatenate, and every block starts from the same state -/

/-- **Regeneration levels add.**  A regeneration at level `d` at time `t`, followed by a
regeneration of the shifted model at level `e ≥ 0` at time `s`, is a regeneration of the original
trajectory at level `d + e` at time `t + s`.  This is the paper's "by iteration" step, with the
record condition carried through the translated segment. -/
theorem regenAt_add {p : ℝ} {m : ℕ} {U : Array N} {t s : ℕ} {d e : ℤ}
    (h : RegenAt p m U t d) (he : 0 ≤ e) (h' : RegenAt p m (levelShift d U) s e) :
    RegenAt p m U (t + s) (d + e) := by
  obtain ⟨hbefore, hat, hstay⟩ := h
  obtain ⟨hbefore', hat', hstay'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · intro k hk i
    rcases Nat.lt_or_ge k t with hkt | hkt
    · have := hbefore k hkt i
      omega
    · obtain ⟨n, hn⟩ : ∃ n, k = t + n := ⟨k - t, by omega⟩
      subst hn
      have hns : n < s := by omega
      have hpos := restart_pos p m U hbefore hat hstay n i
      have := hbefore' n hns i
      omega
  · intro i
    have h1 := restart_pos p m U hbefore hat hstay s i
    rw [h1, hat' i]
  · intro n i
    have hpos := restart_pos p m U hbefore hat hstay (s + n) i
    have hst := hstay' n i
    rw [show t + s + n = t + (s + n) from by omega, hpos]
    omega

/-- **Every regeneration starts from the same canonical state.**  After a regeneration and a
further regeneration of the shifted model, the original state again has local time exactly one at
the new record level and zero strictly above it — the state from which the next translated
segment starts is literally the same canonical profile each time. -/
theorem regenAt_add_ell {p : ℝ} {m : ℕ} {U : Array N} {t s : ℕ} {d e : ℤ}
    (h : RegenAt p m U t d) (he : 0 ≤ e) (h' : RegenAt p m (levelShift d U) s e) :
    (∀ i, (trajectory p m U (t + s)).ell i (d + e) = 1) ∧
      ∀ i, ∀ x : ℤ, d + e < x → (trajectory p m U (t + s)).ell i x = 0 := by
  obtain ⟨hbefore, hat, hstay⟩ := h
  obtain ⟨hbefore', hat', hstay'⟩ := h'
  have hcan := ell_at_simultaneous_record p m (levelShift d U) hbefore' hat'
  constructor
  · intro i
    have h1 := restart_ell p m U hbefore hat hstay s i e he
    rw [h1, hcan.1 i]
  · intro i x hx
    have hd : d ≤ x := by omega
    have hxd : 0 ≤ x - d := by omega
    have hxe : e < x - d := by omega
    have h1 := restart_ell p m U hbefore hat hstay s i (x - d) hxd
    rw [show d + (x - d) = x from by omega] at h1
    rw [h1, hcan.2 i (x - d) hxe]

/-! ### Non-vacuity: the constant-zero array has a regeneration at every level -/

/-- With every array coordinate equal to `0` and `1/2 ≤ p`, every walker steps right at every
step: the right probability is `p` or `1/2`, both at least `1/2`, and `drivenStep 0 α = 1`
whenever `α ≥ 0`. -/
theorem nextPos_zero {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (s : WalkState N) (i : Fin N) :
    nextPos p m (fun _ => (0 : ℝ)) s i = s.pos i + 1 := by
  have hα : 0 ≤ rightProbability p m s.ell i (s.pos i) := by
    unfold rightProbability
    by_cases hE : Excited m s.ell i (s.pos i)
    · rw [if_pos hE]; linarith
    · rw [if_neg hE]; norm_num
  simp only [nextPos, drivenStep]
  rw [if_pos hα]

/-- With the constant-zero array the trajectory is the straight line `pos_n i = n`. -/
theorem trajectory_zero_pos {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (n : ℕ) (i : Fin N) :
    (trajectory p m (fun _ => (0 : ℝ)) n).pos i = (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_pos, nextPos_zero hp, ih]
      push_cast
      ring

/-- **Non-vacuity of `RegenAt`.**  With the constant-zero array every walker moves right at every
step, so the trajectory has a simultaneous record at level `t` at every time `t`, and it never
returns.  In particular the hypotheses of `restart_agreement` are satisfiable at every `t`, so the
translated-segment theorem is not vacuous. -/
theorem regenAt_zero_array (N : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (t : ℕ) :
    RegenAt p m (fun _ : Fin N × ℤ × ℕ => (0 : ℝ)) t (t : ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs i
    rw [trajectory_zero_pos hp]
    exact_mod_cast hs
  · intro i
    rw [trajectory_zero_pos hp]
  · intro n i
    rw [trajectory_zero_pos hp]
    have h : t ≤ t + n := Nat.le_add_right t n
    exact_mod_cast h

/-- Consistency check of the translated-segment theorem on the constant-zero array: both sides
are the straight line, so the identity of `restart_pos` is not merely formal. -/
theorem restart_pos_zero_array (N : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (t n : ℕ) (i : Fin N) :
    (trajectory p m (fun _ : Fin N × ℤ × ℕ => (0 : ℝ)) (t + n)).pos i
      = (t : ℤ) + (trajectory p m (levelShift (t : ℤ) (fun _ => (0 : ℝ))) n).pos i := by
  have hz : levelShift (N := N) (t : ℤ) (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
    funext c; rfl
  have hrec := regenAt_zero_array N p hp m t
  rw [restart_pos p m _ hrec.1 hrec.2.1 hrec.2.2 n i, hz, trajectory_zero_pos hp]

/-! ### The finite product law for an arbitrary finite set of coordinates -/

open ProbabilityTheory

/-- **The array law on a finite cylinder over an arbitrary finite set of coordinates.**  This
generalises `Swarming.Uniform.arrayMeasure_cylinder` (which is stated for the whole family
`Fin N`) to an arbitrary `Finset` of array coordinates. -/
theorem arrayMeasure_finset (N : ℕ) (s : Finset (Fin N × ℤ × ℕ)) (C : Fin N × ℤ × ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i)) :
    (arrayMeasure N) (⋂ i ∈ s, (fun U : Array N => U i) ⁻¹' C i)
      = ∏ i ∈ s, uniform01 (C i) := by
  have hInd : iIndepFun (fun i (ω : Array N) => ω i) (arrayMeasure N) := array_independent N
  have h := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd s
    (sets := C) (fun i _ => hC i)
  rw [h]
  exact Finset.prod_congr rfl fun i _ => arrayMeasure_preimage_set N i (C i) (hC i)

/-- **Disjoint coordinate blocks factorise.**  For two disjoint finite sets of array coordinates
and any measurable coordinate conditions, the measure of the joint cylinder is the product of the
two block measures.  This is the finite form of the block independence that `(freshlaw)` needs. -/
theorem cylinder_mul (N : ℕ) (s t : Finset (Fin N × ℤ × ℕ)) (hst : Disjoint s t)
    (C : Fin N × ℤ × ℕ → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) :
    (arrayMeasure N) (⋂ i ∈ s ∪ t, (fun U : Array N => U i) ⁻¹' C i)
      = (arrayMeasure N) (⋂ i ∈ s, (fun U : Array N => U i) ⁻¹' C i)
        * (arrayMeasure N) (⋂ i ∈ t, (fun U : Array N => U i) ⁻¹' C i) := by
  rw [arrayMeasure_finset N (s ∪ t) C hC, arrayMeasure_finset N s C hC,
    arrayMeasure_finset N t C hC, Finset.prod_union hst]

/-! ### The record part of the regeneration event -/

/-- The record part of `RegenAt`: the simultaneous record at time `t` at level `d`, without the
no-return condition.  By `agreeBelow_of_agree` this part is a function of the array coordinates at
levels `< d`; the no-return part is, by `restart_agreement`, equivalent to the fresh path of the
shifted array staying nonnegative.  Together they make the translated future independent of the
past, once the two coordinate blocks are independent. -/
def RecordAt (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (d : ℤ) : Prop :=
  (∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d) ∧
    ∀ i, (trajectory p m U t).pos i = d

theorem regenAt_recordAt {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (h : RegenAt p m U t d) : RecordAt p m U t d :=
  ⟨h.1, h.2.1⟩
