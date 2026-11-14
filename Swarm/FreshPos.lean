/-
# State-independence of the fresh future from the simultaneous-record set `F = srSet`

Paper `main_1d.tex`, proof of Proposition `regen`:

> "On `{τ_d = t, X_t^i = d for every i}`, all local times at `d` equal `1`, and all local
>  times strictly above `d` equal `0`.  Until a return to or below `d`, we determine the
>  translated future from the local times at and above `d` and independent unrevealed
>  uniforms. ... For an evolution started from any state in `F`, we have the same identity
>  at `d = t = 0`, since its capped local times at `0` are all `1` and those above `0`
>  are all `0`."

`StationaryMass.mass_identity` derives the paper's display `μ (F × C) = π F · pv` from the
per-state identity `κ y C = pv` on `F = srSet`.  `HitStateDep.future_law_state_dependent`
shows that this identity **fails** for an *arbitrary* future event `C`: the raw capped record
state keeps past local times at sites below the level, and paths that dip down there see them.

This file proves the positive half that `HitStateDep` leaves open and that the regeneration
argument actually uses.  The statement is made for an abstract `FreshStart` state, i.e. exactly
the data the paper attributes to `F`: all walkers at the record level, every capped local time
strictly above the level zero, and local time `1` at the level.

* `posAt`, `pos_evolveFun` — the positions after `n` jumps are the starting positions plus a
  function of the jump sequence alone, so "stays strictly above the level" is a property of
  the sequence;
* `eta_above_eq` — if every walker stays strictly above the level at every time `1, …, k`,
  then the capped local times at every site strictly above the level agree for **all**
  fresh starts: below-level data is never queried and never propagates upwards;
* `otherVisits_eq`, `stepW_eq` — hence the excitation count and the one-step joint weight
  agree at each step;
* `pathWFun_eq` — hence the mass of every prescribed positive jump sequence agrees;
* `positive_mass_eq` — **the `k`-step mass of "no walker returns to or below the level" is
  the same for every fresh start**, and `positive_mass_eq_of_srSet` reads this on `srSet`.

Scope.  This is the model-level content of the paper's `(freshlaw)` sentence at `d = t = 0`,
restricted to the finite horizon `k`.  It is *not* the record-kernel identity `κ y C = pv` of
`StationaryMass`: passing to the record kernel needs (i) the `k → ∞` limit of these masses
(continuity from above for the event "no return to the level, ever") and (ii) the
identification of the record kernel's future with the concatenation of the raw segments.
Neither is claimed here, and nothing here asserts `hfull`, regeneration, `(ED)` or a speed.
-/
import Swarm.SimJumpPath
import Swarm.Bridge

open Finset

namespace SwarmFreshPos

open SimJump SimJump.Record SwarmRec

variable {N m : ℕ}

/-! ## The position of the walkers is a function of the jump sequence -/

/-- Net displacement of walker `i` after the first `n` jumps of `u`. -/
noncomputable def posAt (u : ℕ → JumpVec N) (n : ℕ) (i : Fin N) : ℤ :=
  ∑ j ∈ Finset.range n, (if u j i = true then (1 : ℤ) else -1)

theorem posAt_succ (u : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    posAt u (n + 1) i = posAt u n i + (if u n i = true then (1 : ℤ) else -1) := by
  simp only [posAt, Finset.sum_range_succ]

theorem posAt_zero (u : ℕ → JumpVec N) (i : Fin N) : posAt u 0 i = 0 := by
  simp [posAt]

/-- Zero jumps leave the state unchanged. -/
theorem evolveFun_zero (u : ℕ → JumpVec N) (s : State N m) : evolveFun u 0 s = s := rfl

/-- The position of every walker after `n` jumps is its starting position plus the net
displacement of the jump sequence alone. -/
theorem pos_evolveFun (u : ℕ → JumpVec N) (n : ℕ) (s : State N m) (i : Fin N) :
    (evolveFun u n s).pos i = s.pos i + posAt u n i := by
  induction n with
  | zero =>
    show s.pos i = s.pos i + posAt u 0 i
    rw [posAt_zero, add_zero]
  | succ n ih =>
    have hstep : (evolveFun u (n + 1) s).pos i
        = (evolveFun u n s).pos i + (if u n i = true then (1 : ℤ) else -1) := by
      rw [evolveFun_succ, step_pos, stepPos]
    rw [hstep, ih, posAt_succ]
    ring

/-! ## Fresh starts: the data the paper attributes to `F` -/

/-- A state at the record level whose local times above the level are zero and whose local
time at the level is one.  This is the paper's "capped local times at `0` are all `1` and
those above `0` are all `0`". -/
def FreshStart (s : State N m) : Prop :=
  (∀ i, s.pos i = 0) ∧ (∀ (i : Fin N) (x : ℤ), 0 < x → s.eta i x = 0) ∧
    (∀ i, s.eta i 0 = 1)

theorem freshStart_eta_above {s : State N m} (hs : FreshStart s) (i : Fin N) {x : ℤ}
    (hx : 0 < x) : s.eta i x = 0 := hs.2.1 i x hx

/-- Every member of `srSet`, expanded to the uncapped step chain, is a fresh start. -/
theorem freshStart_ofRecState {y : RecState N m} (hy : y ∈ srSet N m) (hm : 1 ≤ m) :
    FreshStart (ofRecState y) := by
  have hrs := ofRecState_recordStart y hm
  refine ⟨fun i => ?_, fun i x hx => hrs.eta_above i x hx, fun i => ?_⟩
  · have hle : dist2 y i ≤ 0 := hy i
    have hd : y.val.1 i = 0 := by
      have hle' : y.val.1 i ≤ 0 := hle
      omega
    change -(2 * (y.val.1 i : ℤ)) = 0
    simp [hd]
  · have h := hrs.eta_origin i
    rw [show (ofRecState y).pos i = 0 from ?_, if_pos rfl] at h
    exact h
    have hle : dist2 y i ≤ 0 := hy i
    have hd : y.val.1 i = 0 := by
      have hle' : y.val.1 i ≤ 0 := hle
      omega
    change -(2 * (y.val.1 i : ℤ)) = 0
    simp [hd]

/-! ## Local times above the level are state-independent along a positive excursion -/

/-- **The core identity.**  Let `u` be a jump sequence that keeps every walker strictly
above the level at every time `1, …, k`.  Then at every time `n ≤ k` the capped local times
at every site strictly above the level agree for all fresh starts. -/
theorem eta_above_eq {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (u : ℕ → JumpVec N) (k : ℕ)
    (hpos : ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < posAt u n i) :
    ∀ n, n ≤ k → ∀ (i : Fin N) (x : ℤ), 0 < x →
      (evolveFun u n s).eta i x = (evolveFun u n s').eta i x := by
  intro n
  induction n with
  | zero =>
    intro _ i x hx
    show s.eta i x = s'.eta i x
    rw [freshStart_eta_above hs i hx, freshStart_eta_above hs' i hx]
  | succ n ih =>
    intro hnk i x hx
    have hnk' : n ≤ k := by omega
    set e := evolveFun u n s with he
    set e' := evolveFun u n s' with he'
    have hepos : e.pos i = posAt u n i := by
      rw [he, pos_evolveFun, hs.1 i, zero_add]
    have hepos' : e'.pos i = posAt u n i := by
      rw [he', pos_evolveFun, hs'.1 i, zero_add]
    have hposEq : e.pos i = e'.pos i := by rw [hepos, hepos']
    have hnew : 0 < posAt u (n + 1) i := hpos (n + 1) (by omega) (by omega) i
    have hnew' : 0 < e.pos i + (if u n i = true then (1 : ℤ) else -1) := by
      rw [hepos, ← posAt_succ]
      exact hnew
    rw [evolveFun_succ, evolveFun_succ]
    by_cases hc : x = e.pos i + (if u n i = true then (1 : ℤ) else -1)
    · have hme : stepPos e (u n) i = e.pos i + (if u n i = true then (1 : ℤ) else -1) := rfl
      have hme' : stepPos e' (u n) i = e.pos i + (if u n i = true then (1 : ℤ) else -1) := by
        rw [stepPos, ← hposEq]
      have hsite : stepPos e' (u n) i = stepPos e (u n) i := by rw [hme', hme]
      rw [← hme] at hc
      rw [hc]
      rw [show (step m e' (u n)).eta i (stepPos e (u n) i)
            = (step m e' (u n)).eta i (stepPos e' (u n) i) from by rw [← hsite]]
      rw [step_eta_of_eq, step_eta_of_eq, hsite]
      have hspos : 0 < stepPos e (u n) i := by rw [hme]; exact hnew'
      rw [ih hnk' i _ hspos]
    · have hc' : x ≠ stepPos e' (u n) i := by
        rw [stepPos, ← hposEq]
        exact hc
      have hc'' : x ≠ stepPos e (u n) i := hc
      rw [step_eta_of_ne (m := m) e (u n) i hc'', step_eta_of_ne (m := m) e' (u n) i hc',
        ih hnk' i x hx]

/-! ## The excitation count and the one-step weight -/

/-- **The excitation count is state-independent along a positive excursion.** -/
theorem otherVisits_eq {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (u : ℕ → JumpVec N) (k : ℕ)
    (hpos : ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < posAt u n i)
    {n : ℕ} (hn : n ≤ k) (i : Fin N) :
    otherVisits (evolveFun u n s) i = otherVisits (evolveFun u n s') i := by
  rcases n with _ | n
  · have key : ∀ (z : State N m), FreshStart z →
        otherVisits z i = ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) := by
      intro z hz
      simp only [otherVisits]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hz.1 i, hz.2.2 j]
    rw [evolveFun_zero, evolveFun_zero, key s hs, key s' hs']
  · have hp : 0 < posAt u (n + 1) i := hpos (n + 1) (by omega) (by omega) i
    have hp' : 0 < (evolveFun u (n + 1) s').pos i := by
      rw [pos_evolveFun, hs'.1 i, zero_add]
      exact hp
    have hposEq : (evolveFun u (n + 1) s).pos i = (evolveFun u (n + 1) s').pos i := by
      rw [pos_evolveFun, pos_evolveFun, hs.1 i, hs'.1 i]
    simp only [otherVisits]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hposEq]
    exact eta_above_eq hs hs' u k hpos (n + 1) (by omega) j _ hp'

/-- **The one-step joint weight is state-independent along a positive excursion.** -/
theorem stepW_eq (p : ℝ) {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (u : ℕ → JumpVec N) (k : ℕ)
    (hpos : ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < posAt u n i)
    {n : ℕ} (hn : n < k) :
    stepW p m (evolveFun u n s) (u n) = stepW p m (evolveFun u n s') (u n) := by
  simp only [stepW_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [stepFactor, qRight]
  rw [otherVisits_eq hs hs' u k hpos (by omega) i]

/-- **The weight of every positive jump sequence is state-independent on fresh starts.** -/
theorem pathWFun_eq (p : ℝ) {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (u : ℕ → JumpVec N) (k : ℕ)
    (hpos : ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < posAt u n i) :
    pathWFun p u k s = pathWFun p u k s' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathWFun_succ, pathWFun_succ, ih (fun n h1 h2 => hpos n h1 (by omega)),
      stepW_eq p hs hs' u (k + 1) hpos (by omega)]

/-! ## The finite-horizon fresh mass -/

/-- The finite-horizon "fresh" event: every walker stays strictly above the level at every
time `1, …, k`.  This is a condition on the jump sequence alone. -/
def PosSeq (k : ℕ) (u : ℕ → JumpVec N) : Prop :=
  ∀ n, 1 ≤ n → n ≤ k → ∀ i, 0 < posAt u n i

/-- Regard a finite jump block `q : Fin k → JumpVec N` as a sequence, extended by the all-left
jump vector past `k`.  Only the first `k` entries are ever inspected. -/
def seqOf {k : ℕ} (q : Fin k → JumpVec N) : ℕ → JumpVec N :=
  fun j => if h : j < k then q ⟨j, h⟩ else fun _ => false

theorem seqOf_val {k : ℕ} (q : Fin k → JumpVec N) (i : Fin k) : seqOf q (i : ℕ) = q i := by
  simp [seqOf, i.isLt]

theorem seq_coe {k : ℕ} (q : Fin k → JumpVec N) : (fun i : Fin k => seqOf q (i : ℕ)) = q := by
  funext i
  exact seqOf_val q i

/-- The finite-horizon fresh event, read on a finite jump block.  The horizon quantifier runs
over `Fin (k+1)` so that the predicate is decidable and can appear in a finite sum. -/
abbrev PosSeqFin {k : ℕ} (q : Fin k → JumpVec N) : Prop :=
  ∀ n : Fin (k + 1), 1 ≤ (n : ℕ) → ∀ i : Fin N, 0 < posAt (seqOf q) (n : ℕ) i

theorem posSeqFin_iff {k : ℕ} {q : Fin k → JumpVec N} :
    PosSeqFin (N := N) q ↔ PosSeq (N := N) k (seqOf q) := by
  constructor
  · intro h n h1 h2 i
    exact h ⟨n, by omega⟩ h1 i
  · intro h n h1 i
    exact h (n : ℕ) h1 (by omega) i

/-- **The paper's finite-horizon fresh mass is the same at every fresh start.**

The `k`-step mass that the future never returns to or below the level does not depend on the
starting state, as long as that state is a fresh start — in particular the past local times
at and below the level are irrelevant, which is the content of the paper's "we determine the
translated future from the local times at and above `d`". -/
theorem positive_mass_eq (p : ℝ) {s s' : State N m} (hs : FreshStart s) (hs' : FreshStart s')
    (k : ℕ) :
    (∑ q : Fin k → JumpVec N, if PosSeqFin (N := N) q then pathW p k q s else 0)
      = ∑ q : Fin k → JumpVec N, if PosSeqFin (N := N) q then pathW p k q s' else 0 := by
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : PosSeqFin (N := N) q
  · rw [if_pos hq, if_pos hq, ← seq_coe q]
    exact pathWFun_eq p hs hs' (seqOf q) k (posSeqFin_iff.mp hq)
  · rw [if_neg hq, if_neg hq]

/-- **The same finite-horizon fresh mass on `F = srSet`**, in the record coordinates of the
stopped record kernel. -/
theorem positive_mass_eq_of_srSet (p : ℝ) {y y' : RecState N m} (hy : y ∈ srSet N m)
    (hy' : y' ∈ srSet N m) (hm : 1 ≤ m) (k : ℕ) :
    (∑ q : Fin k → JumpVec N,
        if PosSeqFin (N := N) q then pathW p k q (ofRecState y) else 0)
      = ∑ q : Fin k → JumpVec N,
        if PosSeqFin (N := N) q then pathW p k q (ofRecState y') else 0 :=
  positive_mass_eq p (freshStart_ofRecState hy hm) (freshStart_ofRecState hy' hm) k

/-- Sanity check of the finite-horizon mass at `k = 0`: the empty jump block is positive and
carries mass `1` from every state. -/
theorem positive_mass_zero (p : ℝ) (s : State N m) :
    (∑ q : Fin 0 → JumpVec N, if PosSeqFin (N := N) q then pathW p 0 q s else 0) = 1 := by
  rw [Fintype.sum_unique]
  have hvac : PosSeqFin (N := N) (default : Fin 0 → JumpVec N) := by
    intro n h1 i
    omega
  split_ifs with h
  · rfl
  · exact absurd hvac h

end SwarmFreshPos


