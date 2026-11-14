/-
# The fresh future is state-independent on the simultaneous-record set `F`

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, §"Regeneration and the
collective speed", proof of Proposition `regen`:

> For an evolution started from any state in `F`, we have the same identity at `d = t = 0`,
> since its capped local times at `0` are all `1` and those above `0` are all `0`.

That sentence is the *only* input to the stationary mass identity `P_π(A) = π(F) P(V)` and to
the factorisation `P_π(X ∈ B | A) = P^*(B)` used by the Kac step.  `areas/kac/StationaryMass.lean`
consumes it as a hypothesis (`hconst`/`hfresh`); `MassSharp.lean` and `HitStateDep.lean` show it
is *not* a consequence of invariance and that the unrestricted future law does depend on the
state.  This file proves the restricted statement for the actual model.

Main result (`fresh_mass_strictPos`): for every record state `y` in `srSet N m` (the paper's
`F = {d_i = 0 for all i}`, i.e. every walker at the record level) and every set `B` of future
paths, the mass, under the actual array law, of

  "the future of the interacting trajectory started from `y` stays strictly above the record
   level and its translated path lies in `B`"

equals the mass of "the fresh path lies in `strictPos ∩ B`" — exactly the fresh probability
`P(V ∩ B)` of the source, with no factor depending on `y`.

The mechanism is the paper's: sites at or above the record level carry the *same* capped local
times in every state of `F` (`η_i(0) = 1`, `η_i(x) = 0` for `x > 0`) as in the fresh start, so
with the *same* uniforms the position paths agree as long as no walker goes below the record;
and on `V` no walker ever does.  Hence not merely the masses but the events themselves coincide.

Everything here is unconditional (no probability-normalisation hypothesis, no invariant law, no
tightness); the only model input is `1 ≤ m`.
-/
import Swarm.PaperV
import Swarm.RecordState

open MeasureTheory Set
open Swarming
open Swarming.Uniform
open Swarming.Trajectory
open SwarmRestart
open SwarmRec
open SwarmFresh
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace SwarmFreshState

variable {N : ℕ}

/-! ### Agreement above the record level for two arbitrary start states -/

/-- The paper's `V` for a trajectory started from an arbitrary walk state: from the next step
onwards every walker is strictly above the record level. -/
def FromV (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) : Prop :=
  ∀ (i : Fin N) (n : ℕ), 0 < n → 0 < (trajFrom p m U s n).pos i

/-- Local times at every site at or above the record level agree at all times at which every
walker is still at or above it.  This is `SwarmRestart.nextWalkState_agreeAbove` iterated, with
the nonnegativity hypothesis discharged level by level. -/
theorem agree_above_upto {p : ℝ} {m : ℕ} {U : Array N} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x) :
    ∀ n : ℕ, (∀ k, k ≤ n → ∀ i, 0 ≤ (trajFrom p m U s k).pos i) →
      (∀ k, k ≤ n → ∀ i, 0 ≤ (trajFrom p m U s' k).pos i) →
      (∀ i, (trajFrom p m U s n).pos i = (trajFrom p m U s' n).pos i) ∧
        ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
          (trajFrom p m U s n).ell i x = (trajFrom p m U s' n).ell i x := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨hpos, hell⟩
  | succ n ih =>
      intro hge hge'
      have hN := ih (fun k hk => hge k (Nat.le_trans hk (Nat.le_succ n)))
        (fun k hk => hge' k (Nat.le_trans hk (Nat.le_succ n)))
      rw [trajFrom_succ, trajFrom_succ]
      exact nextWalkState_agreeAbove (p := p) (m := m) (U := U) (U' := U)
        (s := trajFrom p m U s n) (s' := trajFrom p m U s' n)
        (fun _ _ _ _ => rfl) hN.1 hN.2 (fun i => hge n (Nat.le_succ n) i)

/-- Nothing is below the record level at time `0`. -/
theorem nonneg_of_zero {p : ℝ} {m : ℕ} {U : Array N} {s : WalkState N}
    (h0 : ∀ i, s.pos i = 0) (hV : FromV p m U s) :
    ∀ n i, 0 ≤ (trajFrom p m U s n).pos i := by
  intro n i
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [trajFrom_zero, h0 i]
  · exact le_of_lt (hV i n h)

/-- **The position paths from two states with the same record profile, one of which stays at or
above the record level, are equal.** -/
theorem pos_eq_of_FromV {p : ℝ} {m : ℕ} {U : Array N} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (h0 : ∀ i, s.pos i = 0) (hV : FromV p m U s) :
    ∀ n i, (trajFrom p m U s n).pos i = (trajFrom p m U s' n).pos i := by
  have hNN := nonneg_of_zero h0 hV
  have key : ∀ n : ℕ, (∀ i, (trajFrom p m U s n).pos i = (trajFrom p m U s' n).pos i) ∧
      (∀ (i : Fin N) (x : ℤ), 0 ≤ x →
        (trajFrom p m U s n).ell i x = (trajFrom p m U s' n).ell i x) ∧
      (∀ i, 0 ≤ (trajFrom p m U s' n).pos i) := by
    intro n
    induction n with
    | zero =>
        refine ⟨hpos, hell, fun i => ?_⟩
        show 0 ≤ s'.pos i
        rw [← hpos i, ← h0 i]
    | succ n ih =>
        obtain ⟨hp, he, hge'⟩ := ih
        have hstep := nextWalkState_agreeAbove (p := p) (m := m) (U := U) (U' := U)
          (s := trajFrom p m U s n) (s' := trajFrom p m U s' n)
          (fun _ _ _ _ => rfl) hp he (fun i => hNN n i)
        refine ⟨?_, ?_, fun i => ?_⟩
        · rw [trajFrom_succ, trajFrom_succ]
          exact hstep.1
        · intro i x hx
          rw [trajFrom_succ, trajFrom_succ]
          exact hstep.2 i x hx
        · have h1 : 0 ≤ (nextWalkState p m U (trajFrom p m U s n)).pos i := by
            rw [← trajFrom_succ]
            exact hNN (n + 1) i
          rw [trajFrom_succ, ← hstep.1 i]
          exact h1
  intro n i
  exact (key n).1 i

/-- **The event identity.**  Two start states with the same record profile (equal positions,
equal local times at every site at or above the record level, all walkers at that level) see
*the same* array set: the future stays strictly above the record level and the translated path
lies in `B`, for the one state if and only if for the other. -/
theorem fresh_set_eq {p : ℝ} {m : ℕ} {s s' : WalkState N}
    (hpos : ∀ i, s.pos i = s'.pos i)
    (hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x → s.ell i x = s'.ell i x)
    (h0 : ∀ i, s.pos i = 0) (h0' : ∀ i, s'.pos i = 0) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | FromV p m U s ∧ (fun n i => (trajFrom p m U s n).pos i) ∈ B}
      = {U : Array N | FromV p m U s' ∧ (fun n i => (trajFrom p m U s' n).pos i) ∈ B} := by
  ext U
  constructor
  · rintro ⟨hV, hB⟩
    have hpe := pos_eq_of_FromV hpos hell h0 hV
    refine ⟨?_, ?_⟩
    · intro i n hn
      rw [← hpe n i]
      exact hV i n hn
    · have hfun : (fun n i => (trajFrom p m U s n).pos i)
          = fun n i => (trajFrom p m U s' n).pos i := by
        funext n i
        exact hpe n i
      rw [← hfun]
      exact hB
  · rintro ⟨hV, hB⟩
    have hpe := pos_eq_of_FromV (s := s') (s' := s) (fun i => (hpos i).symm)
      (fun i x hx => (hell i x hx).symm) h0' hV
    refine ⟨?_, ?_⟩
    · intro i n hn
      rw [← hpe n i]
      exact hV i n hn
    · have hfun : (fun n i => (trajFrom p m U s' n).pos i)
          = fun n i => (trajFrom p m U s n).pos i := by
        funext n i
        exact hpe n i
      rw [← hfun]
      exact hB

/-! ### The record states of `F`

The record state space keeps the half-distances `d_i` below the record and the capped local
times `η_i(x)` at relative positions `x ≤ 0`; the paper's `F` is `{d_i = 0 for every i}`,
which is `srSet N m = exh N m 0`. -/

/-- The walk state encoded by a record state: position `-(2 d_i)` relative to the record and
capped local times `η_i`. -/
noncomputable def walkStateOf {N m : ℕ} (y : RecState N m) : WalkState N where
  pos i := -(2 * (y.val.1 i : ℤ))
  ell i x := (y.val.2 i x).val

/-- On `F` the encoded state has exactly the fresh record profile: every walker at the record
level, capped local time `1` there and `0` strictly above. -/
theorem profile_of_srSet {N m : ℕ} (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m) :
    (∀ i, (walkStateOf y).pos i = 0) ∧
      (∀ i, (walkStateOf y).ell i 0 = 1) ∧
      (∀ (i : Fin N) (x : ℤ), 0 < x → (walkStateOf y).ell i x = 0) := by
  have hv : ∀ i, y.val.1 i = 0 := by
    intro i
    have h : dist2 y i ≤ 0 := hy i
    have h3 : dist2 y i = y.val.1 i := rfl
    omega
  have hsec : y.val.2 ∈ secSet N m y.val.1 := y.property.2
  obtain ⟨habove, -, horigin⟩ := hsec
  refine ⟨fun i => by show -(2 * (y.val.1 i : ℤ)) = 0; rw [hv i]; simp, fun i => ?_,
    fun i x hx => ?_⟩
  · have h1 : y.val.2 i 0 = (1 : Fin (m + 1)) := by
      rw [horigin i, if_pos (hv i)]
    show (y.val.2 i 0).val = 1
    rw [h1]
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
  · have h0 : y.val.2 i x = 0 := habove i x hx
    show (y.val.2 i x).val = 0
    rw [h0]
    rfl

/-- The fresh path predicate on the canonical path is the paper's `V`, i.e. `strictPos`. -/
theorem fromV_initial_iff (p : ℝ) (m : ℕ) (U : Array N) :
    FromV p m U (initialWalkState (N := N)) ↔ posPath p m U ∈ strictPos (N := N) := by
  have hpath : posPath p m U
      = fun n i => (trajFrom p m U (initialWalkState (N := N)) n).pos i := by
    funext n i
    rw [posPath, trajectory_eq_trajFrom]
  rw [hpath, SwarmFresh.mem_strictPos]
  exact ⟨fun hV => ⟨fun i => rfl, fun n hn i => hV i n hn⟩,
    fun h i n hn => h.2 n hn i⟩

/-- The fresh event of the canonical start, in the `strictPos` form of `FreshLaw`. -/
theorem initial_set_eq (p : ℝ) (m : ℕ) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | FromV p m U (initialWalkState (N := N)) ∧
        (fun n i => (trajFrom p m U (initialWalkState (N := N)) n).pos i) ∈ B}
      = {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have hpath : ∀ U : Array N,
      (fun n i => (trajFrom p m U (initialWalkState (N := N)) n).pos i) = posPath p m U := by
    intro U
    funext n i
    rw [posPath, trajectory_eq_trajFrom]
  ext U
  rw [mem_ofPred_eq, mem_ofPred_eq, mem_inter_iff, hpath U]
  exact ⟨fun h => ⟨(fromV_initial_iff p m U).mp h.1, h.2⟩,
    fun h => ⟨(fromV_initial_iff p m U).mpr h.1, h.2⟩⟩

/-- **The fresh event from any `y ∈ F` is the canonical fresh event, as a set of arrays.**
`fresh_set_eq` applied to `y` and to the deterministic initial state, whose high profiles
coincide on `F`. -/
theorem fresh_set_eq_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) (B : Set (ℕ → Fin N → ℤ)) :
    {U : Array N | FromV p m U (walkStateOf y) ∧
        (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B}
      = {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  obtain ⟨hpos, hell0, hellup⟩ := profile_of_srSet (N := N) hm hy
  have hell : ∀ (i : Fin N) (x : ℤ), 0 ≤ x →
      (walkStateOf y).ell i x = (initialWalkState (N := N)).ell i x := by
    intro i x hx
    show (walkStateOf y).ell i x = (if x = 0 then 1 else 0)
    rcases lt_or_eq_of_le hx with hlt | heq
    · rw [hellup i x hlt, if_neg (by omega)]
    · subst heq
      rw [hell0 i, if_pos rfl]
  have h0init : ∀ i, (initialWalkState (N := N)).pos i = 0 := fun i => rfl
  rw [fresh_set_eq hpos hell hpos h0init B, initial_set_eq]

/-- **The paper's per-state fresh identity at `d = t = 0`.**  For every `y ∈ F = srSet N m` and
every set `B` of future paths, the mass under the actual array law of

  "the translated future of the trajectory started from `y` stays strictly above the record
   level and lies in `B`"

equals the fresh mass `P(V ∩ B)` of the source — with no factor depending on `y`. -/
theorem fresh_mass_strictPos {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) {B : Set (ℕ → Fin N → ℤ)} :
    (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  rw [fresh_set_eq_srSet (N := N) hm p hy B]

/-- **The paper's mass identity `P_π(A) = π(F) P(V)`, integrated form.**  For every measure `π`
on the record states, the `π`-average over `F = srSet` of the per-state fresh mass of `V` is
`π(F)` times the fresh value `P(V)`: the constant of proportionality does not depend on the
state. -/
theorem mass_identity_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) (π : Measure (RecState N m)) :
    ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y)}
      ∂π
      = π (srSet N m) * (arrayMeasure N) {U : Array N |
          posPath p m U ∈ strictPos (N := N)} := by
  have hcongr : ∀ y ∈ srSet N m,
      (arrayMeasure N) {U : Array N | FromV p m U (walkStateOf y)}
        = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    intro y hy
    have h := fresh_mass_strictPos (N := N) hm p hy (B := univ)
    simpa using h
  rw [setLIntegral_congr_fun (SwarmRec.measurableSet_srSet N m) hcongr,
    setLIntegral_const, mul_comm]

/-- **The paper's factorisation `P_π(X ∈ B | A) = P^*(B)`, per state.**  With `ν` the fresh law
conditioned on `V`, every `y ∈ F` gives the product form `P_y(V ∩ B) = P(V) · ν(B)`. -/
theorem fresh_product_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) (hpv : (arrayMeasure N) {U : Array N |
      posPath p m U ∈ strictPos (N := N)} ≠ 0)
    {B : Set (ℕ → Fin N → ℤ)} (_hB : MeasurableSet B) :
    (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
        * (((arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)})⁻¹
          * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B}) := by
  rw [fresh_mass_strictPos (N := N) hm p hy (B := B), ← mul_assoc,
    ENNReal.mul_inv_cancel hpv (measure_ne_top _ _), one_mul]

/-- **Fresh positivity is uniform on `F`.**  If the fresh probability `P(V)` is positive, then it
is the mass of `V` from *every* simultaneous-record state `y ∈ srSet N m`, not only from the
deterministic initial state.  This is the paper's "all walkers have positive probability of
staying strictly above the record level" after a simultaneous record. -/
theorem fresh_mass_ne_zero_of_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) {y : RecState N m}
    (hy : y ∈ srSet N m) (hpv : (arrayMeasure N) {U : Array N |
      posPath p m U ∈ strictPos (N := N)} ≠ 0) :
    (arrayMeasure N) {U : Array N | FromV p m U (walkStateOf y)} ≠ 0 := by
  have h := fresh_mass_strictPos (N := N) hm p hy (B := univ)
  have h2 : (arrayMeasure N) {U : Array N | FromV p m U (walkStateOf y)}
      = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    simpa using h
  rw [h2]
  exact hpv

end SwarmFreshState

namespace SwarmFreshState

variable {N : ℕ}

/-- **The paper's joint display `P_π(A ∩ {future ∈ B}) = π(F) P(V ∩ B)`, integrated form.**
For every measure `π` on the record states and every set `B` of future paths, the `π`-average
over `F = srSet` of the per-state fresh mass of `V ∩ B` is `π(F)` times the fresh value
`P(V ∩ B)`.  This is the exact form consumed by `areas/kac/StationaryMass.lean`
(`mass_identity` + `factorization`) and hence by the Kac step of `(ED)`. -/
theorem fresh_mass_integral_srSet {N m : ℕ} (hm : 1 ≤ m) (p : ℝ) (π : Measure (RecState N m))
    {B : Set (ℕ → Fin N → ℤ)} :
    ∫⁻ y in srSet N m, (arrayMeasure N) {U : Array N |
        FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B}
      ∂π
      = π (srSet N m) * (arrayMeasure N) {U : Array N |
          posPath p m U ∈ strictPos (N := N) ∩ B} := by
  have hcongr : ∀ y ∈ srSet N m,
      (arrayMeasure N) {U : Array N | FromV p m U (walkStateOf y) ∧
          (fun n i => (trajFrom p m U (walkStateOf y) n).pos i) ∈ B}
        = (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
    fun y hy => fresh_mass_strictPos (N := N) hm p hy (B := B)
  rw [setLIntegral_congr_fun (SwarmRec.measurableSet_srSet N m) hcongr,
    setLIntegral_const, mul_comm]

end SwarmFreshState
