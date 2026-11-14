/-
# Stopped past events are low-block events: the fresh law at a position prefix

`areas/kac/FreshPast.freshlawStrict_record_past` proves the paper's `(freshlaw)` for a past
event `A` that is **already given as a set of low-block arrays** (`A : Set (lowSet d → ℝ)`).
The adaptive attempt-row tower of the paper conditions at the *random* row time `S_q`, so the
past event is available only as a set of arrays decided by the position prefix at `S_q`; the
identification of that set with a low-block set at the row's record level `d` is not supplied
by the public tree (this is the "stopped-history" half of residual R2).

This file supplies exactly that identification, for the actual array law `arrayMeasure N` and
the actual trajectory `Swarming.Trajectory.trajectory`:

* `pfxOf` — the position prefix up to horizon `t` (a finite function, `Pfx N t`);
* `pfx_congr_below` — **the determinism lemma**: two arrays that agree at every coordinate of
  level `< d` produce the same position prefix up to `t`, as long as the first one stays
  strictly below `d` before `t`.  (It is the prefix-level form of
  `FreshLaw.agreeBelow_traj`.)
* `pastRec` / `measurableSet_pastRec` — the low-block form of the stopped event, obtained by
  filling the high block with `0` (`FreshLaw.lowExtend`); measurability is inherited from the
  record event and the finite prefix.
* `pastRec_preimage` / `mem_pastRec_iff` — **the bridge**: for every set `C` of prefixes,
  `{U | RecordAt t d ∧ prefix_t(U) ∈ C} = lowSet d ⁻¹' {V | RecordAt t d ∧ prefix_t(lowExtend V) ∈ C}`.
  Hence "record at `(t,d)` and the past in `C`" **is** a low-block event at level `d`.
* `stopped_escape` — consequently the fresh strict factor applies to every stopped past:
  `μ(past ∧ RecordAt t d ∧ future ∈ strictPos) = P(V) * μ(past ∧ RecordAt t d)`.
* `noReturn_iff_strictPos` — the deterministic row equivalence: at a record at `(t,d)`, "no
  walker ever returns to level `≤ d` after `t`" is literally `relFuture t d ∈ strictPos`
  (whose first clause `X 0 = 0` is exactly the record condition).

Nothing here claims the adaptive tower itself, `μ{InfiniteFailure} = 0`, or a speed.
-/
import Swarm.FreshPast
import Swarm.SeedPos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh
open scoped ENNReal

namespace SwarmStoppedPast

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## The position prefix and its measurability -/

/-- A candidate position prefix of the swarm up to horizon `t`. -/
abbrev Pfx (N n : ℕ) := Fin (n + 1) → Fin N → ℤ

/-- The position prefix up to horizon `t` of the actual trajectory. -/
noncomputable def pfxOf (p : ℝ) (m n : ℕ) (U : Array N) : Pfx N n :=
  fun t => (trajectory p m U t.1).pos

theorem measurable_pfxOf (p : ℝ) (m n : ℕ) : Measurable (pfxOf (N := N) p m n) := by
  refine measurable_pi_iff.mpr (fun t => ?_)
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact (Swarming.Fair.measurable_trajectory p m t.1).1 i

/-! ## A prefix is determined by the low block below the record level -/

/-- **Determinism below a level.**  If two arrays agree at every coordinate of level `< d`,
and the first trajectory stays strictly below `d` before time `t`, then the two position
prefixes up to time `t` agree.  (Positions at time `t` itself are covered: the hypothesis is
`k < t`, and `FreshLaw.agreeBelow_traj` returns full position agreement, not only agreement
below `d`.) -/
theorem pfx_congr_below {p : ℝ} {m : ℕ} {d : ℤ} {U U' : Array N} {t : ℕ}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < d → U (i, x, k) = U' (i, x, k))
    (hbelow : ∀ s, s < t → ∀ i, (trajectory p m U s).pos i < d) :
    pfxOf (N := N) p m t U = pfxOf (N := N) p m t U' := by
  funext s i
  have hsle : s.1 ≤ t := Nat.lt_succ_iff.mp s.2
  exact (agreeBelow_traj (U := U) (U' := U') harr s.1
    (fun k hk => hbelow k (lt_of_lt_of_le hk hsle))).1 i

/-! ## The prefix filtration is nested -/

/-- **The `S_q`/`S_{q+1}` filtration nesting.**  Agreement of the position prefix at a later
horizon implies agreement at every earlier horizon.  This is the inclusion `ℱ_t ⊆ ℱ_{t'}` for
`t ≤ t'` of the position filtration, in the fiber form used by the adaptive tower. -/
theorem pfx_nest {p : ℝ} {m : ℕ} {U U' : Array N} {t t' : ℕ} (htt : t ≤ t')
    (h : pfxOf (N := N) p m t' U = pfxOf (N := N) p m t' U') :
    pfxOf (N := N) p m t U = pfxOf (N := N) p m t U' := by
  funext s i
  have hs : s.1 < t' + 1 := by omega
  exact congrFun (congrFun h ⟨s.1, hs⟩) i

/-- The induced monotonicity of the prefix σ-algebras, in the fiber form: a set that is
decided by the prefix at `t` is decided by the prefix at any later horizon. -/
theorem preimage_pfx_nest {p : ℝ} {m : ℕ} {t t' : ℕ} (htt : t ≤ t') {C : Set (Pfx N t)}
    {U U' : Array N} (h : pfxOf (N := N) p m t' U = pfxOf (N := N) p m t' U')
    (hC : pfxOf (N := N) p m t U ∈ C) : pfxOf (N := N) p m t U' ∈ C := by
  rw [← pfx_nest htt h]
  exact hC

/-! ## The low-block form of a stopped past event -/

/-- The stopped past event "record at `(t,d)` and prefix in `C`", expressed on the low block of
level `d` (the high block is filled with `0` by `FreshLaw.lowExtend`). -/
noncomputable def pastRec (p : ℝ) (m t : ℕ) (d : ℤ) (C : Set (Pfx N t)) :
    Set (lowSet (N := N) d → ℝ) :=
  {V | RecordAt p m (lowExtend (N := N) d V) t d ∧
    pfxOf (N := N) p m t (lowExtend (N := N) d V) ∈ C}

theorem measurableSet_pastRec {p : ℝ} {m t : ℕ} {d : ℤ} {C : Set (Pfx N t)}
    (hC : MeasurableSet C) : MeasurableSet (pastRec (N := N) p m t d C) :=
  ((measurableSet_recordSet p m t d).preimage (measurable_lowExtend d)).inter
    (((measurable_pfxOf (N := N) p m t).comp (measurable_lowExtend d)) hC)

/-- **The bridge.**  A stopped past event at a record is a low-block event at the record
level.  Both directions are `pfx_congr_below` plus `recordAt_congr`; no measurability of `C`
is needed for the identity. -/
theorem pastRec_preimage {p : ℝ} {m t : ℕ} {d : ℤ} (C : Set (Pfx N t)) :
    {U : Array N | RecordAt p m U t d ∧ pfxOf (N := N) p m t U ∈ C}
      = (lowSet (N := N) d).domRestrict ⁻¹'
          pastRec (N := N) p m t d C := by
  ext U
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, pastRec]
  constructor
  · rintro ⟨hrec, hCin⟩
    have hlow := lowExtend_domRestrict_agree (N := N) d U
    refine ⟨(recordAt_congr hlow).mpr hrec, ?_⟩
    have heq := pfx_congr_below (U := U)
      (U' := lowExtend (N := N) d ((lowSet d).domRestrict U))
      (fun i x k hx => (hlow i x k hx).symm) (fun s hs i => hrec.1 s hs i)
    rw [← heq]
    exact hCin
  · rintro ⟨hrec, hCin⟩
    have hlow := lowExtend_domRestrict_agree (N := N) d U
    refine ⟨(recordAt_congr hlow).mp hrec, ?_⟩
    have heq := pfx_congr_below (U := lowExtend (N := N) d ((lowSet d).domRestrict U))
      (U' := U) hlow (fun s hs i => hrec.1 s hs i)
    rw [← heq]
    exact hCin

/-- The membership form of `pastRec_preimage`. -/
theorem mem_pastRec_iff {p : ℝ} {m t : ℕ} {d : ℤ} (C : Set (Pfx N t)) (U : Array N) :
    ((lowSet (N := N) d).domRestrict U ∈ pastRec (N := N) p m t d C) ↔
      (RecordAt p m U t d ∧ pfxOf (N := N) p m t U ∈ C) := by
  have h := congrArg (fun s : Set (Array N) => U ∈ s)
    (pastRec_preimage (N := N) (p := p) (m := m) (t := t) (d := d) C)
  simpa only [Set.mem_ofPred_eq, Set.mem_preimage] using h.to_iff.symm

/-! ## The fresh strict factor at a stopped past -/

/-- **The conditional escape probability at a stopped past event.**  For every measurable set
`C` of prefixes, the mass of "past in `C`, record at `(t,d)`, and no walker ever returns to
level `≤ d`" is `P(V)` times the mass of "past in `C` and record at `(t,d)`".  The factor
`P(V)` does not depend on the past, the time or the level. -/
theorem stopped_escape {p : ℝ} {m t : ℕ} {d : ℤ} {C : Set (Pfx N t)}
    (hC : MeasurableSet C) :
    (arrayMeasure N) {U : Array N | pfxOf (N := N) p m t U ∈ C ∧ RecordAt p m U t d ∧
        relFuture p m U t d ∈ strictPos (N := N)}
      = (arrayMeasure N) {U : Array N | pfxOf (N := N) p m t U ∈ C ∧ RecordAt p m U t d}
        * (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
  have hA := measurableSet_pastRec (N := N) (p := p) (m := m) (t := t) (d := d) hC
  have h := SwarmFreshPast.freshlawStrict_record_past (N := N) p m t d hA (B := univ)
    MeasurableSet.univ
  have hL : {U : Array N | (lowSet (N := N) d).domRestrict U ∈
        pastRec (N := N) p m t d C ∧ RecordAt p m U t d ∧
        relFuture p m U t d ∈ strictPos (N := N) ∩ univ}
      = {U : Array N | pfxOf (N := N) p m t U ∈ C ∧ RecordAt p m U t d ∧
          relFuture p m U t d ∈ strictPos (N := N)} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, and_true,
      mem_pastRec_iff (N := N) (p := p) (m := m) (t := t) (d := d) C U]
    tauto
  have hR : {U : Array N | (lowSet (N := N) d).domRestrict U ∈
        pastRec (N := N) p m t d C ∧ RecordAt p m U t d}
      = {U : Array N | pfxOf (N := N) p m t U ∈ C ∧ RecordAt p m U t d} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
      mem_pastRec_iff (N := N) (p := p) (m := m) (t := t) (d := d) C U]
    tauto
  rw [hL, hR, Set.inter_univ] at h
  exact h

/-! ## The deterministic row equivalence -/

/-- **"No return to the record level" is `strictPos`.**  At a record at `(t,d)` — so every
walker is at `d` at time `t` — the event "every walker stays strictly above `d` at every later
time" is exactly `relFuture t d ∈ strictPos`.  The `X 0 = 0` clause of `strictPos` is the record
condition itself; the `0 < X (n+1)` clause is the no-return condition. -/
theorem noReturn_iff_strictPos {p : ℝ} {m : ℕ} {U : Array N} {t : ℕ} {d : ℤ}
    (hrec : RecordAt p m U t d) :
    (∀ n, t < n → ∀ i, d < (trajectory p m U n).pos i) ↔
      relFuture p m U t d ∈ strictPos (N := N) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun n i => ?_⟩
    · show (trajectory p m U (t + 0)).pos i - d = 0
      rw [Nat.add_zero, hrec.2 i, sub_self]
    · show 0 < (trajectory p m U (t + (n + 1))).pos i - d
      have := h (t + (n + 1)) (by omega) i
      omega
  · rintro ⟨h0, hpos⟩ n htn i
    have h := hpos (n - t - 1) i
    have e1 : t + (n - t - 1 + 1) = n := by omega
    simp only [relFuture] at h
    rw [e1] at h
    omega

end SwarmStoppedPast
