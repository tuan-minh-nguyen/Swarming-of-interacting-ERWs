/-
  **Direction (B): the actual frozen stopped walk.**

  This file isolates the *deterministic* layer of the frozen-process argument at the actual
  interacting-ERW path space `Swarming.Uniform.Array N`:

  * `zWalk` / `nWalk`: the actual integer walker frozen at the first exit of the open window
    `(b0, b1+1)` started at the deterministic time `s`;
  * the exact exit boundary (`exit_eq_boundary`) and two-sided confinement
    (`nWalk_bounds`) — these hold for **every** array, not merely almost surely;
  * `stepAt_nWalk`: the homogeneous nearest-neighbour/absorption structure `StepAt` consumed by
    the generic crossing layer of `areas/transience/{Step2,Cross}.lean`;
  * **the interior identification** `nWalk_right_iff_stepUp` and its indicator form
    `inside_nWalk_mul_stepRight`: inside the window the frozen walk and the original walk have
    the same right jumps.  After absorption they genuinely *differ* (the frozen walker stays at
    the boundary, the original keeps jumping), so the identity is only valid after multiplying
    by the interior indicator `inside`.  The scratch statement `condExp_nWalk_right` of
    `.scratch/frozen-cross/Frozen.lean` asserts a **global** identity of the two indicators and
    is false; `interior_necessary` below records a concrete witness on the actual model.
-/
import Swarm.Cross
import Swarm.EnlJump
import Swarm.StepCross
import Swarm.CondExp
import Swarm.BadCarrier

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

/-- First exit from the open interval `(b0,b1+1)`, started at a deterministic time `s`. -/
noncomputable abbrev exitAfterStart (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) :
    Array N → WithTop ℕ :=
  trajExit N p m i (b0 : ℤ) (b1 + 1 : ℕ) (fun _ => (s : WithTop ℕ))

/-- The actual integer-valued walker frozen at the first exit. -/
noncomputable abbrev zWalk (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (n : ℕ) (U : Array N) : ℤ :=
  stoppedProcess (fun k U => (trajectory p m U k).pos i) (exitAfterStart p m i b0 b1 s) n U

/-- The frozen process as a natural number (the object the crossing layer consumes). -/
noncomputable abbrev nWalk (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (n : ℕ) (U : Array N) : ℕ :=
  (zWalk p m i b0 b1 s n U).toNat

/-- The frozen process as a family `ℕ → Array N → ℕ`, i.e. the shape `StepAt`/`Cross` expect. -/
noncomputable abbrev nWalkF (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) :
    ℕ → Array N → ℕ :=
  fun n U => nWalk p m i b0 b1 s n U

lemma exitAfterStart_le (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (U : Array N) :
    (s : WithTop ℕ) ≤ exitAfterStart p m i b0 b1 s U :=
  SwarmStop.le_exitAfter U

lemma isStoppingTime_exitAfterStart (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) :
    IsStoppingTime (enlFilt (N := N) p m) (exitAfterStart p m i b0 b1 s) :=
  isStoppingTime_trajExit_enlFilt p m (isStoppingTime_const _ s)

lemma zWalk_measurable (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (n : ℕ) :
    Measurable[enlFilt p m n] (zWalk p m i b0 b1 s n) := by
  have hu : StronglyAdapted (enlFilt (N := N) p m)
      (fun k U => (trajectory p m U k).pos i) := by
    intro k
    exact (enl_pos_measurable p m k le_rfl i).stronglyMeasurable
  exact (hu.stoppedProcess_of_discrete (isStoppingTime_exitAfterStart p m i b0 b1 s) n).measurable

lemma nWalk_measurable (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (n : ℕ) :
    Measurable[enlFilt p m n] (nWalk p m i b0 b1 s n) :=
  (measurable_of_countable (fun z : ℤ => z.toNat)).comp (zWalk_measurable p m i b0 b1 s n)

lemma nWalkF_measurable (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (n : ℕ) :
    Measurable[enlFilt p m n] (nWalkF p m i b0 b1 s n) :=
  nWalk_measurable p m i b0 b1 s n

/-- A nearest-neighbour walk started inside the interval exits exactly at one of its endpoints. -/
theorem exit_eq_boundary (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s k : ℕ} (hb : b0 < b1)
    {U : Array N} (hstart : (trajectory p m U s).pos i = b1)
    (hk : exitAfterStart p m i b0 b1 s U = (k : WithTop ℕ)) :
    (trajectory p m U k).pos i = b0 ∨ (trajectory p m U k).pos i = b1 + 1 := by
  have hsle : s ≤ k := by
    have h := exitAfterStart_le p m i b0 b1 s U
    rw [hk] at h
    exact_mod_cast h
  have hsne : s ≠ k := by
    intro heq
    have hout := trajExit_eq_coe p m hk
    subst k
    rw [hstart] at hout
    omega
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hsq : s ≤ q := by omega
  have hinterior : (b0 : ℤ) < (trajectory p m U q).pos i ∧
      (trajectory p m U q).pos i < b1 + 1 := by
    refine trajExit_interior (N := N) (σ := fun _ => (s : WithTop ℕ)) (U := U) (k := q) p m ?_ ?_
    · exact_mod_cast hsq
    · change (q : WithTop ℕ) < exitAfterStart p m i b0 b1 s U
      rw [hk]
      exact_mod_cast Nat.lt_succ_self q
  have hout := trajExit_eq_coe p m hk
  rcases StepCross.pos_succ_eq_or p m U q i with hstep | hstep <;>
    rw [hstep] at hout <;> rcases hout with h | h <;> omega

lemma zWalk_bounds (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hstart : (trajectory p m U s).pos i = b1) (hsn : s ≤ n) :
    b0 ≤ zWalk p m i b0 b1 s n U ∧ zWalk p m i b0 b1 s n U ≤ b1 + 1 := by
  by_cases hstop : exitAfterStart p m i b0 b1 s U ≤ (n : WithTop ℕ)
  · have hne : exitAfterStart p m i b0 b1 s U ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hstop
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hk' : exitAfterStart p m i b0 b1 s U = (k : WithTop ℕ) := hk.symm
    have hval : zWalk p m i b0 b1 s n U = (trajectory p m U k).pos i := by
      exact (stoppedProcess_eq_of_ge hstop).trans
        (congrArg (fun t : WithTop ℕ => (trajectory p m U t.untopA).pos i) hk')
    rw [hval]
    rcases exit_eq_boundary p m i hb hstart hk' with h | h <;> omega
  · have hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U := lt_of_not_ge hstop
    have hval : zWalk p m i b0 b1 s n U = (trajectory p m U n).pos i :=
      stoppedProcess_eq_of_le hlt.le
    rw [hval]
    have hinner := trajExit_interior (N := N) (σ := fun _ => (s : WithTop ℕ)) (U := U) (k := n)
      p m (by exact_mod_cast hsn) hlt
    omega

lemma nWalk_bounds (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hstart : (trajectory p m U s).pos i = b1) (hsn : s ≤ n) :
    b0 ≤ nWalk p m i b0 b1 s n U ∧ nWalk p m i b0 b1 s n U ≤ b1 + 1 := by
  obtain ⟨hlo, hhi⟩ := zWalk_bounds p m i hb hstart hsn
  constructor
  · exact Int.toNat_le_toNat hlo
  · exact Int.toNat_le_toNat hhi

lemma nWalk_stable_of_stopped (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {U : Array N} (hstop : exitAfterStart p m i b0 b1 s U ≤ (n : WithTop ℕ)) :
    nWalk p m i b0 b1 s (n + 1) U = nWalk p m i b0 b1 s n U := by
  have hsucc : exitAfterStart p m i b0 b1 s U ≤ (n + 1 : WithTop ℕ) :=
    hstop.trans (by exact_mod_cast Nat.le_succ n)
  have hzNext : zWalk p m i b0 b1 s (n + 1) U =
      (trajectory p m U (exitAfterStart p m i b0 b1 s U).untopA).pos i :=
    stoppedProcess_eq_of_ge hsucc
  have hzCurrent : zWalk p m i b0 b1 s n U =
      (trajectory p m U (exitAfterStart p m i b0 b1 s U).untopA).pos i :=
    stoppedProcess_eq_of_ge hstop
  exact congrArg (fun z : ℤ => z.toNat) (hzNext.trans hzCurrent.symm)

lemma next_coe_le_exit_of_lt (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {U : Array N} (hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U) :
    (n + 1 : WithTop ℕ) ≤ exitAfterStart p m i b0 b1 s U := by
  by_cases htop : exitAfterStart p m i b0 b1 s U = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
    have hk' : exitAfterStart p m i b0 b1 s U = (k : WithTop ℕ) := hk.symm
    rw [hk'] at hlt ⊢
    exact_mod_cast hlt

lemma nWalk_current_of_not_stopped (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {U : Array N} (hsn : s ≤ n) (hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U) :
    (nWalk p m i b0 b1 s n U : ℤ) = (trajectory p m U n).pos i := by
  have hnonneg : 0 ≤ (trajectory p m U n).pos i := by
    have hinner := trajExit_interior (N := N) (σ := fun _ => (s : WithTop ℕ)) (U := U) (k := n)
      p m (by exact_mod_cast hsn) hlt
    omega
  have hval : zWalk p m i b0 b1 s n U = (trajectory p m U n).pos i :=
    stoppedProcess_eq_of_le hlt.le
  exact (congrArg (fun z : ℤ => (z.toNat : ℤ)) hval).trans (Int.toNat_of_nonneg hnonneg)

lemma nWalk_next_of_not_stopped (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {U : Array N} (hsn : s ≤ n) (hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U) :
    (nWalk p m i b0 b1 s (n + 1) U : ℤ) = (trajectory p m U (n + 1)).pos i := by
  have hnext := next_coe_le_exit_of_lt p m i hlt
  have hnonneg : 0 ≤ (trajectory p m U (n + 1)).pos i := by
    have hinner := trajExit_interior (N := N) (σ := fun _ => (s : WithTop ℕ)) (U := U) (k := n)
      p m (by exact_mod_cast hsn) hlt
    have hstep := StepCross.pos_succ_eq_or p m U n i
    omega
  have hval : zWalk p m i b0 b1 s (n + 1) U = (trajectory p m U (n + 1)).pos i :=
    stoppedProcess_eq_of_le hnext
  exact (congrArg (fun z : ℤ => (z.toNat : ℤ)) hval).trans (Int.toNat_of_nonneg hnonneg)

/-- A frozen walker has the nearest-neighbour/absorption structure `StepAt`. -/
theorem stepAt_nWalk (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hstart : (trajectory p m U s).pos i = b1) (hsn : s ≤ n) :
    StepAt (nWalkF p m i b0 b1 s) b0 b1 n U := by
  by_cases hstop : exitAfterStart p m i b0 b1 s U ≤ (n : WithTop ℕ)
  · have hstable := nWalk_stable_of_stopped p m i hstop
    have hne : exitAfterStart p m i b0 b1 s U ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hstop
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hk' : exitAfterStart p m i b0 b1 s U = (k : WithTop ℕ) := hk.symm
    have hval : zWalk p m i b0 b1 s n U = (trajectory p m U k).pos i :=
      (stoppedProcess_eq_of_ge hstop).trans
        (congrArg (fun t : WithTop ℕ => (trajectory p m U t.untopA).pos i) hk')
    rcases exit_eq_boundary p m i hb hstart hk' with hbottom | htop
    · have hnat : nWalk p m i b0 b1 s n U = b0 :=
        congrArg (fun z : ℤ => z.toNat) (hval.trans hbottom)
      exact Or.inr (Or.inl ⟨hnat.le, hstable⟩)
    · have hnat : nWalk p m i b0 b1 s n U = b1 + 1 :=
        congrArg (fun z : ℤ => z.toNat) (hval.trans htop)
      exact Or.inr (Or.inr ⟨hnat, hstable⟩)
  · have hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U := lt_of_not_ge hstop
    have hinner := trajExit_interior (N := N) (σ := fun _ => (s : WithTop ℕ)) (U := U) (k := n)
      p m (by exact_mod_cast hsn) hlt
    have hcur := nWalk_current_of_not_stopped p m i hsn hlt
    have hnext := nWalk_next_of_not_stopped p m i hsn hlt
    refine Or.inl ⟨?_, ?_, ?_⟩
    · have hb0 : (b0 : ℤ) < (nWalk p m i b0 b1 s n U : ℤ) := by
        rw [hcur]; exact hinner.1
      exact_mod_cast hb0
    · have hb1 : (nWalk p m i b0 b1 s n U : ℤ) ≤ (b1 : ℤ) := by
        rw [hcur]; omega
      exact_mod_cast hb1
    · rcases StepCross.pos_succ_eq_or p m U n i with hs | hs
      · left
        have hs' : (nWalk p m i b0 b1 s (n + 1) U : ℤ) =
            (nWalk p m i b0 b1 s n U : ℤ) + 1 := by
          rw [hcur, hnext, hs]
        exact_mod_cast hs'
      · right
        have hs' : (nWalk p m i b0 b1 s (n + 1) U : ℤ) + 1 =
            (nWalk p m i b0 b1 s n U : ℤ) := by
          rw [hcur, hnext, hs]
          omega
        exact_mod_cast hs'

/-- **Interior identification.**  As long as the frozen walker has not exited the window, its
right jump is exactly the original walk's right jump. -/
theorem nWalk_right_iff_stepUp (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    {U : Array N} (hsn : s ≤ n) (hstop : ¬ exitAfterStart p m i b0 b1 s U ≤ (n : WithTop ℕ)) :
    nWalk p m i b0 b1 s (n + 1) U = nWalk p m i b0 b1 s n U + 1 ↔
      U ∈ StepCross.stepUp p m n i := by
  have hlt : (n : WithTop ℕ) < exitAfterStart p m i b0 b1 s U := lt_of_not_ge hstop
  have hcur := nWalk_current_of_not_stopped p m i hsn hlt
  have hnext := nWalk_next_of_not_stopped p m i hsn hlt
  constructor
  · intro h
    calc (trajectory p m U (n + 1)).pos i = (nWalk p m i b0 b1 s (n + 1) U : ℤ) := hnext.symm
      _ = (nWalk p m i b0 b1 s n U : ℤ) + 1 := by exact_mod_cast h
      _ = (trajectory p m U n).pos i + 1 := by rw [hcur]
  · intro h
    have hz : (nWalk p m i b0 b1 s (n + 1) U : ℤ) =
        (nWalk p m i b0 b1 s n U : ℤ) + 1 := by
      calc (nWalk p m i b0 b1 s (n + 1) U : ℤ) = (trajectory p m U (n + 1)).pos i := hnext
        _ = (trajectory p m U n).pos i + 1 := h
        _ = (nWalk p m i b0 b1 s n U : ℤ) + 1 := by rw [hcur]
    exact_mod_cast hz

/-- **An interior value is an unstopped value.**  If the frozen walker sits in the interior
`(b0, b1]` at time `n ≥ s` then the exit has not yet happened.  (After absorption the frozen
value is a boundary value `b0` or `b1+1`.) -/
lemma not_stopped_of_interior (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hstart : (trajectory p m U s).pos i = b1)
    (h1 : b0 < nWalk p m i b0 b1 s n U) (h2 : nWalk p m i b0 b1 s n U ≤ b1) :
    ¬ exitAfterStart p m i b0 b1 s U ≤ (n : WithTop ℕ) := by
  intro hstop
  have hne : exitAfterStart p m i b0 b1 s U ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hstop
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
  have hk' : exitAfterStart p m i b0 b1 s U = (k : WithTop ℕ) := hk.symm
  have hval : zWalk p m i b0 b1 s n U = (trajectory p m U k).pos i :=
    (stoppedProcess_eq_of_ge hstop).trans
      (congrArg (fun t : WithTop ℕ => (trajectory p m U t.untopA).pos i) hk')
  rcases exit_eq_boundary p m i hb hstart hk' with hbottom | htop
  · have hnat : nWalk p m i b0 b1 s n U = b0 :=
      congrArg (fun z : ℤ => z.toNat) (hval.trans hbottom)
    omega
  · have hnat : nWalk p m i b0 b1 s n U = b1 + 1 :=
      congrArg (fun z : ℤ => z.toNat) (hval.trans htop)
    omega

lemma nWalk_interior_eq_pos (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hsn : s ≤ n) (hstart : (trajectory p m U s).pos i = b1)
    (h1 : b0 < nWalk p m i b0 b1 s n U) (h2 : nWalk p m i b0 b1 s n U ≤ b1) :
    (nWalk p m i b0 b1 s n U : ℤ) = (trajectory p m U n).pos i :=
  nWalk_current_of_not_stopped p m i hsn
    (lt_of_not_ge (not_stopped_of_interior p m i hb hstart h1 h2))

/-- **The interior right-jump identity, in usable form.**  For a frozen walker sitting in the
interior of the window, "the frozen walker steps right" and "the original walker steps right"
are the *same* event. -/
theorem nWalk_interior_step_iff (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {U : Array N} (hsn : s ≤ n) (hstart : (trajectory p m U s).pos i = b1)
    (h1 : b0 < nWalk p m i b0 b1 s n U) (h2 : nWalk p m i b0 b1 s n U ≤ b1) :
    (nWalk p m i b0 b1 s (n + 1) U = nWalk p m i b0 b1 s n U + 1 ↔
        U ∈ StepCross.stepUp p m n i) :=
  nWalk_right_iff_stepUp p m i hsn (not_stopped_of_interior p m i hb hstart h1 h2)

/-- **Pointwise indicator form of the interior identification.**  Multiplying by the interior
indicator `inside` makes the frozen right-jump indicator and the original right-jump indicator
the *same* function: inside the window they agree by `nWalk_interior_step_iff`, and outside the
window both products vanish.  This is the precise statement that replaces the false *global*
identity asserted in `.scratch/frozen-cross/Frozen.lean`. -/
theorem inside_nWalk_mul_stepRight_point (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    (hb : b0 < b1) {U : Array N} (hsn : s ≤ n) (hstart : (trajectory p m U s).pos i = b1) :
    inside (nWalkF p m i b0 b1 s) b0 b1 n U * stepRight (nWalkF p m i b0 b1 s) n U =
      inside (nWalkF p m i b0 b1 s) b0 b1 n U * SwarmCross.stepUpInd p m n i U := by
  by_cases hin : b0 < nWalk p m i b0 b1 s n U ∧ nWalk p m i b0 b1 s n U ≤ b1
  · have hiff := nWalk_interior_step_iff p m i hb hsn hstart hin.1 hin.2 (U := U)
    simp only [inside, stepRight, SwarmCross.stepUpInd]
    rw [if_pos hin]
    by_cases hr : U ∈ StepCross.stepUp p m n i
    · rw [if_pos (hiff.mpr hr), Set.indicator_of_mem hr]
    · rw [if_neg (fun h => hr (hiff.mp h)), Set.indicator_of_notMem (fun h => hr h)]
  · simp only [inside]
    rw [if_neg hin]
    ring

/-- **Almost-sure indicator form.**  On the a.e. event that the frozen walker starts at the top
of the window, the interior-indicator-scaled right-jump indicators coincide. -/
theorem inside_nWalk_mul_stepRight_ae (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    (hb : b0 < b1) (hsn : s ≤ n)
    (hstart : ∀ᵐ U ∂(arrayMeasure N), (trajectory p m U s).pos i = b1) :
    (fun U => inside (nWalkF p m i b0 b1 s) b0 b1 n U * stepRight (nWalkF p m i b0 b1 s) n U)
      =ᵐ[arrayMeasure N]
    (fun U => inside (nWalkF p m i b0 b1 s) b0 b1 n U * SwarmCross.stepUpInd p m n i U) := by
  filter_upwards [hstart] with U hU
  exact inside_nWalk_mul_stepRight_point p m i hb hsn hU

end SwarmSpeed.Frozen
