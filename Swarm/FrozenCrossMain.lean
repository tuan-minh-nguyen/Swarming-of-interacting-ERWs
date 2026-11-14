/-
  **The crossing estimate for the actual frozen walk in the revealed environment.**

  This assembles direction (B) end to end at the actual model: the actual frozen stopped walk
  (`nWalk`, window `[b0, b1+1]`, start at the deterministic time `s`), the bad-time event `A`,
  and the revealed weight family `x ↦ revealedWeight p m · j s x`.  The conclusion is the
  paper's (cross) with the *revealed* environment:

      P(T_{b0}(s) < T_{b1+1}(s) ; A) ≤ ∫_A ∏_{x=b0+1}^{b1} (1 - ω_j(x))/ω_j(x).

  The process fed to the generic layer is `Xtil`, the frozen walk on `A` and the constant
  `b1+1` off `A`.  That modification is what makes the *global* hypotheses of the layer
  (`StepAt`, confinement, `b0 ≤ X_s`) true; it is invisible in the conclusion because the event
  is intersected with `A` and `Xtil = nWalk` on `A`.

  Named inputs, nothing else:
  * `hstepLaw` — the one-step law on the enlarged filtration `enlFilt` (direction (A));
  * `hmeasw` — `enlFilt s`-measurability of `x ↦ revealedWeight p m · j s x` (direction (C)).
-/
import Swarm.CrossLocal
import Swarm.FrozenDomination

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

/-- The process fed to the crossing layer: the frozen walk on `A`, the constant `b1+1` off `A`,
and `0` before the start time `s`. -/
noncomputable def Xtil (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) (A : Set (Array N)) :
    ℕ → Array N → ℕ := by
  classical
  exact fun n U => if s ≤ n then (if U ∈ A then nWalk p m i b0 b1 s n U else b1 + 1) else 0

lemma Xtil_of_mem {p : ℝ} {m : ℕ} {i : Fin N} {b0 b1 s n : ℕ} {A : Set (Array N)}
    {U : Array N} (hsn : s ≤ n) (hU : U ∈ A) :
    Xtil p m i b0 b1 s A n U = nWalk p m i b0 b1 s n U := by
  classical
  unfold Xtil
  rw [if_pos hsn, if_pos hU]

lemma Xtil_of_not_mem {p : ℝ} {m : ℕ} {i : Fin N} {b0 b1 s n : ℕ} {A : Set (Array N)}
    {U : Array N} (hsn : s ≤ n) (hU : U ∉ A) :
    Xtil p m i b0 b1 s A n U = b1 + 1 := by
  classical
  unfold Xtil
  rw [if_pos hsn, if_neg hU]

lemma Xtil_measurable (p : ℝ) (m : ℕ) (i : Fin N) (b0 b1 s : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A) (n : ℕ) :
    Measurable[enlFilt p m n] (Xtil p m i b0 b1 s A n) := by
  classical
  by_cases hsn : s ≤ n
  · have hAn : MeasurableSet[enlFilt p m n] A := (enlFilt p m).mono hsn A hA
    have hgoal : Xtil p m i b0 b1 s A n =
        fun U : Array N => if U ∈ A then nWalk p m i b0 b1 s n U else b1 + 1 := by
      funext U
      by_cases hU : U ∈ A
      · rw [Xtil_of_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
          (A := A) hsn hU, if_pos hU]
      · rw [Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
          (A := A) hsn hU, if_neg hU]
    rw [hgoal]
    exact Measurable.ite hAn (nWalkF_measurable p m i b0 b1 s n) measurable_const
  · have hgoal : Xtil p m i b0 b1 s A n = fun _ => 0 := by
      classical
      funext U; unfold Xtil; rw [if_neg hsn]
    rw [hgoal]; exact measurable_const

/-- The start value of `Xtil` is `b1` on `A`. -/
lemma Xtil_start_mem (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s : ℕ} {A : Set (Array N)}
    {U : Array N} (hU : U ∈ A) (hstart : (trajectory p m U s).pos i = b1) :
    Xtil p m i b0 b1 s A s U = b1 := by
  rw [Xtil_of_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := s)
    (A := A) le_rfl hU]
  have hle : (s : WithTop ℕ) ≤ exitAfterStart p m i b0 b1 s U := exitAfterStart_le p m i b0 b1 s U
  have hz : zWalk p m i b0 b1 s s U = (trajectory p m U s).pos i :=
    stoppedProcess_eq_of_le hle
  show (zWalk p m i b0 b1 s s U).toNat = b1
  rw [hz, hstart]
  simp

/-- `Xtil` has the nearest-neighbour/absorption structure everywhere after the start. -/
lemma Xtil_stepAt (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {A : Set (Array N)} {U : Array N} (hsn : s ≤ n)
    (hstartA : U ∈ A → (trajectory p m U s).pos i = b1) :
    StepAt (Xtil p m i b0 b1 s A) b0 b1 n U := by
  unfold StepAt
  by_cases hU : U ∈ A
  · rw [Xtil_of_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
      (A := A) hsn hU,
      Xtil_of_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n + 1)
      (A := A) (by omega) hU]
    exact stepAt_nWalk p m i hb (hstartA hU) hsn
  · rw [Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
      (A := A) hsn hU,
      Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n + 1)
      (A := A) (by omega) hU]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- `Xtil` stays below `b1+1` after the start. -/
lemma Xtil_range (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {A : Set (Array N)} {U : Array N} (hsn : s ≤ n)
    (hstartA : U ∈ A → (trajectory p m U s).pos i = b1) :
    Xtil p m i b0 b1 s A n U ≤ b1 + 1 := by
  by_cases hU : U ∈ A
  · rw [Xtil_of_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
      (A := A) hsn hU]
    exact (nWalk_bounds p m i hb (hstartA hU) hsn).2
  · rw [Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := n)
      (A := A) hsn hU]

/-- **The crossing estimate for the actual frozen walk in the revealed environment.**

Hypotheses: `hstartA`/`A` (the event on which the frozen walker sits at the top `b1`),
`hmeasw` (direction (C): `x ↦ revealedWeight p m · j s x` is `enlFilt s`-measurable) and
`hdomX`, the revealed-weight domination for the assembled process `Xtil`.  `hdomX` is what
`frozen_hdom_local` provides for `nWalk` on `A`; passing from `nWalk` to `Xtil` needs only the
a.e. transfer of the `enlFilt n`-conditional expectation of `stepRight` along `A`
(`Xtil = nWalk` on `A` at every time `≥ s`, so every `enlFilt n`-subset of `A` has the same
`stepRight` integrals) — that transfer is the one step not carried out here. -/
theorem frozen_cross_prob_le_R (p : ℝ) (m : ℕ) (i j : Fin N) {b0 b1 s : ℕ}
    (hp0 : 1 / 2 < p) (hp1 : p < 1) (hb : b0 < b1) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → (trajectory p m U s).pos i = b1)
    (hmeasw : ∀ x : ℕ, Measurable[enlFilt p m s] (fun U => revealedWF p m j s U x))
    (hdomX : ∀ n, s ≤ n → ∀ᵐ U ∂(arrayMeasure N),
      b0 < Xtil p m i b0 b1 s A n U → Xtil p m i b0 b1 s A n U ≤ b1 →
      revealedWF p m j s U (Xtil p m i b0 b1 s A n U) ≤
        ((arrayMeasure N)[stepRight (Xtil p m i b0 b1 s A) n | enlFilt p m n]) U) :
    (arrayMeasure N).real (exitBottomShift (Xtil p m i b0 b1 s A) b0 b1 s ∩ A)
      ≤ ∫ U in A, R (revealedWF p m j s U) b0 b1 ∂(arrayMeasure N) := by
  classical
  have hp : (1 : ℝ) / 2 ≤ p := le_of_lt hp0
  have hb' : b0 ≤ b1 := le_of_lt hb
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine SwarmSpeedLoc.cross_prob_shift_le_R_local (μ := arrayMeasure N)
    (ℱ := enlFilt p m) (wf := revealedWF p m j s) (X := Xtil p m i b0 b1 s A)
    (hb := hb') (hX := ?_) (hw := hmeasw) (hloh := ?_) (hhih := ?_)
    (hrange := ?_) (hstep := ?_) (hdom := hdomX) (hX0b := ?_) (hstartA := ?_) (hA := hA)
  · exact Xtil_measurable p m i b0 b1 s hA
  · filter_upwards with U x
    exact one_half_le_revealedWeight hp m U j s x
  · filter_upwards with U x
    exact lt_of_le_of_lt (revealedWeight_le_p hp m U j s x) hp1
  · refine hstartA.mono ?_
    intro U hU n hsn
    exact Xtil_range p m i hb hsn hU
  · intro n hsn
    refine hstartA.mono ?_
    intro U hU
    exact Xtil_stepAt p m i hb hsn hU
  · refine hstartA.mono ?_
    intro U hU
    by_cases hmem : U ∈ A
    · rw [Xtil_start_mem p m i hmem (hU hmem)]
      exact le_of_lt hb
    · rw [Xtil_of_not_mem (p := p) (m := m) (i := i) (b0 := b0) (b1 := b1) (s := s) (n := s)
        (A := A) le_rfl hmem]
      exact le_trans (le_of_lt hb) (Nat.le_succ b1)
  · refine hstartA.mono ?_
    intro U hU hmem
    exact Xtil_start_mem p m i hmem (hU hmem)

end SwarmSpeed.Frozen
