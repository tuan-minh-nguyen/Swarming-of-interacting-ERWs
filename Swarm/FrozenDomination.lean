/-
  **Revealed-weight domination for the actual frozen walk.**

  This file assembles, at the actual interacting-ERW path space, the conditional domination
  `(dominate)` that the generic crossing layer consumes.  The deterministic revelation input is
  the verified `Swarming.Trajectory.revealedWeight_le_rightProbability_of_badPos`
  (`Swarm/BadCarrier.lean`): on the bad-time event the revealed environment weight
  at every window site is below walker `i`'s *actual* right probability there, which is exactly
  `SwarmCross.alphaFun`.

  The filtration input is isolated as the single hypothesis `hstepLaw`: the conditional right
  jump law of the original walk on the **enlarged** filtration,
  `μ[1{U_{n,i} ≤ alpha_n^i} | enlFilt n] =ᵐ alpha_n^i` — direction (A).  It is not rebuildable
  from the smaller position filtration `pathMeas`: that σ-algebra is *coarser* than `enlFilt`,
  and a conditional expectation cannot be pushed from a coarser to a finer σ-algebra.

  The conclusion is deliberately **local**: the domination is asserted only on an
  `enlFilt s`-measurable event `A` on which the frozen walker starts at the top `b1`.  A global
  version is false: outside `A` the frozen and original recursions genuinely differ after
  absorption (`inside_nWalk_mul_stepRight_point`).
-/
import Swarm.FrozenBase
import Swarm.CondExpRestrict

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace SwarmSpeed.Frozen

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.Enl Swarming.StepCross SwarmStop SwarmCross

variable {N : ℕ}

/-- The revealed weight at time `s` as a weight family on `ℕ` (the index type the crossing
layer uses for sites). -/
noncomputable def revealedWF (p : ℝ) (m : ℕ) (j : Fin N) (s : ℕ) : Array N → ℕ → ℝ :=
  fun U y => revealedWeight p m U j s (y : ℤ)

/-- **Pointwise interior identity with the event indicator.** -/
theorem indA_inside_step_eq_point (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ} (hb : b0 < b1)
    {A : Set (Array N)} {U : Array N} (hsn : s ≤ n)
    (hstartA : U ∈ A → (trajectory p m U s).pos i = b1) :
    A.indicator (fun _ : Array N => (1 : ℝ)) U *
        (inside (nWalkF p m i b0 b1 s) b0 b1 n U *
          stepRight (nWalkF p m i b0 b1 s) n U) =
      A.indicator (fun _ : Array N => (1 : ℝ)) U *
        (inside (nWalkF p m i b0 b1 s) b0 b1 n U *
          SwarmCross.stepUpInd p m n i U) := by
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU]
    simp only [one_mul]
    exact inside_nWalk_mul_stepRight_point p m i hb hsn (hstartA hU)
  · rw [Set.indicator_of_notMem hU, zero_mul, zero_mul]

/-- **The scaled conditional identity on an `enlFilt s`-event.**
`J · μ[stepRight | enlFilt n] =ᵐ J · alpha_n^i` where `J = 1_A · 1_int`. -/
theorem condExp_stepRight_of_stepLaw (p : ℝ) (m : ℕ) (i : Fin N) {b0 b1 s n : ℕ}
    (hb : b0 < b1) (hsn : s ≤ n) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → (trajectory p m U s).pos i = b1)
    (hstepLaw : (arrayMeasure N)[SwarmCross.stepUpInd p m n i | enlFilt p m n]
      =ᵐ[arrayMeasure N] SwarmCross.alphaFun p m n i) :
    (fun U => (A.indicator (fun _ : Array N => (1 : ℝ)) U *
        inside (nWalkF p m i b0 b1 s) b0 b1 n U) *
        ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n | enlFilt p m n]) U)
      =ᵐ[arrayMeasure N]
    (fun U => (A.indicator (fun _ : Array N => (1 : ℝ)) U *
        inside (nWalkF p m i b0 b1 s) b0 b1 n U) * SwarmCross.alphaFun p m n i U) := by
  classical
  set mu := arrayMeasure N with hmu
  set X := nWalkF p m i b0 b1 s with hXdef
  set J : Array N → ℝ := fun U => A.indicator (fun _ : Array N => (1 : ℝ)) U *
    inside X b0 b1 n U with hJdef
  haveI hprob : IsProbabilityMeasure mu := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI hsig : SigmaFinite (mu.trim hle) := inferInstance
  have hXmeas : ∀ k, Measurable[enlFilt p m k] (X k) := fun k => nWalkF_measurable p m i b0 b1 s k
  have hindA : Measurable (A.indicator (fun _ : Array N => (1 : ℝ))) :=
    measurable_const.indicator ((enlFilt p m).le s A hA)
  have hIns : Measurable (inside X b0 b1 n) := (measurable_insideD hXmeas n).mono hle le_rfl
  have hJmeas : Measurable J := by rw [hJdef]; exact hindA.mul hIns
  have hJnmeas : Measurable[enlFilt p m n] J := by
    rw [hJdef]
    exact ((measurable_const : Measurable[enlFilt p m n] (fun _ : Array N => (1 : ℝ))).indicator
      ((enlFilt p m).mono hsn A hA)).mul (measurable_insideD hXmeas n)
  have hRmeas : Measurable (stepRight X n) := by
    change Measurable (fun U => if X (n + 1) U = X n U + 1 then (1 : ℝ) else 0)
    exact Measurable.ite
      (measurableSet_eq_fun ((hXmeas (n + 1)).mono ((enlFilt p m).le (n + 1)) le_rfl)
        (((hXmeas n).mono ((enlFilt p m).le n) le_rfl).add measurable_const))
      measurable_const measurable_const
  have hSUmeas : Measurable (SwarmCross.stepUpInd p m n i) :=
    measurable_const.indicator (StepCross.measurable_stepUp p m n i)
  have hb1 : ∀ U, ‖stepRight X n U‖ ≤ 1 := fun U => norm_stepRight_le n U
  have hb2 : ∀ U, ‖inside X b0 b1 n U‖ ≤ 1 := fun U => norm_inside_le n U
  have hb3 : ∀ U, ‖SwarmCross.stepUpInd p m n i U‖ ≤ 1 := by
    intro U
    rw [SwarmCross.stepUpInd]
    by_cases hU : U ∈ StepCross.stepUp p m n i
    · rw [Set.indicator_of_mem hU]; simp
    · rw [Set.indicator_of_notMem hU]; simp
  have hbA : ∀ U, ‖A.indicator (fun _ : Array N => (1 : ℝ)) U‖ ≤ 1 := by
    intro U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU]; simp
    · rw [Set.indicator_of_notMem hU]; simp
  have hJb : ∀ U, ‖J U‖ ≤ 1 := by
    intro U
    rw [hJdef]
    simp only [Pi.mul_apply]
    rw [norm_mul]
    calc ‖A.indicator (fun _ : Array N => (1 : ℝ)) U‖ * ‖inside X b0 b1 n U‖ ≤ 1 * 1 :=
          mul_le_mul (hbA U) (hb2 U) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hI3 : Integrable (stepRight X n) mu :=
    Integrable.of_bound hRmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb1)
  have hI4 : Integrable (SwarmCross.stepUpInd p m n i) mu :=
    Integrable.of_bound hSUmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb3)
  have hIJ1 : Integrable (fun U => J U * stepRight X n U) mu := by
    refine Integrable.of_bound ((hJmeas.mul hRmeas).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (fun U => ?_))
    rw [norm_mul]
    calc ‖J U‖ * ‖stepRight X n U‖ ≤ 1 * 1 :=
          mul_le_mul (hJb U) (hb1 U) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hIJ2 : Integrable (fun U => J U * SwarmCross.stepUpInd p m n i U) mu := by
    refine Integrable.of_bound ((hJmeas.mul hSUmeas).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (fun U => ?_))
    rw [norm_mul]
    calc ‖J U‖ * ‖SwarmCross.stepUpInd p m n i U‖ ≤ 1 * 1 :=
          mul_le_mul (hJb U) (hb3 U) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hIJ : Integrable J mu :=
    Integrable.of_bound hJmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hJb)
  have hpt : (fun U => J U * stepRight X n U) =ᵐ[mu]
      (fun U => J U * SwarmCross.stepUpInd p m n i U) := by
    filter_upwards [hstartA] with U hU
    have hkey := indA_inside_step_eq_point p m i hb hsn (A := A) (U := U) hU
    rw [hJdef]
    simp only [Pi.mul_apply]
    calc A.indicator (fun _ : Array N => (1 : ℝ)) U * inside X b0 b1 n U * stepRight X n U
        = A.indicator (fun _ : Array N => (1 : ℝ)) U *
            (inside X b0 b1 n U * stepRight X n U) := by ring
      _ = A.indicator (fun _ : Array N => (1 : ℝ)) U *
            (inside X b0 b1 n U * SwarmCross.stepUpInd p m n i U) := hkey
      _ = A.indicator (fun _ : Array N => (1 : ℝ)) U * inside X b0 b1 n U *
            SwarmCross.stepUpInd p m n i U := by ring
  have e1 : mu[(fun U => J U * stepRight X n U) | enlFilt p m n]
      =ᵐ[mu] mu[(fun U => J U * SwarmCross.stepUpInd p m n i U) | enlFilt p m n] :=
    condExp_congr_ae hpt
  have e2 : mu[(fun U => J U * SwarmCross.stepUpInd p m n i U) | enlFilt p m n]
      =ᵐ[mu] (fun U => J U * (mu[SwarmCross.stepUpInd p m n i | enlFilt p m n]) U) := by
    have h := condExp_mul_of_stronglyMeasurable_left (m := enlFilt p m n)
      hJnmeas.stronglyMeasurable hIJ2 hI4
    filter_upwards [h] with U hU
    exact hU
  have e3 : mu[(fun U => J U * stepRight X n U) | enlFilt p m n]
      =ᵐ[mu] (fun U => J U * (mu[stepRight X n | enlFilt p m n]) U) := by
    have h := condExp_mul_of_stronglyMeasurable_left (m := enlFilt p m n)
      hJnmeas.stronglyMeasurable hIJ1 hI3
    filter_upwards [h] with U hU
    exact hU
  have e4 : (fun U => J U * (mu[SwarmCross.stepUpInd p m n i | enlFilt p m n]) U)
      =ᵐ[mu] (fun U => J U * SwarmCross.alphaFun p m n i U) := by
    filter_upwards [hstepLaw] with U hU
    rw [hU]
  calc (fun U => J U * (mu[stepRight X n | enlFilt p m n]) U)
      =ᵐ[mu] mu[(fun U => J U * stepRight X n U) | enlFilt p m n] := e3.symm
    _ =ᵐ[mu] mu[(fun U => J U * SwarmCross.stepUpInd p m n i U) | enlFilt p m n] := e1
    _ =ᵐ[mu] (fun U => J U * (mu[SwarmCross.stepUpInd p m n i | enlFilt p m n]) U) := e2
    _ =ᵐ[mu] (fun U => J U * SwarmCross.alphaFun p m n i U) := e4

/-- **The revealed-weight domination at the actual model, on the bad-time event.**  Given the
one-step law on the enlarged filtration (direction (A)) and the bad-time event `A`, the frozen
walker's conditional right-jump probability dominates the revealed environment weight at every
interior site it visits at every time `n ≥ s`.  This is `(dominate)`, with the frozen walk
exactly replacing the actual walk inside the window. -/
theorem frozen_hdom_local (p : ℝ) (m : ℕ) (i j : Fin N) {b0 b1 s n : ℕ}
    (hp : 1 / 2 ≤ p) (hb : b0 < b1) (hij : i ≠ j) (hsn : s ≤ n) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m s] A)
    (hstartA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → (trajectory p m U s).pos i = b1)
    (hbadA : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → badPos p m U i j (b1 : ℤ) s)
    (hstepLaw : (arrayMeasure N)[SwarmCross.stepUpInd p m n i | enlFilt p m n]
      =ᵐ[arrayMeasure N] SwarmCross.alphaFun p m n i) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ A →
      b0 < nWalk p m i b0 b1 s n U → nWalk p m i b0 b1 s n U ≤ b1 →
      revealedWF p m j s U (nWalk p m i b0 b1 s n U) ≤
        ((arrayMeasure N)[stepRight (nWalkF p m i b0 b1 s) n | enlFilt p m n]) U := by
  classical
  have hsc := condExp_stepRight_of_stepLaw p m i hb hsn hA hstartA hstepLaw
  filter_upwards [hsc, hstartA, hbadA] with U hscU hstartU hbadU
  intro hU h1 h2
  have hinside : inside (nWalkF p m i b0 b1 s) b0 b1 n U = 1 := by
    simp only [inside, nWalkF]; rw [if_pos ⟨h1, h2⟩]
  have hindA : A.indicator (fun _ : Array N => (1 : ℝ)) U = 1 := Set.indicator_of_mem hU _
  have hJ1 : (A.indicator (fun _ : Array N => (1 : ℝ)) U *
      inside (nWalkF p m i b0 b1 s) b0 b1 n U) = 1 := by
    rw [hindA, hinside, mul_one]
  rw [hJ1, one_mul] at hscU
  have hXeq : (nWalk p m i b0 b1 s n U : ℤ) = (trajectory p m U n).pos i :=
    nWalk_interior_eq_pos p m i hb hsn (hstartU hU) h1 h2
  have hb0 : (0 : ℤ) ≤ (b0 : ℤ) := Int.natCast_nonneg b0
  have hpos0 : (b0 : ℤ) < (trajectory p m U n).pos i := by rw [← hXeq]; exact_mod_cast h1
  have hposb : (trajectory p m U n).pos i ≤ (b1 : ℤ) := by rw [← hXeq]; exact_mod_cast h2
  have hdom := revealedWeight_le_rightProbability_of_badPos (hp := hp) (m := m) (U := U)
    (i := i) (j := j) hij (s := s) (hbadU hU) (t := n) hsn (b0 := (b0 : ℤ)) hb0 hpos0 hposb
  have hwf : revealedWF p m j s U (nWalk p m i b0 b1 s n U)
      = revealedWeight p m U j s ((trajectory p m U n).pos i) := by
    rw [revealedWF, hXeq]
  rw [hwf, hscU]
  simp only [one_mul]
  exact hdom

end SwarmSpeed.Frozen
