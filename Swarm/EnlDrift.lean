/-
  **The one-step conditional drift of walker `i` on the enlarged filtration.**

  From the conditional right-jump law `condExp_stepUp_enl` we deduce

      (arrayMeasure N)[1{X_{n+1}^i = X_n^i - 1} | enlFilt p m n] =ᵐ 1 - alphaFun p m n i,
      (arrayMeasure N)[(X_{n+1}^i - X_n^i) | enlFilt p m n]       =ᵐ 2 * alphaFun p m n i - 1.

  The second identity is the genuine conditional drift of the paper's martingale
  `M_n^i`: it is a statement about expectations given the enlarged filtration,
  not a fixed-history one-step mass.
-/
import Swarm.EnlJoint

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open Swarming.Transition SwarmCross

variable {N : ℕ}

/-- The indicator of the one-step left-jump event, as a real function. -/
noncomputable def stepDownInd (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : Array N → ℝ :=
  (StepCross.stepDown p m n i).indicator (fun _ => (1 : ℝ))

lemma stepUp_or_stepDown (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    U ∈ StepCross.stepUp p m n i ∨ U ∈ StepCross.stepDown p m n i :=
  StepCross.pos_succ_eq_or p m U n i

lemma not_stepUp_and_stepDown (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    ¬ (U ∈ StepCross.stepUp p m n i ∧ U ∈ StepCross.stepDown p m n i) := by
  rintro ⟨h1, h2⟩
  rw [StepCross.mem_stepUp] at h1
  rw [StepCross.mem_stepDown] at h2
  omega

lemma stepDownInd_eq_one_sub (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (U : Array N) :
    stepDownInd p m n i U = 1 - stepUpInd p m n i U := by
  by_cases h : U ∈ StepCross.stepUp p m n i
  · have h2 : U ∉ StepCross.stepDown p m n i :=
      fun hd => not_stepUp_and_stepDown p m U n i ⟨h, hd⟩
    rw [stepDownInd, Set.indicator_of_notMem h2, stepUpInd, Set.indicator_of_mem h]
    norm_num
  · have h2 : U ∈ StepCross.stepDown p m n i := (stepUp_or_stepDown p m U n i).resolve_left h
    rw [stepDownInd, Set.indicator_of_mem h2, stepUpInd, Set.indicator_of_notMem h]
    norm_num

lemma inc_eq_ind (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (U : Array N) :
    ((trajectory p m U (n + 1)).pos i - (trajectory p m U n).pos i : ℝ) =
      stepUpInd p m n i U - stepDownInd p m n i U := by
  by_cases h : U ∈ StepCross.stepUp p m n i
  · have h2 : U ∉ StepCross.stepDown p m n i :=
      fun hd => not_stepUp_and_stepDown p m U n i ⟨h, hd⟩
    have hp : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + 1 := h
    rw [hp, stepUpInd, Set.indicator_of_mem h, stepDownInd, Set.indicator_of_notMem h2]
    push_cast
    ring
  · have h2 : U ∈ StepCross.stepDown p m n i := (stepUp_or_stepDown p m U n i).resolve_left h
    have hp : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1 := h2
    rw [hp, stepUpInd, Set.indicator_of_notMem h, stepDownInd, Set.indicator_of_mem h2]
    push_cast
    ring

lemma integrable_stepUpInd (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Integrable (stepUpInd p m n i) (arrayMeasure N) := by
  have hstep : MeasurableSet (StepCross.stepUp p m n i) := StepCross.measurable_stepUp p m n i
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator hstep).aestronglyMeasurable) ?_
  filter_upwards with U
  by_cases hU : U ∈ StepCross.stepUp p m n i
  · rw [stepUpInd, Set.indicator_of_mem hU, Real.norm_eq_abs, abs_one]
  · rw [stepUpInd, Set.indicator_of_notMem hU]
    simp

lemma integrable_stepDownInd (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Integrable (stepDownInd p m n i) (arrayMeasure N) := by
  have hstep : MeasurableSet (StepCross.stepDown p m n i) := StepCross.measurable_stepDown p m n i
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator hstep).aestronglyMeasurable) ?_
  filter_upwards with U
  by_cases hU : U ∈ StepCross.stepDown p m n i
  · rw [stepDownInd, Set.indicator_of_mem hU, Real.norm_eq_abs, abs_one]
  · rw [stepDownInd, Set.indicator_of_notMem hU]
    simp

/-- **Conditional left-jump law on the enlarged filtration.** -/
theorem condExp_stepDown_enl (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (i : Fin N) :
    (arrayMeasure N)[stepDownInd p m n i | enlFilt p m n] =ᵐ[arrayMeasure N]
      fun U => 1 - alphaFun p m n i U := by
  classical
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI hsig : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hpt : stepDownInd p m n i =ᵐ[arrayMeasure N]
      ((fun _ : Array N => (1 : ℝ)) - stepUpInd p m n i) :=
    Filter.Eventually.of_forall fun U => stepDownInd_eq_one_sub p m n i U
  have hsub := condExp_sub (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := fun _ : Array N => (1 : ℝ)) (g := stepUpInd (N := N) p m n i)
    (integrable_const (1 : ℝ)) (integrable_stepUpInd p m n i)
  have hconst := condExp_const (μ := arrayMeasure N) (m := enlFilt p m n) hle (1 : ℝ)
  have hone : (arrayMeasure N)[stepUpInd p m n i | enlFilt p m n] =ᵐ[arrayMeasure N]
      alphaFun p m n i := condExp_stepUp_enl p hp0 hp1 i
  calc (arrayMeasure N)[stepDownInd p m n i | enlFilt p m n]
      =ᵐ[arrayMeasure N] (arrayMeasure N)[((fun _ : Array N => (1 : ℝ)) - stepUpInd p m n i) |
            enlFilt p m n] := condExp_congr_ae hpt
    _ =ᵐ[arrayMeasure N] ((arrayMeasure N)[(fun _ : Array N => (1 : ℝ)) | enlFilt p m n] -
          (arrayMeasure N)[stepUpInd p m n i | enlFilt p m n]) := hsub
    _ =ᵐ[arrayMeasure N] ((fun _ : Array N => (1 : ℝ)) - alphaFun p m n i) :=
        (Filter.EventuallyEq.of_eq hconst).sub hone
    _ =ᵐ[arrayMeasure N] (fun U => 1 - alphaFun p m n i U) := Filter.EventuallyEq.of_eq rfl

/-- **Conditional one-step drift of walker `i` on the enlarged filtration.** -/
theorem condExp_inc_enl (p : ℝ) (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (i : Fin N) :
    (arrayMeasure N)[(fun U => ((trajectory p m U (n + 1)).pos i -
        (trajectory p m U n).pos i : ℝ)) | enlFilt p m n] =ᵐ[arrayMeasure N]
      fun U => 2 * alphaFun p m n i U - 1 := by
  classical
  have hpt : (fun U => ((trajectory p m U (n + 1)).pos i -
      (trajectory p m U n).pos i : ℝ)) =ᵐ[arrayMeasure N]
      (fun U => stepUpInd p m n i U - stepDownInd p m n i U) :=
    Filter.Eventually.of_forall fun U => inc_eq_ind p m n i U
  have hsub := condExp_sub (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := stepUpInd (N := N) p m n i) (g := stepDownInd (N := N) p m n i)
    (integrable_stepUpInd p m n i) (integrable_stepDownInd p m n i)
  have hone : (arrayMeasure N)[stepUpInd p m n i | enlFilt p m n] =ᵐ[arrayMeasure N]
      alphaFun p m n i := condExp_stepUp_enl p hp0 hp1 i
  have hdown : (arrayMeasure N)[stepDownInd p m n i | enlFilt p m n] =ᵐ[arrayMeasure N]
      (fun U => 1 - alphaFun p m n i U) := condExp_stepDown_enl p hp0 hp1 i
  calc (arrayMeasure N)[(fun U => ((trajectory p m U (n + 1)).pos i -
        (trajectory p m U n).pos i : ℝ)) | enlFilt p m n]
      =ᵐ[arrayMeasure N] (arrayMeasure N)[(fun U => stepUpInd p m n i U - stepDownInd p m n i U) |
        enlFilt p m n] := condExp_congr_ae hpt
    _
      =ᵐ[arrayMeasure N] ((arrayMeasure N)[stepUpInd p m n i | enlFilt p m n] -
          (arrayMeasure N)[stepDownInd p m n i | enlFilt p m n]) := hsub
    _ =ᵐ[arrayMeasure N] (alphaFun p m n i - fun U => 1 - alphaFun p m n i U) := hone.sub hdown
    _ =ᵐ[arrayMeasure N] (fun U => 2 * alphaFun p m n i U - 1) :=
        Filter.EventuallyEq.of_eq (by
          funext U
          show alphaFun p m n i U - (1 - alphaFun p m n i U) =
            2 * alphaFun p m n i U - 1
          ring)

end Swarming.Enl


