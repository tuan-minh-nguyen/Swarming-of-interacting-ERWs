/-
  **Direction B (m2): the actual one-step Poisson drift, part 2 — pulling adapted
  multipliers out of the jump-set conditional means.**

  `EnlDrift.condExp_stepUp_enl` proves the jump law for *indicators*:
  `(arrayMeasure N)[1{up} | enlFilt p m n] =ᵐ alphaFun`.  The paper's one-step computation
  multiplies that indicator by a *function* of the current state, which is only known to be
  `enlFilt p m n`-measurable when it is below the record.  Here we prove the general form

      (arrayMeasure N)[1{up} * f | enlFilt p m n] =ᵐ alphaFun * f,
      (arrayMeasure N)[1{down} * f | enlFilt p m n] =ᵐ (1 - alphaFun) * f

  for every `enlFilt p m n`-measurable, essentially bounded `f`.  This is the exact
  conditional-independence statement "given `F_n` the next jump of walker `i` is not correlated
  with the adapted part of the environment", and it is *not* a fixed-history mass identity.

  Consequence recorded here: `condExp_drift_of_adapted` — **the one-step drift on an adapted event
  on which the environment values are adapted**: for an `enlFilt p m n`-measurable set `A` on which
  both `hZpot h (X_n^i)` and `hZpot h (X_n^i - 1)` are `enlFilt p m n`-measurable,

      E[1_A (Hpot(X_{n+1}^i) - Hpot(X_n^i)) | F_n]
        =ᵐ 1_A (alpha_n^i hZpot(X_n^i) - (1 - alpha_n^i) hZpot(X_n^i - 1)),

  which is the paper's `(Zdrift)` *on that event*, with the two measurability inputs named
  explicitly.  The negative and the interior region below the record are instances
  (`Regional.lean`); the record and above-record regions are exactly where the hypothesis fails,
  and they are not claimed here.
-/
import Swarm.PoissonStep

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open SwarmCross

variable {N : ℕ}

instance instFiniteArrayMeasure (N : ℕ) : IsFiniteMeasure (arrayMeasure N) :=
  ⟨by haveI := arrayMeasure_isProbabilityMeasure N; exact measure_lt_top _ _⟩

/-! ### Integrability of the jump indicator times a bounded adapted function -/

lemma abs_stepUpInd_le (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    ‖stepUpInd p m n i U‖ ≤ 1 := by
  by_cases hU : U ∈ stepUp p m n i
  · rw [stepUpInd, Set.indicator_of_mem hU]; simp
  · rw [stepUpInd, Set.indicator_of_notMem hU]; simp

lemma abs_stepDownInd_le (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    ‖stepDownInd p m n i U‖ ≤ 1 := by
  by_cases hU : U ∈ stepDown p m n i
  · rw [stepDownInd, Set.indicator_of_mem hU]; simp
  · rw [stepDownInd, Set.indicator_of_notMem hU]; simp

lemma integrable_stepUpInd_mul {p : ℝ} {m n : ℕ} {i : Fin N} {F : Array N → ℝ}
    (hF : Measurable[enlFilt p m n] F) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ U, ‖F U‖ ≤ c) :
    Integrable (fun U => stepUpInd p m n i U * F U) (arrayMeasure N) := by
  have hFamb : Measurable F := fun s hs => (enlFilt p m).le' n (F ⁻¹' s) (hF hs)
  have hmeas : Measurable (fun U => stepUpInd p m n i U * F U) :=
    (Measurable.indicator measurable_const (measurable_stepUp p m n i)).mul hFamb
  refine Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_mul]
  calc |stepUpInd p m n i U| * |F U|
      ≤ 1 * c := by
        apply mul_le_mul (abs_stepUpInd_le p m n i U) (hc U) (abs_nonneg _) (by norm_num)
    _ = c := one_mul c

lemma integrable_stepDownInd_mul {p : ℝ} {m n : ℕ} {i : Fin N} {F : Array N → ℝ}
    (hF : Measurable[enlFilt p m n] F) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ U, ‖F U‖ ≤ c) :
    Integrable (fun U => stepDownInd p m n i U * F U) (arrayMeasure N) := by
  have hFamb : Measurable F := fun s hs => (enlFilt p m).le' n (F ⁻¹' s) (hF hs)
  have hmeas : Measurable (fun U => stepDownInd p m n i U * F U) :=
    (Measurable.indicator measurable_const (measurable_stepDown p m n i)).mul hFamb
  refine Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_mul]
  calc |stepDownInd p m n i U| * |F U|
      ≤ 1 * c := by
        apply mul_le_mul (abs_stepDownInd_le p m n i U) (hc U) (abs_nonneg _) (by norm_num)
    _ = c := one_mul c

/-! ### Pulling an adapted indicator out of a conditional expectation -/

/-- The indicator of an enlarged-filtration event pulls out of the conditional expectation. -/
theorem condExp_indicator_one_mul {p : ℝ} {m n : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m n] A) {g : Array N → ℝ} (hg : Integrable g (arrayMeasure N)) :
    condExp (enlFilt p m n) (arrayMeasure N) (fun U => A.indicator (fun _ => (1 : ℝ)) U * g U)
      =ᵐ[arrayMeasure N] fun U => A.indicator (fun _ => (1 : ℝ)) U
        * condExp (enlFilt p m n) (arrayMeasure N) g U := by
  have hconst : Measurable[enlFilt p m n] (fun _ : Array N => (1 : ℝ)) := measurable_const
  have hf : StronglyMeasurable[enlFilt p m n]
      (fun U : Array N => A.indicator (fun _ => (1 : ℝ)) U) :=
    (hconst.indicator hA).stronglyMeasurable
  refine condExp_stronglyMeasurable_mul_of_bound (m := enlFilt p m n)
    ((enlFilt p m).le n) hf hg 1 (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU]; simp
  · rw [Set.indicator_of_notMem hU]; simp

/-! ### The jump-set conditional means with an adapted multiplier -/

/-- **Up-jump conditional mean with an adapted multiplier.** -/
theorem condExp_stepUp_mul_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (i : Fin N) {f : Array N → ℝ}
    (hf : Measurable[enlFilt p m n] f) (c : ℝ) (hc : ∀ U, ‖f U‖ ≤ c) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => stepUpInd p m n i U * f U)
      =ᵐ[arrayMeasure N] fun U => alphaFun p m n i U * f U := by
  have hcomm : condExp (enlFilt p m n) (arrayMeasure N) (fun U => stepUpInd p m n i U * f U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => f U * stepUpInd p m n i U) :=
    condExp_congr_ae (Filter.Eventually.of_forall fun U => mul_comm _ _)
  have hpull := condExp_stronglyMeasurable_mul_of_bound (m := enlFilt p m n)
    ((enlFilt p m).le n) (f := f) (g := stepUpInd p m n i) hf.stronglyMeasurable
    (integrable_stepUpInd p m n i) c (Filter.Eventually.of_forall hc)
  have hα := condExp_stepUp_enl p hp0 hp1 (m := m) (n := n) i
  refine hcomm.trans (hpull.trans ?_)
  filter_upwards [hα] with U hU
  rw [Pi.mul_apply, hU, mul_comm]

/-- **Down-jump conditional mean with an adapted multiplier.** -/
theorem condExp_stepDown_mul_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {n : ℕ} (i : Fin N) {f : Array N → ℝ}
    (hf : Measurable[enlFilt p m n] f) (c : ℝ) (hc : ∀ U, ‖f U‖ ≤ c) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => stepDownInd p m n i U * f U)
      =ᵐ[arrayMeasure N] fun U => (1 - alphaFun p m n i U) * f U := by
  have hcomm : condExp (enlFilt p m n) (arrayMeasure N) (fun U => stepDownInd p m n i U * f U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => f U * stepDownInd p m n i U) :=
    condExp_congr_ae (Filter.Eventually.of_forall fun U => mul_comm _ _)
  have hpull := condExp_stronglyMeasurable_mul_of_bound (m := enlFilt p m n)
    ((enlFilt p m).le n) (f := f) (g := stepDownInd p m n i) hf.stronglyMeasurable
    (integrable_stepDownInd p m n i) c (Filter.Eventually.of_forall hc)
  have hα := condExp_stepDown_enl p hp0 hp1 (m := m) (n := n) i
  refine hcomm.trans (hpull.trans ?_)
  filter_upwards [hα] with U hU
  rw [Pi.mul_apply, hU, mul_comm]

/-! ### The one-step drift on an adapted event -/

/-- The pointwise identity behind `condExp_drift_of_adapted`: on an adapted event `A`, the
restricted potential increment only sees the restricted (hence adapted) potential steps. -/
lemma indicator_Hpot_sub_eq {p : ℝ} {m n : ℕ} (h : Array N → ℕ → ℝ) (i : Fin N)
    {A : Set (Array N)} :
    (fun U => A.indicator (fun U => SwarmOcc.Hpot (h U) ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot (h U) ((trajectory p m U n).pos i)) U)
      = fun U => stepUpInd p m n i U
          * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U)
        - stepDownInd p m n i U
          * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U) := by
  funext U
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU,
      Hpot_traj_sub (h U) U i]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

/-- **The one-step Poisson drift of the actual potential on an adapted event.**

For an `enlFilt p m n`-measurable event `A` on which both integer-indexed potential steps
`hZpot h (X_n^i)` and `hZpot h (X_n^i - 1)` are `enlFilt p m n`-measurable (with the bound `c`),
the conditional mean of the potential increment is the paper's

    `alpha_n^i hZpot h (X_n^i) - (1 - alpha_n^i) hZpot h (X_n^i - 1)`

on `A`, and `0` off `A`.  This is `(Zdrift)` restricted to `A`; the two measurability inputs are
the *only* hypotheses, and they are what fails at and above the running record. -/
theorem condExp_drift_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} (h : Array N → ℕ → ℝ) (i : Fin N) {A : Set (Array N)}
    (hA : MeasurableSet[enlFilt p m n] A)
    (hup : Measurable[enlFilt p m n]
      (fun U => A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U))
    (hdn : Measurable[enlFilt p m n]
      (fun U => A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U))
    (c : ℝ) (hc0 : 0 ≤ c)
    (hcup : ∀ U, ‖A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U‖ ≤ c)
    (hcdn : ∀ U, ‖A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U‖ ≤ c) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => A.indicator
          (fun U => SwarmOcc.Hpot (h U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (h U) ((trajectory p m U n).pos i)) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => alphaFun p m n i U * hZpot (h U) ((trajectory p m U n).pos i)
          - (1 - alphaFun p m n i U) * hZpot (h U) ((trajectory p m U n).pos i - 1)) U := by
  rw [indicator_Hpot_sub_eq h i]
  have hupc : condExp (enlFilt p m n) (arrayMeasure N) (fun U => stepUpInd p m n i U
        * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U))
      =ᵐ[arrayMeasure N] fun U => alphaFun p m n i U
        * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U) :=
    condExp_stepUp_mul_of_adapted hp0 hp1 i hup c hcup
  have hdnc : condExp (enlFilt p m n) (arrayMeasure N) (fun U => stepDownInd p m n i U
        * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U))
      =ᵐ[arrayMeasure N] fun U => (1 - alphaFun p m n i U)
        * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U) :=
    condExp_stepDown_mul_of_adapted hp0 hp1 i hdn c hcdn
  have hsub := condExp_sub (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := fun U => stepUpInd p m n i U
      * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i)) U))
    (g := fun U => stepDownInd p m n i U
      * (A.indicator (fun U => hZpot (h U) ((trajectory p m U n).pos i - 1)) U))
    (integrable_stepUpInd_mul hup hc0 hcup) (integrable_stepDownInd_mul hdn hc0 hcdn)
  refine hsub.trans ?_
  filter_upwards [hupc, hdnc] with U h1 h2
  rw [Pi.sub_apply, h1, h2]
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

end Swarming.Enl


