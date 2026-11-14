/-
  **DIRECTION B (m2) — the common actual one-step increment `HpotInc`.**

  Two integrated modules describe the same one-step `Hpot` increment of the actual trajectory:

  * `AboveActualDrift` writes it with the `ℕ → ℝ` environment `siteH p m j U`:
        `SwarmOcc.Hpot (siteH p m j U) (X_{n+1}^i) - SwarmOcc.Hpot (siteH p m j U) (X_n^i)`;
  * `RecordTower` packages it as `HpotInc p m n i j U`, built from `envH p m j U`.

  This file shows that `siteH p m j U` and `envH p m j U` are *definitionally* the same
  environment (`Regional.envH` is `fun U u => hof p (siteMarks p m U j) u`, `siteH` is the same
  lambda), so `HpotInc` **is** the `AboveActualDrift` increment and there is no third increment.
  It then restates every `AboveActualDrift` restricted statement for `g ≥ 1` verbatim in terms of
  the single common object `RecordTower.HpotInc`, and re-exports the `RecordTower` record-region
  (`g = 0`) statements under the same common object.

  New content (everything else is a transparent restatement of integrated theorems):

  * `siteH_eq_envH`, `siteH_apply_eq_envH`, `HpotInc_eq_siteH`, `HpotInc_eq_fun`,
    `HpotInc_eq_envH`: the definitional bridge;
  * `HpotInc_eq_jumpSplit`, `HpotInc_apply_eq_jumpSplit`,
    `indicator_HpotInc_eq_indicator_jumpSplit`: the unrestricted jump split of the common
    increment (restatement of `PoissonStep.Hpot_traj_sub`);
  * `integrable_HpotInc`: **unrestricted** integrability of the actual one-step increment
    (from `AboveActualDrift.integrable_Hpot_traj_step`);
  * `measurable_HpotInc`, `aestronglyMeasurable_HpotInc`: ambient measurability of the common
    increment (from the jump split, no integrability needed);
  * `integrable_indicator_HpotInc_abovePosSet`: integrability of the increment restricted to the
    above-record event `A_g`, for every `g` (from the unrestricted integrability and ambient
    measurability of `A_g`);
  * `norm_HpotInc_le`: the deterministic bound `‖HpotInc‖ ≤ 4n + 10`;

  plus the `_HpotInc_abovePosSet*` restatements of the `AboveActualDrift` identities and the
  `_common` re-exports of the `RecordTower` record-region results, and a compiled smoke
  instantiation at `N = 2`, `p = 3/4`, `m = 2`, `i = 0 ≠ 1 = j`, `g = 1`.

  No new probabilistic input, no tower substitution, no conditional-expectation statement beyond
  the restated ones, and no claim about `Q`, occupation, regeneration or Ballistic behaviour.
-/
import Swarm.AboveActualDrift
import Swarm.RecordTower

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### 1. The actual environment: `siteH` and `envH` coincide definitionally -/

/-- `Regional.envH` and `AboveActualDrift.siteH` are the same environment function. -/
theorem siteH_eq_envH (p : ℝ) (m : ℕ) (j : Fin N) : siteH p m j = envH p m j := rfl

/-- Pointwise form of `siteH_eq_envH`. -/
theorem siteH_apply_eq_envH (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) :
    siteH p m j U = envH p m j U := rfl

/-- `envH` is the actual full-history site environment. -/
theorem envH_def_eq (p : ℝ) (m : ℕ) (j : Fin N) :
    envH p m j = fun U u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := rfl

/-! ### 2. The common increment -/

/-- **`RecordTower.HpotInc` is the `AboveActualDrift` increment.**  Written out with `siteH`,
the common increment is exactly the difference of the actual `Hpot` values used in
`AboveActualDrift`. -/
theorem HpotInc_eq_siteH (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    HpotInc p m n i j U =
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

/-- Function-level form of `HpotInc_eq_siteH`. -/
theorem HpotInc_eq_fun (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

/-- `HpotInc` is the difference of the two actual `Hpot` values of the full-history
environment. -/
theorem HpotInc_eq_envH (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U =>
      SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i) := rfl

/-- **The unrestricted jump split of the common increment**: the increment is the up jump times
`hZpot` at the current site minus the down jump times `hZpot` at its predecessor.  Restatement of
`PoissonStep.Hpot_traj_sub` for `HpotInc` (the restricted version on `A_g`, `g ≥ 1`, is
`indicator_HpotInc_abovePosSet_eq` below). -/
theorem HpotInc_eq_jumpSplit (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U =>
      stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1) := by
  funext U
  rw [HpotInc_eq_siteH, Hpot_traj_sub (p := p) (m := m) (n := n) (siteH p m j U) U i]

/-- Pointwise form of `HpotInc_eq_jumpSplit`. -/
theorem HpotInc_apply_eq_jumpSplit (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    HpotInc p m n i j U =
      stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1) :=
  congrFun (HpotInc_eq_jumpSplit p m n i j) U

/-- Restricting the common increment to an arbitrary event is the same as restricting its jump
split.  (Used by the finite offset decomposition, which sums the restricted jump pieces.) -/
theorem indicator_HpotInc_eq_indicator_jumpSplit (p : ℝ) (m n : ℕ) (i j : Fin N)
    (A : Set (Array N)) :
    A.indicator (HpotInc p m n i j) = A.indicator (fun U =>
      stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)) :=
  congrArg (Set.indicator A) (HpotInc_eq_jumpSplit p m n i j)

/-- **Unrestricted integrability of the actual one-step `Hpot` increment.**  Restatement of
`AboveActualDrift.integrable_Hpot_traj_step` for the common object `HpotInc`. -/
theorem integrable_HpotInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (i j : Fin N) :
    Integrable (HpotInc p m n i j) (arrayMeasure N) :=
  integrable_Hpot_traj_step hp0 hp1 hpne m n i j

/-- **Ambient measurability of the common increment**, from the jump split: the two indicators of
the jump sets are measurable, `hZpot` at the (measurable) current site and its predecessor is
measurable.  No integrability hypothesis. -/
theorem measurable_HpotInc (p : ℝ) (m n : ℕ) (i j : Fin N) :
    Measurable (HpotInc p m n i j) := by
  rw [HpotInc_eq_jumpSplit]
  exact ((Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
      (measurable_hZpot_traj p m n j i)).sub
    ((Measurable.indicator measurable_const (StepCross.measurable_stepDown p m n i)).mul
      (measurable_hZpot_traj_pred p m n j i))

/-- `AEStronglyMeasurable` form of `measurable_HpotInc`. -/
theorem aestronglyMeasurable_HpotInc (p : ℝ) (m n : ℕ) (i j : Fin N) :
    AEStronglyMeasurable (HpotInc p m n i j) (arrayMeasure N) :=
  (measurable_HpotInc p m n i j).aestronglyMeasurable

/-- **A deterministic bound on the actual one-step increment**: the increment is the jump-split
expression `1_up hZpot(X_n^i) - 1_down hZpot(X_n^i - 1)`, and each term is bounded by `2n+3`;
hence `‖HpotInc‖ ≤ 2(2n+3) ≤ 4n + 10`. -/
theorem norm_HpotInc_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (i j : Fin N) (U : Array N) :
    ‖HpotInc p m n i j U‖ ≤ 4 * (n : ℝ) + 10 := by
  have hup := abs_stepUpInd_mul_hZpot_traj_le hp0 hp1 hpne m n i j U
  have hdn := abs_stepDownInd_mul_hZpot_pred_traj_le hp0 hp1 hpne m n i j U
  rw [HpotInc_eq_siteH, Real.norm_eq_abs, Hpot_traj_sub (p := p) (m := m) (n := n)
    (siteH p m j U) U i]
  rw [Real.norm_eq_abs] at hup hdn
  have hsplit : |stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
      - stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)|
      ≤ |stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)|
        + |stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)| := by
    have h := abs_add_le
      (stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i))
      (-(stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)))
    rwa [sub_eq_add_neg, abs_neg] at h
  linarith

/-! ### 3. The above-record region `A_g`, `g ≥ 1`, in the common object -/

/-- **The restricted increment is the restricted jump split** (`g ≥ 1`), written with
`HpotInc`.  Restatement of `AboveActualDrift.indicator_Hpot_traj_sub_abovePosSet`. -/
theorem indicator_HpotInc_abovePosSet_eq (p : ℝ) (hp0 : p ≠ 0) {m n : ℕ} (i j : Fin N)
    {g : ℕ} (hg : 1 ≤ g) :
    (abovePosSet p m n i j g).indicator (HpotInc p m n i j)
      = (abovePosSet p m n i j g).indicator
        (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j g U
          - stepDownInd p m n i U * shiftG (H0 p m n j) p m n j (g - 1) U) :=
  indicator_Hpot_traj_sub_abovePosSet p hp0 i j hg

/-- **Integrability of the increment restricted to the above-record event `A_g`.**  Off `A_g` the
function vanishes; on `A_g` it is the unrestricted increment, which is integrable
(`integrable_HpotInc`), and `A_g` is ambient measurable. -/
theorem integrable_indicator_HpotInc_abovePosSet {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Integrable ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) (arrayMeasure N) := by
  have hA : MeasurableSet (abovePosSet p m n i j g) :=
    infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)
  exact (integrable_HpotInc hp0 hp1 hpne m n i j).indicator hA

/-- **The actual one-step `Hpot` drift above the record, successor form, in the common
object.**  For `g = k+1 ≥ 1`,

    `E[1_{A_{k+1}} HpotInc | infoPiece k]`
      `=ᵐ 1_{A_{k+1}} [ alpha (1 + aRec (1 + shiftG H0 k)) - (1 - alpha) shiftG H0 k ]`.

Restatement of `AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet_succ`. -/
theorem condExp_indicator_HpotInc_abovePosSet_succ (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (k : ℕ) :
    condExp (infoPiece (N := N) p m n j k) (arrayMeasure N)
        ((abovePosSet p m n i j (k + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j k U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j k U) :=
  condExp_indicator_Hpot_step_abovePosSet_succ p hp0 hp1 hij k

/-- **The actual one-step `Hpot` drift above the record for any `g ≥ 1`**, at the record
information `infoPiece (g-1)`, in the common object.  Restatement of
`AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet`. -/
theorem condExp_indicator_HpotInc_abovePosSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U) :=
  condExp_indicator_Hpot_step_abovePosSet p hp0 hp1 hij hg

/-- The same identity with the actual site values `h_j(M_n^j + g - 1)` displayed, in the common
object.  Restatement of `AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet_hof`. -/
theorem condExp_indicator_HpotInc_abovePosSet_hof (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                  ((recVal j (prefOf p m n U)).toNat + (g - 1))))
            - (1 - alphaFun p m n i U) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                ((recVal j (prefOf p m n U)).toNat + (g - 1))) :=
  condExp_indicator_Hpot_step_abovePosSet_hof p hp0 hp1 hij hg

/-- **Set-integral form** of the above-record drift in the common object.  Restatement of
`AboveActualDrift.setIntegral_Hpot_step_abovePosSet`. -/
theorem setIntegral_HpotInc_abovePosSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    ∫ U in (abovePosSet p m n i j g), HpotInc p m n i j U ∂(arrayMeasure N)
      = ∫ U in (abovePosSet p m n i j g),
          (alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U)
          ∂(arrayMeasure N) :=
  setIntegral_Hpot_step_abovePosSet p hp0 hp1 hij hg

/-! ### 4. The record region `A_0`, `g = 0`, in the common object

`RecordTower` already states the record-region results for `HpotInc`; the lemmas below are
transparent re-exports under the common API, so that a downstream assembly can cite one file. -/

/-- The restricted record increment is integrable (re-export of
`RecordTower.integrable_indicator_HpotInc_zero`). -/
theorem integrable_indicator_HpotInc_zero_common {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) (i j : Fin N) :
    Integrable ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) (arrayMeasure N) :=
  integrable_indicator_HpotInc_zero hp1 hp2 m n i j

/-- The record-region one-step conditional mean at the record information, for the common
increment (re-export of `RecordTower.condExp_indicator_HpotInc_infoPiece_zero`). -/
theorem condExp_indicator_HpotInc_infoPiece_zero_common (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (infoPiece p m n j 0) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * H0 p m n j U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) :=
  condExp_indicator_HpotInc_infoPiece_zero p hp1 hp2 m n hij

/-- The restricted record identity at `enlFilt n`, for the common increment (re-export of
`RecordTower.condExp_indicator_HpotInc_enlFilt_zero`). -/
theorem condExp_indicator_HpotInc_enlFilt_zero_common (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * eRec p m n j 0 U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) :=
  condExp_indicator_HpotInc_enlFilt_zero p hp1 hp2 m n hij

/-- The restricted record lower bound `1_{A_0}(1 - b_n)` (re-export of
`RecordTower.indicator_le_condExp_indicator_HpotInc_zero`). -/
theorem indicator_le_condExp_indicator_HpotInc_zero_common (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    (fun U => (abovePosSet p m n i j 0).indicator (fun U => 1 - bRec p m n j U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) :=
  indicator_le_condExp_indicator_HpotInc_zero p hp1 hp2 m n hij

/-- The set-integral form of the restricted record bound (re-export of
`RecordTower.setIntegral_le_setIntegral_HpotInc_zero`). -/
theorem setIntegral_le_setIntegral_HpotInc_zero_common (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N)
      ≤ ∫ U in abovePosSet p m n i j 0, HpotInc p m n i j U ∂(arrayMeasure N) :=
  setIntegral_le_setIntegral_HpotInc_zero p hp1 hp2 m n hij

/-! ### 5. Compiled smoke instantiation at `N = 2`, `p = 3/4`, `m = 2`, `i = 0`, `j = 1`,
`g = 1`.

The constants `(1:ℝ)/2 < 3/4`, `3/4 < 1`, `3/4 ≠ 0` and `(0 : Fin 2) ≠ 1` are discharged by
`norm_num` / `decide`; nothing is assumed. -/

/-- Smoke: the unrestricted increment is integrable at `N = 2`, `p = 3/4`, `m = 2`. -/
theorem smoke_integrable_HpotInc :
    Integrable (HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2)) (arrayMeasure 2) :=
  integrable_HpotInc (p := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    2 0 (0 : Fin 2) (1 : Fin 2)

/-- Smoke: the deterministic bound at `N = 2`, `p = 3/4`, `m = 2`, `n = 0`. -/
theorem smoke_norm_HpotInc_le (U : Array 2) :
    ‖HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) U‖
      ≤ 4 * ((0 : ℕ) : ℝ) + 10 :=
  norm_HpotInc_le (p := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    2 0 (0 : Fin 2) (1 : Fin 2) U

/-- Smoke: the above-record restricted increment is integrable at `g = 1`. -/
theorem smoke_integrable_indicator_HpotInc_abovePosSet :
    Integrable ((abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 1).indicator
      (HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2))) (arrayMeasure 2) :=
  integrable_indicator_HpotInc_abovePosSet (p := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 2 0 (0 : Fin 2) (1 : Fin 2) 1

/-- Smoke: the `infoPiece` restricted identity at `g = 1` instantiates with all actual
constants. -/
theorem smoke_condExp_indicator_HpotInc_abovePosSet :
    condExp (infoPiece (N := 2) (3 / 4 : ℝ) 2 0 (1 : Fin 2) 0) (arrayMeasure 2)
        ((abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 1).indicator
          (HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2)))
      =ᵐ[arrayMeasure 2] (abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 1).indicator
          (fun U => alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U
              * (1 + aRec (3 / 4 : ℝ) 2
                  * (1 + shiftG (H0 (3 / 4 : ℝ) 2 0 (1 : Fin 2)) (3 / 4 : ℝ) 2 0
                      (1 : Fin 2) 0 U))
            - (1 - alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U)
                * shiftG (H0 (3 / 4 : ℝ) 2 0 (1 : Fin 2)) (3 / 4 : ℝ) 2 0 (1 : Fin 2) 0 U) :=
  condExp_indicator_HpotInc_abovePosSet (p := (3 / 4 : ℝ)) (m := 2) (n := 0)
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (g := 1)
    (by norm_num) (by norm_num) (by decide) le_rfl

/-- Smoke: the set-integral above-record identity at `g = 1`. -/
theorem smoke_setIntegral_HpotInc_abovePosSet :
    ∫ U in (abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 1),
        HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) U ∂(arrayMeasure 2)
      = ∫ U in (abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 1),
          (alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U
              * (1 + aRec (3 / 4 : ℝ) 2
                  * (1 + shiftG (H0 (3 / 4 : ℝ) 2 0 (1 : Fin 2)) (3 / 4 : ℝ) 2 0
                      (1 : Fin 2) 0 U))
            - (1 - alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U)
                * shiftG (H0 (3 / 4 : ℝ) 2 0 (1 : Fin 2)) (3 / 4 : ℝ) 2 0 (1 : Fin 2) 0 U)
          ∂(arrayMeasure 2) :=
  setIntegral_HpotInc_abovePosSet (p := (3 / 4 : ℝ)) (m := 2) (n := 0)
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (g := 1)
    (by norm_num) (by norm_num) (by decide) le_rfl

/-- Smoke: the record-region `enlFilt` identity at `N = 2`, `p = 3/4`, `m = 2`, `g = 0`. -/
theorem smoke_condExp_indicator_HpotInc_enlFilt_zero :
    condExp (enlFilt (N := 2) (3 / 4 : ℝ) 2 0) (arrayMeasure 2)
        ((abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 0).indicator
          (HpotInc (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2)))
      =ᵐ[arrayMeasure 2] (abovePosSet (3 / 4 : ℝ) 2 0 (0 : Fin 2) (1 : Fin 2) 0).indicator
          (fun U => alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U
              * eRec (3 / 4 : ℝ) 2 0 (1 : Fin 2) 0 U
            - (1 - alphaFun (3 / 4 : ℝ) 2 0 (0 : Fin 2) U)
                * HprevAt (3 / 4 : ℝ) 2 0 (1 : Fin 2) U) :=
  condExp_indicator_HpotInc_enlFilt_zero (p := (3 / 4 : ℝ)) (m := 2) (n := 0)
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by norm_num) (by norm_num) (by decide)

/-! ### 6. Axiom audit -/


end Swarming.Enl
