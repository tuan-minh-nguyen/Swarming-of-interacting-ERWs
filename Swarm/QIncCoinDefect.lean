/-
  **Raw-increment coin / defect decomposition (actual model, no projection).**

  The raw increment of the ledger compensator is

      qInc_t = Qcomp(t+1) - Qcomp t = HpotInc_t - Cinc_t - Edrift_t ,

  with `HpotInc_t = H_j(X_{t+1}^i) - H_j(X_t^i)` the increment of the *environment* potential,
  `Cinc_t` the correction increment and `Edrift_t` the ledger drift.  This file proves that it
  splits **pointwise in the array** as

      qInc_t = (stepUpInd_t - alphaFun_t) * qAmp_t + qDefect_t ,

  where

  * `qAmp_t = (H_j(X_t+1) - H_j(X_t-1)) - (F_{b_t}(g_t+1) - F_{b_t}(g_t-1))` is the *amplitude* of
    the raw step (`g_t = X_t^i - M_t^j`), an explicit function of the read prefix at time `t` and of
    the environment marks of walker `j` only;
  * `stepUpInd_t - alphaFun_t` is the (centred) coin of the step, `alphaFun_t` the actual
    right-jump probability;
  * `qDefect_t = alphaMeanH_t - E[HpotInc_t | enlFilt t]` is the **projection defect** of the
    environment potential: the gap between the `enlFilt t`-conditional mean of `HpotInc_t` and the
    *enlarged* mean `alphaMeanH_t = alpha H_j(X_t+1) + (1-alpha) H_j(X_t-1) - H_j(X_t)`, which is
    built from the environment values that `enlFilt t` cannot see.

  Nothing here is projected: `qInc` is the raw increment of `QOrthogonalActual`.  Nothing here is
  assumed: both identities are pure pointwise algebra on top of `Qcomp_succ_sub`, `Zpot_add_J` and
  the definitions of `Cinc`, `corrDrift`, `Edrift`.  The *measure-theoretic* consequences
  (orthogonality, variance) need one further input — the conditional law of the coin given the
  prefix **and** the environment marks — which is not claimed in this file.
-/
import Swarm.QOrthogonalActual

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmActualBudget

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ## 1. The five explicit values entering the decomposition -/

/-- The environment potential one step **up** from the current position: `H_j(X_t^i + 1)`. -/
noncomputable def qHup (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i + 1)

/-- The environment potential one step **down** from the current position: `H_j(X_t^i - 1)`. -/
noncomputable def qHdown (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i - 1)

/-- The environment potential at the current position: `H_j(X_t^i)`. -/
noncomputable def qHmid (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)

/-- `F_{b_t}` at the up-gap `g_t + 1`. -/
noncomputable def qFup (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
    ((trajectory p m U t).pos i + 1 - runMax p m U j t)

/-- `F_{b_t}` at the down-gap `g_t - 1`. -/
noncomputable def qFdown (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
    ((trajectory p m U t).pos i - 1 - runMax p m U j t)

/-- `F_{b_t}` at the current gap `g_t`. -/
noncomputable def qFmid (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
    ((trajectory p m U t).pos i - runMax p m U j t)

/-- **The amplitude of the raw step**: the difference of the up/down environment potentials
minus the difference of the up/down corrections. -/
noncomputable def qAmp (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  (qHup p m i j U t - qHdown p m i j U t) - (qFup p m eps i j U t - qFdown p m eps i j U t)

/-- **The enlarged (environment-aware) conditional mean of the `H` increment**:
`alpha H_j(X_t+1) + (1-alpha) H_j(X_t-1) - H_j(X_t)`. -/
noncomputable def qAlphaMeanH (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  alphaFun p m t i U * qHup p m i j U t + (1 - alphaFun p m t i U) * qHdown p m i j U t
    - qHmid p m i j U t

/-- **The projection defect** of the environment potential: the enlarged conditional mean of
`HpotInc_t` minus its actual `enlFilt t`-conditional mean. -/
noncomputable def qDefect (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) : ℝ :=
  qAlphaMeanH p m i j U t
    - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U

/-! ## 2. The `H` part and the correction part, split along the step -/

/-- `HpotInc_t` is the `alpha`-mean plus `(stepUpInd - alpha)` times the up/down gap. -/
theorem HpotInc_eq_alphaMean_add (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) :
    HpotInc p m t i j U
      = qAlphaMeanH p m i j U t
        + (stepUpInd p m t i U - alphaFun p m t i U)
            * (qHup p m i j U t - qHdown p m i j U t) := by
  have hcases := StepCross.pos_succ_eq_or p m U t i
  by_cases hup : U ∈ StepCross.stepUp p m t i
  · have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hup
    have hind : stepUpInd p m t i U = 1 := by
      rw [stepUpInd, Set.indicator_of_mem hup]
    rw [HpotInc_def, hpos, hind, qAlphaMeanH, qHup, qHmid, qHdown]
    try ring
  · have hdown : U ∈ StepCross.stepDown p m t i :=
      hcases.resolve_left hup
    have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hdown
    have hind : stepUpInd p m t i U = 0 := by
      rw [stepUpInd, Set.indicator_of_notMem hup]
    rw [HpotInc_def, hpos, hind, qAlphaMeanH, qHup, qHmid, qHdown]
    try ring

/-- `Cinc_t` is the correction drift plus `(stepUpInd - alpha)` times the up/down gap of `F`. -/
theorem Cinc_eq_corrDrift_add (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    Cinc p m eps i j U t
      = corrDrift (aRec p m) eps (alphaFun p m t i U) (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t)
        + (stepUpInd p m t i U - alphaFun p m t i U)
            * (qFup p m eps i j U t - qFdown p m eps i j U t) := by
  have hcases := StepCross.pos_succ_eq_or p m U t i
  by_cases hup : U ∈ StepCross.stepUp p m t i
  · have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hup
    have hind : stepUpInd p m t i U = 1 := by
      rw [stepUpInd, Set.indicator_of_mem hup]
    rw [Cinc, hpos, hind, corrDrift, qFup, qFdown]
    try ring
  · have hdown : U ∈ StepCross.stepDown p m t i := hcases.resolve_left hup
    have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hdown
    have hind : stepUpInd p m t i U = 0 := by
      rw [stepUpInd, Set.indicator_of_notMem hup]
    rw [Cinc, hpos, hind, corrDrift, qFup, qFdown]
    try ring

/-! ## 3. The raw increment as coin × amplitude plus the projection defect -/

/-- **The exact coin/defect decomposition of the raw increment** (pointwise in the array):

    qInc_t = (stepUpInd_t - alphaFun_t) * qAmp_t + qDefect_t . -/
theorem qInc_eq_coin_mul_amp_add_defect (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (U : Array N) (t : ℕ) :
    qInc p m eps i j t U
      = (stepUpInd p m t i U - alphaFun p m t i U) * qAmp p m eps i j U t
        + qDefect p m eps i j U t := by
  have hZJ : qInc p m eps i j t U
      = HpotInc p m t i j U - Cinc p m eps i j U t - Edrift p m eps (fun s => alphaFun p m s i) i j U t := by
    rw [qInc, Qcomp_succ_sub p m eps (fun s => alphaFun p m s i) i j U t, Zpot_add_J]
  rw [hZJ, Edrift, HpotInc_eq_alphaMean_add, Cinc_eq_corrDrift_add, qAmp, qDefect]
  try ring

/-- If the projection defect vanishes at `t`, the raw increment **is** the centred coin times the
explicit amplitude. -/
theorem qInc_eq_coin_mul_amp_of_defect_eq_zero (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (U : Array N) (t : ℕ) (h : qDefect p m eps i j U t = 0) :
    qInc p m eps i j t U
      = (stepUpInd p m t i U - alphaFun p m t i U) * qAmp p m eps i j U t := by
  rw [qInc_eq_coin_mul_amp_add_defect, h, add_zero]

/-- The squared raw increment in terms of the coin, the amplitude and the defect (pointwise). -/
theorem qInc_sq_eq (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    (qInc p m eps i j t U) ^ 2
      = (stepUpInd p m t i U - alphaFun p m t i U) ^ 2 * (qAmp p m eps i j U t) ^ 2
        + 2 * (stepUpInd p m t i U - alphaFun p m t i U) * (qAmp p m eps i j U t)
            * (qDefect p m eps i j U t)
        + (qDefect p m eps i j U t) ^ 2 := by
  rw [qInc_eq_coin_mul_amp_add_defect]
  try ring

/-- **The coin is exactly centred** in the sense that the two-point structure of the step is
`alpha`/`(1 - alpha)`: `coin^2 = alpha (1 - alpha) + (1 - 2 alpha) * coin`. -/
theorem coin_sq_eq (p : ℝ) (m : ℕ) (i : Fin N) (U : Array N) (t : ℕ) :
    (stepUpInd p m t i U - alphaFun p m t i U) ^ 2
      = alphaFun p m t i U * (1 - alphaFun p m t i U)
        + (1 - 2 * alphaFun p m t i U)
            * (stepUpInd p m t i U - alphaFun p m t i U) := by
  have hcases := StepCross.pos_succ_eq_or p m U t i
  by_cases hup : U ∈ StepCross.stepUp p m t i
  · have hind : stepUpInd p m t i U = 1 := by
      rw [stepUpInd, Set.indicator_of_mem hup]
    rw [hind]; try ring
  · have hind : stepUpInd p m t i U = 0 := by
      rw [stepUpInd, Set.indicator_of_notMem hup]
    rw [hind]; try ring

/-- **The amplitude in terms of the potential steps**: the difference of the up/down potentials is
`h_j(X_t) + h_j(X_t - 1)` (i.e. `Hpot_succ_sub'` plus `Hpot_pred_sub`), so

    qAmp_t = h_j(X_t^i) + h_j(X_t^i - 1) - (F_{b_t}(g_t+1) - F_{b_t}(g_t-1)) . -/
theorem qAmp_eq_hZpot (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    qAmp p m eps i j U t
      = hZpot (envH p m j U) ((trajectory p m U t).pos i)
        + hZpot (envH p m j U) ((trajectory p m U t).pos i - 1)
        - (qFup p m eps i j U t - qFdown p m eps i j U t) := by
  have h1 : qHup p m i j U t - qHmid p m i j U t
      = hZpot (envH p m j U) ((trajectory p m U t).pos i) := by
    rw [qHup, qHmid]
    exact Hpot_succ_sub' _
  have h2 : qHdown p m i j U t - qHmid p m i j U t
      = -hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) := by
    rw [qHdown, qHmid]
    exact Hpot_pred_sub _
  rw [qAmp]
  linarith

end SwarmActualBudget
