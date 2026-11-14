/-
  **Where the raw increment really is a centred coin, and where the projection defect lives.**

  `QIncCoinDefect` proves the exact pointwise decomposition

      qInc_t = (stepUpInd_t - alphaFun_t) * qAmp_t + qDefect_t

  for the *raw* increment of `QOrthogonalActual.qInc`.  This file localises the defect:

  * `qAlphaMeanH_eq_hZpot`: the enlarged `alpha`-mean `qAlphaMeanH_t` is exactly the paper's
    bracket `alpha * h_j(X_t) - (1 - alpha) * h_j(X_t - 1)` in the actual site-mark
    environment `h_j = envH p m j` and the integer-indexed step `hZpot`.
  * `qDefect_eq_zero_belowRec`: **on the below-record region `X_t^i < M_t^j` the projection
    defect vanishes** — a.e. (`arrayMeasure N`), for every `p ∈ (1/2, 1)`, `m`, `i`, `j`, `eps`.
    The proof is the audited below-record conditional-mean theorem restricted to the event, plus
    the pull-out of the `enlFilt t`-measurable indicator; no new probability is assumed.
  * `qInc_eq_coin_belowRec`: consequently, on the below-record region the raw increment **is**
    the centred coin times the explicit amplitude — exactly, with no projection, no defect.
  * `qInc_sq_eq_coin_variance`: the exact pointwise squared identity with the coin variance
    `alpha (1 - alpha)` split out.  Its `alpha (1 - alpha) * qAmp^2` term is what the dyadic
    variance criterion needs; the defect and cross terms are the honest remainder.
  * `qInc_sq_le_amp_add_defect`: the unconditional pointwise bound `qInc_t^2 <= 2 qAmp_t^2
    + 2 qDefect_t^2` — a raw (not projected) variance reduction.

  None of these statements uses `Qproj` or any optional projection: every object is the raw
  `qInc`/`HpotInc`.  What is **not** proved here (and is not claimed): that the cross terms
  `∫ (stepUpInd_t - alphaFun_t) * qAmp_t ^ 2` and the pairwise covariance vanish.  Both need the
  conditional law of the coin given the read prefix *and* the environment marks, which is the
  exact open input; the pointwise identities below are what that input has to be applied to.
-/
import Swarm.QIncCoinDefect
import Swarm.BelowRecordHpotInc

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmActualBudget

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ## 1. The enlarged `alpha`-mean is the paper's bracket -/

/-- `qAlphaMeanH_t` is `alpha * h_j(X_t) - (1 - alpha) * h_j(X_t - 1)` for the actual
site-mark environment.  Pure algebra on `Hpot_succ_sub'` / `Hpot_pred_sub`. -/
theorem qAlphaMeanH_eq_hZpot (p : ℝ) (m : ℕ) (i j : Fin N) (U : Array N) (t : ℕ) :
    qAlphaMeanH p m i j U t
      = alphaFun p m t i U * hZpot (envH p m j U) ((trajectory p m U t).pos i)
        - (1 - alphaFun p m t i U) * hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) := by
  have h1 : qHup p m i j U t - qHmid p m i j U t
      = hZpot (envH p m j U) ((trajectory p m U t).pos i) := by
    rw [qHup, qHmid]
    exact Hpot_succ_sub' _
  have h2 : qHdown p m i j U t - qHmid p m i j U t
      = -hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) := by
    rw [qHdown, qHmid]
    exact Hpot_pred_sub _
  have e1 : qHup p m i j U t = qHmid p m i j U t
      + hZpot (envH p m j U) ((trajectory p m U t).pos i) := by linarith
  have e2 : qHdown p m i j U t = qHmid p m i j U t
      - hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) := by linarith
  rw [qAlphaMeanH, e1, e2]
  ring

/-! ## 2. The defect vanishes below the record -/

/-- **The projection defect is supported on `{X_t^i >= M_t^j}`.**  On the below-record region the
`enlFilt t`-conditional mean of the raw `HpotInc_t` is already the environment-aware
`alpha`-mean, so `qDefect_t` vanishes there a.e. -/
theorem condExp_HpotInc_eq_qAlphaMeanH_belowRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (t : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ belowRecSet p m t i j →
      condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U
        = qAlphaMeanH p m i j U t := by
  classical
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  have hB : MeasurableSet[enlFilt p m t] (belowRecSet p m t i j) :=
    measurableSet_belowRecSet p m t i j
  have hrec := condExp_HpotInc_belowRec (N := N) (p := p) hp0 hp1 (m := m) (n := t) i j
  have hpull : condExp (enlFilt p m t) (arrayMeasure N)
      (fun U : Array N => (belowRecSet p m t i j).indicator (HpotInc p m t i j) U)
      =ᵐ[arrayMeasure N] (belowRecSet p m t i j).indicator
        (fun U => condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) :=
    condExp_indicator (Budget.integrable_HpotInc hp0 hp1 hpne m t i j) hB
  filter_upwards [hrec, hpull] with U h1 h2 hU
  simp only [Set.indicator_of_mem hU] at h1 h2
  refine h2.symm.trans (h1.trans ?_)
  rw [qAlphaMeanH_eq_hZpot]

/-- On the below-record region the projection defect vanishes a.e. -/
theorem qDefect_eq_zero_of_mem_belowRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} {i j : Fin N} (t : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ belowRecSet p m t i j →
      qDefect p m eps i j U t = 0 := by
  filter_upwards [condExp_HpotInc_eq_qAlphaMeanH_belowRec (N := N) hp0 hp1 (m := m)
    (i := i) (j := j) t] with U hU hmem
  show qAlphaMeanH p m i j U t
    - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U = 0
  rw [hU hmem]
  ring

/-- **The projection defect is supported on `{X_t^i >= M_t^j}`**, in indicator form. -/
theorem qDefect_eq_zero_belowRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} {i j : Fin N} (t : ℕ) :
    (fun U : Array N => (belowRecSet p m t i j).indicator (fun U => qDefect p m eps i j U t) U)
      =ᵐ[arrayMeasure N] 0 := by
  filter_upwards [qDefect_eq_zero_of_mem_belowRec (N := N) hp0 hp1 (m := m) (eps := eps)
    (i := i) (j := j) t] with U hU
  by_cases hmem : U ∈ belowRecSet p m t i j
  · rw [Set.indicator_of_mem hmem]
    exact hU hmem
  · rw [Set.indicator_of_notMem hmem]
    rfl

/-- **On the below-record region the raw increment is exactly the centred coin times the
amplitude**: `qInc_t = (stepUpInd_t - alphaFun_t) * qAmp_t`, a.e. on `{X_t^i < M_t^j}`. -/
theorem qInc_eq_coin_belowRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} {i j : Fin N} (t : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ belowRecSet p m t i j →
      qInc p m eps i j t U
        = (stepUpInd p m t i U - alphaFun p m t i U) * qAmp p m eps i j U t := by
  filter_upwards [qDefect_eq_zero_of_mem_belowRec (N := N) hp0 hp1 (m := m) (eps := eps)
    (i := i) (j := j) t] with U hU hmem
  exact qInc_eq_coin_mul_amp_of_defect_eq_zero p m eps i j U t (hU hmem)

/-- The defect equals its restriction to the complement of the below-record region. -/
theorem qDefect_eq_indicator_compl {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} {i j : Fin N} (t : ℕ) :
    (fun U : Array N => qDefect p m eps i j U t)
      =ᵐ[arrayMeasure N] (belowRecSet p m t i j)ᶜ.indicator
        (fun U => qDefect p m eps i j U t) := by
  filter_upwards [qDefect_eq_zero_of_mem_belowRec (N := N) hp0 hp1 (m := m) (eps := eps)
    (i := i) (j := j) t] with U hU
  by_cases hmem : U ∈ belowRecSet p m t i j
  · rw [hU hmem, Set.indicator_of_notMem (by simpa using hmem)]
  · rw [Set.indicator_of_mem (by simpa using hmem)]

/-! ## 3. The exact squared identity and the raw variance reduction -/

/-- **Exact pointwise squared identity with the coin variance split out**: using
`coin^2 = alpha (1 - alpha) + (1 - 2 alpha) * coin`. -/
theorem qInc_sq_eq_coin_variance (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N)
    (t : ℕ) :
    (qInc p m eps i j t U) ^ 2
      = alphaFun p m t i U * (1 - alphaFun p m t i U) * (qAmp p m eps i j U t) ^ 2
        + (1 - 2 * alphaFun p m t i U)
            * (stepUpInd p m t i U - alphaFun p m t i U)
            * (qAmp p m eps i j U t) ^ 2
        + 2 * (stepUpInd p m t i U - alphaFun p m t i U) * (qAmp p m eps i j U t)
            * (qDefect p m eps i j U t)
        + (qDefect p m eps i j U t) ^ 2 := by
  rw [qInc_sq_eq, coin_sq_eq]
  try ring

/-- **Raw variance reduction (pointwise)**: the squared raw increment is controlled by the
amplitude and the defect, with no projection and no covariance input. -/
theorem qInc_sq_le_amp_add_defect {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (t : ℕ) :
    (qInc p m eps i j t U) ^ 2
      ≤ 2 * (qAmp p m eps i j U t) ^ 2 + 2 * (qDefect p m eps i j U t) ^ 2 := by
  have hα : (0 : ℝ) ≤ alphaFun p m t i U := (alphaFun_mem_Icc hp0 hp1 m t i U).1
  have hα1 : alphaFun p m t i U ≤ 1 := (alphaFun_mem_Icc hp0 hp1 m t i U).2
  have hb : |stepUpInd p m t i U - alphaFun p m t i U| ≤ 1 := by
    have h0 : (0 : ℝ) ≤ stepUpInd p m t i U := by
      by_cases h : U ∈ StepCross.stepUp p m t i
      · simp only [stepUpInd, Set.indicator_of_mem h]; norm_num
      · simp only [stepUpInd, Set.indicator_of_notMem h]; norm_num
    have h1 : stepUpInd p m t i U ≤ 1 := by
      by_cases h : U ∈ StepCross.stepUp p m t i
      · simp only [stepUpInd, Set.indicator_of_mem h]; norm_num
      · simp only [stepUpInd, Set.indicator_of_notMem h]; norm_num
    rw [abs_le]
    constructor <;> linarith
  have hsq : (stepUpInd p m t i U - alphaFun p m t i U) ^ 2 ≤ 1 := by
    have habs := abs_nonneg (stepUpInd p m t i U - alphaFun p m t i U)
    nlinarith [hb, habs, sq_abs (stepUpInd p m t i U - alphaFun p m t i U)]
  rw [qInc_eq_coin_mul_amp_add_defect]
  set c := stepUpInd p m t i U - alphaFun p m t i U with hc
  set A := qAmp p m eps i j U t with hA
  set D := qDefect p m eps i j U t with hD
  have h3 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have h5 : c ^ 2 * A ^ 2 ≤ A ^ 2 := by nlinarith [hsq, h3]
  nlinarith [sq_nonneg (c * A - D), sq_nonneg (c * A), sq_nonneg D, h5]

theorem lintegral_qInc_sq_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) :
    ∫⁻ U, ENNReal.ofReal ((qInc p m eps i j t U) ^ 2) ∂(arrayMeasure N)
      ≤ ∫⁻ U, ENNReal.ofReal (2 * (qAmp p m eps i j U t) ^ 2
          + 2 * (qDefect p m eps i j U t) ^ 2) ∂(arrayMeasure N) := by
  refine lintegral_mono fun U => ?_
  exact ENNReal.ofReal_le_ofReal (qInc_sq_le_amp_add_defect hp0 hp1 m eps i j U t)

end SwarmActualBudget
