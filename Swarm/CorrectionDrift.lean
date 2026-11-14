/-
  **DIRECTION F (m6) — `CorrectionDrift.lean`: the correction drift is the `enlFilt`
  conditional mean of the correction increment.**

  `VdriftTimeAssembly.compensator_of_correction` reduced the compensator identification
  `E_t = condExp (enlFilt t) (Z_{t+1} - Z_t + J_{t+1})` to the single identity

      condExp (enlFilt p m t) μ (Cinc t)  =ᵐ  corrDrift (aRec p m) eps (alpha_n^i) (b_n) (g_n),

  where `Cinc t = F_{b_t}(X_{t+1}^i - M_t^j) - F_{b_t}(X_t^i - M_t^j)` and
  `corrDrift a eps alpha b g = alpha F_b(g+1) + (1-alpha) F_b(g-1) - F_b(g)`.

  This file discharges that identity with no hypotheses beyond `1/2 < p < 1` and `0 < eps`.
  The ingredients, all already integrated:

  * `b_n` (`bRec`) is `enlFilt p m t`-measurable, unconditionally
    (`BelowRecord.measurable_HprevAt_enlFilt`), and bounded by `2t+5`
    (`RecordAbove.abs_HprevAt_le`);
  * the running record is `enlFilt`-measurable (`BelowMeas.measurableSet_runMax_eq`, by fibres);
  * the step indicators have the conditional laws `alpha_n^i` and `1 - alpha_n^i`
    (`PullOut.condExp_stepUp_mul_of_adapted`, `condExp_stepDown_mul_of_adapted`), with
    `1/2 <= alpha_n^i` (`InteriorBound.one_half_le_alphaFun`);
  * `F_b` is bounded by `b^2/(eps (1-a)^2)` (`SwarmOcc.Fcorr_abs_le`).

  The one-sided arithmetic `alpha F_b(g+1) + (1-alpha) F_b(g-1) - F_b(g) <= FbRHS` is *not*
  used here: that is `(Fdrift)` (`Fcorr_coin_drift`).  The identity below is exact, and it is
  what turns `VdriftTimeAssembly.Edrift` into a genuine compensator drift.
-/
import Swarm.VdriftTimeAssembly
import Swarm.PullOut
import Swarm.BelowMeas

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace VdriftAssembly

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-- `enlFilt`-measurability implies ambient measurability (`enlFilt p m n <= ambient`). -/
theorem measurable_ambient_of_enl {p : ℝ} {m n : ℕ} {f : Array N → ℝ}
    (h : Measurable[enlFilt p m n] f) : Measurable f := by
  intro s hs
  exact (enlFilt p m).le n (f ⁻¹' s) (h hs)

/-! ## 1. The two correction steps, in closed form -/

/-- The up-jump correction step `F_b(g+1) - F_b(g)` at the frozen record cost and record. -/
noncomputable def CstepUp (p : ℝ) (m t : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t + 1)
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)

/-- The down-jump correction step `F_b(g-1) - F_b(g)`. -/
noncomputable def CstepDown (p : ℝ) (m t : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) : ℝ :=
  SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t - 1)
    - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t)

/-- **The correction increment on the two jump sets**:
`Cinc t = 1{up} (F_b(g+1) - F_b(g)) + 1{down} (F_b(g-1) - F_b(g))`. -/
theorem Cinc_eq_inds (p : ℝ) (m t : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) :
    Cinc p m eps i j U t
      = stepUpInd p m t i U * CstepUp p m t eps i j U
        + stepDownInd p m t i U * CstepDown p m t eps i j U := by
  by_cases hup : U ∈ StepCross.stepUp p m t i
  · have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hup
    have hdn : U ∉ StepCross.stepDown p m t i :=
      fun hd => not_stepUp_and_stepDown p m U t i ⟨hup, hd⟩
    have harg : (trajectory p m U t).pos i + 1 - runMax p m U j t
        = (trajectory p m U t).pos i - runMax p m U j t + 1 := by ring
    rw [Cinc, hpos, harg, CstepUp, stepUpInd, Set.indicator_of_mem hup, CstepDown,
      stepDownInd, Set.indicator_of_notMem hdn]
    ring
  · have hdn : U ∈ StepCross.stepDown p m t i := (stepUp_or_stepDown p m U t i).resolve_left hup
    have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hdn
    have harg : (trajectory p m U t).pos i - 1 - runMax p m U j t
        = (trajectory p m U t).pos i - runMax p m U j t - 1 := by ring
    rw [Cinc, hpos, harg, CstepUp, CstepDown, stepUpInd, Set.indicator_of_notMem hup,
      stepDownInd, Set.indicator_of_mem hdn]
    ring

/-! ## 2. `enlFilt`-measurability of the record-ledger components -/

/-- The running record is `enlFilt p m n`-measurable (countably many values, measurable fibres). -/
theorem measurable_runMax_enl (p : ℝ) (m n : ℕ) (j : Fin N) :
    Measurable[enlFilt p m n] (fun U : Array N => runMax p m U j n) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  exact measurable_to_countable' (fun y => measurableSet_runMax_eq p m n j y)

/-- The gap `g_n = X_n^i - M_n^j` is `enlFilt p m n`-measurable. -/
theorem measurable_gap_enl (p : ℝ) (m n : ℕ) (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U : Array N => (trajectory p m U n).pos i - runMax p m U j n) :=
  (enl_pos_measurable p m n le_rfl i).sub (measurable_runMax_enl p m n j)

/-- `g_n + 1` is `enlFilt`-measurable. -/
theorem measurable_gap_add_enl (p : ℝ) (m n : ℕ) (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U : Array N => (trajectory p m U n).pos i - runMax p m U j n + 1) :=
  (measurable_gap_enl p m n i j).add_const 1

/-- `g_n - 1` is `enlFilt`-measurable. -/
theorem measurable_gap_sub_enl (p : ℝ) (m n : ℕ) (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U : Array N => (trajectory p m U n).pos i - runMax p m U j n - 1) :=
  (measurable_gap_enl p m n i j).sub_const 1

/-- The record cost `b_n = h_j(M_n^j - 1) + 2` is `enlFilt p m n`-measurable. -/
theorem measurable_bRec_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlFilt p m n] (bRec p m n j) := by
  show Measurable[enlFilt p m n] (fun U => HprevAt p m n j U + (2 : ℝ))
  exact (measurable_HprevAt_enlFilt hp m n j).add_const (2 : ℝ)

/-- For fixed `b`, the correction value `F_b(y)` is a measurable function of `b`. -/
lemma measurable_Fdiff_right (a eps : ℝ) (i : ℕ) :
    Measurable (fun b : ℝ => SwarmOcc.Fdiff a eps b i) := by
  unfold SwarmOcc.Fdiff SwarmOcc.Farg
  measurability

/-- For fixed gap `y`, `F_{b_n}(y)` is `enlFilt p m n`-measurable. -/
theorem measurable_Fcorr_fixed_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (a eps : ℝ) (y : ℤ) :
    Measurable[enlFilt p m n] (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y) := by
  have hb : Measurable[enlFilt p m n] (bRec p m n j) := measurable_bRec_enl hp m n j
  have hfun : (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
      = fun U => ∑ i ∈ Finset.range y.toNat, SwarmOcc.Fdiff a eps (bRec p m n j U) i := by
    funext U
    rfl
  rw [hfun]
  exact Finset.measurable_sum _ (fun i _ => (measurable_Fdiff_right a eps i).comp hb)

/-- `F_{b_n}` at an `enlFilt p m n`-measurable integer gap is `enlFilt`-measurable
(countable pieces over `ℤ`). -/
theorem measurable_Fcorr_gap_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (a eps : ℝ) {φ : Array N → ℤ} (hφ : Measurable[enlFilt p m n] φ) :
    Measurable[enlFilt p m n]
      (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
  letI : MeasurableSpace (Array N) := enlFilt p m n
  have key : Measurable (fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) (φ U)) := by
    refine SwarmIID.measurable_of_countable_pieces
      (U := fun y : ℤ => fun U : Array N => SwarmOcc.Fcorr a eps (bRec p m n j U) y)
      (fun y => measurable_Fcorr_fixed_enl hp m n j a eps y) φ ?_
    intro y
    exact hφ (measurableSet_singleton y)
  exact key

/-- The up-jump correction step is `enlFilt p m t`-measurable. -/
theorem measurable_CstepUp_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) : Measurable[enlFilt p m t] (CstepUp p m t eps i j) := by
  have h1 : Measurable[enlFilt p m t] (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t + 1)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_add_enl p m t i j)
  have h0 : Measurable[enlFilt p m t] (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_enl p m t i j)
  show Measurable[enlFilt p m t] (fun U =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t + 1)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t))
  exact h1.sub h0

/-- The down-jump correction step is `enlFilt p m t`-measurable. -/
theorem measurable_CstepDown_enl {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (i j : Fin N)
    (eps : ℝ) : Measurable[enlFilt p m t] (CstepDown p m t eps i j) := by
  have h1 : Measurable[enlFilt p m t] (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t - 1)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_sub_enl p m t i j)
  have h0 : Measurable[enlFilt p m t] (fun U : Array N =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t)) :=
    measurable_Fcorr_gap_enl hp m t j (aRec p m) eps (measurable_gap_enl p m t i j)
  show Measurable[enlFilt p m t] (fun U =>
      SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t - 1)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t))
  exact h1.sub h0

/-! ## 3. Bounds -/

/-- `b_n = h_j(M_n^j - 1) + 2 <= 2n+5`, uniformly in the array. -/
theorem bRec_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : bRec p m n j U ≤ 2 * (n : ℝ) + 5 := by
  have h := abs_HprevAt_le hp0 hp1 m n j U
  have h2 : HprevAt p m n j U ≤ 2 * (n : ℝ) + 3 := (abs_le.mp h).2
  simp only [bRec]
  linarith

/-- Uniform bound on `F_{b_n}(y)`, every gap `y`. -/
theorem abs_Fcorr_bRec_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (j : Fin N) {eps : ℝ} (hε : 0 < eps) (U : Array N) (y : ℤ) :
    |SwarmOcc.Fcorr (aRec p m) eps (bRec p m n j U) y|
      ≤ (2 * (n : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp0 hp1 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp0 hp1 m
  have hb0 : (0 : ℝ) ≤ bRec p m n j U := by
    have h3 := three_le_bRec hp0 hp1 m n j U
    linarith
  have hB := bRec_le hp0 hp1 m n j U
  have hden : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by
    have h1a : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  refine le_trans (SwarmOcc.Fcorr_abs_le ha0 ha1 hb0 hε y) ?_
  gcongr

/-- The correction steps are bounded by the uniform bound. -/
theorem abs_CstepUp_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (U : Array N) :
    |CstepUp p m t eps i j U|
      ≤ 2 * ((2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by
  have h1 := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t + 1)
  have h2 := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t)
  have h := abs_sub
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t + 1))
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t))
  have hC : CstepUp p m t eps i j U
      = SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t + 1)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t) := rfl
  rw [hC]
  linarith

/-- The down-jump correction step is bounded by the uniform bound. -/
theorem abs_CstepDown_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (U : Array N) :
    |CstepDown p m t eps i j U|
      ≤ 2 * ((2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by
  have h1 := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t - 1)
  have h2 := abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((trajectory p m U t).pos i - runMax p m U j t)
  have h := abs_sub
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t - 1))
    (SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
      ((trajectory p m U t).pos i - runMax p m U j t))
  have hC : CstepDown p m t eps i j U
      = SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t - 1)
        - SwarmOcc.Fcorr (aRec p m) eps (bRec p m t j U)
          ((trajectory p m U t).pos i - runMax p m U j t) := rfl
  rw [hC]
  linarith

/-- The up-step indicator is bounded by one. -/
theorem abs_stepUpInd_le (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    |stepUpInd p m n i U| ≤ 1 := by
  by_cases hU : U ∈ StepCross.stepUp p m n i
  · rw [stepUpInd, Set.indicator_of_mem hU]; norm_num
  · rw [stepUpInd, Set.indicator_of_notMem hU]; norm_num

/-- The down-step indicator is bounded by one. -/
theorem abs_stepDownInd_le (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    |stepDownInd p m n i U| ≤ 1 := by
  by_cases hU : U ∈ StepCross.stepDown p m n i
  · rw [stepDownInd, Set.indicator_of_mem hU]; norm_num
  · rw [stepDownInd, Set.indicator_of_notMem hU]; norm_num

/-! ## 4. Integrability of the correction increment -/

/-- **The correction increment is integrable**: it is a bounded measurable two-value step. -/
theorem integrable_Cinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) :
    Integrable (fun U : Array N => Cinc p m eps i j U t) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set c : ℝ := 2 * ((2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) with hc
  have hm_up : Measurable (stepUpInd p m t i) :=
    (measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator
      (StepCross.measurable_stepUp p m t i)
  have hm_dn : Measurable (stepDownInd p m t i) :=
    (measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator
      (StepCross.measurable_stepDown p m t i)
  have hm_u : Measurable (CstepUp p m t eps i j) :=
    measurable_ambient_of_enl (measurable_CstepUp_enl hp0.le m t i j eps)
  have hm_v : Measurable (CstepDown p m t eps i j) :=
    measurable_ambient_of_enl (measurable_CstepDown_enl hp0.le m t i j eps)
  have hbd_u : ∀ U, ‖CstepUp p m t eps i j U‖ ≤ c := by
    intro U
    rw [Real.norm_eq_abs, hc]
    exact abs_CstepUp_le hp0 hp1 m t i j hε U
  have hbd_v : ∀ U, ‖CstepDown p m t eps i j U‖ ≤ c := by
    intro U
    rw [Real.norm_eq_abs, hc]
    exact abs_CstepDown_le hp0 hp1 m t i j hε U
  have hup : Integrable (fun U : Array N => stepUpInd p m t i U * CstepUp p m t eps i j U)
      (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const c) (hm_up.mul hm_u).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |stepUpInd p m t i U| ≤ 1 := abs_stepUpInd_le p m t i U
    calc |stepUpInd p m t i U| * |CstepUp p m t eps i j U| ≤ 1 * c :=
          mul_le_mul h1 (by simpa only [Real.norm_eq_abs] using hbd_u U) (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  have hdn : Integrable (fun U : Array N => stepDownInd p m t i U * CstepDown p m t eps i j U)
      (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const c) (hm_dn.mul hm_v).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |stepDownInd p m t i U| ≤ 1 := abs_stepDownInd_le p m t i U
    calc |stepDownInd p m t i U| * |CstepDown p m t eps i j U| ≤ 1 * c :=
          mul_le_mul h1 (by simpa only [Real.norm_eq_abs] using hbd_v U) (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  have hsplit : (fun U : Array N => Cinc p m eps i j U t)
      = fun U => stepUpInd p m t i U * CstepUp p m t eps i j U
          + stepDownInd p m t i U * CstepDown p m t eps i j U := by
    funext U
    exact Cinc_eq_inds p m t eps i j U
  rw [hsplit]
  exact hup.add hdn

/-! ## 5. The correction drift identity -/

/-- **The correction drift identity.**  No hypotheses beyond `1/2 < p < 1` and `0 < eps`:

    condExp (enlFilt t) (Cinc t) =ᵐ alpha_n^i F_b(g+1) + (1-alpha_n^i) F_b(g-1) - F_b(g).

The two jump sets contribute `alpha_n^i (F_b(g+1) - F_b(g))` and
`(1 - alpha_n^i)(F_b(g-1) - F_b(g))`; the arithmetic at the end is exact. -/
theorem condExp_Cinc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) :
    condExp (enlFilt p m t) (arrayMeasure N) (fun U : Array N => Cinc p m eps i j U t)
      =ᵐ[arrayMeasure N] fun U => corrDrift (aRec p m) eps (alphaFun p m t i U)
        (bRec p m t j U) ((trajectory p m U t).pos i - runMax p m U j t) := by
  classical
  set c : ℝ := 2 * ((2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) with hc
  have hu_meas : Measurable[enlFilt p m t] (CstepUp p m t eps i j) :=
    measurable_CstepUp_enl hp0.le m t i j eps
  have hv_meas : Measurable[enlFilt p m t] (CstepDown p m t eps i j) :=
    measurable_CstepDown_enl hp0.le m t i j eps
  have hu_bound : ∀ U, ‖CstepUp p m t eps i j U‖ ≤ c := by
    intro U
    rw [Real.norm_eq_abs, hc]
    exact abs_CstepUp_le hp0 hp1 m t i j hε U
  have hv_bound : ∀ U, ‖CstepDown p m t eps i j U‖ ≤ c := by
    intro U
    rw [Real.norm_eq_abs, hc]
    exact abs_CstepDown_le hp0 hp1 m t i j hε U
  have hup := condExp_stepUp_mul_of_adapted hp0 hp1 (m := m) (n := t) i hu_meas c hu_bound
  have hdn := condExp_stepDown_mul_of_adapted hp0 hp1 (m := m) (n := t) i hv_meas c hv_bound
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hm_up : Measurable (stepUpInd p m t i) :=
    (measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator
      (StepCross.measurable_stepUp p m t i)
  have hm_dn : Measurable (stepDownInd p m t i) :=
    (measurable_const : Measurable fun _ : Array N => (1 : ℝ)).indicator
      (StepCross.measurable_stepDown p m t i)
  have hm_u : Measurable (CstepUp p m t eps i j) := measurable_ambient_of_enl hu_meas
  have hm_v : Measurable (CstepDown p m t eps i j) := measurable_ambient_of_enl hv_meas
  have hup_int : Integrable (fun U : Array N => stepUpInd p m t i U * CstepUp p m t eps i j U)
      (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const c) (hm_up.mul hm_u).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |stepUpInd p m t i U| ≤ 1 := abs_stepUpInd_le p m t i U
    calc |stepUpInd p m t i U| * |CstepUp p m t eps i j U| ≤ 1 * c :=
          mul_le_mul h1 (by simpa only [Real.norm_eq_abs] using hu_bound U) (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  have hdn_int : Integrable (fun U : Array N => stepDownInd p m t i U * CstepDown p m t eps i j U)
      (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const c) (hm_dn.mul hm_v).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |stepDownInd p m t i U| ≤ 1 := abs_stepDownInd_le p m t i U
    calc |stepDownInd p m t i U| * |CstepDown p m t eps i j U| ≤ 1 * c :=
          mul_le_mul h1 (by simpa only [Real.norm_eq_abs] using hv_bound U) (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  have hsplit : (fun U : Array N => Cinc p m eps i j U t)
      = (fun U => stepUpInd p m t i U * CstepUp p m t eps i j U)
        + fun U => stepDownInd p m t i U * CstepDown p m t eps i j U := by
    funext U
    simp only [Pi.add_apply]
    exact Cinc_eq_inds p m t eps i j U
  rw [hsplit]
  refine (condExp_add (f := fun U : Array N => stepUpInd p m t i U * CstepUp p m t eps i j U)
    (g := fun U : Array N => stepDownInd p m t i U * CstepDown p m t eps i j U)
    hup_int hdn_int (enlFilt p m t)).trans ?_
  refine (hup.add hdn).trans ?_
  filter_upwards with U
  simp only [Pi.add_apply, CstepUp, CstepDown, corrDrift]
  ring

/-! ## 6. The compensator identification, unconditionally -/

/-- **The compensator identification with no hypotheses**: `Edrift` *is* the
`enlFilt t`-conditional mean of the `Z`-plus-`J` increment. -/
theorem compensator_unconditional {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∀ t, condExp (enlFilt p m t) (arrayMeasure N)
        (fun U => Zpot p m eps i j U (t + 1) - Zpot p m eps i j U t + Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N] fun U => Edrift p m eps (fun t => alphaFun p m t i) i j U t :=
  compensator_of_correction (α := fun t => alphaFun p m t i) hp0 hp1
    (fun t => integrable_Cinc hp0 hp1 m t i j hε)
    (fun t => condExp_Cinc hp0 hp1 m t i j hε)

/-! ## 7. The one-step drift and the ledger with the *actual* `alpha_n^i`

`VdriftTimeAssembly.oneStep_drift` was stated with an abstract `alpha >= 1/2`; with
`InteriorBound.one_half_le_alphaFun` the actual right probability `alpha_n^i` qualifies, so the
one-step drift and the finite-time ledger hold with `alpha = alphaFun p m t i` and no side
condition on the array. -/

/-- **The one-step `(Vdrift)` drift with the actual jump probability `alpha_n^i`.** -/
theorem oneStep_drift_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m n : ℕ}
    {i j : Fin N} {eps : ℝ} (hε : 0 < eps)
    (hAB : Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) :
    (fun U : Array N =>
        SwarmOcc.occInd (fun t => (trajectory p m U t).pos i) (fun t => runMax p m U j t) n
          - eps)
      ≤ᵐ[arrayMeasure N] fun U => Edrift p m eps (fun t => alphaFun p m t i) i j U n :=
  oneStep_drift hp0 hp1 hε (fun U => one_half_le_alphaFun hp0 hp1 m n i U) hAB

/-- **The finite-time ledger with the actual jump probability `alpha_n^i`.** -/
theorem ledger_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {eps : ℝ} (hε : 0 < eps)
    (hAB : ∀ n, Budget.paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (T : ℕ) :
    (fun U : Array N => ∑ t ∈ Finset.range T,
        SwarmOcc.occInd (fun s => (trajectory p m U s).pos i) (fun s => runMax p m U j s) t)
      ≤ᵐ[arrayMeasure N] fun U =>
        eps * (T : ℝ) + (Zpot p m eps i j U T - Zpot p m eps i j U 0)
          + (∑ t ∈ Finset.range T, Jcorr p m eps i j U t)
          - Qcomp p m eps (fun t => alphaFun p m t i) i j U T :=
  occupation_ledger hp0 hp1 hε (fun t U => one_half_le_alphaFun hp0 hp1 m t i U) hAB T

end VdriftAssembly
end Swarming.Enl
