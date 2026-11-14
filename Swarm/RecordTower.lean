/-
  **Direction F (m6) — record-level tower step and the restricted `(Zloss)` bound.**

  The record region of the one-step ledger is

      A_0 = abovePosSet p m n i j 0 = {X_n^i = M_n^j},      M_n^j = runMax p m U j n.

  On it the `PoissonStep` split of the *actual* increment `H(X_{n+1}^i) - H(X_n^i)` uses the
  record values `h_j(M_n^j)` (up) and `h_j(M_n^j - 1)` (down).  The first is `H0`, the second is
  `HprevAt`, and the `M = 0` boundary (`hZpot h (-1) = 1 = h_j(-1)`) is one of the two cases.

  This file, all on the actual trajectory and the actual `arrayMeasure N`:

  * proves the record-level pointwise bridge and, with it, the **integrability** of the restricted
    increment `1_{A_0}(H(X_{n+1}^i) - H(X_n^i))`;
  * proves the `infoPiece p m n j 0` identity
    `E[1_{A_0}(H(X_{n+1}^i) - H(X_n^i)) | infoPiece 0]
     =ᵐ 1_{A_0}(alpha_n^i h_j(M_n^j) - (1 - alpha_n^i) h_j(M_n^j - 1))`
    from the integrated `RecDown.condExp_stepUp_H0_infoPiece` (the record row is inside
    `infoPiece 0`) and `RecDown.condExp_stepDown_mul_of_infoPiece` (the predecessor value is
    bounded and `infoPiece 0`-measurable);
  * applies the **valid** tower direction `enlFilt n ≤ infoPiece 0` and pulls the
    `enlFilt n`-measurable bounded multipliers `1_{A_0} alpha_n^i` and
    `1_{A_0} (1 - alpha_n^i) h_j(M_n^j-1)` out (using
    `BelowRecord.measurable_HprevAt_enlFilt`) to obtain the restricted `enlFilt` identity
    `1_{A_0}[alpha_n^i e_0 - (1 - alpha_n^i) h_j(M_n^j-1)]`, where `e_0` is
    `RecordAbove.eRec p m n j 0`;
  * composes with the record-boundary scalar bound (`SwarmOcc.zdrift_at`, using `1 ≤ e_0`,
    `e_0 ≤ b_n` and `1/2 ≤ alpha_n^i`) to obtain the **restricted lower bound**
    `1_{A_0} (1 - b_n)`.

  No above-record (`g ≥ 1`) statement is made here, `Hpot` is never replaced by `shiftH`, and the
  direction `enlFilt ≤ infoPiece 0` is used in the only orientation that is true.  The main
  statements also come in "direction-D identity as an explicit hypothesis" form
  (`*_of_recordIdentity`), so that the tower step can be reused with any equivalent statement of
  the `infoPiece 0` identity.
-/
import Swarm.AboveRecIncrement
import Swarm.BelowRecord
import Swarm.RecDown
import Swarm.InteriorBound

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### The record region `A_0 = {X_n^i = M_n^j}` -/

/-- `abovePosSet` read through the actual trajectory. -/
lemma abovePosSet_traj_iff (p : ℝ) (m n : ℕ) (i j : Fin N) (k : ℕ) (U : Array N) :
    U ∈ abovePosSet p m n i j k ↔
      (trajectory p m U n).pos i = runMax p m U j n + (k : ℤ) := by
  have h1 : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  rw [abovePosSet, Set.mem_ofPred_eq, h1, runMax_eq_recVal]

/-- `A_0` is in the enlarged filtration itself (it is path-determined). -/
theorem measurableSet_abovePosSet_enlFilt (p : ℝ) (m n : ℕ) (i j : Fin N) (k : ℕ) :
    MeasurableSet[enlFilt p m n] (abovePosSet p m n i j k) := by
  rw [enlFilt_apply, show enlMeas (N := N) p m n
      = pieceMeas (N := N) p m n (fun γ => prefRead n γ) from rfl]
  refine measurableSet_pieceMeas_of_piecewise fun γ => ?_
  by_cases h : ext γ n i = recVal j γ + (k : ℤ)
  · right
    ext U
    constructor
    · intro hU
      exact hU.1
    · intro hU
      refine ⟨hU, ?_⟩
      have hp : prefOf p m n U = γ := prefOf_eq_of_mem_prefAgree hU
      show ext (prefOf p m n U) n i = recVal j (prefOf p m n U) + (k : ℤ)
      rw [hp]
      exact h
  · left
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro U ⟨hU, hG⟩
    have hp : prefOf p m n U = γ := prefOf_eq_of_mem_prefAgree hU
    have hG' : ext (prefOf p m n U) n i = recVal j (prefOf p m n U) + (k : ℤ) := hG
    rw [hp] at hG'
    exact h hG'

/-- `A_0` has the same description in terms of `runMax`. -/
lemma abovePosSet_zero_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    abovePosSet p m n i j 0
      = {U : Array N | (trajectory p m U n).pos i = runMax p m U j n} := by
  ext U
  rw [abovePosSet_traj_iff]
  simp only [Set.mem_ofPred_eq, Nat.cast_zero, add_zero]

/-! ### The actual one-step potential increment -/

/-- The actual one-step increment of the full-history potential of walker `j` along the
trajectory of walker `i`. -/
noncomputable def HpotInc (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) : ℝ :=
  SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
    - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)

lemma HpotInc_def (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    HpotInc p m n i j U =
      SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i) := rfl

/-! ### The record-level pointwise bridge (`g = 0`)

At `A_0 = {X_n^i = M_n^j}` the integer site of walker `i` is exactly the running record, so the
`hZpot` step function of `PoissonStep.Hpot_traj_sub` is `h_j(M_n^j) = H0` for the up step and
`h_j(M_n^j - 1) = HprevAt` for the down step — with the boundary value `1` at record `0`. -/

theorem hZpot_traj_eq_H0_of_abovePosSet_zero {p : ℝ} (m n : ℕ) (i j : Fin N) {U : Array N}
    (hU : U ∈ abovePosSet p m n i j 0) :
    hZpot (fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k)
        ((trajectory p m U n).pos i)
      = H0 p m n j U := by
  rw [abovePosSet_traj_iff] at hU
  have hpos : (trajectory p m U n).pos i = recVal j (prefOf p m n U) := by
    rw [hU, runMax_eq_recVal, Nat.cast_zero, add_zero]
  rw [hpos, hZpot_of_nonneg (zero_le_recVal_prefOf p m U j n)]
  exact (H0_def m n j U).symm

theorem hZpot_traj_pred_eq_HprevAt_of_abovePosSet_zero {p : ℝ} (m n : ℕ) (i j : Fin N)
    {U : Array N} (hU : U ∈ abovePosSet p m n i j 0) :
    hZpot (fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k)
        ((trajectory p m U n).pos i - 1)
      = HprevAt p m n j U := by
  rw [abovePosSet_traj_iff] at hU
  have hpos : (trajectory p m U n).pos i = recVal j (prefOf p m n U) := by
    rw [hU, runMax_eq_recVal, Nat.cast_zero, add_zero]
  have hM0 : (0 : ℤ) ≤ recVal j (prefOf p m n U) := zero_le_recVal_prefOf p m U j n
  rw [hpos]
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m n U)).toNat) with h0 | hpos'
  · have hMeq : recVal j (prefOf p m n U) = 0 := by
      have hcast : ((recVal j (prefOf p m n U)).toNat : ℤ) = recVal j (prefOf p m n U) :=
        Int.toNat_of_nonneg hM0
      rw [← hcast, h0]
      simp
    rw [hMeq, HprevAt_of_zero p m n j U h0]
    have : (0 : ℤ) - 1 = -1 := by ring
    rw [this, hZpot_of_nonpos le_rfl]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m n U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m n j U k hk]
    have hMeq : recVal j (prefOf p m n U) = (k : ℤ) + 1 := by
      have hcast : ((recVal j (prefOf p m n U)).toNat : ℤ) = recVal j (prefOf p m n U) :=
        Int.toNat_of_nonneg hM0
      rw [← hcast, hk]
      push_cast
      ring
    have hsub : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
    rw [hMeq, hsub, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k), Int.toNat_natCast]

/-- **The restricted increment is the restricted jump split.**  On `A_0` the actual `Hpot`
increment equals `1{up} h_j(M_n^j) - 1{down} h_j(M_n^j - 1)`, and off `A_0` both sides vanish. -/
theorem indicator_HpotInc_eq_zero (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (abovePosSet p m n i j 0).indicator (HpotInc p m n i j)
      = (abovePosSet p m n i j 0).indicator
        (fun U => stepUpInd p m n i U * H0 p m n j U
          - stepDownInd p m n i U * HprevAt p m n j U) := by
  funext U
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, HpotInc_def]
    have hpt := Hpot_traj_sub (p := p) (m := m) (n := n)
      (fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) U i
    rw [hZpot_traj_eq_H0_of_abovePosSet_zero m n i j hU,
      hZpot_traj_pred_eq_HprevAt_of_abovePosSet_zero m n i j hU] at hpt
    exact hpt
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-! ### Integrability of the restricted record increment -/

/-- `h_j(M_n^j)` is ambient measurable (it is `hof` at the record index). -/
lemma measurable_H0_ambient (p : ℝ) (m n : ℕ) (j : Fin N) : Measurable (H0 p m n j) := by
  have h := measurable_hof_siteMarks_add p m n j 0
  have h2 : H0 p m n j = fun U : Array N =>
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((recVal j (prefOf p m n U)).toNat + 0) := by
    funext U
    rw [H0_def, Nat.add_zero]
  rw [h2]
  exact h

/-- A jump indicator times an ambient-measurable function bounded by `c` is integrable. -/
lemma integrable_indicator_stepUp_mul {p : ℝ} {m n : ℕ} {i : Fin N} {A : Set (Array N)}
    (hA : MeasurableSet A) {f : Array N → ℝ} (hf : Measurable f) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ U, ‖f U‖ ≤ c) :
    Integrable (fun U => A.indicator (fun U => stepUpInd p m n i U * f U) U) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U => A.indicator (fun U => stepUpInd p m n i U * f U) U) :=
    ((Measurable.indicator measurable_const (measurable_stepUp p m n i)).mul hf).indicator hA
  refine Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_mul]
    calc |stepUpInd p m n i U| * |f U| ≤ 1 * c :=
          mul_le_mul (by simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U) (hc U)
            (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  · rw [Set.indicator_of_notMem hU, norm_zero]
    exact hc0

/-- The down-jump companion. -/
lemma integrable_indicator_stepDown_mul {p : ℝ} {m n : ℕ} {i : Fin N} {A : Set (Array N)}
    (hA : MeasurableSet A) {f : Array N → ℝ} (hf : Measurable f) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ U, ‖f U‖ ≤ c) :
    Integrable (fun U => A.indicator (fun U => stepDownInd p m n i U * f U) U) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmeas : Measurable (fun U => A.indicator (fun U => stepDownInd p m n i U * f U) U) :=
    ((Measurable.indicator measurable_const (measurable_stepDown p m n i)).mul hf).indicator hA
  refine Integrable.mono' (integrable_const c) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_mul]
    calc |stepDownInd p m n i U| * |f U| ≤ 1 * c :=
          mul_le_mul (by simpa only [Real.norm_eq_abs] using abs_stepDownInd_le p m n i U) (hc U)
            (abs_nonneg _) zero_le_one
      _ = c := one_mul c
  · rw [Set.indicator_of_notMem hU, norm_zero]
    exact hc0

/-- The restricted increment split into the restricted up and down terms. -/
lemma indicator_HpotInc_eq_sub_zero (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (abovePosSet p m n i j 0).indicator (HpotInc p m n i j)
      = fun U => (abovePosSet p m n i j 0).indicator
          (fun U => stepUpInd p m n i U * H0 p m n j U) U
        - (abovePosSet p m n i j 0).indicator
          (fun U => stepDownInd p m n i U * HprevAt p m n j U) U := by
  funext U
  have h := congrFun (indicator_HpotInc_eq_zero p m n i j) U
  rw [h]
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    simp only [sub_zero]

/-- **The restricted record increment is integrable.** -/
lemma integrable_indicator_HpotInc_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    Integrable ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) (arrayMeasure N) := by
  have hp0 : p ≠ 0 := by linarith
  rw [indicator_HpotInc_eq_sub_zero p m n i j]
  have hA : MeasurableSet (abovePosSet p m n i j 0) :=
    infoPiece_le p m n j 0 _ (measurableSet_abovePosSet p m n i j 0 0)
  have hup : Integrable (fun U => (abovePosSet p m n i j 0).indicator
      (fun U => stepUpInd p m n i U * H0 p m n j U) U) (arrayMeasure N) :=
    integrable_indicator_stepUp_mul (p := p) (m := m) (n := n) (i := i) hA
      (measurable_H0_ambient p m n j) (c := 2 * (n : ℝ) + 3) (by positivity)
      (fun U => by simpa only [Real.norm_eq_abs] using abs_H0_le hp1 hp2 hp0 m n j U)
  have hdn : Integrable (fun U => (abovePosSet p m n i j 0).indicator
      (fun U => stepDownInd p m n i U * HprevAt p m n j U) U) (arrayMeasure N) :=
    integrable_indicator_stepDown_mul (p := p) (m := m) (n := n) (i := i) hA
      (measurable_HprevAt p m n j) (c := 2 * (n : ℝ) + 3) (by positivity)
      (fun U => by simpa only [Real.norm_eq_abs] using abs_HprevAt_le hp1 hp2 m n j U)
  exact hup.sub hdn

/-! ### Direction D's record identity: the increment at `infoPiece 0` -/

lemma measurable_H0_infoPiece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) (g : ℕ) :
    Measurable[infoPiece p m n j g] (H0 p m n j) :=
  fun s hs => enlRecMeas_le_infoPiece p m n j g _ (measurable_H0 hp m n j hs)

lemma measurable_HprevAt_infoPiece_zero {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[infoPiece p m n j 0] (HprevAt p m n j) :=
  fun s hs => enlMeas_le_infoPiece p m n j 0 _ (measurable_HprevAt_enlFilt hp m n j hs)

/-- **The record-region one-step conditional mean at the record information.**
For distinct walkers,

  `E[1_{A_0} (H(X_{n+1}^i) - H(X_n^i)) | infoPiece 0]`
    `=ᵐ 1_{A_0} (alpha_n^i h_j(M_n^j) - (1 - alpha_n^i) h_j(M_n^j - 1))`.

The up half is `RecDown.condExp_stepUp_H0_infoPiece` (the record row is inside `infoPiece 0`),
the down half is `RecDown.condExp_stepDown_mul_of_infoPiece` at the bounded
`infoPiece 0`-measurable `HprevAt`. -/
theorem condExp_indicator_HpotInc_infoPiece_zero (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (infoPiece p m n j 0) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * H0 p m n j U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) := by
  have hp0 : p ≠ 0 := by linarith
  have hA : MeasurableSet[infoPiece p m n j 0] (abovePosSet p m n i j 0) :=
    measurableSet_abovePosSet p m n i j 0 0
  have hup := condExp_stepUp_H0_infoPiece (N := N) (m := m) (n := n) (i := i) (j := j)
    p hp1 hp2 hij (A := abovePosSet p m n i j 0) hA
  have hdn := condExp_stepDown_mul_of_infoPiece (N := N) (m := m) (n := n) (i := i) (j := j)
    p hp1 hp2 hij 0 (A := abovePosSet p m n i j 0) hA
    (f := HprevAt p m n j) (measurable_HprevAt_infoPiece_zero hp1.le m n j)
    (c := 2 * (n : ℝ) + 3) (by positivity)
    (fun U => by simpa only [Real.norm_eq_abs] using abs_HprevAt_le hp1 hp2 m n j U)
  have hint1 : Integrable (fun U => (abovePosSet p m n i j 0).indicator
      (fun U => stepUpInd p m n i U * H0 p m n j U) U) (arrayMeasure N) :=
    integrable_indicator_stepUp_mul (p := p) (m := m) (n := n) (i := i)
      (infoPiece_le p m n j 0 _ hA) (measurable_H0_ambient p m n j)
      (c := 2 * (n : ℝ) + 3) (by positivity)
      (fun U => by simpa only [Real.norm_eq_abs] using abs_H0_le hp1 hp2 hp0 m n j U)
  have hint2 : Integrable (fun U => (abovePosSet p m n i j 0).indicator
      (fun U => stepDownInd p m n i U * HprevAt p m n j U) U) (arrayMeasure N) :=
    integrable_indicator_stepDown_mul (p := p) (m := m) (n := n) (i := i)
      (infoPiece_le p m n j 0 _ hA) (measurable_HprevAt p m n j)
      (c := 2 * (n : ℝ) + 3) (by positivity)
      (fun U => by simpa only [Real.norm_eq_abs] using abs_HprevAt_le hp1 hp2 m n j U)
  -- the restricted split
  have hsplit : condExp (infoPiece p m n j 0) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] condExp (infoPiece p m n j 0) (arrayMeasure N)
        (fun U => (abovePosSet p m n i j 0).indicator
            (fun U => stepUpInd p m n i U * H0 p m n j U) U
          - (abovePosSet p m n i j 0).indicator
            (fun U => stepDownInd p m n i U * HprevAt p m n j U) U) := by
    exact condExp_congr_ae (Filter.EventuallyEq.of_eq (indicator_HpotInc_eq_sub_zero p m n i j))
  refine hsplit.trans ?_
  refine (condExp_sub hint1 hint2 _).trans ?_
  refine (hup.sub hdn).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  simp only [Pi.sub_apply]
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · simp only [Set.indicator_of_mem hU]
  · simp only [Set.indicator_of_notMem hU, sub_zero]

/-! ### The tower step `enlFilt n ≤ infoPiece 0` -/

/-- The enlarged filtration sits inside the record information. -/
lemma enlFilt_le_infoPiece_zero (p : ℝ) (m n : ℕ) (j : Fin N) :
    enlFilt p m n ≤ infoPiece p m n j 0 :=
  enlMeas_le_infoPiece p m n j 0

/-- `e_0` is the `enlFilt`-conditional mean of `h_j(M_n^j)`. -/
theorem condExp_H0_eq_eRec_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j)
      =ᵐ[arrayMeasure N] eRec p m n j 0 := by
  have h := eRec_eq_condExp hp1 hp2 m (n := n) j 0
  have h2 : (fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat + 0)) = H0 p m n j := by
    funext U
    rw [H0_def, Nat.add_zero]
  rw [h2] at h
  exact h.symm

/-- The indicator function of the region, as a real multiplier. -/
noncomputable def regInd (p : ℝ) (m n : ℕ) (i j : Fin N) : Array N → ℝ :=
  (abovePosSet p m n i j 0).indicator (fun _ => (1 : ℝ))

lemma measurable_regInd (p : ℝ) (m n : ℕ) (i j : Fin N) :
    Measurable[enlFilt p m n] (regInd p m n i j) :=
  measurable_const.indicator (measurableSet_abovePosSet_enlFilt p m n i j 0)

lemma abs_regInd_le (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    ‖regInd p m n i j U‖ ≤ 1 := by
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [regInd, Set.indicator_of_mem hU]; simp
  · rw [regInd, Set.indicator_of_notMem hU]; simp

/-- Ambient measurability from `enlFilt n`-measurability. -/
lemma measurable_ambient_of_enlFilt {p : ℝ} {m n : ℕ} {f : Array N → ℝ}
    (hf : Measurable[enlFilt p m n] f) : Measurable f :=
  fun s hs => (enlFilt p m).le n (f ⁻¹' s) (hf hs)

/-- **The restricted bracket as a product of adapted multipliers.** -/
lemma indicator_bracket_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * H0 p m n j U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U)
      = fun U => (regInd p m n i j U * alphaFun p m n i U) * H0 p m n j U
        - (regInd p m n i j U * (1 - alphaFun p m n i U)) * HprevAt p m n j U := by
  funext U
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU, regInd, Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, regInd, Set.indicator_of_notMem hU]
    ring

/-- **The restricted `enlFilt` identity at the record.**  Applying the tower property in the
direction `enlFilt n ≤ infoPiece 0` to the `infoPiece 0` record identity, and pulling the
`enlFilt`-measurable bounded multipliers `1_{A_0} alpha_n^i` and
`1_{A_0}(1 - alpha_n^i) h_j(M_n^j - 1)` out, replaces `E[h_j(M_n^j) | enlFilt]` by `e_0`:

  `E[1_{A_0}(H(X_{n+1}^i) - H(X_n^i)) | enlFilt n]`
    `=ᵐ 1_{A_0}(alpha_n^i e_0 - (1 - alpha_n^i) h_j(M_n^j - 1))`. -/
theorem condExp_indicator_HpotInc_enlFilt_zero_of_recordIdentity (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N}
    (hD : condExp (infoPiece p m n j 0) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * H0 p m n j U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U)) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * eRec p m n j 0 U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) := by
  have hp0 : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hleI : infoPiece p m n j 0 ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j 0
  haveI : SigmaFinite ((arrayMeasure N).trim hleI) := inferInstance
  -- step 1: tower, then direction D's `infoPiece 0` identity
  have htower : condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator
          (fun U => alphaFun p m n i U * H0 p m n j U
            - (1 - alphaFun p m n i U) * HprevAt p m n j U)) := by
    refine (MeasureTheory.condExp_condExp_of_le (μ := arrayMeasure N)
      (m₁ := enlFilt p m n) (m₂ := infoPiece p m n j 0)
      (f := (abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      (enlFilt_le_infoPiece_zero p m n j) hleI).symm.trans ?_
    exact condExp_congr_ae hD
  -- step 2: rewrite the bracket as a product and pull the adapted multipliers out
  refine htower.trans ?_
  rw [indicator_bracket_eq]
  -- integrability of the two pulling-out products
  have hH0int : Integrable (H0 p m n j) (arrayMeasure N) :=
    (recSeed_hypotheses_complete hp1 hp2 m n j).2.1
  have hc1meas : Measurable[enlFilt p m n]
      (fun U => regInd p m n i j U * alphaFun p m n i U) :=
    (measurable_regInd p m n i j).mul (measurable_alphaFun_enl p m n i)
  have hc1b : ∀ U, ‖regInd p m n i j U * alphaFun p m n i U‖ ≤ 1 := by
    intro U
    rw [norm_mul]
    have h1 : ‖regInd p m n i j U‖ ≤ 1 := abs_regInd_le p m n i j U
    have h2 : ‖alphaFun p m n i U‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (alphaFun_mem_Icc hp1 hp2 m n i U).1]
      exact (alphaFun_mem_Icc hp1 hp2 m n i U).2
    calc ‖regInd p m n i j U‖ * ‖alphaFun p m n i U‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hc2meas : Measurable[enlFilt p m n]
      (fun U => regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U) :=
    (((measurable_regInd p m n i j).mul
      (measurable_const.sub (measurable_alphaFun_enl p m n i))).mul
      (measurable_HprevAt_enlFilt hp1.le m n j))
  have hc2b : ∀ U, ‖regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U‖
      ≤ 2 * (n : ℝ) + 3 := by
    intro U
    rw [norm_mul, norm_mul]
    have h1 : ‖regInd p m n i j U‖ ≤ 1 := abs_regInd_le p m n i j U
    have h2 : ‖1 - alphaFun p m n i U‖ ≤ 1 := by
      have h0 := (alphaFun_mem_Icc hp1 hp2 m n i U).1
      have h1' := (alphaFun_mem_Icc hp1 hp2 m n i U).2
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h3 : ‖HprevAt p m n j U‖ ≤ 2 * (n : ℝ) + 3 := by
      rw [Real.norm_eq_abs]; exact abs_HprevAt_le hp1 hp2 m n j U
    have hC : (0 : ℝ) ≤ 2 * (n : ℝ) + 3 := by positivity
    calc ‖regInd p m n i j U‖ * ‖1 - alphaFun p m n i U‖ * ‖HprevAt p m n j U‖
        ≤ 1 * 1 * (2 * (n : ℝ) + 3) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
          nlinarith
      _ = 2 * (n : ℝ) + 3 := by ring
  have hc1int : Integrable (fun U => (regInd p m n i j U * alphaFun p m n i U) * H0 p m n j U)
      (arrayMeasure N) := by
    have hmeas : Measurable (fun U => (regInd p m n i j U * alphaFun p m n i U) * H0 p m n j U) :=
      ((measurable_ambient_of_enlFilt hc1meas).mul (measurable_H0_ambient p m n j))
    refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |regInd p m n i j U * alphaFun p m n i U| ≤ 1 := by
      have := hc1b U
      rwa [Real.norm_eq_abs] at this
    have h3 : |H0 p m n j U| ≤ 2 * (n : ℝ) + 3 := abs_H0_le hp1 hp2 hp0 m n j U
    have hC : (0 : ℝ) ≤ 2 * (n : ℝ) + 3 := by positivity
    calc |regInd p m n i j U * alphaFun p m n i U| * |H0 p m n j U|
        ≤ 1 * (2 * (n : ℝ) + 3) := mul_le_mul h1 h3 (abs_nonneg _) zero_le_one
      _ = 2 * (n : ℝ) + 3 := one_mul _
  have hc2int : Integrable
      (fun U => regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U)
      (arrayMeasure N) := by
    have hmeas : Measurable
        (fun U => regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U) :=
      (measurable_ambient_of_enlFilt hc2meas)
    refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs]
    exact hc2b U
  -- the two pull-outs
  have hpull1 := condExp_stronglyMeasurable_mul_of_bound (μ := arrayMeasure N)
    (m := enlFilt p m n) hle
    (f := fun U => regInd p m n i j U * alphaFun p m n i U) (g := H0 p m n j)
    hc1meas.stronglyMeasurable hH0int 1 (Filter.Eventually.of_forall hc1b)
  have hpull2 : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U)
      =ᵐ[arrayMeasure N] fun U =>
        regInd p m n i j U * (1 - alphaFun p m n i U) * HprevAt p m n j U :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable hle hc2meas.stronglyMeasurable hc2int)
  have hH0cond := condExp_H0_eq_eRec_zero hp1 hp2 m (n := n) j
  refine (condExp_sub hc1int hc2int _).trans ?_
  refine (hpull1.sub hpull2).trans ?_
  filter_upwards [hH0cond] with U hU
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [hU, regInd]
  by_cases hU' : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU', Set.indicator_of_mem hU']
    ring
  · rw [Set.indicator_of_notMem hU', Set.indicator_of_notMem hU']
    ring

/-- The compiled direction-D record identity turns the tower theorem into the unconditional
restricted `enlFilt` identity. -/
theorem condExp_indicator_HpotInc_enlFilt_zero (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * eRec p m n j 0 U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) :=
  condExp_indicator_HpotInc_enlFilt_zero_of_recordIdentity p hp1 hp2 m n
    (condExp_indicator_HpotInc_infoPiece_zero p hp1 hp2 m n hij)

/-! ### The record-boundary `(Zloss)` with the actual random `alpha_n^i` -/

/-- **`zdrift_at` at the actual random right probability.**  Since `alphaFun p m n i ≥ 1/2`
(`one_half_le_alphaFun`) and `1 ≤ e_0 ≤ b_n`, the record-boundary bound holds with the
`U`-dependent multiplier `alpha_n^i`, not just for a fixed `α ≥ 1/2`:

  `1 - b_n ≤ alpha_n^i e_0 - (1 - alpha_n^i) h_j(M_n^j - 1)`. -/
theorem zdrift_at_eRec_alphaFun {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    (fun U => 1 - bRec p m n j U) ≤ᵐ[arrayMeasure N]
      fun U => alphaFun p m n i U * eRec p m n j 0 U
        - (1 - alphaFun p m n i U) * HprevAt p m n j U := by
  filter_upwards [one_le_eRec_zero hp1 hp2 m (n := n) j,
    eRec_zero_le_bRec_unconditional hp1 hp2 m n j] with U h1 hb
  simp only [Pi.one_apply] at h1
  have hα : (1 : ℝ) / 2 ≤ alphaFun p m n i U := one_half_le_alphaFun hp1 hp2 m n i U
  have hprev : 0 ≤ HprevAt p m n j U := by
    have h := one_le_HprevAt hp1 hp2 m n j U
    linarith
  have hsum : 0 ≤ eRec p m n j 0 U + HprevAt p m n j U := by linarith
  have hres := SwarmOcc.zdrift_at (α := alphaFun p m n i U) (e := eRec p m n j 0 U)
    (hprev := HprevAt p m n j U) (b := HprevAt p m n j U + 2) hα h1 hsum hprev rfl
  simpa only [bRec] using hres

/-- **The restricted record lower bound (main statement of this file).**

For distinct walkers `i ≠ j`, on the record region `A_0 = {X_n^i = M_n^j}` the `enlFilt n`-
conditional mean of the *actual* one-step `Hpot` increment dominates `1 - b_n`:

  `1_{A_0} (1 - b_n) ≤ᵐ (arrayMeasure N)[ 1_{A_0} (H(X_{n+1}^i) - H(X_n^i)) | enlFilt n ]`.

No above-record work, no `shiftH`, no tower beyond `enlFilt n ≤ infoPiece 0`. -/
theorem indicator_le_condExp_indicator_HpotInc_zero (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    (fun U => (abovePosSet p m n i j 0).indicator (fun U => 1 - bRec p m n j U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) := by
  have hrec := zdrift_at_eRec_alphaFun hp1 hp2 m n i j
  have hspec := condExp_indicator_HpotInc_enlFilt_zero p hp1 hp2 m n hij
  filter_upwards [hrec, hspec] with U h1 h2
  rw [h2]
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    exact h1
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-- **Set-integral form of the restricted record bound**: the mass form of
`indicator_le_condExp_indicator_HpotInc_zero`, obtained by integrating the a.e. inequality and
using `integral_condExp` / `integral_indicator`. -/
theorem setIntegral_le_setIntegral_HpotInc_zero (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N)
      ≤ ∫ U in abovePosSet p m n i j 0, HpotInc p m n i j U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hA : MeasurableSet (abovePosSet p m n i j 0) :=
    infoPiece_le p m n j 0 _ (measurableSet_abovePosSet p m n i j 0 0)
  have hInt : Integrable ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      (arrayMeasure N) := integrable_indicator_HpotInc_zero hp1 hp2 m n i j
  have hbound : Integrable (fun U => (abovePosSet p m n i j 0).indicator
      (fun U => 1 - bRec p m n j U) U) (arrayMeasure N) := by
    have hb : Measurable (fun U : Array N => 1 - (HprevAt p m n j U + 2)) :=
      measurable_const.sub ((measurable_HprevAt p m n j).add_const 2)
    have hfun : (fun U : Array N => 1 - bRec p m n j U)
        = fun U => 1 - (HprevAt p m n j U + 2) := by
      funext U
      rw [bRec]
    have hmeas : Measurable (fun U => (abovePosSet p m n i j 0).indicator
        (fun U => 1 - bRec p m n j U) U) := by
      rw [hfun]
      exact hb.indicator hA
    refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 5)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    by_cases hU : U ∈ abovePosSet p m n i j 0
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, bRec]
      have h1 : |HprevAt p m n j U| ≤ 2 * (n : ℝ) + 3 := abs_HprevAt_le hp1 hp2 m n j U
      have h3 : (-1 : ℝ) ≤ HprevAt p m n j U := by
        have hle := one_le_HprevAt hp1 hp2 m n j U
        linarith
      have h4 : HprevAt p m n j U ≤ 2 * (n : ℝ) + 3 := (abs_le.mp h1).2
      have heq : (1 : ℝ) - (HprevAt p m n j U + 2) = -(HprevAt p m n j U + 1) := by ring
      rw [heq, abs_neg, abs_of_nonneg (by linarith)]
      linarith
    · rw [Set.indicator_of_notMem hU, norm_zero]
      positivity
  have hmono := integral_mono_ae hbound integrable_condExp
    (indicator_le_condExp_indicator_HpotInc_zero p hp1 hp2 m n hij)
  have hce : ∫ U, condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) U ∂(arrayMeasure N)
      = ∫ U, (abovePosSet p m n i j 0).indicator (HpotInc p m n i j) U ∂(arrayMeasure N) :=
    integral_condExp hle
  rw [hce, integral_indicator hA, integral_indicator hA] at hmono
  exact hmono

/-- The restricted record lower bound with direction D's identity as an **explicit hypothesis**
(the remaining external interface, if it is needed in a different shape). -/
theorem indicator_le_condExp_indicator_HpotInc_zero_of_recordIdentity (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N}
    (hD : condExp (infoPiece p m n j 0) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * H0 p m n j U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U)) :
    (fun U => (abovePosSet p m n i j 0).indicator (fun U => 1 - bRec p m n j U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) := by
  have hrec := zdrift_at_eRec_alphaFun hp1 hp2 m n i j
  have hspec := condExp_indicator_HpotInc_enlFilt_zero_of_recordIdentity p hp1 hp2 m n hD
  filter_upwards [hrec, hspec] with U h1 h2
  rw [h2]
  by_cases hU : U ∈ abovePosSet p m n i j 0
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    exact h1
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]


end Swarming.Enl
