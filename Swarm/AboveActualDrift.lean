/-
  **DIRECTION C (m3) — the ACTUAL one-step `Hpot` drift at and above the running record,
  restricted to `A_g = {X_n^i = M_n^j + g}`, for `g ≥ 1`.**

  For the actual trajectory `Swarming.Trajectory.trajectory`, the actual array measure
  `arrayMeasure N`, the actual **full-history** site environment `h_j = hof p (siteMarks p m · j)`
  and the actual record `M = recVal j (prefOf p m n U)`, this file computes the
  `infoPiece p m n j (g-1)`-conditional mean (the record information which does *not* yet know the
  site `M+g`) of the genuine one-step Poisson increment `H(X_{n+1}^i) - H(X_n^i)`,
  `H = SwarmOcc.Hpot h_j`, restricted to the above-record event `A_g = {X_n^i = M_n^j + g}`:

      E[1_{A_g} (H(X_{n+1}^i) - H(X_n^i)) | infoPiece (g-1)]
        =ᵐ 1_{A_g} [ alpha_n^i * (1 + aRec * (1 + shiftG H0 (g-1)))
                      - (1 - alpha_n^i) * shiftG H0 (g-1) ],

  with `shiftG H0 (g-1) = h_j(M_n^j + g - 1)` (`ShiftedSeed.shiftG_H0`).

  Route (all ingredients already integrated, so **no external hypothesis remains**):

  * `PoissonStep.Hpot_traj_sub` splits the increment by jump direction;
  * on `A_g` the two `hZpot` values are `shiftG H0 g` and `shiftG H0 (g-1)`
    (`RecDown.hZpot_eq_shiftG_H0` + `ShiftedSeed.shiftG_H0`) — the pointwise bridge
    `indicator_Hpot_traj_sub_abovePosSet`;
  * **up**: `shiftG H0 g = 1 + rhoStep_j(g) (1 + shiftG H0 (g-1))` (`RecSeed.shiftG_succ`), so
    `1_up h_j(M+g) = 1_up + 1_up rhoStep_j(g) (1 + H_{g-1})`.  The marginal term is
    `RecDown.condExp_stepUp_mul_of_infoPiece` at `f = 1`; the weighted term is the integrated
    above-record `rho` law `AboveRecIncrement.condExp_stepUp_mul_rhoStep_infoPiece` combined with
    the bounded-`infoPiece` pull-out `RecDown.condExp_indicator_mul_of_infoPiece`.  `aRec` is not
    absorbed into `alpha` and no product of separate conditional means is used;
  * **down**: `RecDown.condExp_stepDown_shiftG_infoPiece` (the value `h_j(M+g-1)` is
    `infoPiece (g-1)`-measurable and bounded);
  * the `condExp` subtraction/indicator algebra (`condExp_sub`, `condExp_add`,
    `Set.indicator_sub`, `condExp_congr_ae`) is done in full, with all integrability supplied by
    `integrable_indicator_stepUp_mul_shiftG_H0`, `integrable_indicator_stepDown_mul_shiftG_H0`.

  This is an `infoPiece`-conditional statement only: **no `enlFilt` identity, no tower step, and no
  claim about `hZpot` at `enlFilt`** (that is direction E).  Nothing here sums the drift, builds
  `Q`, or claims a regeneration/occupation/Ballistic statement.

  No `sorry`, no `admit`, no custom axioms, no `native_decide`; axiom audit at the end.
-/
import Swarm.RecDown
import Swarm.AboveRecIncrement
import Swarm.PoissonStep

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### The actual site environment as a `ℕ → ℝ` step function -/

/-- The actual **full-history** environment of walker `j` at the array `U`, as the `ℕ → ℝ`
argument of `SwarmOcc.Hpot` / `hZpot`.  It is the paper's `h_j` (full history), not a
record-restarted environment. -/
noncomputable def siteH (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) : ℕ → ℝ :=
  fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k

/-- `siteH` is the actual site-mark environment, definitionally. -/
lemma siteH_def (p : ℝ) (m : ℕ) (j : Fin N) (U : Array N) :
    siteH p m j U = fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k := rfl

/-! ### Ambient measurability of the actual environment and of the potential step -/

/-- The actual site-mark sequence of walker `j` is ambient measurable. -/
lemma measurable_siteMarks_ambient (p : ℝ) (m : ℕ) (j : Fin N) :
    Measurable fun U : Array N => SwarmLogRatio.siteMarks p m U j := by
  classical
  refine measurable_pi_iff.mpr fun x => ?_
  refine measurable_to_bool ?_
  have hset : {U : Array N | SwarmLogRatio.siteMarks p m U j x = true}
      = {U : Array N | SiteMark p m U j (x : ℤ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, SwarmLogRatio.siteMarks]
    exact decide_eq_true_iff
  rw [hset]
  exact measurableSet_siteMark_array p m j (x : ℤ)

/-- `h_j(k)` at a fixed site is ambient measurable, as a function of the actual site marks. -/
lemma measurable_hof_siteMarks_ambient (p : ℝ) (m : ℕ) (j : Fin N) (k : ℕ) :
    Measurable fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k :=
  (measurable_hof_any p k).comp (measurable_siteMarks_ambient p m j)

/-- The integer-indexed potential step at a measurable random site is ambient measurable. -/
lemma measurable_hZpot_comp (p : ℝ) (m : ℕ) (j : Fin N) {Y : Array N → ℤ} (hY : Measurable Y) :
    Measurable fun U : Array N => hZpot (siteH p m j U) (Y U) := by
  classical
  have hfix : ∀ y : ℤ, Measurable fun U : Array N => hZpot (siteH p m j U) y := by
    intro y
    by_cases hy : y ≤ -1
    · have heq : (fun U : Array N => hZpot (siteH p m j U) y) = fun _ => (1 : ℝ) := by
        funext U
        exact hZpot_of_nonpos hy
      rw [heq]
      exact measurable_const
    · have hy0 : 0 ≤ y := by omega
      have heq : (fun U : Array N => hZpot (siteH p m j U) y)
          = fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) y.toNat := by
        funext U
        exact hZpot_of_nonneg hy0
      rw [heq]
      exact measurable_hof_siteMarks_ambient p m j y.toNat
  exact SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℤ)
    (U := fun y : ℤ => fun U : Array N => hZpot (siteH p m j U) y) hfix Y
    (fun y => hY (measurableSet_singleton y))

/-- The integer-indexed potential step at the actual above-record position is ambient
measurable. -/
lemma measurable_hZpot_traj (p : ℝ) (m n : ℕ) (j : Fin N) (i : Fin N) :
    Measurable fun U : Array N => hZpot (siteH p m j U) ((trajectory p m U n).pos i) :=
  measurable_hZpot_comp p m j ((Swarming.Fair.measurable_trajectory (N := N) p m n).1 i)

/-- Its predecessor form is ambient measurable as well. -/
lemma measurable_hZpot_traj_pred (p : ℝ) (m n : ℕ) (j : Fin N) (i : Fin N) :
    Measurable fun U : Array N => hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1) :=
  measurable_hZpot_comp p m j
    (((Swarming.Fair.measurable_trajectory (N := N) p m n).1 i).sub measurable_const)

/-! ### Membership in the above-record event `A_g` -/

/-- On `A_g = {X_n^i = M_n^j + g}` the position of walker `i` is the record shifted by `g`. -/
lemma pos_eq_of_mem_abovePosSet {p : ℝ} {m n : ℕ} {i j : Fin N} {k : ℕ} {U : Array N}
    (hU : U ∈ abovePosSet p m n i j k) :
    (trajectory p m U n).pos i = recVal j (prefOf p m n U) + (k : ℤ) := by
  have hpos : (trajectory p m U n).pos i = ext (prefOf p m n U) n i :=
    (ext_prefOf U le_rfl i).symm
  rw [hpos]
  exact hU

/-! ### The pointwise bridge: `hZpot` at the current site and at its predecessor -/

/-- **The `hZpot` value at the current above-record site.**  On `A_g`,
`hZpot h_j (X_n^i) = h_j(M_n^j + g) = shiftG H0 g`. -/
lemma hZpot_pos_of_mem_abovePosSet {p : ℝ} (hp0 : p ≠ 0) {m n : ℕ} (j : Fin N) {i : Fin N}
    {k : ℕ} {U : Array N} (hU : U ∈ abovePosSet p m n i j k) :
    hZpot (siteH p m j U) ((trajectory p m U n).pos i)
      = shiftG (H0 p m n j) p m n j k U :=
  hZpot_eq_shiftG_H0 (p := p) hp0 (m := m) (n := n) j
    (zero_le_recVal_prefOf p m U j n) (pos_eq_of_mem_abovePosSet hU)

/-- **The `hZpot` value at the predecessor of the current above-record site.**  On `A_g` with
`g ≥ 1`, `hZpot h_j (X_n^i - 1) = h_j(M_n^j + g - 1) = shiftG H0 (g-1)`. -/
lemma hZpot_pred_of_mem_abovePosSet {p : ℝ} (hp0 : p ≠ 0) {m n : ℕ} (j : Fin N) {i : Fin N}
    {g : ℕ} (hg : 1 ≤ g) {U : Array N} (hU : U ∈ abovePosSet p m n i j g) :
    hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)
      = shiftG (H0 p m n j) p m n j (g - 1) U := by
  have hx : (trajectory p m U n).pos i = recVal j (prefOf p m n U) + (g : ℤ) :=
    pos_eq_of_mem_abovePosSet hU
  have hcast : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hg]; ring
  refine hZpot_eq_shiftG_H0 (p := p) hp0 (m := m) (n := n) j
    (zero_le_recVal_prefOf p m U j n) (x := (trajectory p m U n).pos i - 1) ?_
  rw [hx]
  linarith [hcast]

/-- **The pointwise bridge for the actual one-step increment.**  On `A_g` (`g ≥ 1`) the actual
Poisson increment equals the jump-split expression with the *actual full-history* values replaced
by `shiftG H0 g` (up) and `shiftG H0 (g-1)` (down); off `A_g` both sides vanish.  No conditional
expectation is involved. -/
theorem indicator_Hpot_traj_sub_abovePosSet (p : ℝ) (hp0 : p ≠ 0) {m n : ℕ} (i j : Fin N)
    {g : ℕ} (hg : 1 ≤ g) :
    (abovePosSet p m n i j g).indicator
        (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i))
      = (abovePosSet p m n i j g).indicator
        (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j g U
          - stepDownInd p m n i U * shiftG (H0 p m n j) p m n j (g - 1) U) := by
  refine Set.indicator_congr ?_
  intro U hU
  show SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
      - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)
    = stepUpInd p m n i U * shiftG (H0 p m n j) p m n j g U
      - stepDownInd p m n i U * shiftG (H0 p m n j) p m n j (g - 1) U
  rw [Hpot_traj_sub (p := p) (m := m) (n := n) (siteH p m j U) U i,
    hZpot_pos_of_mem_abovePosSet hp0 j hU, hZpot_pred_of_mem_abovePosSet hp0 j hg hU]

/-! ### Bounds and integrability of the actual potential steps -/

/-- The one-site potential is bounded by `2n+3` at every site the trajectory can reach. -/
lemma abs_hZpot_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    {m n : ℕ} (j : Fin N) (U : Array N) {x : ℤ} (hx : x ≤ (n : ℤ)) :
    |hZpot (siteH p m j U) x| ≤ 2 * (n : ℝ) + 3 := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hxl : x ≤ -1
  · rw [hZpot_of_nonpos hxl, abs_one]; linarith
  · have hx0 : 0 ≤ x := by omega
    rw [hZpot_of_nonneg hx0]
    have hxn : x.toNat ≤ n := Int.toNat_le_toNat hx
    have hb := SwarmShiftMarks.abs_hof_le' hp0 hp1 hpne
      (SwarmLogRatio.siteMarks p m U j) x.toNat
    have hcast : ((x.toNat : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxn
    simp only [siteH]
    linarith

/-- The up-jump term of the actual increment is bounded by `2n+3`. -/
lemma abs_stepUpInd_mul_hZpot_traj_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) (U : Array N) :
    ‖stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)‖
      ≤ 2 * (n : ℝ) + 3 := by
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |stepUpInd p m n i U| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U
  have h2 : |hZpot (siteH p m j U) ((trajectory p m U n).pos i)| ≤ 2 * (n : ℝ) + 3 :=
    abs_hZpot_le hp0 hp1 hpne j U (pos_le_time p m U n i)
  calc |stepUpInd p m n i U| * |hZpot (siteH p m j U) ((trajectory p m U n).pos i)|
      ≤ 1 * (2 * (n : ℝ) + 3) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 2 * (n : ℝ) + 3 := one_mul _

/-- The down-jump term of the actual increment is bounded by `2n+3`. -/
lemma abs_stepDownInd_mul_hZpot_pred_traj_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) (U : Array N) :
    ‖stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)‖
      ≤ 2 * (n : ℝ) + 3 := by
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |stepDownInd p m n i U| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_stepDownInd_le p m n i U
  have h2 : |hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)| ≤ 2 * (n : ℝ) + 3 := by
    refine abs_hZpot_le hp0 hp1 hpne j U ?_
    have ht := pos_le_time p m U n i
    omega
  calc |stepDownInd p m n i U| * |hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)|
      ≤ 1 * (2 * (n : ℝ) + 3) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 2 * (n : ℝ) + 3 := one_mul _

/-- Integrability of the up-jump term of the actual increment. -/
lemma integrable_stepUpInd_mul_hZpot_traj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N => stepUpInd p m n i U
      * hZpot (siteH p m j U) ((trajectory p m U n).pos i)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
      (measurable_hZpot_traj p m n j i)
  · filter_upwards with U
    exact abs_stepUpInd_mul_hZpot_traj_le hp0 hp1 hpne m n i j U

/-- Integrability of the down-jump term of the actual increment. -/
lemma integrable_stepDownInd_mul_hZpot_pred_traj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N => stepDownInd p m n i U
      * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Measurable.indicator measurable_const (StepCross.measurable_stepDown p m n i)).mul
      (measurable_hZpot_traj_pred p m n j i)
  · filter_upwards with U
    exact abs_stepDownInd_mul_hZpot_pred_traj_le hp0 hp1 hpne m n i j U

/-- **Integrability of the actual one-step potential increment**
`H(X_{n+1}^i) - H(X_n^i)` for the full-history potential. -/
theorem integrable_Hpot_traj_step {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (hpne : p ≠ 0) (m n : ℕ) (i j : Fin N) :
    Integrable (fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hjump : Integrable (fun U : Array N => stepUpInd p m n i U
        * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
      - stepDownInd p m n i U
        * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)) (arrayMeasure N) :=
    (integrable_stepUpInd_mul_hZpot_traj hp0 hp1 hpne m n i j).sub
      (integrable_stepDownInd_mul_hZpot_pred_traj hp0 hp1 hpne m n i j)
  refine hjump.congr ?_
  filter_upwards with U
  exact (Hpot_traj_sub (p := p) (m := m) (n := n) (siteH p m j U) U i).symm

/-! ### Integrability of the `shiftG`-restricted jump terms -/

/-- Ambient measurability of the shifted full-history potential. -/
lemma measurable_shiftG_H0_ambient {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N)
    (k : ℕ) : Measurable (shiftG (H0 p m n j) p m n j k) := by
  have hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) := measurable_seedH hp m n j
  exact fun s hs =>
    infoPiece_le p m n j k _ ((measurable_shiftG (h0 := H0 p m n j) (hh0 := hh0) m n j k) hs)

/-- `1 + shiftG H0 k` is bounded by `2n + 2k + 6`. -/
lemma abs_one_add_shiftG_H0_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hpne : p ≠ 0)
    (m n : ℕ) (j : Fin N) (k : ℕ) (U : Array N) :
    |1 + shiftG (H0 p m n j) p m n j k U| ≤ 2 * (n : ℝ) + 2 * (k : ℝ) + 6 := by
  have h := abs_shiftG_le hp0 hp1 (fun U => abs_H0_le hp0 hp1 hpne m n j U) m n j k U
  have h1 : |1 + shiftG (H0 p m n j) p m n j k U|
      ≤ 1 + |shiftG (H0 p m n j) p m n j k U| := by
    have h2 := abs_add_le (1 : ℝ) (shiftG (H0 p m n j) p m n j k U)
    rwa [abs_one] at h2
  linarith

/-- **Integrability of the restricted up term** `1_{A_{k+1}} 1_up shiftG H0 (k+1)`. -/
lemma integrable_indicator_stepUp_mul_shiftG_H0 {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) (k : ℕ) :
    Integrable (fun U : Array N => (abovePosSet p m n i j (k + 1)).indicator
      (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j (k + 1) U) U)
      (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hAamb : MeasurableSet (abovePosSet p m n i j (k + 1)) :=
    infoPiece_le p m n j k _ (measurableSet_abovePosSet p m n i j (k + 1) k)
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 2 * (k : ℝ) + 7)) ?_ ?_
  · refine Measurable.aestronglyMeasurable (Measurable.indicator ?_ hAamb)
    exact (Measurable.indicator measurable_const (StepCross.measurable_stepUp p m n i)).mul
      (measurable_shiftG_H0_ambient hp0.le m n j (k + 1))
  · filter_upwards with U
    by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_mul]
      have h1 : |stepUpInd p m n i U| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U
      have h2 : |shiftG (H0 p m n j) p m n j (k + 1) U| ≤ 2 * (n : ℝ) + 2 * (k : ℝ) + 7 := by
        have h3 := abs_shiftG_le hp0 hp1 (fun U => abs_H0_le hp0 hp1 (by linarith) m n j U)
          m n j (k + 1) U
        push_cast at h3
        linarith
      calc |stepUpInd p m n i U| * |shiftG (H0 p m n j) p m n j (k + 1) U|
          ≤ 1 * (2 * (n : ℝ) + 2 * (k : ℝ) + 7) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 2 * (n : ℝ) + 2 * (k : ℝ) + 7 := one_mul _
    · rw [Set.indicator_of_notMem hU, norm_zero]
      positivity

/-- **Integrability of the restricted down term** `1_{A_{k+1}} 1_down shiftG H0 k`. -/
lemma integrable_indicator_stepDown_mul_shiftG_H0 {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) (k : ℕ) :
    Integrable (fun U : Array N => (abovePosSet p m n i j (k + 1)).indicator
      (fun U => stepDownInd p m n i U * shiftG (H0 p m n j) p m n j k U) U)
      (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hAamb : MeasurableSet (abovePosSet p m n i j (k + 1)) :=
    infoPiece_le p m n j k _ (measurableSet_abovePosSet p m n i j (k + 1) k)
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 2 * (k : ℝ) + 5)) ?_ ?_
  · refine Measurable.aestronglyMeasurable (Measurable.indicator ?_ hAamb)
    exact (Measurable.indicator measurable_const (StepCross.measurable_stepDown p m n i)).mul
      (measurable_shiftG_H0_ambient hp0.le m n j k)
  · filter_upwards with U
    by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_mul]
      have h1 : |stepDownInd p m n i U| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using abs_stepDownInd_le p m n i U
      have h2 : |shiftG (H0 p m n j) p m n j k U| ≤ 2 * (n : ℝ) + 2 * (k : ℝ) + 5 := by
        have h3 := abs_shiftG_le hp0 hp1 (fun U => abs_H0_le hp0 hp1 (by linarith) m n j U)
          m n j k U
        linarith
      calc |stepDownInd p m n i U| * |shiftG (H0 p m n j) p m n j k U|
          ≤ 1 * (2 * (n : ℝ) + 2 * (k : ℝ) + 5) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 2 * (n : ℝ) + 2 * (k : ℝ) + 5 := one_mul _
    · rw [Set.indicator_of_notMem hU, norm_zero]
      positivity

/-! ### The restricted up term above the record -/

/-- **The restricted up term above the record.**  For `g = k+1 ≥ 1` and at the record information
`infoPiece p m n j k` (which does not yet know the site `M+k+1`),

    E[1_{A_{k+1}} 1_up_i h_j(M+k+1) | infoPiece k]
      =ᵐ 1_{A_{k+1}} alpha_n^i * (1 + aRec * (1 + h_j(M+k))) .

The multiplier at the fresh site is handled by the integrated above-record `rho` law
(`condExp_stepUp_mul_rhoStep_infoPiece`, index `k`) combined with the bounded-`infoPiece` pull-out of
`1 + h_j(M+k) = 1 + shiftG H0 k` (`condExp_indicator_mul_of_infoPiece`); the bare `stepUpInd`
term is the `f = 1` case of `condExp_stepUp_mul_of_infoPiece`.  `aRec` stays outside `alpha`. -/
theorem condExp_indicator_up_abovePosSet_succ (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (k : ℕ) :
    condExp (infoPiece (N := N) p m n j k) (arrayMeasure N)
        ((abovePosSet p m n i j (k + 1)).indicator
          (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j (k + 1) U))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
          (fun U => alphaFun p m n i U
            * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j k U))) := by
  have hpne : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hA : MeasurableSet[infoPiece (N := N) p m n j k] (abovePosSet p m n i j (k + 1)) :=
    measurableSet_abovePosSet p m n i j (k + 1) k
  have hAamb : MeasurableSet (abovePosSet p m n i j (k + 1)) :=
    infoPiece_le p m n j k _ hA
  have hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) := measurable_seedH hp0.le m n j
  have hf : Measurable[infoPiece (N := N) p m n j k]
      (fun U => 1 + shiftG (H0 p m n j) p m n j k U) :=
    (measurable_shiftG (p := p) (h0 := H0 p m n j) (hh0 := hh0) m n j k).const_add 1
  have hfamb : Measurable (fun U => 1 + shiftG (H0 p m n j) p m n j k U) :=
    fun s hs => infoPiece_le p m n j k _ (hf hs)
  have hfc : ∀ U, ‖1 + shiftG (H0 p m n j) p m n j k U‖ ≤ 2 * (n : ℝ) + 2 * (k : ℝ) + 6 := by
    intro U
    rw [Real.norm_eq_abs]
    exact abs_one_add_shiftG_H0_le hp0 hp1 hpne m n j k U
  -- the bare jump indicator
  have h1 : condExp (infoPiece (N := N) p m n j k) (arrayMeasure N)
        (fun U => (abovePosSet p m n i j (k + 1)).indicator
          (fun U => stepUpInd p m n i U * (1 : ℝ)) U)
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
          (fun U => alphaFun p m n i U * (1 : ℝ)) :=
    condExp_stepUp_mul_of_infoPiece (N := N) p hp0 hp1 hij k hA
      (f := fun _ : Array N => (1 : ℝ)) measurable_const zero_le_one (fun U => by simp)
  -- the marked jump indicator times the (record-up-shifted) potential
  have h2 := condExp_indicator_mul_of_infoPiece (p := p) (m := m) (n := n) (i := i) (j := j) k hA
    (F := fun U => stepUpInd p m n i U * rhoStep p m n j (k + 1) U)
    (integrable_stepUpInd_mul_rhoStep hp0 hp1 m n i j k)
    (f := fun U => 1 + shiftG (H0 p m n j) p m n j k U) hf
    (c := 2 * (n : ℝ) + 2 * (k : ℝ) + 6) (by positivity) hfc
  have h2' : condExp (infoPiece (N := N) p m n j k) (arrayMeasure N)
        (fun U => (abovePosSet p m n i j (k + 1)).indicator
          (fun U => (stepUpInd p m n i U * rhoStep p m n j (k + 1) U)
            * (1 + shiftG (H0 p m n j) p m n j k U)) U)
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
          (fun U => (aRec p m * alphaFun p m n i U)
            * (1 + shiftG (H0 p m n j) p m n j k U)) := by
    refine h2.trans ?_
    filter_upwards [condExp_stepUp_mul_rhoStep_infoPiece p hp0 hp1 hij k] with U hU
    by_cases hU' : U ∈ abovePosSet p m n i j (k + 1)
    · rw [Set.indicator_of_mem hU', Set.indicator_of_mem hU', hU]
    · rw [Set.indicator_of_notMem hU', Set.indicator_of_notMem hU']
  -- pointwise split of the up term
  have hsplit : ((abovePosSet p m n i j (k + 1)).indicator
        (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j (k + 1) U))
      = (fun U => (abovePosSet p m n i j (k + 1)).indicator
            (fun U => stepUpInd p m n i U * (1 : ℝ)) U
          + (abovePosSet p m n i j (k + 1)).indicator
            (fun U => (stepUpInd p m n i U * rhoStep p m n j (k + 1) U)
              * (1 + shiftG (H0 p m n j) p m n j k U)) U) := by
    funext U
    by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU]
      have hG : shiftG (H0 p m n j) p m n j (k + 1) U
          = 1 + rhoStep p m n j (k + 1) U * (1 + shiftG (H0 p m n j) p m n j k U) := by
        rw [shiftG_succ]
      rw [hG]
      ring
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
      ring
  -- integrability of both summands
  have hint1 : Integrable (fun U : Array N =>
      (abovePosSet p m n i j (k + 1)).indicator
        (fun U => stepUpInd p m n i U * (1 : ℝ)) U) (arrayMeasure N) := by
    have hEq : (fun U : Array N => (abovePosSet p m n i j (k + 1)).indicator
          (fun U => stepUpInd p m n i U * (1 : ℝ)) U)
        = (abovePosSet p m n i j (k + 1)).indicator (stepUpInd p m n i) := by
      funext U
      by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
      · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, mul_one]
      · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    rw [hEq]
    exact (integrable_stepUpInd p m n i).indicator hAamb
  have hint2 : Integrable (fun U : Array N =>
      (abovePosSet p m n i j (k + 1)).indicator
        (fun U => (stepUpInd p m n i U * rhoStep p m n j (k + 1) U)
          * (1 + shiftG (H0 p m n j) p m n j k U)) U) (arrayMeasure N) := by
    refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 2 * (k : ℝ) + 6)) ?_ ?_
    · refine Measurable.aestronglyMeasurable (Measurable.indicator ?_ hAamb)
      exact ((Measurable.indicator measurable_const
        (StepCross.measurable_stepUp p m n i)).mul (measurable_rhoStep p m n j (k + 1))).mul hfamb
    · filter_upwards with U
      by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
      · rw [Set.indicator_of_mem hU, Real.norm_eq_abs, abs_mul, abs_mul]
        have h1' : |stepUpInd p m n i U| ≤ 1 := by
          simpa only [Real.norm_eq_abs] using abs_stepUpInd_le p m n i U
        have h2' : |rhoStep p m n j (k + 1) U| ≤ 1 := abs_rhoStep_le hp0 hp1 m n j (k + 1) U
        have h3 : |1 + shiftG (H0 p m n j) p m n j k U| ≤ 2 * (n : ℝ) + 2 * (k : ℝ) + 6 := by
          simpa only [Real.norm_eq_abs] using hfc U
        have h4 : |stepUpInd p m n i U| * |rhoStep p m n j (k + 1) U| ≤ 1 := by
          calc |stepUpInd p m n i U| * |rhoStep p m n j (k + 1) U| ≤ 1 * 1 :=
                mul_le_mul h1' h2' (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc |stepUpInd p m n i U| * |rhoStep p m n j (k + 1) U|
              * |1 + shiftG (H0 p m n j) p m n j k U|
            ≤ 1 * (2 * (n : ℝ) + 2 * (k : ℝ) + 6) :=
              mul_le_mul h4 h3 (abs_nonneg _) zero_le_one
          _ = 2 * (n : ℝ) + 2 * (k : ℝ) + 6 := one_mul _
      · rw [Set.indicator_of_notMem hU, norm_zero]
        positivity
  refine (condExp_congr_ae (Filter.EventuallyEq.of_eq hsplit)).trans ?_
  refine (condExp_add hint1 hint2 (infoPiece (N := N) p m n j k)).trans ?_
  refine (h1.add h2').trans (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ abovePosSet p m n i j (k + 1)
  · rw [Pi.add_apply, Set.indicator_of_mem hU, Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    ring
  · rw [Pi.add_apply, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU,
      Set.indicator_of_notMem hU]
    ring

/-- **The drift expression is measurable for the record information.**  For `g = k+1` the whole
bracket `alpha (1 + aRec (1 + shiftG H0 k)) - (1 - alpha) shiftG H0 k` is
`infoPiece p m n j k`-measurable (both `alpha_n^i` and the shifted potential are).  This is the
measurability half of the restricted drift; no conditional-expectation statement is made here. -/
lemma measurable_drift_above_infoPiece {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (i j : Fin N)
    (k : ℕ) :
    Measurable[infoPiece (N := N) p m n j k]
      (fun U => alphaFun p m n i U
          * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j k U))
        - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j k U) := by
  have hα : Measurable[infoPiece (N := N) p m n j k] (alphaFun p m n i) :=
    fun s hs => enlMeas_le_infoPiece p m n j k _ (measurable_alphaFun_enl p m n i hs)
  have hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) := measurable_seedH hp m n j
  have hH : Measurable[infoPiece (N := N) p m n j k]
      (shiftG (H0 p m n j) p m n j k) :=
    measurable_shiftG (p := p) (h0 := H0 p m n j) (hh0 := hh0) m n j k
  exact (hα.mul (measurable_const.add (measurable_const.mul (measurable_const.add hH)))).sub
    ((measurable_const.sub hα).mul hH)

/-! ### The main theorem: the actual restricted one-step drift at level `g ≥ 1` -/

/-- **The actual one-step `Hpot` drift above the record, successor form.**  For `g = k+1 ≥ 1`,

    E[1_{A_{k+1}} (H(X_{n+1}^i) - H(X_n^i)) | infoPiece p m n j k]
      =ᵐ 1_{A_{k+1}} [ alpha_n^i (1 + aRec (1 + shiftG H0 k))
                        - (1 - alpha_n^i) shiftG H0 k ] ,

`H = SwarmOcc.Hpot` at the actual full-history environment and `shiftG H0 k = h_j(M_n^j+k)`. -/
theorem condExp_indicator_Hpot_step_abovePosSet_succ (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (k : ℕ) :
    condExp (infoPiece (N := N) p m n j k) (arrayMeasure N)
        ((abovePosSet p m n i j (k + 1)).indicator
          (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j k U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j k U) := by
  have hpne : p ≠ 0 := by linarith
  have hA : MeasurableSet[infoPiece (N := N) p m n j k] (abovePosSet p m n i j (k + 1)) :=
    measurableSet_abovePosSet p m n i j (k + 1) k
  -- step 1: the pointwise bridge from the actual potential to the shifted ones
  refine (condExp_congr_ae (Filter.EventuallyEq.of_eq
    (indicator_Hpot_traj_sub_abovePosSet p hpne i j (g := k + 1) (by omega)))).trans ?_
  -- step 2: split the restricting indicator over the difference
  refine (condExp_congr_ae (Filter.EventuallyEq.of_eq (Set.indicator_sub
    (abovePosSet p m n i j (k + 1))
    (fun U => stepUpInd p m n i U * shiftG (H0 p m n j) p m n j (k + 1) U)
    (fun U => stepDownInd p m n i U * shiftG (H0 p m n j) p m n j k U)))).trans ?_
  -- step 3: `condExp` is additive over the two jump directions
  refine (condExp_sub (integrable_indicator_stepUp_mul_shiftG_H0 hp0 hp1 m n i j k)
    (integrable_indicator_stepDown_mul_shiftG_H0 hp0 hp1 m n i j k)
    (infoPiece (N := N) p m n j k)).trans ?_
  -- step 4: the up and down conditional laws
  refine ((condExp_indicator_up_abovePosSet_succ p hp0 hp1 hij k).sub
    (condExp_stepDown_shiftG_infoPiece (N := N) (m := m) (n := n) p hp0 hp1 hij k hA)).trans ?_
  -- step 5: collect the indicator into the difference of the two drift terms
  exact Filter.EventuallyEq.of_eq (Set.indicator_sub (abovePosSet p m n i j (k + 1))
    (fun U => alphaFun p m n i U
      * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j k U)))
    (fun U => (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j k U)).symm

/-- **The actual one-step `Hpot` drift above the record**, at the record information
`infoPiece p m n j (g-1)` and for any `g ≥ 1`. -/
theorem condExp_indicator_Hpot_step_abovePosSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator
          (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    condExp_indicator_Hpot_step_abovePosSet_succ (p := p) hp0 hp1 (m := m) (n := n)
      (i := i) (j := j) hij k

/-- **The same identity written with the actual full-history site values**: with
`H_{g-1} = h_j(M_n^j + g - 1)` (`ShiftedSeed.shiftG_H0`),

    E[1_{A_g} (H(X_{n+1}^i) - H(X_n^i)) | infoPiece (g-1)]
      =ᵐ 1_{A_g} [ alpha_n^i (1 + aRec (1 + h_j(M_n^j+g-1)))
                    - (1 - alpha_n^i) h_j(M_n^j+g-1) ] . -/
theorem condExp_indicator_Hpot_step_abovePosSet_hof (p : ℝ) (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator
          (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                  ((recVal j (prefOf p m n U)).toNat + (g - 1))))
            - (1 - alphaFun p m n i U) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                ((recVal j (prefOf p m n U)).toNat + (g - 1))) := by
  have hpne : p ≠ 0 := by linarith
  refine (condExp_indicator_Hpot_step_abovePosSet p hp0 hp1 hij hg).trans ?_
  refine Filter.Eventually.of_forall fun U => ?_
  by_cases hU : U ∈ abovePosSet p m n i j g
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU,
      shiftG_H0 hpne m n j (g - 1) U]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-- **The set-integral (real integral) form** of the restricted above-record drift: over the
above-record event `A_g` the actual potential increment integrates to the drift expression. -/
theorem setIntegral_Hpot_step_abovePosSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    ∫ U in (abovePosSet p m n i j g),
        (SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)) ∂(arrayMeasure N)
      = ∫ U in (abovePosSet p m n i j g),
          (alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U)
          ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hle : infoPiece (N := N) p m n j (g - 1) ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j (g - 1)
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hf : Integrable (fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)) (arrayMeasure N) :=
    integrable_Hpot_traj_step hp0 hp1 hpne m n i j
  have hAm : MeasurableSet[infoPiece (N := N) p m n j (g - 1)] (abovePosSet p m n i j g) :=
    measurableSet_abovePosSet p m n i j g (g - 1)
  have hA0 : MeasurableSet (abovePosSet p m n i j g) := hle _ hAm
  have hfind : Integrable ((abovePosSet p m n i j g).indicator
      (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i))) (arrayMeasure N) :=
    hf.indicator hA0
  calc ∫ U in (abovePosSet p m n i j g),
        (SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)) ∂(arrayMeasure N)
      = ∫ U in (abovePosSet p m n i j g),
          (abovePosSet p m n i j g).indicator
            (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
              - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i)) U
          ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA0 ?_
        filter_upwards with U hU
        rw [Set.indicator_of_mem hU]
    _ = ∫ U in (abovePosSet p m n i j g),
          condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
            ((abovePosSet p m n i j g).indicator
              (fun U => SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
                - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i))) U
          ∂(arrayMeasure N) := (setIntegral_condExp hle hfind hAm).symm
    _ = ∫ U in (abovePosSet p m n i j g),
          (abovePosSet p m n i j g).indicator
            (fun U => alphaFun p m n i U
                * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
              - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U) U
          ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA0 ?_
        filter_upwards [condExp_indicator_Hpot_step_abovePosSet p hp0 hp1 hij hg] with U hU _
        exact hU
    _ = ∫ U in (abovePosSet p m n i j g),
          (alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j (g - 1) U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U)
          ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA0 ?_
        filter_upwards with U hU
        rw [Set.indicator_of_mem hU]

/-! ### Axiom audit -/


end Swarming.Enl
