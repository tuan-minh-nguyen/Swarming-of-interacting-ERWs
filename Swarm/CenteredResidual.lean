/-
  **DIRECTION H (m8) — the one-step centred residual of the actual `Hpot` increment.**

  The integrated record/above-record work describes the *conditional mean* of the actual
  one-step potential increment

      HpotInc_n = H(X_{n+1}^i) - H(X_n^i)      (`RecordTower.HpotInc`, `siteH`/`envH`),

  at `enlFilt n` on the record region and at `infoPiece (g-1)` above the record.  This file
  introduces the *centred* object that the post-one-step compensator argument consumes:

      centeredResidual_n = HpotInc_n - E[HpotInc_n | enlFilt n] .

  Proved here, all on the actual trajectory and the actual `arrayMeasure`:

  * `HpotInc` is the `siteH`-increment of `AboveActualDrift` (`HpotInc_eq_step`, definitional),
    it is ambient measurable and integrable (`measurable_HpotInc`, `integrable_HpotInc`);
  * the pointwise one-step bound `|HpotInc_n| <= 4n+6`, from the Poisson step split and the
    `2n+3` bound on each site potential (`abs_HpotInc_le`);
  * `centeredResidual_n` is integrable and has **zero `enlFilt n`-conditional mean**:
    `E[centeredResidual_n | enlFilt n] =ᵐ 0` (`condExp_centeredResidual_eq_zero`);
  * consequently it has zero total mean, and the *linear* deterministic a.e. bound
    `|centeredResidual_n| <= 8n+12` together with its integral form (`abs_centeredResidual_le`,
    `integral_abs_centeredResidual_le`);
  * the **restricted residual bridge**: if `A ∈ enlFilt n` and the integrated restricted drift
    identity `E[1_A HpotInc_n | enlFilt n] =ᵐ 1_A d` holds, then
    `1_A centeredResidual_n =ᵐ 1_A (HpotInc_n - d)`.  This is the interface through which the
    below-record, record and above-record drift bounds of the other directions enter the centred
    decomposition.  It is instantiated at the integrated record region (`A_0`, drift
    `alpha e_0 - (1-alpha) HprevAt`), and stated with the above-record tower identity as an
    explicit hypothesis (direction A's interface);
  * the successive residuals at times `0..n-1` are packaged as `centeredResidualSum`; each
    residual has zero conditional mean, the partial sums have zero mean, and **if** the residual
    at time `k` is `enlFilt (k+1)`-measurable (the adaptedness interface, which is *not* claimed
    here: `envH` reads the full site-mark array, so adaptedness is exactly the missing input),
    then the partial sums form a genuine `MeasureTheory.Martingale` with respect to `enlFilt`.
    No future-independence, no SLLN, no occupation/`Q` statement is used or claimed.

  No `sorry`, no `admit`, no custom axioms, no `native_decide`; axiom audit at the end.
-/
import Swarm.CommonIncrement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### 1. The actual increment as a function of the actual site environment -/

/-- `HpotInc` is the `siteH` one-step increment of `AboveActualDrift`, definitionally
(`envH` and `siteH` are the same `ℕ → ℝ` site environment). -/
lemma HpotInc_eq_step (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

lemma HpotInc_eq_step_apply (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    HpotInc p m n i j U =
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

/-- **The pointwise one-step bound.**  The increment splits into an up and a down jump term,
each bounded by `2n+3` (`AboveActualDrift.abs_stepUpInd_mul_hZpot_traj_le`,
`…abs_stepDownInd_mul_hZpot_pred_traj_le`). -/
theorem abs_HpotInc_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) (U : Array N) :
    |HpotInc p m n i j U| ≤ 4 * (n : ℝ) + 6 := by
  have hpne : p ≠ 0 := by linarith
  have hsplit := Hpot_traj_sub (p := p) (m := m) (n := n) (siteH p m j U) U i
  have h1 : |stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)|
      ≤ 2 * (n : ℝ) + 3 := by
    simpa only [Real.norm_eq_abs] using
      abs_stepUpInd_mul_hZpot_traj_le hp0 hp1 hpne m n i j U
  have h2 : |stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)|
      ≤ 2 * (n : ℝ) + 3 := by
    simpa only [Real.norm_eq_abs] using
      abs_stepDownInd_mul_hZpot_pred_traj_le hp0 hp1 hpne m n i j U
  rw [HpotInc_eq_step_apply, hsplit]
  calc |stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)|
      ≤ |stepUpInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i)|
        + |stepDownInd p m n i U * hZpot (siteH p m j U) ((trajectory p m U n).pos i - 1)| :=
        abs_sub _ _
    _ ≤ (2 * (n : ℝ) + 3) + (2 * (n : ℝ) + 3) := add_le_add h1 h2
    _ = 4 * (n : ℝ) + 6 := by ring

/-! ### 2. The centred residual -/

/-- **The one-step centred residual of the actual `Hpot` increment**:
`HpotInc_n - E[HpotInc_n | enlFilt n]`. -/
noncomputable def centeredResidual (p : ℝ) (m n : ℕ) (i j : Fin N) : Array N → ℝ :=
  fun U => HpotInc p m n i j U
    - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U

lemma centeredResidual_def (p : ℝ) (m n : ℕ) (i j : Fin N) :
    centeredResidual p m n i j = fun U => HpotInc p m n i j U
      - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U := rfl

/-- The increment is the residual plus its `enlFilt n`-conditional mean. -/
lemma HpotInc_eq_centeredResidual_add_condExp (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = centeredResidual p m n i j
      + condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) := by
  funext U
  simp only [centeredResidual, Pi.add_apply]
  ring

/-- **Integrability of the centred residual.** -/
theorem integrable_centeredResidual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    Integrable (centeredResidual p m n i j) (arrayMeasure N) := by
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  exact hf.sub (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := HpotInc p m n i j))

/-- **Zero conditional mean of the centred residual.** -/
theorem condExp_centeredResidual_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N) (centeredResidual p m n i j) =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  have hsub : condExp (enlFilt p m n) (arrayMeasure N) (centeredResidual p m n i j)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)
        - condExp (enlFilt p m n) (arrayMeasure N)
            (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) := by
    have h := condExp_sub (μ := arrayMeasure N) (f := HpotInc p m n i j)
      (g := condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
      hf integrable_condExp (enlFilt p m n)
    show condExp (enlFilt p m n) (arrayMeasure N)
      (fun U => HpotInc p m n i j U
        - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) =ᵐ[arrayMeasure N] _
    exact h
  have htower : condExp (enlFilt p m n) (arrayMeasure N)
        (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) :=
    condExp_condExp_of_le (μ := arrayMeasure N) (f := HpotInc p m n i j) le_rfl hle
  filter_upwards [hsub, htower] with U hU hU'
  rw [hU]
  show condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U
      - condExp (enlFilt p m n) (arrayMeasure N)
          (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) U = 0
  rw [hU', sub_self]

/-- **The centred residual has zero total mean.** -/
theorem integral_centeredResidual_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∫ U, centeredResidual p m n i j U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  have hsub : ∫ U, centeredResidual p m n i j U ∂(arrayMeasure N)
      = ∫ U, HpotInc p m n i j U ∂(arrayMeasure N)
        - ∫ U, condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U
            ∂(arrayMeasure N) := by
    rw [centeredResidual_def]
    exact integral_sub hf (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n)
      (f := HpotInc p m n i j))
  rw [hsub, integral_condExp hle, sub_self]

/-- **The `enlFilt n`-conditional mean of the increment is itself bounded by `4n+6`.** -/
theorem abs_condExp_HpotInc_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      |condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U| ≤ 4 * (n : ℝ) + 6 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  have h1 := abs_condExp_ae_le_condExp_abs (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := HpotInc p m n i j)
  have h2 : condExp (enlFilt p m n) (arrayMeasure N) (fun U => |HpotInc p m n i j U|)
      ≤ᵐ[arrayMeasure N] fun _ => 4 * (n : ℝ) + 6 := by
    have hmono := condExp_mono (μ := arrayMeasure N) (m := enlFilt p m n)
      (f := fun U => |HpotInc p m n i j U|) (g := fun _ => 4 * (n : ℝ) + 6)
      hf.abs (integrable_const (4 * (n : ℝ) + 6))
      (Filter.Eventually.of_forall fun U => abs_HpotInc_le hp0 hp1 m n i j U)
    rwa [condExp_const hle] at hmono
  filter_upwards [h1, h2] with U h1U h2U
  exact h1U.trans h2U

/-- **The linear deterministic a.e. bound on the centred residual.**
`|HpotInc_n - E[HpotInc_n | enlFilt n]| <= 2 * (4n+6) = 8n+12`. -/
theorem abs_centeredResidual_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), |centeredResidual p m n i j U| ≤ 8 * (n : ℝ) + 12 := by
  have hce := abs_condExp_HpotInc_le hp0 hp1 m n i j
  filter_upwards [hce] with U hU
  have h1 : |HpotInc p m n i j U| ≤ 4 * (n : ℝ) + 6 := abs_HpotInc_le hp0 hp1 m n i j U
  have h2 : |HpotInc p m n i j U
      - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U|
      ≤ |HpotInc p m n i j U|
        + |condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U| := abs_sub _ _
  show |HpotInc p m n i j U
      - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U| ≤ 8 * (n : ℝ) + 12
  linarith

/-- **Integral form of the linear bound**: `∫ |centeredResidual_n| <= 8n+12`. -/
theorem integral_abs_centeredResidual_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∫ U, |centeredResidual p m n i j U| ∂(arrayMeasure N) ≤ 8 * (n : ℝ) + 12 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h := integral_mono_ae
    (integrable_centeredResidual hp0 hp1 m n i j).abs
    (integrable_const (8 * (n : ℝ) + 12))
    (abs_centeredResidual_le hp0 hp1 m n i j)
  simpa using h

/-! ### 3. The restricted residual: increment minus the restricted drift -/

/-- **Restricted residual bridge.**  If `A` is an `enlFilt n`-event and the *integrated restricted
drift identity* `E[1_A HpotInc_n | enlFilt n] =ᵐ 1_A d` holds for some drift function `d`, then on
`A` the centred residual is the actual increment minus `d`:

  `1_A centeredResidual_n =ᵐ 1_A (HpotInc_n - d)`.

This is exactly the shape in which the below-record, record and above-record bounds of the other
directions enter the centred decomposition: the hypothesis `hD` is the restricted identity, not a
global conditional expectation, and no future independence is used. -/
theorem indicator_centeredResidual_eq_of_restricted_drift {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (i j : Fin N)
    {A : Set (Array N)} {d : Array N → ℝ}
    (hA : MeasurableSet[enlFilt p m n] A)
    (hD : condExp (enlFilt p m n) (arrayMeasure N) (A.indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] A.indicator d) :
    A.indicator (centeredResidual p m n i j)
      =ᵐ[arrayMeasure N] A.indicator (fun U => HpotInc p m n i j U - d U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  -- pull the `enlFilt n`-measurable indicator out of the conditional expectation
  have hpull : A.indicator (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] A.indicator d :=
    (condExp_indicator hf hA).symm.trans hD
  have hsub : A.indicator (centeredResidual p m n i j)
      = A.indicator (HpotInc p m n i j)
        - A.indicator (condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)) := by
    show A.indicator (fun U => HpotInc p m n i j U
        - condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) = _
    exact Set.indicator_sub A _ _
  rw [hsub]
  filter_upwards [hpull] with U hU
  by_cases h : U ∈ A
  · simp only [Pi.sub_apply, Set.indicator_of_mem h] at hU ⊢
    rw [hU]
  · simp only [Pi.sub_apply, Set.indicator_of_notMem h, sub_self]

/-- **The centred residual on the record region**, using the integrated
`RecordTower.condExp_indicator_HpotInc_enlFilt_zero`: on `A_0 = {X_n^i = M_n^j}` the residual is
the actual increment minus the record drift `alpha e_0 - (1-alpha) HprevAt`. -/
theorem indicator_centeredResidual_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    (abovePosSet p m n i j 0).indicator (centeredResidual p m n i j)
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j 0).indicator
        (fun U => HpotInc p m n i j U
          - (alphaFun p m n i U * eRec p m n j 0 U
            - (1 - alphaFun p m n i U) * HprevAt p m n j U)) := by
  refine indicator_centeredResidual_eq_of_restricted_drift hp1 hp2 m n i j
    (measurableSet_abovePosSet_enlFilt p m n i j 0) ?_
  exact condExp_indicator_HpotInc_enlFilt_zero p hp1 hp2 m n hij

/-- **Above-record interface (direction A).**  If the above-record restricted `enlFilt n` identity
of direction A holds with drift `d` on `A_g = {X_n^i = M_n^j + g}`, then on `A_g` the centred
residual is `HpotInc - d`.  The drift identity is an explicit hypothesis: it is *not* proved in
this file. -/
theorem indicator_centeredResidual_above_of_drift {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (i j : Fin N) (g : ℕ)
    {d : Array N → ℝ}
    (hD : condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator d) :
    (abovePosSet p m n i j g).indicator (centeredResidual p m n i j)
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
        (fun U => HpotInc p m n i j U - d U) :=
  indicator_centeredResidual_eq_of_restricted_drift hp0 hp1 m n i j
    (measurableSet_abovePosSet_enlFilt p m n i j g) hD

/-- **The residual has zero integral on every `enlFilt n`-event** (set-integral form of the
zero conditional mean). -/
theorem setIntegral_centeredResidual_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A) :
    ∫ U in A, centeredResidual p m n i j U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) := integrable_HpotInc hp0 hp1 (by linarith) m n i j
  have hsub : ∫ U in A, centeredResidual p m n i j U ∂(arrayMeasure N)
      = ∫ U in A, HpotInc p m n i j U ∂(arrayMeasure N)
        - ∫ U in A, condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U
            ∂(arrayMeasure N) := by
    rw [centeredResidual_def]
    exact integral_sub hf.integrableOn (integrable_condExp.integrableOn)
  rw [hsub, setIntegral_condExp hle hf hA, sub_self]

/-- **Region-wise residual bound from a restricted drift.**  On an `enlFilt n`-event `A` where the
restricted drift identity holds with a drift `d` bounded by `B`, the residual at every point of `A`
is bounded by the one-step bound plus `B`:

  `U ∈ A → |centeredResidual_n U| ≤ 4n + 6 + B`.

Together with the region drift bounds of the other directions this is the interface through which
the linear bounds enter the centred decomposition. -/
theorem abs_centeredResidual_le_of_restricted_drift {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (i j : Fin N)
    {A : Set (Array N)} {d : Array N → ℝ} {B : ℝ}
    (hA : MeasurableSet[enlFilt p m n] A)
    (hD : condExp (enlFilt p m n) (arrayMeasure N) (A.indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] A.indicator d)
    (hd : ∀ᵐ U ∂(arrayMeasure N), U ∈ A → |d U| ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ A → |centeredResidual p m n i j U| ≤ 4 * (n : ℝ) + 6 + B := by
  have hbridge := indicator_centeredResidual_eq_of_restricted_drift hp0 hp1 m n i j hA hD
  filter_upwards [hbridge, hd] with U hU hdbd hmem
  have hR : A.indicator (centeredResidual p m n i j) U = centeredResidual p m n i j U :=
    Set.indicator_of_mem hmem (centeredResidual p m n i j)
  have hfd : A.indicator (fun U => HpotInc p m n i j U - d U) U
      = HpotInc p m n i j U - d U :=
    Set.indicator_of_mem hmem _
  rw [hR, hfd] at hU
  rw [hU]
  have h1 : |HpotInc p m n i j U| ≤ 4 * (n : ℝ) + 6 := abs_HpotInc_le hp0 hp1 m n i j U
  have h2 : |d U| ≤ B := hdbd hmem
  calc |HpotInc p m n i j U - d U| ≤ |HpotInc p m n i j U| + |d U| := abs_sub _ _
    _ ≤ (4 * (n : ℝ) + 6) + B := add_le_add h1 h2

/-- **The record drift is bounded by `4n+8` a.e.**: with `0 ≤ alpha ≤ 1`, `1 ≤ e_0 ≤ b_n` and
`|HprevAt| ≤ 2n+3`,

  `|alpha e_0 - (1-alpha) HprevAt| ≤ |e_0| + |HprevAt| ≤ (2n+5) + (2n+3) = 4n+8`. -/
theorem abs_recordDrift_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N),
      |alphaFun p m n i U * eRec p m n j 0 U
        - (1 - alphaFun p m n i U) * HprevAt p m n j U| ≤ 4 * (n : ℝ) + 8 := by
  filter_upwards [one_le_eRec_zero hp1 hp2 m (n := n) j,
    eRec_zero_le_bRec_unconditional hp1 hp2 m n j] with U h1 hb
  have hα0 : 0 ≤ alphaFun p m n i U := (alphaFun_mem_Icc hp1 hp2 m n i U).1
  have hα1 : alphaFun p m n i U ≤ 1 := (alphaFun_mem_Icc hp1 hp2 m n i U).2
  have hβ0 : 0 ≤ 1 - alphaFun p m n i U := by linarith
  have hβ1 : 1 - alphaFun p m n i U ≤ 1 := by linarith
  have h1' : (1 : ℝ) ≤ eRec p m n j 0 U := by simpa using h1
  have he0pos : 0 < eRec p m n j 0 U := by linarith
  have hprev_abs : |HprevAt p m n j U| ≤ 2 * (n : ℝ) + 3 := abs_HprevAt_le hp1 hp2 m n j U
  have h4 : HprevAt p m n j U ≤ 2 * (n : ℝ) + 3 := (abs_le.mp hprev_abs).2
  have he_abs : |eRec p m n j 0 U| ≤ 2 * (n : ℝ) + 5 := by
    rw [abs_of_pos he0pos]
    have hb' : eRec p m n j 0 U ≤ HprevAt p m n j U + 2 := by
      simpa only [bRec] using hb
    linarith
  calc |alphaFun p m n i U * eRec p m n j 0 U
        - (1 - alphaFun p m n i U) * HprevAt p m n j U|
      ≤ |alphaFun p m n i U * eRec p m n j 0 U|
        + |(1 - alphaFun p m n i U) * HprevAt p m n j U| := abs_sub _ _
    _ = alphaFun p m n i U * |eRec p m n j 0 U|
        + (1 - alphaFun p m n i U) * |HprevAt p m n j U| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg hβ0]
    _ ≤ 1 * (2 * (n : ℝ) + 5) + 1 * (2 * (n : ℝ) + 3) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hα1 he_abs (abs_nonneg _) (by linarith)
        · exact mul_le_mul hβ1 hprev_abs (abs_nonneg _) (by linarith)
    _ = 4 * (n : ℝ) + 8 := by ring

/-- **Record-region residual bound.**  Instantiation of the restricted-drift bridge at the record
region `A_0`, with the integrated record drift identity and the explicit record-drift bound
`4n+8`: on `A_0` the residual is bounded by `8n+14`. -/
theorem abs_centeredResidual_le_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ U ∂(arrayMeasure N), U ∈ abovePosSet p m n i j 0 →
      |centeredResidual p m n i j U| ≤ 8 * (n : ℝ) + 14 := by
  have h := abs_centeredResidual_le_of_restricted_drift (B := 4 * (n : ℝ) + 8)
    hp1 hp2 m n i j (measurableSet_abovePosSet_enlFilt p m n i j 0)
    (condExp_indicator_HpotInc_enlFilt_zero p hp1 hp2 m n hij)
    ((abs_recordDrift_le hp1 hp2 m n i j).mono (fun U h _ => h))
  filter_upwards [h] with U hU hmem
  linarith [hU hmem]

/-! ### 4. Successive residuals and the martingale-difference candidate -/

/-- The partial sums of the one-step centred residuals at the successive times `0, …, n-1`. -/
noncomputable def centeredResidualSum (p : ℝ) (m : ℕ) (i j : Fin N) (n : ℕ) : Array N → ℝ :=
  fun U => ∑ k ∈ Finset.range n, centeredResidual p m k i j U

lemma centeredResidualSum_zero (p : ℝ) (m : ℕ) (i j : Fin N) :
    centeredResidualSum p m i j 0 = 0 := by
  funext U
  simp [centeredResidualSum]

lemma centeredResidualSum_succ (p : ℝ) (m : ℕ) (i j : Fin N) (n : ℕ) :
    centeredResidualSum p m i j (n + 1)
      = centeredResidualSum p m i j n + centeredResidual p m n i j := by
  funext U
  simp only [centeredResidualSum, Pi.add_apply, Finset.sum_range_succ]

/-- The partial sums are integrable. -/
theorem integrable_centeredResidualSum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) (n : ℕ) :
    Integrable (centeredResidualSum p m i j n) (arrayMeasure N) := by
  have hsum : centeredResidualSum p m i j n
      = fun U => ∑ k ∈ Finset.range n, centeredResidual p m k i j U := rfl
  rw [hsum]
  exact integrable_finsetSum _ fun k _ => integrable_centeredResidual hp0 hp1 m k i j

/-- **The partial sums of the residuals have zero mean.** -/
theorem integral_centeredResidualSum_eq_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) (n : ℕ) :
    ∫ U, centeredResidualSum p m i j n U ∂(arrayMeasure N) = 0 := by
  have hsum : centeredResidualSum p m i j n
      = fun U => ∑ k ∈ Finset.range n, centeredResidual p m k i j U := rfl
  rw [hsum, integral_finsetSum]
  · simp only [integral_centeredResidual_eq_zero hp0 hp1 m _ i j, Finset.sum_const_zero]
  · intro k _
    exact integrable_centeredResidual hp0 hp1 m k i j

/-- **Partial sums are `enlFilt n`-strongly-measurable under the adaptedness interface**: for each
`k < n` the residual at time `k` is required to be `enlFilt (k+1)`-measurable.  This adaptedness is
*not* proved here: `envH` reads the full site-mark array, not only the revealed coordinates. -/
lemma stronglyMeasurable_centeredResidualSum {p : ℝ} {m : ℕ} {i j : Fin N}
    (hadapt : ∀ n, StronglyMeasurable[enlFilt p m (n + 1)] (centeredResidual p m n i j))
    (n : ℕ) :
    StronglyMeasurable[enlFilt p m n] (centeredResidualSum p m i j n) := by
  have hsum : centeredResidualSum p m i j n
      = fun U => ∑ k ∈ Finset.range n, centeredResidual p m k i j U := rfl
  rw [hsum]
  have hmeas : ∀ k ∈ Finset.range n,
      StronglyMeasurable[enlFilt p m n] (centeredResidual p m k i j) := by
    intro k hk
    exact (hadapt k).mono ((enlFilt p m).mono (by
      have := Finset.mem_range.mp hk
      omega))
  have hsumfun : (fun U => ∑ k ∈ Finset.range n, centeredResidual p m k i j U)
      = ∑ k ∈ Finset.range n, centeredResidual p m k i j := by
    funext U
    simp only [Finset.sum_apply]
  rw [hsumfun]
  exact Finset.stronglyMeasurable_sum (Finset.range n) hmeas

/-- **One-step martingale-difference relation**, under the adaptedness interface:
`E[S_{n+1} | enlFilt n] =ᵐ S_n`. -/
theorem condExp_centeredResidualSum_succ_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    (hadapt : ∀ n, StronglyMeasurable[enlFilt p m (n + 1)] (centeredResidual p m n i j))
    (n : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N) (centeredResidualSum p m i j (n + 1))
      =ᵐ[arrayMeasure N] centeredResidualSum p m i j n := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hS := centeredResidualSum_succ p m i j n
  rw [hS]
  have h1 := condExp_add (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := centeredResidualSum p m i j n) (g := centeredResidual p m n i j)
    (integrable_centeredResidualSum hp0 hp1 m i j n)
    (integrable_centeredResidual hp0 hp1 m n i j)
  have h2 : condExp (enlFilt p m n) (arrayMeasure N) (centeredResidualSum p m i j n)
      =ᵐ[arrayMeasure N] centeredResidualSum p m i j n :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable hle (stronglyMeasurable_centeredResidualSum hadapt n)
        (integrable_centeredResidualSum hp0 hp1 m i j n))
  have h3 := condExp_centeredResidual_eq_zero hp0 hp1 m n i j
  refine h1.trans ?_
  filter_upwards [h2, h3] with U h2U h3U
  simp only [Pi.add_apply, Pi.zero_apply, h2U, h3U, add_zero]

/-- **The martingale-difference identity at all pairs of times**, under the adaptedness
interface. -/
theorem condExp_centeredResidualSum_eq_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    (hadapt : ∀ n, StronglyMeasurable[enlFilt p m (n + 1)] (centeredResidual p m n i j))
    {a b : ℕ} (hab : a ≤ b) :
    condExp (enlFilt p m a) (arrayMeasure N) (centeredResidualSum p m i j b)
      =ᵐ[arrayMeasure N] centeredResidualSum p m i j a := by
  induction b, hab using Nat.le_induction with
  | base =>
      haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
      have hle : enlFilt p m a ≤ (inferInstance : MeasurableSpace (Array N)) :=
        (enlFilt p m).le a
      haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
      exact Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable hle (stronglyMeasurable_centeredResidualSum hadapt a)
          (integrable_centeredResidualSum hp0 hp1 m i j a))
  | succ n han ih =>
      have hstep := condExp_centeredResidualSum_succ_of_adapted hp0 hp1 m i j hadapt n
      have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
      haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
      have htower : condExp (enlFilt p m a) (arrayMeasure N)
            (condExp (enlFilt p m n) (arrayMeasure N) (centeredResidualSum p m i j (n + 1)))
          =ᵐ[arrayMeasure N] condExp (enlFilt p m a) (arrayMeasure N)
            (centeredResidualSum p m i j (n + 1)) :=
        condExp_condExp_of_le (μ := arrayMeasure N) ((enlFilt p m).mono han) hle
      exact htower.symm.trans ((condExp_congr_ae (μ := arrayMeasure N)
        (m := enlFilt p m a) hstep).trans ih)

/-- **The martingale-difference candidate, packaged.**  Under the adaptedness interface the
partial sums of the one-step centred residuals form a genuine `MeasureTheory.Martingale` with
respect to the enlarged filtration.  No future independence, SLLN or `Q` estimate is used. -/
theorem martingale_centeredResidualSum_of_adapted {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    (hadapt : ∀ n, StronglyMeasurable[enlFilt p m (n + 1)] (centeredResidual p m n i j)) :
    Martingale (centeredResidualSum p m i j) (enlFilt p m) (arrayMeasure N) :=
  ⟨fun n => stronglyMeasurable_centeredResidualSum hadapt n,
    fun _ _ hab => condExp_centeredResidualSum_eq_of_adapted hp0 hp1 m i j hadapt hab⟩

/-- **Summary of the unconditional one-step residual facts.**  Everything in this conjunction is
proved without any adaptedness assumption; the missing adaptedness appears only in
`martingale_centeredResidualSum_of_adapted` as an explicit hypothesis. -/
theorem centeredResidual_candidate {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (i j : Fin N) :
    (∀ n, Integrable (centeredResidual p m n i j) (arrayMeasure N)) ∧
    (∀ n, condExp (enlFilt p m n) (arrayMeasure N) (centeredResidual p m n i j)
      =ᵐ[arrayMeasure N] 0) ∧
    (∀ n, ∀ᵐ U ∂(arrayMeasure N), |centeredResidual p m n i j U| ≤ 8 * (n : ℝ) + 12) ∧
    (∀ n, ∫ U, centeredResidualSum p m i j n U ∂(arrayMeasure N) = 0) :=
  ⟨fun n => integrable_centeredResidual hp0 hp1 m n i j,
    fun n => condExp_centeredResidual_eq_zero hp0 hp1 m n i j,
    fun n => abs_centeredResidual_le hp0 hp1 m n i j,
    fun n => integral_centeredResidualSum_eq_zero hp0 hp1 m i j n⟩

/-! ### Axiom audit -/


end Swarming.Enl
