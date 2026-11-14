/-
  **DIRECTION A (m1) — `AboveTower.lean`: the ACTUAL one-step `Hpot` drift above the record,
  restricted to the enlarged filtration `enlFilt p m n`.**

  For the actual trajectory `Swarming.Trajectory.trajectory`, the actual array measure
  `arrayMeasure N`, the actual full-history environment `envH p m j` (= `AboveActualDrift.siteH`
  definitionally) and the above-record event

      A_g = abovePosSet p m n i j g = {X_n^i = M_n^j + g},      M_n^j = recVal j (prefOf p m n U),

  this file proves, for `g ≥ 1`,

      (arrayMeasure N)[ 1_{A_g} (H(X_{n+1}^i) - H(X_n^i)) | enlFilt n ]
        =ᵐ 1_{A_g} [ alpha_n^i * e_g - (1 - alpha_n^i) * e_{g-1} ],

  where `H = SwarmOcc.Hpot` at the actual full-history environment, `e_g = RecordAbove.eRec` is the
  actual random record sequence `e_g = Φ^g(E[h_j(M_n^j) | enlFilt n])`, and `alpha_n^i` is the
  **random** right probability `alphaFun p m n i` (never a fixed scalar).

  Route (every ingredient integrated, so no external hypothesis remains):

  * `AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet` — the actual `infoPiece p m n j
    (g-1)`-conditional identity, applied verbatim to the common increment `RecordTower.HpotInc`
    (`envH` and `siteH` are definitionally the same environment, `siteH_eq_envH`);
  * `RecordTower.measurableSet_abovePosSet_enlFilt` — `A_g` is `enlFilt n`-measurable (it is
    path-determined), so it can be used as a multiplier at `enlFilt n`;
  * `RecEnv.enlMeas_le_infoPiece` — the **valid** tower direction `enlFilt n ≤ infoPiece (g-1)`;
    `infoPiece (g-1)` is the record information that has *not* yet read the site `M_n^j+g`;
  * `RecordAbove.eRec_eq_condExp` + `ShiftedSeed.shiftG_H0` — `E[h_j(M_n^j+g) | enlFilt n] = e_g`;
  * algebra: the bracket `alpha (1 + a (1 + H_{g-1})) - (1-alpha) H_{g-1}` restricted to `A_g`
    equals `1_{A_g} alpha (1+a) + 1_{A_g} (alpha a - (1-alpha)) H_{g-1}`, and the second factor is
    pulled out of the `enlFilt`-conditional mean after multiplying by `H_{g-1} = h_j(M_n^j+g-1)`;
    `RecordAbove.eRec_succ` (`e_g = 1 + a (1 + e_{g-1})`) closes the bracket.

  Consequence (`m ≥ 2`): the restricted `(Zloss)` bound above the record

      (fun U => 1_{A_g} (-(b_n a^g))) ≤ᵐ (arrayMeasure N)[ 1_{A_g}(H(X_{n+1}^i) - H(X_n^i)) | enlFilt n ],

  with `b_n = RecordAbove.bRec` the paper's `h_j(M_n^j-1)+2`.  The random-`alpha` inequality is
  discharged pointwise from `SwarmOcc.zdrift_above` (not from the fixed-`α` theorem
  `RecordAbove.eRec_zdrift_above`), and the set-integral (mass) form is derived with
  `integral_condExp` / `integral_indicator`.

  Nothing here sums the drift over `g`, and nothing claims `Q`, occupation, regeneration or
  Ballistic behaviour.

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

/-! ### 1. The common increment normalization (`siteH` vs `envH`) -/

/-- The same, as functions of the array. -/
lemma siteH_eq_envH_fun (p : ℝ) (m : ℕ) (j : Fin N) : siteH p m j = envH p m j := rfl

/-- **The common increment is the `siteH`-form used by the integrated above-record drift.**  The
`envH` of `RecordTower.HpotInc` and the `siteH` of `AboveActualDrift` are the same term, so this is
a definitional identity: no third increment is introduced. -/
lemma HpotInc_eq_siteH_form (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j = fun U : Array N =>
      SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (siteH p m j U) ((trajectory p m U n).pos i) := rfl

/-- **Integrability of the common (unrestricted) one-step increment**, transported from
`AboveActualDrift.integrable_Hpot_traj_step` across the definitional identification. -/
theorem integrable_HpotInc_tower {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    Integrable (HpotInc p m n i j) (arrayMeasure N) :=
  integrable_Hpot_traj_step hp0 hp1 (by linarith) m n i j

/-! ### 2. The indicator of `A_g` as an `enlFilt`-measurable multiplier -/

/-- The indicator function of the above-record event `A_g`, as a real multiplier. -/
noncomputable def aboveInd (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) : Array N → ℝ :=
  (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ))

/-- `A_g` is `enlFilt n`-measurable (it is determined by the path prefix). -/
lemma measurable_aboveInd (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Measurable[enlFilt p m n] (aboveInd p m n i j g) :=
  measurable_const.indicator (measurableSet_abovePosSet_enlFilt p m n i j g)

/-- `1_{A_g}` is bounded by one. -/
lemma abs_aboveInd_le (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) (U : Array N) :
    ‖aboveInd p m n i j g U‖ ≤ 1 := by
  by_cases hU : U ∈ abovePosSet p m n i j g
  · rw [aboveInd, Set.indicator_of_mem hU]; simp
  · rw [aboveInd, Set.indicator_of_notMem hU]; simp

/-! ### 3. The pointwise random-`alpha` above-record drift inequality

`alphaFun p m n i` is a **random** multiplier, so the fixed-`α` theorem
`RecordAbove.eRec_zdrift_above` cannot be applied to it.  The inequality
`-b a^{k+1} ≤ alpha e_{k+1} - (1-alpha) e_k` is proved pointwise for `alpha = alphaFun … U`, from
`SwarmOcc.zdrift_above` itself. -/

/-- **Pointwise (random-`alpha`) above-record `(Zloss)` bound.**  For `m ≥ 2`, every `k`, with the
actual random right probability `alpha_n^i`, the actual `b_n = h_j(M_n^j-1) + 2` and the actual
record sequence `e_g = eRec`:

  `-(b_n a^{k+1}) ≤ᵐ alpha_n^i e_{k+1} - (1 - alpha_n^i) e_k`. -/
theorem zdrift_above_eRec_alphaFun {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) (hm : 2 ≤ m) (k : ℕ) :
    (fun U : Array N => -(bRec p m n j U * aRec p m ^ (k + 1)))
      ≤ᵐ[arrayMeasure N]
        fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
          - (1 - alphaFun p m n i U) * eRec p m n j k U := by
  have hab := aRec_bounds hp1 hp2 hm
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := hab.2
  have ha13 : (1 : ℝ) / 3 ≤ aRec p m := by linarith [hab.1]
  have hne : ∀ᵐ U ∂(arrayMeasure N), ∀ g : ℕ, 0 ≤ eRec p m n j g U :=
    MeasureTheory.ae_all_iff.mpr (fun g => zero_le_eRec hp1 hp2 m j g)
  filter_upwards [eRec_zero_le_bRec_unconditional hp1 hp2 m n j, hne] with U he0 hneU
  have hbU : 0 ≤ bRec p m n j U := by
    have := three_le_bRec hp1 hp2 m n j U
    linarith
  have hα : (1 : ℝ) / 2 ≤ alphaFun p m n i U := one_half_le_alphaFun hp1 hp2 m n i U
  simpa only [neg_mul] using
    SwarmOcc.zdrift_above ha0 ha1 ha13 hbU hα (fun g => eRec p m n j g U)
      (fun g => by rw [eRec_succ]; ring) he0 (fun g => hneU g) k

/-! ### 4. The restricted bracket as an adapted multiplier times the shifted potential -/

/-- **The pointwise algebra of the above-record bracket.**  On `A_{K+1} = {X_n^i = M_n^j+K+1}`
the restricted drift bracket

  `alpha (1 + a (1 + H_K)) - (1-alpha) H_K`,     `H_K = h_j(M_n^j+K)` (`shiftG H0 K`),

is the sum of the adapted term `1_{A} alpha (1+a)` and the adapted multiple
`1_A (alpha a - (1-alpha))` of `H_K`; off `A` both sides vanish.  This is the exact shape in which
the conditional mean can be taken: only the second factor of the second term is random and needs
`E[H_K | enlFilt] = e_K`. -/
lemma indicator_bracket_eq_above (p : ℝ) (m n : ℕ) (i j : Fin N) (K : ℕ) :
    (abovePosSet p m n i j (K + 1)).indicator
        (fun U => alphaFun p m n i U
            * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j K U))
          - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j K U)
      = fun U => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m)
          + (aboveInd p m n i j (K + 1) U
              * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)))
              * shiftG (H0 p m n j) p m n j K U := by
  funext U
  by_cases hU : U ∈ abovePosSet p m n i j (K + 1)
  · rw [Set.indicator_of_mem hU, aboveInd, Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, aboveInd, Set.indicator_of_notMem hU]
    ring

/-! ### 5. The shifted full-history potential at the enlarged filtration

Two facts about `H_K = shiftG H0 K = h_j(M_n^j + K)` (`ShiftedSeed.shiftG_H0`) that are used by the
tower step and are useful on their own: its integrability and `E[H_K | enlFilt n] = e_K`.  At
`K = 0` the second is exactly `RecordTower.condExp_H0_eq_eRec_zero`. -/

/-- `H_K = h_j(M_n^j+K)` is integrable (`|H_K| ≤ 2n + 2K + 2` deterministically). -/
theorem integrable_shiftG_H0 {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (j : Fin N) (K : ℕ) :
    Integrable (fun U : Array N => shiftG (H0 p m n j) p m n j K U) (arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  refine (integrable_hof_siteMarks_add hp0 hp1 m n j K).congr ?_
  filter_upwards with U
  exact (shiftG_H0 hpne m n j K U).symm

/-- **`E[h_j(M_n^j+K) | enlFilt n] = e_K`** — the actual record sequence is the conditional mean of
the actual full-history potential at every offset above the record. -/
theorem condExp_shiftG_H0_eq_eRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (j : Fin N) (K : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => shiftG (H0 p m n j) p m n j K U)
      =ᵐ[arrayMeasure N] eRec p m n j K := by
  have hpne : p ≠ 0 := by linarith
  have hcongr : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => shiftG (H0 p m n j) p m n j K U)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + K)) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq (funext fun U => shiftG_H0 hpne m n j K U))
  exact hcongr.trans (eRec_eq_condExp hp0 hp1 m (n := n) j K).symm

/-- Consistency with the accepted record module: at `K = 0` the shifted potential is `H0`, so
`E[h_j(M_n^j) | enlFilt n] = e_0` — the statement of `RecordTower.condExp_H0_eq_eRec_zero`. -/
example {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j)
      =ᵐ[arrayMeasure N] eRec p m n j 0 := by
  have h := condExp_shiftG_H0_eq_eRec hp0 hp1 m n j 0
  rwa [shiftG_zero] at h

/-! ### 6. The restricted `enlFilt n` identity above the record -/

/-- **Tower step + the integrated above-record `infoPiece` identity.**  For `g = K+1 ≥ 1`, from the
`infoPiece K`-conditional identity (supplied as the explicit hypothesis `hD`, exactly the shape of
`AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet`) the restricted `enlFilt n`-conditional
mean holds, with `E[H_K | enlFilt] = e_K` replacing the (unread) site value `h_j(M_n^j+K)`:

  `(arrayMeasure N)[1_{A_g} HpotInc | enlFilt n] =ᵐ 1_{A_g}(alpha^i e_g - (1-alpha^i) e_{g-1})`. -/
theorem condExp_indicator_HpotInc_enlFilt_abovePosSet_succ_of_infoIdentity (p : ℝ)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) {i j : Fin N} (K : ℕ)
    (hD : condExp (infoPiece p m n j K) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (K + 1)).indicator
        (fun U => alphaFun p m n i U
            * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j K U))
          - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j K U)) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (K + 1)).indicator
        (fun U => alphaFun p m n i U * eRec p m n j (K + 1) U
          - (1 - alphaFun p m n i U) * eRec p m n j K U) := by
  have hpne : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hleI : infoPiece p m n j K ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j K
  haveI : SigmaFinite ((arrayMeasure N).trim hleI) := inferInstance
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  -- (1) the tower step `enlFilt n ≤ infoPiece K` followed by the `infoPiece K` identity
  have htower : condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j K U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j K U)) := by
    refine (MeasureTheory.condExp_condExp_of_le (μ := arrayMeasure N)
      (m₁ := enlFilt p m n) (m₂ := infoPiece p m n j K)
      (f := (abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      (enlMeas_le_infoPiece p m n j K) hleI).symm.trans ?_
    exact condExp_congr_ae hD
  -- (2) the pointwise algebra of the restricted bracket
  have hbracket : condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator
          (fun U => alphaFun p m n i U
              * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j K U))
            - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j K U))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m)
          + (aboveInd p m n i j (K + 1) U
              * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)))
              * shiftG (H0 p m n j) p m n j K U) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq (indicator_bracket_eq_above p m n i j K))
  -- (3) the shifted potential is integrable and its conditional mean is `e_K`
  have hXint : Integrable (fun U : Array N => shiftG (H0 p m n j) p m n j K U)
      (arrayMeasure N) := integrable_shiftG_H0 hp0 hp1 m n j K
  have hXcond : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => shiftG (H0 p m n j) p m n j K U)
      =ᵐ[arrayMeasure N] eRec p m n j K := condExp_shiftG_H0_eq_eRec hp0 hp1 m n j K
  -- (4) the two bounded adapted multipliers
  have hαbdd : ∀ U : Array N, ‖alphaFun p m n i U‖ ≤ 1 := by
    intro U
    rw [Real.norm_eq_abs, abs_of_nonneg (alphaFun_mem_Icc hp0 hp1 m n i U).1]
    exact (alphaFun_mem_Icc hp0 hp1 m n i U).2
  have h1a : (0 : ℝ) ≤ 1 + aRec p m := by linarith [zero_le_aRec hp0 hp1 m]
  have h1b : 1 + aRec p m ≤ 2 := by linarith [aRec_lt_one hp0 hp1 m]
  have hb1 : ∀ U : Array N,
      ‖aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m)‖ ≤ 2 := by
    intro U
    rw [norm_mul, norm_mul]
    have h1 : ‖aboveInd p m n i j (K + 1) U‖ ≤ 1 := abs_aboveInd_le p m n i j (K + 1) U
    have h2 : ‖alphaFun p m n i U‖ ≤ 1 := hαbdd U
    have h3 : ‖(1 + aRec p m : ℝ)‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h1a]; exact h1b
    have h12 : ‖aboveInd p m n i j (K + 1) U‖ * ‖alphaFun p m n i U‖ ≤ 1 * 1 :=
      mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    calc ‖aboveInd p m n i j (K + 1) U‖ * ‖alphaFun p m n i U‖ * ‖(1 + aRec p m : ℝ)‖
        ≤ (1 * 1) * 2 := mul_le_mul h12 h3 (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hb2 : ∀ U : Array N,
      ‖aboveInd p m n i j (K + 1) U
        * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U))‖ ≤ 2 := by
    intro U
    rw [norm_mul]
    have h1 : ‖aboveInd p m n i j (K + 1) U‖ ≤ 1 := abs_aboveInd_le p m n i j (K + 1) U
    have h2 : ‖alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)‖ ≤ 2 := by
      have ha : ‖aRec p m‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_aRec hp0 hp1 m)]
        linarith [aRec_lt_one hp0 hp1 m]
      have hp1' : ‖alphaFun p m n i U * aRec p m‖ ≤ 1 := by
        calc ‖alphaFun p m n i U * aRec p m‖ = ‖alphaFun p m n i U‖ * ‖aRec p m‖ := norm_mul _ _
          _ ≤ 1 * 1 := mul_le_mul (hαbdd U) ha (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hp2' : ‖1 - alphaFun p m n i U‖ ≤ 1 := by
        have h0 := (alphaFun_mem_Icc hp0 hp1 m n i U).1
        have h1' := (alphaFun_mem_Icc hp0 hp1 m n i U).2
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      calc ‖alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)‖
          ≤ ‖alphaFun p m n i U * aRec p m‖ + ‖1 - alphaFun p m n i U‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hp1' hp2'
        _ = 2 := by norm_num
    calc ‖aboveInd p m n i j (K + 1) U‖
          * ‖alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)‖
        ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 2 := by norm_num
  -- (5) integrability of the two products
  have hfameas : Measurable[enlFilt p m n]
      (fun U : Array N => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m)) :=
    ((measurable_aboveInd p m n i j (K + 1)).mul (measurable_alphaFun_enl p m n i)).mul
      measurable_const
  have hfaamb : Measurable
      (fun U : Array N => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m)) :=
    measurable_ambient_of_enlFilt hfameas
  have hfaint : Integrable
      (fun U : Array N => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m))
      (arrayMeasure N) :=
    Integrable.mono' (integrable_const 2) hfaamb.aestronglyMeasurable
      (Filter.Eventually.of_forall hb1)
  have hf2meas : Measurable[enlFilt p m n]
      (fun U : Array N => aboveInd p m n i j (K + 1) U
        * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U))) :=
    (measurable_aboveInd p m n i j (K + 1)).mul
      (((measurable_alphaFun_enl p m n i).mul measurable_const).sub
        (measurable_const.sub (measurable_alphaFun_enl p m n i)))
  have hf2amb : Measurable
      (fun U : Array N => aboveInd p m n i j (K + 1) U
        * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U))) :=
    measurable_ambient_of_enlFilt hf2meas
  have hf2Xint : Integrable
      (fun U : Array N => (aboveInd p m n i j (K + 1) U
        * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)))
          * shiftG (H0 p m n j) p m n j K U) (arrayMeasure N) :=
    hXint.bdd_mul hf2amb.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  -- (6) the conditional means of the two summands
  have hfacond : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m))
      =ᵐ[arrayMeasure N]
        fun U => aboveInd p m n i j (K + 1) U * alphaFun p m n i U * (1 + aRec p m) :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable hle hfameas.stronglyMeasurable hfaint)
  have hf2Xcond : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U : Array N => (aboveInd p m n i j (K + 1) U
          * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)))
            * shiftG (H0 p m n j) p m n j K U)
      =ᵐ[arrayMeasure N] fun U => (aboveInd p m n i j (K + 1) U
          * (alphaFun p m n i U * aRec p m - (1 - alphaFun p m n i U)))
            * condExp (enlFilt p m n) (arrayMeasure N)
              (fun U => shiftG (H0 p m n j) p m n j K U) U :=
    condExp_stronglyMeasurable_mul_of_bound (m := enlFilt p m n) hle
      hf2meas.stronglyMeasurable hXint 2 (Filter.Eventually.of_forall hb2)
  -- (7) linearity and the final pointwise identification
  refine (htower.trans hbracket).trans ?_
  refine (condExp_add hfaint hf2Xint (enlFilt p m n)).trans ?_
  refine (hfacond.add hf2Xcond).trans ?_
  filter_upwards [hXcond] with U hU
  simp only [Pi.add_apply]
  rw [hU]
  by_cases hU' : U ∈ abovePosSet p m n i j (K + 1)
  · rw [Set.indicator_of_mem hU', aboveInd, Set.indicator_of_mem hU',
      eRec_succ p m n j K U]
    ring
  · rw [Set.indicator_of_notMem hU', aboveInd, Set.indicator_of_notMem hU']
    ring

/-- **The actual restricted `enlFilt n` above-record identity.**  For distinct walkers and
`g = K+1 ≥ 1`, specialised to the integrated `infoPiece K` identity
`AboveActualDrift.condExp_indicator_Hpot_step_abovePosSet`:

  `(arrayMeasure N)[1_{A_{K+1}} HpotInc | enlFilt n]`
    `=ᵐ 1_{A_{K+1}}(alpha_n^i e_{K+1} - (1 - alpha_n^i) e_K)`. -/
theorem condExp_indicator_HpotInc_enlFilt_abovePosSet_succ (p : ℝ)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j) (K : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (K + 1)).indicator
        (fun U => alphaFun p m n i U * eRec p m n j (K + 1) U
          - (1 - alphaFun p m n i U) * eRec p m n j K U) :=
  condExp_indicator_HpotInc_enlFilt_abovePosSet_succ_of_infoIdentity p hp0 hp1 m n K
    (condExp_indicator_Hpot_step_abovePosSet_succ p hp0 hp1 hij K)

/-- **The actual restricted `enlFilt n` above-record identity, any `g ≥ 1`:**

  `(arrayMeasure N)[1_{A_g} HpotInc | enlFilt n]`
    `=ᵐ 1_{A_g}(alpha_n^i e_g - (1 - alpha_n^i) e_{g-1})`. -/
theorem condExp_indicator_HpotInc_enlFilt_abovePosSet (p : ℝ)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j)
    {g : ℕ} (hg : 1 ≤ g) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j g).indicator
        (fun U => alphaFun p m n i U * eRec p m n j g U
          - (1 - alphaFun p m n i U) * eRec p m n j (g - 1) U) := by
  obtain ⟨K, rfl⟩ : ∃ K, g = K + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    condExp_indicator_HpotInc_enlFilt_abovePosSet_succ (p := p) hp0 hp1 m n hij K

/-! ### 7. The restricted `(Zloss)` lower bound above the record -/

/-- **The restricted above-record `(Zloss)` bound**, in "direction-D identity as an explicit
hypothesis" form (successor version).  Nothing else is assumed: the random-`alpha` pointwise
inequality `zdrift_above_eRec_alphaFun` and the restricted `enlFilt` identity are the only inputs. -/
theorem indicator_le_condExp_indicator_HpotInc_abovePosSet_succ_of_infoIdentity (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hm : 2 ≤ m) (K : ℕ)
    (hD : condExp (infoPiece p m n j K) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (K + 1)).indicator
        (fun U => alphaFun p m n i U
            * (1 + aRec p m * (1 + shiftG (H0 p m n j) p m n j K U))
          - (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j K U)) :
    (fun U : Array N => (abovePosSet p m n i j (K + 1)).indicator
        (fun U => -(bRec p m n j U * aRec p m ^ (K + 1))) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j)) := by
  have hspec :=
    condExp_indicator_HpotInc_enlFilt_abovePosSet_succ_of_infoIdentity p hp1 hp2 m n K hD
  have hpt := zdrift_above_eRec_alphaFun hp1 hp2 m n i j hm K
  filter_upwards [hpt, hspec] with U h1 h2
  rw [h2]
  by_cases hU : U ∈ abovePosSet p m n i j (K + 1)
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    exact h1
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-- **The restricted above-record `(Zloss)` bound** (successor form, `m ≥ 2`):

  `(fun U => 1_{A_{K+1}} (-(b_n a^{K+1}))) ≤ᵐ (arrayMeasure N)[1_{A_{K+1}} HpotInc | enlFilt n]`.

The pointwise inequality is `zdrift_above_eRec_alphaFun` (random `alpha`). -/
theorem indicator_le_condExp_indicator_HpotInc_abovePosSet_succ (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j)
    (hm : 2 ≤ m) (K : ℕ) :
    (fun U : Array N => (abovePosSet p m n i j (K + 1)).indicator
        (fun U => -(bRec p m n j U * aRec p m ^ (K + 1))) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j (K + 1)).indicator (HpotInc p m n i j)) :=
  indicator_le_condExp_indicator_HpotInc_abovePosSet_succ_of_infoIdentity p hp1 hp2 m n hm K
    (condExp_indicator_Hpot_step_abovePosSet_succ p hp1 hp2 hij K)

/-- **The restricted above-record `(Zloss)` bound, any `g ≥ 1`** (`m ≥ 2`):

  `(fun U => 1_{A_g} (-(b_n a^g))) ≤ᵐ (arrayMeasure N)[1_{A_g} HpotInc | enlFilt n]`. -/
theorem indicator_le_condExp_indicator_HpotInc_abovePosSet (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j)
    (hm : 2 ≤ m) {g : ℕ} (hg : 1 ≤ g) :
    (fun U : Array N => (abovePosSet p m n i j g).indicator
        (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) := by
  obtain ⟨K, rfl⟩ : ∃ K, g = K + 1 := ⟨g - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    indicator_le_condExp_indicator_HpotInc_abovePosSet_succ (p := p) hp1 hp2 m n hij hm K

/-! ### 8. Integrability and the set-integral (mass) form -/

/-- The restricted increment `1_{A_g} HpotInc` is integrable for every `g`. -/
theorem integrable_indicator_HpotInc_abovePosSet_tower {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Integrable ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) (arrayMeasure N) := by
  have hA : MeasurableSet (abovePosSet p m n i j g) :=
    infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)
  exact (integrable_HpotInc_tower hp1 hp2 m n i j).indicator hA

/-- **The set-integral form of the above-record lower bound** (`m ≥ 2`, `g ≥ 1`):

  `∫_{A_g} -(b_n a^g) ≤ ∫_{A_g} HpotInc`,

obtained by integrating the a.e. conditional inequality with `integral_condExp` and
`integral_indicator`.  This is the shape the finite-offset partition sums. -/
theorem setIntegral_le_setIntegral_HpotInc_enlFilt_abovePosSet (p : ℝ)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j)
    (hm : 2 ≤ m) {g : ℕ} (hg : 1 ≤ g) :
    ∫ U in abovePosSet p m n i j g, (-(bRec p m n j U * aRec p m ^ g)) ∂(arrayMeasure N)
      ≤ ∫ U in abovePosSet p m n i j g, HpotInc p m n i j U ∂(arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hA : MeasurableSet (abovePosSet p m n i j g) :=
    infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)
  have hInt : Integrable ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      (arrayMeasure N) := integrable_indicator_HpotInc_abovePosSet_tower hp1 hp2 m n i j g
  -- the deterministic bound on the weight `-(b_n a^g)`
  have hbdd : ∀ U : Array N, ‖-(bRec p m n j U * aRec p m ^ g)‖ ≤ 2 * (n : ℝ) + 5 := by
    intro U
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    have h1 : |bRec p m n j U| ≤ 2 * (n : ℝ) + 5 := by
      have hb : bRec p m n j U = HprevAt p m n j U + 2 := rfl
      rw [hb]
      have hab := abs_add_le (HprevAt p m n j U) (2 : ℝ)
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      have h3 := abs_HprevAt_le hp1 hp2 m n j U
      linarith
    have h2 : |aRec p m ^ g| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (zero_le_aRec hp1 hp2 m) g)]
      exact pow_le_one₀ (zero_le_aRec hp1 hp2 m) (le_of_lt (aRec_lt_one hp1 hp2 m))
    calc |bRec p m n j U| * |aRec p m ^ g| ≤ (2 * (n : ℝ) + 5) * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 2 * (n : ℝ) + 5 := by ring
  have hbound : Integrable ((abovePosSet p m n i j g).indicator
      (fun U : Array N => -(bRec p m n j U * aRec p m ^ g))) (arrayMeasure N) := by
    have hbmeas : Measurable (fun U : Array N => -(bRec p m n j U * aRec p m ^ g)) := by
      have hb : Measurable (fun U : Array N => HprevAt p m n j U + 2) :=
        (measurable_HprevAt p m n j).add_const 2
      have hfun : (fun U : Array N => -(bRec p m n j U * aRec p m ^ g))
          = fun U => -((HprevAt p m n j U + 2) * aRec p m ^ g) := by
        funext U
        rw [bRec]
      rw [hfun]
      exact (hb.mul_const _).neg
    refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 5))
      (hbmeas.indicator hA).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => ?_)
    by_cases hU : U ∈ abovePosSet p m n i j g
    · rw [Set.indicator_of_mem hU]; exact hbdd U
    · rw [Set.indicator_of_notMem hU]
      simp only [norm_zero]
      positivity
  have hmono := integral_mono_ae hbound integrable_condExp
    (indicator_le_condExp_indicator_HpotInc_abovePosSet p hp1 hp2 m n hij hm hg)
  rw [integral_condExp hle, integral_indicator hA, integral_indicator hA] at hmono
  exact hmono

/-! ### 9. Smoke instantiation at concrete constants

The constants instantiate at `N = 2`, `p = 3/4`, `m = 2`, `n = 0`, `i = 0 ≠ j = 1`, `g = 1`
(so `a = aRec 3/4 2` is genuinely greater than `1/3` and the `m ≥ 2` lower bound applies). -/

/-- The restricted `enlFilt` identity at `p = 3/4`, `m = 2`, `g = 1`. -/
example :
    condExp (enlFilt (N := 2) (3 / 4) 2 0) (arrayMeasure 2)
        ((abovePosSet (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ 1).indicator
          (HpotInc (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩))
      =ᵐ[arrayMeasure 2]
        (abovePosSet (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ 1).indicator
          (fun U => alphaFun (3 / 4) 2 0 ⟨0, by norm_num⟩ U * eRec (3 / 4) 2 0 ⟨1, by norm_num⟩ 1 U
            - (1 - alphaFun (3 / 4) 2 0 ⟨0, by norm_num⟩ U)
                * eRec (3 / 4) 2 0 ⟨1, by norm_num⟩ 0 U) :=
  condExp_indicator_HpotInc_enlFilt_abovePosSet (p := 3 / 4) (by norm_num) (by norm_num)
    2 0 (i := ⟨0, by norm_num⟩) (j := ⟨1, by norm_num⟩) (by decide) (le_refl 1)

/-- The restricted lower bound at the same constants (`m = 2`, `g = 1`). -/
example :
    (fun U : Array 2 => (abovePosSet (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ 1).indicator
        (fun U => -(bRec (3 / 4) 2 0 ⟨1, by norm_num⟩ U * aRec (3 / 4) 2 ^ 1)) U)
      ≤ᵐ[arrayMeasure 2] condExp (enlFilt (N := 2) (3 / 4) 2 0) (arrayMeasure 2)
        ((abovePosSet (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ 1).indicator
          (HpotInc (3 / 4) 2 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)) :=
  indicator_le_condExp_indicator_HpotInc_abovePosSet (p := 3 / 4) (by norm_num) (by norm_num)
    2 0 (i := ⟨0, by norm_num⟩) (j := ⟨1, by norm_num⟩) (by decide) (le_refl 2) (le_refl 1)

/-- **The set-integral form of the restricted above-record identity** (`g ≥ 1`):

  `∫_{A_g} HpotInc = ∫_{A_g} (alpha_n^i e_g - (1 - alpha_n^i) e_{g-1})`,

the integrated counterpart of `condExp_indicator_HpotInc_enlFilt_abovePosSet` (obtained with
`setIntegral_condExp`, so no separate a.e. reasoning is needed). -/
theorem setIntegral_HpotInc_enlFilt_abovePosSet (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) {g : ℕ} (hg : 1 ≤ g) :
    ∫ U in abovePosSet p m n i j g, HpotInc p m n i j U ∂(arrayMeasure N)
      = ∫ U in abovePosSet p m n i j g,
          (alphaFun p m n i U * eRec p m n j g U
            - (1 - alphaFun p m n i U) * eRec p m n j (g - 1) U) ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hA : MeasurableSet (abovePosSet p m n i j g) :=
    infoPiece_le p m n j g _ (measurableSet_abovePosSet p m n i j g g)
  have hAm : MeasurableSet[enlFilt p m n] (abovePosSet p m n i j g) :=
    measurableSet_abovePosSet_enlFilt p m n i j g
  have hInt : Integrable ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))
      (arrayMeasure N) := integrable_indicator_HpotInc_abovePosSet_tower hp0 hp1 m n i j g
  calc ∫ U in abovePosSet p m n i j g, HpotInc p m n i j U ∂(arrayMeasure N)
      = ∫ U in abovePosSet p m n i j g,
          (abovePosSet p m n i j g).indicator (HpotInc p m n i j) U ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA ?_
        filter_upwards with U hU
        rw [Set.indicator_of_mem hU]
    _ = ∫ U in abovePosSet p m n i j g,
          condExp (enlFilt p m n) (arrayMeasure N)
            ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) U
          ∂(arrayMeasure N) := (setIntegral_condExp hle hInt hAm).symm
    _ = ∫ U in abovePosSet p m n i j g,
          (abovePosSet p m n i j g).indicator
            (fun U => alphaFun p m n i U * eRec p m n j g U
              - (1 - alphaFun p m n i U) * eRec p m n j (g - 1) U) U
          ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA ?_
        filter_upwards [condExp_indicator_HpotInc_enlFilt_abovePosSet p hp0 hp1 m n hij hg]
          with U hU _
        exact hU
    _ = ∫ U in abovePosSet p m n i j g,
          (alphaFun p m n i U * eRec p m n j g U
            - (1 - alphaFun p m n i U) * eRec p m n j (g - 1) U) ∂(arrayMeasure N) := by
        refine setIntegral_congr_ae hA ?_
        filter_upwards with U hU
        rw [Set.indicator_of_mem hU]

/-! ### Axiom audit -/


end Swarming.Enl
