/-
  **Raw second moment of the actual compensator increment: a logarithmic bound.**

  This file computes the *diagonal* term of the raw covariance mass of the actual model, with no
  orthogonality and no conditional-independence input.

  Input (already verified, pointwise in the array): `QIncDefectSupport.qInc_sq_le_amp_add_defect`

      qInc_t^2 <= 2 * qAmp_t^2 + 2 * qDefect_t^2 .

  Both right-hand sides are then dominated, **pointwise**, by the mark-space running maximum of
  the environment function `h_j = hof p (siteMarks j)` over the sites `0, …, t+1`:

  * `qAmp_t = h_j(X_t) + h_j(X_t - 1) - (F_{b_t}(g_t+1) - F_{b_t}(g_t-1))` and
    `b_t = h_j(M_t - 1) + 2 <= max h_j + 2`, so `|qAmp_t| <= K (1 + Y_t)^2`;
  * `qAlphaMeanH_t = alpha h_j(X_t) - (1 - alpha) h_j(X_t - 1)` and
    `HpotInc_t = h_j(X_t)`, so `|qAlphaMeanH_t| <= 1 + Y_t` and `|HpotInc_t| <= 1 + Y_t`;
    conditional Jensen bounds the conditional-expectation half of `qDefect_t`.

  `SwarmMarks.maxmom_h` (display (maxmom) of the paper, `s`-th mark moment) gives
  `E[(1+Y_t)^s] <= C_s (log(t+2))^s` under the *actual* array law, because the law of one row of
  site marks is exactly `markMeasure (boolMeasure ((1-p)^(m-1)))`
  (`SwarmLogRatio.measurePreserving_siteMarks`).  Hence

      integral qInc_t^2 <= C (log (t+2))^4      for every t,

  and consequently the dyadic weighted variance series `sum_k (k+1)^2/4^k * sum_{t<2^{k+1}}` of
  the **raw** increment is summable — for every `m >= 2`.  This is the diagonal half of the raw
  covariance mass; off-diagonal decay is not claimed here.
-/
import Swarm.QIncDefectSupport
import Swarm.QProjVarianceHonest
import Swarm.MarkMaxmom

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmActualBudget

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-! ## 1. The mark-space running maximum attached to one row of site marks -/

/-- The running maximum of the environment function over the sites `0, …, t+1`, read off the
actual site marks of walker `j`.  This is `SwarmMarks.Yfun` transported along `siteMarks`. -/
noncomputable def qY (p : ℝ) (m t : ℕ) (j : Fin N) : Array N → ℝ :=
  fun U => SwarmMarks.Yfun p t (SwarmLogRatio.siteMarks p m U j)

lemma one_le_qY {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (m t : ℕ) (j : Fin N)
    (U : Array N) : 1 ≤ qY (N := N) p m t j U :=
  SwarmMarks.one_le_Yfun hp1 hp2 t _

lemma measurable_qY {p : ℝ} (hp0 : p ≠ 0) (m t : ℕ) (j : Fin N) :
    Measurable (qY (N := N) p m t j) :=
  (SwarmMarks.measurable_Yfun p hp0 t).comp (measurable_siteMarks p m j)

/-! ## 2. Pointwise domination by the mark maximum -/

/-- `h_j(-) = hof p (siteMarks j)` is positive at every integer site (both branches are `>= 1`). -/
lemma hZpot_envH_pos {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (m : ℕ) (j : Fin N)
    (U : Array N) (x : ℤ) : 0 < hZpot (envH p m j U) x := by
  by_cases h : x ≤ -1
  · rw [hZpot_of_nonpos h]; norm_num
  · rw [hZpot_of_nonneg (by omega)]
    show (0 : ℝ) < SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x.toNat
    have := SwarmMarks.one_le_hof hp1 hp2 (SwarmLogRatio.siteMarks p m U j) x.toNat
    linarith

/-- **Every environment value up to the horizon is dominated by the mark maximum.** -/
theorem hZpot_envH_le_qY {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (m t : ℕ)
    (j : Fin N) (U : Array N) {x : ℤ} (hx : x ≤ (t : ℤ) + 1) :
    hZpot (envH p m j U) x ≤ 1 + qY (N := N) p m t j U := by
  by_cases h : x ≤ -1
  · rw [hZpot_of_nonpos h]
    have := one_le_qY hp1 hp2 m t j U
    linarith
  · have hx0 : 0 ≤ x := by omega
    rw [hZpot_of_nonneg hx0]
    show SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x.toNat
      ≤ 1 + SwarmMarks.Yfun p t (SwarmLogRatio.siteMarks p m U j)
    have hmem : x.toNat ∈ Finset.range (t + 2) := by
      have h1 : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
      rw [Finset.mem_range]
      omega
    have h := SwarmMarks.hof_le_Yfun p t x.toNat (SwarmLogRatio.siteMarks p m U j) hmem
    have := one_le_qY hp1 hp2 m t j U
    linarith

/-- `b_t = h_j(M_t - 1) + 2` is dominated by the mark maximum plus `2`. -/
theorem bRec_le_qY_add_two {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (m t : ℕ)
    (j : Fin N) (U : Array N) : bRec p m t j U ≤ qY (N := N) p m t j U + 2 := by
  have h : HprevAt p m t j U ≤ qY (N := N) p m t j U := by
    rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m t U)).toNat) with h0 | hpos
    · rw [HprevAt_of_zero p m t j U h0]
      exact one_le_qY hp1 hp2 m t j U
    · obtain ⟨k, hk⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m t U)).toNat ≠ 0)
      rw [HprevAt_of_succ p m t j U k hk]
      have hk2 : k < t + 2 := by
        have := toNat_recVal_prefOf_le p m U j t
        omega
      have := SwarmMarks.hof_le_Yfun p t k (SwarmLogRatio.siteMarks p m U j)
        (Finset.mem_range.mpr hk2)
      simpa only [qY] using this
  simp only [bRec]
  linarith

/-- **The `F_b` value of the up-step is dominated by the mark maximum.** -/
theorem abs_qFup_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m t : ℕ) (j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (i : Fin N) (U : Array N) :
    |qFup p m eps i j U t|
      ≤ (qY (N := N) p m t j U + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hY : 1 ≤ qY (N := N) p m t j U := one_le_qY hp1.le hp2 m t j U
  have hb1 : (0 : ℝ) ≤ bRec p m t j U := by
    have := one_le_HprevAt hp1 hp2 m t j U
    simp only [bRec]; linarith
  have hb2 := bRec_le_qY_add_two hp1.le hp2 m t j U
  have hden : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by
    have h : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  have hsq : (bRec p m t j U) ^ 2 ≤ (qY (N := N) p m t j U + 2) ^ 2 := by
    have h2 : (0 : ℝ) ≤ qY (N := N) p m t j U + 2 := by linarith
    exact pow_le_pow_left₀ hb1 hb2 2
  rw [qFup]
  refine (SwarmOcc.Fcorr_abs_le ha0 ha1 hb1 hε _).trans ?_
  exact div_le_div_of_nonneg_right hsq hden.le

/-- **The `F_b` value of the down-step is dominated by the mark maximum.** -/
theorem abs_qFdown_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m t : ℕ) (j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (i : Fin N) (U : Array N) :
    |qFdown p m eps i j U t|
      ≤ (qY (N := N) p m t j U + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp1 hp2 m
  have hY : 1 ≤ qY (N := N) p m t j U := one_le_qY hp1.le hp2 m t j U
  have hb1 : (0 : ℝ) ≤ bRec p m t j U := by
    have := one_le_HprevAt hp1 hp2 m t j U
    simp only [bRec]; linarith
  have hb2 := bRec_le_qY_add_two hp1.le hp2 m t j U
  have hden : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by
    have h : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  have hsq : (bRec p m t j U) ^ 2 ≤ (qY (N := N) p m t j U + 2) ^ 2 := by
    have h2 : (0 : ℝ) ≤ qY (N := N) p m t j U + 2 := by linarith
    exact pow_le_pow_left₀ hb1 hb2 2
  rw [qFdown]
  refine (SwarmOcc.Fcorr_abs_le ha0 ha1 hb1 hε _).trans ?_
  exact div_le_div_of_nonneg_right hsq hden.le

/-- **The raw amplitude is dominated by the mark maximum**, uniformly in time and in the pair
`(i,j)`: `|qAmp_t| <= K (1 + Y_t)^2` with `K = 2 + 18/(eps (1-a)^2)`. -/
theorem abs_qAmp_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m t : ℕ) (j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (i : Fin N) (U : Array N) :
    |qAmp p m eps i j U t|
      ≤ (2 + 18 / (eps * (1 - aRec p m) ^ 2)) * (1 + qY (N := N) p m t j U) ^ 2 := by
  set Y : ℝ := qY (N := N) p m t j U with hYdef
  have hY1 : 1 ≤ Y := one_le_qY hp1.le hp2 m t j U
  have hxabs : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) :=
    le_trans (le_abs_self _) (ZBudget.abs_pos_le_time p m U i t)
  have hxabs2 : ((trajectory p m U t).pos i : ℤ) - 1 ≤ (t : ℤ) + 1 := by omega
  have hX1 : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) + 1 := by omega
  have hp1' : (1 : ℝ) / 2 ≤ p := hp1.le
  have hz1pos := hZpot_envH_pos hp1' hp2 m j U ((trajectory p m U t).pos i)
  have hz2pos := hZpot_envH_pos hp1' hp2 m j U ((trajectory p m U t).pos i - 1)
  have hz1 : hZpot (envH p m j U) ((trajectory p m U t).pos i) ≤ 1 + Y :=
    hZpot_envH_le_qY hp1' hp2 m t j U hX1
  have hz2 : hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) ≤ 1 + Y :=
    hZpot_envH_le_qY hp1' hp2 m t j U hxabs2
  have h5 : |qFup p m eps i j U t| ≤ (Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    abs_qFup_le hp1 hp2 m t j hε i U
  have h6 : |qFdown p m eps i j U t| ≤ (Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2) :=
    abs_qFdown_le hp1 hp2 m t j hε i U
  have hden : (0 : ℝ) < eps * (1 - aRec p m) ^ 2 := by
    have h : (0 : ℝ) < 1 - aRec p m := by
      have := aRec_lt_one hp1 hp2 m; linarith
    positivity
  have hmain : |qAmp p m eps i j U t|
      ≤ 2 * (1 + Y) + 2 * ((Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by
    have hs1 : |hZpot (envH p m j U) ((trajectory p m U t).pos i)
        + hZpot (envH p m j U) ((trajectory p m U t).pos i - 1)|
        ≤ (1 + Y) + (1 + Y) := by
      rw [abs_of_pos (by linarith)]
      linarith
    have hs2 : |qFup p m eps i j U t - qFdown p m eps i j U t|
        ≤ (Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2)
          + (Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
      refine (abs_sub _ _).trans ?_
      linarith
    have hsplit := abs_sub (hZpot (envH p m j U) ((trajectory p m U t).pos i)
      + hZpot (envH p m j U) ((trajectory p m U t).pos i - 1))
      (qFup p m eps i j U t - qFdown p m eps i j U t)
    calc |qAmp p m eps i j U t|
        = |hZpot (envH p m j U) ((trajectory p m U t).pos i)
            + hZpot (envH p m j U) ((trajectory p m U t).pos i - 1)
            - (qFup p m eps i j U t - qFdown p m eps i j U t)| := by
          rw [qAmp_eq_hZpot]
      _ ≤ _ := hsplit
      _ ≤ 2 * (1 + Y) + 2 * ((Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by linarith
  have hY2 : (Y + 2) ^ 2 ≤ 9 * (1 + Y) ^ 2 := by
    have h1' : Y + 2 ≤ 3 * (1 + Y) := by linarith
    have h0 : (0 : ℝ) ≤ Y + 2 := by linarith
    calc (Y + 2) ^ 2 ≤ (3 * (1 + Y)) ^ 2 := pow_le_pow_left₀ h0 h1' 2
      _ = 9 * (1 + Y) ^ 2 := by ring
  have hpos : (0 : ℝ) ≤ 1 + Y := by linarith
  have hle1 : (1 + Y) ≤ (1 + Y) ^ 2 := by nlinarith
  have key : 2 * ((Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2))
      ≤ 18 / (eps * (1 - aRec p m) ^ 2) * (1 + Y) ^ 2 := by
    rw [div_mul_eq_mul_div, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  calc |qAmp p m eps i j U t|
      ≤ 2 * (1 + Y) + 2 * ((Y + 2) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := hmain
    _ ≤ 2 * (1 + Y) ^ 2 + 18 / (eps * (1 - aRec p m) ^ 2) * (1 + Y) ^ 2 := by
        have h2 : 2 * (1 + Y) ≤ 2 * (1 + Y) ^ 2 := by linarith
        linarith
    _ = (2 + 18 / (eps * (1 - aRec p m) ^ 2)) * (1 + Y) ^ 2 := by ring

/-- The centred alpha-mean of the environment potential is dominated by the mark maximum. -/
theorem abs_qAlphaMeanH_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m t : ℕ)
    (j : Fin N) (i : Fin N) (U : Array N) :
    |qAlphaMeanH p m i j U t| ≤ 1 + qY (N := N) p m t j U := by
  set Y : ℝ := qY (N := N) p m t j U with hYdef
  have hY1 : 1 ≤ Y := one_le_qY hp1.le hp2 m t j U
  have hp1' : (1 : ℝ) / 2 ≤ p := hp1.le
  have hxabs : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) :=
    le_trans (le_abs_self _) (ZBudget.abs_pos_le_time p m U i t)
  have hX2 : ((trajectory p m U t).pos i : ℤ) - 1 ≤ (t : ℤ) + 1 := by omega
  have hX1 : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) + 1 := by omega
  have h1 : hZpot (envH p m j U) ((trajectory p m U t).pos i) ≤ 1 + Y :=
    hZpot_envH_le_qY hp1' hp2 m t j U hX1
  have h2 : hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) ≤ 1 + Y :=
    hZpot_envH_le_qY hp1' hp2 m t j U hX2
  have hz1 : (0:ℝ) ≤ hZpot (envH p m j U) ((trajectory p m U t).pos i) :=
    (hZpot_envH_pos hp1' hp2 m j U _).le
  have hz2 : (0:ℝ) ≤ hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) :=
    (hZpot_envH_pos hp1' hp2 m j U _).le
  have hα := alphaFun_mem_Icc hp1 hp2 m t i U
  have hA : |alphaFun p m t i U * hZpot (envH p m j U) ((trajectory p m U t).pos i)|
      ≤ alphaFun p m t i U * (1 + Y) := by
    rw [abs_mul, abs_of_nonneg hα.1, abs_of_nonneg hz1]
    exact mul_le_mul_of_nonneg_left h1 hα.1
  have hB : |(1 - alphaFun p m t i U) * hZpot (envH p m j U) ((trajectory p m U t).pos i - 1)|
      ≤ (1 - alphaFun p m t i U) * (1 + Y) := by
    have h1α : (0:ℝ) ≤ 1 - alphaFun p m t i U := by linarith [hα.2]
    rw [abs_mul, abs_of_nonneg h1α, abs_of_nonneg hz2]
    exact mul_le_mul_of_nonneg_left h2 h1α
  rw [qAlphaMeanH_eq_hZpot]
  have := (abs_sub (alphaFun p m t i U * hZpot (envH p m j U) ((trajectory p m U t).pos i))
    ((1 - alphaFun p m t i U) * hZpot (envH p m j U) ((trajectory p m U t).pos i - 1))).trans
    (add_le_add hA hB)
  have e2 : alphaFun p m t i U * (1 + Y) + (1 - alphaFun p m t i U) * (1 + Y) = 1 + Y := by
    ring
  linarith [this, e2]

/-- The potential increment is one environment value at the current site, hence dominated by the
mark maximum. -/
theorem abs_HpotInc_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m t : ℕ)
    (j : Fin N) (i : Fin N) (U : Array N) :
    |HpotInc p m t i j U| ≤ 1 + qY (N := N) p m t j U := by
  have hp1' : (1 : ℝ) / 2 ≤ p := hp1.le
  have hxabs : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) :=
    le_trans (le_abs_self _) (ZBudget.abs_pos_le_time p m U i t)
  have hX1 : ((trajectory p m U t).pos i : ℤ) ≤ (t : ℤ) + 1 := by omega
  have hX2 : ((trajectory p m U t).pos i : ℤ) - 1 ≤ (t : ℤ) + 1 := by omega
  have hcases := StepCross.pos_succ_eq_or p m U t i
  by_cases hup : U ∈ StepCross.stepUp p m t i
  · have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i + 1 := hup
    have hsub : SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i + 1)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)
        = hZpot (envH p m j U) ((trajectory p m U t).pos i) := Hpot_succ_sub' _
    rw [HpotInc_def, hpos, hsub, abs_of_pos (hZpot_envH_pos hp1' hp2 m j U _)]
    exact hZpot_envH_le_qY hp1' hp2 m t j U hX1
  · have hdown : U ∈ StepCross.stepDown p m t i := hcases.resolve_left hup
    have hpos : (trajectory p m U (t + 1)).pos i = (trajectory p m U t).pos i - 1 := hdown
    have hsub : SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i - 1)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U t).pos i)
        = -hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) :=
      Hpot_pred_sub _
    rw [HpotInc_def, hpos, hsub, abs_neg, abs_of_pos (hZpot_envH_pos hp1' hp2 m j U _)]
    exact hZpot_envH_le_qY hp1' hp2 m t j U hX2

/-! ## 3. Measurability of the amplitude, the centred mean and the defect -/

lemma measurable_hZpot_envH_traj (p : ℝ) (m t : ℕ) (j : Fin N) (i : Fin N) :
    Measurable fun U : Array N => hZpot (envH p m j U) ((trajectory p m U t).pos i) :=
  measurable_hZpot_traj p m t j i

lemma measurable_hZpot_envH_traj_pred (p : ℝ) (m t : ℕ) (j : Fin N) (i : Fin N) :
    Measurable fun U : Array N => hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) :=
  measurable_hZpot_traj_pred p m t j i

lemma measurable_qAlphaMeanH_t (p : ℝ) (m t : ℕ) (i j : Fin N) :
    Measurable fun U : Array N => qAlphaMeanH p m i j U t := by
  have heq : (fun U : Array N => qAlphaMeanH p m i j U t) = fun U =>
      alphaFun p m t i U * hZpot (envH p m j U) ((trajectory p m U t).pos i)
        - (1 - alphaFun p m t i U)
            * hZpot (envH p m j U) ((trajectory p m U t).pos i - 1) := by
    funext U
    exact qAlphaMeanH_eq_hZpot p m i j U t
  have hα : Measurable fun U : Array N => alphaFun p m t i U :=
    (measurable_alphaFun p m t i).mono (pathMeas_le p m t) le_rfl
  rw [heq]
  exact (hα.mul (measurable_hZpot_envH_traj p m t j i)).sub
    ((measurable_const.sub hα).mul (measurable_hZpot_envH_traj_pred p m t j i))

/-! ## 4. Transporting the mark maximum to the actual array law -/

/-- **The mark maximum has the paper's `s`-th moment under the actual array law.** -/
theorem lintegral_qY_pow_le {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (s : ℕ) (hs : 1 ≤ s) (j : Fin N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      ∫⁻ U, ENNReal.ofReal ((1 + qY (N := N) p m t j U) ^ s) ∂(arrayMeasure N)
        ≤ ENNReal.ofReal (C * (Real.log ((t : ℝ) + 2)) ^ s) := by
  obtain ⟨C, hCpos, hC⟩ := SwarmMarks.maxmom_h hp1 hp2 hm s hs
  refine ⟨C, hCpos, fun t => ?_⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hYmeas : Measurable (fun ω : ℕ → Bool => (1 + SwarmMarks.Yfun p t ω)) :=
    measurable_const.add (SwarmMarks.measurable_Yfun p hpne t)
  have hf : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal ((1 + SwarmMarks.Yfun p t ω) ^ s)) :=
    ENNReal.measurable_ofReal.comp ((continuous_pow s).measurable.comp hYmeas)
  have hmap := SwarmLogRatio.measurePreserving_siteMarks (N := N) (p := p) hp0 hp2 m j
  calc ∫⁻ U, ENNReal.ofReal ((1 + qY (N := N) p m t j U) ^ s) ∂(arrayMeasure N)
      = ∫⁻ U, (fun ω : ℕ → Bool => ENNReal.ofReal ((1 + SwarmMarks.Yfun p t ω) ^ s))
          (SwarmLogRatio.siteMarks p m U j) ∂(arrayMeasure N) := rfl
    _ = ∫⁻ ω, ENNReal.ofReal ((1 + SwarmMarks.Yfun p t ω) ^ s)
          ∂(Measure.map (fun U : Array N => SwarmLogRatio.siteMarks p m U j)
            (arrayMeasure N)) := (lintegral_map hf hmap.measurable).symm
    _ = ∫⁻ ω, ENNReal.ofReal ((1 + SwarmMarks.Yfun p t ω) ^ s)
          ∂(SwarmMarks.markMeasure (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))) := by
        rw [hmap.map_eq]
    _ ≤ ENNReal.ofReal (C * (Real.log ((t : ℝ) + 2)) ^ s) := hC t

/-- The mark maximum's `s`-th moment as an honest Bochner integral, with integrability. -/
theorem integrable_and_integral_qY_pow {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (s : ℕ) (hs : 1 ≤ s) (j : Fin N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U => (1 + qY (N := N) p m t j U) ^ s) (arrayMeasure N) ∧
        ∫ U, (1 + qY (N := N) p m t j U) ^ s ∂(arrayMeasure N)
          ≤ C * (Real.log ((t : ℝ) + 2)) ^ s := by
  obtain ⟨C, hCpos, hC⟩ := lintegral_qY_pow_le (N := N) hp0 hp1 hp2 hm s hs j
  refine ⟨C, hCpos, fun t => ?_⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hcont : Measurable (fun U : Array N => (1 + qY (N := N) p m t j U) ^ s) :=
    (continuous_pow s).measurable.comp (measurable_const.add (measurable_qY hpne m t j))
  have hbase : ∀ U : Array N, (0 : ℝ) ≤ 1 + qY (N := N) p m t j U := fun U => by
    have := one_le_qY hp1.le hp2 m t j U; linarith
  have hnn : 0 ≤ᵐ[arrayMeasure N] fun U : Array N => (1 + qY (N := N) p m t j U) ^ s :=
    Filter.Eventually.of_forall fun U => pow_nonneg (hbase U) s
  have hbound := hC t
  have hfin : HasFiniteIntegral (fun U : Array N => (1 + qY (N := N) p m t j U) ^ s)
      (arrayMeasure N) :=
    (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have hint : Integrable (fun U : Array N => (1 + qY (N := N) p m t j U) ^ s)
      (arrayMeasure N) := ⟨hcont.aestronglyMeasurable, hfin⟩
  refine ⟨hint, ?_⟩
  have hEq := ofReal_integral_eq_lintegral_ofReal hint hnn
  have hle : ENNReal.ofReal (∫ U, (1 + qY (N := N) p m t j U) ^ s ∂(arrayMeasure N))
      ≤ ENNReal.ofReal (C * (Real.log ((t : ℝ) + 2)) ^ s) := by
    rw [hEq]; exact hbound
  have hlog : 0 ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hCnn : 0 ≤ C * (Real.log ((t : ℝ) + 2)) ^ s :=
    mul_nonneg hCpos.le (pow_nonneg hlog s)
  exact (ENNReal.ofReal_le_ofReal_iff hCnn).mp hle

/-- The same bound for the `L^2` moment of the mark maximum. -/
theorem integrable_and_integral_qY_sq {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (j : Fin N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U => (1 + qY (N := N) p m t j U) ^ 2) (arrayMeasure N) ∧
        ∫ U, (1 + qY (N := N) p m t j U) ^ 2 ∂(arrayMeasure N)
          ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4 := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  refine ⟨C4, hC4pos, fun t => ?_⟩
  obtain ⟨hint4, hb4⟩ := hC4 t
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hcont2 : Measurable (fun U : Array N => (1 + qY (N := N) p m t j U) ^ 2) :=
    (continuous_pow 2).measurable.comp (measurable_const.add (measurable_qY hpne m t j))
  have hY1 : ∀ U : Array N, (1 : ℝ) ≤ 1 + qY (N := N) p m t j U :=
    fun U => by have := one_le_qY hp1.le hp2 m t j U; linarith
  have hpoint : ∀ U : Array N, (1 + qY (N := N) p m t j U) ^ 2
      ≤ (1 + qY (N := N) p m t j U) ^ 4 := by
    intro U
    set a : ℝ := 1 + qY (N := N) p m t j U with ha
    have h1 : (1:ℝ) ≤ a := hY1 U
    have h0 : (0:ℝ) ≤ a := by linarith
    have h2 : (1:ℝ) ≤ a ^ 2 := by nlinarith
    have h3 : a ^ 2 ≤ a ^ 2 * a ^ 2 := by
      calc a ^ 2 = a ^ 2 * 1 := by ring
        _ ≤ a ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
    calc a ^ 2 ≤ a ^ 2 * a ^ 2 := h3
      _ = a ^ 4 := by ring
  have hint2 : Integrable (fun U : Array N => (1 + qY (N := N) p m t j U) ^ 2)
      (arrayMeasure N) := by
    refine Integrable.mono' hint4 hcont2.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint U
  refine ⟨hint2, ?_⟩
  refine (integral_mono hint2 hint4 hpoint).trans hb4

/-! ## 5. Ambient measurability of the amplitude -/

lemma measurable_qFup_ambient {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (j : Fin N)
    (eps : ℝ) (i : Fin N) : Measurable fun U : Array N => qFup p m eps i j U t := by
  have hrm : Measurable fun U : Array N => runMax p m U j t :=
    measurable_to_countable'
      (fun y => (enlFilt p m).le t _ (measurableSet_runMax_eq p m t j y))
  have hgap : Measurable fun U : Array N =>
      (trajectory p m U t).pos i + 1 - runMax p m U j t :=
    (((Swarming.Fair.measurable_trajectory (N := N) p m t).1 i).add_const 1).sub hrm
  exact measurable_Fcorr_gap_ambient hp1 m t j (aRec p m) eps hgap

lemma measurable_qFdown_ambient {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (j : Fin N)
    (eps : ℝ) (i : Fin N) : Measurable fun U : Array N => qFdown p m eps i j U t := by
  have hrm : Measurable fun U : Array N => runMax p m U j t :=
    measurable_to_countable'
      (fun y => (enlFilt p m).le t _ (measurableSet_runMax_eq p m t j y))
  have hgap : Measurable fun U : Array N =>
      (trajectory p m U t).pos i - 1 - runMax p m U j t :=
    (((Swarming.Fair.measurable_trajectory (N := N) p m t).1 i).sub_const 1).sub hrm
  exact measurable_Fcorr_gap_ambient hp1 m t j (aRec p m) eps hgap

lemma measurable_qAmp_ambient {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (m t : ℕ) (j : Fin N)
    (eps : ℝ) (i : Fin N) : Measurable fun U : Array N => qAmp p m eps i j U t := by
  have h1 := measurable_hZpot_envH_traj (N := N) p m t j i
  have h2 := measurable_hZpot_envH_traj_pred (N := N) p m t j i
  have h5 := measurable_qFup_ambient (N := N) hp1 m t j eps i
  have h6 := measurable_qFdown_ambient (N := N) hp1 m t j eps i
  have heq : (fun U : Array N => qAmp p m eps i j U t) = fun U =>
      hZpot (envH p m j U) ((trajectory p m U t).pos i)
        + hZpot (envH p m j U) ((trajectory p m U t).pos i - 1)
        - (qFup p m eps i j U t - qFdown p m eps i j U t) := by
    funext U
    exact qAmp_eq_hZpot p m eps i j U t
  rw [heq]
  exact (h1.add h2).sub (h5.sub h6)

/-! ## 6. The second moments of the amplitude, the defect and the raw increment -/

/-- The raw amplitude is square integrable, with the mark-maximum bound. -/
theorem integrable_and_integral_sq_qAmp {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) (t : ℕ) (i j : Fin N) :
    Integrable (fun U => qAmp p m eps i j U t ^ 2) (arrayMeasure N) ∧
      ∫ U, qAmp p m eps i j U t ^ 2 ∂(arrayMeasure N)
        ≤ (2 + 18 / (eps * (1 - aRec p m) ^ 2)) ^ 2
            * (∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N)) := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  obtain ⟨hint4, hb4⟩ := hC4 t
  set K : ℝ := 2 + 18 / (eps * (1 - aRec p m) ^ 2) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have h : (0 : ℝ) < 1 - aRec p m := by
      have := aRec_lt_one hp1 hp2 m; linarith
    have : (0 : ℝ) ≤ 18 / (eps * (1 - aRec p m) ^ 2) := by positivity
    rw [hKdef]; linarith
  have habs := abs_qAmp_le (N := N) hp1 hp2 m t j hε i
  have hpoint : ∀ U : Array N, qAmp p m eps i j U t ^ 2
      ≤ K ^ 2 * (1 + qY (N := N) p m t j U) ^ 4 := by
    intro U
    have h1 : qAmp p m eps i j U t ^ 2
        = |qAmp p m eps i j U t| ^ 2 := (sq_abs _).symm
    rw [h1]
    calc |qAmp p m eps i j U t| ^ 2
        ≤ (K * (1 + qY (N := N) p m t j U) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (habs U) 2
      _ = K ^ 2 * (1 + qY (N := N) p m t j U) ^ 4 := by ring
  have hcont : Measurable fun U : Array N => qAmp p m eps i j U t ^ 2 :=
    (continuous_pow 2).measurable.comp (measurable_qAmp_ambient hp1.le m t j eps i)
  have hmaj : Integrable (fun U : Array N => K ^ 2 * (1 + qY (N := N) p m t j U) ^ 4)
      (arrayMeasure N) := hint4.const_mul _
  have hint : Integrable (fun U => qAmp p m eps i j U t ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hcont.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint U
  refine ⟨hint, ?_⟩
  refine (integral_mono hint hmaj hpoint).trans_eq ?_
  rw [integral_const_mul]

/-- The centred alpha-mean is square integrable, with the mark-maximum bound. -/
theorem integrable_and_integral_sq_qAlphaMeanH {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) (t : ℕ) (i j : Fin N) :
    Integrable (fun U => qAlphaMeanH p m i j U t ^ 2) (arrayMeasure N) ∧
      ∫ U, qAlphaMeanH p m i j U t ^ 2 ∂(arrayMeasure N)
        ≤ ∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N) := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  obtain ⟨hint4, hb4⟩ := hC4 t
  have hcont : Measurable fun U : Array N => qAlphaMeanH p m i j U t ^ 2 :=
    (continuous_pow 2).measurable.comp (measurable_qAlphaMeanH_t p m t i j)
  have hY1 : ∀ U : Array N, (1 : ℝ) ≤ 1 + qY (N := N) p m t j U := fun U => by
    have := one_le_qY hp1.le hp2 m t j U; linarith
  have hpoint : ∀ U : Array N, qAlphaMeanH p m i j U t ^ 2
      ≤ (1 + qY (N := N) p m t j U) ^ 4 := by
    intro U
    set a : ℝ := 1 + qY (N := N) p m t j U with ha
    have h1 : (1:ℝ) ≤ a := hY1 U
    have h0 : (0:ℝ) ≤ a := by linarith
    have habs := abs_qAlphaMeanH_le (N := N) hp1 hp2 m t j i U
    have h2 : qAlphaMeanH p m i j U t ^ 2 = |qAlphaMeanH p m i j U t| ^ 2 :=
      (sq_abs _).symm
    rw [h2]
    refine (pow_le_pow_left₀ (abs_nonneg _) habs 2).trans ?_
    have h3 : (1:ℝ) ≤ a ^ 2 := by nlinarith
    calc a ^ 2 = a ^ 2 * 1 := by ring
      _ ≤ a ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
      _ = a ^ 4 := by ring
  have hint : Integrable (fun U => qAlphaMeanH p m i j U t ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hint4 hcont.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint U
  exact ⟨hint, integral_mono hint hint4 hpoint⟩

/-- The exact terminal-defect increment of the raw ledger is square integrable, with an explicit
logarithmic bound: `integral qDefect_t^2 <= 4 * integral (1+Y_t)^4`. -/
theorem integrable_and_integral_sq_qDefect {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) (t : ℕ) (i j : Fin N) :
    Integrable (fun U => qDefect p m eps i j U t ^ 2) (arrayMeasure N) ∧
      ∫ U, qDefect p m eps i j U t ^ 2 ∂(arrayMeasure N)
        ≤ 4 * ∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N) := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  obtain ⟨hint4, hb4⟩ := hC4 t
  obtain ⟨hintA, hAle⟩ :=
    integrable_and_integral_sq_qAlphaMeanH (N := N) hp0 hp1 hp2 hm t i j
  -- the potential increment
  have hHmeas : Measurable fun U : Array N => HpotInc p m t i j U := measurable_HpotInc p m t i j
  have hH2cont : Measurable fun U : Array N => HpotInc p m t i j U ^ 2 :=
    (continuous_pow 2).measurable.comp hHmeas
  have hY1 : ∀ U : Array N, (1 : ℝ) ≤ 1 + qY (N := N) p m t j U := fun U => by
    have := one_le_qY hp1.le hp2 m t j U; linarith
  have hY2cont : Measurable fun U : Array N => (1 + qY (N := N) p m t j U) ^ 2 :=
    (continuous_pow 2).measurable.comp (measurable_const.add (measurable_qY (ne_of_gt hp0) m t j))
  obtain ⟨C2, hC2pos, hC2⟩ := integrable_and_integral_qY_sq (N := N) hp0 hp1 hp2 hm j
  obtain ⟨hintY2, hb2⟩ := hC2 t
  have hHpt : ∀ U : Array N, HpotInc p m t i j U ^ 2
      ≤ (1 + qY (N := N) p m t j U) ^ 2 := by
    intro U
    have h := abs_HpotInc_le (N := N) hp1 hp2 m t j i U
    have h2 : HpotInc p m t i j U ^ 2 = |HpotInc p m t i j U| ^ 2 := (sq_abs _).symm
    rw [h2]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hintH2 : Integrable (fun U => HpotInc p m t i j U ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hintY2 hH2cont.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hHpt U
  have hHle : ∫ U, HpotInc p m t i j U ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (1 + qY (N := N) p m t j U) ^ 2 ∂(arrayMeasure N) :=
    integral_mono hintH2 hintY2 hHpt
  -- the conditional-expectation half
  have hcond_le := ProjHonest.integral_sq_condExp_le_enl (N := N) (p := p) m t
    hHmeas.aestronglyMeasurable hintH2
  have hcond_int := ProjHonest.integrable_sq_condExp_enl (N := N) (p := p) m t
    hHmeas.aestronglyMeasurable hintH2
  -- pointwise split of the defect
  have hdefpt : ∀ U : Array N, qDefect p m eps i j U t ^ 2
      ≤ 2 * qAlphaMeanH p m i j U t ^ 2
        + 2 * (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) ^ 2 := by
    intro U
    have h : qDefect p m eps i j U t
        = qAlphaMeanH p m i j U t
          - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U := rfl
    rw [h]
    nlinarith [sq_nonneg (qAlphaMeanH p m i j U t
      - condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U),
      sq_nonneg (qAlphaMeanH p m i j U t
      + condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U)]
  have hCmeas : StronglyMeasurable
      (fun U : Array N => condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) :=
    (stronglyMeasurable_condExp (f := HpotInc p m t i j) (m := enlFilt p m t)
      (μ := arrayMeasure N)).mono ((enlFilt p m).le t)
  have hdefcont : AEStronglyMeasurable (fun U : Array N => qDefect p m eps i j U t ^ 2)
      (arrayMeasure N) :=
    ((continuous_pow 2).measurable.comp
      (measurable_qAlphaMeanH_t p m t i j |>.sub hCmeas.measurable)).aestronglyMeasurable
  have hmaj : Integrable (fun U : Array N => 2 * qAlphaMeanH p m i j U t ^ 2
      + 2 * (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) ^ 2)
      (arrayMeasure N) :=
    (hintA.const_mul 2).add (hcond_int.const_mul 2)
  have hintD : Integrable (fun U => qDefect p m eps i j U t ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hdefcont ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdefpt U
  refine ⟨hintD, ?_⟩
  have h1 : ∫ U, qDefect p m eps i j U t ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (2 * qAlphaMeanH p m i j U t ^ 2
        + 2 * (condExp (enlFilt p m t) (arrayMeasure N) (HpotInc p m t i j) U) ^ 2)
        ∂(arrayMeasure N) := integral_mono hintD hmaj hdefpt
  rw [integral_add (hintA.const_mul 2) (hcond_int.const_mul 2), integral_const_mul,
    integral_const_mul] at h1
  have h2 : ∫ U, (1 + qY (N := N) p m t j U) ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N) := by
    have hpt : ∀ U : Array N, (1 + qY (N := N) p m t j U) ^ 2
        ≤ (1 + qY (N := N) p m t j U) ^ 4 := by
      intro U
      set a : ℝ := 1 + qY (N := N) p m t j U with ha
      have h1 : (1:ℝ) ≤ a := hY1 U
      have h0 : (0:ℝ) ≤ a := by linarith
      have h3 : (1:ℝ) ≤ a ^ 2 := by nlinarith
      calc a ^ 2 = a ^ 2 * 1 := by ring
        _ ≤ a ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
        _ = a ^ 4 := by ring
    exact integral_mono hintY2 hint4 hpt
  linarith [h1, hAle, hcond_le.trans hHle, h2]

/-! ## 7. The second moment of the raw increment: `C (log (t+2))^4` -/

/-- **Uniform logarithmic bound on the raw second moment.**  For every `m >= 2`, `p in (1/2,1)`,
`eps > 0` and every ordered pair `(i,j)` there is `C = C(m,p,eps) < infinity` with
`integral qInc_t^2 <= C (log (t+2))^4` for all `t`.  No orthogonality, no conditional law of the
coin and no adaptedness of `qInc` enters. -/
theorem exists_integral_sq_qInc_le {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) (i j : Fin N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U => qInc p m eps i j t U ^ 2) (arrayMeasure N) ∧
        ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
          ≤ C * (Real.log ((t : ℝ) + 2)) ^ 4 := by
  obtain ⟨C4, hC4pos, hC4⟩ :=
    integrable_and_integral_qY_pow (N := N) hp0 hp1 hp2 hm 4 (by norm_num) j
  set K : ℝ := 2 + 18 / (eps * (1 - aRec p m) ^ 2) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have h : (0 : ℝ) < 1 - aRec p m := by
      have := aRec_lt_one hp1 hp2 m; linarith
    have : (0 : ℝ) ≤ 18 / (eps * (1 - aRec p m) ^ 2) := by positivity
    rw [hKdef]; linarith
  refine ⟨(2 * K ^ 2 + 8) * C4, by positivity, fun t => ?_⟩
  obtain ⟨hint4, hb4⟩ := hC4 t
  obtain ⟨hintAp, hAle⟩ := integrable_and_integral_sq_qAmp (N := N) hp0 hp1 hp2 hm hε t i j
  obtain ⟨hintD, hDle⟩ := integrable_and_integral_sq_qDefect (N := N) hp0 hp1 hp2 hm hε t i j
  have hpoint : ∀ U : Array N, qInc p m eps i j t U ^ 2
      ≤ 2 * qAmp p m eps i j U t ^ 2 + 2 * qDefect p m eps i j U t ^ 2 :=
    fun U => qInc_sq_le_amp_add_defect hp1 hp2 m eps i j U t
  have hcont : AEStronglyMeasurable (fun U : Array N => qInc p m eps i j t U ^ 2)
      (arrayMeasure N) :=
    (continuous_pow 2).comp_aestronglyMeasurable
      (integrable_qInc (N := N) hp1 hp2 hε (i := i) (j := j) t).aestronglyMeasurable
  have hmaj : Integrable (fun U : Array N => 2 * qAmp p m eps i j U t ^ 2
      + 2 * qDefect p m eps i j U t ^ 2) (arrayMeasure N) :=
    (hintAp.const_mul 2).add (hintD.const_mul 2)
  have hint : Integrable (fun U => qInc p m eps i j t U ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hcont ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpoint U
  refine ⟨hint, ?_⟩
  have h1 : ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (2 * qAmp p m eps i j U t ^ 2 + 2 * qDefect p m eps i j U t ^ 2)
          ∂(arrayMeasure N) := integral_mono hint hmaj hpoint
  rw [integral_add (hintAp.const_mul 2) (hintD.const_mul 2), integral_const_mul,
    integral_const_mul] at h1
  have hK2 : K ^ 2 * ∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N)
      ≤ K ^ 2 * (C4 * (Real.log ((t : ℝ) + 2)) ^ 4) :=
    mul_le_mul_of_nonneg_left hb4 (sq_nonneg K)
  have h4 : ∫ U, (1 + qY (N := N) p m t j U) ^ 4 ∂(arrayMeasure N) ≤
      C4 * (Real.log ((t : ℝ) + 2)) ^ 4 := hb4
  nlinarith [h1, hAle, hDle, hK2, hK0]

/-! ## 8. The dyadic weighted variance series is summable -/

/-- `2^(k+1)/4^k = 2*(1/2)^k` — the exact geometric ratio of the dyadic weights. -/
lemma geomDiv (k : ℕ) : (2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k = 2 * (1 / 2 : ℝ) ^ k := by
  have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hk : (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [h4, hk]
  have e : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := pow_succ 2 k
  rw [e]
  field_simp

lemma dyaW_mul_pow (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1)
      = 2 * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k) := by
  calc ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1)
      = ((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
    _ = ((k : ℝ) + 1) ^ 2 * (2 * (1 / 2 : ℝ) ^ k) := by rw [geomDiv k]
    _ = 2 * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k) := by ring

/-- `sum_k (k+1)^2 (k+2)^4 (1/2)^k < infinity`. -/
theorem summable_poly_half :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ k) := by
  have hP : ∀ k : ℕ, ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ k
      = (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)
        + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k) + 88 * ((k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k)
        + 104 * ((k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) + 64 * ((k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k)
        + 16 * ((k : ℝ) ^ 0 * (1 / 2 : ℝ) ^ k) := by
    intro k
    have h : ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4
        = (k : ℝ) ^ 6 + 10 * (k : ℝ) ^ 5 + 41 * (k : ℝ) ^ 4 + 88 * (k : ℝ) ^ 3
          + 104 * (k : ℝ) ^ 2 + 64 * (k : ℝ) + 16 := by ring
    rw [h]; ring
  have hs : ∀ j : ℕ, Summable (fun k : ℕ => (k : ℝ) ^ j * (1 / 2 : ℝ) ^ k) :=
    fun j => summable_pow_mul_geometric_of_norm_lt_one j (by norm_num)
  have hsum : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
      + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k) + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)
      + 88 * ((k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k) + 104 * ((k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k)
      + 64 * ((k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k) + 16 * ((k : ℝ) ^ 0 * (1 / 2 : ℝ) ^ k)) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
        + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)) := (hs 6).add ((hs 5).mul_left 10)
    have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
        + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)
        + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)) := h1.add ((hs 4).mul_left 41)
    have h3 : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
        + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)
        + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)
        + 88 * ((k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k)) := h2.add ((hs 3).mul_left 88)
    have h4 : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
        + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)
        + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)
        + 88 * ((k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k)
        + 104 * ((k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k)) := h3.add ((hs 2).mul_left 104)
    have h5 : Summable (fun k : ℕ => (k : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
        + 10 * ((k : ℝ) ^ 5 * (1 / 2 : ℝ) ^ k)
        + 41 * ((k : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)
        + 88 * ((k : ℝ) ^ 3 * (1 / 2 : ℝ) ^ k)
        + 104 * ((k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k)
        + 64 * ((k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k)) := h4.add ((hs 1).mul_left 64)
    exact h5.add ((hs 0).mul_left 16)
  exact Summable.congr hsum (fun k => (hP k).symm)

/-- **The raw diagonal mass is summable under the dyadic weights.**  For every `m >= 2` the
weighted dyadic series of the raw second moments converges:
`sum_k (k+1)^2/4^k * sum_{t < 2^(k+1)} integral qInc_t^2 < infinity`. -/
theorem summable_dyaW_qInc {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {eps : ℝ} (hε : 0 < eps) (i j : Fin N) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_integral_sq_qInc_le (N := N) hp0 hp1 hp2 hm hε i j
  set L : ℝ := Real.log 2 with hLdef
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  have hmaj : Summable (fun k : ℕ =>
      2 * C * L ^ 4 * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ k)) :=
    summable_poly_half.mul_left _
  have hstep : ∀ k : ℕ, ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      (∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
      ≤ 2 * C * L ^ 4 * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hterm : ∀ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N) ≤ C * (((k : ℝ) + 2) * L) ^ 4 := by
      intro t ht
      have htlt : t < 2 ^ (k + 1) := Finset.mem_range.mp ht
      have htR : (t : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast htlt
      have h2k : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hle : (t : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 2) := by
        have e : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by rw [pow_succ]
        nlinarith
      have hlog0 : 0 ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hlog : Real.log ((t : ℝ) + 2) ≤ ((k : ℝ) + 2) * L := by
        have h1 : Real.log ((t : ℝ) + 2) ≤ Real.log ((2 : ℝ) ^ (k + 2)) :=
          Real.log_le_log (by linarith) hle
        rw [Real.log_pow] at h1
        rw [hLdef]
        have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
        rw [hcast] at h1
        exact h1
      have hp4 : (Real.log ((t : ℝ) + 2)) ^ 4 ≤ (((k : ℝ) + 2) * L) ^ 4 :=
        pow_le_pow_left₀ hlog0 hlog 4
      exact ((hC t).2).trans (mul_le_mul_of_nonneg_left hp4 hCpos.le)
    have hsum : (∑ t ∈ Finset.range (2 ^ (k + 1)),
          ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
        ≤ (2 : ℝ) ^ (k + 1) * (C * (((k : ℝ) + 2) * L) ^ 4) := by
      calc ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
          ≤ ∑ t ∈ Finset.range (2 ^ (k + 1)), C * (((k : ℝ) + 2) * L) ^ 4 :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ (k + 1) * (C * (((k : ℝ) + 2) * L) ^ 4) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hcoef : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k := by positivity
    calc ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
        (∑ t ∈ Finset.range (2 ^ (k + 1)),
          ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
        ≤ ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
            ((2 : ℝ) ^ (k + 1) * (C * (((k : ℝ) + 2) * L) ^ 4)) :=
          mul_le_mul_of_nonneg_left hsum hcoef
      _ = 2 * C * L ^ 4 * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ k) := by
          rw [← mul_assoc, dyaW_mul_pow k]; ring
  refine Summable.of_nonneg_of_le (fun k => ?_) hstep hmaj
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun t _ => integral_nonneg (fun U => sq_nonneg _)))

/-! ## 9. Consequence: the raw orthogonality route needs *only* orthogonality -/

/-- **The `hQ` one-sided budget from raw pairwise orthogonality alone.**  The `1/64`-budget for
the raw actual compensator follows from `qInc` being pairwise orthogonal: the second-moment
criterion of `QOrthogonalActual.qResidual_of_orthogonal` is now discharged unconditionally for
every `m >= 2`. -/
theorem qresidual_of_raw_orthogonal_only {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N}
    (horth : ∀ s t : ℕ, s ≠ t →
      ∫ U, qInc p m (1 / 64) i j s U * qInc p m (1 / 64) i j t U ∂(arrayMeasure N) = 0) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤
        Qcomp p m (1 / 64) (fun s => alphaFun p m s i) i j U T := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_integral_sq_qInc_le (N := N) (by linarith : (0:ℝ) < p) hp0 hp1 hm
      (eps := 1 / 64) (by norm_num) i j
  refine qResidual_of_orthogonal (N := N) hp0 hp1 (m := m) (i := i) (j := j)
    (fun t => (hC t).1) horth ?_
  exact summable_dyaW_qInc (N := N) (by linarith : (0:ℝ) < p) hp0 hp1 hm
    (eps := 1 / 64) (by norm_num) i j

/-! ## 10. The threshold: a bounded diagonal already satisfies the criterion -/

/-- **The dyadic criterion only needs `a_t < t^{1-λ}`: a bounded diagonal suffices.**

Since `2^(k+1)/4^k = 2/2^k`, any uniformly bounded non-negative diagonal `a` makes the weighted
dyadic series converge.  (Growth like `a_t ~ t^β` is allowed for every `β < 1`; the old `O(t^2)`
bound is above the threshold, a `(log t)^A` bound is far below it.) -/
theorem summable_dyaW_of_bounded_sq {a : ℕ → ℝ} (ha0 : ∀ t : ℕ, 0 ≤ a t) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t : ℕ, a t ≤ C) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)), a t) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  have h1 : Summable (fun k : ℕ => (2 * C) * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k)) := by
    have h2 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k) := by
      have he : (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k)
          = fun k : ℕ => ((k : ℝ) ^ 2 + 2 * (k : ℝ) + 1) * (1 / 2 : ℝ) ^ k := by
        funext k; ring
      rw [he]
      simpa only [pow_one, pow_zero] using
        ((((hs).add ((summable_pow_mul_geometric_of_norm_lt_one
          (r := (1 / 2 : ℝ)) 1 (by norm_num)).mul_left 2)).add
          (summable_pow_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) 0 (by norm_num)))).congr
          (fun k => by ring)
    exact h2.mul_left _
  have hstep : ∀ k : ℕ, ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      (∑ t ∈ Finset.range (2 ^ (k + 1)), a t)
      ≤ (2 * C) * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hsum : (∑ t ∈ Finset.range (2 ^ (k + 1)), a t)
        ≤ (2 : ℝ) ^ (k + 1) * C := by
      calc ∑ t ∈ Finset.range (2 ^ (k + 1)), a t
          ≤ ∑ t ∈ Finset.range (2 ^ (k + 1)), C := Finset.sum_le_sum (fun t _ => hC t)
        _ = (2 : ℝ) ^ (k + 1) * C := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hcoef : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k := by positivity
    calc ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k * (∑ t ∈ Finset.range (2 ^ (k + 1)), a t)
        ≤ ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k * ((2 : ℝ) ^ (k + 1) * C) :=
          mul_le_mul_of_nonneg_left hsum hcoef
      _ = (2 * C) * (((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ k) := by
          rw [← mul_assoc, dyaW_mul_pow k]; ring
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (Finset.sum_nonneg (fun t _ => ha0 t))) hstep h1

/-! ## 11. What the covariance-mass hypotheses still require -/

/-- **The covariance-mass hypotheses imply the dyadic diagonal criterion.**

The correlated strong law (`QCorrelatedStrongLaw` via `QCorrelatedActual`) asks for absolute
summability of every covariance column of the raw increment, a per-column majorant `A t`, and
weighted dyadic summability of `A`.  The diagonal summand `s = t` of the column at `t` is exactly
`integral qInc_t^2`, so those three hypotheses **imply** the weighted dyadic summability of the
raw second moments — the same criterion that the raw-orthogonality route needs.

By `summable_dyaW_of_bounded_sq` that criterion is automatic once the diagonal is bounded at all
(the weight satisfies `2^(k+1)/4^k = 2/2^k`).  Hence the diagonal part of `hS`/`hA` carries no
content, and the whole remaining substance of the covariance-mass route is the *absolute
summability of the off-diagonal part of every column* together with the terminal-fluctuation
budget. -/
theorem summable_dyaW_of_covariance_mass {p : ℝ} {m : ℕ} {eps : ℝ} {i j : Fin N} {A : ℕ → ℝ}
    (hS : ∀ t : ℕ, Summable (fun s : ℕ =>
      |∫ U, qInc p m eps i j s U * qInc p m eps i j t U ∂(arrayMeasure N)|))
    (hA : ∀ t : ℕ, (∑' s : ℕ,
      |∫ U, qInc p m eps i j s U * qInc p m eps i j t U ∂(arrayMeasure N)|) ≤ A t)
    (hw : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)), A t)) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / (4 : ℝ) ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)) := by
  have hdiag : ∀ t : ℕ, ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N) ≤ A t := by
    intro t
    have hdiageq : ∫ U, qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        = |∫ U, qInc p m eps i j t U * qInc p m eps i j t U ∂(arrayMeasure N)| := by
      have e : (fun U : Array N => qInc p m eps i j t U ^ 2)
          = fun U => qInc p m eps i j t U * qInc p m eps i j t U := by
        funext U; ring
      rw [e, abs_of_nonneg (integral_nonneg (fun U => mul_self_nonneg _))]
    rw [hdiageq]
    exact ((hS t).le_tsum t (fun s _ => abs_nonneg _)).trans (hA t)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hw
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => integral_nonneg (fun U => sq_nonneg _)))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hdiag t)) (by positivity)

end SwarmActualBudget

/-! ## Axiom audit -/


