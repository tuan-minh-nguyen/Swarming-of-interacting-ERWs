/-
  # `(lococc)` in the paper's literal shape: `+ C_T L^{3/4}`

  `LocOccAllPairs.lococc_recordCarrier_allPairs` proves the paper's display for every pair of
  distinct walkers and every start of the window, but with the abstract remainder
  `L34 L (Lw T L)`.  `L34PaperScale.L34_Lw_le_rpow34` converts that remainder into `C_T L^{3/4}`.
  Here the two are composed, which yields the display exactly as printed in Proposition `local`:

      sum_{u=s}^{t-1} 1{X^i_u <= M^j_u}
        <= C (M_t^i - M^i_s + M^i_s - X^i_s + (M^i_s - M^j_s)_+) + (t-s)/8 + C_T L^{3/4}.

  The coefficient `C` of the record-dependent combination is `Kocc p m C`, which contains no `T`;
  the `T`-dependence sits entirely in `CTocc p m C T` (through `(2T+3)`), exactly as the paper's
  "`C` independent of `T`, `C_T` depending only on `N,m,p,T`".
-/
import Swarm.LocOccAllPairs
import Swarm.L34PaperScale

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccPaperScale

open Finset
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier LocOccAllStarts LocOccAllPairs
open LocOccCarrierAssembly SummedSlope.Model

variable {N : ℕ} [Nonempty (Fin N)]

/-- The paper's `C` in front of the record-dependent combination.  It contains `C` (the
`(locsum)`/`(locmax)` constant, depending only on `N,m,p`), `Lc p m`, `CJc p m` — and **no** `T`. -/
noncomputable def Kocc (p : ℝ) (m : ℕ) (C : ℝ) : ℝ :=
  (2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1

/-- The paper's `C_T` in front of `L^{3/4}`.  Its `T`-dependence is exactly `(2T+3)`. -/
noncomputable def CTocc (p : ℝ) (m : ℕ) (C : ℝ) (T : ℕ) : ℝ :=
  (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1 + 4 / (1 - aRec p m))
    * (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
        + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1)

theorem Kocc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ}
    (hC1 : 1 ≤ C) : 0 ≤ Kocc p m C := by
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have h1 := Lc_nonneg hp1 hp2 m
  have h2 := CJc_nonneg hp1 hp2 m
  unfold Kocc
  nlinarith

theorem CTocc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {C : ℝ}
    (hC1 : 1 ≤ C) (T : ℕ) : 0 ≤ CTocc p m C T := by
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have h1 := KFc_nonneg hp1 hp2 m
  have h2 := CJc_nonneg hp1 hp2 m
  have h3 := one_sub_aRec_pos hp1 hp2 m
  have h4 : (0 : ℝ) ≤ 4 / (1 - aRec p m) := by positivity
  have h5 : (0 : ℝ) ≤ 9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
      + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1 := by positivity
  unfold CTocc
  have h6 : (0 : ℝ) ≤ 2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
      + 4 / (1 - aRec p m) := by nlinarith
  exact mul_nonneg h6 h5

/-- **The paper's `(lococc)` display in its literal form**, for all pairs of distinct walkers and
all starts of the window, on the single event `GoodAllPairs`:
`Kocc p m C` times the record-dependent combination, plus `(t-s)/8`, plus `CTocc p m C T L^{3/4}`. -/
theorem lococc_allPairs_paperScale
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) {L : ℕ} (hL : 1 ≤ L) {T : ℕ} (hT : 1 ≤ T) {r s0 : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hLsum : ∀ (j : Fin N) (U : Array N),
      U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) →
      ∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      U ∈ GoodAllPairs (N := N) p m C r T L s0 →
      ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
          ≤ Kocc p m C *
              ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ))
                + (((runMax p m U q.1 s).toNat : ℝ)
                    - (((trajectory p m U s).pos q.1).toNat : ℝ))
                + max 0 (((runMax p m U q.1 s).toNat : ℝ)
                    - ((runMax p m U q.2 s).toNat : ℝ)))
            + ((t : ℝ) - (s : ℝ)) / 8
            + CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ)) := by
  have hL34 := L34PaperScale.L34_Lw_le_rpow34 T hL
  have hK : 0 ≤ Kocc p m C := Kocc_nonneg hp1 hp2 hC1
  have hCT : 0 ≤ CTocc p m C T := CTocc_nonneg hp1 hp2 hC1 T
  have hCTeq : CTocc p m C T
      = (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1 + 4 / (1 - aRec p m))
        * (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
            + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1) := rfl
  rw [hCTeq] at hCT ⊢
  filter_upwards [lococc_recordCarrier_allPairs (N := N) hp1 hp2 hm hC1 hL hT hr hLsum]
    with U hall
  intro q hq hUc hgood s t h1 h2 h3
  have hmain := hall q hq hUc hgood s t h1 h2 h3
  have hcoef : ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) = Kocc p m C := rfl
  rw [hcoef] at hmain
  have hstep : (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
        + 4 / (1 - aRec p m)) * L34 L (Lw T L)
      ≤ ((2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
            + 4 / (1 - aRec p m))
          * (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
              + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have h0 : (0 : ℝ) ≤ 2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
        + 4 / (1 - aRec p m) := by
      have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
      have h1' := KFc_nonneg hp1 hp2 m
      have h2' := CJc_nonneg hp1 hp2 m
      have h3' := one_sub_aRec_pos hp1 hp2 m
      have h4 : (0 : ℝ) ≤ 4 / (1 - aRec p m) := by positivity
      nlinarith
    calc (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
          + 4 / (1 - aRec p m)) * L34 L (Lw T L)
        ≤ (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
            + 4 / (1 - aRec p m))
            * ((9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
                + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1) * (L : ℝ) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hL34 h0
      _ = ((2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1
            + 4 / (1 - aRec p m))
          * (9 * (((2 * T + 3 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
              + (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 8 : ℝ) + 1)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
          ring
  linarith [hmain, hstep]

/-- The same, packaged with `LocSumR1.array_locsum_h_start`: only `LocSum.Mb p (qOf p m) < C`,
`T >= 1`, `(T+3)L <= r` and `2 ellT (xOf (Lw T L)) <= A0 r T L` remain, together with the
exponential bound on the good event's `(locsum)`/`(locmax)` component. -/
theorem exists_lococc_allPairs_paperScale
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ {r s0 : ℕ},
      (T + 3) * L ≤ r → 2 * ellT (xOf (Lw T L)) ≤ A0 r T L →
      ((arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
          ENNReal.ofReal (Real.exp (-c * xOf (Lw T L)))) ∧
      (∀ᵐ U ∂(arrayMeasure N), ∀ q : Fin N × Fin N, q ∈ offDiag (N := N) →
        U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
        U ∈ GoodAllPairs (N := N) p m C r T L s0 →
        ∀ s t : ℕ, s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
          ∑ u ∈ Finset.Ico s t,
              (if (trajectory p m U u).pos q.1 ≤ runMax p m U q.2 u then (1 : ℝ) else 0)
            ≤ Kocc p m C *
                ((((runMax p m U q.1 t).toNat : ℝ) - ((runMax p m U q.1 s).toNat : ℝ))
                  + (((runMax p m U q.1 s).toNat : ℝ)
                      - (((trajectory p m U s).pos q.1).toNat : ℝ))
                  + max 0 (((runMax p m U q.1 s).toNat : ℝ)
                      - ((runMax p m U q.2 s).toNat : ℝ)))
              + ((t : ℝ) - (s : ℝ)) / 8
              + CTocc p m C T * ((L : ℝ) ^ (3 / 4 : ℝ))) := by
  obtain ⟨c, hc, L₀, hL0⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hL
  have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
  intro r s0 hr hbig
  have hLLw : L₀ ≤ Lw T L := le_trans hL₀ (le_Lw T L)
  have hres := hL0 (Lw T L) hLLw (A0 r T L) hbig
  exact ⟨hres.1, lococc_allPairs_paperScale (N := N) hp1 hp2 hm hC1 hL1 hT hr
    (fun j U hU a b ha hb hab => hres.2 U hU j a b ha hb hab)⟩

end LocOccPaperScale
