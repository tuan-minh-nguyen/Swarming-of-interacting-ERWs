/-
  # Paper-scale complement bound for the record-carrier good event

  This module takes the *already compiled* joint record-carrier union bound

      `LocOccCarrierAssembly.measureReal_recordCarrier_joint_le`

  and composes it with the accepted residual identifications of `CarrierQplResidual`:

  * `carrier ∩ shiftedContDefect = ∅` at the paper parameters `A = r-(T+2)L`, `M = Lw+1`;
  * `carrier ∩ harmDefect ⊆ exp (-c Lw^{1/16})`.

  The remaining two terms (the carrier-weighted maximal Azuma price at
  `V = Lw^{1/16}` and the cardinality-weighted projected-oscillation term) are bounded
  by elementary explicit arithmetic: `envB(Lw^{1/16})` is `O(L^{1/16})`,
  `capB(Lw^{1/16})` is `O(L^{1/16})`, and `L34 >= L^{3/4}`, so both exponents dominate
  a fixed positive multiple of `L^{1/16}`.  A Taylor bound for `exp` absorbs the
  polynomial prefactor `O(L^2)`.

  Outcome: an explicit `C_T` and `c_T > 0` with

      mu(carrier ∩ {the three-field good event fails}) <= C_T * exp (-c_T * L^{1/16}).

  `C_T` and `c_T` are explicit functions of the input rate `c`, `N`, `m`, `p`, `T`.
  Nothing else is assumed: no carrier mass, no independence of the fields, no new
  probability input.  The good event is exactly the one of the joint bound
  (`no LsBad`, `no qplDrop`, `OscPair`), i.e. no field and no site is dropped.
-/
import Swarm.LocOccCarrierAssembly
import Swarm.CarrierQplResidual

set_option maxHeartbeats 6400000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RecCarrierPaper

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct LocOccCarrier
open SummedSlope.Model
open LocOccCarrierAssembly

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The paper window as a function of `L` -/

/-- `xOf` is monotone. -/
theorem xOf_le_of_le {L M : ℕ} (h : L ≤ M) : xOf L ≤ xOf M := by
  unfold xOf
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by norm_num)

/-- `Lw = (2T+2)L + 1 <= (2T+3)L` for `L >= 1`. -/
theorem Lw_le_paper {T L : ℕ} (hL : 1 ≤ L) : Lw T L ≤ (2 * T + 3) * L := by
  unfold Lw
  have h1 : (2 * T + 2) * L + 1 ≤ (2 * T + 2) * L + L := by omega
  have h2 : (2 * T + 2) * L + L = (2 * T + 3) * L := by ring
  omega

/-- `xOf Lw <= (2T+3) * L^{1/16}`. -/
theorem xOf_Lw_le {T L : ℕ} (hL : 1 ≤ L) :
    xOf (Lw T L) ≤ ((2 * T + 3 : ℕ) : ℝ) * (L : ℝ) ^ (1 / 16 : ℝ) := by
  have hmono := xOf_le_of_le (L := Lw T L) (M := (2 * T + 3) * L) (Lw_le_paper (T := T) hL)
  have hsplit : xOf ((2 * T + 3) * L)
      = (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 16 : ℝ) * (L : ℝ) ^ (1 / 16 : ℝ) := by
    unfold xOf
    have hcast : ((((2 * T + 3) * L : ℕ)) : ℝ) = (((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ) := by
      push_cast; ring
    rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
  have hbase1 : (1 : ℝ) ≤ ((2 * T + 3 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * T + 3 := by omega
    exact_mod_cast this
  have hb : (((2 * T + 3 : ℕ)) : ℝ) ^ (1 / 16 : ℝ) ≤ (((2 * T + 3 : ℕ)) : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase1 (by norm_num : (1 / 16 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at h
  have hL16 : (0 : ℝ) ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [hsplit] at hmono
  nlinarith [hmono, hb, hL16]

/-! ## 2. The envelopes `capB` and `envB` at `V = Lw^{1/16}` are `O(L^{1/16})` -/

/-- `capB` is at most `9 Cproj * V` once `V >= 1`. -/
theorem capB_le_nine {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {V : ℝ} (hV : 1 ≤ V) :
    SiteHMax.capB p m V ≤ 9 * SiteHMax.Cproj p m * V := by
  have hC : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp1 hp2 m
  have h2 : 2 * V + 7 ≤ 9 * V := by linarith
  have h3 : SiteHMax.Cproj p m * (2 * V + 7) ≤ SiteHMax.Cproj p m * (9 * V) :=
    mul_le_mul_of_nonneg_left h2 hC
  unfold SiteHMax.capB
  nlinarith [h3]

/-- The constant of the `V`-linear bound on `envB`. -/
noncomputable def Kb (p : ℝ) (m : ℕ) : ℝ :=
  18 * SiteHMax.Cproj p m + 12 + 12 * (1 - aRec p m)⁻¹ + 8 * QplWindow.Lc p m

theorem Kb_pos {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) : 0 < Kb p m := by
  have hC : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp1 hp2 m
  have ha : 0 < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have hinv : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr ha
  have hLc : 0 ≤ QplWindow.Lc p m := QplWindow.Lc_nonneg hp1 hp2 m
  unfold Kb
  nlinarith

theorem Kb_nonneg {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) : 0 ≤ Kb p m :=
  (Kb_pos hp1 hp2).le

/-- `envB` at `V >= 1` is at most `Kb * V`. -/
theorem envB_le_Kb {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {V : ℝ} (hV : 1 ≤ V) :
    QplPredEnv.envB p m V (QplWindow.envC p m V) ≤ Kb p m * V := by
  have hC : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp1 hp2 m
  have ha : 0 < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have hinv : 0 ≤ (1 - aRec p m)⁻¹ := inv_nonneg.mpr ha.le
  have hLc : 0 ≤ QplWindow.Lc p m := QplWindow.Lc_nonneg hp1 hp2 m
  have hcap := capB_le_nine (p := p) (m := m) hp1 hp2 hV
  have hV0 : 0 ≤ V := by linarith
  -- `envC <= 6V + 4Lc`
  have henvC : QplWindow.envC p m V ≤ 6 * V + 4 * QplWindow.Lc p m := by
    unfold QplWindow.envC
    linarith
  -- the inverse term
  have hstep : V + 2 ≤ 3 * V := by linarith
  have hprod : 2 * (V + 2) * (1 - aRec p m)⁻¹ ≤ 6 * V * (1 - aRec p m)⁻¹ := by
    have h2 : 2 * (V + 2) ≤ 2 * (3 * V) := by linarith
    calc 2 * (V + 2) * (1 - aRec p m)⁻¹
        ≤ (2 * (3 * V)) * (1 - aRec p m)⁻¹ := mul_le_mul_of_nonneg_right h2 hinv
      _ = 6 * V * (1 - aRec p m)⁻¹ := by ring
  have hsum : SiteHMax.capB p m V + QplWindow.envC p m V
      + 2 * (V + 2) * (1 - aRec p m)⁻¹
      ≤ 9 * SiteHMax.Cproj p m * V + (6 * V + 4 * QplWindow.Lc p m) + 6 * V * (1 - aRec p m)⁻¹ := by
    linarith
  have h2 : QplPredEnv.envB p m V (QplWindow.envC p m V)
      ≤ 2 * (9 * SiteHMax.Cproj p m * V + (6 * V + 4 * QplWindow.Lc p m)
          + 6 * V * (1 - aRec p m)⁻¹) := by
    unfold QplPredEnv.envB
    linarith
  have h3 : 2 * (9 * SiteHMax.Cproj p m * V + (6 * V + 4 * QplWindow.Lc p m)
        + 6 * V * (1 - aRec p m)⁻¹) ≤ Kb p m * V := by
    unfold Kb
    have hLcV : QplWindow.Lc p m ≤ QplWindow.Lc p m * V := by nlinarith
    nlinarith [hLcV]
  linarith

/-- `xOf (Lw) >= 1`. -/
theorem one_le_xOf_Lw (T L : ℕ) : (1 : ℝ) ≤ xOf (Lw T L) := by
  apply one_le_xOf
  unfold Lw; omega

/-- The maximal-Azuma envelope at the paper's scale, as a power of `L`. -/
theorem envB_xOf_Lw_le {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {T L : ℕ} (hL : 1 ≤ L) :
    QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
      ≤ (Kb p m * (((2 * T + 3 : ℕ)) : ℝ)) * (L : ℝ) ^ (1 / 16 : ℝ) := by
  have h1 := envB_le_Kb (p := p) (m := m) hp1 hp2 (V := xOf (Lw T L)) (one_le_xOf_Lw T L)
  have h2 := xOf_Lw_le (T := T) (L := L) hL
  have hK : 0 ≤ Kb p m := Kb_nonneg hp1 hp2
  calc QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
      ≤ Kb p m * xOf (Lw T L) := h1
    _ ≤ Kb p m * ((((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ) ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hK
    _ = (Kb p m * (((2 * T + 3 : ℕ)) : ℝ)) * (L : ℝ) ^ (1 / 16 : ℝ) := by ring

/-- The `(locmax)` cap envelope at the paper's scale, as a power of `L`. -/
theorem capB_xOf_Lw_le {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {T L : ℕ} (hL : 1 ≤ L) :
    SiteHMax.capB p m (xOf (Lw T L))
      ≤ (9 * SiteHMax.Cproj p m * (((2 * T + 3 : ℕ)) : ℝ)) * (L : ℝ) ^ (1 / 16 : ℝ) := by
  have h1 := capB_le_nine (p := p) (m := m) hp1 hp2 (V := xOf (Lw T L)) (one_le_xOf_Lw T L)
  have h2 := xOf_Lw_le (T := T) (L := L) hL
  have hC : 0 ≤ SiteHMax.Cproj p m := SiteHMax.Cproj_nonneg hp1 hp2 m
  calc SiteHMax.capB p m (xOf (Lw T L))
      ≤ 9 * SiteHMax.Cproj p m * xOf (Lw T L) := h1
    _ ≤ 9 * SiteHMax.Cproj p m * ((((2 * T + 3 : ℕ)) : ℝ) * (L : ℝ) ^ (1 / 16 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = (9 * SiteHMax.Cproj p m * (((2 * T + 3 : ℕ)) : ℝ)) * (L : ℝ) ^ (1 / 16 : ℝ) := by ring

/-! ## 3. The two exponents dominate a fixed multiple of `L^{1/16}` -/

/-- `(L^{1/16})^2 = L^{1/8}`. -/
theorem sq_sixteenth {L : ℝ} (hL : 0 ≤ L) :
    (L ^ (1 / 16 : ℝ)) ^ 2 = L ^ (1 / 8 : ℝ) := by
  rw [← Real.rpow_natCast (L ^ (1 / 16 : ℝ)) 2, ← Real.rpow_mul hL]
  norm_num

/-- `(L^{3/4})^2 = L^{3/2}`. -/
theorem sq_three_quarters {L : ℝ} (hL : 0 ≤ L) :
    (L ^ (3 / 4 : ℝ)) ^ 2 = L ^ (3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast (L ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hL]
  norm_num

/-- `L^{1/16} * L * L^{1/8} = L^{19/16}`. -/
theorem rpow_chain {L : ℝ} (hL : 0 < L) :
    L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ) = L ^ (19 / 16 : ℝ) := by
  have h1 : L ^ (1 / 16 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (3 / 16 : ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  calc L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ)
      = L * (L ^ (1 / 16 : ℝ) * L ^ (1 / 8 : ℝ)) := by ring
    _ = L * L ^ (3 / 16 : ℝ) := by rw [h1]
    _ = L ^ (1 : ℝ) * L ^ (3 / 16 : ℝ) := by rw [Real.rpow_one]
    _ = L ^ ((1 : ℝ) + 3 / 16) := by rw [Real.rpow_add hL]
    _ = L ^ (19 / 16 : ℝ) := by norm_num

/-- **Azuma exponent.**  If the maximal envelope is at most `K L^{1/16}` and `L34 >= L^{3/4}`,
then the maximal-Azuma exponent is at least `L^{1/16}/(4 T K^2)`. -/
theorem azuma_exp_arg_ge {L : ℝ} (hL : 1 ≤ L) {T K E L34 : ℝ}
    (hT : 0 < T) (hK : 0 < K) (hE0 : 0 < E) (hEK : E ≤ K * L ^ (1 / 16 : ℝ))
    (hL34 : L ^ (3 / 4 : ℝ) ≤ L34) :
    L ^ (1 / 16 : ℝ) / (4 * T * K ^ 2) ≤ L34 ^ 2 / (4 * (T * L) * E ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL16 : (0 : ℝ) < L ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hE2 : E ^ 2 ≤ (K * L ^ (1 / 16 : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hE0.le hEK 2
  have hE2' : (K * L ^ (1 / 16 : ℝ)) ^ 2 = K ^ 2 * L ^ (1 / 8 : ℝ) := by
    rw [mul_pow, sq_sixteenth hL0.le]
  have hL34' : (L ^ (3 / 4 : ℝ)) ^ 2 ≤ L34 ^ 2 := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) hL34 2
  have hL34'' : (L ^ (3 / 4 : ℝ)) ^ 2 = L ^ (3 / 2 : ℝ) := sq_three_quarters hL0.le
  have hden1 : (0 : ℝ) < 4 * T * K ^ 2 := by positivity
  have hden2 : (0 : ℝ) < 4 * (T * L) * E ^ 2 := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hchain : L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ) = L ^ (19 / 16 : ℝ) := rpow_chain hL0
  have hmono : L ^ (19 / 16 : ℝ) ≤ L ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hA : L ^ (1 / 16 : ℝ) * (4 * (T * L) * E ^ 2)
      ≤ 4 * T * K ^ 2 * L ^ (3 / 2 : ℝ) := by
    have hE2'' : E ^ 2 ≤ K ^ 2 * L ^ (1 / 8 : ℝ) := by rw [← hE2']; exact hE2
    have h1 : L ^ (1 / 16 : ℝ) * (4 * (T * L) * E ^ 2)
        ≤ L ^ (1 / 16 : ℝ) * (4 * (T * L) * (K ^ 2 * L ^ (1 / 8 : ℝ))) := by
      have hpos : (0 : ℝ) ≤ 4 * (T * L) * L ^ (1 / 16 : ℝ) := by positivity
      have h := mul_le_mul_of_nonneg_left hE2'' hpos
      nlinarith [h]
    have h2 : L ^ (1 / 16 : ℝ) * (4 * (T * L) * (K ^ 2 * L ^ (1 / 8 : ℝ)))
        = 4 * T * K ^ 2 * (L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ)) := by ring
    rw [h2, hchain] at h1
    have h3 : 4 * T * K ^ 2 * L ^ (19 / 16 : ℝ) ≤ 4 * T * K ^ 2 * L ^ (3 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left hmono
      positivity
    linarith
  have hB : 4 * T * K ^ 2 * L ^ (3 / 2 : ℝ) ≤ L34 ^ 2 * (4 * T * K ^ 2) := by
    have h : L ^ (3 / 2 : ℝ) ≤ L34 ^ 2 := by rw [← hL34'']; exact hL34'
    nlinarith [h]
  linarith

/-- **Projected-oscillation exponent.** -/
theorem osc_exp_arg_ge {L : ℝ} (hL : 1 ≤ L) {T K B : ℝ}
    (hT : 0 < T) (hK : 0 < K) (hB0 : 0 < B) (hBK : B ≤ K * L ^ (1 / 16 : ℝ)) :
    L ^ (1 / 16 : ℝ) / (16 * T * K ^ 2) ≤ L ^ (3 / 2 : ℝ) / (16 * (T * L) * B ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hB2 : B ^ 2 ≤ K ^ 2 * L ^ (1 / 8 : ℝ) := by
    calc B ^ 2 ≤ (K * L ^ (1 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ hB0.le hBK 2
      _ = K ^ 2 * L ^ (1 / 8 : ℝ) := by rw [mul_pow, sq_sixteenth hL0.le]
  have hden1 : (0 : ℝ) < 16 * T * K ^ 2 := by positivity
  have hden2 : (0 : ℝ) < 16 * (T * L) * B ^ 2 := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hchain : L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ) = L ^ (19 / 16 : ℝ) := rpow_chain hL0
  have hmono : L ^ (19 / 16 : ℝ) ≤ L ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h1 : L ^ (1 / 16 : ℝ) * (16 * (T * L) * B ^ 2)
      ≤ L ^ (1 / 16 : ℝ) * (16 * (T * L) * (K ^ 2 * L ^ (1 / 8 : ℝ))) := by
    have hpos : (0 : ℝ) ≤ 16 * (T * L) * L ^ (1 / 16 : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hB2 hpos
    nlinarith [h]
  have h2 : L ^ (1 / 16 : ℝ) * (16 * (T * L) * (K ^ 2 * L ^ (1 / 8 : ℝ)))
      = 16 * T * K ^ 2 * (L ^ (1 / 16 : ℝ) * L * L ^ (1 / 8 : ℝ)) := by ring
  rw [h2, hchain] at h1
  have h3 : 16 * T * K ^ 2 * L ^ (19 / 16 : ℝ) ≤ L ^ (3 / 2 : ℝ) * (16 * T * K ^ 2) := by
    nlinarith [hmono]
  linarith

/-! ## 4. Absorbing a polynomial prefactor into the stretched exponential -/

/-- For every `k : ℕ` and `b > 0`, `L^k * exp (-b L^{1/16})` is at most an explicit constant
times `exp (-(b/2) L^{1/16})` for all `L >= 1`.  The constant comes from the Taylor lower bound
`exp x >= x^n / n!` at `x = (b/2) L^{1/16}` and `n = 16(k+1)`. -/
theorem pow_mul_exp_neg_absorb {b : ℝ} (hb : 0 < b) (k : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    L ^ k * Real.exp (-b * L ^ (1 / 16 : ℝ)) ≤
      (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1))) *
        Real.exp (-(b / 2) * L ^ (1 / 16 : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hb2 : (0 : ℝ) < b / 2 := by linarith
  have hx : (0 : ℝ) ≤ b / 2 * L ^ (1 / 16 : ℝ) := by positivity
  have htaylor := Real.pow_div_factorial_le_exp (b / 2 * L ^ (1 / 16 : ℝ)) hx (16 * (k + 1))
  have hLpow : (L ^ (1 / 16 : ℝ)) ^ (16 * (k + 1)) = L ^ ((k + 1 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast (L ^ (1 / 16 : ℝ)) (16 * (k + 1)), ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have hpow : (b / 2 * L ^ (1 / 16 : ℝ)) ^ (16 * (k + 1))
      = (b / 2) ^ (16 * (k + 1)) * L ^ ((k + 1 : ℕ) : ℝ) := by
    rw [mul_pow, hLpow]
  have hfac : (0 : ℝ) < (((16 * (k + 1)).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (16 * (k + 1))
  have hbpow : (0 : ℝ) < (b / 2) ^ (16 * (k + 1)) := pow_pos hb2 _
  -- the truncated exponential at order `n = 16(k+1)`
  have h1 : (b / 2) ^ (16 * (k + 1)) * L ^ ((k + 1 : ℕ) : ℝ) / (((16 * (k + 1)).factorial : ℕ) : ℝ)
      ≤ Real.exp (b / 2 * L ^ (1 / 16 : ℝ)) := by
    rw [hpow] at htaylor
    exact htaylor
  have hLcast : L ^ ((k + 1 : ℕ) : ℝ) = L ^ (k + 1) := Real.rpow_natCast L (k + 1)
  have hLk : L ^ k ≤ L ^ ((k + 1 : ℕ) : ℝ) := by
    rw [hLcast]
    calc L ^ k = L ^ k * 1 := by ring
      _ ≤ L ^ k * L := mul_le_mul_of_nonneg_left hL (pow_nonneg hL0.le k)
      _ = L ^ (k + 1) := by ring
  have hnum : (b / 2) ^ (16 * (k + 1)) * L ^ k
      ≤ (b / 2) ^ (16 * (k + 1)) * L ^ ((k + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hLk hbpow.le
  have h2 : (b / 2) ^ (16 * (k + 1)) * L ^ k / (((16 * (k + 1)).factorial : ℕ) : ℝ)
      ≤ Real.exp (b / 2 * L ^ (1 / 16 : ℝ)) := by
    refine le_trans ?_ h1
    exact div_le_div_of_nonneg_right hnum hfac.le
  have h5 : L ^ k ≤ (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
      * Real.exp (b / 2 * L ^ (1 / 16 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt (div_pos hfac hbpow))
    have heq : (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
        * ((b / 2) ^ (16 * (k + 1)) * L ^ k / (((16 * (k + 1)).factorial : ℕ) : ℝ)) = L ^ k := by
      field_simp
    calc L ^ k = (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
          * ((b / 2) ^ (16 * (k + 1)) * L ^ k / (((16 * (k + 1)).factorial : ℕ) : ℝ)) := heq.symm
      _ ≤ (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
          * Real.exp (b / 2 * L ^ (1 / 16 : ℝ)) := hmul
  have hexp : Real.exp (b / 2 * L ^ (1 / 16 : ℝ)) * Real.exp (-b * L ^ (1 / 16 : ℝ))
      = Real.exp (-(b / 2) * L ^ (1 / 16 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc L ^ k * Real.exp (-b * L ^ (1 / 16 : ℝ))
      ≤ ((((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
          * Real.exp (b / 2 * L ^ (1 / 16 : ℝ))) * Real.exp (-b * L ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = (((16 * (k + 1)).factorial : ℝ) / (b / 2) ^ (16 * (k + 1)))
          * Real.exp (-(b / 2) * L ^ (1 / 16 : ℝ)) := by
        rw [mul_assoc, hexp]


/-! ## 5. The paper-scale complement bound for the record-carrier good event

Everything below is composition: the joint union bound `measureReal_recordCarrier_joint_le`
(the three fields `LsBad`, `qplDrop`, `OscPair` on the actual adapted carrier), the
`CarrierQplResidual` identifications of the two `Qpl` residual masses, and the arithmetic of
sections 1-4.  No probability input is added.
-/

/-- `Cproj` is strictly positive. -/
theorem Cproj_pos {p : ℝ} {m : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) :
    0 < SiteHMax.Cproj p m := by
  have ha : 0 < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
  have hinv : 0 < (1 - aRec p m)⁻¹ := inv_pos.mpr ha
  unfold SiteHMax.Cproj
  linarith

/-- **Paper-scale complement bound.**  For the paper's record carrier at `A = r-(T+2)L`,
`Lw = (2T+2)L+1`, the failure of the three-field good event (no `(locsum)`/`(locmax)` failure,
no adapted projected `Qpl` drop, and the start-site projected-oscillation pair) is bounded by
`C_T * exp (-c_T * L^{1/16})` with `c_T > 0` and `C_T >= 0`.

The constant `c_T` is `b/2` where `b` is the minimum of the input rate `c`, the harmonic rate
`c'` of `CarrierQplResidual`, and the two explicit envelope rates `1/(4 T Kb²)` and
`1/(16 T Kcap²)`; `C_T = K3 * 48!/(b/2)^48` absorbs the polynomial prefactor.  Both constants
depend only on `c`, `c'`, `N`, `m`, `p`, `T`. -/
theorem recordCarrier_joint_complement_le_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C c : ℝ} (hC1 : 1 ≤ C) (hc : 0 < c) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s t : ℕ}, (T + 3) * L ≤ r → s ≤ t → t ≤ s + T * L →
      (arrayMeasure N) (LocSumR1.LsBad N p m C (Lw T L) (A0 r T L)) ≤
        ENNReal.ofReal (Real.exp (-c * xOf (Lw T L))) →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
              U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L)
                (2 * L34 L (Lw T L)) ∧
              OscPair p m i j s t L U)}) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  -- the harmonic rate of `CarrierQplResidual`
  obtain ⟨c', hc', L₀', hb'⟩ :=
    CarrierQplResidual.measureReal_carrier_harmDefect_le_exp (N := N) hp1 hp2 hm T hT
  -- the two envelope constants `K1` (Azuma) and `K2` (oscillation)
  set K1 : ℝ := Kb p m * (((2 * T + 3 : ℕ)) : ℝ) with hK1def
  set K2 : ℝ := 9 * SiteHMax.Cproj p m * (((2 * T + 3 : ℕ)) : ℝ) with hK2def
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT3pos : (0 : ℝ) < (((2 * T + 3 : ℕ)) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * T + 3 := by omega
    exact_mod_cast this
  have hK1 : 0 < K1 := mul_pos (Kb_pos hp1 hp2) hT3pos
  have hK2 : 0 < K2 := by
    have := Cproj_pos (p := p) (m := m) hp1 hp2
    rw [hK2def]; positivity
  -- the rate `b`
  set b : ℝ := min (min c c') (min (1 / (4 * (T : ℝ) * K1 ^ 2)) (1 / (16 * (T : ℝ) * K2 ^ 2)))
    with hbdef
  have hb1 : 0 < 1 / (4 * (T : ℝ) * K1 ^ 2) := by positivity
  have hb2 : 0 < 1 / (16 * (T : ℝ) * K2 ^ 2) := by positivity
  have hbpos : 0 < b := by
    rw [hbdef]
    exact lt_min (lt_min hc hc') (lt_min hb1 hb2)
  have hblec : b ≤ c := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hblec' : b ≤ c' := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hbleK1 : b ≤ 1 / (4 * (T : ℝ) * K1 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hbleK2 : b ≤ 1 / (16 * (T : ℝ) * K2 ^ 2) := by
    rw [hbdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- the polynomial constant
  set K3 : ℝ := 3 + 2 * ((T : ℝ) + 1) + 2 * ((T : ℝ) + 1) * (2 * (T : ℝ) + 4) with hK3def
  have hK3 : 0 ≤ K3 := by rw [hK3def]; positivity
  refine ⟨b / 2, by linarith, K3 * (((48).factorial : ℝ) / (b / 2) ^ 48), ?_, max L₀' 1, ?_⟩
  · have hfac : (0 : ℝ) < (((48).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos 48
    have hb2 : (0 : ℝ) < (b / 2) ^ 48 := pow_pos (by linarith) 48
    positivity
  intro L hLbound r s t hr hst htT hLsBad
  have hL : 1 ≤ L := le_trans (le_max_right L₀' 1) hLbound
  have hL₀' : L₀' ≤ L := le_trans (le_max_left L₀' 1) hLbound
  obtain ⟨hA0, hA1⟩ := CarrierQplResidual.cA_hyp_of_paper hT hL hr
  -- the joint union bound, with the two residuals plugged in
  have hJ := LocOccCarrierAssembly.measureReal_recordCarrier_joint_le (N := N) hp1 hp2 hm hij
    (C := C) (L := L) hL (T := T) hT (r := r) (s := s) (t := t) hr hst htT
    (V := xOf (Lw T L)) (one_le_xOf_Lw T L) (w := CarrierQplResidual.cA r T L)
    (M := CarrierQplResidual.cM T L) hA1 hc.le hLsBad
  have hzero := CarrierQplResidual.measureReal_carrier_inter_shiftedContDefect (N := N)
    (p := p) (m := m) (r := r) (s := s) (L := L) (T := T) (n := T * L) hA0 le_rfl i j
  rw [hzero] at hJ
  simp only [add_zero] at hJ
  -- abbreviations used by the joint bound
  set Lr : ℝ := (L : ℝ) ^ (1 / 16 : ℝ) with hLrdef
  set E : ℝ := QplPredEnv.envB p m (xOf (Lw T L)) (QplWindow.envC p m (xOf (Lw T L)))
    with hEdef
  set B : ℝ := SiteHMax.capB p m (xOf (Lw T L)) with hBdef
  set A : ℝ := (arrayMeasure N).real (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L)
    with hAdef
  set harm : ℝ := (arrayMeasure N).real
    (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
      QplWindow.harmDefect p m j (xOf (Lw T L)) (CarrierQplResidual.cA r T L)
        (CarrierQplResidual.cM T L)) with hharmdef
  have hharm : harm ≤ Real.exp (-c' * xOf (Lw T L)) := by
    have h := hb' (r := r) (s := s) (L := L) (j := j) hL₀' hA1
    simpa [hharmdef, CarrierQplResidual.cLw, Lw] using h
  -- positivity and the carrier mass bound
  have hA0' : 0 ≤ A := by rw [hAdef]; exact measureReal_nonneg
  have hA1' : A ≤ 1 := by rw [hAdef]; exact measureReal_le_one
  -- `L^{1/16} <= xOf Lw`
  have hLr_le : Lr ≤ xOf (Lw T L) := by
    have := xOf_le_of_le (L := L) (M := Lw T L) (le_Lw (T := T) L)
    simpa [hLrdef, LocSumAct.xOf] using this
  have hLr0 : 0 ≤ Lr := by rw [hLrdef]; positivity
  -- the harmonic exponential is below the target exponential
  have hharm2 : Real.exp (-c' * xOf (Lw T L)) ≤ Real.exp (-b * Lr) := by
    have harg : -c' * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c' * Lr := mul_le_mul_of_nonneg_right hblec' hLr0
      have h2 : c' * Lr ≤ c' * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc'.le
      linarith
    exact Real.exp_le_exp.mpr harg
  have hharm' : harm ≤ Real.exp (-b * Lr) := le_trans hharm hharm2
  -- term 1: the two `LsBad` exponentials
  have hterm1 : 2 * Real.exp (-c * xOf (Lw T L)) ≤ 2 * Real.exp (-b * Lr) := by
    have harg : -c * xOf (Lw T L) ≤ -b * Lr := by
      have h1 : b * Lr ≤ c * Lr := mul_le_mul_of_nonneg_right hblec hLr0
      have h2 : c * Lr ≤ c * xOf (Lw T L) := mul_le_mul_of_nonneg_left hLr_le hc.le
      linarith
    have := Real.exp_le_exp.mpr harg
    linarith
  -- the Azuma exponent
  have hV1x : (1 : ℝ) ≤ xOf (Lw T L) := one_le_xOf_Lw T L
  have hV0x : (0 : ℝ) ≤ xOf (Lw T L) := by linarith
  have hEpos : 0 < E := by
    rw [hEdef]
    exact QplPredEnv.envB_pos hp1 hp2 m hV0x (QplWindow.envC_nonneg hp1 hp2 m hV0x)
  have hEK : E ≤ K1 * Lr := by
    rw [hEdef, hK1def, hLrdef]
    exact envB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hTLcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hL34 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L (Lw T L) := L34_lower_rpow L (Lw T L)
  have hAzarg : Lr / (4 * (T : ℝ) * K1 ^ 2) ≤ L34 L (Lw T L) ^ 2 /
      (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
    have h := azuma_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K1) (E := E)
      (L34 := L34 L (Lw T L)) (by exact_mod_cast hL) hTpos hK1 hEpos hEK hL34
    simpa [hLrdef, hTLcast] using h
  have hAz : Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2) := by
        have h2 : b * Lr ≤ Lr / (4 * (T : ℝ) * K1 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK1 hLr0
          calc b * Lr ≤ (1 / (4 * (T : ℝ) * K1 ^ 2)) * Lr := h3
            _ = Lr / (4 * (T : ℝ) * K1 ^ 2) := by ring
        linarith
      have heq : ((2 * L34 L (Lw T L) / 2) ^ 2) = L34 L (Lw T L) ^ 2 := by ring
      have hneg : -(L34 L (Lw T L) ^ 2) / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)
          = -(L34 L (Lw T L) ^ 2 / (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the oscillation exponent
  have hBpos : 0 < B := by
    rw [hBdef]
    exact SiteHMax.capB_pos hp1 hp2 m hV0x
  have hBK : B ≤ K2 * Lr := by
    rw [hBdef, hK2def, hLrdef]
    exact capB_xOf_Lw_le (p := p) (m := m) hp1 hp2 (T := T) (L := L) hL
  have hOsc : Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ Real.exp (-b * Lr) := by
    have harg : -((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
        (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) ≤ -b * Lr := by
      have h1 : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
        have h2 : b * Lr ≤ Lr / (16 * (T : ℝ) * K2 ^ 2) := by
          have h3 := mul_le_mul_of_nonneg_right hbleK2 hLr0
          calc b * Lr ≤ (1 / (16 * (T : ℝ) * K2 ^ 2)) * Lr := h3
            _ = Lr / (16 * (T : ℝ) * K2 ^ 2) := by ring
        have h4 := osc_exp_arg_ge (L := (L : ℝ)) (T := (T : ℝ)) (K := K2) (B := B)
          (by exact_mod_cast hL) hTpos hK2 hBpos hBK
        have h4' : b * Lr ≤ (L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2) := by
          rw [hTLcast]
          linarith
        linarith
      have heq : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (L : ℝ) ^ (3 / 2 : ℝ) := sq_three_quarters (by linarith)
      have hneg : -((L : ℝ) ^ (3 / 2 : ℝ)) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)
          = -((L : ℝ) ^ (3 / 2 : ℝ) / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) := by ring
      rw [heq, hneg]
      linarith
    exact Real.exp_le_exp.mpr harg
  -- the sum, with the polynomial prefactor
  have hcoef : (0 : ℝ) ≤ 2 * ((((T * L : ℕ)) : ℝ) + 1) := by positivity
  have hprodA : A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
        (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) ≤
      (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hAz (Real.exp_pos _).le (by norm_num)
    calc A * (2 * ((((T * L : ℕ)) : ℝ) + 1) * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
          (4 * (((T * L : ℕ)) : ℝ) * E ^ 2)))
        = (2 * ((((T * L : ℕ)) : ℝ) + 1)) *
            (A * Real.exp (-((2 * L34 L (Lw T L) / 2) ^ 2) /
              (4 * (((T * L : ℕ)) : ℝ) * E ^ 2))) := by ring
      _ ≤ (2 * ((((T * L : ℕ)) : ℝ) + 1)) * (1 * Real.exp (-b * Lr)) :=
          mul_le_mul_of_nonneg_left h1 hcoef
      _ = (2 * ((((T * L : ℕ)) : ℝ) + 1)) * Real.exp (-b * Lr) := by ring
  have hprodO : (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
        Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)))) ≤
      ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by
    have h1 : A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
          (16 * (((T * L : ℕ)) : ℝ) * B ^ 2)) ≤ 1 * Real.exp (-b * Lr) :=
      mul_le_mul hA1' hOsc (Real.exp_pos _).le (by norm_num)
    calc (Lw T L : ℝ) * (A * (2 * ((((T * L : ℕ)) : ℝ) + 1) *
          Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))))
        = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
            (A * Real.exp (-((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 /
              (16 * (((T * L : ℕ)) : ℝ) * B ^ 2))) := by ring
      _ ≤ ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * (1 * Real.exp (-b * Lr)) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) * Real.exp (-b * Lr) := by ring
  have hsum : (arrayMeasure N).real
      (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
        {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
          U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L)
            (2 * L34 L (Lw T L)) ∧
          OscPair p m i j s t L U)}) ≤
      (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) + (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
        Real.exp (-b * Lr) := by
    nlinarith [hJ, hterm1, hprodA, hharm', hprodO]
  -- the polynomial prefactor is at most `K3 * L^2`
  have hTL1 : (((T * L : ℕ)) : ℝ) + 1 ≤ ((T : ℝ) + 1) * (L : ℝ) := by
    have h1 : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
    have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    rw [h1]; nlinarith
  have hLwle : (Lw T L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
    have h1 : Lw T L ≤ (2 * T + 3) * L := Lw_le_paper (T := T) hL
    have h1' : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 3) * L : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (((2 * T + 3) * L : ℕ) : ℝ) = (2 * (T : ℝ) + 3) * (L : ℝ) := by push_cast; ring
    have h3 : (2 * (T : ℝ) + 3) * (L : ℝ) ≤ (2 * (T : ℝ) + 4) * (L : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith
      nlinarith
    linarith
  have hpoly : 3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) + (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))
      ≤ K3 * (L : ℝ) ^ 2 := by
    have h2 : 2 * ((((T * L : ℕ)) : ℝ) + 1) ≤ 2 * (((T : ℝ) + 1) * (L : ℝ)) := by linarith
    have h3 : (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))
        ≤ ((2 * (T : ℝ) + 4) * (L : ℝ)) * (2 * (((T : ℝ) + 1) * (L : ℝ))) := by
      apply mul_le_mul hLwle h2
      · positivity
      · positivity
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hLsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [hK3def]
    nlinarith
  -- absorb the polynomial into the stretched exponential
  have habs := pow_mul_exp_neg_absorb hbpos 2 (L := (L : ℝ)) (by exact_mod_cast hL)
  have hfinal : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) + (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
        Real.exp (-b * Lr) ≤
      (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by
    have h1 : (3 + 2 * ((((T * L : ℕ)) : ℝ) + 1) + (Lw T L : ℝ) * (2 * ((((T * L : ℕ)) : ℝ) + 1))) *
          Real.exp (-b * Lr) ≤ (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    have h2 : (K3 * (L : ℝ) ^ 2) * Real.exp (-b * Lr)
        = K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) := by ring
    have h3 : K3 * ((L : ℝ) ^ 2 * Real.exp (-b * Lr)) ≤
        K3 * ((((16 * (2 + 1)).factorial : ℝ) / (b / 2) ^ (16 * (2 + 1))) *
          Real.exp (-(b / 2) * Lr)) := by
      apply mul_le_mul_of_nonneg_left _ hK3
      simpa [hLrdef] using habs
    have h4 : (16 * (2 + 1)) = 48 := by norm_num
    rw [h4] at h3
    have h5 : K3 * ((((48).factorial : ℝ) / (b / 2) ^ 48) * Real.exp (-(b / 2) * Lr))
        = (K3 * (((48).factorial : ℝ) / (b / 2) ^ 48)) * Real.exp (-(b / 2) * Lr) := by ring
    linarith [h1, h2, h3, h5]
  linarith [hsum, hfinal]


/-- **The paper's own hypotheses suffice.**  Composing with
`LocOccCarrierAssembly.exists_lococc_recordCarrier_TL'` (which supplies the `LsBad` rate `c` from
`LocSumR1.array_locsum_h_start` at the paper's constant `C`, and removes the arithmetic start
condition) removes the last hypothesis of `recordCarrier_joint_complement_le_paper`: for
`1/2 < p < 1`, `m >= 2`, `i ≠ j`, `C >= 1`, `C > Mb`, `T >= 1` there are `c_T > 0`, `C_T >= 0`
and `L₀` such that for every `L >= L₀`, every `r >= (T+3)L` and every `s <= t <= s + T L`,

  `mu (carrier ∩ {the three-field good event fails}) <= C_T exp (-c_T L^{1/16})`.

The three-field good event is exactly: no `(locsum)`/`(locmax)` failure `LsBad`, no adapted
projected `Qpl` drop at threshold `2 L34`, and the start-site projected-oscillation pair. -/
theorem exists_recordCarrier_joint_complement_paper
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s t : ℕ}, (T + 3) * L ≤ r → s ≤ t → t ≤ s + T * L →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m C (Lw T L) (A0 r T L) ∧
              U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L)
                (2 * L34 L (Lw T L)) ∧
              OscPair p m i j s t L U)}) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  obtain ⟨c, hc, L₀₁, hL₁⟩ :=
    LocOccCarrierAssembly.exists_lococc_recordCarrier_TL' (N := N) hp1 hp2 hm hij hC1 hCM hT
  obtain ⟨c_T, hc_T, C_T, hC_T, L₀₂, hL₂⟩ :=
    recordCarrier_joint_complement_le_paper (N := N) hp1 hp2 hm hij hC1 hc hT
  refine ⟨c_T, hc_T, C_T, hC_T, max L₀₁ L₀₂, ?_⟩
  intro L hL r s t hr hst htT
  have h1 : L₀₁ ≤ L := le_trans (le_max_left _ _) hL
  have h2 : L₀₂ ≤ L := le_trans (le_max_right _ _) hL
  exact hL₂ L h2 hr hst htT (hL₁ L h1 hr hst htT).1

/-- **No free constant `C`.**  The paper's only requirement on `C` is `C >= 1` and `C > Mb`, so
`C := |Mb p (qOf p m)| + 1` is admissible.  This instance makes the dependence of the constants
explicit: `c_T, C_T` are then functions of `N`, `m`, `p`, `T` only (with `Mb` and `qOf` functions
of `p`, `m`). -/
theorem exists_recordCarrier_joint_complement_paper_canonical
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {T : ℕ} (hT : 1 ≤ T) :
    ∃ c_T : ℝ, 0 < c_T ∧ ∃ C_T : ℝ, 0 ≤ C_T ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ {r s t : ℕ}, (T + 3) * L ≤ r → s ≤ t → t ≤ s + T * L →
      (arrayMeasure N).real
          (ActualRecordFiltration.recordPrefixBand (N := N) p m r s L ∩
            {U : Array N | ¬ (U ∉ LocSumR1.LsBad N p m (|LocSum.Mb p (LocSumAct.qOf p m)| + 1)
                (Lw T L) (A0 r T L) ∧
              U ∉ LocOccQ.qplDrop (ProjLedger.Qpl p m (1 / 8) i j) s (T * L)
                (2 * L34 L (Lw T L)) ∧
              OscPair p m i j s t L U)}) ≤
        C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  set Mb := LocSum.Mb p (LocSumAct.qOf p m) with hMb
  have h1 : (1 : ℝ) ≤ |Mb| + 1 := by
    have h := abs_nonneg Mb
    linarith
  have h2 : Mb < |Mb| + 1 := by
    have h := le_abs_self Mb
    linarith
  exact exists_recordCarrier_joint_complement_paper (N := N) hp1 hp2 hm hij
    (C := |Mb| + 1) h1 h2 hT

end RecCarrierPaper


