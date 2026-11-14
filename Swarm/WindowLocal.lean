/-
# The windowed `(locmove)` failure event, measured with the canonical geometry

`MWin.measureReal_locMoveFailAtClockWin_le` measures the windowed `(locmove)` failure event but
takes two inputs: a bad set `bad` (where the `(loccoord)` display may fail) with a bound `eb`, and
a *free* window family `geom` with the pointwise display `hcc` on `badᶜ ∩ geom`.

Both are supplied here by the **canonical** objects, with no extra hypothesis:

* `bad := SingleBad.badAll` (hence `UniversalFamily.univBad`), with `eb` the proved `exf` profile
  `SingleBad.exists_badAll_bound`;
* `geom := ClockLocMove.locCoordGeom p m A hA r T L`, the `(loccoord)` carrier *itself*, so that
  `U ∈ geom s t` is *literally* the geometric window hypothesis of the `(loccoord)` display;
* `hcc` is then the `(loccoord)` conjunct of `UniversalFamily.exists_universal_bad_and_good`,
  with `C = Cmax`, `β = betaOf` and `3·Cmax·betaOf = Cerr·L^{3/4}`.

The result is a per-group bound uniform in the group `A`:
`2 · [(T+3)L+1]^2 · exp (-ε₁²/(4(T+3)L(2·stepEnv p (Bstar L))²))` plus the same with `Bstar L`
plus the `exf` profile, and both exponential terms are converted into the profile by
`WindowAbsorb`, using `RecClockLG.Bstar L = O(xOf L)` and `stepEnv p B = O(B²)`.
-/
import Swarm.WindowAbsorb

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace WindowLocal

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. `Bstar` and `stepEnv` are polynomial in the profile variable -/

/-- The truncation level `Bstar L` is linear in `xOf L`. -/
theorem Bstar_le (L : ℕ) : RecClockLG.Bstar L ≤ 2 * LocSumAct.xOf L + 6 := by
  unfold RecClockLG.Bstar
  refine max_le ?_ ?_
  · linarith
  · linarith

/-- `Bstar L` is nonnegative for every scale. -/
theorem Bstar_nonneg' (L : ℕ) : (0 : ℝ) ≤ RecClockLG.Bstar L := by
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
  unfold RecClockLG.Bstar
  refine le_trans ?_ (le_max_left _ _)
  linarith

/-- The one-step envelope at `Bstar L` is quadratic in `xOf L`. -/
theorem stepEnv_Bstar_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) (L : ℕ) :
    stepEnv (N := N) p (RecClockLG.Bstar L)
      ≤ (16 + 162 * (N : ℝ)) * (LocSumAct.xOf L + 1) ^ 2 := by
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
  have hB := Bstar_le L
  have hB0 : (0 : ℝ) ≤ RecClockLG.Bstar L := Bstar_nonneg' L
  have hquad := stepEnv_le_quad (N := N) hp0 hp1 hB0
  have hcoef : (2 * p - 1) / p ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hcoef0 : (0 : ℝ) ≤ (2 * p - 1) / p := by
    apply div_nonneg _ (by linarith)
    linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hstep : stepEnv (N := N) p (RecClockLG.Bstar L)
      = 2 * RecClockLG.Bstar L
        + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + RecClockLG.Bstar L) * RecClockLG.Bstar L)) :=
    stepEnv_eq p _
  rw [hstep]
  -- `1 + B ≤ 2x+7 ≤ 9(x+1)`, `B ≤ 9(x+1)`
  have h1B : 1 + RecClockLG.Bstar L ≤ 9 * (LocSumAct.xOf L + 1) := by nlinarith
  have hB9 : RecClockLG.Bstar L ≤ 9 * (LocSumAct.xOf L + 1) := by nlinarith
  have hprod : (1 + RecClockLG.Bstar L) * RecClockLG.Bstar L
      ≤ 81 * (LocSumAct.xOf L + 1) ^ 2 := by
    have h0 : (0:ℝ) ≤ 9 * (LocSumAct.xOf L + 1) := by linarith
    calc (1 + RecClockLG.Bstar L) * RecClockLG.Bstar L
        ≤ (9 * (LocSumAct.xOf L + 1)) * (9 * (LocSumAct.xOf L + 1)) :=
          mul_le_mul h1B hB9 hB0 h0
      _ = 81 * (LocSumAct.xOf L + 1) ^ 2 := by ring
  have hprod0 : 0 ≤ (1 + RecClockLG.Bstar L) * RecClockLG.Bstar L := by
    have : (0:ℝ) ≤ 1 + RecClockLG.Bstar L := by linarith
    exact mul_nonneg this hB0
  have hmid : ((2 * p - 1) / p) * (N : ℝ) * ((1 + RecClockLG.Bstar L) * RecClockLG.Bstar L)
      ≤ (N : ℝ) * (81 * (LocSumAct.xOf L + 1) ^ 2) := by
    have h1 : ((2 * p - 1) / p) * (N : ℝ) ≤ 1 * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoef hN0
    calc ((2 * p - 1) / p) * (N : ℝ) * ((1 + RecClockLG.Bstar L) * RecClockLG.Bstar L)
        ≤ (1 * (N : ℝ)) * (81 * (LocSumAct.xOf L + 1) ^ 2) :=
          mul_le_mul h1 hprod hprod0 (by positivity)
      _ = (N : ℝ) * (81 * (LocSumAct.xOf L + 1) ^ 2) := by ring
  have hfin : 2 * RecClockLG.Bstar L
        + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + RecClockLG.Bstar L) * RecClockLG.Bstar L))
      ≤ (16 + 162 * (N : ℝ)) * (LocSumAct.xOf L + 1) ^ 2 := by
    have hxB : 2 * RecClockLG.Bstar L ≤ 18 * (LocSumAct.xOf L + 1) := by nlinarith
    have hx1 : (1:ℝ) ≤ (LocSumAct.xOf L + 1) ^ 2 := by nlinarith
    nlinarith
  linarith

/-- The same envelope, squared: `(2 stepEnv p (Bstar L))² ≤ K (x+1)^4`. -/
theorem two_stepEnv_Bstar_sq_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) (L : ℕ) :
    (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
      ≤ 4 * (16 + 162 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L + 1) ^ 4 := by
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
  have hC : (0:ℝ) ≤ 16 + 162 * (N : ℝ) := by positivity
  have hpos : (0:ℝ) ≤ stepEnv (N := N) p (RecClockLG.Bstar L) :=
    stepEnv_nonneg (N := N) hp0 hp1 (Bstar_nonneg' L)
  have h := stepEnv_Bstar_le (N := N) hp0 hp1 (L := L)
  have h2 : (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
      ≤ (2 * ((16 + 162 * (N : ℝ)) * (LocSumAct.xOf L + 1) ^ 2)) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  calc (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
      ≤ (2 * ((16 + 162 * (N : ℝ)) * (LocSumAct.xOf L + 1) ^ 2)) ^ 2 := h2
    _ = 4 * (16 + 162 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L + 1) ^ 4 := by ring

/-! ## 2. Power identities for `ε₁ = L^{3/4}` -/

theorem rpow34_sq {L : ℕ} (hL : 0 < L) :
    ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [← Real.rpow_natCast ((L : ℝ) ^ ((3 : ℝ) / 4)) 2,
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (L:ℝ))]
  norm_num

theorem rpow_half_eq_pow8 (L : ℕ) :
    (L : ℝ) ^ ((1 : ℝ) / 2) = (LocSumAct.xOf L) ^ 8 := by
  have h8 : ((1 : ℝ) / 16) * ((8 : ℕ) : ℝ) = (1 : ℝ) / 2 := by norm_num
  rw [LocSumAct.xOf, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 16)) 8,
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (L:ℝ)), h8]

theorem rpow_three_halves {L : ℕ} (hL : 0 < L) :
    (L : ℝ) ^ ((3 : ℝ) / 2) = (L : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) := by
  have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  rw [h, Real.rpow_add (by positivity : (0:ℝ) < (L:ℝ)), Real.rpow_one]

/-! ## 3. The exponential term of the measured `(locmove)` bound, in the profile -/

/-- **The `(locmove)` martingale term decays at a positive profile rate.**  With `ε₁ = L^{3/4}` and
the truncation level `Bstar L`,

    exp (-ε₁² / (4 (T+3)L (2 stepEnv p (Bstar L))²)) ≤ exf (1 / (256 (T+3) (16+162N)²)) L .

No probability is involved: this is `ε₁² = L^{3/2} = L·L^{1/2} = L·xOf⁸`, the quadratic envelope
of `stepEnv` (`stepEnv_Bstar_le`) and `(x+1)^4 ≤ 16x^4`. -/
theorem exp_env_le_exf {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {T : ℕ} (hT : 1 ≤ T)
    {L : ℕ} (hL : 1 ≤ L) :
    Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ LocalGoodAll.exf (1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)) L := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hx1 : 1 ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) < LocSumAct.xOf L := by linarith
  have hT3 : (0 : ℝ) < (T : ℝ) + 3 := by positivity
  have hC : (0:ℝ) < 16 + 162 * (N : ℝ) := by positivity
  have henv := two_stepEnv_Bstar_sq_le (N := N) hp0 hp1 (L := L)
  -- `((T+3)*L : ℝ) = (T+3) * L`
  have hcast : (((T + 3) * L : ℕ) : ℝ) = ((T : ℝ) + 3) * (L : ℝ) := by push_cast; ring
  -- `ε₁² = L^{3/2} = L * x^8`
  have hε : ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (L : ℝ) * (LocSumAct.xOf L) ^ 8 := by
    rw [rpow34_sq (Nat.lt_of_lt_of_le Nat.zero_lt_one hL), rpow_three_halves (Nat.lt_of_lt_of_le Nat.zero_lt_one hL),
      rpow_half_eq_pow8]
  -- denominator bound
  have hden : 4 * (((T + 3) * L : ℕ) : ℝ) * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
      ≤ 16 * ((T : ℝ) + 3) * (L : ℝ) * (16 + 162 * (N : ℝ)) ^ 2
          * (LocSumAct.xOf L + 1) ^ 4 := by
    rw [hcast]
    have hpos : (0:ℝ) ≤ 4 * (((T : ℝ) + 3) * (L : ℝ)) := by positivity
    calc 4 * (((T : ℝ) + 3) * (L : ℝ))
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
        ≤ 4 * (((T : ℝ) + 3) * (L : ℝ))
            * (4 * (16 + 162 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L + 1) ^ 4) :=
          mul_le_mul_of_nonneg_left henv hpos
      _ = 16 * ((T : ℝ) + 3) * (L : ℝ) * (16 + 162 * (N : ℝ)) ^ 2
            * (LocSumAct.xOf L + 1) ^ 4 := by ring
  have hden_pos : (0:ℝ) < 4 * (((T + 3) * L : ℕ) : ℝ)
      * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by
    have hK : (0:ℝ) < (((T + 3) * L : ℕ) : ℝ) := by
      have h : 0 < (T + 3) * L := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast h
    have h2 : (0:ℝ) < stepEnv (N := N) p (RecClockLG.Bstar L) :=
      stepEnv_pos (N := N) hp0 hp1 (RecClockLG.Bstar_pos hL)
    have h3 : (0:ℝ) < (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by positivity
    nlinarith
  -- the rate comparison
  have hrate : 1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2) * LocSumAct.xOf L
      ≤ ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2
          / (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2) := by
    rw [le_div_iff₀ hden_pos, hε]
    have hx4 : (LocSumAct.xOf L) ^ 4 ≤ (LocSumAct.xOf L + 1) ^ 4 := by
      apply pow_le_pow_left₀ (by linarith)
      linarith
    have hx4pos : (0:ℝ) < (LocSumAct.xOf L) ^ 4 := by positivity
    have hexpand : 1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2) * LocSumAct.xOf L
          * (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
        = (LocSumAct.xOf L)
            * (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
            / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2) := by ring
    -- reduce to `4·L·(2env)²·x ≤ 256(T+3)C²·L·x⁸`
    have step1 : (LocSumAct.xOf L)
          * (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
          / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)
        ≤ (LocSumAct.xOf L)
            * (16 * ((T : ℝ) + 3) * (L : ℝ) * (16 + 162 * (N : ℝ)) ^ 2
              * (LocSumAct.xOf L + 1) ^ 4)
          / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hden (by linarith)
    have step2 : (LocSumAct.xOf L)
          * (16 * ((T : ℝ) + 3) * (L : ℝ) * (16 + 162 * (N : ℝ)) ^ 2
            * (LocSumAct.xOf L + 1) ^ 4)
          / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)
        = (L : ℝ) * (LocSumAct.xOf L) * (LocSumAct.xOf L + 1) ^ 4 / 16 := by
      field_simp
      ring
    rw [hexpand]
    refine le_trans step1 ?_
    rw [step2]
    -- `L x (x+1)^4 / 16 ≤ L x^8` because `(x+1)^4 ≤ 16 x^4` and `x^5 ≤ x^8`
    have hx4' : (LocSumAct.xOf L + 1) ^ 4 ≤ 16 * (LocSumAct.xOf L) ^ 4 := by
      have h1 : LocSumAct.xOf L + 1 ≤ 2 * LocSumAct.xOf L := by linarith
      calc (LocSumAct.xOf L + 1) ^ 4 ≤ (2 * LocSumAct.xOf L) ^ 4 :=
            pow_le_pow_left₀ (by linarith) h1 4
        _ = 16 * (LocSumAct.xOf L) ^ 4 := by ring
    have hx5 : (LocSumAct.xOf L) ^ 5 ≤ (LocSumAct.xOf L) ^ 8 := by
      calc (LocSumAct.xOf L) ^ 5 = (LocSumAct.xOf L) ^ 5 * 1 := (mul_one _).symm
        _ ≤ (LocSumAct.xOf L) ^ 5 * (LocSumAct.xOf L) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc (1:ℝ) = 1 ^ 3 := (one_pow 3).symm
              _ ≤ (LocSumAct.xOf L) ^ 3 := by
                  apply pow_le_pow_left₀ (by linarith) hx1
        _ = (LocSumAct.xOf L) ^ 8 := by ring
    have hkey : (L : ℝ) * (LocSumAct.xOf L) * (LocSumAct.xOf L + 1) ^ 4 / 16
        ≤ (L : ℝ) * (LocSumAct.xOf L) ^ 8 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
      have hLnn : (0:ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have h1 : (L : ℝ) * LocSumAct.xOf L * (LocSumAct.xOf L + 1) ^ 4
          ≤ (L : ℝ) * LocSumAct.xOf L * (16 * (LocSumAct.xOf L) ^ 4) :=
        mul_le_mul_of_nonneg_left hx4' (by positivity)
      have h2 : (L : ℝ) * LocSumAct.xOf L * (16 * (LocSumAct.xOf L) ^ 4)
          = 16 * ((L : ℝ) * (LocSumAct.xOf L) ^ 5) := by ring
      have h3 : 16 * ((L : ℝ) * (LocSumAct.xOf L) ^ 5)
          ≤ 16 * ((L : ℝ) * (LocSumAct.xOf L) ^ 8) := by
        have := mul_le_mul_of_nonneg_left hx5 hLnn
        linarith
      linarith
    exact hkey
  calc Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2)
        / (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ Real.exp (-(1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)
          * LocSumAct.xOf L)) := by
        apply Real.exp_le_exp.mpr
        have h := neg_le_neg hrate
        simp only [neg_div] at h ⊢
        linarith
    _ = LocalGoodAll.exf (1 / (256 * ((T : ℝ) + 3) * (16 + 162 * (N : ℝ)) ^ 2)) L := by
        unfold LocalGoodAll.exf
        ring_nf

/-- The second (max-growth) term of the measured bound is dominated by the first, because
`Bstar L ≤ stepEnv p (Bstar L)`: the envelope's own scale is at least the truncation level. -/
theorem exp_maxgrowth_le_exp_env {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {T : ℕ}
    {L : ℕ} (hL : 1 ≤ L) :
    Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hB : (0:ℝ) < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL
  have henv : RecClockLG.Bstar L ≤ stepEnv (N := N) p (RecClockLG.Bstar L) := by
    have h := stepEnv_eq (N := N) p (RecClockLG.Bstar L)
    have hcoef : (0:ℝ) ≤ ((2 * p - 1) / p) * (N : ℝ)
        * ((1 + RecClockLG.Bstar L) * RecClockLG.Bstar L) := by
      have h1 : (0:ℝ) ≤ (2 * p - 1) / p := by
        apply div_nonneg _ (by linarith); linarith
      have h2 : (0:ℝ) ≤ (1 + RecClockLG.Bstar L) * RecClockLG.Bstar L := by
        have : (0:ℝ) ≤ 1 + RecClockLG.Bstar L := by linarith
        exact mul_nonneg this hB.le
      exact mul_nonneg (mul_nonneg h1 (Nat.cast_nonneg N)) h2
    rw [h]; nlinarith
  have hK : (0:ℝ) < (((T + 3) * L : ℕ) : ℝ) := by
    have : 0 < (T + 3) * L := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hden1 : (0:ℝ) < 4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2 := by
    have h3 : (0:ℝ) < (2 * RecClockLG.Bstar L) ^ 2 := by positivity
    nlinarith
  have hden2 : (0:ℝ) < 4 * (((T + 3) * L : ℕ) : ℝ)
      * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by
    have h2 : (0:ℝ) < stepEnv (N := N) p (RecClockLG.Bstar L) :=
      stepEnv_pos (N := N) hp0 hp1 hB
    have h3 : (0:ℝ) < (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by positivity
    nlinarith
  have hεnn : (0:ℝ) ≤ ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 := by positivity
  have hsq : (2 * RecClockLG.Bstar L) ^ 2 ≤ (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hdenle : 4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2
      ≤ 4 * (((T + 3) * L : ℕ) : ℝ)
        * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by
    have hK : (0:ℝ) ≤ (((T + 3) * L : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hsq (by linarith : (0:ℝ) ≤ 4 * (((T + 3) * L : ℕ) : ℝ))
    linarith
  have hstep : ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2
        / (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
      ≤ ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2
        / (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2) :=
    div_le_div_of_nonneg_left hεnn hden1 hdenle
  have h := neg_le_neg hstep
  simp only [neg_div] at h ⊢
  linarith

end WindowLocal
