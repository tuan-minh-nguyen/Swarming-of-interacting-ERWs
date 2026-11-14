/-
# Polynomial-times-profile absorption for the measured block clauses

The measured pieces of the campaign produce error terms of the shapes

  `2^N · [(T+3)L+1]^2 · exp (-L^{3/2} / (4 (T+3) L (2·stepEnv p (Bstar L))^2))`,
  `2N · exp (-r μ / (64 N))`,
  `N · (clockCut N p m r + T·L + 3) · (1-q)^{Kc p L}`,

all of the form `poly(L) · exp (-c · L^{Lipschitz})` with a *polynomial* prefactor.  The paper's
single profile is `exf c L = exp (-c · xOf L)` with `xOf L = L^{1/16}`.  This file proves the
absorption in one place, with no probabilistic content at all:

* `poly_le_exp`: `C · (x^16 + 1)^k ≤ M · exp (b x)` for `x` large (from
  `isLittleO_pow_exp_pos_mul_atTop`);
* `exists_poly_mul_exf_le`: for `0 < cT < c₀` and `k : ℕ`,
  `C₁ · (L+1)^k · exf c₀ L ≤ M · exf cT L` for every `L ≥ L₀`, with a *positive* constant `M`;
* `exp_neg_mul_le_exf`: `exp (-c L) ≤ exf c' L` for `1 ≤ L` and `0 < c' ≤ c`
  (uses `L^{1/16} ≤ L`), the form the record-clock term needs;
* `pow_le_mul_exf`: `(1-q)^K ≤ exf cQ L` from `K ≤ C·xOf L` and `q ∈ (0,1)`, the form the
  finite-run term needs.

Every statement here is elementary real arithmetic; nothing about the process is assumed.
-/
import Swarm.SingleBadGroups
import Swarm.LocCoordGeomCarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 1200000
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

namespace WindowAbsorb

/-! ## 1. The profile is monotone in its rate -/

/-- A smaller rate gives a *larger* profile term. -/
theorem exf_mono_c {c c' : ℝ} (h : c' ≤ c) (L : ℕ) :
    LocalGoodAll.exf c L ≤ LocalGoodAll.exf c' L := by
  unfold LocalGoodAll.exf
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
  nlinarith

theorem exf_pos (c : ℝ) (L : ℕ) : 0 < LocalGoodAll.exf c L := Real.exp_pos _

/-- `xOf L = L^{1/16} ≤ L` for `L ≥ 1`. -/
theorem xOf_le_self {L : ℕ} (hL : 1 ≤ L) : LocSumAct.xOf L ≤ (L : ℝ) := by
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  rw [LocSumAct.xOf]
  calc (L : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) ^ (1 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = (L : ℝ) := Real.rpow_one _

/-- `(L^{1/16})^16 = L`. -/
theorem xOf_pow_sixteen (L : ℕ) : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := by
  have h2 : (1 / 16 : ℝ) * ((16 : ℕ) : ℝ) = 1 := by norm_num
  rw [LocSumAct.xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 16,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (L : ℝ)), h2, Real.rpow_one]

/-! ## 2. `x^16 + 1` powers are dominated by the exponential -/

/-- **Polynomial versus exponential in the profile variable.**  For `b > 0`, any constant multiple
of `(x^16+1)^k` is eventually dominated by `M · exp (b x)`. -/
theorem exists_pow16_add_one_pow_le_exp {C M b : ℝ} (hC : 0 ≤ C) (hM : 0 < M) (hb : 0 < b)
    (k : ℕ) :
    ∃ X : ℝ, 0 ≤ X ∧ ∀ x : ℝ, X ≤ x → C * (x ^ 16 + 1) ^ k ≤ M * Real.exp (b * x) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · refine ⟨0, le_rfl, fun x _ => ?_⟩
    simp only [← hC0, zero_mul]
    exact mul_nonneg hM.le (Real.exp_pos _).le
  · have hε : 0 < M / (C * 2 ^ k) := by positivity
    have hf : (fun x : ℝ => x ^ (16 * k)) =o[atTop] fun x => Real.exp (b * x) :=
      isLittleO_pow_exp_pos_mul_atTop (16 * k) hb
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (hf.bound hε)
    refine ⟨max X₀ 1, le_trans zero_le_one (le_max_right _ _), fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
    have hX₀' : X₀ ≤ x := le_trans (le_max_left _ _) hx
    have hbound := hX₀ x hX₀'
    rw [norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0,
      abs_of_pos (Real.exp_pos _)] at hbound
    -- `(x^16+1)^k ≤ 2^k x^(16k)`
    have hx16 : 1 ≤ x ^ 16 := by
      calc (1 : ℝ) = 1 ^ 16 := by norm_num
        _ ≤ x ^ 16 := by exact pow_le_pow_left₀ zero_le_one hx1 16
    have hstep : x ^ 16 + 1 ≤ 2 * x ^ 16 := by linarith
    have hpow : (x ^ 16 + 1) ^ k ≤ 2 ^ k * x ^ (16 * k) := by
      calc (x ^ 16 + 1) ^ k ≤ (2 * x ^ 16) ^ k :=
            pow_le_pow_left₀ (by linarith) hstep k
        _ = 2 ^ k * x ^ (16 * k) := by rw [mul_pow, ← pow_mul]
    have hfinal : C * (2 ^ k * x ^ (16 * k)) ≤ M * Real.exp (b * x) := by
      have hCC : (0 : ℝ) < C * 2 ^ k := by positivity
      have : x ^ (16 * k) ≤ M / (C * 2 ^ k) * Real.exp (b * x) := by
        have := hbound
        rw [div_mul_eq_mul_div, le_div_iff₀ hCC] at this
        linarith
      calc C * (2 ^ k * x ^ (16 * k)) = C * 2 ^ k * x ^ (16 * k) := by ring
        _ ≤ C * 2 ^ k * (M / (C * 2 ^ k) * Real.exp (b * x)) := by
            exact mul_le_mul_of_nonneg_left this hCC.le
        _ = M * Real.exp (b * x) := by field_simp
    calc C * (x ^ 16 + 1) ^ k ≤ C * (2 ^ k * x ^ (16 * k)) :=
          mul_le_mul_of_nonneg_left hpow hC
      _ ≤ M * Real.exp (b * x) := hfinal

/-! ## 3. The absorption lemma in the `exf` shape -/

/-- **A polynomial prefactor is absorbed by slowing the profile rate.**  For `C₁ ≥ 0`, `0 < cT < c₀`
and any `k`, there are `M > 0` and `L₀` with

    C₁ · (L+1)^k · exf c₀ L ≤ M · exf cT L      for every L ≥ L₀.

The loss is exactly the halving of the gap `c₀ - cT`, which is the only price of killing the
polynomial factor; no probabilistic statement is involved. -/
theorem exists_poly_mul_exf_le {C₁ c₀ cT : ℝ} (hC₁ : 0 ≤ C₁) (hcT : 0 < cT) (hlt : cT < c₀)
    (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ C₁ ≤ M ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      C₁ * (((L : ℝ) + 1) ^ k) * LocalGoodAll.exf c₀ L ≤ M * LocalGoodAll.exf cT L := by
  set b : ℝ := (c₀ - cT) / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  obtain ⟨X, hX0, hX⟩ := exists_pow16_add_one_pow_le_exp hC₁ (M := max 1 C₁ + 1)
    (by positivity : (0:ℝ) < max 1 C₁ + 1) hb k
  refine ⟨max 1 C₁ + 1, by positivity, by linarith [le_max_right 1 C₁],
    ⌈X ^ 16⌉₊ + 1, fun L hL => ?_⟩
  -- `xOf L ≥ X`
  have hXnonneg : (0 : ℝ) ≤ X := hX0
  have hLbig : X ^ 16 ≤ (L : ℝ) := by
    have h1 : X ^ 16 ≤ ((⌈X ^ 16⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈X ^ 16⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : (⌈X ^ 16⌉₊ : ℕ) ≤ L := by omega
      exact_mod_cast this
    linarith
  have hxX : X ≤ LocSumAct.xOf L := by
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ X ^ 16) hLbig
      (by norm_num : (0:ℝ) ≤ 1 / 16)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ X),
      show ((16 : ℕ) : ℝ) * (1 / 16) = 1 by norm_num, Real.rpow_one] at h
  have hL1 : 1 ≤ L := by
    have : 1 ≤ ⌈X ^ 16⌉₊ + 1 := Nat.le_add_left 1 _
    omega
  have hLX : (L : ℝ) = (LocSumAct.xOf L) ^ 16 := (xOf_pow_sixteen L).symm
  have hpoly : C₁ * (((L : ℝ) + 1) ^ k)
      ≤ (max 1 C₁ + 1) * Real.exp (b * LocSumAct.xOf L) := by
    have h := hX (LocSumAct.xOf L) hxX
    rw [hLX]
    exact h
  -- `exf c₀ L = exp (-c₀ x)`, `exf cT L = exp (-cT x)`
  have hexp_pos : 0 < Real.exp (-cT * LocSumAct.xOf L) := Real.exp_pos _
  have hgoal : C₁ * (((L : ℝ) + 1) ^ k) * Real.exp (-c₀ * LocSumAct.xOf L)
      ≤ (max 1 C₁ + 1) * Real.exp (-cT * LocSumAct.xOf L) := by
    have e1 : C₁ * (((L : ℝ) + 1) ^ k) * Real.exp (-c₀ * LocSumAct.xOf L)
        ≤ (max 1 C₁ + 1) * Real.exp (b * LocSumAct.xOf L)
            * Real.exp (-c₀ * LocSumAct.xOf L) := by
      have := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-c₀ * LocSumAct.xOf L)).le
      linarith
    have e2 : Real.exp (b * LocSumAct.xOf L) * Real.exp (-c₀ * LocSumAct.xOf L)
        ≤ Real.exp (-cT * LocSumAct.xOf L) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hxnn : 0 ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
      have hbval : b = (c₀ - cT) / 2 := hbdef
      nlinarith
    have e3 : (max 1 C₁ + 1) * Real.exp (b * LocSumAct.xOf L)
          * Real.exp (-c₀ * LocSumAct.xOf L)
        ≤ (max 1 C₁ + 1) * Real.exp (-cT * LocSumAct.xOf L) := by
      have hpos : (0:ℝ) ≤ max 1 C₁ + 1 := by positivity
      calc (max 1 C₁ + 1) * Real.exp (b * LocSumAct.xOf L) * Real.exp (-c₀ * LocSumAct.xOf L)
          = (max 1 C₁ + 1) * (Real.exp (b * LocSumAct.xOf L)
              * Real.exp (-c₀ * LocSumAct.xOf L)) := by ring
        _ ≤ (max 1 C₁ + 1) * Real.exp (-cT * LocSumAct.xOf L) :=
            mul_le_mul_of_nonneg_left e2 hpos
    linarith
  simpa only [LocalGoodAll.exf] using hgoal

/-! ## 4. The two shapes used by the record-clock and finite-run terms -/

/-- **A pure exponential in `L` is dominated by the profile.**  For `1 ≤ L` and `0 < c' ≤ c`,
`exp (-c L) ≤ exf c' L`, because `L^{1/16} ≤ L`. -/
theorem exp_neg_mul_le_exf {c c' : ℝ} (hc' : 0 < c') (hle : c' ≤ c) {L : ℕ} (hL : 1 ≤ L) :
    Real.exp (-c * (L : ℝ)) ≤ LocalGoodAll.exf c' L := by
  have hxL : LocSumAct.xOf L ≤ (L : ℝ) := xOf_le_self hL
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  unfold LocalGoodAll.exf
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **`(1-q)^K` is dominated by the profile.**  If `q ∈ (0,1)` and `K ≥ c · xOf L` with `c > 0`,
then `(1-q)^K ≤ exf (-log (1-q) · c) L`: a *lower* bound on the run length is what turns the
geometric decay of the mark row into the paper's profile. -/
theorem pow_le_exf {q c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : 0 < c) {K : ℕ} {L : ℕ}
    (hK : c * LocSumAct.xOf L ≤ (K : ℝ)) :
    (1 - q) ^ K ≤ LocalGoodAll.exf (-(Real.log (1 - q)) * c) L := by
  have h1q : 0 < 1 - q := by linarith
  have hlog : Real.log (1 - q) < 0 := Real.log_neg h1q (by linarith)
  have hKexp : (1 - q) ^ K = Real.exp ((K : ℝ) * Real.log (1 - q)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1q]
  have hmain : (K : ℝ) * Real.log (1 - q)
      ≤ -(-(Real.log (1 - q)) * c) * LocSumAct.xOf L := by
    have hpos : (0 : ℝ) ≤ -Real.log (1 - q) := by linarith
    have hmul : c * LocSumAct.xOf L * (-Real.log (1 - q))
        ≤ (K : ℝ) * (-Real.log (1 - q)) := mul_le_mul_of_nonneg_right hK hpos
    nlinarith
  have hexp : Real.exp ((K : ℝ) * Real.log (1 - q))
      ≤ Real.exp (-(-(Real.log (1 - q)) * c) * LocSumAct.xOf L) :=
    Real.exp_le_exp.mpr hmain
  calc (1 - q) ^ K = Real.exp ((K : ℝ) * Real.log (1 - q)) := hKexp
    _ ≤ Real.exp (-(-(Real.log (1 - q)) * c) * LocSumAct.xOf L) := hexp
    _ = LocalGoodAll.exf (-(Real.log (1 - q)) * c) L := by
        unfold LocalGoodAll.exf
        ring_nf

end WindowAbsorb
