/-
# One measured local-good event at the record window `(T+3)L`

This module assembles the four public components of Proposition `local` that are index-compatible at
the record window into **one** measured event `LocalBad`, and proves the single subexponential bound
`C_T exp(-c_T L^{1/16})` for it:

* `LsBad N p m CU ((2T+4)L) (r-(T+2)L)` — the single `(locsum)` carrier of both `(loccoord)`
  (`loccoord_CU_explicit`) and `(locmove)` (`exists_measure_locmove_T3`, at the paper's
  `(T+3)L ≤ r`);
* `LocMaxBad` — the `(locmax)` event of the record window;
* the a.e.-null failure of `BddAbove Gtrunc` (the potential-convergence support);
* the all-pair clock-fibre union `⋃ s0 band s0 ∩ GoodWinAllPairs(s0)ᶜ` — the `(lococc)` event,
  kept in its raw `ReachAll`-restricted fibre form (it is *not* identified with `{d_r ≤ L}` off
  `ReachAll`);
* `lgFail` — the `(locgroup)` window-deviation failure at the (deterministic) clock `n0`;
* `lmFail` — the `(locmove)` display failure at the (deterministic) clock `n0` and window `[s,t)`.

The complementary good statement is `localGood_off_localBad`: off `LocalBad`, *all four* component
conclusions hold simultaneously (see the exact labelled carriers there — in particular `(sep)` on
`[s,t)`, `RecHyp`, `locmoveGood` and the range facts are **carriers**, not conclusions).

## What is deliberately NOT claimed

* No `(sep)` survival: `lgFail`/`lmFail` contain `(sep)` on `[s,t)` as a *carrier*, so off
  `LocalBad` the conclusions are statements about windows on which `(sep)` is *assumed* to hold.
* No potential convergence support beyond the a.e. `BddAbove` (which is proved, so it costs 0).
* No event positivity, no invariant measure, no stationarity/regeneration, no `MainClaim`.
* **The random-clock step is not done.**  The paper's `(locgroup)`/`(locmove)` are displayed for
  the *record clock* `τ_r` (`n0 = τ_r(U)`), whereas `lgFail`/`lmFail` are indexed by a
  *deterministic* `n0`.  `random_clock_obstruction` below records precisely why the fixed-`n0`
  bound does not give the `τ_r`-version by union over `n0`: the record-debt carriers
  `band s0` are disjoint in `s0` (which is exactly what makes the `(lococc)` summation count-free)
  but `lgFail`/`lmFail` carry no such disjoint carrier, so `⋃_{n0}` costs one factor per clock.
-/
import Swarm.LocalGoodCore

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocalGood

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. Absorption arithmetic: polynomial prefactors against `exp(-c L^{1/16})` -/

/-- `u e^{-cu} ≤ 1/(e c)` (the elementary maximum of `u ↦ u e^{-cu}`). -/
theorem mul_exp_neg_le_aux (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 ≤ u) :
    u * Real.exp (-(c * u)) ≤ 1 / (Real.exp 1 * c) := by
  have hden : (0 : ℝ) < Real.exp 1 * c := by positivity
  rw [le_div_iff₀ hden]
  have h1 : Real.exp 1 * (c * u) ≤ Real.exp (c * u) := by
    have h := Real.add_one_le_exp (c * u - 1)
    have h2 : Real.exp 1 * Real.exp (c * u - 1) = Real.exp (c * u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h4 : (0 : ℝ) < Real.exp (c * u - 1) := Real.exp_pos _
    nlinarith [h, h2, h3, h4]
  have h2 : Real.exp 1 * (c * u) * Real.exp (-(c * u)) ≤
      Real.exp (c * u) * Real.exp (-(c * u)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h4 : u * Real.exp (-(c * u)) * (Real.exp 1 * c) =
      Real.exp 1 * (c * u) * Real.exp (-(c * u)) := by ring
  rw [h4]
  linarith [h2, h3.le, h3.ge]

/-- `u^k e^{-εu} ≤ (k/(e ε))^k`: the general elementary maximum. -/
theorem pow_mul_exp_neg_le_aux {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) (u : ℝ)
    (hu : 0 ≤ u) : u ^ k * Real.exp (-(ε * u)) ≤ ((k : ℝ) / (Real.exp 1 * ε)) ^ k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hεk : 0 < ε / (k : ℝ) := by positivity
  have h1 : u * Real.exp (-(ε / (k : ℝ) * u)) ≤ 1 / (Real.exp 1 * (ε / (k : ℝ))) :=
    mul_exp_neg_le_aux (ε / (k : ℝ)) hεk u hu
  have hnn : 0 ≤ u * Real.exp (-(ε / (k : ℝ) * u)) := mul_nonneg hu (Real.exp_pos _).le
  have h2 := pow_le_pow_left₀ hnn h1 k
  have hexp : Real.exp (-(ε / (k : ℝ) * u)) ^ k = Real.exp (-(ε * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hl : (u * Real.exp (-(ε / (k : ℝ) * u))) ^ k = u ^ k * Real.exp (-(ε * u)) := by
    rw [mul_pow, hexp]
  have hr : (1 / (Real.exp 1 * (ε / (k : ℝ)))) ^ k = ((k : ℝ) / (Real.exp 1 * ε)) ^ k := by
    congr 1
    field_simp
  rwa [hl, hr] at h2

/-- `L^k = (xOf L)^{16k}`. -/
theorem natCast_pow_eq_xOf_pow (L : ℕ) (k : ℕ) :
    (L : ℝ) ^ k = (LocSumAct.xOf L) ^ (16 * k) := by
  have h1 : ((1 : ℝ) / 16) * ((16 * k : ℕ) : ℝ) = (k : ℝ) := by push_cast; ring
  calc (L : ℝ) ^ k = (L : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast _ _).symm
    _ = (L : ℝ) ^ (((1 : ℝ) / 16) * ((16 * k : ℕ) : ℝ)) := by rw [h1]
    _ = ((L : ℝ) ^ ((1 : ℝ) / 16)) ^ ((16 * k : ℕ) : ℝ) :=
        Real.rpow_mul (Nat.cast_nonneg L) _ _
    _ = ((L : ℝ) ^ ((1 : ℝ) / 16)) ^ (16 * k) := by rw [Real.rpow_natCast]

/-- **Polynomial decay against `exp(-c L^{1/16})`**: `L^k e^{-c xOf L}` is bounded. -/
theorem poly_mul_exp_xOf_le {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) ^ k * Real.exp (-(c * LocSumAct.xOf L))
      ≤ (((16 * k : ℕ) : ℝ) / (Real.exp 1 * c)) ^ (16 * k) := by
  have hu0 : (0 : ℝ) ≤ LocSumAct.xOf L := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hk16 : 1 ≤ 16 * k := by omega
  rw [natCast_pow_eq_xOf_pow]
  exact pow_mul_exp_neg_le_aux hc hk16 _ hu0

/-- **The general absorption.**  For `a > 0`, a final rate `c_T > 0` and a power `j ≥ 2` of
`xOf L`, every `(L)^k e^{-a (xOf L)^j}` is eventually bounded by `C e^{-c_T xOf L}`.  This is the
single arithmetic step that lets the polynomial prefactors `t-s+1 ≤ (T+3)L+1` of `(locmove)` and
the faster (`L^{1/4}`, `L^{3/8}`) exponents be absorbed into the target profile. -/
theorem absorb_rpow {a c_T : ℝ} (ha : 0 < a) (hcT : 0 < c_T) {j k : ℕ} (hj : 2 ≤ j) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (L : ℝ) ^ k * Real.exp (-(a * (LocSumAct.xOf L) ^ j))
        ≤ C * Real.exp (-(c_T * LocSumAct.xOf L)) := by
  -- threshold: `2 c_T ≤ a (xOf L)^{j-1}`
  have hthr : ∃ L₀ : ℕ, ∀ L ≥ L₀, 2 * c_T / a ≤ LocSumAct.xOf L := by
    have h := LocSumAct.xOf_tendsto.eventually (eventually_ge_atTop (max 0 (2 * c_T / a)))
    rw [eventually_atTop] at h
    obtain ⟨L₀, hL₀⟩ := h
    exact ⟨L₀, fun L hL => le_trans (le_max_right _ _) (hL₀ L hL)⟩
  obtain ⟨L₀, hL₀⟩ := hthr
  refine ⟨(((16 * k : ℕ) : ℝ) / (Real.exp 1 * c_T)) ^ (16 * k), by positivity, max L₀ 1, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hu0 : (0 : ℝ) ≤ LocSumAct.xOf L := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hxle : 2 * c_T / a ≤ LocSumAct.xOf L := hL₀ L (le_trans (le_max_left _ _) hL)
  have hx1 : 1 ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1
  -- `2 c_T xOf L ≤ a (xOf L)^j`
  have hcmp : 2 * c_T * LocSumAct.xOf L ≤ a * (LocSumAct.xOf L) ^ j := by
    have h1 : 2 * c_T ≤ a * LocSumAct.xOf L := by
      have : a * (2 * c_T / a) = 2 * c_T := by field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_left hxle ha.le
    have h2 : (LocSumAct.xOf L) ^ 2 ≤ (LocSumAct.xOf L) ^ j :=
      pow_le_pow_right₀ hx1 hj
    have h4 : a * (LocSumAct.xOf L) ^ 2 ≤ a * (LocSumAct.xOf L) ^ j :=
      mul_le_mul_of_nonneg_left h2 ha.le
    calc 2 * c_T * LocSumAct.xOf L ≤ a * LocSumAct.xOf L * LocSumAct.xOf L := by
          nlinarith [h1, hu0]
      _ = a * (LocSumAct.xOf L) ^ 2 := by ring
      _ ≤ a * (LocSumAct.xOf L) ^ j := h4
  have hexp : Real.exp (-(a * (LocSumAct.xOf L) ^ j))
      ≤ Real.exp (-(2 * c_T * LocSumAct.xOf L)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpoly := poly_mul_exp_xOf_le (c := c_T) hcT hk hL1
  have hsplit : (L : ℝ) ^ k * Real.exp (-(2 * c_T * LocSumAct.xOf L))
      = ((L : ℝ) ^ k * Real.exp (-(c_T * LocSumAct.xOf L)))
        * Real.exp (-(c_T * LocSumAct.xOf L)) := by
    have h2e : Real.exp (-(2 * c_T * LocSumAct.xOf L))
        = Real.exp (-(c_T * LocSumAct.xOf L)) ^ 2 := by
      have hh : -(2 * c_T * LocSumAct.xOf L)
          = (2 : ℕ) * (-(c_T * LocSumAct.xOf L)) := by push_cast; ring
      rw [hh, Real.exp_nat_mul]
    rw [h2e]
    ring
  calc (L : ℝ) ^ k * Real.exp (-(a * (LocSumAct.xOf L) ^ j))
      ≤ (L : ℝ) ^ k * Real.exp (-(2 * c_T * LocSumAct.xOf L)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = ((L : ℝ) ^ k * Real.exp (-(c_T * LocSumAct.xOf L)))
        * Real.exp (-(c_T * LocSumAct.xOf L)) := hsplit
    _ ≤ (((16 * k : ℕ) : ℝ) / (Real.exp 1 * c_T)) ^ (16 * k)
        * Real.exp (-(c_T * LocSumAct.xOf L)) := by
        exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le

end LocalGood
