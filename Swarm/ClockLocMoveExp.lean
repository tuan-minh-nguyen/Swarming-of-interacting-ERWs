/-
# The `(locmove)` actual-clock clause in the paper's single exponential profile

`2 (K+1)^2 e^{-eps_1^2/(4K (2 stepEnv)^2)} + 2 (K+1)^2 e^{-eps_2^2/(4K (2B)^2)} + e_b`.

At the paper's scale `B = Bstar L`, `eps_1 = eps_2 = L^{3/4}` (`xOf L = L^{1/16}`) each deviation
term is `poly L * exp (-a (xOf L)^j)` with `j = 4` (resp. `j = 6`), and the `(loccoord)` error is
already `exp (-c xOf ((2T+4)L))`.  Using the accepted `LocalGood.absorb_rpow` this file
absorbs all three into **one** `C_T exp (-c_T xOf L)` term.  No new probabilistic input.
-/
import Swarm.ClockLocMove
import Swarm.LocalGoodAbsorb

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl

namespace ClockLocMove

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 7. Powers of `xOf` -/

theorem xOf_pow_nat (L n : ℕ) : (LocSumAct.xOf L) ^ n = (L : ℝ) ^ ((n : ℝ) / 16) := by
  have h0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1 : (LocSumAct.xOf L) ^ n = ((L : ℝ) ^ ((1 : ℝ) / 16)) ^ n := rfl
  rw [h1, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 16)) n, ← Real.rpow_mul h0]
  rw [show (1 : ℝ) / 16 * (n : ℝ) = (n : ℝ) / 16 by ring]

theorem xOf_pow_two {L : ℕ} : (LocSumAct.xOf L) ^ 2 = (L : ℝ) ^ ((1 : ℝ) / 8) := by
  rw [xOf_pow_nat L 2]
  norm_num

theorem xOf_pow_four {L : ℕ} : (LocSumAct.xOf L) ^ 4 = (L : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [xOf_pow_nat L 4]
  norm_num

theorem xOf_pow_sixteen {L : ℕ} : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := by
  have h : (((16 : ℕ)) : ℝ) / 16 = 1 := by norm_num
  rw [xOf_pow_nat L 16, h, Real.rpow_one]

/-- `(L^{3/4})^2 = (xOf L)^24`. -/
theorem rpow_three_quarters_sq {L : ℕ} :
    ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (LocSumAct.xOf L) ^ 24 := by
  have h0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1 : ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((L : ℝ) ^ ((3 : ℝ) / 4)) 2, ← Real.rpow_mul h0]
    norm_num
  have h2 : (LocSumAct.xOf L) ^ 24 = (L : ℝ) ^ ((24 : ℝ) / 16) := xOf_pow_nat L 24
  rw [h1, h2]
  norm_num

/-! ## 8. The two deviation exponents at `B = Bstar L`, `eps = L^{3/4}` -/

/-- `Gamma`-half exponent at the record scale: at least `(xOf L)^4 / (4 (T+3) (321N)^2)`. -/
theorem gamma_exp_at_Bstar {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {T L : ℕ} (hL : 1 ≤ L) :
    (1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2)) * (LocSumAct.xOf L) ^ 4
      ≤ (((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) *
            (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := le_trans zero_le_one hx1
  have hstep := RecClockLG.two_stepEnv_Bstar_le (N := N) hp0 hp1 hN hL
  have hstep' : 2 * stepEnv (N := N) p (RecClockLG.Bstar L)
      ≤ 321 * (N : ℝ) * (LocSumAct.xOf L) ^ 2 := by
    have h := hstep
    rw [← xOf_pow_two] at h
    exact h
  have hstep0 : 0 ≤ 2 * stepEnv (N := N) p (RecClockLG.Bstar L) := by
    have h := stepEnv_nonneg (N := N) hp0 hp1 (RecClockLG.Bstar_nonneg hL)
    linarith
  have hsq : (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
      ≤ (321 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L) ^ 4 := by
    have h1 : (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
        ≤ (321 * (N : ℝ) * (LocSumAct.xOf L) ^ 2) ^ 2 :=
      pow_le_pow_left₀ hstep0 hstep' 2
    calc (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2
        ≤ (321 * (N : ℝ) * (LocSumAct.xOf L) ^ 2) ^ 2 := h1
      _ = (321 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L) ^ 4 := by ring
  have hK : (((T + 3) * L : ℕ) : ℝ) = ((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16 := by
    push_cast
    rw [show ((L : ℝ)) = (LocSumAct.xOf L) ^ 16 from (xOf_pow_sixteen (L := L)).symm]
  have hK0 : (0 : ℝ) < (((T + 3) * L : ℕ) : ℝ) := by
    have h2 : 0 < (T + 3) * L := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h2
  have hDpos : 0 < 4 * (((T + 3) * L : ℕ) : ℝ)
      * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := by
    have hsp : 0 < stepEnv (N := N) p (RecClockLG.Bstar L) :=
      stepEnv_pos (N := N) hp0 hp1 (RecClockLG.Bstar_pos hL)
    have h2 : 0 < 2 * stepEnv (N := N) p (RecClockLG.Bstar L) := by linarith
    have h3 : (0 : ℝ) < (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2 := pow_pos h2 2
    have h4 : (0 : ℝ) < 4 * (((T + 3) * L : ℕ) : ℝ) := by linarith
    exact mul_pos h4 h3
  rw [le_div_iff₀ hDpos, rpow_three_quarters_sq, hK]
  have hprod : (1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2)) * (LocSumAct.xOf L) ^ 4
        * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
      ≤ (1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2)) * (LocSumAct.xOf L) ^ 4
          * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16)
            * ((321 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L) ^ 4)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have heq : (1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2)) * (LocSumAct.xOf L) ^ 4
        * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16)
          * ((321 * (N : ℝ)) ^ 2 * (LocSumAct.xOf L) ^ 4)) = (LocSumAct.xOf L) ^ 24 := by
    have hT3 : ((T : ℝ) + 3) ≠ 0 := by positivity
    have hN3 : (321 * (N : ℝ)) ≠ 0 := by positivity
    field_simp
  linarith [hprod, heq]

/-- Max-growth exponent at the record scale: at least `(xOf L)^6 / (1024 (T+3))`. -/
theorem maxgrowth_exp_at_Bstar {T L : ℕ} (hL : 1 ≤ L) :
    (1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6
      ≤ (((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2) := by
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := le_trans zero_le_one hx1
  have hB : RecClockLG.Bstar L ≤ 2 * LocSumAct.xOf L + 6 := by
    unfold RecClockLG.Bstar
    refine max_le ?_ ?_ <;> linarith
  have hB0 : (0 : ℝ) ≤ RecClockLG.Bstar L := RecClockLG.Bstar_nonneg hL
  have hsq : (2 * RecClockLG.Bstar L) ^ 2 ≤ 256 * (LocSumAct.xOf L) ^ 2 := by
    have h1 : (2 * RecClockLG.Bstar L) ^ 2 ≤ (16 * LocSumAct.xOf L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc (2 * RecClockLG.Bstar L) ^ 2 ≤ (16 * LocSumAct.xOf L) ^ 2 := h1
      _ = 256 * (LocSumAct.xOf L) ^ 2 := by ring
  have hK : (((T + 3) * L : ℕ) : ℝ) = ((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16 := by
    push_cast
    rw [show ((L : ℝ)) = (LocSumAct.xOf L) ^ 16 from (xOf_pow_sixteen (L := L)).symm]
  have hK0 : (0 : ℝ) < (((T + 3) * L : ℕ) : ℝ) := by
    have h2 : 0 < (T + 3) * L := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h2
  have hDpos : 0 < 4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2 := by
    have h3 : (0 : ℝ) < (2 * RecClockLG.Bstar L) ^ 2 := by
      have h4 : 0 < 2 * RecClockLG.Bstar L := by linarith [RecClockLG.Bstar_pos hL]
      exact pow_pos h4 2
    have h4' : (0 : ℝ) < 4 * (((T + 3) * L : ℕ) : ℝ) := by linarith
    exact mul_pos h4' h3
  rw [le_div_iff₀ hDpos, rpow_three_quarters_sq, hK]
  have hprod : (1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6
        * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16) * (2 * RecClockLG.Bstar L) ^ 2)
      ≤ (1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6
          * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16)
            * (256 * (LocSumAct.xOf L) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have heq : (1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6
        * (4 * (((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16)
          * (256 * (LocSumAct.xOf L) ^ 2)) = (LocSumAct.xOf L) ^ 24 := by
    have hT3 : ((T : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    norm_num
  linarith [hprod, heq]

/-! ## 9. The single-exponential profile `C_T exp (-c_T xOf L)` -/

/-- **The `(locmove)` actual-clock failure in the paper's own profile.**

There is a rate `lam > 0`, independent of `T` and `L`, such that for every `T` there are `CT > 0`
and `L₀` with: for `L ≥ L₀`, `(3T+6)L ≤ r`, `B = Bstar L` and `eps_1 = eps_2 = L^{3/4}`,

```
mu.real {U | locMoveFailAtClock ... (Bstar L) ((2C_0+1)/2) (betaT ...) (L^{3/4}) (L^{3/4})
              (locCoordGeom ...) U}
  <= CT * exp (-lam * xOf L).
```

This collects the three terms of `exists_measureReal_locMoveFailAtClock_le` — the two
clock-anchored deviation bounds (absorbed through `LocalGood.absorb_rpow`, exponents
`(xOf L)^4` and `(xOf L)^6`, polynomial prefactors of degree `2` in `L`) and the `(loccoord)` error
`exp (-c xOf ((2T+4)L))` — into one term.  The probabilistic content is entirely in
`ClockLocMove.lean`; this is the arithmetic step only. -/
theorem exists_measureReal_locMoveFailAtClock_paper {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) (hN : 1 ≤ N) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀)
    (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ T : ℕ, ∃ CT : ℝ, 0 < CT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ max L₀ 2, ∀ r : ℕ, (3 * T + 6) * L ≤ r →
      (arrayMeasure N).real
          {U : Array N |
            locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L) ((2 * C₀ + 1) / 2)
              ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
              (locCoordGeom p m A hA r T L) U}
        ≤ CT * Real.exp (-(lam * LocSumAct.xOf L)) := by
  obtain ⟨c, hc, L₀, hLc⟩ :=
    exists_measureReal_locMoveFailAtClock_le (N := N) hp0 hp1 hm A hA hAc hC₀1 hC₀M hγC
  refine ⟨c / 2, by linarith, ?_⟩
  intro T
  -- the two absorption constants at this `T`
  have hT3 : (0 : ℝ) < (T : ℝ) + 3 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h321 : (0 : ℝ) < 321 * (N : ℝ) := by linarith
  have ha₁ : (0 : ℝ) < 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2) := by positivity
  have ha₂ : (0 : ℝ) < 1 / (1024 * ((T : ℝ) + 3)) := by positivity
  have hcT : (0 : ℝ) < c / 2 := by linarith
  obtain ⟨C₁, hC₁0, L₁, hL₁⟩ :=
    LocalGood.absorb_rpow (a := 1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
      (c_T := c / 2) ha₁ hcT (j := 4) (k := 2) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂0, L₂, hL₂⟩ :=
    LocalGood.absorb_rpow (a := 1 / (1024 * ((T : ℝ) + 3)))
      (c_T := c / 2) ha₂ hcT (j := 6) (k := 2) (by norm_num) (by norm_num)
  refine ⟨2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂ + 1, by positivity,
    max (max L₀ L₁) L₂, ?_⟩
  intro L hLbig r hr
  have hinner : max (max L₀ L₁) L₂ ≤ L :=
    le_trans (le_max_left (max (max L₀ L₁) L₂) 2) hLbig
  have hL0 : L₀ ≤ L := le_trans (le_max_left L₀ L₁) (le_trans (le_max_left (max L₀ L₁) L₂) hinner)
  have hL1 : L₁ ≤ L := le_trans (le_max_right L₀ L₁) (le_trans (le_max_left (max L₀ L₁) L₂) hinner)
  have hL2 : L₂ ≤ L := le_trans (le_max_right (max L₀ L₁) L₂) hinner
  have hL2' : 2 ≤ L := le_trans (le_max_right (max (max L₀ L₁) L₂) 2) hLbig
  have hL1' : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1'
  have hL0r : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1'
  have hx0 : (0 : ℝ) ≤ LocSumAct.xOf L := le_trans zero_le_one hx1
  have hε : (0 : ℝ) < (L : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hBpos : 0 < RecClockLG.Bstar L := RecClockLG.Bstar_pos hL1'
  have hLbig0 : max L₀ 2 ≤ L := max_le hL0 hL2'
  have hprev := hLc L hLbig0 T r hr (B := RecClockLG.Bstar L)
    (ε₁ := (L : ℝ) ^ ((3 : ℝ) / 4)) (ε₂ := (L : ℝ) ^ ((3 : ℝ) / 4)) hBpos hε hε
  -- the three termwise bounds
  have hK2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by
    have h1 : ((((T + 3) * L : ℕ) : ℝ) + 1) ≤ ((T : ℝ) + 4) * (L : ℝ) := by
      push_cast
      nlinarith [hLr, Nat.cast_nonneg (α := ℝ) T]
    have h2 : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 4) * (L : ℝ)) ^ 2 := h2
      _ = ((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hexp₁ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ)
          * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
          * (LocSumAct.xOf L) ^ 4)) := by
    apply Real.exp_le_exp.mpr
    have h := gamma_exp_at_Bstar (N := N) (T := T) (L := L) hp0 hp1.le hN hL1'
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2)) from by rw [neg_div]]
    linarith
  have hexp₂ : Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
        (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
    apply Real.exp_le_exp.mpr
    have h := maxgrowth_exp_at_Bstar (T := T) (L := L) hL1'
    rw [show -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)
        = -((((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2)) from by rw [neg_div]]
    linarith
  have hT1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := by
      refine mul_le_mul ?_ hexp₁ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ)
              * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
              * (LocSumAct.xOf L) ^ 4))) := by ring
  have hT2 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6))) := by
    have h1 : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := by
      refine mul_le_mul ?_ hexp₂ (Real.exp_pos _).le (by positivity)
      linarith [hK2]
    calc 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
            (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
        ≤ 2 * (((T : ℝ) + 4) ^ 2 * (L : ℝ) ^ 2) *
            Real.exp (-((1 / (1024 * ((T : ℝ) + 3))) * (LocSumAct.xOf L) ^ 6)) := h1
      _ = 2 * ((T : ℝ) + 4) ^ 2 *
            ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
              * (LocSumAct.xOf L) ^ 6))) := by ring
  have hT3 : Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
      ≤ Real.exp (-((c / 2) * LocSumAct.xOf L)) := by
    apply Real.exp_le_exp.mpr
    have hmono : (L : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) T, hL0r]
    have hxmono : LocSumAct.xOf L ≤ LocSumAct.xOf ((2 * T + 4) * L) := by
      unfold LocSumAct.xOf
      exact Real.rpow_le_rpow (by positivity) hmono (by norm_num)
    nlinarith
  -- assemble
  have hsum : 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ)
            * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
      + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
          (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
      + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
      ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + Real.exp (-((c / 2) * LocSumAct.xOf L)) := by
    have h1' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (4 * ((T : ℝ) + 3) * (321 * (N : ℝ)) ^ 2))
            * (LocSumAct.xOf L) ^ 4)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))) := by
      exact mul_le_mul_of_nonneg_left (hL₁ L hL1) (by positivity)
    have h2' : 2 * ((T : ℝ) + 4) ^ 2 *
          ((L : ℝ) ^ 2 * Real.exp (-((1 / (1024 * ((T : ℝ) + 3)))
            * (LocSumAct.xOf L) ^ 6)))
        ≤ 2 * ((T : ℝ) + 4) ^ 2 * (C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))) := by
      exact mul_le_mul_of_nonneg_left (hL₂ L hL2) (by positivity)
    have e1 : 2 * ((T : ℝ) + 4) ^ 2 * (C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L)))
        = 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
    have e2 : 2 * ((T : ℝ) + 4) ^ 2 * (C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L)))
        = 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
    linarith [hT1, hT2, hT3, h1', h2', e1, e2]
  have hfinal : 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
        + Real.exp (-((c / 2) * LocSumAct.xOf L))
      = (2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂ + 1)
        * Real.exp (-((c / 2) * LocSumAct.xOf L)) := by ring
  calc (arrayMeasure N).real
        {U : Array N |
          locMoveFailAtClock p m A hA hAc r T L (RecClockLG.Bstar L) ((2 * C₀ + 1) / 2)
            ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4))
            (locCoordGeom p m A hA r T L) U}
      ≤ 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ)
                * (2 * stepEnv (N := N) p (RecClockLG.Bstar L)) ^ 2))
          + 2 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) /
              (4 * (((T + 3) * L : ℕ) : ℝ) * (2 * RecClockLG.Bstar L) ^ 2))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := hprev
    _ ≤ 2 * ((T : ℝ) + 4) ^ 2 * C₁ * Real.exp (-((c / 2) * LocSumAct.xOf L))
          + 2 * ((T : ℝ) + 4) ^ 2 * C₂ * Real.exp (-((c / 2) * LocSumAct.xOf L))
          + Real.exp (-((c / 2) * LocSumAct.xOf L)) := hsum
    _ = (2 * ((T : ℝ) + 4) ^ 2 * C₁ + 2 * ((T : ℝ) + 4) ^ 2 * C₂ + 1)
          * Real.exp (-((c / 2) * LocSumAct.xOf L)) := hfinal

end ClockLocMove
