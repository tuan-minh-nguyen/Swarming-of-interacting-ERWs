/-
Paper-scale instantiation of the composed `(locmove)` estimate.

`LocMoveLocal.measure_max_abs_Lcum_paper_scale` does this for the max-growth half alone.  Here both
halves are instantiated at `B = L^(1/16)`, `ε₁ = ε₂ = L^(3/4)`, on a window of length at least `L`.
-/
import Swarm.LocMoveCompose
import Swarm.LocMoveLocalScale

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveCompose

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 6. Arithmetic at the paper's local scale -/

/-- `(L^(1/16))^n = L^(n/16)`. -/
theorem xOf_pow_eq (L n : ℕ) : (LocSumAct.xOf L) ^ n = (L : ℝ) ^ ((n : ℝ) / 16) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [LocSumAct.xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) n, ← Real.rpow_mul hL]
  congr 1
  ring

/-- `(xOf L)^16 = L`. -/
theorem xOf_pow_sixteen (L : ℕ) : (LocSumAct.xOf L) ^ 16 = (L : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  rw [LocSumAct.xOf, ← Real.rpow_natCast ((L : ℝ) ^ (1 / 16 : ℝ)) 16, ← Real.rpow_mul hL]
  norm_num

/-- `2 · stepEnv p B ≤ 20 N B²` for `B ≥ 1`, `N ≥ 1`. -/
theorem two_mul_stepEnv_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {B : ℝ} (hB : 1 ≤ B)
    (hN : 1 ≤ N) :
    2 * stepEnv (N := N) p B ≤ 20 * ((N : ℝ) * B ^ 2) := by
  have hB0 : (0 : ℝ) < B := by linarith
  have hNB : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hX : (0 : ℝ) ≤ (1 + B) * B := by positivity
  have hc : (2 * p - 1) / p ≤ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < p)]
    linarith
  have hcN : ((2 * p - 1) / p) * ((N : ℝ) * ((1 + B) * B)) ≤ 2 * ((N : ℝ) * ((1 + B) * B)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have hstep : stepEnv (N := N) p B ≤ 2 * B + 4 * ((N : ℝ) * ((1 + B) * B)) := by
    rw [stepEnv_eq]
    nlinarith [hcN]
  have hNB1 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have h1 : (N : ℝ) * ((1 + B) * B) ≤ 2 * ((N : ℝ) * B ^ 2) := by
    have h2 : (1 + B) * B ≤ 2 * B ^ 2 := by nlinarith
    calc (N : ℝ) * ((1 + B) * B) ≤ (N : ℝ) * (2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hNB1
      _ = 2 * ((N : ℝ) * B ^ 2) := by ring
  have hstep' : stepEnv (N := N) p B ≤ 2 * B + 8 * ((N : ℝ) * B ^ 2) := by nlinarith [hstep, h1]
  have hb : 2 * B ≤ 2 * ((N : ℝ) * B ^ 2) := by nlinarith
  nlinarith [hstep', hb]

/-- `(L^(3/4))² = (xOf L)^24`. -/
theorem rpow_three_quarters_sq (L : ℕ) :
    ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (LocSumAct.xOf L) ^ 24 := by
  rw [sq, ← LocMoveLocal.xOf_pow_twelve L, ← pow_add]

/-- `xOf L ≠ 0`. -/
theorem xOf_ne_zero {L : ℕ} (hL : 1 ≤ L) : LocSumAct.xOf L ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (LocSumAct.one_le_xOf hL))

/-- `K ≤ (T+3)L` gives `K ≤ (T+3) (xOf L)^16`. -/
theorem K_le_T3_xOf {L K T : ℕ} (hKle : K ≤ (T + 3) * L) :
    (K : ℝ) ≤ ((T : ℝ) + 3) * (LocSumAct.xOf L) ^ 16 := by
  have h2 : (K : ℝ) ≤ (((T + 3) * L : ℕ) : ℝ) := by exact_mod_cast hKle
  have h3 : (((T + 3) * L : ℕ) : ℝ) = ((T : ℝ) + 3) * (L : ℝ) := by push_cast; ring
  rw [h3, ← xOf_pow_sixteen L] at h2
  exact h2

/-- **The `Γ`-half exponent at the paper's scale.**  With `B = xOf L`, `ε₁ = L^(3/4)` and
`K ≤ (T+3)L`, the maximal-deviation exponent of the `GoodW` martingale is at most
`−(xOf L)^4 / (1600 N² (T+3))` in size. -/
theorem gamma_exponent_le {L K T : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K) (hKle : K ≤ (T + 3) * L)
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) (hN : 1 ≤ N) :
    -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)
      ≤ -((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))) := by
  set x : ℝ := LocSumAct.xOf L with hxdef
  have hx1 : (1 : ℝ) ≤ x := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) < x := by linarith
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hT3 : (0 : ℝ) < (T : ℝ) + 3 := by positivity
  have hN0 : (0 : ℝ) < ((N : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    positivity
  have henv := two_mul_stepEnv_le (N := N) hp0 hp1 (B := x) hx1 hN
  have henv0 : (0 : ℝ) < 2 * stepEnv (N := N) p x := by
    have := stepEnv_pos (N := N) hp0 hp1 hx0
    linarith
  have hsqu : (2 * stepEnv (N := N) p x) ^ 2 ≤ 400 * ((N : ℝ) ^ 2 * x ^ 4) := by
    have h2 : (2 * stepEnv (N := N) p x) ^ 2 ≤ (20 * ((N : ℝ) * x ^ 2)) ^ 2 := by nlinarith
    calc (2 * stepEnv (N := N) p x) ^ 2 ≤ (20 * ((N : ℝ) * x ^ 2)) ^ 2 := h2
      _ = 400 * ((N : ℝ) ^ 2 * x ^ 4) := by ring
  have hden1 : (0 : ℝ) < 4 * (K : ℝ) * (2 * stepEnv (N := N) p x) ^ 2 := by positivity
  have hle : 4 * (K : ℝ) * (2 * stepEnv (N := N) p x) ^ 2
      ≤ 4 * (K : ℝ) * (400 * ((N : ℝ) ^ 2 * x ^ 4)) := by nlinarith [hsqu, hK0]
  have hnum : (0 : ℝ) ≤ ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := by positivity
  have hstep1 : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (4 * (K : ℝ) * (400 * ((N : ℝ) ^ 2 * x ^ 4)))
      ≤ ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (4 * (K : ℝ) * (2 * stepEnv (N := N) p x) ^ 2) :=
    div_le_div_of_nonneg_left hnum hden1 hle
  have hpow24 : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = x ^ 24 := by
    rw [hxdef]; exact rpow_three_quarters_sq L
  have hLHS : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (4 * (K : ℝ) * (400 * ((N : ℝ) ^ 2 * x ^ 4)))
      = x ^ 20 / (1600 * ((N : ℝ) ^ 2 * (K : ℝ))) := by
    rw [hpow24]
    have hxn : x ≠ 0 := ne_of_gt hx0
    field_simp
    ring
  have hKle' : (K : ℝ) ≤ ((T : ℝ) + 3) * x ^ 16 := by
    rw [hxdef]; exact K_le_T3_xOf hKle
  have hstep2 : x ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))
      ≤ x ^ 20 / (1600 * ((N : ℝ) ^ 2 * (K : ℝ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1600 * ((N : ℝ) ^ 2 * (K : ℝ))
        ≤ 1600 * ((N : ℝ) ^ 2 * (((T : ℝ) + 3) * x ^ 16)) := by nlinarith [hKle', hN0]
    calc x ^ 4 * (1600 * ((N : ℝ) ^ 2 * (K : ℝ)))
        ≤ x ^ 4 * (1600 * ((N : ℝ) ^ 2 * (((T : ℝ) + 3) * x ^ 16))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = x ^ 20 * (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))) := by ring
  have e1 : -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (2 * stepEnv (N := N) p x) ^ 2)
      = -((((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (2 * stepEnv (N := N) p x) ^ 2)) := by rw [neg_div]
  have e2 : -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (400 * ((N : ℝ) ^ 2 * x ^ 4)))
      = -((((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (K : ℝ) * (400 * ((N : ℝ) ^ 2 * x ^ 4)))) := by rw [neg_div]
  linarith [e1, e2, hstep1, hLHS, hstep2]

/-- **The max-growth exponent at the paper's scale.**  With `B = xOf L`, `ε₂ = L^(3/4)` and
`K ≤ (T+3)L`, the maximal-deviation exponent of the truncated maximum martingale is at most
`−(xOf L)^6 / (16 (T+3))` in size. -/
theorem maxgrowth_exponent_le {L K T : ℕ} (hL : 1 ≤ L) (hK : 1 ≤ K) (hKle : K ≤ (T + 3) * L) :
    -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (4 * (K : ℝ) * (2 * LocSumAct.xOf L) ^ 2)
      ≤ -((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3))) := by
  set x : ℝ := LocSumAct.xOf L with hxdef
  have hx1 : (1 : ℝ) ≤ x := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) < x := by linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hKle' : (K : ℝ) ≤ ((T : ℝ) + 3) * x ^ 16 := by
    rw [hxdef]; exact K_le_T3_xOf hKle
  have hpow24 : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = x ^ 24 := by
    rw [hxdef]; exact rpow_three_quarters_sq L
  have hLHS : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (4 * (K : ℝ) * (2 * x) ^ 2)
      = x ^ 22 / (16 * (K : ℝ)) := by
    rw [hpow24]
    have hxn : x ≠ 0 := ne_of_gt hx0
    field_simp
    ring
  have hstep : x ^ 6 / (16 * ((T : ℝ) + 3)) ≤ x ^ 22 / (16 * (K : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 16 * (K : ℝ) ≤ 16 * (((T : ℝ) + 3) * x ^ 16) := by nlinarith [hKle']
    calc x ^ 6 * (16 * (K : ℝ)) ≤ x ^ 6 * (16 * (((T : ℝ) + 3) * x ^ 16)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = x ^ 22 * (16 * ((T : ℝ) + 3)) := by ring
  have e1 : -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (4 * (K : ℝ) * (2 * x) ^ 2)
      = -((((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (4 * (K : ℝ) * (2 * x) ^ 2)) := by rw [neg_div]
  linarith [e1, hLHS, hstep]

/-- `L ≤ K` makes the Chernoff side condition automatic at the local scale. -/
theorem side_conditions {L K : ℕ} (hL : 1 ≤ L) (hK : L ≤ K)
    {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) :
    (L : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * ((K : ℝ) * stepEnv (N := N) p (LocSumAct.xOf L))
      ∧ (L : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * ((K : ℝ) * LocSumAct.xOf L) := by
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL
  have hx0 : (0 : ℝ) < LocSumAct.xOf L := by linarith
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hKge : (L : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hpow : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) := by
    calc (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLr (by norm_num)
      _ = (L : ℝ) := Real.rpow_one _
  have hstep0 : (2 : ℝ) * LocSumAct.xOf L ≤ stepEnv (N := N) p (LocSumAct.xOf L) := by
    have hc : (0 : ℝ) ≤ (2 * p - 1) / p := div_nonneg (by linarith) (by linarith)
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hX : (0 : ℝ) ≤ (1 + LocSumAct.xOf L) * LocSumAct.xOf L := by positivity
    have hprod : (0 : ℝ) ≤ ((2 * p - 1) / p) *
        ((N : ℝ) * ((1 + LocSumAct.xOf L) * LocSumAct.xOf L)) :=
      mul_nonneg hc (mul_nonneg hN0 hX)
    rw [stepEnv_eq]
    nlinarith [hprod]
  refine ⟨?_, ?_⟩
  · rw [← mul_assoc]
    nlinarith [hstep0]
  · nlinarith

/-- **Display `(locmove)` at the paper's local scale.**  `B = L^(1/16)`, `ε₁ = ε₂ = L^(3/4)`, and
window length at least `L`.  The two martingale terms become

`2(t-s+1) e^{-(xOf L)^6/(16(T+3))}` and `2(t-s+1) e^{-(xOf L)^4/(1600 N²(T+3))}`,

i.e. `C_T e^{-c_T L^{1/16}}` with `c_T = 1/(1600 N² (T+3))` at worst, plus the `(locsum)` term
`e^{-c L^{1/16}}`.  Apart from the exponent's `T+3` this is the paper's own `C_T, c_T` dependence.

Restriction, stated exactly: the Chernoff side condition `ε ≤ 4(t-s)B` at `ε = L^{3/4}` needs
`L ≲ t-s`, so the statement is for `L ≤ t-s` (the paper's `C_T L^{3/4}` slack covers the short
windows by the deterministic one-step envelope, which is not composed here). -/
theorem exists_measure_locmove_paper_scale {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hN : 1 ≤ N) {C₀ : ℝ} (hC₀1 : 1 ≤ C₀) (hC₀M : LocSum.Mb p (LocSumAct.qOf p m) < C₀)
    (hγC : 1 ≤ gammaRate p m A * ((2 * C₀ + 1) / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      ∀ {n0 s t : ℕ} (_hn0 : n0 ≤ s) (_hst : s ≤ t) (_hhor : t ≤ n0 + (T + 3) * L)
        (_hr : (T + 3) * L ≤ r) (_hK : L ≤ t - s),
      (arrayMeasure N).real
        {U : Array N |
          locmoveGood (N := N) p m A hA (r : ℤ) T L (LocSumAct.xOf L) n0 s t U ∧
            (0 ≤ Xmin p m U A hA s ∧
              r - (T + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
              (Rmax p m U A hA t).toNat ≤ r + (T + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ locmoveRHS (N := N) p m A hA L ((2 * C₀ + 1) / 2)
                    ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
                    ((L : ℝ) ^ (3 / 4 : ℝ)) ((L : ℝ) ^ (3 / 4 : ℝ)) s t U)}
        ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3))))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
  obtain ⟨c, hc, L₀, htot⟩ :=
    exists_measure_locmove_total (N := N) hp0 hp1 hm A hA hAc hC₀1 hC₀M hγC
  refine ⟨c, hc, max L₀ 1, ?_⟩
  intro L hLbig T r hr n0 s t hn0 hst hhor hr' hK
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  have hK1 : 1 ≤ t - s := le_trans hL1 hK
  have hKle : t - s ≤ (T + 3) * L := by omega
  have hx1 : (1 : ℝ) ≤ LocSumAct.xOf L := LocSumAct.one_le_xOf hL1
  have hB : (0 : ℝ) < LocSumAct.xOf L := by linarith
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL1)
  have hε : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hLr _
  obtain ⟨hside₁, hside₂⟩ := side_conditions (N := N) hL1 hK hp0 hp1.le
  have hside₁' : (L : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * ((t - s : ℕ) : ℝ) *
      stepEnv (N := N) p (LocSumAct.xOf L) := by
    have h := hside₁
    rwa [← mul_assoc] at h
  have hside₂' : (L : ℝ) ^ (3 / 4 : ℝ) ≤ 4 * ((t - s : ℕ) : ℝ) * LocSumAct.xOf L := by
    have h := hside₂
    rwa [← mul_assoc] at h
  have hmain := htot L hL0 T r hr hn0 hst hhor hr' (B := LocSumAct.xOf L) hB hε hε hK1
    hside₁' hside₂'
  have hE₁ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))) := by
    apply Real.exp_le_exp.mpr
    have h2 : (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))
        = 4 * ((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2 := by ring
    rw [h2]
    exact gamma_exponent_le (N := N) hL1 hK1 hKle hp0 hp1.le hN
  have hE₂ : Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
        (4 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))
      ≤ Real.exp (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3)))) := by
    apply Real.exp_le_exp.mpr
    have h2 : (4 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2))
        = 4 * ((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2 := by ring
    rw [h2]
    exact maxgrowth_exponent_le hL1 hK1 hKle
  calc (arrayMeasure N).real
        {U : Array N |
          locmoveGood (N := N) p m A hA (r : ℤ) T L (LocSumAct.xOf L) n0 s t U ∧
            (0 ≤ Xmin p m U A hA s ∧
              r - (T + 2) * L ≤ (Xmin p m U A hA s).toNat ∧
              (Rmax p m U A hA t).toNat ≤ r + (T + 2) * L) ∧
            ¬ (WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
                ≤ locmoveRHS (N := N) p m A hA L ((2 * C₀ + 1) / 2)
                    ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
                    ((L : ℝ) ^ (3 / 4 : ℝ)) ((L : ℝ) ^ (3 / 4 : ℝ)) s t U)}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2)))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (4 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := hmain
    _ ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3))))
          + 2 * (((t - s : ℕ) : ℝ) + 1) *
            Real.exp (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3)))))
          + Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L)) := by
        nlinarith [hE₁, hE₂,
          Real.exp_pos (-((LocSumAct.xOf L) ^ 6 / (16 * ((T : ℝ) + 3)))),
          Real.exp_pos (-((LocSumAct.xOf L) ^ 4 / (1600 * ((N : ℝ) ^ 2 * ((T : ℝ) + 3))))),
          Real.exp_pos (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p (LocSumAct.xOf L)) ^ 2))),
          Real.exp_pos (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) /
              (4 * (((t - s : ℕ) : ℝ) * (2 * LocSumAct.xOf L) ^ 2)))]

end LocMoveCompose
