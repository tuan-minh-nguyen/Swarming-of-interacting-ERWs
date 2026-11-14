/-
# `(loccoord)` at the paper's record clock: canonical constant, no side conditions,
# and the record-window range transfer done explicitly

The verified base `LocStartRange.loccoord_full_window_concrete` proves the paper's
`(loccoord)` on the full record window `[r-(T+2)L, r+(T+2)L]` under `r ≥ (T+3)L`, but

* with an abstract `(locsum)` constant `C` satisfying `1 ≤ C` and `Mb p (qOf p m) < C`,
* with the additive remainder `3 C · betaT (xOf ((2T+4)L))` instead of the paper's
  `C_T L^{3/4}`,
* with the explicit arithmetic side condition `(2T+4)·4^16 ≤ L^15`, and
* with the *range hypotheses* `r-(T+2)L ≤ Xmin_s`, `Rmax_t ≤ r+(T+2)L`, `0 ≤ Xmin_s`
  supplied by hand.

This file removes all four in the form the paper states them.  Nothing about a model
field, an extra hypothesis or an unspecified constant is hidden.

## 1. Canonical constant

`Ccan p m = |Mb p (qOf p m)| + 1` — *definitionally* the accepted canonical constant
`SingleWindowSiteRate.Ccan` of the site-rate base (B).  `one_le_Ccan` and `Mb_lt_Ccan`
discharge the two hypotheses of the whole `(locsum)` chain at this constant.

## 2. Arithmetic: `(2T+4)·4^16 ≤ L^15` is not a hypothesis of the paper's statement

The paper quantifies `L` over "all sufficiently large integers" *after* fixing `T`
(`for every fixed T ≥ 1, all sufficiently large integers L`).  `exists_arith_L0`
produces `L₀ = L₀(T)` past which `(2T+4)·4^16 ≤ L^15` holds for good, so the side
condition disappears into the threshold `L₀(T)`.  No inequality is dropped: the
theorem `loccoord_canonical_paper` below is *derived from*
`loccoord_full_window_concrete`, it does not replace it.

## 3. Paper constants

`loccoord_canonical_paper` replaces `3 Ccan · betaT (xOf ((2T+4)L))` by
`C_T · L^{3/4}` with the named
`C_T = 9·Ccan·(2T+4)^{3/4} + 1`
(using `LocSumAct.betaT_xOf_le_rpow34` and `Real.mul_rpow`), and the probability bound
`exp(-c · xOf ((2T+4)L))` by `C_T exp(-c_T L^{1/16})` with the named `c_T = c`
(since `xOf ((2T+4)L) ≥ xOf L`).  `C_T` carries the whole `T`-dependence; `Ccan` is
`T`-free, as in the paper ("the coefficient C is independent of T").

## 4. Record window → potential: the range hypotheses are derived, not assumed

The paper's `(loccoord)` is asserted on `G_{r,L,T} ∩ {d_r ≤ L}` for
`τ_r ≤ s ≤ t ≤ τ_r + ⌊TL⌋`.  The verified formalisation of the same proposition
(`Loccoord.loccoord_full_window*`) takes the resulting *range* facts
`r-(T+2)L ≤ Xmin_s` and `Rmax_t ≤ r+(T+2)L` as hypotheses.  They are pure
deterministic consequences of the record structure:

* `IsRecord` (the definition of `τ_r = inf{n : max_i X_n^i = r}`) says nobody is at
  level `r` before `τ_r` and the maximum *is* `r` at `τ_r`;
* `d_r ≤ L` says `r - min_i X_{τ_r}^i ≤ L`;
* one step moves a walker by exactly `±1`, so over `[τ_r, τ_r+TL]` a walker can lose
  at most `⌊TL⌋` sites and can rise at most `⌊TL⌋`.

Hence `Xmin_s ≥ r - L - TL ≥ r - (T+2)L` and `Rmax_t ≤ r + TL ≤ r + (T+2)L`
(`Xmin_ge`, `Rmax_toNat_le`), and `loccoord_record_window` feeds them into the
canonical estimate.  The result is the paper's `(loccoord)` for the actual trajectory,
at actual integer times, with no range hypotheses and no side arithmetic.

No `sorry`, no `admit`, no custom axiom.
-/
import Swarm.LocStartRange
import Swarm.LocCoordRange
import Swarm.BetaNormalise
import Swarm.TopRowChain
import Swarm.ActualRecordFiltration
import Swarm.RecordMeas

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace LocCoordPaper

noncomputable section

variable {N : ℕ}

/-! ### 1. The canonical `(locsum)` constant -/

/-- **The canonical constant.** `Ccan p m = |Mb p (qOf p m)| + 1`, definitionally the
accepted `SingleWindowSiteRate.Ccan` of the site-rate base. -/
noncomputable def Ccan (p : ℝ) (m : ℕ) : ℝ := |LocSum.Mb p (LocSumAct.qOf p m)| + 1

theorem one_le_Ccan (p : ℝ) (m : ℕ) : 1 ≤ Ccan p m := by
  unfold Ccan
  have h : (0 : ℝ) ≤ |LocSum.Mb p (LocSumAct.qOf p m)| := abs_nonneg _
  linarith

theorem Mb_lt_Ccan (p : ℝ) (m : ℕ) : LocSum.Mb p (LocSumAct.qOf p m) < Ccan p m := by
  unfold Ccan
  have h : LocSum.Mb p (LocSumAct.qOf p m) ≤ |LocSum.Mb p (LocSumAct.qOf p m)| := le_abs_self _
  linarith

theorem Ccan_pos (p : ℝ) (m : ℕ) : 0 < Ccan p m := lt_of_lt_of_le zero_lt_one (one_le_Ccan p m)

/-- The named `T`-dependent remainder constant `C_T = 9·Ccan·(2T+4)^{3/4} + 1`. -/
noncomputable def CT (p : ℝ) (m T : ℕ) : ℝ :=
  9 * Ccan p m * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) + 1

theorem one_le_CT (p : ℝ) (m T : ℕ) : 1 ≤ CT p m T := by
  unfold CT
  have h1 : (1 : ℝ) ≤ Ccan p m := one_le_Ccan p m
  have h2 : (0 : ℝ) ≤ (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) := by positivity
  nlinarith

/-! ### 2. The start-range arithmetic absorbed into the threshold `L₀(T)` -/

/-- **For each fixed `T` the side condition `(2T+4)·4^16 ≤ L^15` holds eventually.**
This is exactly what the paper's "for every fixed `T ≥ 1`, all sufficiently large `L`"
allows, so the side condition of `loccoord_full_window_concrete` is not a hypothesis of
the paper's statement. -/
theorem exists_arith_L0 (T : ℕ) : ∃ L₀ : ℕ, ∀ L ≥ L₀, (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 := by
  refine ⟨max 2 ((2 * T + 4) * 4 ^ 16), fun L hL => ?_⟩
  have hc : (2 * T + 4) * 4 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  exact le_trans hc (Nat.le_self_pow (by norm_num) L)

/-! ### 2b. The paper's good event `𝒢_{r,L,T}` -/

/-- **The paper's local good event** `𝒢_{r,L,T}` at the canonical constant: the complement
of the `(locsum)` bad event on the full record window `[r-(T+2)L, r+(T+2)L)`.  On it every
walker's harmonic potential satisfies the paper's `(locsum)` on every interval of the
window (`LocSumR1.array_locsum_h_start`), and by `loccoord_record_window` it carries the
`(loccoord)` estimate. -/
noncomputable def goodSet (p : ℝ) (m T L r : ℕ) : Set (Swarming.Uniform.Array N) :=
  (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))ᶜ

theorem mem_goodSet_iff {p : ℝ} {m T L r : ℕ} (U : Swarming.Uniform.Array N) :
    U ∈ goodSet (N := N) p m T L r
      ↔ U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) :=
  Iff.rfl

/-! ### 3. `(loccoord)` in the paper's constants, without the side condition -/

/-- **The paper's `(loccoord)` with canonical constants and no side conditions.**

For every `1/2 < p < 1`, `m ≥ 2` and every fixed `T` there are `c_T, C_T > 0`
(`C_T = CT p m T ≥ 1`, `c_T` the rate of the `(locsum)` chain) and a threshold `L₀`
such that for every `L ≥ L₀`, every `r ≥ (T+3)L`, off an event of `arrayMeasure` at
most `C_T e^{-c_T L^{1/16}}`, every group `B` and every `s ≤ t` with the window range
`r-(T+2)L ≤ Xmin_s`, `Rmax_t ≤ r+(T+2)L` satisfy

  average_{k∈B}(H_t^B(X_t^k) - H_s^B(X_s^k))
    ≤ ((2 Ccan+1)/2)(Rmax_t - Xmin_s) + C_T L^{3/4}.

The `(locsum)` constant is the canonical `Ccan`, the arithmetic side condition
`(2T+4)·4^16 ≤ L^15` is absorbed into `L₀ = L₀(T)`, and no other hypothesis is added. -/
theorem loccoord_canonical_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Loccoord.Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Loccoord.Xmin p m U B hB s).toNat →
      (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * Ccan p m + 1) / 2)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ :=
    Loccoord.loccoord_full_window_concrete (N := N) hp1 hp2 hm
      (C := Ccan p m) (one_le_Ccan p m) (Mb_lt_Ccan p m)
  obtain ⟨L₁, hL₁⟩ := exists_arith_L0 T
  refine ⟨c, CT p m T, hc, one_le_CT p m T, max L₀ (max L₁ (max 1 1)), ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hLarith : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 :=
    hL₁ L (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLbig)
  have hL1 : 1 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLbig
  obtain ⟨hprob, hbound⟩ := hL L hL0 T r hr hLarith
  -- the probability bound, with the paper's `C_T e^{-c_T L^{1/16}}`
  have hLM : (L : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by
    have hpos : 0 < 2 * T + 4 := by omega
    have h := Nat.le_mul_of_pos_left L hpos
    exact_mod_cast h
  have hxle : (L : ℝ) ^ (1 / 16 : ℝ)
      ≤ ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (1 / 16 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hLM (by norm_num)
  have hexp : Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
      ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : LocSumAct.xOf ((2 * T + 4) * L)
        = ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (1 / 16 : ℝ) := rfl
    rw [this]
    nlinarith [hxle, hc]
  have hexp2 : Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))
      ≤ CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    have hpos : (0 : ℝ) < Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := Real.exp_pos _
    calc Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))
        = 1 * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by ring
      _ ≤ CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) :=
          mul_le_mul_of_nonneg_right (one_le_CT p m T) hpos.le
  have hprob' : Swarming.Uniform.arrayMeasure N
      (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
      ≤ ENNReal.ofReal (CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))) :=
    le_trans hprob (ENNReal.ofReal_le_ofReal (le_trans hexp hexp2))
  refine ⟨hprob', ?_⟩
  intro U hU B hB s t hst hX0 hXmin hRmax
  have hmain := hbound U hU B hB s t hst hX0 hXmin hRmax
  -- the `(locsum)` remainder `3 Ccan betaT (xOf ((2T+4)L))` inside `C_T L^{3/4}`
  have hLw : 1 ≤ (2 * T + 4) * L := by
    have hpos : 0 < 2 * T + 4 := by omega
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (2 * T + 4) * L := Nat.mul_le_mul (by omega) hL1
  have hbeta : ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ 3 * ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) :=
    LocSumAct.betaT_xOf_le_rpow34 hLw
  have hcast : ((((2 * T + 4) * L : ℕ)) : ℝ) = (((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ) := by
    push_cast; ring
  have hsplit : ((((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ)) ^ (3 / 4 : ℝ)
      = ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hC0 : (0 : ℝ) ≤ Ccan p m := le_trans zero_le_one (one_le_Ccan p m)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hrem : 3 * Ccan p m * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ CT p m T * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : 3 * Ccan p m
        * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
        ≤ 3 * Ccan p m * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
            * (L : ℝ) ^ (3 / 4 : ℝ))) := by
      rw [← hsplit, ← hcast]
      have h3 : (0 : ℝ) ≤ 3 * Ccan p m := by linarith
      nlinarith [hbeta, h3]
    have h2 : 3 * Ccan p m * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
        * (L : ℝ) ^ (3 / 4 : ℝ)))
        = (9 * Ccan p m * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
      ring
    rw [h2] at h1
    unfold CT
    nlinarith [h1, hLnn]
  linarith [hmain, hrem]

end

/-- **The measure of the bad event is `≤ C_T e^{-c_T L^{1/16}}`** in the paper's notation. -/
theorem measure_goodSet_compl {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N (goodSet (N := N) p m T L r)ᶜ
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) := by
  obtain ⟨c_T, C_T, hc, hC, L₀, hL⟩ := loccoord_canonical_paper (N := N) hp1 hp2 hm T
  refine ⟨c_T, C_T, hc, hC, L₀, ?_⟩
  intro L hLbig r hr
  have h := (hL L hLbig r hr).1
  rwa [goodSet, compl_compl]

/-! ### 4. From the record clock to the potential: the range transfer -/

section RecordWindow

open RecordDefect RecordoSupply

variable [Nonempty (Fin N)]

/-- The per-walker running maximum is the supremum of `actX` over the past. -/
lemma runMax_eq_sup (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N) (t : ℕ) :
    Swarming.Trajectory.runMax p m U i t
      = (Finset.range (t + 1)).sup'
          ⟨0, Finset.mem_range.mpr (Nat.succ_pos t)⟩ (fun u => actX p m U i u) := rfl

/-- A pointwise bound on the past bounds the per-walker running maximum. -/
lemma runMax_le_of_pointwise {p : ℝ} {m : ℕ} {U : Swarming.Uniform.Array N} {i : Fin N}
    {t : ℕ} {a : ℤ} (h : ∀ u ≤ t, actX p m U i u ≤ a) :
    Swarming.Trajectory.runMax p m U i t ≤ a := by
  obtain ⟨u, hu, hue⟩ := Swarming.Trajectory.exists_eq_runMax p m U i t
  have h' : actX p m U i u = Swarming.Trajectory.runMax p m U i t := hue
  rw [← h']
  exact h u hu

/-- `actX` is the trajectory position. -/
lemma actX_eq_pos (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N) (n : ℕ) :
    actX p m U i n = (Swarming.Trajectory.trajectory p m U n).pos i := rfl

/-- A walker never rises by more than the number of elapsed steps (`actX` form). -/
lemma actX_step_upper (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N)
    {a b : ℕ} (hab : a ≤ b) :
    actX p m U i b ≤ actX p m U i a + ((b - a : ℕ) : ℤ) :=
  TopRowChain.step_upper p m U i hab

/-- A walker never falls by more than the number of elapsed steps (`actX` form). -/
lemma actX_step_lower (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N)
    {a b : ℕ} (hab : a ≤ b) :
    actX p m U i a - ((b - a : ℕ) : ℤ) ≤ actX p m U i b :=
  TopRowChain.step_lower p m U i hab

/-- **Upper end of the record window.**  On a record window `[τ, τ+TL]` with record level
`r` at `τ`, no walker's running maximum exceeds `r + TL`, hence certainly
`r + (T+2)L`. -/
theorem Rmax_le_nat {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N} {t τ : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hlow : ∀ n < τ, runMax (actX p m U) n < (r : ℤ))
    (hτmax : runMax (actX p m U) τ = (r : ℤ))
    (hst : τ ≤ t) (htT : t ≤ τ + T * L) :
    (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L := by
  have hkey : ∀ k ∈ B,
      Swarming.Trajectory.runMax p m U k t ≤ (((r + (T + 2) * L : ℕ)) : ℤ) := by
    intro k _
    refine runMax_le_of_pointwise (fun u hu => ?_)
    have hle : actX p m U k u ≤ (r : ℤ) + ((u - τ : ℕ) : ℤ) := by
      by_cases huτ : u ≤ τ
      · have h1 : actX p m U k u ≤ runMax (actX p m U) u := le_runMax u k
        have hcast : ((u - τ : ℕ) : ℤ) = 0 := by
          have : u - τ = 0 := by omega
          rw [this]; norm_num
        rw [hcast, add_zero]
        rcases lt_or_eq_of_le huτ with hlt | heq
        · have h2 := hlow u hlt
          linarith
        · subst heq
          rw [hτmax] at h1
          exact h1
      · push Not at huτ
        have hstep := actX_step_upper p m U k (le_of_lt huτ)
        have h2 : actX p m U k τ ≤ (r : ℤ) := by
          have := le_runMax (X := actX p m U) τ k
          rw [hτmax] at this
          exact this
        linarith
    have hsub : ((u - τ : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
      have h1 : u - τ ≤ T * L := by omega
      exact_mod_cast h1
    have hnat : (r : ℤ) + ((T * L : ℕ) : ℤ) ≤ (((r + (T + 2) * L : ℕ)) : ℤ) := by
      have : r + T * L ≤ r + (T + 2) * L := by
        have : T * L ≤ (T + 2) * L := Nat.mul_le_mul_right L (by omega)
        omega
      have h := Nat.cast_le (α := ℤ).mpr this
      push_cast at h ⊢
      linarith
    linarith
  have hsup : Loccoord.Rmax p m U B hB t ≤ (((r + (T + 2) * L : ℕ)) : ℤ) :=
    Finset.sup'_le hB (fun k => Swarming.Trajectory.runMax p m U k t) hkey
  have h := Int.toNat_le_toNat hsup
  rwa [Int.toNat_natCast] at h

/-- **Lower end of the record window.**  If the defect at the record time is at most `L`
(`d_r ≤ L`) then at every time `s ∈ [τ, τ+TL]` every walker of the group stands at or
above `r - L - TL ≥ r - (T+2)L`. -/
theorem Xmin_ge_int {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N} {s τ : ℕ}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hdef : (r : ℤ) - runMin (actX p m U) τ ≤ (L : ℤ))
    (hτs : τ ≤ s) (hsT : s ≤ τ + T * L) :
    (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ Loccoord.Xmin p m U B hB s := by
  have hmin : (r : ℤ) - (L : ℤ) ≤ runMin (actX p m U) τ := by linarith
  refine Finset.le_inf' hB (fun k => SepGroup.Model.X p m U s k) (fun k _ => ?_)
  have h1 : (r : ℤ) - (L : ℤ) ≤ actX p m U k τ :=
    le_trans hmin (runMin_le τ k)
  have h2 : actX p m U k τ - ((s - τ : ℕ) : ℤ) ≤ actX p m U k s :=
    TopRowChain.step_lower p m U k hτs
  have hsub : ((s - τ : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have h : s - τ ≤ T * L := by omega
    exact_mod_cast h
  have hcast : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ)
      ≤ (r : ℤ) - (L : ℤ) - ((T * L : ℕ) : ℤ) := by
    have hmul : (L : ℤ) + ((T * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by
      have h1 : L + T * L ≤ (T + 2) * L := by
        have h2 : (T + 1) * L ≤ (T + 2) * L := Nat.mul_le_mul_right L (by omega)
        have h3 : (T + 1) * L = T * L + L := by ring
        omega
      exact_mod_cast h1
    linarith
  have hX : SepGroup.Model.X p m U s k = actX p m U k s := rfl
  rw [hX]
  linarith

end RecordWindow

/-! ### 5. `(loccoord)` on the record window, with no range hypotheses -/

section RecordWindowMain

open RecordDefect RecordoSupply

variable [Nonempty (Fin N)]

/-- **The paper's `(loccoord)` at the actual record clock.**

For every `1/2 < p < 1`, `m ≥ 2` and fixed `T` there are `c_T, C_T > 0` and `L₀` such
that for every `L ≥ L₀` and every `r ≥ (T+3)L`, off an event of `arrayMeasure` at most
`C_T e^{-c_T L^{1/16}}`, for every `U` for which the canonical record clock
`recTimeA p m U` is a record sequence and whose defect at level `r` is at most `L`
(the paper's `{d_r ≤ L}`), and for all times `τ_r ≤ s ≤ t ≤ τ_r + ⌊TL⌋` and every group
`B`,

  average_{k∈B}(H_t^B(X_t^k) - H_s^B(X_s^k))
    ≤ ((2 Ccan+1)/2)(Rmax_t - Xmin_s) + C_T L^{3/4}.

The range hypotheses of `Loccoord.loccoord_full_window*` are *derived* here
(`Xmin_ge_int`, `Rmax_le_nat`), the constant is the canonical `Ccan`, and the
start-range arithmetic side condition is absorbed into `L₀ = L₀(T)`. -/
theorem loccoord_record_window {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
      RecordDefect.IsRecord (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) →
      RecordDefect.defect (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r ≤ (L : ℤ) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ),
      SwarmRecordMeas.Actual.recTimeA p m U r ≤ s → s ≤ t →
      t ≤ SwarmRecordMeas.Actual.recTimeA p m U r + T * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * Ccan p m + 1) / 2)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c_T, C_T, hc, hC, L₀, hL⟩ := loccoord_canonical_paper (N := N) hp1 hp2 hm T
  refine ⟨c_T, C_T, hc, hC, max L₀ 1, ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hLbig
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hprob, hbound⟩ := hL L hL0 r hr
  refine ⟨hprob, ?_⟩
  intro U hU hrec hdef B hB s t hs hst htT
  set τ := SwarmRecordMeas.Actual.recTimeA p m U r with hτdef
  have hlow : ∀ n < τ, runMax (actX p m U) n < (r : ℤ) := (hrec r).1
  have hτmax : runMax (actX p m U) τ = (r : ℤ) := (hrec r).2
  have hdef' : (r : ℤ) - runMin (actX p m U) τ ≤ (L : ℤ) := by
    have : RecordDefect.defect (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r
        = (r : ℤ) - runMin (actX p m U) τ := rfl
    rw [this] at hdef
    exact hdef
  have hXmin : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ Loccoord.Xmin p m U B hB s :=
    Xmin_ge_int (s := s) (B := B) hB hdef' hs (le_trans hst htT)
  have hRmax : (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L :=
    Rmax_le_nat (t := t) (B := B) hB hlow hτmax (le_trans hs hst) htT
  have hTL : (T + 2) * L ≤ r := by
    have : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    omega
  have hX0 : (0 : ℤ) ≤ Loccoord.Xmin p m U B hB s := by
    have hcast : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hTL
    linarith
  have hXminNat : r - (T + 2) * L ≤ (Loccoord.Xmin p m U B hB s).toNat := by
    refine (Int.le_toNat hX0).2 ?_
    have hcast : ((r - (T + 2) * L : ℕ) : ℤ)
        = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hTL]
      ring
    rw [hcast]
    exact hXmin
  exact hbound U hU B hB s t hst hX0 hXminNat hRmax

/-- **`(loccoord)` at the record clock in the paper's `C(b0-a0) + C_T L^{3/4}` shape,
with the extremal endpoints and the `T`-free coefficient.**

Same statement as `loccoord_record_window`, with the coefficient `(2 Ccan+1)/2` weakened to
the `T`-free `Ccan + 1` (`≤ Ccan + 1` because `(2Ccan+1)/2 = Ccan + 1/2`).  This is the
form consumed by the `(locmove)` chain (`LocMoveCompose`, `ShortLocMove`), where the mean
term is bounded by `C (R_t^A - min_{i∈A} X_s^i) + C_T L^{3/4}`. -/
theorem loccoord_record_window_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
      RecordDefect.IsRecord (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) →
      RecordDefect.defect (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r ≤ (L : ℤ) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ),
      SwarmRecordMeas.Actual.recTimeA p m U r ≤ s → s ≤ t →
      t ≤ SwarmRecordMeas.Actual.recTimeA p m U r + T * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ (Ccan p m + 1)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c_T, C_T, hc, hC, L₀, hL⟩ := loccoord_record_window (N := N) hp1 hp2 hm T
  refine ⟨c_T, C_T, hc, hC, L₀, ?_⟩
  intro L hLbig r hr
  obtain ⟨hprob, hbound⟩ := hL L hLbig r hr
  refine ⟨hprob, ?_⟩
  intro U hU hrec hdef B hB s t hs hst htT
  have hmain := hbound U hU hrec hdef B hB s t hs hst htT
  have hdiff : (0 : ℝ) ≤ ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
      - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ) := by
    have h1 : Loccoord.Xmin p m U B hB s ≤ Loccoord.Rmax p m U B hB t :=
      Loccoord.Xmin_le_Rmax (p := p) (m := m) U hB hst
    have h2 : ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ)
        ≤ ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have hcoef : ((2 * Ccan p m + 1) / 2) ≤ Ccan p m + 1 := by linarith
  have hstep : ((2 * Ccan p m + 1) / 2)
      * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
          - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
      ≤ (Ccan p m + 1)
        * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
            - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hcoef hdiff
  linarith [hmain, hstep]

end RecordWindowMain

/-! ### 6. Helper normalisations: exponential and `betaT` at the paper's scale -/

section Normalise

/-- `exp(-c · xOf M) ≤ C_T exp(-c_T L^{1/16})` for `1 ≤ L ≤ M`: the window length
`M = (2T+4)L` only makes the rate stronger, and `C_T ≥ 1` absorbs the constant. -/
lemma exp_normalise {p : ℝ} {m T L M : ℕ} {c : ℝ} (hc : 0 < c) (hL : 1 ≤ L) (hLM : L ≤ M) :
    Real.exp (-c * LocSumAct.xOf M)
      ≤ CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
  have hLM' : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hLM
  have hxle : (L : ℝ) ^ (1 / 16 : ℝ) ≤ (M : ℝ) ^ (1 / 16 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hLM' (by norm_num)
  have hxM : LocSumAct.xOf M = (M : ℝ) ^ (1 / 16 : ℝ) := rfl
  have hxL : LocSumAct.xOf L = (L : ℝ) ^ (1 / 16 : ℝ) := rfl
  have hexp : Real.exp (-c * LocSumAct.xOf M)
      ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [hxM]
    nlinarith [hxle, hc]
  have hpos : (0 : ℝ) < Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := Real.exp_pos _
  calc Real.exp (-c * LocSumAct.xOf M)
      ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := hexp
    _ = 1 * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by ring
    _ ≤ CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_right (one_le_CT p m T) hpos.le

/-- The actual `(locsum)` remainder `3 Ccan betaT (xOf ((2T+4)L))` is at most
`C_T L^{3/4}` with the named constant `C_T = 9 Ccan (2T+4)^{3/4} + 1`. -/
lemma betaT_normalise {p : ℝ} {m T L : ℕ} (hL : 1 ≤ L) :
    3 * Ccan p m * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ CT p m T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hLw : 1 ≤ (2 * T + 4) * L := by
    have hpos : 0 < 2 * T + 4 := by omega
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (2 * T + 4) * L := Nat.mul_le_mul (by omega) hL
  have hbeta : ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ 3 * ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) :=
    LocSumAct.betaT_xOf_le_rpow34 hLw
  have hcast : ((((2 * T + 4) * L : ℕ)) : ℝ) = (((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ) := by
    push_cast; ring
  have hsplit : ((((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ)) ^ (3 / 4 : ℝ)
      = ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hC0 : (0 : ℝ) ≤ Ccan p m := le_trans zero_le_one (one_le_Ccan p m)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have h1 : 3 * Ccan p m
      * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ 3 * Ccan p m * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
          * (L : ℝ) ^ (3 / 4 : ℝ))) := by
    rw [← hsplit, ← hcast]
    have h3 : (0 : ℝ) ≤ 3 * Ccan p m := by linarith
    nlinarith [hbeta, h3]
  have h2 : 3 * Ccan p m * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
      * (L : ℝ) ^ (3 / 4 : ℝ)))
      = (9 * Ccan p m * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    ring
  rw [h2] at h1
  unfold CT
  nlinarith [h1, hLnn]

end Normalise

section FixedForm

open RecordDefect RecordoSupply

variable [Nonempty (Fin N)]

/-- **The paper's displayed `(loccoord)` at the actual record clock.**

For every `1/2 < p < 1`, `m ≥ 2` and fixed `T` there are `c_T, C_T > 0` and `L₀` such
that for every `L ≥ L₀`, every `r ≥ (T+3)L`, off an event of `arrayMeasure` at most
`C_T e^{-c_T L^{1/16}}`, every `U` with record structure `recTimeA p m U` and defect at
level `r` at most `L` (`d_r ≤ L`), every nonempty group `B`, every time
`t ∈ [τ_r, τ_r+TL]` and all integers `r-(T+2)L ≤ a0 ≤ b0 ≤ R_t^B` satisfy

  H_t^B(b0) - H_t^B(a0) ≤ (Ccan + 1)(b0 - a0) + C_T L^{3/4}.

This is equation `(loccoord)` of Proposition `local` verbatim (the coefficient `C` is
weakened to the `T`-free `Ccan + 1 = (2Ccan+1)/2 + 1/2`), with the range facts derived
from the record structure and no arithmetic side condition. -/
theorem loccoord_record_fixed {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
      RecordDefect.IsRecord (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) →
      RecordDefect.defect (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r ≤ (L : ℤ) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (t : ℕ),
      SwarmRecordMeas.Actual.recTimeA p m U r ≤ t →
      t ≤ SwarmRecordMeas.Actual.recTimeA p m U r + T * L →
      ∀ a0 b0 : ℕ,
      r - (T + 2) * L ≤ a0 → a0 ≤ b0 → (b0 : ℤ) ≤ Loccoord.Rmax p m U B hB t →
      SepGroup.Model.HA p m U t B (b0 : ℤ) - SepGroup.Model.HA p m U t B (a0 : ℤ)
        ≤ (Ccan p m + 1) * ((b0 : ℝ) - (a0 : ℝ)) + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  -- the raw `(locsum)` display, with its per-walker interval bound
  obtain ⟨c, hc, L₀, hL⟩ := LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm
    (C := Ccan p m) (one_le_Ccan p m) (Mb_lt_Ccan p m)
  obtain ⟨L₁, hL₁⟩ := exists_arith_L0 T
  refine ⟨c, CT p m T, hc, one_le_CT p m T, max (max L₀ L₁) 1, ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hLarith : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 :=
    hL₁ L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  -- the `(locsum)` window `[r-(T+2)L, r+(T+2)L)` starts at least `2⌈((2T+4)L)^{1/16}⌉`
  have hwin0 : L₀ ≤ (2 * T + 4) * L := by
    have h1 : 1 ≤ 2 * T + 4 := by omega
    calc L₀ ≤ L := hL0
      _ = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L h1
      _ = (2 * T + 4) * L := Nat.mul_comm _ _ 
  have hTL : (T + 2) * L ≤ r := by
    have : (T + 2) * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    omega
  have hstart : 2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L)) ≤ r - (T + 2) * L := by
    have h1 : 2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L)) ≤ L :=
      LocSumAct.two_mul_ellT_window_le hL1 hLarith
    have h2 : L ≤ r - (T + 2) * L := by
      refine (Nat.le_sub_iff_add_le hTL).2 ?_
      have h3 : L + (T + 2) * L = (T + 3) * L := by ring
      omega
    omega
  obtain ⟨hprob, hbound⟩ := hL ((2 * T + 4) * L) hwin0 (r - (T + 2) * L) hstart
  have hMge : L ≤ (2 * T + 4) * L := by
    have hpos : 0 < 2 * T + 4 := by omega
    calc L = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L (by omega)
      _ = (2 * T + 4) * L := Nat.mul_comm _ _ 
  have hprob' : Swarming.Uniform.arrayMeasure N
      (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
      ≤ ENNReal.ofReal (CT p m T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))) :=
    le_trans hprob (ENNReal.ofReal_le_ofReal
      (exp_normalise (p := p) (m := m) (T := T) hc hL1 hMge))
  refine ⟨hprob', ?_⟩
  intro U hU hrec hdef B hB t ht1 ht2 a0 b0 ha0 hab hb0
  set τ := SwarmRecordMeas.Actual.recTimeA p m U r with hτdef
  have hlow : ∀ n < τ, runMax (actX p m U) n < (r : ℤ) := (hrec r).1
  have hτmax : runMax (actX p m U) τ = (r : ℤ) := (hrec r).2
  -- the record-window upper range for `Rmax`
  have hRmax : (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L :=
    Rmax_le_nat (t := t) (B := B) hB hlow hτmax ht1 ht2
  have hR0 : (0 : ℤ) ≤ Loccoord.Rmax p m U B hB t :=
    le_trans (by exact_mod_cast Nat.zero_le b0) hb0
  -- the harmonic window `[A, A+Lw)` contains `[a0,b0)`
  have hbLw : b0 ≤ (r - (T + 2) * L) + ((2 * T + 4) * L) := by
    have h1 : b0 ≤ r + (T + 2) * L := by
      have hcast : ((b0 : ℤ)) ≤ (((r + (T + 2) * L : ℕ)) : ℤ) := by
        have h2 : Loccoord.Rmax p m U B hB t ≤ (((r + (T + 2) * L : ℕ)) : ℤ) := by
          have h3 : (((Loccoord.Rmax p m U B hB t).toNat : ℕ) : ℤ)
              = Loccoord.Rmax p m U B hB t := Int.toNat_of_nonneg hR0
          have h4 : (((Loccoord.Rmax p m U B hB t).toNat : ℕ) : ℤ)
              ≤ (((r + (T + 2) * L : ℕ)) : ℤ) := by exact_mod_cast hRmax
          linarith
        linarith
      exact_mod_cast hcast
    have hmul : (2 * T + 4) * L = (T + 2) * L + (T + 2) * L := by ring
    have h2 : (r - (T + 2) * L) + ((2 * T + 4) * L) = r + (T + 2) * L := by
      rw [hmul, ← Nat.add_assoc, Nat.sub_add_cancel hTL]
    rw [h2]
    exact h1
  -- choose the leader realising `R_t^B`
  obtain ⟨i, hiB, hieq⟩ := Finset.exists_mem_eq_sup' hB
    (fun k => Swarming.Trajectory.runMax p m U k t)
  have hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t := by
    rw [← hieq]
    exact hb0

  -- the `(locsum)` bound on `[a0,b0)` for the leader, in group coordinates
  have hp0 : p ≠ 0 := by linarith
  have hsum0 := hbound U hU i a0 b0 ha0 hbLw hab
  have hsum : ∑ x ∈ Finset.Ico a0 b0,
      (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 2 * Ccan p m * (3 * ((LocSumAct.betaT
              (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)) := by
    have hbridge : ∀ x : ℕ, Cookie.hfix (SepGroup.Model.omegaN p m U i) x
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x :=
      fun x => Loccoord.hfix_omegaN_eq_hof hp0 i x
    have hcongr : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
        = ∑ x ∈ Finset.Ico a0 b0,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [hbridge x]
    rw [hcongr]
    nlinarith [hsum0]
  -- the deterministic single-time `(loccoord)`
  have hmain := Loccoord.loccoord_fixed (p := p) (m := m) (N := N) (le_of_lt hp1)
    (le_of_lt hp2) U (n := t) (B := B) (i := i) hiB hab hbR
    (K := 2 * Ccan p m) (β := 3 * ((LocSumAct.betaT
      (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ))
    (by have := one_le_Ccan p m; linarith) (by positivity) hsum
  have harith : ((2 * Ccan p m + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ))
      + ((2 * Ccan p m) / 2)
        * (3 * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ))
      = ((2 * Ccan p m + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ))
        + 3 * Ccan p m
          * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ) := by
    ring
  rw [harith] at hmain
  -- weaken the `(b0-a0)` coefficient to the `T`-free `Ccan + 1`
  have hdiff : (0 : ℝ) ≤ (b0 : ℝ) - (a0 : ℝ) := by
    have : (a0 : ℝ) ≤ (b0 : ℝ) := by exact_mod_cast hab
    linarith
  have hcoef : ((2 * Ccan p m + 1) / 2) ≤ Ccan p m + 1 := by linarith
  have hstep1 : ((2 * Ccan p m + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ))
      ≤ (Ccan p m + 1) * ((b0 : ℝ) - (a0 : ℝ)) :=
    mul_le_mul_of_nonneg_right hcoef hdiff
  have hstep2 : 3 * Ccan p m
      * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ CT p m T * (L : ℝ) ^ (3 / 4 : ℝ) := betaT_normalise (p := p) (m := m) (T := T) hL1
  linarith [hmain, hstep1, hstep2]

end FixedForm

/-! ### 8. Removing the record-structure hypothesis almost surely -/

section AE

open RecordDefect RecordoSupply

variable [Nonempty (Fin N)]

/-- **`(loccoord)` at the record clock, almost surely in `U`.**

The record-structure hypothesis `IsRecord (actX p m U) (recTimeA p m U)` of
`loccoord_record_window` is not extra data: by the verified
`SwarmRecordMeas.Actual.ae_isRecord_recTimeA` (Swarm/RecordMeas.lean) it holds for
almost every array as soon as `N ≥ 2`, `1/2 < p < 1` and `m ≥ 2`.  Consequently the
paper's `(loccoord)`, on the paper's `{d_r ≤ L}` and record window `[τ_r, τ_r+TL]`,
holds for almost every `U`, off an event of `arrayMeasure` at most `C_T e^{-c_T L^{1/16}}`. -/
theorem loccoord_record_window_ae {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
        U ∉ LocSumR1.LsBad N p m (Ccan p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
        RecordDefect.defect (actX p m U) (SwarmRecordMeas.Actual.recTimeA p m U) r ≤ (L : ℤ) →
        ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ),
        SwarmRecordMeas.Actual.recTimeA p m U r ≤ s → s ≤ t →
        t ≤ SwarmRecordMeas.Actual.recTimeA p m U r + T * L →
        Swarming.Group.average B (fun k =>
            SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
              - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
          ≤ ((2 * Ccan p m + 1) / 2)
              * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                  - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
            + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c_T, C_T, hc, hC, L₀, hL⟩ := loccoord_record_window (N := N) hp1 hp2 hm T
  refine ⟨c_T, C_T, hc, hC, L₀, ?_⟩
  intro L hLbig r hr
  obtain ⟨hprob, hbound⟩ := hL L hLbig r hr
  refine ⟨hprob, ?_⟩
  filter_upwards [SwarmRecordMeas.Actual.ae_isRecord_recTimeA (N := N) hp1 hp2 hm hN]
    with U hrec hU hdef B hB s t hs hst htT
  exact hbound U hU hrec hdef B hB s t hs hst htT

end AE

/-! ### 9. Drop-in replacement for `Loccoord.loccoord_full_window` at the paper's threshold

The three public consumers of `(loccoord)` (`LocMoveCompose`, `LocMoveAllWindows`,
`ShortLocMove`) call `Loccoord.loccoord_full_window`, which needs `(3T+6)L ≤ r` and takes
the range hypotheses as arguments.  The theorem below has the *same conclusion and the same
abstract constant `C`*, but the paper's threshold `(T+3)L ≤ r` and no arithmetic side
condition; the start-range arithmetic is absorbed into `L₀(T)` exactly as in §3.  Consumers
can therefore be re-pointed by renaming the call and (optionally) dropping their explicit
range hypotheses.  No public source is edited here. -/

section DropIn

/-- The `T`-dependent remainder constant for a general `(locsum)` constant `C`:
`C_T = 9·C·(2T+4)^{3/4} + 1`. -/
noncomputable def CTof (C : ℝ) (T : ℕ) : ℝ :=
  9 * C * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) + 1

theorem one_le_CTof {C : ℝ} (hC : 0 ≤ C) (T : ℕ) : 1 ≤ CTof C T := by
  unfold CTof
  have h2 : (0 : ℝ) ≤ (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ) := by positivity
  nlinarith

theorem CT_eq_CTof_Ccan (p : ℝ) (m T : ℕ) : CT p m T = CTof (Ccan p m) T := rfl

/-- `3 C betaT (xOf ((2T+4)L)) ≤ C_T L^{3/4}` for a general nonnegative `C`. -/
lemma betaT_normalise_of {C : ℝ} (hC : 0 ≤ C) {T L : ℕ} (hL : 1 ≤ L) :
    3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ CTof C T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hLw : 1 ≤ (2 * T + 4) * L := by
    have hpos : 0 < 2 * T + 4 := by omega
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (2 * T + 4) * L := Nat.mul_le_mul (by omega) hL
  have hbeta : ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ 3 * ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) :=
    LocSumAct.betaT_xOf_le_rpow34 hLw
  have hcast : ((((2 * T + 4) * L : ℕ)) : ℝ)
      = (((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ) := by push_cast; ring
  have hsplit : ((((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ)) ^ (3 / 4 : ℝ)
      = ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have h1 : 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℕ) : ℝ)
      ≤ 3 * C * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
          * (L : ℝ) ^ (3 / 4 : ℝ))) := by
    rw [← hsplit, ← hcast]
    have h3 : (0 : ℝ) ≤ 3 * C := by linarith
    nlinarith [hbeta, h3]
  have h2 : 3 * C * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
      * (L : ℝ) ^ (3 / 4 : ℝ)))
      = (9 * C * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    ring
  rw [h2] at h1
  unfold CTof
  nlinarith [h1, hLnn]

/-- **`(loccoord)` on the full record window at `r ≥ (T+3)L`, abstract constant `C`.**

Identical conclusion to `Loccoord.loccoord_full_window`, with
`C_T = 9·C·(2T+4)^{3/4} + 1`, at the paper's threshold `(T+3)L ≤ r` and with the
`(locsum)` start arithmetic absorbed into `L₀(T)`.  The window range hypotheses are still
arguments here (consumers already supply them); use `loccoord_record_window` to have them
derived from the record clock. -/
theorem loccoord_full_window_T3 {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C)
    (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Loccoord.Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Loccoord.Xmin p m U B hB s).toNat →
      (Loccoord.Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ)
                - ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ))
          + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ :=
    Loccoord.loccoord_full_window_concrete (N := N) hp1 hp2 hm hC1 hCM
  obtain ⟨L₁, hL₁⟩ := exists_arith_L0 T
  refine ⟨c, CTof C T, hc, one_le_CTof (le_trans zero_le_one hC1) T, max (max L₀ L₁) 1, ?_⟩
  intro L hLbig r hr
  have hL0 : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hLarith : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 :=
    hL₁ L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLbig
  obtain ⟨hprob, hbound⟩ := hL L hL0 T r hr hLarith
  -- the probability bound
  have hMge : L ≤ (2 * T + 4) * L := by
    have hpos : 0 < 2 * T + 4 := by omega
    calc L = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L (by omega)
      _ = (2 * T + 4) * L := Nat.mul_comm _ _ 
  have hexp : Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))
      ≤ Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hLM : (L : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by exact_mod_cast hMge
    have hxle : (L : ℝ) ^ (1 / 16 : ℝ)
        ≤ ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    have hxM : LocSumAct.xOf ((2 * T + 4) * L)
        = ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (1 / 16 : ℝ) := rfl
    rw [hxM]
    nlinarith [hxle, hc]
  have hexp2 : Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))
      ≤ CTof C T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by
    have hpos : (0 : ℝ) < Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := Real.exp_pos _
    calc Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))
        = 1 * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) := by ring
      _ ≤ CTof C T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ)) :=
          mul_le_mul_of_nonneg_right (one_le_CTof (le_trans zero_le_one hC1) T) hpos.le
  have hprob' : Swarming.Uniform.arrayMeasure N
      (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
      ≤ ENNReal.ofReal (CTof C T * Real.exp (-c * (L : ℝ) ^ (1 / 16 : ℝ))) :=
    le_trans hprob (ENNReal.ofReal_le_ofReal (le_trans hexp hexp2))
  refine ⟨hprob', ?_⟩
  intro U hU B hB s t hst hX0 hXmin hRmax
  have hmain := hbound U hU B hB s t hst hX0 hXmin hRmax
  have hrem := betaT_normalise_of (le_trans zero_le_one hC1) (T := T) hL1
  linarith [hmain, hrem]

end DropIn

end LocCoordPaper
