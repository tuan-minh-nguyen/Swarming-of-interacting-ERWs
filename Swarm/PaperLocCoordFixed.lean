/-
# `(loccoord)` in the paper's literal single-time spatial shape, off the family event

## What this file is

The verified public packages `OccDisplayNull` and `LocalGoodFamily` export, off the one
finite-family bad event `famBad`,

  `average_{k∈B} (H_t^B(X_t^k) - H_s^B(X_s^k)) ≤ Cmax·(R_t^B - Xmin_s^B) + Cerr·L^{3/4}`

(`LocalGoodFamily.familyGood_loccoord`), which is the **two-time averaged / dynamic** form.  The
paper's `(loccoord)` in `main_1d_revised.tex` is the **single-time spatial** inequality

  `H_n^A(b0) - H_n^A(a0) ≤ C (b0 - a0) + C_T L^{3/4}`,
  for `r - (T+2)L ≤ a0 ≤ b0 ≤ R_n^A`, `n ∈ [τ_r, τ_r + TL]`,

and the roadmap (`results/proposition-local-declaration-roadmap.md`, §C5 row 3, §D2) records that
the transport from the family event to that shape was not packaged.  This file packages it.

The transport does **not** go through the averaging lemma.  It goes through the source proof of
the paper: the leader `i ∈ A` with `M_n^i = R_n^A` (`Finset.exists_mem_eq_sup'`), the `(hcomp)`
domination `h^A ≤ h_i` below the leader's running record (`Loccoord.loccoord_fixed`, which is
exactly `(loccoord)` conditional on the leader's squared-site sum), the pointwise `(locsum)`
content already exported by the family event at the `(lococc)` window `[A0, A0+Lw)`
(`LocOccSiteRate.Ccan`, `Lw = (2T+2)L+1`), and the bridge `h_i = hof (siteMarks i)`
(`Loccoord.hfix_omegaN_eq_hof`).

## What is genuinely new here

* `isRecord_recTimeA_of_reachAll`, `runMaxA_le_r_add_TL`: on `recordCarrier` the record clock is a
  record sequence and every group record stays inside `[.., r + TL]`, so the *upper* end of the
  `(locsum)` window `A0 + Lw = r + TL + 1` is reached with `b0 ≤ R_t^B` alone — no range premise.
* `le_A0_add_Lw`: `b0 ≤ r + TL ⟹ b0 ≤ A0 + Lw`, including the degenerate branch `r < (T+2)L`
  where `A0` saturates at `0`.
* `three_mul_betaT_Lw_le`: the family remainder `3·C·betaT (xOf (Lw T L))` is `≤ CTof C T · L^{3/4}`
  at the **`(lococc)`** window `Lw`, not the `(2T+4)L` window of `LocCoordPaper`.
* `loccoord_fixed_of_locsum` (**the conversion**): the paper's display from the family `(locsum)`
  content, with the *explicit* constant `LocCoordPaper.CT p m T` (no new existential `C_T`).
* `familyGood_loccoord_fixed` / `exists_famBad_loccoord_fixed`: the same display off `famBad`
  for **every** nonempty group at the common coefficient `Cmax`, at the same bad-event bound.

## What is *not* claimed

No separation survival, no positivity of the bad event's complement, no `(locmove)`, no
`(block)`, no tightness, speed or `MainClaim`.  The `(locsum)` content is consumed, not proved as
a probabilistic statement here — it is the eighth clause of `exists_famBad_and_good`.
No public source is edited.  No `sorry`, no `native_decide`, no custom axiom.
-/
import Swarm.LocalGoodFamily
import Swarm.L34PaperScale

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccCarrierAssembly
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open Loccoord

namespace PaperLocCoord

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The record clock on the carrier, and the upper end of the `(locsum)` window -/

/-- **`recTimeA` is the paper's record sequence on `ReachAll`.**  This is the local form of
`RowTail.isRecord_recTimeA`, proved from `recTimeA_spec`/`recTimeA_min` and the discrete
intermediate-value property of the running maximum (`RecordoSupply.exists_runMax_eq`). -/
theorem runMax_recTimeA_lt (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N)
    (hR : U ∈ ReachAll (N := N) p m) (r : ℕ) :
    ∀ n < recTimeA p m U r, RecordDefect.runMax (actX p m U) n < (r : ℤ) := by
  intro n hn
  by_contra hcon
  have hge : (r : ℤ) ≤ RecordDefect.runMax (actX p m U) n := not_lt.mp hcon
  obtain ⟨m', hm', hval⟩ := RecordoSupply.exists_runMax_eq (actX p m U)
    (RecordoSupply.actX_step p m U) (RecordoSupply.actX_zero p m U) hge
  exact recTimeA_min p m U r m' (lt_of_le_of_lt hm' hn) (Or.inr hval)

/-- **`recTimeA` is a record sequence on `ReachAll`.** -/
theorem isRecord_recTimeA_of_reachAll (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N)
    (hR : U ∈ ReachAll (N := N) p m) :
    RecordDefect.IsRecord (actX p m U) (recTimeA p m U) :=
  fun r => ⟨runMax_recTimeA_lt p m U hR r,
    (recTimeA_spec p m U r).resolve_left (fun h => h hR)⟩

/-- **On the record window every group record stays at most `r + TL`.**

This is `LocCoordPaper.Rmax_le_nat`'s internal estimate sharpened from `r + (T+2)L` to `r + T*L`,
which is what makes the `(lococc)` window `[A0, A0+Lw) = [r-(T+2)L, r+TL+1)` reach `R_t^B`. -/
theorem runMaxA_le_r_add_TL {p : ℝ} {m r T L τ t : ℕ} {U : Swarming.Uniform.Array N}
    {B : Finset (Fin N)} (hB : B.Nonempty)
    (hlow : ∀ n < τ, RecordDefect.runMax (actX p m U) n < (r : ℤ))
    (hτmax : RecordDefect.runMax (actX p m U) τ = (r : ℤ))
    (hτt : τ ≤ t) (htK : t ≤ τ + T * L) :
    Enl.runMaxA p m U hB t ≤ (((r + T * L : ℕ)) : ℤ) := by
  refine Finset.sup'_le hB (fun k => Swarming.Trajectory.runMax p m U k t) (fun k _ => ?_)
  refine LocCoordPaper.runMax_le_of_pointwise (fun u _ => ?_)
  have hle : actX p m U k u ≤ (r : ℤ) + ((u - τ : ℕ) : ℤ) := by
    by_cases huτ : u ≤ τ
    · have h1 : actX p m U k u ≤ RecordDefect.runMax (actX p m U) u :=
        RecordDefect.le_runMax u k
      have hcast : ((u - τ : ℕ) : ℤ) = 0 := by
        have hzero : u - τ = 0 := by omega
        rw [hzero]; norm_num
      rw [hcast, add_zero]
      rcases lt_or_eq_of_le huτ with hlt | heq
      · have h2 := hlow u hlt
        linarith
      · subst heq
        rw [hτmax] at h1
        exact h1
    · push Not at huτ
      have hstep := LocCoordPaper.actX_step_upper p m U k (le_of_lt huτ)
      have h2 : actX p m U k τ ≤ (r : ℤ) := by
        have h3 := RecordDefect.le_runMax (X := actX p m U) τ k
        rw [hτmax] at h3
        exact h3
      linarith
  have hsub : ((u - τ : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have h1 : u - τ ≤ T * L := by omega
    exact_mod_cast h1
  have hnat : (r : ℤ) + ((T * L : ℕ) : ℤ) = (((r + T * L : ℕ)) : ℤ) := by
    push_cast
    ring
  linarith

/-! ## 2. The `(locsum)` window covers `R_t^B` -/

/-- **`b0 ≤ r + TL` puts `b0` inside `[A0, A0+Lw)`.**  Both branches of the saturating
subtraction in `A0 = r - (T+2)L` are handled: on `(T+2)L ≤ r` by the cast identity
`A0 + Lw = r + TL + 1`, otherwise because `A0 = 0` and `r + TL ≤ (2T+2)L ≤ Lw`. -/
theorem le_A0_add_Lw {r T L b0 : ℕ} (hb : b0 ≤ r + T * L) :
    b0 ≤ A0 r T L + Lw T L := by
  rcases lt_or_ge r ((T + 2) * L) with hr | hr
  · have hA0 : A0 r T L = 0 := by
      unfold A0
      exact Nat.sub_eq_zero_of_le (le_of_lt hr)
    rw [hA0, Nat.zero_add]
    have h2 : r ≤ (T + 2) * L := le_of_lt hr
    have h3 : (T + 2) * L + T * L = (2 * T + 2) * L := by
      rw [← Nat.add_mul]; congr 1; omega
    have h1 : r + T * L ≤ (2 * T + 2) * L := by omega
    have h4 : (2 * T + 2) * L ≤ Lw T L := by
      unfold Lw; omega
    omega
  · have hcast := A0_add_Lw_cast (r := r) (T := T) (L := L) hr
    have h1 : ((b0 : ℕ) : ℤ) ≤ (((r + T * L : ℕ)) : ℤ) := by exact_mod_cast hb
    have h1' : (((r + T * L : ℕ)) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) := by
      push_cast; ring
    rw [h1'] at h1
    have h2 : (((A0 r T L + Lw T L : ℕ)) : ℤ) = (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by
      rw [Nat.cast_add, hcast]
    have h3 : ((b0 : ℕ) : ℤ) ≤ (((A0 r T L + Lw T L : ℕ)) : ℤ) := by rw [h2]; linarith
    exact_mod_cast h3

/-! ## 3. The remainder `3·C·betaT(xOf (Lw T L))` at the `(lococc)` scale -/

/-- **The family `(locsum)` remainder is `C_T L^{3/4}` at the `(lococc)` window `Lw`.**

`LocCoordPaper.betaT_normalise_of` does this at the wider `(locsum)` window `(2T+4)L`; the family
event's pointwise content is at `Lw T L = (2T+2)L + 1`, and `Lw T L ≤ (2T+4)L` for `1 ≤ L`, so the
same constant `CTof C T = 9·C·(2T+4)^{3/4} + 1` serves. -/
theorem three_mul_betaT_Lw_le {C : ℝ} (hC : 0 ≤ C) {T L : ℕ} (hL : 1 ≤ L) :
    3 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ LocCoordPaper.CTof C T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hLw1 : 1 ≤ Lw T L := one_le_Lw T L
  have hβ : ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ 3 * ((Lw T L : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
    LocSumAct.betaT_xOf_le_rpow34 (L := Lw T L) hLw1
  have hnat : Lw T L ≤ (2 * T + 4) * L := by
    have h2L : 1 ≤ 2 * L := by omega
    have hstep : (2 * T + 2) * L + 1 ≤ (2 * T + 2) * L + 2 * L :=
      Nat.add_le_add_left h2L _
    have hsum : (2 * T + 2) * L + 2 * L = (2 * T + 4) * L := by ring
    unfold Lw
    omega
  have hmono : ((Lw T L : ℕ) : ℝ) ≤ (((2 * T + 4) * L : ℕ) : ℝ) := by exact_mod_cast hnat
  have h34 : ((Lw T L : ℕ) : ℝ) ^ (3 / 4 : ℝ)
      ≤ ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmono (by norm_num)
  have hβ2 : ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ 3 * ((((2 * T + 4) * L : ℕ)) : ℝ) ^ (3 / 4 : ℝ) := by linarith
  have hcast : ((((2 * T + 4) * L : ℕ)) : ℝ) = (((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ) := by
    push_cast; ring
  have hsplit : ((((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ)) ^ (3 / 4 : ℝ)
      = ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have h1 : 3 * C * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ 3 * C * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
          * (L : ℝ) ^ (3 / 4 : ℝ))) := by
    rw [← hsplit, ← hcast]
    have h3 : (0 : ℝ) ≤ 3 * C := by linarith
    nlinarith [hβ2, h3]
  have h2 : 3 * C * (3 * ((((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)
      * (L : ℝ) ^ (3 / 4 : ℝ)))
      = (9 * C * (((2 * T + 4 : ℕ)) : ℝ) ^ (3 / 4 : ℝ)) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    ring
  rw [h2] at h1
  unfold LocCoordPaper.CTof
  nlinarith [h1, hLnn]


/-! ## 4. The paper's single-time spatial `(loccoord)` from the family `(locsum)` content -/

/-- **The paper's `(loccoord)` display, transported from the family `(locsum)` content.**

This is `main_1d_revised.tex`, proof of Proposition `local`, `(loccoord)`:

  `H_t^B(b0) - H_t^B(a0) ≤ C (b0 - a0) + C_T L^{3/4}`

for `r - (T+2)L ≤ a0 ≤ b0 ≤ R_t^B` and `τ_r ≤ t ≤ τ_r + TL`, **single time**, from

* the leader `i ∈ B` with `M_t^i = R_t^B` (`Finset.exists_mem_eq_sup'`),
* `(hcomp)` `h^B ≤ h_i` below the leader's record (`Loccoord.loccoord_fixed`),
* the pointwise `(locsum)` content `hsum` at the `(lococc)` window `[A0, A0+Lw)`,
* the bridge `h_i = hof (siteMarks i)` (`Loccoord.hfix_omegaN_eq_hof`).

The coefficient is `Cmax = (2 CUmax + 1)/2` and the error is the **explicit**
`C_T = LocCoordPaper.CT p m T = 9·Ccan·(2T+4)^{3/4} + 1`; there is no new existential constant.
The range facts `b0 ≤ r + TL` (hence `b0 ≤ A0 + Lw`) come from `recordCarrier`, not from a premise.
-/
theorem loccoord_fixed_of_locsum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Swarming.Uniform.Array N} (hL : 1 ≤ L)
    (hsum : ∀ j : Fin N, ∀ a0 b0 : ℕ,
      A0 r T L ≤ a0 → b0 ≤ A0 r T L + Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
    (hcarrier : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {B : Finset (Fin N)} (hB : B.Nonempty) {t : ℕ}
    (hτt : recTimeA p m U r ≤ t) (htK : t ≤ recTimeA p m U r + T * L)
    {a0 b0 : ℕ} (ha0 : r - (T + 2) * L ≤ a0) (hab : a0 ≤ b0)
    (hb0 : (b0 : ℤ) ≤ Enl.runMaxA p m U hB t) :
    HA p m U t B (b0 : ℤ) - HA p m U t B (a0 : ℤ)
      ≤ LocalGoodFamily.Cmax (N := N) p m * ((b0 : ℝ) - (a0 : ℝ))
        + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hp0' : p ≠ 0 := by linarith
  have hrec := isRecord_recTimeA_of_reachAll p m U hcarrier.1
  -- `b0 ≤ R_t^B ≤ r + TL ≤ A0 + Lw`: the `(locsum)` window covers `[a0,b0)`
  have hbTL : b0 ≤ r + T * L := by
    have h1 : Enl.runMaxA p m U hB t ≤ (((r + T * L : ℕ)) : ℤ) :=
      runMaxA_le_r_add_TL hB (hrec r).1 (hrec r).2 hτt htK
    have h2 : (b0 : ℤ) ≤ (((r + T * L : ℕ)) : ℤ) := le_trans hb0 h1
    exact_mod_cast h2
  have hbLw : b0 ≤ A0 r T L + Lw T L := le_A0_add_Lw hbTL
  -- the leader realising `R_t^B`
  obtain ⟨i, hiB, hieq⟩ := Finset.exists_mem_eq_sup' hB
    (fun k => Swarming.Trajectory.runMax p m U k t)
  have hbR : (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t := by
    rw [← hieq]
    exact hb0
  -- the leader's squared-site sum, in `hfix` coordinates
  have hsumFix : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
        + 2 * LocOccSiteRate.Ccan p m
            * (3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) := by
    have h0 := hsum i a0 b0 (show A0 r T L ≤ a0 from ha0) hbLw hab
    have hcongr : (∑ x ∈ Finset.Ico a0 b0,
          (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2)
        = ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U i) x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [Loccoord.hfix_omegaN_eq_hof hp0' i x]
    rw [hcongr]
    nlinarith [h0]
  have hmain := Loccoord.loccoord_fixed (p := p) (m := m) (N := N) (le_of_lt hp0) (le_of_lt hp1)
    U (n := t) (B := B) (i := i) hiB hab hbR
    (K := 2 * LocOccSiteRate.Ccan p m)
    (β := 3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
    (by linarith [LocOccSiteRate.one_le_Ccan p m]) (by positivity) hsumFix
  -- the common coefficient `Cmax` dominates `(2 Ccan + 1)/2`
  have hCUle : LocOccSiteRate.Ccan p m ≤ RecordGroupUniform.CUmax N p m :=
    (LocalGood.Ccan_le_CU (N := N) p m (∅ : Finset (Fin N))).trans
      (RecordGroupUniform.CU_le_CUmax (N := N) p m ∅)
  have hcoef : ((2 * LocOccSiteRate.Ccan p m + 1) / 2)
      ≤ LocalGoodFamily.Cmax (N := N) p m := by
    unfold LocalGoodFamily.Cmax RecordGroupUniform.commonCoordCoefficient
    linarith
  have hdiff : (0 : ℝ) ≤ (b0 : ℝ) - (a0 : ℝ) := by
    have hle : (a0 : ℝ) ≤ (b0 : ℝ) := by exact_mod_cast hab
    linarith
  have hstep : ((2 * LocOccSiteRate.Ccan p m + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ))
      ≤ LocalGoodFamily.Cmax (N := N) p m * ((b0 : ℝ) - (a0 : ℝ)) :=
    mul_le_mul_of_nonneg_right hcoef hdiff
  -- the remainder is `C_T L^{3/4}` at the `(lococc)` window
  have hrem : 3 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1 : 3 * LocCoordPaper.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
        ≤ LocCoordPaper.CTof (LocCoordPaper.Ccan p m) T * (L : ℝ) ^ (3 / 4 : ℝ) :=
      three_mul_betaT_Lw_le (le_trans zero_le_one (LocCoordPaper.one_le_Ccan p m)) hL
    have h2 : LocCoordPaper.CTof (LocCoordPaper.Ccan p m) T
        = LocCoordPaper.CT p m T := (LocCoordPaper.CT_eq_CTof_Ccan p m T).symm
    rw [h2] at h1
    exact h1
  have hK : (2 * LocOccSiteRate.Ccan p m / 2) * (3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
      = 3 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ) := by ring
  linarith [hmain, hstep, hrem, hK]

/-! ## 5. From the public `(locsum)` bad event to the display -/

/-- The `(locsum)` pointwise content at the `(lococc)` window, off the public `(locsum)` bad set
`sumBadOcc` — the eighth clause of `exists_famBad_and_good`, factored out with its threshold. -/
theorem exists_locsum_content_of_sumBadOcc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Swarming.Uniform.Array N,
      U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L →
      (∀ j : Fin N, ∀ a0 b0 : ℕ,
        A0 r T L ≤ a0 → b0 ≤ A0 r T L + Lw T L → a0 ≤ b0 →
        ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
            + 6 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) ∧
      1 ≤ L := by
  obtain ⟨c₉, -, L₉, h₉⟩ :=
    LocSumR1.array_locsum_h_start (N := N) hp0 hp1 hm
      (C := LocOccSiteRate.Ccan p m) (LocOccSiteRate.one_le_Ccan p m)
      (LocOccSiteRate.Mb_lt_Ccan p m)
  obtain ⟨L₁₀, hL₁₀⟩ := LocOccCarrierAssembly.exists_two_mul_ellT_xOf_Lw_le T
  refine ⟨max (max L₉ L₁₀) 1, ?_⟩
  intro L hL r hr U hU
  have hL9 : L₉ ≤ L := by omega
  have hL10 : L₁₀ ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  refine ⟨?_, hL1⟩
  intro j a0 b0 ha0 hb0 hab
  have hside : 2 * ellT (LocSumAct.xOf (Lw T L)) ≤ A0 r T L := by
    have hArith : L + (T + 2) * L ≤ r := by
      have hEq : L + (T + 2) * L = (T + 3) * L := by ring
      rw [hEq]
      exact hr
    have hLA0 : L ≤ A0 r T L := by
      unfold A0
      exact Nat.le_sub_of_add_le hArith
    exact le_trans (hL₁₀ L hL10) hLA0
  exact (h₉ (Lw T L) (le_trans hL9 (LocOccCarrierAssembly.le_Lw T L))
    (A0 r T L) hside).2 U hU j a0 b0 ha0 hb0 hab

/-- **The paper's `(loccoord)` off the public `(locsum)` bad set `sumBadOcc`.** -/
theorem exists_loccoord_fixed_of_sumBadOcc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Swarming.Uniform.Array N,
      U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L →
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (t : ℕ),
        recTimeA p m U r ≤ t → t ≤ recTimeA p m U r + T * L →
        ∀ a0 b0 : ℕ, r - (T + 2) * L ≤ a0 → a0 ≤ b0 →
          (b0 : ℤ) ≤ Enl.runMaxA p m U hB t →
          HA p m U t B (b0 : ℤ) - HA p m U t B (a0 : ℤ)
            ≤ LocalGoodFamily.Cmax (N := N) p m * ((b0 : ℝ) - (a0 : ℝ))
              + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨L₀, hL₀⟩ := exists_locsum_content_of_sumBadOcc (N := N) hp0 hp1 hm T
  refine ⟨L₀, ?_⟩
  intro L hL r hr U hU hcarr B hB t hτt htK a0 b0 ha0 hab hb0
  obtain ⟨hsum, hL1⟩ := hL₀ L hL r hr U hU
  exact loccoord_fixed_of_locsum hp0 hp1 hL1 hsum hcarr hB hτt htK ha0 hab hb0

/-- **`(loccoord)` off the finite-family bad event, for every nonempty group.**  The analogue of
`LocalGoodFamily.familyGood_loccoord` in the paper's own shape: single time, spatial, coefficient
`Cmax`, explicit error `C_T L^{3/4}`. -/
theorem familyGood_loccoord_fixed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ {Cerr : ℝ}
      {moveFam : Finset (Finset (Fin N))} {hne : ∀ A ∈ moveFam, A.Nonempty}
      {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
      {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
      {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty},
      ∀ U : Swarming.Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (t : ℕ),
        recTimeA p m U r ≤ t → t ≤ recTimeA p m U r + T * L →
        ∀ a0 b0 : ℕ, r - (T + 2) * L ≤ a0 → a0 ≤ b0 →
          (b0 : ℤ) ≤ Enl.runMaxA p m U hB t →
          HA p m U t B (b0 : ℤ) - HA p m U t B (a0 : ℤ)
            ≤ LocalGoodFamily.Cmax (N := N) p m * ((b0 : ℝ) - (a0 : ℝ))
              + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨L₀, hL₀⟩ := exists_loccoord_fixed_of_sumBadOcc (N := N) hp0 hp1 hm T
  refine ⟨L₀, ?_⟩
  intro L hL r hr Cerr moveFam hne hco grpFam hI hJ U hcarr hnot B hB t hτt htK a0 b0 ha0 hab hb0
  have hsumBad : U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L :=
    (LocalGoodFamily.not_mem_commonBad (N := N)
      (LocalGoodFamily.not_mem_famBad (N := N) hnot).1.1).1
  exact hL₀ L hL r hr U hsumBad hcarr B hB t hτt htK a0 b0 ha0 hab hb0

/-! ## 6. The headline: one measured family event, the paper's `(loccoord)` off it -/

/-- **The finite-family headline with the paper-form `(loccoord)`.**

Same quantified data as `LocalGoodFamily.exists_famBad_and_good` — one `Cerr ≥ 1`, one exponential
bound `CT * exf cT L` for the single bad event `famBad`, one threshold — but the `(loccoord)` clause
is now the paper's **single-time spatial** display at the common coefficient `Cmax` and the explicit
error `C_T = LocCoordPaper.CT p m T`, for every nonempty `B ⊆ Fin N` and every window
`τ_r ≤ t ≤ τ_r + TL`. -/
theorem exists_famBad_loccoord_fixed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧
      (∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
        ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
          (arrayMeasure N).real
              (LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
            ≤ CT * LocalGoodAll.exf cT L) ∧
      ∃ Lg : ℕ, ∀ L ≥ Lg, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Swarming.Uniform.Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
        ∀ (B : Finset (Fin N)) (hB : B.Nonempty) (t : ℕ),
          recTimeA p m U r ≤ t → t ≤ recTimeA p m U r + T * L →
          ∀ a0 b0 : ℕ, r - (T + 2) * L ≤ a0 → a0 ≤ b0 →
            (b0 : ℤ) ≤ Enl.runMaxA p m U hB t →
            HA p m U t B (b0 : ℤ) - HA p m U t B (a0 : ℤ)
              ≤ LocalGoodFamily.Cmax (N := N) p m * ((b0 : ℝ) - (a0 : ℝ))
                + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨Cerr, hCerr1, hbad, _Lg₀, _hgood⟩ :=
    LocalGoodFamily.exists_famBad_and_good (N := N) hp0 hp1 hm hT hN moveFam hne hco grpFam
      hI hJ hdisj
  obtain ⟨L₁, hL₁⟩ := familyGood_loccoord_fixed (N := N) hp0 hp1 hm T
  refine ⟨Cerr, hCerr1, hbad, L₁, ?_⟩
  intro L hL r hr U hcarr hnot B hB t hτt htK a0 b0 ha0 hab hb0
  exact hL₁ L hL r hr U hcarr hnot B hB t hτt htK a0 b0 ha0 hab hb0


/-! ## 7. The `(loccoord)` shape consumed by `(locmove)`, with the geometry derived -/

/-- **The defect at the record time, from `recordCarrier`.**  (The carrier stores the defect as a
`toNat` inequality; this is the `ℤ` form used by `Xmin_ge_int`.) -/
theorem defect_le_of_carrier {p : ℝ} {m r L : ℕ} {U : Swarming.Uniform.Array N}
    (hcarrier : U ∈ RecClockLG.recordCarrier (N := N) p m r L) :
    (r : ℤ) - runMin (actX p m U) (recTimeA p m U r) ≤ (L : ℤ) :=
  Int.toNat_le.mp hcarrier.2

/-- **The range facts `locCoordGeom` holds from `recordCarrier` alone.**  All three components are
derived: `0 ≤ Xmin` and `A0 ≤ Xmin.toNat` from the defect bound and the unit step, and
`Rmax.toNat ≤ r + (T+2)L` from the record structure.  No separation, no `(locsum)` content and no
probability enters. -/
theorem locCoordGeom_of_carrier {p : ℝ} {m r T L : ℕ} {U : Swarming.Uniform.Array N}
    {B : Finset (Fin N)} (hB : B.Nonempty) {s t : ℕ}
    (hr : (T + 3) * L ≤ r)
    (hcarrier : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hτs : recTimeA p m U r ≤ s) (hst : s ≤ t)
    (htK : t ≤ recTimeA p m U r + T * L) :
    U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t := by
  have hTL : (T + 2) * L ≤ r := LocOccCarrierAssembly.T2L_le_r hr
  have hrec := isRecord_recTimeA_of_reachAll p m U hcarrier.1
  have hdef := defect_le_of_carrier (N := N) hcarrier
  have hXge : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ Xmin p m U B hB s :=
    LocCoordPaper.Xmin_ge_int hB hdef hτs (le_trans hst htK)
  have hcast0 : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hTL
  have hX0 : (0 : ℤ) ≤ Xmin p m U B hB s := by linarith
  have hAle : A0 r T L ≤ (Xmin p m U B hB s).toNat := by
    refine (Int.le_toNat hX0).2 ?_
    have hcast : ((A0 r T L : ℕ) : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) :=
      A0_cast hTL
    rw [hcast]
    exact hXge
  have hLb : (Enl.runMaxA p m U hB t).toNat ≤ r + (T + 2) * L :=
    LocCoordPaper.Rmax_le_nat (t := t) (B := B) hB (hrec r).1 (hrec r).2
      (le_trans hτs hst) htK
  exact ⟨hX0, hAle, hLb⟩

/-- **The `(loccoord)` display in the averaged extremal shape used by `(locmove)`:**

  `average_{k∈B} (H_t^B(X_t^k) - H_s^B(X_s^k)) ≤ C (R_t^B - min_{k∈B} X_s^k) + C_T L^{3/4}`,

from the family `(locsum)` content, at the common coefficient `Cmax` and the explicit
`C_T = LocCoordPaper.CT p m T` — and with **no `locCoordGeom` premise**: the range facts are derived
from `recordCarrier` (`locCoordGeom_of_carrier`). -/
theorem loccoord_average_of_locsum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r T L : ℕ} {U : Swarming.Uniform.Array N} (hL : 1 ≤ L)
    (hsum : ∀ j : Fin N, ∀ a0 b0 : ℕ,
      A0 r T L ≤ a0 → b0 ≤ A0 r T L + Lw T L → a0 ≤ b0 →
      ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
          + 6 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
    (hr : (T + 3) * L ≤ r)
    (hcarrier : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    {B : Finset (Fin N)} (hB : B.Nonempty) {s t : ℕ}
    (hτs : recTimeA p m U r ≤ s) (hst : s ≤ t)
    (htK : t ≤ recTimeA p m U r + T * L) :
    Swarming.Group.average B
        (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
      ≤ LocalGoodFamily.Cmax (N := N) p m
          * (((Enl.runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
        + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  have hp0' : p ≠ 0 := by linarith
  have hTL : (T + 2) * L ≤ r := LocOccCarrierAssembly.T2L_le_r hr
  have hrec := isRecord_recTimeA_of_reachAll p m U hcarrier.1
  have hdef := defect_le_of_carrier (N := N) hcarrier
  obtain ⟨hX0a, hAle, hLb⟩ :
      (0 : ℤ) ≤ Xmin p m U B hB s ∧ A0 r T L ≤ (Xmin p m U B hB s).toNat ∧
        (Enl.runMaxA p m U hB t).toNat ≤ r + (T + 2) * L := by
    have hg := locCoordGeom_of_carrier (N := N) hB hr hcarrier hτs hst htK
    exact ⟨hg.1, hg.2.1, hg.2.2⟩
  -- the `(locsum)` bound on the extremal interval
  have hsumB : ∀ i ∈ B,
      ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * LocOccSiteRate.Ccan p m
          * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
        + 2 * LocOccSiteRate.Ccan p m
            * (3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)) := by
    intro i _
    have hmono : (Xmin p m U B hB s).toNat ≤ (Rmax p m U B hB t).toNat :=
      Int.toNat_le_toNat (Xmin_le_Rmax (p := p) (m := m) U hB hst)
    have hbLw : (Rmax p m U B hB t).toNat ≤ A0 r T L + Lw T L := by
      have h1 : (Loccoord.Rmax p m U B hB t).toNat ≤ r + T * L := by
        have h2 : Loccoord.Rmax p m U B hB t ≤ (((r + T * L : ℕ)) : ℤ) :=
          runMaxA_le_r_add_TL (t := t) hB (hrec r).1 (hrec r).2 (le_trans hτs hst) htK
        rw [Int.toNat_le]
        exact h2
      have h3 : r + T * L ≤ A0 r T L + Lw T L := le_A0_add_Lw (le_refl (r + T * L))
      omega
    have h0 := hsum i (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat hAle hbLw hmono
    have hbridge : (∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat
          (Rmax p m U B hB t).toNat,
          (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2)
        = ∑ x ∈ Finset.Ico (Xmin p m U B hB s).toNat (Rmax p m U B hB t).toNat,
            (hof p (siteMarks p m U i) x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [Loccoord.hfix_omegaN_eq_hof hp0' i x]
    rw [hbridge]
    -- `Int.toNat` casts are the genuine differences because both ends are nonnegative
    have hRnonneg : (0 : ℤ) ≤ Loccoord.Rmax p m U B hB t :=
      le_trans hX0a (Xmin_le_Rmax (p := p) (m := m) U hB hst)
    have hXn : ((((Loccoord.Xmin p m U B hB s).toNat : ℕ)) : ℝ)
        = ((Loccoord.Xmin p m U B hB s : ℤ) : ℝ) := by
      have h3 : (((Loccoord.Xmin p m U B hB s).toNat : ℕ) : ℤ)
          = Loccoord.Xmin p m U B hB s := Int.toNat_of_nonneg hX0a
      exact_mod_cast h3
    have hRn : ((((Loccoord.Rmax p m U B hB t).toNat : ℕ)) : ℝ)
        = ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) := by
      have h3 : (((Loccoord.Rmax p m U B hB t).toNat : ℕ) : ℤ)
          = Loccoord.Rmax p m U B hB t := Int.toNat_of_nonneg hRnonneg
      exact_mod_cast h3
    rw [hXn, hRn] at h0
    nlinarith [h0]
  have hmain := Loccoord.loccoord_range_of_hsum (p := p) (m := m) (N := N) (le_of_lt hp0)
    (le_of_lt hp1) U hB hst hX0a
    (K := 2 * LocOccSiteRate.Ccan p m)
    (β := 3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
    (by linarith [LocOccSiteRate.one_le_Ccan p m]) (by positivity) hsumB
  -- coefficient and remainder
  have hCUle : LocOccSiteRate.Ccan p m ≤ RecordGroupUniform.CUmax N p m :=
    (LocalGood.Ccan_le_CU (N := N) p m (∅ : Finset (Fin N))).trans
      (RecordGroupUniform.CU_le_CUmax (N := N) p m ∅)
  have hcoef : ((2 * LocOccSiteRate.Ccan p m + 1) / 2)
      ≤ LocalGoodFamily.Cmax (N := N) p m := by
    unfold LocalGoodFamily.Cmax RecordGroupUniform.commonCoordCoefficient
    linarith
  have hdiff : (0 : ℝ)
      ≤ ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ) := by
    have h1 : Xmin p m U B hB s ≤ Loccoord.Rmax p m U B hB t :=
      Xmin_le_Rmax (p := p) (m := m) U hB hst
    have h2 : ((Xmin p m U B hB s : ℤ) : ℝ) ≤ ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hstep : ((2 * LocOccSiteRate.Ccan p m + 1) / 2)
      * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
      ≤ LocalGoodFamily.Cmax (N := N) p m
        * (((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hcoef hdiff
  have hrem : 3 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
      ≤ LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
    have h1 : 3 * LocCoordPaper.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ)
        ≤ LocCoordPaper.CTof (LocCoordPaper.Ccan p m) T * (L : ℝ) ^ (3 / 4 : ℝ) :=
      three_mul_betaT_Lw_le (le_trans zero_le_one (LocCoordPaper.one_le_Ccan p m)) hL
    have h2 : LocCoordPaper.CTof (LocCoordPaper.Ccan p m) T
        = LocCoordPaper.CT p m T := (LocCoordPaper.CT_eq_CTof_Ccan p m T).symm
    rw [h2] at h1
    exact h1
  have hK : (2 * LocOccSiteRate.Ccan p m / 2) * (3 * ((betaT (xOf (Lw T L)) : ℕ) : ℝ))
      = 3 * LocOccSiteRate.Ccan p m * ((betaT (xOf (Lw T L)) : ℕ) : ℝ) := by ring
  have hRw : ((Loccoord.Rmax p m U B hB t : ℤ) : ℝ) = ((Enl.runMaxA p m U hB t : ℤ) : ℝ) := rfl
  rw [hRw] at hmain hstep
  linarith [hmain, hstep, hrem, hK]

/-- **The `(loccoord)` average/extremal form off `sumBadOcc`.** -/
theorem exists_loccoord_average_of_sumBadOcc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Swarming.Uniform.Array N,
      U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L →
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) {s t : ℕ},
        recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        Swarming.Group.average B
            (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
          ≤ LocalGoodFamily.Cmax (N := N) p m
              * (((Enl.runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
            + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨L₀, hL₀⟩ := exists_locsum_content_of_sumBadOcc (N := N) hp0 hp1 hm T
  refine ⟨L₀, ?_⟩
  intro L hL r hr U hU hcarr B hB s t hτs hst htK
  obtain ⟨hsum, hL1⟩ := hL₀ L hL r hr U hU
  exact loccoord_average_of_locsum hp0 hp1 hL1 hsum hr hcarr hB hτs hst htK

/-- **The `(loccoord)` average/extremal form off the finite-family bad event, without the
`locCoordGeom` premise.**  This is `LocalGoodFamily.familyGood_loccoord`'s display with the error
`Cerr L^{3/4}` replaced by the explicit `C_T L^{3/4} = LocCoordPaper.CT p m T · L^{3/4}`, and with
`locCoordGeom` *derived* from `recordCarrier` rather than assumed. -/
theorem familyGood_loccoord_average {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ {Cerr : ℝ}
      {moveFam : Finset (Finset (Fin N))} {hne : ∀ A ∈ moveFam, A.Nonempty}
      {hco : ∀ A ∈ moveFam, Aᶜ.Nonempty}
      {grpFam : Finset (Finset (Fin N) × Finset (Fin N))}
      {hI : ∀ q ∈ grpFam, q.1.Nonempty} {hJ : ∀ q ∈ grpFam, q.2.Nonempty},
      ∀ U : Swarming.Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ LocalGoodFamily.famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty) {s t : ℕ},
        recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        Swarming.Group.average B
            (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
          ≤ LocalGoodFamily.Cmax (N := N) p m
              * (((Enl.runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
            + LocCoordPaper.CT p m T * (L : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨L₀, hL₀⟩ := exists_loccoord_average_of_sumBadOcc (N := N) hp0 hp1 hm T
  refine ⟨L₀, ?_⟩
  intro L hL r hr Cerr moveFam hne hco grpFam hI hJ U hcarr hnot B hB s t hτs hst htK
  have hsumBad : U ∉ LocalGoodAll.sumBadOcc (N := N) p m r T L :=
    (LocalGoodFamily.not_mem_commonBad (N := N)
      (LocalGoodFamily.not_mem_famBad (N := N) hnot).1.1).1
  exact hL₀ L hL r hr U hsumBad hcarr B hB hτs hst htK

end PaperLocCoord
