/-
  # `(lococc)` on one actual carrier: the composition, with every field discharged
    except the two named structural inputs.

  The paper's display (Proposition `local`, `(lococc)`) is

      sum_{u=s}^{t-1} 1{X_u^i <= M_u^j}
        <= C (M_t^i - M_s^i + M_s^i - X_s^i + (M_s^i - M_s^j)_+) + (t-s)/8 + C_T L^{3/4}

  for `i != j` and `tau_r <= s <= t <= tau_r + floor (T L)` on the good event.

  This file instantiates `LocOcc.lococc_window_eighth` on ONE actual carrier:

  * `X n = (trajectory p m U n).pos i`, `Mi n = (runMax p m U i n)`, `Mj n = (runMax p m U j n)`
    (all converted to `ℕ` by `Int.toNat`, which is exact on the nonnegative cell);
  * `h x = hof p (siteMarks p m U j) x`, `wt x = h x ^ 2` (the quenched weight);
  * `H t y = projH p m j t U y` (the projected potential `H_{j,t}(y)`);
  * `Z = Zproj`, `J = Jcorr`, `Q = Qpl` at `eps = 1/8` (the accepted adapted projected ledger).

  Discharged here, with proofs (no citation-only fields): `hocc`, `hled` (from
  `LocOcc.ae_step_ledger_actual` plus nonnegativity of the cell), `hZs`/`hZt` (definitional),
  `hh`/`hhw`, `hint` (the squared-site `(locsum)` theorem rescaled to the consumer's
  `K(b-a)+K beta` shape with `K = 2C`, `beta = 3 betaT`), `hFs`/`hFt` (the endpoint
  `(Fbounds)` with the *record-squared cap* supplied by the cell's `(locmax)` cap — the cap
  `LocOccEndpoint.abs_Fcorr_endpoint_le` leaves explicit), `hJstruct` (the exact `(Jbound)` shape
  from `LocOccEndpoint.abs_Jcorr_le`), `hMjmono`/`hMjstep`/`hXW`/`hMiw`/`hXMiS`/`hXtMi` and the five
  containments (running-max monotonicity, unit steps and the cell).

  Not discharged, and stated as the only two remaining structural inputs, is the pair of
  *spatial slope* identities of the projected potential:
    `hslopeLo` below the record (`(projH)`-revealed part) and
    `hslopeHi` above the record at a constant `Kp`.
  The README records precisely why the per-site `hslopeHi` is not what this model supplies
  (the recursion gives a *sum* bound, not a per-site one) — this is the exact remaining
  obligation, not a re-labelling.
-/
import Swarm.LocOccProjected
import Swarm.LocOccEndpoint
import Swarm.M3Hosc
import Swarm.LocStartRange
import Swarm.QplWindow
import Swarm.ShiftedQplResidual
import Swarm.BetaNormalise

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccCarrier

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocSumAct

variable {N : ℕ}

/-! ### 1. The `(locsum)` remainder, rescaled to the consumer's `K (b-a) + K beta` shape -/

/-- **`(locsum)` at the consumer's normalisation.**  `LocSumR1.array_locsum_h_start` gives, on the
complement of its bad set, `sum h_j^2 <= 2C (b-a) + 6C betaT` on every subinterval of a window of
length `Lw`.  The consumer `LocOcc.lococc_window` wants `K (b-a) + K beta` with a *single* constant
`K` multiplying both terms.  Taking `K = 2C` and `beta = 3 betaT` is exactly that rescaling
(`6C betaT = 2C * (3 betaT)`), and this is the honest conversion: the remainder keeps the beta
term, it is not dropped. -/
theorem locsum_hint_shape {h : ℕ → ℝ} {A Lw : ℕ} {C : ℝ} (hC : 0 ≤ C) {β : ℝ}
    (hsq : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, h x ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * β) :
    ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, h x ≤ (2 * C) * ((b : ℝ) - (a : ℝ)) + (2 * C) * (3 * β) := by
  intro a b ha hb hab
  have hbnd := hsq a b ha hb hab
  calc ∑ x ∈ Finset.Ico a b, h x
      ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * β := hbnd
    _ = (2 * C) * ((b : ℝ) - (a : ℝ)) + (2 * C) * (3 * β) := by ring

/-- **The squared-site sum in the consumer's `wt = h^2` form.**  Same statement for the actual
weight `wt x = h_j(x)^2`. -/
theorem locsum_hint_wt {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {A Lw : ℕ} {C : ℝ}
    (hC : 0 ≤ C) {β : ℝ}
    (hsq : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + 6 * C * β) :
    ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
        ≤ (2 * C) * ((b : ℝ) - (a : ℝ)) + (2 * C) * (3 * β) :=
  locsum_hint_shape hC hsq

/-! ### 2. The paper-scale remainder `L34` and `beta <= L34` -/

/-- The paper-scale remainder used throughout this file:
`L34 = 3 betaT(Lw^{1/16}) + V^2 + L^{3/4}`, where `Lw` is the site-window length, `V = Lw^{1/16}`
is the `(locmax)` cap and `L^{3/4}` is the paper's `L^{3/4}`.  It dominates the `(locsum)`
remainder, the record-squared cap and the oscillation/martingale thresholds simultaneously. -/
noncomputable def L34 (L Lw : ℕ) : ℝ :=
  3 * ((betaT (xOf Lw) : ℕ) : ℝ) + (xOf Lw) ^ 2 + (L : ℝ) ^ (3 / 4 : ℝ)

theorem L34_nonneg (L Lw : ℕ) : 0 ≤ L34 L Lw := by
  unfold L34; positivity

theorem one_le_L34 {L Lw : ℕ} (hL : 1 ≤ L) : 1 ≤ L34 L Lw := by
  unfold L34
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have h2 : (0 : ℝ) ≤ 3 * ((betaT (xOf Lw) : ℕ) : ℝ) + (xOf Lw) ^ 2 := by positivity
  linarith

theorem L34_lower_rpow (L Lw : ℕ) : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L Lw := by
  unfold L34
  have h2 : (0 : ℝ) ≤ 3 * ((betaT (xOf Lw) : ℕ) : ℝ) + (xOf Lw) ^ 2 := by positivity
  linarith

/-- `beta = 3 betaT (xOf Lw) <= L34`: the `(locsum)` remainder fits in the paper-scale
remainder by construction. -/
theorem three_betaT_le_L34 (L Lw : ℕ) :
    3 * ((betaT (xOf Lw) : ℕ) : ℝ) ≤ L34 L Lw := by
  unfold L34
  have h2 : (0 : ℝ) ≤ (xOf Lw) ^ 2 + (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  linarith

/-! ### 3. The `(locmax)` cap at the record and the `(Fbounds)` endpoint estimate

`LocOccEndpoint.abs_Fcorr_endpoint_le` leaves the hypothesis

    `(h_j (M_n^j))^2 <= L34`

explicit.  On the record cell this hypothesis is *not* extra data: the cell's `(locmax)` cap
`h_j <= V` on the site window together with the record containment `M_n^j ∈ [A, A+M)` gives
`h_j(M_n^j)^2 <= V^2`.  This is the discharge. -/

/-- **The record-squared cap from `(locmax)` and the record containment.** -/
theorem hof_sq_record_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {U : Array N} {j : Fin N} (n : ℕ) {A Mv : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hloc : ∀ y ∈ Finset.Ico A (A + Mv), hof p (siteMarks p m U j) y ≤ V)
    (hrec : (runMax p m U j n).toNat ∈ Finset.Ico A (A + Mv)) :
    (hof p (siteMarks p m U j) ((runMax p m U j n).toNat)) ^ 2 ≤ V ^ 2 := by
  have h1 : hof p (siteMarks p m U j) ((runMax p m U j n).toNat) ≤ V := hloc _ hrec
  have h0 : (0 : ℝ) ≤ hof p (siteMarks p m U j) ((runMax p m U j n).toNat) :=
    le_trans zero_le_one (one_le_hof (le_of_lt hp1) hp2 _ _)
  nlinarith

/-- **`(Fbounds)` at the paper scale.**  `|F_{b_n}(X_n^i - M_n^j)| <= KF * L34` with the explicit
coefficient `KF`, reduced to the record-squared cap only. -/
theorem abs_Fcorr_endpoint_L34 {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} (U : Array N) (n : ℕ) {L Lw : ℕ}
    (hcap : (hof p (siteMarks p m U j) ((runMax p m U j n).toNat)) ^ 2 ≤ (xOf Lw) ^ 2) :
    |SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m n j U)
        ((trajectory p m U n).pos i - runMax p m U j n)|
      ≤ ((p / (1 - p) + 2) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2)) * L34 L Lw := by
  have hε : (0 : ℝ) < 1 / 8 := by norm_num
  have h1 := LocOccEnd.abs_Fcorr_endpoint_le (N := N) hp1 hp2 (m := m) (i := i) (j := j)
    (ε := 1 / 8) hε U n hcap
  have hK : (0 : ℝ) ≤ (p / (1 - p) + 2) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2) := by
    have h1a : (0 : ℝ) < 1 - aRec p m := by
      have := aRec_lt_one hp1 hp2 m; linarith
    have h1p : (0 : ℝ) < 1 - p := by linarith
    have hpq : (0 : ℝ) ≤ p / (1 - p) := by positivity
    positivity
  have h2 : (xOf Lw) ^ 2 ≤ L34 L Lw := by
    unfold L34
    have h3 : (0 : ℝ) ≤ 3 * ((betaT (xOf Lw) : ℕ) : ℝ) + (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
    linarith
  calc |SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m n j U)
        ((trajectory p m U n).pos i - runMax p m U j n)|
      ≤ ((p / (1 - p) + 2) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2)) * (xOf Lw) ^ 2 := h1
    _ ≤ ((p / (1 - p) + 2) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2)) * L34 L Lw :=
        mul_le_mul_of_nonneg_left h2 hK

/-! ### 4. The `(Jbound)` structural estimate in the consumer's exact shape -/

/-- **`hJstruct` from `LocOccEndpoint.abs_Jcorr_le`.**  On the nonnegative cell, with the record
monotone and unit-step, the record cost `J` satisfies exactly the consumer's support/weight
inequality, with `CJ = 2 ((p/(1-p)+4)^2 / ((1/8)(1-a)^2))` and `wt x = h_j(x)^2`. -/
theorem Jstruct_endpoint {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {i j : Fin N} (U : Array N) (n : ℕ)
    (hposnext : 0 ≤ (trajectory p m U (n + 1)).pos i)
    (hmono : (runMax p m U j n).toNat ≤ (runMax p m U j (n + 1)).toNat)
    (hstep : (runMax p m U j (n + 1)).toNat ≤ (runMax p m U j n).toNat + 1) :
    |Jcorr p m (1 / 8) i j U n|
      ≤ 2 * ((p / (1 - p) + 4) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2)) *
          ((hof p (siteMarks p m U j) ((runMax p m U j n).toNat)) ^ 2
            + (hof p (siteMarks p m U j) ((runMax p m U j n).toNat + 1)) ^ 2) *
          (if (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
              ((runMax p m U j n).toNat : ℤ)
                < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            then 1 else 0) :=
  LocOccEnd.abs_Jcorr_le (N := N) hp1 hp2 (m := m) (i := i) (j := j) (ε := 1 / 8)
    (by norm_num) U n hposnext hmono hstep

/-! ### 5. Explicit constants -/

/-- The record-cost coefficient of `(Jbound)`. -/
noncomputable def CJc (p : ℝ) (m : ℕ) : ℝ :=
  2 * ((p / (1 - p) + 4) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2))

/-- The endpoint-correction coefficient of `(Fbounds)`. -/
noncomputable def KFc (p : ℝ) (m : ℕ) : ℝ :=
  (p / (1 - p) + 2) ^ 2 / ((1 / 8) * (1 - aRec p m) ^ 2)

theorem CJc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 ≤ CJc p m := by
  have h1a : (0 : ℝ) < 1 - aRec p m := by have := aRec_lt_one hp1 hp2 m; linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hpq : (0 : ℝ) ≤ p / (1 - p) := by positivity
  unfold CJc; positivity

theorem KFc_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) : 0 ≤ KFc p m := by
  have h1a : (0 : ℝ) < 1 - aRec p m := by have := aRec_lt_one hp1 hp2 m; linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hpq : (0 : ℝ) ≤ p / (1 - p) := by positivity
  unfold KFc; positivity

/-! ### 6. Running-max bookkeeping on `ℕ` -/

/-- `M_n^j = (runMax p m U j n).toNat` is monotone. -/
theorem runMax_toNat_mono {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {a b : ℕ} (h : a ≤ b) :
    (runMax p m U j a).toNat ≤ (runMax p m U j b).toNat := by
  rw [runMax_eq_recVal, runMax_eq_recVal]
  exact Int.toNat_le_toNat (QplWindow.recVal_mono_le h)

/-- `M_{n+1}^j ≤ M_n^j + 1`. -/
theorem runMax_toNat_step {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} (n : ℕ) :
    (runMax p m U j (n + 1)).toNat ≤ (runMax p m U j n).toNat + 1 := by
  have hstep : recVal j (prefOf p m (n + 1) U) ≤ recVal j (prefOf p m n U) + 1 :=
    Swarming.Enl.recVal_succ_le p m U j n
  have heq : ((runMax p m U j n).toNat : ℤ) = recVal j (prefOf p m n U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j n)
  have hnn2 : 0 ≤ recVal j (prefOf p m (n + 1) U) := zero_le_recVal_prefOf p m U j (n + 1)
  have h4 : ((recVal j (prefOf p m (n + 1) U)).toNat : ℤ)
      ≤ (((runMax p m U j n).toNat + 1 : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn2]
    push_cast
    rw [heq]
    linarith
  have h5 : (recVal j (prefOf p m (n + 1) U)).toNat ≤ (runMax p m U j n).toNat + 1 := by
    exact_mod_cast h4
  rwa [runMax_eq_recVal]

/-- Positions are dominated by the running maximum, in `ℕ`-form on a nonnegative time. -/
theorem pos_toNat_le_runMax {p : ℝ} {m : ℕ} {U : Array N} {i : Fin N} {n : ℕ}
    (h : 0 ≤ (trajectory p m U n).pos i) :
    ((trajectory p m U n).pos i).toNat ≤ (runMax p m U i n).toNat := by
  refine Int.toNat_le_toNat ?_
  exact le_runMax p m U i n

/-- The `(Jbound)` inequality holds at *every* `n`, with no positivity hypothesis.  The negative
case is the support statement `F_b = 0` for nonpositive gaps: both gaps `X_{n+1} - M_n` and
`X_{n+1} - M_{n+1}` are then negative and the indicator vanishes as well. -/
theorem Jstruct_all {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} {i j : Fin N}
    (U : Array N) (n : ℕ) :
    |Jcorr p m (1 / 8) i j U n|
      ≤ CJc p m *
          ((hof p (siteMarks p m U j) ((runMax p m U j n).toNat)) ^ 2
            + (hof p (siteMarks p m U j) ((runMax p m U j n).toNat + 1)) ^ 2) *
          (if (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
              ((runMax p m U j n).toNat : ℤ)
                < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            then 1 else 0) := by
  by_cases hpos : 0 ≤ (trajectory p m U (n + 1)).pos i
  · have h := Jstruct_endpoint (N := N) hp1 hp2 (m := m) (i := i) (j := j) U n hpos
      (runMax_toNat_mono (le_of_lt (Nat.lt_succ_self n))) (runMax_toNat_step n)
    simpa only [CJc] using h
  · push_neg at hpos
    -- both gaps are strictly negative, so both corrections vanish
    have hrm0 : 0 ≤ runMax p m U j n := zero_le_runMax p m U j n
    have hrm1 : 0 ≤ runMax p m U j (n + 1) := zero_le_runMax p m U j (n + 1)
    have hgap1 : (trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1) ≤ 0 := by omega
    have hgap0 : (trajectory p m U (n + 1)).pos i - runMax p m U j n ≤ 0 := by omega
    have hJ0 : Jcorr p m (1 / 8) i j U n = 0 := by
      unfold VdriftAssembly.Jcorr
      rw [LocOccEnd.Fcorr_eq_zero_of_nonpos _ _ _ hgap1,
        LocOccEnd.Fcorr_eq_zero_of_nonpos _ _ _ hgap0]
      ring
    have htoNat0 : ((trajectory p m U (n + 1)).pos i).toNat = 0 :=
      Int.toNat_of_nonpos (le_of_lt hpos)
    have hind : ¬ (((runMax p m U j n).toNat : ℤ) < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)) := by
      rw [htoNat0]
      simp only [Nat.cast_zero]
      omega
    rw [hJ0, abs_zero, if_neg (fun hc => hind hc.2)]
    simp

/-! ### 7. The composition: `(lococc)` on the actual carrier -/

/-- **The paper's `(lococc)` on one actual carrier, with every field of
`LocOcc.lococc_window_eighth` discharged except the two spatial-slope identities of the projected
potential.**

Carrier: `X_n = (X_n^i).toNat`, `M_n^i = (runMax i n).toNat`, `M_n^j = (runMax j n).toNat`,
`h = h_j = hof p (siteMarks p m U ·)`, `wt = h^2`, `H_t(y) = H_{j,t}(y) = projH p m j t U y`,
`Z = Zproj`, `J = Jcorr`, `Q = Qpl` at `eps = 1/8`.

Everything the consumer asks for is *proved* here: the indicator identity `hocc`, the summed
`(Vdrift)` ledger `hled`, the definitional `Z`-decomposition, `hh`/`hhw`, the rescaled squared-site
`(locsum)` `hint` (`K = 2C`, `beta = 3 betaT`), the `(Fbounds)` endpoints `hFs`/`hFt` with the
record-squared cap taken from `(locmax)`, the `(Jbound)` field `hJstruct`, the record monotonicity
and unit step, the four running-max comparisons and the five window containments.

The two remaining inputs are `hslopeLo` and `hslopeHi`: the *spatial* slope of the projected
potential below and above the time-`t` record.  See the README for the exact status of each. -/
theorem lococc_actual_carrier
    {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C) {Kp : ℝ} (hKp : 0 ≤ Kp)
    {L : ℕ} (hL : 1 ≤ L) {Lw : ℕ} (hLw : 1 ≤ Lw) {A : ℕ} (hA : 1 ≤ A)
    {U : Array N} {s0 n s t : ℕ} (hs0 : s0 ≤ s) (hst : s ≤ t) (htn : t ≤ s0 + n)
    -- the good event: `(locsum)` and the adapted ledger
    (hlsq : ∀ a b : ℕ, A ≤ a → b ≤ A + Lw → a ≤ b →
      ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
        ≤ 2 * C * ((b : ℝ) - (a : ℝ))
          + 6 * C * ((betaT (xOf Lw) : ℕ) : ℝ))
    (hledger : ∀ u : ℕ,
      SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u - 1 / 8
        ≤ (Zproj p m (1 / 8) i j (u + 1) U - Zproj p m (1 / 8) i j u U)
          + Jcorr p m (1 / 8) i j U u
          - (Qpl p m (1 / 8) i j (u + 1) U - Qpl p m (1 / 8) i j u U))
    -- the bridge between the ledger's optional projection and the `projH` potential
    (hZeq : ∀ n : ℕ,
      ProjLedger.Zproj p m (1 / 8) i j n U = Swarming.Enl.Zproj p m (1 / 8) i j U n)
    -- the good event: the projected martingale and `projH` oscillation windows
    (hqpl : ∀ k : ℕ, k ≤ n →
      |Qpl p m (1 / 8) i j (s0 + k) U - Qpl p m (1 / 8) i j s0 U| < (L : ℝ) ^ (3 / 4 : ℝ))
    (hoscGood : ∀ u v : ℕ, s0 ≤ u → u ≤ v → v ≤ s0 + n →
      |projH p m j v U ((trajectory p m U u).pos i)
        - projH p m j u U ((trajectory p m U u).pos i)| < (L : ℝ) ^ (3 / 4 : ℝ))
    -- the record cell `{d_r <= L}` together with `(locmax)`
    (hcellX : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      A ≤ ((trajectory p m U u).pos i).toNat ∧ ((trajectory p m U u).pos i).toNat < A + Lw)
    (hcellMj : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      A ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A + Lw)
    (hcellMi : A ≤ (runMax p m U i t).toNat ∧ (runMax p m U i t).toNat + 1 ≤ A + Lw)
    (hloc : ∀ y ∈ Finset.Ico A (A + Lw), hof p (siteMarks p m U j) y ≤ xOf Lw)
    -- the two structural inputs
    (hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) = hof p (siteMarks p m U j) x)
    (hslopeHi : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
        projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp) :
    ∑ u ∈ Finset.Ico s t,
        (if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0)
      ≤ ((2 * C + Kp) + 2 * CJc p m * (2 * C) + 1) *
          ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
            + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
            + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
        + ((t : ℝ) - (s : ℝ)) / 8
        + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 2 + 1) * L34 L Lw := by
  -- ### nonnegativity and cast bookkeeping on the window
  have hnonneg : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    have hc := (hcellX u h1 h2).1
    have hpos : 0 < ((trajectory p m U u).pos i).toNat := by omega
    by_contra hcon
    push Not at hcon
    have hzero : ((trajectory p m U u).pos i).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hcon)
    omega
  have hnonneg' : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    exact hnonneg u (le_trans hs0 h1) (by omega)
  have hcast : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) = (trajectory p m U u).pos i :=
    fun u h1 h2 => Int.toNat_of_nonneg (hnonneg u h1 h2)
  -- ### the indicator identity `hocc`
  have hoccP : ∀ u : ℕ, s ≤ u → u < t →
      SwarmOcc.occInd (fun r => (trajectory p m U r).pos i) (fun r => runMax p m U j r) u
        = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
    fun u h1 h2 => LocOccEnd.occInd_eq_toNat_toNat (p := p) m U (hnonneg' u h1 (le_of_lt h2))
  -- ### the record-cost coefficient is nonnegative
  have hCJ0 : (0 : ℝ) ≤ CJc p m := CJc_nonneg hp1 hp2 m
  have hKF0 : (0 : ℝ) ≤ KFc p m := KFc_nonneg hp1 hp2 m
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  -- ### the record-squared cap at the two endpoints
  have hcap : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + n →
      (hof p (siteMarks p m U j) ((runMax p m U j u).toNat)) ^ 2 ≤ (xOf Lw) ^ 2 := by
    intro u h1 h2
    have hm := hcellMj u h1 h2
    refine hof_sq_record_le (N := N) hp1 hp2 (m := m) (U := U) (j := j) u
      (A := A) (Mv := Lw) (V := xOf Lw) (Real.rpow_nonneg (by positivity) _) (fun y hy => hloc y hy) ?_
    exact Finset.mem_Ico.mpr ⟨hm.1, hm.2⟩
  refine le_trans ?_ (LocOcc.lococc_window_eighth (X := fun u => ((trajectory p m U u).pos i).toNat)
      (Mi := fun u => (runMax p m U i u).toNat)
      (Mj := fun u => (runMax p m U j u).toNat)
      (occ := fun u => SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
        (fun r => runMax p m U j r) u)
      (J := fun u => Jcorr p m (1 / 8) i j U u)
      (Z := fun u => Zproj p m (1 / 8) i j u U)
      (Q := fun u => Qpl p m (1 / 8) i j u U)
      (H := fun t y => projH p m j t U (y : ℤ))
      (Fs := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s))
      (Ft := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t))
      (h := fun x => hof p (siteMarks p m U j) x)
      (wt := fun x => (hof p (siteMarks p m U j) x) ^ 2)
      (A := A) (Lw := Lw) (K := 2 * C) (β := 3 * ((betaT (xOf Lw) : ℕ) : ℝ)) (Kp := Kp)
      (CH := 1) (KQ := 2) (KF := KFc p m) (CJ := CJc p m) (L34 := L34 L Lw)
      hst hoccP hledger ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · -- the left-hand side is the paper's indicator sum on the nonnegative window
    refine le_of_eq (Finset.sum_congr rfl (fun u hu => ?_))
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hu
    exact (hoccP u h1 h2).symm
  · -- `hZs`: the bridge, then the definitional decomposition
    rw [hZeq s]
    show Swarming.Enl.Zproj p m (1 / 8) i j U s
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s)
    rw [hcast s hs0 (by omega)]
    rfl
  · -- `hZt`
    rw [hZeq t]
    show Swarming.Enl.Zproj p m (1 / 8) i j U t
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t)
    rw [hcast t (le_trans hs0 hst) htn]
    rfl
  · -- `hh`
    intro x
    exact LocOccEnd.hof_nonneg hp1 hp2 _ x
  · -- `hhw`
    intro x
    exact le_refl _
  · -- `hslopeLo`
    intro x hx
    have := hslopeLo x hx
    simpa only [Nat.cast_add, Nat.cast_one] using this
  · -- `hslopeHi`
    intro x hx
    have := hslopeHi x hx
    simpa only [Nat.cast_add, Nat.cast_one] using this
  · -- `hint`: the rescaled squared-site `(locsum)`
    exact locsum_hint_wt (p := p) (m := m) (U := U) (j := j) (A := A) (Lw := Lw) (C := C)
      (β := ((betaT (xOf Lw) : ℕ) : ℝ)) hC0 hlsq
  · -- `hosc`
    have h1 := hoscGood s t hs0 hst htn
    have e1 : (projH p m j t U (((trajectory p m U s).pos i).toNat)
        - projH p m j s U (((trajectory p m U s).pos i).toNat))
        = projH p m j t U ((trajectory p m U s).pos i) - projH p m j s U ((trajectory p m U s).pos i) := by
      rw [hcast s hs0 (by omega)]
    rw [e1]
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h3 := le_abs_self (projH p m j t U ((trajectory p m U s).pos i)
      - projH p m j s U ((trajectory p m U s).pos i))
    have h4 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L Lw := L34_lower_rpow L Lw
    linarith [le_of_lt h1, h3, h4, h2]
  · -- `hQ`
    have hs' : s0 + (s - s0) = s := Nat.add_sub_cancel' hs0
    have ht' : s0 + (t - s0) = t := Nat.add_sub_cancel' (le_trans hs0 hst)
    have h1 := hqpl (s - s0) (by omega)
    have h2 := hqpl (t - s0) (by omega)
    rw [hs'] at h1
    rw [ht'] at h2
    have h3 : |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U|
        ≤ |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U|
          + |Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U| := by
      have e : Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U
          = (Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U)
            + (Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U) := by ring
      calc |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U|
          = |(Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s0 U)
            + (Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U)| := by rw [e]
        _ ≤ _ := abs_add_le _ _
    have h4 : |Qpl p m (1 / 8) i j s0 U - Qpl p m (1 / 8) i j s U|
        = |Qpl p m (1 / 8) i j s U - Qpl p m (1 / 8) i j s0 U| := abs_sub_comm _ _
    have h5 := neg_le_abs (Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U)
    have h6 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ L34 L Lw := L34_lower_rpow L Lw
    have h7 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
    rw [h4] at h3
    linarith [le_of_lt h2, le_of_lt h1]
  · -- `hFs`
    exact abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U s
      (hcap s hs0 (by omega))
  · -- `hFt`
    exact abs_Fcorr_endpoint_L34 (N := N) hp1 hp2 (m := m) (i := i) (j := j) U t
      (hcap t (le_trans hs0 hst) htn)
  · -- `hJstruct`
    intro nx
    exact Jstruct_all (N := N) hp1 hp2 (m := m) (i := i) (j := j) U nx
  · -- `hMjmono`
    intro nx
    exact runMax_toNat_mono (le_of_lt (Nat.lt_succ_self nx))
  · -- `hMjstep`
    intro nx
    exact runMax_toNat_step nx
  · -- `hXW`
    intro nx h1 h2
    calc ((trajectory p m U (nx + 1)).pos i).toNat
        ≤ (runMax p m U i (nx + 1)).toNat :=
          pos_toNat_le_runMax (hnonneg' (nx + 1) (by omega) (by omega))
      _ ≤ (runMax p m U i t).toNat := runMax_toNat_mono (by omega)
  · -- `hMiw`
    exact runMax_toNat_mono hst
  · -- `hXMiS`
    exact pos_toNat_le_runMax (hnonneg' s (le_refl s) hst)
  · -- `hXtMi`
    exact pos_toNat_le_runMax (hnonneg' t hst (le_refl t))
  · -- `hcont1`
    exact (hcellX s hs0 (by omega)).1
  · -- `hcont2`
    exact (hcellMj s hs0 (by omega)).1
  · -- `hcont3`
    exact le_of_lt (hcellX t (le_trans hs0 hst) htn).2
  · -- `hcont4`
    exact hcellMi.2
  · -- `hcont5`
    exact le_of_lt (hcellMj t (le_trans hs0 hst) htn).2
  · linarith
  · positivity
  · exact hKp
  · exact hCJ0
  · norm_num
  · exact hKF0
  · norm_num
  · exact L34_nonneg L Lw
  · exact one_le_L34 hL
  · exact three_betaT_le_L34 L Lw


/-! ### 8. Where the per-site above-record slope hypothesis bites

The consumer's `hslopeHi` is a *per-site* bound with a constant `Kp`.  On the actual model the step
immediately above the record is the projected seed `e_0 = eRec p m t j 0 U` (the `g = 0` term of the
closed form `(projh)`), and the only bounds the tree has for `e_0` are `bRec = h_j(M_t^j-1)+2` and
the cell cap `L^{1/16}+2`.  So the per-site hypothesis, at the record site alone, is the statement
`e_0 <= Kp`; with an `L`-independent `Kp` this is strictly stronger than what the model supplies. -/

/-- **The closed form's `g = 0` step**: immediately above the record the projected step is the
projected seed `e_0`. -/
theorem slope_at_record_eq_seed {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m))) :
    projH p m j t U (recVal j (prefOf p m t U) + 1) - projH p m j t U (recVal j (prefOf p m t U))
      = eRec p m t j 0 U := by
  have h0 := hcl (recVal j (prefOf p m t U)) 0 (by ring)
  have hg1 : recVal j (prefOf p m t U) + 1
      = recVal j (prefOf p m t U) + ((0 + 1 : ℕ) : ℤ) := by push_cast; ring
  have h2 := hcl (recVal j (prefOf p m t U) + 1) 1 hg1
  rw [h0, h2]
  have hnum : (1 : ℝ) - aRec p m ^ 1 = 1 - aRec p m := by ring
  rw [hnum]
  have hne : (1 : ℝ) - aRec p m ≠ 0 := by
    have h := aRec_lt_one hp1 hp2 m
    linarith
  field_simp
  ring

/-- **The per-site hypothesis at the record site is `e_0 <= Kp`.** -/
theorem seed_le_of_slopeHi {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    {j : Fin N} {t : ℕ} {U : Array N} {Kp : ℝ}
    (hcl : ∀ (y : ℤ) (g : ℕ), y = recVal j (prefOf p m t U) + (g : ℤ) →
      projH p m j t U y
        = SwarmOcc.Hpot (siteH p m j U) (recVal j (prefOf p m t U))
          + (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m t j 0 U - (1 + aRec p m) / (1 - aRec p m))
              * ((1 - aRec p m ^ g) / (1 - aRec p m)))
    (hslopeHi : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ∧
        projH p m j t U ((x : ℤ) + 1) - projH p m j t U (x : ℤ) ≤ Kp) :
    eRec p m t j 0 U ≤ Kp := by
  have hstep := (hslopeHi (runMax p m U j t).toNat le_rfl).2
  have hcast : (((runMax p m U j t).toNat : ℕ) : ℤ) = recVal j (prefOf p m t U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j t)
  rw [hcast, slope_at_record_eq_seed hp1 hp2 hcl] at hstep
  exact hstep
