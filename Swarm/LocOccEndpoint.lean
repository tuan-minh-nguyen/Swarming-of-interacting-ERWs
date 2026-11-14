/-
# Endpoint `h_j^*`/`F_b`/`J` bookkeeping for `(lococc)` on the actual array

Scope.  `LocOcc.lococc_window` (in `Swarm/LocOccProjected.lean`) is the paper's
`(lococc)` display abstracted over a list of *hypotheses*.  Four of those hypotheses are not
stochastic at all: they are the endpoint wiring `Z_t = H_t(X_t) - F_t` and the two structural
bounds `(Fbounds)`/`(Jbound)` for the paper's correction `F_b` and record cost `J_{t+1}`:

* `hZs`, `hZt`  — the definitional identity of the projected ledger;
* `hFs`, `hFt`  — `|F_{b_n}(X_n^i - M_n^j)| <= C L^{3/4}` at the two endpoints;
* `hJstruct`    — `|J_{n+1}| <= C (h_j(M_n^j)^2 + h_j(M_n^j+1)^2) 1{record advanced, X_{n+1} > M_n^j}`;

plus `hocc` (the ledger indicator is the position comparison on a nonnegative window) and
`hh`/`hhw` (the harmonic weight `h_j` and its square).  This file *proves* all of them, from the
actual definitions of `bRec = h_j(M_n^j-1)+2`, `Fcorr`, `Jcorr` and the actual site marks
`SwarmLogRatio.siteMarks p m U j`, and then feeds them into `LocOcc.lococc_window_eighth`.

The mathematical content is the paper's:

* `(hrec)` gives `h_j(x-1) <= (p/(1-p)) h_j(x)` and `h_j(x) >= 1`, hence
  `b_n <= (p/(1-p) + 2) h_j(M_n^j)` and `b_{n+1} <= (p/(1-p) + 4) h_j(M_n^j)`;
* `(Fbounds)` gives `|F_b(g)| <= b^2 / (eps (1-a)^2)` uniformly in the gap `g`, and `F_b(g) = 0`
  for every `g <= 0`;
* consequently `|J_{n+1}| = 0` unless the record advances *and* `X_{n+1}^i > M_n^j`, and otherwise
  `|J_{n+1}| <= CJ (h_j(M_n^j)^2 + h_j(M_n^j+1)^2)`.

What is **not** claimed: any probability statement.  In particular the two-sided `Qpl` window
deviation (`hQ`), the site-indexed potential oscillation (`hosc`), the interval `(locsum)` bound
(`hint`) and the `(locmax)` cap at the endpoint records (`hcapS`, `hcapT`) remain explicit
hypotheses.  See README.md for the exact residual list.
-/
import Swarm.LocOccLedger
import Swarm.ProjLedgerBridge
import Swarm.SiteHMax

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LocOccEnd

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-- Elementary division rearrangement, `(A h)/d = (A/d) h`, used to pull the `(Fbounds)`
denominator out of the spatial factor. -/
theorem div_mul_div {A h d : ℝ} (hd : d ≠ 0) : (A * h) / d = (A / d) * h := by
  field_simp

/-! ### 1. `F_b` vanishes on nonpositive gaps -/

/-- **`(Fbounds)`, support part.**  `F_b(g) = sum_{0 <= i < g} (...)` is empty when `g <= 0`. -/
theorem Fcorr_eq_zero_of_nonpos (a ε b : ℝ) {g : ℤ} (hg : g ≤ 0) :
    SwarmOcc.Fcorr a ε b g = 0 := by
  unfold SwarmOcc.Fcorr
  rw [Int.toNat_eq_zero.mpr hg, Finset.range_zero, Finset.sum_empty]

/-- **`(Fbounds)`, size part, at any gap.**  `|F_b(g)| <= b^2 / (eps (1-a)^2)`. -/
theorem abs_Fcorr_le {a ε b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (g : ℤ) : |SwarmOcc.Fcorr a ε b g| ≤ b ^ 2 / (ε * (1 - a) ^ 2) :=
  SwarmOcc.Fcorr_abs_le ha0 ha1 hb hε g

/-! ### 2. The `(hrec)` consequences for the site potential -/

/-- **`(hrec)`, comparison form.**  For `1/2 < p < 1` the two-branch recursion gives
`h_j(x) <= (p/(1-p)) h_j(x+1)` for every `x`: in the marked branch the right side is
`1/(1-p) + h_j(x)`, in the unmarked branch it is `p/(1-p) (h_j(x)+2)`, and `p/(1-p) > 1`. -/
theorem hof_le_const_mul_hof_succ {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (ω : ℕ → Bool) (x : ℕ) :
    SwarmMarks.hof p ω x ≤ (p / (1 - p)) * SwarmMarks.hof p ω (x + 1) := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hqpos : (0 : ℝ) < p / (1 - p) := by positivity
  have h1 : (1 : ℝ) ≤ SwarmMarks.hof p ω x :=
    SwarmMarks.one_le_hof hp0.le hp1 ω x
  rw [SwarmMarks.hof_succ]
  cases hb : ω (x + 1) with
  | true =>
      rw [SwarmMarks.hstep_true]
      have hkey : (p / (1 - p)) * (1 / p + ((1 - p) / p) * SwarmMarks.hof p ω x)
          = 1 / (1 - p) + SwarmMarks.hof p ω x := by
        field_simp
      calc SwarmMarks.hof p ω x ≤ 1 / (1 - p) + SwarmMarks.hof p ω x := by
            have h2 : (0 : ℝ) ≤ 1 / (1 - p) := by positivity
            linarith
        _ = (p / (1 - p)) * (1 / p + ((1 - p) / p) * SwarmMarks.hof p ω x) := hkey.symm
  | false =>
      rw [SwarmMarks.hstep_false]
      have hratio : (1 : ℝ) ≤ p / (1 - p) := by
        rw [le_div_iff₀ hq]; linarith
      have hnn : (0 : ℝ) ≤ SwarmMarks.hof p ω x := by linarith
      calc SwarmMarks.hof p ω x
          ≤ (p / (1 - p)) * SwarmMarks.hof p ω x := by
            nlinarith [mul_le_mul_of_nonneg_left hratio hnn]
        _ ≤ (p / (1 - p)) * (SwarmMarks.hof p ω x + 2) := by
            have h2 : (0 : ℝ) ≤ 2 * (p / (1 - p)) := by positivity
            nlinarith
/-- `h_j(x) >= 0`, hence the weight `h_j(x)^2` dominates it in the sense needed by `hh`/`hhw`. -/
theorem hof_nonneg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (ω : ℕ → Bool) (x : ℕ) :
    0 ≤ SwarmMarks.hof p ω x :=
  le_trans zero_le_one (SwarmMarks.one_le_hof hp0.le hp1 ω x)

/-- **`b_n` in terms of the record-level harmonic weight.**  `HprevAt n <= (p/(1-p)) h_j(M_n^j)`,
including the record-`0` boundary case (where `HprevAt = 1` and `h_j >= 1`). -/
theorem HprevAt_le_ratio_mul_hof {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (j : Fin N) (U : Array N) :
    HprevAt p m n j U
      ≤ (p / (1 - p)) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat) := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hratio : (1 : ℝ) ≤ p / (1 - p) := by rw [le_div_iff₀ hq]; linarith
  rw [runMax_eq_recVal]
  have h1 : (1 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat) :=
    SwarmMarks.one_le_hof hp0.le hp1 _ _
  have hnn : (0 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat) := le_trans zero_le_one h1
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m n U)).toNat) with h0 | hpos
  · rw [HprevAt, if_pos h0]
    have := mul_le_mul_of_nonneg_right hratio hnn
    rw [one_mul] at this
    linarith
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m n U)).toNat ≠ 0)
    rw [HprevAt, if_neg (by omega)]
    have hidx : (recVal j (prefOf p m n U)).toNat - 1 = k := by omega
    rw [hidx, hk]
    exact hof_le_const_mul_hof_succ hp0 hp1 _ k

/-- **`(hrec)` at the record: `b_n <= (p/(1-p) + 2) h_j(M_n^j)`.** -/
theorem bRec_le_ratio {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) :
    bRec p m n j U
      ≤ (p / (1 - p) + 2) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat) := by
  have h1 : (1 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((runMax p m U j n).toNat) :=
    SwarmMarks.one_le_hof hp0.le hp1 _ _
  have h2 := HprevAt_le_ratio_mul_hof (N := N) hp0 hp1 m n j U
  have h3 : bRec p m n j U = HprevAt p m n j U + 2 := rfl
  rw [h3]
  nlinarith

/-- **`(hrec)` at the record, one step later: `b_{n+1} <= (p/(1-p) + 4) h_j(M_n^j)`.** -/
theorem bRec_succ_le_ratio {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (j : Fin N) (U : Array N) :
    bRec p m (n + 1) j U
      ≤ (p / (1 - p) + 4) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat) := by
  have h1 : (1 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((runMax p m U j n).toNat) :=
    SwarmMarks.one_le_hof hp0.le hp1 _ _
  have h2 := HprevAt_le_ratio_mul_hof (N := N) hp0 hp1 m n j U
  have h3 := SiteHMax.bRec_succ_le hp0 hp1 m n j U
  nlinarith

/-- `bRec` is nonnegative (used to apply the `(Fbounds)` size estimate). -/
theorem bRec_nonneg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : 0 ≤ bRec p m n j U := by
  have h1 : (1 : ℝ) ≤ HprevAt p m n j U :=
    one_le_HprevAt hp0 hp1 m n j U
  have h3 : bRec p m n j U = HprevAt p m n j U + 2 := rfl
  rw [h3]; linarith

/-! ### 3. The `(Fbounds)` endpoint estimate -/

/-- **`(Fbounds)` at the actual record cost.**  `F_{b_n}` is nonpositive, of size at most
`b_n^2/(eps (1-a)^2)`, and `b_n <= (p/(1-p)+2) h_j(M_n^j)`, so at a site where the record-level
harmonic weight is at most `L34` the correction is at most `(p/(1-p)+2)^2 L34 / (eps (1-a)^2)`. -/
theorem abs_Fcorr_endpoint_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {i j : Fin N} {ε L34 : ℝ} (hε : 0 < ε) (U : Array N) (n : ℕ)
    (hcap : (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((runMax p m U j n).toNat)) ^ 2 ≤ L34) :
    |SwarmOcc.Fcorr (aRec p m) ε (bRec p m n j U)
        ((trajectory p m U n).pos i - runMax p m U j n)|
      ≤ ((p / (1 - p) + 2) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * L34 := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp0 hp1 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp0 hp1 m
  have hden : (0 : ℝ) < ε * (1 - aRec p m) ^ 2 := by
    have : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  have hb0 := bRec_nonneg (N := N) hp0 hp1 m n j U
  have h1 := abs_Fcorr_le ha0 ha1 hb0 hε
    ((trajectory p m U n).pos i - runMax p m U j n)
  have h2 := bRec_le_ratio (N := N) hp0 hp1 m n j U
  have h3 : (0 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((runMax p m U j n).toNat) := hof_nonneg hp0 hp1 _ _
  have hb2 : bRec p m n j U ^ 2
      ≤ ((p / (1 - p) + 2) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat)) ^ 2 := by
    have hbpos : (0 : ℝ) ≤ bRec p m n j U := hb0
    nlinarith
  have h4 : bRec p m n j U ^ 2 / (ε * (1 - aRec p m) ^ 2)
      ≤ ((p / (1 - p) + 2) ^ 2 * (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat)) ^ 2) / (ε * (1 - aRec p m) ^ 2) := by
    have := hb2
    have hmul : ((p / (1 - p) + 2) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat)) ^ 2
        = (p / (1 - p) + 2) ^ 2 * (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat)) ^ 2 := by ring
    rw [hmul] at this
    exact div_le_div_of_nonneg_right this hden.le
  have h5 : ((p / (1 - p) + 2) ^ 2 * (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((runMax p m U j n).toNat)) ^ 2) / (ε * (1 - aRec p m) ^ 2)
      ≤ ((p / (1 - p) + 2) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * L34 := by
    rw [div_mul_div (by positivity : (ε * (1 - aRec p m) ^ 2) ≠ 0)]
    exact mul_le_mul_of_nonneg_left hcap (by positivity)
  linarith

/-! ### 4. The `(Jbound)` structural estimate -/

/-- **`(Jbound)`, structural part.**  The record cost `J_{n+1} = F_{b_{n+1}}(X_{n+1}^i - M_{n+1}^j)
- F_{b_n}(X_{n+1}^i - M_n^j)` vanishes unless the record of walker `j` advances at time `n+1`
*and* `X_{n+1}^i` is strictly above the old record `M_n^j`; when it does not vanish it is bounded
by `CJ (h_j(M_n^j)^2 + h_j(M_n^j+1)^2)`.  This is the paper's
`|J_{t+1}| <= C h_j(r_t-1)^2 1{r_{t+1} = r_t+1, X_{t+1}^i > r_t}` together with
`h_j(r_t-1) <= (p/(1-p)) h_j(r_t)`. -/
theorem abs_Jcorr_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N}
    {ε : ℝ} (hε : 0 < ε) (U : Array N) (n : ℕ)
    (hposnext : 0 ≤ (trajectory p m U (n + 1)).pos i)
    (hmono : (runMax p m U j n).toNat ≤ (runMax p m U j (n + 1)).toNat)
    (hstep : (runMax p m U j (n + 1)).toNat ≤ (runMax p m U j n).toNat + 1) :
    |Jcorr p m ε i j U n|
      ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) *
          ((SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) ((runMax p m U j n).toNat)) ^ 2
            + (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                ((runMax p m U j n).toNat + 1)) ^ 2) *
          (if (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
              ((runMax p m U j n).toNat : ℤ) < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            then 1 else 0) := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have ha0 : (0 : ℝ) ≤ aRec p m := zero_le_aRec hp0 hp1 m
  have ha1 : aRec p m < 1 := aRec_lt_one hp0 hp1 m
  have hden : (0 : ℝ) < ε * (1 - aRec p m) ^ 2 := by
    have : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  set M : ℕ := (runMax p m U j n).toNat with hMdef
  set h : ℝ := SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) M with hhdef
  have hh1 : (1 : ℝ) ≤ h := SwarmMarks.one_le_hof hp0.le hp1 _ M
  have hhnn : (0 : ℝ) ≤ h := by linarith
  have hMcast : ((runMax p m U j n).toNat : ℤ) = runMax p m U j n :=
    Int.toNat_of_nonneg (zero_le_runMax p m U j n)
  have hMncast : ((M : ℕ) : ℤ) = runMax p m U j n := hMcast
  have hposcast : ((((trajectory p m U (n + 1)).pos i).toNat : ℕ) : ℤ)
      = (trajectory p m U (n + 1)).pos i := Int.toNat_of_nonneg hposnext
  have hJ : Jcorr p m ε i j U n
      = SwarmOcc.Fcorr (aRec p m) ε (bRec p m (n + 1) j U)
          ((trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1))
        - SwarmOcc.Fcorr (aRec p m) ε (bRec p m n j U)
          ((trajectory p m U (n + 1)).pos i - runMax p m U j n) := rfl
  by_cases hI : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1 ∧
      ((runMax p m U j n).toNat : ℤ) < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
  · rw [if_pos hI, mul_one]
    have hb0 := bRec_nonneg (N := N) hp0 hp1 m n j U
    have hb1 := bRec_nonneg (N := N) hp0 hp1 m (n + 1) j U
    set F1 := SwarmOcc.Fcorr (aRec p m) ε (bRec p m (n + 1) j U)
        ((trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1)) with hF1
    set F0 := SwarmOcc.Fcorr (aRec p m) ε (bRec p m n j U)
        ((trajectory p m U (n + 1)).pos i - runMax p m U j n) with hF0
    have e1 := abs_Fcorr_le ha0 ha1 hb1 hε
      ((trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1))
    have e0 := abs_Fcorr_le ha0 ha1 hb0 hε
      ((trajectory p m U (n + 1)).pos i - runMax p m U j n)
    have k1 := bRec_succ_le_ratio (N := N) hp0 hp1 m n j U
    have k0 := bRec_le_ratio (N := N) hp0 hp1 m n j U
    have hc4 : (0 : ℝ) ≤ p / (1 - p) + 4 := by
      have : (0 : ℝ) ≤ p / (1 - p) := by positivity
      linarith
    have hb1' : bRec p m (n + 1) j U ≤ (p / (1 - p) + 4) * h := k1
    have hb0' : bRec p m n j U ≤ (p / (1 - p) + 4) * h := by
      have h24 : (p / (1 - p) + 2) ≤ (p / (1 - p) + 4) := by linarith
      have hm := mul_le_mul_of_nonneg_right h24 hhnn
      linarith
    have hle1 : bRec p m (n + 1) j U ^ 2
        ≤ (p / (1 - p) + 4) ^ 2 * h ^ 2 := by nlinarith
    have hle0 : bRec p m n j U ^ 2 ≤ (p / (1 - p) + 4) ^ 2 * h ^ 2 := by nlinarith
    have hC0 : (0 : ℝ) ≤ (p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2) :=
      div_nonneg (by positivity) hden.le
    have hd : |F1| ≤ ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2 := by
      have h2 : bRec p m (n + 1) j U ^ 2 / (ε * (1 - aRec p m) ^ 2)
          ≤ ((p / (1 - p) + 4) ^ 2 * h ^ 2) / (ε * (1 - aRec p m) ^ 2) :=
        div_le_div_of_nonneg_right hle1 hden.le
      have e : ((p / (1 - p) + 4) ^ 2 * h ^ 2) / (ε * (1 - aRec p m) ^ 2)
          = ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2 :=
        div_mul_div (by positivity : (ε * (1 - aRec p m) ^ 2) ≠ 0)
      rw [e] at h2
      exact le_trans e1 h2
    have hd0 : |F0| ≤ ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2 := by
      have h2 : bRec p m n j U ^ 2 / (ε * (1 - aRec p m) ^ 2)
          ≤ ((p / (1 - p) + 4) ^ 2 * h ^ 2) / (ε * (1 - aRec p m) ^ 2) :=
        div_le_div_of_nonneg_right hle0 hden.le
      have e : ((p / (1 - p) + 4) ^ 2 * h ^ 2) / (ε * (1 - aRec p m) ^ 2)
          = ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2 :=
        div_mul_div (by positivity : (ε * (1 - aRec p m) ^ 2) ≠ 0)
      rw [e] at h2
      exact le_trans e0 h2
    have htri : |F1 - F0| ≤ |F1| + |F0| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [neg_abs_le F1, le_abs_self F0]
      · linarith [le_abs_self F1, neg_abs_le F0]
    have hbound : |F1 - F0| ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * (h ^ 2) := by
      have h2 : |F1| + |F0| ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2 := by
        nlinarith [hd, hd0]
      linarith
    have hmon : 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) * h ^ 2
        ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) *
            (h ^ 2 + (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((runMax p m U j n).toNat + 1)) ^ 2) := by
      have h1nn : (0 : ℝ) ≤ (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((runMax p m U j n).toNat + 1)) ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) ≤ 2 * ((p / (1 - p) + 4) ^ 2 / (ε * (1 - aRec p m) ^ 2)) := by
        nlinarith [hC0]
      nlinarith [hC0, h1nn, h2]
    rw [hJ]
    exact le_trans hbound hmon
  · rw [if_neg hI, mul_zero]
    have hzero : Jcorr p m ε i j U n = 0 := by
      by_cases hA : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat + 1
      · have hB : ¬ (((runMax p m U j n).toNat : ℤ)
            < (((trajectory p m U (n + 1)).pos i).toNat : ℤ)) := fun hc => hI ⟨hA, hc⟩
        have hB2 : (((trajectory p m U (n + 1)).pos i).toNat : ℤ)
            ≤ ((runMax p m U j n).toNat : ℤ) := not_lt.mp hB
        rw [hposcast] at hB2
        have hM1 : ((runMax p m U j (n + 1)).toNat : ℤ)
            = ((runMax p m U j n).toNat : ℤ) + 1 := by rw [hA]; push_cast; ring
        have hgap1 : (trajectory p m U (n + 1)).pos i - runMax p m U j (n + 1) ≤ 0 := by
          have e : runMax p m U j (n + 1) = ((runMax p m U j (n + 1)).toNat : ℤ) :=
            (Int.toNat_of_nonneg (zero_le_runMax p m U j (n + 1))).symm
          rw [e, hM1]; linarith
        have hgap0 : (trajectory p m U (n + 1)).pos i - runMax p m U j n ≤ 0 := by
          linarith [hMncast]
        rw [hJ, Fcorr_eq_zero_of_nonpos _ _ _ hgap1, Fcorr_eq_zero_of_nonpos _ _ _ hgap0]
        ring
      · have hA' : (runMax p m U j (n + 1)).toNat = (runMax p m U j n).toNat := by omega
        have hr : runMax p m U j (n + 1) = runMax p m U j n := by
          have e1 : runMax p m U j (n + 1) = ((runMax p m U j (n + 1)).toNat : ℤ) :=
            (Int.toNat_of_nonneg (zero_le_runMax p m U j (n + 1))).symm
          have e0 : runMax p m U j n = ((runMax p m U j n).toNat : ℤ) :=
            (Int.toNat_of_nonneg (zero_le_runMax p m U j n)).symm
          rw [e1, e0, hA']
        have hb : bRec p m (n + 1) j U = bRec p m n j U := by
          have hrec : recVal j (prefOf p m (n + 1) U) = recVal j (prefOf p m n U) := by
            rw [← runMax_eq_recVal, ← runMax_eq_recVal]; exact hr
          have hH : HprevAt p m (n + 1) j U = HprevAt p m n j U := by
            unfold HprevAt; rw [hrec]
          show HprevAt p m (n + 1) j U + 2 = HprevAt p m n j U + 2
          rw [hH]
        rw [hJ, hr, hb]
        ring
    rw [hzero, abs_zero]

/-! ### 5. The indicator and the record-level weight -/

/-- `((pos u).toNat : ℤ) = pos u` on a nonnegative window. -/
theorem toNat_cast {a : ℤ} (ha : 0 ≤ a) : (((a.toNat : ℕ)) : ℤ) = a := Int.toNat_of_nonneg ha

/-- `a.toNat <= b.toNat` is `a <= b` for nonnegative integers. -/
theorem toNat_le_toNat_iff {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a.toNat ≤ b.toNat ↔ a ≤ b := by
  constructor
  · intro h
    have h2 : (((a.toNat : ℕ)) : ℤ) ≤ (((b.toNat : ℕ)) : ℤ) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] at h2
  · intro h
    have h2 : (((a.toNat : ℕ)) : ℤ) ≤ (((b.toNat : ℕ)) : ℤ) := by
      rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]; exact h
    exact_mod_cast h2

/-- **`hocc` on a nonnegative window.**  `occInd = 1{0 <= X <= M}` is the paper's
`1{X_u^i <= M_u^j}` once the walker is nonnegative. -/
theorem occInd_eq_toNat_toNat {p : ℝ} (m : ℕ) (U : Array N) {i j : Fin N} {u : ℕ}
    (hu : 0 ≤ (trajectory p m U u).pos i) :
    SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
        (fun r => runMax p m U j r) u
      = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 := by
  rw [LocOcc.occInd_eq_of_nonneg hu]
  by_cases h : (trajectory p m U u).pos i ≤ runMax p m U j u
  · rw [if_pos h, if_pos ((toNat_le_toNat_iff hu (zero_le_runMax p m U j u)).mpr h)]
  · rw [if_neg h,
      if_neg (fun hc => h ((toNat_le_toNat_iff hu (zero_le_runMax p m U j u)).mp hc))]
