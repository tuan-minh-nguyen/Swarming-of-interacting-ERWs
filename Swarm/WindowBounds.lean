/-
  **Direction (B): pathwise finite-time comparisons and event containment for `(locsum)`.**

  Paper reference: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, proof of
  Proposition `local`, the passage beginning "We consider the integers `R_s^A < y ≤ R_t^A - 2m`".
  There it is asserted that for every such integer `y`

  * `s < σ_y^A`,
  * `σ_y^A + 2m - 1 ≤ t - 1`  (equivalently `σ_y^A + 2m ≤ t`), and
  * the times `σ_y^A + 2m - 1` are distinct,

  so that the trials `Γ_y^A` counted by the residue-class martingale are decided strictly inside
  the window `[s,t]` and at distinct times.

  This file proves those assertions on the actual trajectory, from the integrated
  `GammaSigma.lean` primitives `runMaxA`, `ARMax`, `sigmaA`, `sigmaA_le_of_record_le`,
  `sigmaA_nesting`, `sigmaA_nesting_two_m` and `sigmaA_trial_sep`.  No measure, tail estimate,
  density hypothesis or probability statement is used or claimed here: every result is a
  deterministic statement about one uniform array `U`.

  ## The exact statements, and why `WithTop` needs care

  `σ_y^A` is `WithTop ℕ`-valued, and a level the path never reaches has `σ_y^A = ⊤`.  The window
  hypothesis `R_t^A ≥ y + 2m` rules that out (`sigmaA_ne_top_of_runMaxA_le`), but the comparisons
  must be phrased so that they are *true* rather than merely convenient:

  * `sigmaA_le_iff_runMaxA_le` records the exact finite-level criterion
    `σ_y^A ≤ t ↔ y ≤ R_t^A` (for `0 ≤ y`), the form in which the window hypothesis feeds every
    later step.  Its `→` direction is not immediate from the name `sigmaA_le_of_record_le`; it
    uses `ARMax.eq` (no overshoot) and `runMaxA_mono`.
  * `sigmaA_add_two_m_le` is the `WithTop`-honest form of the paper's `σ_{y+2m}^A ≥ σ_y^A + 2m`:
    it needs no finiteness hypothesis, because `⊤ + k = ⊤` and `σ_y^A ≤ σ_{y+2m}^A`.  Stating it
    between natural numbers would require a finiteness side condition the paper leaves implicit.
  * `window_bounds` produces *integer* witnesses `j = σ_y^A`, `n = σ_{y+2m}^A` with
    `s < j`, `j + 2m ≤ n`, `n ≤ t`; `sigmaA_trial_sep` supplies `j + 2m ≤ n`.  The paper's
    `σ_y^A + 2m - 1 ≤ t - 1` is `window_end_le`, and needs `1 ≤ m` (else `2m - 1 = 0`).
  * `σ_{y+2m}^A + 1 ≤ t` is **not** a consequence: `WindowSharp.lean` exhibits the all-zero
    reference array, for which `σ_{y+2m}^A = t` is attained while the window hypothesis holds.
    Hence `n ≤ t`, equivalently `σ_y^A + 2m - 1 ≤ t - 1`, is the sharp conclusion.
  * Distinctness of finishing times needs injectivity of `σ` on finite values:
    `sigmaA_eq_of_eq_coe` (first passages to `y` and `y'` at one common time force `y = y'`,
    because `ARMax.eq` gives no overshoot).  With `sigmaA_finish_inj` this yields
    `window_finish_card`: finishing times over a finite set of window levels are distinct, so the
    number of trials equals the number of occupied times.

  ## Measurability gateway

  `measurableSet_GammaSet_inter_sigmaA_le` shows that `Γ_y^A ∩ {σ_{y+2m}^A ≤ t}` is
  `enlFilt p m t`-measurable: it is a finite union over `n ≤ t` of the pieces
  `{σ_{y+2m}^A = n} ∩ Γ_y^A`, each `enlFilt p m n`-measurable by `measurableSet_GammaSet_next`,
  and `enlFilt p m n ≤ enlFilt p m t`.  Rewritten on the window event `{y + 2m ≤ R_t^A}` this is
  `measurableSet_GammaSet_inter_window`.  This is the adaptedness statement "sum only the trials
  lying fully inside `[s,t]`", in the form a time-`t` argument (maximal Azuma–Hoeffding at `t`)
  consumes.

  ## Scope

  Only deterministic path content plus that measurability.  Nothing here proves `(locsum)`,
  `(locgroup)`, tightness, regeneration, or `MainClaim`.  No probability is bounded and no union
  over residue classes is taken: the residue-class count tail is the separate scoped
  `GammaTail`/`GammaTailExp`/`GammaEndpoint` development (direction (A)).
-/
import Swarm.GammaTail

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}

/-! ## 1. `firstIdx` monotonicity, level monotonicity and the finite-level criterion -/

/-- **Monotonicity of `firstIdx`** in the predicate.  If `P` implies `Q` pointwise then `Q` hits
no later than `P`, so `firstIdx Q ≤ firstIdx P` — the direction that matters, since the `⊤`-valued
first hit of a *larger* event is *smaller*. -/
theorem firstIdx_anti {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) : firstIdx Q ≤ firstIdx P := by
  classical
  rcases eq_or_ne (firstIdx P) ⊤ with hP | hP
  · rw [hP]; exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hP
    have hPn : P n := (firstIdx_eq_coe_iff.mp hn.symm).1
    rw [← hn]
    exact firstIdx_le_iff.mpr ⟨n, le_rfl, h n hPn⟩

/-- **`σ_y^A` is nondecreasing in the level `y`.**  Reaching a higher level first cannot happen
earlier.  (Direct proof, no sign and no finiteness hypothesis: when `σ_{y'}^A = ⊤` the claim is
trivial; otherwise `ARMax` at `σ_{y'}^A` puts the record at or above `y` there.) -/
theorem sigmaA_mono {y y' : ℤ} (h : y ≤ y') : sigmaA p m U hA y ≤ sigmaA p m U hA y' := by
  rcases eq_or_ne (sigmaA p m U hA y') ⊤ with htop | hfin
  · rw [htop]; exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hAR : ARMax p m U hA y' n := sigmaA_eq_coe_iff.mp hn.symm
    have hle : sigmaA p m U hA y ≤ (n : WithTop ℕ) :=
      sigmaA_le_of_record_le ⟨n, le_rfl, h.trans hAR.1⟩
    rwa [← hn]

/-- The group record is always nonnegative: it starts at `0` and is nondecreasing. -/
theorem runMaxA_nonneg (n : ℕ) : 0 ≤ runMaxA p m U hA n := by
  have h := runMaxA_mono (p := p) (m := m) (U := U) (hA := hA) (a := 0) (b := n) (Nat.zero_le n)
  rw [runMaxA_zero] at h
  exact h

/-- **`σ_y^A = ⊤` exactly when the group record never reaches `y`.** -/
theorem sigmaA_eq_top_iff {y : ℤ} :
    sigmaA p m U hA y = ⊤ ↔ ∀ n, runMaxA p m U hA n < y := by
  constructor
  · intro h n
    by_contra hcon
    push Not at hcon
    have hle : sigmaA p m U hA y ≤ (n : WithTop ℕ) := sigmaA_le_of_record_le ⟨n, le_rfl, hcon⟩
    rw [h] at hle
    exact absurd hle (by simp)
  · intro h
    by_contra hcon
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hcon
    have hAR : ARMax p m U hA y n := sigmaA_eq_coe_iff.mp hn.symm
    exact absurd hAR.1 (not_le.mpr (h n))

/-- `σ_y^A ≤ t` as soon as the record is at level `y` at time `t`. -/
theorem sigmaA_le_of_record_le' {y : ℤ} {t : ℕ} (h : y ≤ runMaxA p m U hA t) :
    sigmaA p m U hA y ≤ (t : WithTop ℕ) :=
  sigmaA_le_of_record_le ⟨t, le_rfl, h⟩

/-- **The exact finite-level criterion**: for a nonnegative level, `σ_y^A ≤ t` iff the group
record has reached `y` by time `t`.  The forward direction uses that a first passage has no
overshoot (`ARMax.eq`, hence `R_{σ_y^A} = y`) and that the record is nondecreasing. -/
theorem sigmaA_le_iff_runMaxA_le {y : ℤ} (hy : 0 ≤ y) {t : ℕ} :
    sigmaA p m U hA y ≤ (t : WithTop ℕ) ↔ y ≤ runMaxA p m U hA t := by
  constructor
  · intro hle
    obtain ⟨k, hk, hAR⟩ := sigmaA_le_iff.mp hle
    exact (hAR.eq hy).ge.trans (runMaxA_mono hk)
  · exact sigmaA_le_of_record_le'

/-- **Finiteness from the window hypothesis**: if the record is at level `y` by time `t` then
`σ_y^A ≠ ⊤`. -/
theorem sigmaA_ne_top_of_runMaxA_le {y : ℤ} {t : ℕ} (h : y ≤ runMaxA p m U hA t) :
    sigmaA p m U hA y ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.coe_ne_top) (sigmaA_le_of_record_le' h)

/-- **Nothing below the current record has been reached yet**: if `R_s^A < y` then `s < σ_y^A`.
(`σ_y^A = ⊤` is allowed; then `s < ⊤` holds too.) -/
theorem lt_sigmaA_of_runMaxA_lt {y : ℤ} {s : ℕ} (h : runMaxA p m U hA s < y) :
    (s : WithTop ℕ) < sigmaA p m U hA y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk, hAR⟩ := sigmaA_le_iff.mp hcon
  have h1 : y ≤ runMaxA p m U hA k := hAR.1
  have h2 : runMaxA p m U hA k ≤ runMaxA p m U hA s := runMaxA_mono hk
  omega

/-- **The paper's `σ_{y+2m}^A ≥ σ_y^A + 2m`, stated honestly in `WithTop ℕ`.**  No finiteness
hypothesis is needed: the `⊤` cases are handled by `⊤ + k = ⊤` and `σ_y^A ≤ σ_{y+2m}^A`. -/
theorem sigmaA_add_two_m_le {y : ℤ} (hy : 0 ≤ y) :
    sigmaA p m U hA y + ((2 * m : ℕ) : WithTop ℕ) ≤
      sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) := by
  rcases eq_or_ne (sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ))) ⊤ with htop | hfin
  · rw [htop]; exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    obtain ⟨j, -, hjeq⟩ := sigmaA_nesting_two_m (p := p) (m := m) (U := U) (hA := hA) hy hn.symm
    have hsep : j + 2 * m ≤ n :=
      sigmaA_trial_sep (p := p) (m := m) (U := U) (hA := hA) hy hjeq hn.symm
    rw [hjeq, ← hn]
    change ((j + 2 * m : ℕ) : WithTop ℕ) ≤ ((n : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr hsep

/-! ## 2. The window `R_s^A < y ≤ R_t^A - 2m`: finiteness and the exact integer bounds -/

/-- **The window bounds.**  For a nonnegative integer level `y` with `R_s^A < y` and
`y + 2m ≤ R_t^A`, the first passage `σ_y^A` and the next passage `σ_{y+2m}^A` of the same residue
class are finite integers `j`, `n` with

`s < j`,  `j + 2m ≤ n`,  `n ≤ t`.

This is the deterministic content of "the trials counted in the window `[s,t]` are decided inside
`[s,t]`": the `2m-1` steps observed by `Γ_y^A` start at `j > s` and end at `j + 2m - 1 < n ≤ t`. -/
theorem window_bounds {y : ℤ} (hy : 0 ≤ y) {s t : ℕ}
    (hs : runMaxA p m U hA s < y)
    (ht : y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    ∃ j n : ℕ,
      sigmaA p m U hA y = (j : WithTop ℕ) ∧
        sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ) ∧
          s < j ∧ j + 2 * m ≤ n ∧ n ≤ t := by
  have hy1 : y ≤ runMaxA p m U hA t := by omega
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (sigmaA_ne_top_of_runMaxA_le hy1)
  have hjle : j ≤ t := by
    have h := sigmaA_le_of_record_le' (y := y) (t := t) hy1
    rw [← hj] at h
    exact WithTop.coe_le_coe.mp h
  have hslt : s < j := by
    have h := lt_sigmaA_of_runMaxA_lt (y := y) hs
    rw [← hj] at h
    exact WithTop.coe_lt_coe.mp h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
    (sigmaA_ne_top_of_runMaxA_le (y := y + ((2 * m : ℕ) : ℤ)) ht)
  have hnle : n ≤ t := by
    have h := sigmaA_le_of_record_le' (y := y + ((2 * m : ℕ) : ℤ)) (t := t) ht
    rw [← hn] at h
    exact WithTop.coe_le_coe.mp h
  have hsep : j + 2 * m ≤ n := sigmaA_trial_sep hy hj.symm hn.symm
  exact ⟨j, n, hj.symm, hn.symm, hslt, hsep, hnle⟩

/-- The same window bounds with the paper's literal right-hand hypothesis `y ≤ R_t^A - 2m`. -/
theorem window_bounds_paper {y : ℤ} (hy : 0 ≤ y) {s t : ℕ}
    (hs : runMaxA p m U hA s < y)
    (ht : y ≤ runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)) :
    ∃ j n : ℕ,
      sigmaA p m U hA y = (j : WithTop ℕ) ∧
        sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ) ∧
          s < j ∧ j + 2 * m ≤ n ∧ n ≤ t := by
  refine window_bounds (p := p) (m := m) (U := U) (hA := hA) hy hs ?_
  omega

/-! ### A tiny arithmetic helper, kept in `ℕ` so that no mixed `ℤ`/`ℕ` context disturbs it -/

/-- If `j + 2m ≤ n ≤ t` and `1 ≤ m` then the finishing time `j + 2m - 1` is strictly before `t`
(and hence at most `t - 1`). -/
theorem window_arith {j n t m : ℕ} (hm : 1 ≤ m) (h1 : j + 2 * m ≤ n) (h2 : n ≤ t) :
    j + (2 * m - 1) ≤ t - 1 ∧ j + (2 * m - 1) < t := by
  have h3 : j + 2 * m ≤ t := le_trans h1 h2
  have h4 : (2 * m - 1) + 1 = 2 * m := by omega
  have h5 : j + (2 * m - 1) < t := by omega
  exact ⟨Nat.le_sub_one_of_lt h5, h5⟩

/-- **The paper's `σ_y^A + 2m - 1 ≤ t - 1`**, together with `σ_{y+2m}^A ≤ t` and the strict form
`σ_y^A + 2m - 1 < t`.  Requires `1 ≤ m`. -/
theorem window_end_le {y : ℤ} (hy : 0 ≤ y) (hm : 1 ≤ m) {s t : ℕ}
    (hs : runMaxA p m U hA s < y)
    (ht : y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    ∃ j n : ℕ,
      sigmaA p m U hA y = (j : WithTop ℕ) ∧
        sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ) ∧
          s < j ∧ (j + (2 * m - 1) ≤ t - 1) ∧ (j + (2 * m - 1) < t) ∧ n ≤ t := by
  obtain ⟨j, n, hj, hn, hslt, hsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) hy hs ht
  obtain ⟨h1, h2⟩ := window_arith hm hsep hnle
  exact ⟨j, n, hj, hn, hslt, h1, h2, hnle⟩

/-- **Every time of the trial lies strictly inside the window.**  If `R_s^A < y ≤ R_t^A - 2m`
and `1 ≤ m`, then all `2m - 1` observed steps of `Γ_y^A`, namely the times
`σ_y^A, σ_y^A + 1, …, σ_y^A + 2m - 1`, satisfy `s < · < t`. -/
theorem window_trial_inside {y : ℤ} (hy : 0 ≤ y) (hm : 1 ≤ m) {s t : ℕ}
    (hs : runMaxA p m U hA s < y)
    (ht : y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    ∃ j n : ℕ,
      sigmaA p m U hA y = (j : WithTop ℕ) ∧
        sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ) ∧
          s < j ∧ j + 2 * m ≤ n ∧ n ≤ t ∧
            (∀ u : ℕ, u ≤ 2 * m - 1 → s < j + u ∧ j + u < t) := by
  obtain ⟨j, n, hj, hn, hslt, hsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) hy hs ht
  obtain ⟨-, hlast⟩ := window_arith hm hsep hnle
  exact ⟨j, n, hj, hn, hslt, hsep, hnle, fun u hu => ⟨by omega, by omega⟩⟩

/-- **The paper's window sentence in a single statement.**  For `0 ≤ y`, `1 ≤ m`, `R_s^A < y` and
`y + 2m ≤ R_t^A`:

* `s < σ_y^A`  (the first passage has not happened by time `s`),
* `σ_y^A + 2m ≤ σ_{y+2m}^A`  (the passes of one residue class are `2m` apart),
* `σ_{y+2m}^A ≤ t`  (the next passage happens inside the window), and
* `σ_y^A + 2m - 1 ≤ t - 1`  (the whole trial `Γ_y^A` is decided inside the window).

The first three are `WithTop ℕ` comparisons; all four are sharp, since `σ_{y+2m}^A = t` is
attained on the all-zero reference array (`WindowSharp.window_bound_sharp`). -/
theorem window_gateway {y : ℤ} (hy : 0 ≤ y) (hm : 1 ≤ m) {s t : ℕ}
    (hs : runMaxA p m U hA s < y)
    (ht : y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    (s : WithTop ℕ) < sigmaA p m U hA y ∧
      sigmaA p m U hA y + ((2 * m : ℕ) : WithTop ℕ) ≤
        sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) ∧
      sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) ≤ (t : WithTop ℕ) ∧
      sigmaA p m U hA y + ((2 * m - 1 : ℕ) : WithTop ℕ) ≤ ((t - 1 : ℕ) : WithTop ℕ) := by
  obtain ⟨j, n, hj, hn, hslt, hsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) hy hs ht
  obtain ⟨h1, -⟩ := window_arith hm hsep hnle
  refine ⟨?_, sigmaA_add_two_m_le (p := p) (m := m) (U := U) (hA := hA) hy, ?_, ?_⟩
  · rw [hj]
    exact WithTop.coe_lt_coe.mpr hslt
  · rw [hn]
    exact WithTop.coe_le_coe.mpr hnle
  · rw [hj]
    change ((j + (2 * m - 1) : ℕ) : WithTop ℕ) ≤ ((t - 1 : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr h1

/-! ## 3. Distinctness of the finishing times `σ_y^A + 2m - 1` -/

/-- **First passages at a common time have equal level.**  At a finite first passage the group
record *equals* the level (`ARMax.eq`, which needs `0 ≤ y`), so two such passages at one time `n`
force `y = y'`. -/
theorem sigmaA_eq_of_eq_coe {y y' : ℤ} (hy : 0 ≤ y) (hy' : 0 ≤ y') {n : ℕ}
    (h : sigmaA p m U hA y = (n : WithTop ℕ))
    (h' : sigmaA p m U hA y' = (n : WithTop ℕ)) : y = y' := by
  have h1 : runMaxA p m U hA n = y := (sigmaA_eq_coe_iff.mp h).eq hy
  have h2 : runMaxA p m U hA n = y' := (sigmaA_eq_coe_iff.mp h').eq hy'
  rw [h1] at h2
  exact h2

/-- **Distinct nonnegative levels have distinct finishing times.**  If `σ_y^A = j` and
`σ_{y'}^A = j'` are finite and `j + (2m-1) = j' + (2m-1)` then `y = y'`. -/
theorem sigmaA_finish_inj {y y' : ℤ} (hy : 0 ≤ y) (hy' : 0 ≤ y') {j j' : ℕ}
    (h : sigmaA p m U hA y = (j : WithTop ℕ))
    (h' : sigmaA p m U hA y' = (j' : WithTop ℕ))
    (heq : j + (2 * m - 1) = j' + (2 * m - 1)) : y = y' := by
  have hjj : j = j' := by omega
  subst hjj
  exact sigmaA_eq_of_eq_coe hy hy' h h'

/-- Contrapositive form of `sigmaA_finish_inj`: distinct levels finish at distinct times. -/
theorem sigmaA_finish_ne {y y' : ℤ} (hy : 0 ≤ y) (hy' : 0 ≤ y') {j j' : ℕ}
    (h : sigmaA p m U hA y = (j : WithTop ℕ))
    (h' : sigmaA p m U hA y' = (j' : WithTop ℕ)) (hne : y ≠ y') :
    j + (2 * m - 1) ≠ j' + (2 * m - 1) :=
  fun heq => hne (sigmaA_finish_inj hy hy' h h' heq)

/-- **The count of window trials equals the count of occupied times.**  For a finite set `Y` of
integer levels all lying in the window `R_s^A < y ≤ R_t^A - 2m`, the finishing times
`σ_y^A + 2m - 1` are pairwise distinct, so the image of `Y` under `y ↦ σ_y^A + 2m - 1` has the
same cardinality as `Y`.  This is the combinatorial step that lets a sum of `𝟙_{Γ_y^A}` over the
window be replaced by a sum of bounded increments at distinct times. -/
theorem window_finish_card {s t : ℕ} (Y : Finset ℤ)
    (hs : ∀ y ∈ Y, runMaxA p m U hA s < y)
    (ht : ∀ y ∈ Y, y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    (Y.image (fun y => sigmaA p m U hA y + ((2 * m - 1 : ℕ) : WithTop ℕ))).card = Y.card := by
  classical
  refine Finset.card_image_of_injOn (fun y hyY y' hy'Y heq => ?_)
  have hy0 : 0 ≤ y :=
    (runMaxA_nonneg (p := p) (m := m) (U := U) (hA := hA) s).trans_lt (hs y hyY) |>.le
  have hy0' : 0 ≤ y' :=
    (runMaxA_nonneg (p := p) (m := m) (U := U) (hA := hA) s).trans_lt (hs y' hy'Y) |>.le
  have hle : y ≤ runMaxA p m U hA t := by
    have h := ht y hyY
    have h2m : (0 : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by positivity
    omega
  have hle' : y' ≤ runMaxA p m U hA t := by
    have h := ht y' hy'Y
    have h2m : (0 : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by positivity
    omega
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (sigmaA_ne_top_of_runMaxA_le hle)
  obtain ⟨j', hj'⟩ := WithTop.ne_top_iff_exists.mp (sigmaA_ne_top_of_runMaxA_le hle')
  rw [← hj, ← hj'] at heq
  have heq' : ((j + (2 * m - 1) : ℕ) : WithTop ℕ) = ((j' + (2 * m - 1) : ℕ) : WithTop ℕ) := heq
  exact sigmaA_finish_inj hy0 hy0' hj.symm hj'.symm (WithTop.coe_inj.mp heq')

/-- `lvl y0 m` is injective in the index when `1 ≤ m`. -/
theorem lvl_inj {y0 : ℤ} (hm : 1 ≤ m) : Function.Injective (fun i => lvl y0 m i) := by
  intro i j hij
  have h : (i : ℤ) * ((2 * m : ℕ) : ℤ) = (j : ℤ) * ((2 * m : ℕ) : ℤ) := by
    simp only [lvl] at hij
    linarith
  have hc : ((2 * m : ℕ) : ℤ) ≠ 0 := by
    have hpos : (0 : ℤ) < ((2 * m : ℕ) : ℤ) := by
      have : 0 < 2 * m := by omega
      exact_mod_cast this
    omega
  have h2 : (i : ℤ) = (j : ℤ) := mul_right_cancel₀ hc h
  exact_mod_cast h2

/-- **Distinctness in the residue-class parametrisation.**  For the levels
`lvl y0 m i = y0 + 2mi` of one class, `1 ≤ m` makes the index map injective, and if all `K`
levels `i < K` lie in the window then the `K` finishing times are distinct: the `K` trials of the
class occupy `K` distinct times strictly inside `(s,t)`.

This is the interface to `GammaTail`'s residue-class levels.  It is index bookkeeping only: no
probability, no count tail, and no union over classes — those are the separate direction (A). -/
theorem window_finish_card_lvl {y0 : ℤ} (hy0 : 0 ≤ y0) (hm : 1 ≤ m) {s t : ℕ} (K : ℕ)
    (hs : runMaxA p m U hA s < y0)
    (ht : ∀ i ∈ Finset.range K, lvl y0 m i + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t) :
    (((Finset.range K).image (fun i => lvl y0 m i)).image
      (fun y => sigmaA p m U hA y + ((2 * m - 1 : ℕ) : WithTop ℕ))).card = K := by
  classical
  set Y : Finset ℤ := (Finset.range K).image (fun i => lvl y0 m i) with hY
  have hYK : Y.card = K := by
    rw [hY, Finset.card_image_of_injective _ (lvl_inj (m := m) hm), Finset.card_range]
  have hcard := window_finish_card (p := p) (m := m) (U := U) (hA := hA) (s := s) (t := t) Y
    (fun y hyY => ?_) (fun y hyY => ?_)
  · rwa [hcard]
  · rw [hY] at hyY
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyY
    have h1 : y0 ≤ lvl y0 m i := by
      simp only [lvl]
      have h2 : (0 : ℤ) ≤ (i : ℤ) * ((2 * m : ℕ) : ℤ) := by positivity
      linarith
    exact hs.trans_le h1
  · rw [hY] at hyY
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hyY
    exact ht i hi

/-- **Event containment**: every finishing time of a window level lies in `[s+1, t-1]` (as an
element of `WithTop ℕ`).  Combined with `window_finish_card`, the trials of `Y` occupy `Y.card`
distinct times inside `[s+1, t-1]`, so a sum of one bounded increment per occupied time is a sum
over times that are all strictly inside the window. -/
theorem window_finish_mem_Icc {s t : ℕ} (hm : 1 ≤ m) (Y : Finset ℤ)
    (hs : ∀ y ∈ Y, runMaxA p m U hA s < y)
    (ht : ∀ y ∈ Y, y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t)
    {z : WithTop ℕ}
    (hz : z ∈ Y.image (fun y => sigmaA p m U hA y + ((2 * m - 1 : ℕ) : WithTop ℕ))) :
    ((s + 1 : ℕ) : WithTop ℕ) ≤ z ∧ z ≤ ((t - 1 : ℕ) : WithTop ℕ) := by
  classical
  obtain ⟨y, hyY, rfl⟩ := Finset.mem_image.mp hz
  have hy0 : 0 ≤ y :=
    (runMaxA_nonneg (p := p) (m := m) (U := U) (hA := hA) s).trans_lt (hs y hyY) |>.le
  obtain ⟨j, n, hj, hn, hslt, hsep, hnle⟩ :=
    window_bounds (p := p) (m := m) (U := U) (hA := hA) hy0 (hs y hyY) (ht y hyY)
  obtain ⟨h1, -⟩ := window_arith hm hsep hnle
  rw [hj]
  constructor
  · change ((s + 1 : ℕ) : WithTop ℕ) ≤ ((j + (2 * m - 1) : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr
      (le_trans (Nat.succ_le_of_lt hslt) (Nat.le_add_right j (2 * m - 1)))
  · change ((j + (2 * m - 1) : ℕ) : WithTop ℕ) ≤ ((t - 1 : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr h1

/-! ## 4. Measurability at time `t`: the trial is decided inside the window -/

/-- **`Γ_y^A ∩ {σ_{y+2m}^A ≤ t}` is `enlFilt p m t`-measurable.**  The trial at level `y` is
already decided at the next passage of the residue class (`measurableSet_GammaSet_next`), and on
`{σ_{y+2m}^A ≤ t}` that passage happens at one of the finitely many times `n ≤ t`. -/
theorem measurableSet_GammaSet_inter_sigmaA_le {y : ℤ} (hy : 0 ≤ y) (t : ℕ) :
    MeasurableSet[enlFilt (N := N) p m t]
      (GammaSet p m hA y ∩
        {U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) ≤ (t : WithTop ℕ)}) := by
  classical
  have hEq : GammaSet p m hA y ∩
      {U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) ≤ (t : WithTop ℕ)}
      = ⋃ n ∈ Finset.range (t + 1),
          ({U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) = (n : WithTop ℕ)}
            ∩ GammaSet p m hA y) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro V ⟨hG, hle⟩
      simp only [Set.mem_ofPred_eq] at hle
      have hne : sigmaA p m V hA (y + ((2 * m : ℕ) : ℤ)) ≠ ⊤ :=
        ne_top_of_le_ne_top (WithTop.coe_ne_top) hle
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      have hnle : n ≤ t := by
        rw [← hn] at hle
        exact WithTop.coe_le_coe.mp hle
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnle), hn.symm, hG⟩⟩
    · rintro V hV
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_ofPred_eq] at hV ⊢
      obtain ⟨n, hnlt, hEqn, hG⟩ := hV
      refine ⟨hG, ?_⟩
      rw [hEqn]
      exact WithTop.coe_le_coe.mpr (Nat.lt_succ_iff.mp hnlt)
  rw [hEq]
  refine Finset.measurableSet_biUnion _ (fun n hn => ?_)
  exact (enlFilt (N := N) p m).mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) _
    (measurableSet_GammaSet_next p m n A hA y hy)

/-- The window event in record form: `{σ_{y+2m}^A ≤ t} = {y + 2m ≤ R_t^A}`. -/
theorem sigmaA_le_set_eq_runMaxA {y : ℤ} (hy : 0 ≤ y) (t : ℕ) :
    {U : Array N | sigmaA p m U hA (y + ((2 * m : ℕ) : ℤ)) ≤ (t : WithTop ℕ)}
      = {U : Array N | y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t} := by
  ext V
  exact sigmaA_le_iff_runMaxA_le (U := V) (by positivity) (t := t)

/-- **`Γ_y^A ∩ {y + 2m ≤ R_t^A}` is `enlFilt p m t`-measurable.**  This is the form in which
"only trials that finish inside `[s,t]` are summed, at time `t`" enters a time-`t` argument. -/
theorem measurableSet_GammaSet_inter_window {y : ℤ} (hy : 0 ≤ y) (t : ℕ) :
    MeasurableSet[enlFilt (N := N) p m t]
      (GammaSet p m hA y ∩ {U : Array N | y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t}) := by
  rw [← sigmaA_le_set_eq_runMaxA (p := p) (m := m) (hA := hA) (y := y) hy t]
  exact measurableSet_GammaSet_inter_sigmaA_le (p := p) (m := m) (hA := hA) hy t

/-- The same measurability when the window condition is known to hold on the whole space. -/
theorem measurableSet_GammaSet_of_window_all {y : ℤ} (hy : 0 ≤ y) (t : ℕ)
    (hwin : ∀ V : Array N, y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m V hA t) :
    MeasurableSet[enlFilt (N := N) p m t] (GammaSet p m hA y) := by
  have h := measurableSet_GammaSet_inter_window (p := p) (m := m) (hA := hA) (y := y) hy t
  have huniv : {U : Array N | y + ((2 * m : ℕ) : ℤ) ≤ runMaxA p m U hA t} = Set.univ := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hwin V
  rwa [huniv, Set.inter_univ] at h

end Swarming.Enl


