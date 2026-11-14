/-
# The windowed `(locgroup)` martingale: truncation, envelope, telescope and maximal deviation

Display `(locgroup)` of Proposition `local` says: for disjoint nonempty `I, J`, if `(sep)` holds at
every integer `u ∈ [s,t)`, then `W_t^{I,J} - W_s^{I,J} ≤ C_T L^{3/4}`.

The accepted file `LocGroupWindow` proves the maximal deviation estimate for the `GoodW`-truncated
martingale, where `GoodW` bounds the *prefix* envelopes `Efix`/`Esum` (suprema over all levels
`u ≤ xTop`).  `PrefixObstruction` shows that no window data can ever supply `GoodW`: a long block of
unmarked sites far below the record window makes `Efix` huge.  `WindowEnvelope`/`WindowStep`/
`WindowIncrement` supply the repair: the *windowed* envelopes `EfixWin A`/`EsumWin A` (suprema over
the level window `[A-1, xTop]`, exactly the range the record geometry controls) are enough for the
one-step size bound `|W_{n+1}-W_n| ≤ envB` and the drift `(Wdrift)` remains valid because the
truncation set is still contained in `(sep)`.

What was missing is the martingale itself on the windowed envelope.  This file supplies it:

* `winTrunc` — the truncation event: the windowed good event `SiteWindow.GoodWWin` together with the
  record geometry (all positions at or above the level window's left edge `A`), which is what the
  windowed one-step bound needs and what the record window supplies;
* `incTW`, `dQTW` — the truncated increment and its centred version, with
  `condExp dQTW = 0` (a genuine `posFilt`-martingale difference), `|dQTW| ≤ 2 envB` a.e.;
* `ae_telescope_winTrunc` — the paper's summation of `(Wdrift)` on a window on which `winTrunc`
  holds at every time;
* `measure_all_windows_le` — **the simultaneous `(locgroup)` deviation bound**: the display for
  *every* sub-window `[s,t)` of the record window at once, from a single maximal Azuma bound.

Nothing here estimates `GoodWWin` itself, the record geometry, `(locmax)`, the invariant law,
regeneration or the speed; those are the explicit inputs, named in
`LocGroupSimultaneous.lean`.
-/
import Swarm.LocMaxWindow
import Swarm.LocGroupWindow
import Swarm.QplWindow
import Swarm.ScaleArithmetic

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1

namespace LocGroupSimul

variable {N : ℕ}

/-! ## 1. Splitting a `LocMart.psum` at an earlier start -/

/-- `psum` over `[a, a+k)` is the difference of the global partial sums. -/
theorem psum_sub_eq (ξ : ℕ → Array N → ℝ) (a : ℕ) :
    ∀ k : ℕ, LocMart.psum (fun j => ξ (a + j)) k
      = fun U => LocMart.psum ξ (a + k) U - LocMart.psum ξ a U := by
  intro k
  induction k with
  | zero => funext U; simp [LocMart.psum]
  | succ k ih =>
      funext U
      rw [LocMart.psum_succ, ih]
      have h1 : a + (k + 1) = (a + k) + 1 := by ring
      rw [h1, LocMart.psum_succ]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring

/-! ## 2. One-step geometry of the running record -/

/-- The running record can increase by at most one per step. -/
theorem runMax_succ_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    runMax p m U i (n + 1) ≤ runMax p m U i n + 1 := by
  rw [runMax, runMax]
  refine Finset.sup'_le _ _ fun t ht => ?_
  rw [Finset.mem_range] at ht
  rcases lt_or_eq_of_le (show t ≤ n + 1 by omega) with h | h
  · have hmem : t ∈ Finset.range (n + 1) := Finset.mem_range.mpr h
    have h1 := Finset.le_sup' (fun t => (trajectory p m U t).pos i) hmem
    linarith
  · subst h
    have h2 := Swarming.Trajectory.pos_succ_le p m U n i
    have h3 := Finset.le_sup' (fun t => (trajectory p m U t).pos i)
      (Finset.mem_range.mpr (Nat.lt_succ_self n) : n ∈ Finset.range (n + 1))
    linarith

/-- The running record grows at most linearly: `M_n ≤ M_{n₀} + (n - n₀)`. -/
theorem runMax_le_add_run (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) {n0 n : ℕ} (h : n0 ≤ n) :
    runMax p m U i n ≤ runMax p m U i n0 + ((n - n0 : ℕ) : ℤ) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have h1 : runMax p m U i (n + 1) ≤ runMax p m U i n + 1 := runMax_succ_le p m U i n
      have h2 : ((n + 1 - n0 : ℕ) : ℤ) = ((n - n0 : ℕ) : ℤ) + 1 := by
        rw [Nat.succ_sub hn]; push_cast; ring
      rw [h2]; linarith

/-! ## 3. The record hypothesis `{d_r ≤ L}` at the record time -/

/-- The paper's record localisation at the (random) record time `n0`: every position is at least
`r - L` and every running record is at most `r`.  At `n0 = τ_r` and on `{d_r ≤ L}` this holds
(`M_{τ_r}^k ≤ r` because `τ_r` is the *first* time the maximum reaches `r`, and
`M_{τ_r}^k ≥ X_{τ_r}^k ≥ r - d_r ≥ r - L`). -/
def RecHyp (p : ℝ) (m : ℕ) (r n0 L : ℕ) (U : Array N) : Prop :=
  (∀ i : Fin N, (r : ℤ) - (L : ℤ) ≤ (trajectory p m U n0).pos i) ∧
    (∀ k : Fin N, runMax p m U k n0 ≤ (r : ℤ))

/-- The running record is monotone in time. -/
theorem runMax_mono_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) {a b : ℕ} (h : a ≤ b) :
    runMax p m U i a ≤ runMax p m U i b := by
  rw [runMax, runMax]
  refine Finset.sup'_le _ _ fun t ht => ?_
  refine Finset.le_sup' (fun t => (trajectory p m U t).pos i) ?_
  rw [Finset.mem_range] at ht ⊢
  omega

/-- **Containment in the record window.**  On `RecHyp` at `n0`, for every `n ∈ [n0, n0+TL]` every
running record lies in `[r-(T+1)L, r+TL]`. -/
theorem RecHyp_runMax_bounds {p : ℝ} {m : ℕ} {r n0 L T : ℕ} {U : Array N}
    (hrec : RecHyp p m r n0 L U) {n : ℕ} (hn0 : n0 ≤ n) (hnT : n ≤ n0 + T * L) :
    ∀ k : Fin N, (r : ℤ) - (((T + 1) * L : ℕ) : ℤ) ≤ runMax p m U k n
      ∧ runMax p m U k n ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
  intro k
  obtain ⟨hpos, hmax⟩ := hrec
  have hM0 : (r : ℤ) - (L : ℤ) ≤ runMax p m U k n0 :=
    le_trans (hpos k) (Swarming.Trajectory.le_runMax p m U k n0)
  have hstep := runMax_le_add_run p m U k hn0
  have hcast : ((n - n0 : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    exact_mod_cast (by omega : n - n0 ≤ T * L)
  have hTL : (((T + 1) * L : ℕ) : ℤ) = (L : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h : ((T + 1) * L : ℕ) = L + T * L := by ring
    rw [h]; push_cast; ring
  have hmono : runMax p m U k n0 ≤ runMax p m U k n := runMax_mono_le p m U k hn0
  have hmaxk : runMax p m U k n0 ≤ (r : ℤ) := hmax k
  constructor
  · rw [hTL]; linarith
  · linarith

/-- **Position lower bound in the record window.**  On `RecHyp` at `n0`, for every
`n ∈ [n0, n0+TL]` every position is at least `r-(T+1)L`. -/
theorem RecHyp_pos_ge {p : ℝ} {m : ℕ} {r n0 L T : ℕ} {U : Array N}
    (hrec : RecHyp p m r n0 L U) {n : ℕ} (hn0 : n0 ≤ n) (hnT : n ≤ n0 + T * L) :
    ∀ k : Fin N, (r : ℤ) - (((T + 1) * L : ℕ) : ℤ) ≤ (trajectory p m U n).pos k := by
  intro k
  obtain ⟨hpos, hmax⟩ := hrec
  have h1 : (trajectory p m U n0).pos k - ((n - n0 : ℕ) : ℤ) ≤ (trajectory p m U (n0 + (n - n0))).pos k :=
    QplWindow.pos_sub_run_le p m U k n0 (n - n0)
  rw [Nat.add_sub_cancel' hn0] at h1
  have hcast : ((n - n0 : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    exact_mod_cast (by omega : n - n0 ≤ T * L)
  have hTL : (((T + 1) * L : ℕ) : ℤ) = (L : ℤ) + ((T * L : ℕ) : ℤ) := by
    have h : ((T + 1) * L : ℕ) = L + T * L := by ring
    rw [h]; push_cast; ring
  rw [hTL]; linarith [hpos k]

/-! ## 4. The windowed truncation event -/

/-- The truncation event of the windowed `(locgroup)` martingale at time `n`: the windowed good
event of `SiteWindow` (separation together with the *level window* envelope bounds at level `B`
and left edge `A`) and the *predictable* record geometry: every position at time `n` is at least
`A+1`.

Both conjuncts are `posFilt n`-measurable, so the truncation is genuinely predictable.  The
`+1` is what makes the future one-step conditions of `SiteWindow.abs_WA_step_le_window` follow from
the unit-step property alone: a walker at `≥ A+1` at time `n` is at `≥ A` at time `n+1`, so the
level window `[A-1, xTop]` is untouched by the step.  On the record window every position is at
least `r-(T+1)L = A+L`, so the truncation is active there with `A = r-(T+2)L-1`. -/
def winTrunc (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (B : ℝ) (A : ℕ)
    (U : Array N) : Prop :=
  SiteWindow.GoodWWin p m n I J hI B A U ∧
    (∀ k : Fin N, A + 1 ≤ (X p m U n k).toNat)

theorem winTrunc_sep {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty} {B : ℝ} {A : ℕ}
    {U : Array N} (h : winTrunc p m n I J hI B A U) : SepSet p m n I J U := h.1.1

/-- Measurability of the truncation event, in `posFilt n`: it is predictable. -/
theorem measurableSet_winTrunc (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (B : ℝ) (A : ℕ) :
    MeasurableSet[posFilt N p m n] {U : Array N | winTrunc p m n I J hI B A U} := by
  have hK : (I ∪ J).Nonempty := Finset.Nonempty.mono (Finset.subset_union_left) hI
  have hsep : MeasurableSet[posFilt N p m n] {U : Array N | SepSet p m n I J U} :=
    measurableSet_sepSet p m n I J
  have h1 : MeasurableSet[posFilt N p m n]
      {U : Array N | SiteWindow.EfixWin p m n J (I ∪ J) hK A U ≤ B} :=
    measurableSet_le (SiteWindow.measurable_EfixWin p m n J (I ∪ J) hK A) measurable_const
  have h2 : MeasurableSet[posFilt N p m n]
      {U : Array N | SiteWindow.EsumWin p m n J (I ∪ J) hK A U ≤ B} :=
    measurableSet_le (SiteWindow.measurable_EsumWin p m n J (I ∪ J) hK A) measurable_const
  have hposn : MeasurableSet[posFilt N p m n]
      {U : Array N | ∀ k : Fin N, A + 1 ≤ (X p m U n k).toNat} := by
    have heq : {U : Array N | ∀ k : Fin N, A + 1 ≤ (X p m U n k).toNat}
        = ⋂ k : Fin N, {U : Array N | A + 1 ≤ (X p m U n k).toNat} := by
      ext U; simp
    rw [heq]
    refine MeasurableSet.iInter fun k => ?_
    letI : MeasurableSpace (Array N) := posFilt N p m n
    exact measurableSet_le measurable_const (by
      have h : Measurable (fun U : Array N => (trajectory p m U n).pos k) :=
        measurable_pos_posFilt p m k le_rfl
      exact measurable_int_toNat h)
  exact (hsep.inter (h1.inter h2)).inter hposn

/-! ## 5. The truncated increment and its centred version -/

/-- The `winTrunc`-truncated increment `1_{winTrunc}(W_{n+1} - W_n)`. -/
noncomputable def incTW (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (U : Array N) : ℝ :=
  ({U | winTrunc p m n I J hI B A U}).indicator
    (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U

/-- The centred truncated increment: the windowed `(locgroup)` martingale difference. -/
noncomputable def dQTW (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) (U : Array N) : ℝ :=
  incTW p m n I J hI hJ B A U
    - condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U

theorem incTW_of_mem {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty}
    {hJ : J.Nonempty} {B : ℝ} {A : ℕ} {U : Array N}
    (hU : U ∈ {U : Array N | winTrunc p m n I J hI B A U}) :
    incTW p m n I J hI hJ B A U
      = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ :=
  Set.indicator_of_mem hU _

theorem incTW_of_notMem {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty}
    {hJ : J.Nonempty} {B : ℝ} {A : ℕ} {U : Array N}
    (hU : U ∉ {U : Array N | winTrunc p m n I J hI B A U}) :
    incTW p m n I J hI hJ B A U = 0 :=
  Set.indicator_of_notMem hU _

theorem measurable_incTW_succ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    Measurable[posFilt N p m (n + 1)] (incTW p m n I J hI hJ B A) := by
  have h1 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U (n + 1) I J hI hJ) :=
    measurable_WA_posFilt p m (n + 1) I J hI hJ
  have h2 : Measurable[posFilt N p m (n + 1)] (fun U => WA p m U n I J hI hJ) :=
    (measurable_WA_posFilt p m n I J hI hJ).mono ((posFilt N p m).mono (Nat.le_succ n)) le_rfl
  have h3 : MeasurableSet[posFilt N p m (n + 1)] {U : Array N | winTrunc p m n I J hI B A U} :=
    ((posFilt N p m).mono (Nat.le_succ n)) _ (measurableSet_winTrunc p m n I J hI B A)
  exact (h1.sub h2).indicator h3

theorem integrable_incTW {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    Integrable (incTW p m n I J hI hJ B A) (arrayMeasure N) :=
  ((integrable_WA hp hp1 m (n + 1) I J hI hJ).sub
      (integrable_WA hp hp1 m n I J hI hJ)).indicator
    (((posFilt N p m).le n) _ (measurableSet_winTrunc p m n I J hI B A))

theorem integrable_condExp_incTW {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N)
      (incTW p m n I J hI hJ B A) U) (arrayMeasure N) := by
  haveI := integrable_incTW (N := N) hp hp1 m n I J hI hJ B A
  exact integrable_condExp

theorem integrable_dQTW {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    Integrable (dQTW p m n I J hI hJ B A) (arrayMeasure N) :=
  (integrable_incTW (N := N) hp hp1 m n I J hI hJ B A).sub
    (integrable_condExp_incTW (N := N) hp hp1 m n I J hI hJ B A)

theorem stronglyMeasurable_dQTW (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    StronglyMeasurable[posFilt N p m (n + 1)] (dQTW p m n I J hI hJ B A) := by
  have hinc : StronglyMeasurable[posFilt N p m (n + 1)] (fun U => incTW p m n I J hI hJ B A U) :=
    (measurable_incTW_succ p m n I J hI hJ B A).stronglyMeasurable
  have hce : StronglyMeasurable[posFilt N p m (n + 1)]
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U) :=
    stronglyMeasurable_mono_filt (stronglyMeasurable_condExp (μ := arrayMeasure N)
      (m := posFilt N p m n) (f := incTW p m n I J hI hJ B A))
      ((posFilt N p m).mono (Nat.le_succ n))
  exact hinc.sub hce

/-- The drift inequality `(Wdrift)` for the windowed truncation: the truncation set is contained
in `(sep)`, so the conditional mean of the truncated increment is nonpositive. -/
theorem condExp_incTW_nonpos {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) (A : ℕ) :
    condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) ≤ᵐ[arrayMeasure N] 0 := by
  have h := condExp_indicator_WA_drift_le_zero (N := N) hp0 hp1 m n I J hI hJ hid
    (A₀ := {U : Array N | winTrunc p m n I J hI B A U})
    (measurableSet_winTrunc p m n I J hI B A) (fun U hU => winTrunc_sep hU)
  have heq : (fun U : Array N => ({U : Array N | winTrunc p m n I J hI B A U}).indicator
      (fun U => WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) U)
      = incTW p m n I J hI hJ B A := rfl
  rwa [heq] at h

/-- The truncated centred increment is a `posFilt`-martingale difference. -/
theorem condExp_dQTW {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (B : ℝ) (A : ℕ) :
    condExp (posFilt N p m n) (arrayMeasure N) (dQTW p m n I J hI hJ B A)
      =ᵐ[arrayMeasure N] 0 := by
  have hX := integrable_incTW (N := N) hp hp1 m n I J hI hJ B A
  have hY := integrable_condExp_incTW (N := N) hp hp1 m n I J hI hJ B A
  have hsub : condExp (posFilt N p m n) (arrayMeasure N) (dQTW p m n I J hI hJ B A)
      =ᵐ[arrayMeasure N]
        condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A)
          - condExp (posFilt N p m n) (arrayMeasure N)
              (fun U => condExp (posFilt N p m n) (arrayMeasure N)
                (incTW p m n I J hI hJ B A) U) :=
    condExp_sub hX hY _
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => condExp (posFilt N p m n) (arrayMeasure N)
        (incTW p m n I J hI hJ B A) U)
      = fun U => condExp (posFilt N p m n) (arrayMeasure N)
          (incTW p m n I J hI hJ B A) U :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) stronglyMeasurable_condExp hY
  refine hsub.trans ?_
  rw [hpull]
  filter_upwards with U
  simp

/-- **The one-step envelope on the windowed truncation.**  On `winTrunc` the actual separated
group increment is bounded by `stepEnv p B`, with `B` the common level of the windowed envelopes
and `A` the left edge of the level window. -/
theorem abs_incTW_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) (U : Array N) :
    |incTW p m n I J hI hJ B A U| ≤ LocGroupWindow.stepEnv (N := N) p B := by
  by_cases hU : winTrunc p m n I J hI B A U
  · have hmem : U ∈ {U : Array N | winTrunc p m n I J hI B A U} := hU
    obtain ⟨⟨hsep, hf, hs⟩, hposn⟩ := hU
    have hK : (I ∪ J).Nonempty := Finset.Nonempty.mono (Finset.subset_union_left) hI
    set Ef : ℝ := SiteWindow.EfixWin p m n J (I ∪ J) hK A U with hEf
    set Es : ℝ := SiteWindow.EsumWin p m n J (I ∪ J) hK A U with hEs
    have hEf0 : 0 ≤ Ef := SiteWindow.EfixWin_nonneg hp0.le hp1 m n J (I ∪ J) hK A U
    have hEs0 : 0 ≤ Es := SiteWindow.EsumWin_nonneg hp0.le hp1 m n J (I ∪ J) hK A U
    have hEfle : SiteWindow.EfixWin p m n J (I ∪ J) hK A U ≤ Ef := le_of_eq hEf.symm
    have hEsle : SiteWindow.EsumWin p m n J (I ∪ J) hK A U ≤ Es := le_of_eq hEs.symm
    -- positions: `≥ A+1` at time `n` (predictable), hence `≥ A` at time `n+1`
    have hA1 : ∀ k : Fin N, A + 1 ≤ (X p m U n k).toNat := hposn
    have hXn : ∀ k : Fin N, (0 : ℤ) ≤ X p m U n k := by
      intro k
      have h1 : 1 ≤ (X p m U n k).toNat := by have := hA1 k; omega
      by_contra hneg
      push Not at hneg
      have h0 : (X p m U n k).toNat = 0 := Int.toNat_of_nonpos hneg.le
      omega
    have hcastn : ∀ k : Fin N, ((X p m U n k).toNat : ℤ) = X p m U n k :=
      fun k => Int.toNat_of_nonneg (hXn k)
    have hsucc : ∀ k : Fin N, A ≤ (X p m U (n + 1) k).toNat := by
      intro k
      have hAn1 : (A : ℤ) + 1 ≤ X p m U n k := by
        rw [← hcastn k]; exact_mod_cast hA1 k
      rcases X_succ_sub_X p m U n k with h | h
      · have hpos : (0 : ℤ) ≤ X p m U (n + 1) k := by rw [h]; linarith
        have hge : ((X p m U (n + 1) k).toNat : ℤ) = X p m U (n + 1) k :=
          Int.toNat_of_nonneg hpos
        have : (A : ℤ) ≤ ((X p m U (n + 1) k).toNat : ℤ) := by rw [hge, h]; linarith
        exact_mod_cast this
      · have hpos : (0 : ℤ) ≤ X p m U (n + 1) k := by rw [h]; linarith
        have hge : ((X p m U (n + 1) k).toNat : ℤ) = X p m U (n + 1) k :=
          Int.toNat_of_nonneg hpos
        have : (A : ℤ) ≤ ((X p m U (n + 1) k).toNat : ℤ) := by rw [hge, h]; linarith
        exact_mod_cast this
    have hAn : ∀ k ∈ I ∪ J, A ≤ (X p m U n k).toNat + 1 := fun k _ => by
      have := hA1 k; omega
    have hAs : ∀ k ∈ I ∪ J, A ≤ (X p m U (n + 1) k).toNat + 1 := fun k _ => by
      have := hsucc k; omega
    have hag : ∀ u : ℕ, u < A → wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u :=
      SiteWindow.wA_eq_of_positions_ge hp0 (fun i _ => hsucc i)
    have hstep := SiteWindow.abs_WA_step_le_window hp0 hp1 I J hI hJ hid hsep hAn hAs hag
      (B := Ef) (S := Es) hEfle hEsle hEf0 hEs0
    rw [incTW_of_mem hmem, LocGroupWindow.stepEnv_eq]
    have hprod : (1 + Ef) * Es ≤ (1 + B) * B := by
      have h1 : (1 + Ef) * Es ≤ (1 + B) * Es := mul_le_mul_of_nonneg_right (by linarith) hEs0
      have h2 : (1 + B) * Es ≤ (1 + B) * B := mul_le_mul_of_nonneg_left hs (by linarith)
      linarith
    have hcoef : 0 ≤ (2 * p - 1) / p * (N : ℝ) := by
      have hp : (0 : ℝ) < p := by linarith
      have h1 : 0 ≤ (2 * p - 1) / p := div_nonneg (by linarith) hp.le
      have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      exact mul_nonneg h1 h2
    have hmono : (2 * p - 1) / p * (N : ℝ) * ((1 + Ef) * Es)
        ≤ (2 * p - 1) / p * (N : ℝ) * ((1 + B) * B) :=
      mul_le_mul_of_nonneg_left hprod hcoef
    linarith
  · have hmem : U ∉ {U : Array N | winTrunc p m n I J hI B A U} := hU
    rw [incTW_of_notMem hmem, abs_zero]
    exact LocGroupWindow.stepEnv_nonneg hp0 hp1 hB

/-- The conditional mean of the truncated increment has the same envelope a.e. -/
theorem ae_abs_condExp_incTW_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N),
      |condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U|
        ≤ LocGroupWindow.stepEnv (N := N) p B := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set E := LocGroupWindow.stepEnv (N := N) p B with hE
  have hE0 : 0 ≤ E := LocGroupWindow.stepEnv_nonneg hp0 hp1 hB
  have h1 := abs_condExp_ae_le_condExp_abs (μ := arrayMeasure N) (m := posFilt N p m n)
    (f := incTW p m n I J hI hJ B A)
  have hbdd : (|incTW p m n I J hI hJ B A|) ≤ᵐ[arrayMeasure N] fun _ => E :=
    Filter.Eventually.of_forall (fun U => abs_incTW_le (m := m) (n := n) hp0 hp1 I J hI hJ hid hB A U)
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (|incTW p m n I J hI hJ B A|)
      ≤ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) :=
    condExp_mono ((integrable_incTW (N := N) hp0.le hp1 m n I J hI hJ B A).abs)
      (integrable_const E) hbdd
  have h3 : condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) = fun _ => E :=
    condExp_const ((posFilt N p m).le n) E
  filter_upwards [h1, h2] with U h1U h2U
  have h3U : condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) U = E := by rw [h3]
  calc |condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U|
      ≤ condExp (posFilt N p m n) (arrayMeasure N) (|incTW p m n I J hI hJ B A|) U := h1U
    _ ≤ condExp (posFilt N p m n) (arrayMeasure N) (fun _ => E) U := h2U
    _ = E := h3U

/-- **The windowed martingale differences have the doubled envelope a.e.** -/
theorem ae_abs_dQTW_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), |dQTW p m n I J hI hJ B A U| ≤ 2 * LocGroupWindow.stepEnv (N := N) p B := by
  filter_upwards [ae_abs_condExp_incTW_le (N := N) hp0 hp1 I J hI hJ hid hB A] with U hU
  have h2 := abs_incTW_le (m := m) (n := n) hp0 hp1 I J hI hJ hid hB A U
  have hd : dQTW p m n I J hI hJ B A U
      = incTW p m n I J hI hJ B A U
        - condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U := rfl
  rw [hd]
  calc |incTW p m n I J hI hJ B A U
        - condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U|
      ≤ |incTW p m n I J hI hJ B A U|
        + |condExp (posFilt N p m n) (arrayMeasure N) (incTW p m n I J hI hJ B A) U| := abs_sub _ _
    _ ≤ LocGroupWindow.stepEnv (N := N) p B + LocGroupWindow.stepEnv (N := N) p B := add_le_add h2 hU
    _ = 2 * LocGroupWindow.stepEnv (N := N) p B := by ring

/-! ## 6. Telescoping on a window on which the truncation event holds -/

/-- **The paper's summation of `(Wdrift)` for the windowed truncation.**  Almost surely, for every
window `[s, s+K)` on which `winTrunc` holds at every time, the drift corrections are nonpositive
and `W_{s+K} - W_s ≤ Σ_{k<K} dQ_{s+k}`. -/
theorem ae_telescope_winTrunc {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ s K : ℕ,
      (∀ k, s ≤ k → k < s + K → winTrunc p m k I J hI B A U) →
      WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
        + LocMart.psum (fun j => dQTW p m (s + j) I J hI hJ B A) K U := by
  have hdrift : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      condExp (posFilt N p m k) (arrayMeasure N) (incTW p m k I J hI hJ B A) U ≤ 0 :=
    ae_all_iff.mpr (fun k => condExp_incTW_nonpos (N := N) hp0 hp1 m k I J hI hJ hid B A)
  filter_upwards [hdrift] with U hU s K hgood
  have hpt : ∀ k, s ≤ k → k < s + K →
      WA p m U (k + 1) I J hI hJ - WA p m U k I J hI hJ
        ≤ dQTW p m k I J hI hJ B A U := by
    intro k hk hkt
    have hG : winTrunc p m k I J hI B A U := hgood k hk hkt
    have hinc := incTW_of_mem (hJ := hJ) (B := B) (A := A) (U := U) (n := k) (show U ∈ {U : Array N | winTrunc p m k I J hI B A U} from hG)
    have hd : dQTW p m k I J hI hJ B A U
        = incTW p m k I J hI hJ B A U
          - condExp (posFilt N p m k) (arrayMeasure N) (incTW p m k I J hI hJ B A) U := rfl
    have hd0 := hU k
    linarith
  have haux := telescope_aux (a := fun n => WA p m U n I J hI hJ)
    (c := fun n => dQTW p m n I J hI hJ B A U) (s := s) (s + K)
    (Nat.le_add_right s K) hpt
  have hsplit : ∑ k ∈ Finset.range (s + K), dQTW p m k I J hI hJ B A U
      = ∑ k ∈ Finset.range s, dQTW p m k I J hI hJ B A U
        + ∑ j ∈ Finset.range K, dQTW p m (s + j) I J hI hJ B A U := by
    have h := Finset.sum_range_add (fun k => dQTW p m k I J hI hJ B A U) s K
    simpa only [Nat.add_comm] using h
  rw [hsplit] at haux
  simp only [LocMart.psum]
  linarith

/-! ## 7. The maximal deviation bound for the windowed martingale -/

/-- **Maximal deviation of the windowed `(locgroup)` martingale.**
For `K ≥ 1`, `B > 0`, `ε > 0` with the Chernoff side condition `ε ≤ 4 K envB`,

  `μ{∃ k ≤ K, ε ≤ |Σ_{j<k} dQ_{s+j}|} ≤ 2 (K+1) exp (-ε²/(4 K (2 envB p B)²))`.

Same proof as `LocGroupWindow.measure_deviation_goodW_le`, with `dQTW` in place of `dQT`. -/
theorem measure_deviation_dQTW_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) (A : ℕ) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * (K : ℝ) * LocGroupWindow.stepEnv (N := N) p B) :
    (arrayMeasure N).real
      {U : Array N | ∃ k ≤ K,
        ε ≤ |LocMart.psum (fun j => dQTW p m (s + j) I J hI hJ B A) k U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((K : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp1' : p ≤ 1 := le_of_lt hp1
  set E : ℝ := LocGroupWindow.stepEnv (N := N) p B with hE
  have hEpos : 0 < E := LocGroupWindow.stepEnv_pos hp0 hp1' hB
  set S : ℝ := (K : ℝ) * (2 * E) ^ 2 with hS
  have hSpos : 0 < S := by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    rw [hS]; positivity
  have hproxy : LocMax.proxy (fun _ : ℕ => 2 * E) K ≤ S := by
    have h : LocMax.proxy (fun _ : ℕ => 2 * E) K = (K : ℝ) * (2 * E) ^ 2 := by
      simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h, hS]
  have hmeas : ∀ k < K, StronglyMeasurable[(LocGroupWindow.shiftedFilt (N := N) p m s) (k + 1)]
      (fun U => dQTW p m (s + k) I J hI hJ B A U) := by
    intro k hk
    exact stronglyMeasurable_dQTW p m (s + k) I J hI hJ B A
  have hcpos : ∀ k < K, 0 < (fun _ : ℕ => 2 * E) k := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    exact h2
  have hbdd : ∀ k < K, ∀ᵐ U ∂(arrayMeasure N),
      |(fun U => dQTW p m (s + k) I J hI hJ B A U) U| ≤ (fun _ : ℕ => 2 * E) k := by
    intro k hk
    simpa only [hE] using ae_abs_dQTW_le (N := N) hp0 hp1' I J hI hJ hid hB.le (A := A) (n := s + k)
  have hmean : ∀ k < K,
      (arrayMeasure N)[(fun U => dQTW p m (s + k) I J hI hJ B A U)
        | ↑((LocGroupWindow.shiftedFilt (N := N) p m s) k)] =ᵐ[arrayMeasure N] 0 := by
    intro k hk
    exact condExp_dQTW hp0.le hp1' m (s + k) I J hI hJ B A
  have hsideK : ∀ k < K, ε * (fun _ : ℕ => 2 * E) k ≤ 2 * S := by
    intro k hk
    have h2 : (0 : ℝ) < 2 * E := by linarith
    have hcalc : ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := by
      have := mul_le_mul_of_nonneg_right hside (le_of_lt h2)
      simpa only [hE] using this
    have hS8 : 2 * S = 8 * ((K : ℝ) * E ^ 2) := by
      rw [hS]; ring
    rw [hS8]
    calc ε * (2 * E) ≤ (4 * (K : ℝ) * E) * (2 * E) := hcalc
      _ = 8 * ((K : ℝ) * E ^ 2) := by ring
  have key := LocMax.measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := LocGroupWindow.shiftedFilt (N := N) p m s)
    (ξ := fun k U => dQTW p m (s + k) I J hI hJ B A U) (c := fun _ : ℕ => 2 * E)
    (ε := ε) (n := K) (S := S) hK hSpos hproxy hmeas hcpos hbdd hmean hε hsideK
  simpa only [hS, hE] using key

/-! ## 8. Chaining: the display for *every* sub-window at once -/

/-- `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add_le a (-b)

/-- **Chaining.**  Almost surely, on a window `[n0, n0+K)` on which the truncation event holds at
every time, the `(locgroup)` increment over an *arbitrary* sub-window `[s,t)` is at most the sum of
the absolute values of the two partial sums of the windowed martingale measured from `n0`. -/
theorem WA_sub_le_psum_abs {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (B : ℝ) (A : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ (n0 s t K : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ
        ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U| := by
  filter_upwards [ae_telescope_winTrunc (N := N) hp0 hp1 I J hI hJ hid B A] with U htel
  intro n0 s t K hn0 hst htK hwin
  set ξ : ℕ → Array N → ℝ := fun k => dQTW p m k I J hI hJ B A with hξ
  have hgood : ∀ k, s ≤ k → k < s + (t - s) → winTrunc p m k I J hI B A U := by
    intro k hk hkt
    exact hwin k hk (by omega)
  have h1 := htel s (t - s) hgood
  rw [Nat.add_sub_cancel' hst] at h1
  have htn : n0 ≤ t := le_trans hn0 hst
  have hps : LocMart.psum (fun j => ξ (s + j)) (t - s) U
      = LocMart.psum ξ t U - LocMart.psum ξ s U := by
    have h := congrFun (psum_sub_eq ξ s (t - s)) U
    rw [h, Nat.add_sub_cancel' hst]
  have e1 : LocMart.psum ξ t U - LocMart.psum ξ s U
      = LocMart.psum (fun j => ξ (n0 + j)) (t - n0) U
        - LocMart.psum (fun j => ξ (n0 + j)) (s - n0) U := by
    have ht' := congrFun (psum_sub_eq ξ n0 (t - n0)) U
    have hs' := congrFun (psum_sub_eq ξ n0 (s - n0)) U
    rw [ht', hs', Nat.add_sub_cancel' htn, Nat.add_sub_cancel' hn0]
    ring
  have h2 : LocMart.psum ξ t U - LocMart.psum ξ s U
      ≤ |LocMart.psum (fun j => ξ (n0 + j)) (t - n0) U|
        + |LocMart.psum (fun j => ξ (n0 + j)) (s - n0) U| := by
    rw [e1]
    calc LocMart.psum (fun j => ξ (n0 + j)) (t - n0) U
          - LocMart.psum (fun j => ξ (n0 + j)) (s - n0) U
        ≤ |LocMart.psum (fun j => ξ (n0 + j)) (t - n0) U
            - LocMart.psum (fun j => ξ (n0 + j)) (s - n0) U| := le_abs_self _
      _ ≤ |LocMart.psum (fun j => ξ (n0 + j)) (t - n0) U|
            + |LocMart.psum (fun j => ξ (n0 + j)) (s - n0) U| := abs_sub_le_abs_add _ _
  rw [hps] at h1
  simp only [hξ] at h1 h2 ⊢
  linarith

/-- **The simultaneous `(locgroup)` deviation bound.**  On the event that the truncation event
holds at every time of the window `[n0, n0+K)`, the paper's display holds for *every* sub-window
`[s,t) ⊆ [n0, n0+K)` at once, off a set of measure at most the single maximal Azuma bound.

This is the point where the paper's quantifier `for all τ_r ≤ s ≤ t ≤ τ_r + ⌊TL⌋` is matched: the
accepted fixed-window estimate cannot be used directly for a `∀ s t` statement, and a union bound
over the `~ (TL)²` windows would be wasteful; instead the telescoped increment is dominated by two
values of the *single* maximal process started at `n0`. -/
theorem measure_all_windows_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) (A : ℕ) {n0 K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * (K : ℝ) * LocGroupWindow.stepEnv (N := N) p B) :
    (arrayMeasure N).real
      {U : Array N |
        ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + K ∧
          (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-((ε / 2) ^ 2) / (4 * ((K : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set D : Set (Array N) :=
    {U : Array N | ∃ k ≤ K,
      ε / 2 ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) k U|} with hD
  have hDbound : (arrayMeasure N).real D
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-((ε / 2) ^ 2) / (4 * ((K : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2))) :=
    measure_deviation_dQTW_le (N := N) hp0 hp1 I J hI hJ hid hB A hK
      (ε := ε / 2) (by linarith) (by
        have hhalf : ε / 2 ≤ ε := by linarith
        exact le_trans hhalf hside)
  -- the null set on which the chaining fails, restricted to our `n0` and `K`
  have hae := WA_sub_le_psum_abs (N := N) (m := m) hp0 hp1 I J hI hJ hid B A
  have hspec : ∀ᵐ U ∂(arrayMeasure N), ∀ (s t : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ
        ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U| :=
    hae.mono (fun U hU s t hn0s hst htK hwin => hU n0 s t K hn0s hst (by omega) hwin)
  set N₀ : Set (Array N) :=
    {U : Array N | ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + K ∧
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) ∧
      |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U|
        < WA p m U t I J hI hJ - WA p m U s I J hI hJ} with hN₀
  have hN₀sub : N₀ ⊆ {U : Array N | ¬ (∀ (s t : ℕ), n0 ≤ s → s ≤ t → t ≤ n0 + K →
      (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) →
      WA p m U t I J hI hJ - WA p m U s I J hI hJ
        ≤ |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U|
          + |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U|)} := by
    rintro U ⟨s, t, hn0s, hst, htK, hwin, hfail⟩ hp
    exact absurd (hp s t hn0s hst htK hwin) (not_le.mpr hfail)
  have hN₀z : (arrayMeasure N) N₀ = 0 :=
    measure_mono_null hN₀sub ((MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hspec)
  have hN₀r : (arrayMeasure N).real N₀ = 0 := by
    rw [measureReal_def, hN₀z]; simp
  have hsub : {U : Array N |
        ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + K ∧
          (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
      ⊆ D ∪ N₀ := by
    rintro U ⟨s, t, hn0, hst, htK, hgood, hbad⟩
    by_cases hmem : U ∈ D
    · exact Or.inl hmem
    · refine Or.inr ?_
      have hlt : ∀ k, k ≤ K →
          |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) k U| < ε / 2 := by
        intro k hk
        exact not_le.mp (fun hle => hmem ⟨k, hk, hle⟩)
      have h1 : |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (t - n0) U| < ε / 2 :=
        hlt _ (by omega)
      have h2 : |LocMart.psum (fun j => dQTW p m (n0 + j) I J hI hJ B A) (s - n0) U| < ε / 2 :=
        hlt _ (by omega)
      exact ⟨s, t, hn0, hst, htK, hgood, by linarith⟩
  have hmain : (arrayMeasure N).real {U : Array N |
        ∃ s t : ℕ, n0 ≤ s ∧ s ≤ t ∧ t ≤ n0 + K ∧
          (∀ k, s ≤ k → k < t → winTrunc p m k I J hI B A U) ∧
          ε < WA p m U t I J hI hJ - WA p m U s I J hI hJ}
      ≤ (arrayMeasure N).real (D ∪ N₀) := measureReal_mono hsub (measure_ne_top _ _)
  have h2 : (arrayMeasure N).real (D ∪ N₀)
      ≤ (arrayMeasure N).real D + (arrayMeasure N).real N₀ :=
    MeasureTheory.measureReal_union_le (μ := arrayMeasure N) D N₀
  have h3 : (arrayMeasure N).real D + (arrayMeasure N).real N₀
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-((ε / 2) ^ 2) / (4 * ((K : ℝ) * (2 * LocGroupWindow.stepEnv (N := N) p B) ^ 2))) := by
    linarith [hDbound, hN₀r]
  linarith [hmain, h2, h3]

end LocGroupSimul
