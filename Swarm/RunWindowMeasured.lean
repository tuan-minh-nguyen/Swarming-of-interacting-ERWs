/-
# The record-window run event, measured with no clock-cutoff hypothesis

## The gap this file closes

`AstarPos.arrayMeasure_runWindow_compl_le` (`Swarm/AstarPosition.lean`) is the measured
form of the *finite run event* on the record window that the windowed movement carrier needs
(`AstarPos.moveCarrierWin_of_carrier_hybrid`, `AstarPos.carrierMoveWin_of_univBad`).  It carries
the explicit hypothesis

    hB : ∀ U ∈ recordCarrier p m r L, recTimeA p m U r ≤ B,

i.e. a *deterministic cutoff of the random record clock*, and it deliberately takes no union over
clock values.  Nothing in the public tree supplies `hB`, and a naive union over the (random) clock
is invalid: `¬ RunsOK b K` is *monotone increasing* in the level `b`, so the window event is an
event at the random level `τ_r + T·L + 3`, and the level must be paid for.

This file removes `hB` by *measuring* the clock, with the already-proved unconditional
record-clock tail `RecordClockTail.recTimeA_tail`:

    P(τ_r > B) ≤ 2N exp(−((Bμ − Nr)/N)²/(16B)),        μ = (2p−1)(N − 2m),

and splitting the run-window failure at the *deterministic* level `B + T·L + 3`:

    {¬ runWindow} ⊆ {τ_r > B} ∪ {¬ RunsOK (B+T·L+3) K for some walker},

so that no union over clock values is taken and no event is assumed.  Note what is *not* used
here: the failure event is never assumed absent (its measure is bounded, not supposed small),
`ambGoodAll` is never assumed, and no invariant law, optional stopping or fibre summation appears.
The price is one clock-tail term; the run-window event is now measured with **no hypothesis on the
clock at all**, only an explicit cutoff `B`.

## Scope, exactly

* `arrayMeasure_runWindow_compl_le_clock` — every `B ≥ 1` with `N r < B μ` (the tail's own
  regularity region), `2m < N`, `2 ≤ m`, `K ≥ 1`.
* `arrayMeasure_runWindow_compl_le_auto` — the cutoff chosen automatically,
  `B = ⌈2Nr/μ⌉₊ + 1` (a function of `N`, `p`, `m`, `r` only, fixed before the event is measured),
  giving the closed form

      P(¬ runWindow) ≤ 2N exp(−rμ/(64N)) + N·(B + T·L + 3)·(1−q)^K,   q = (1−p)^(m−1).

* `exists_measureReal_not_moveCarrierWin_le` — the composition with the windowed movement
  carrier: on `recordCarrier ∩ univBadᶜ ∩ ambGoodAll`, failure of `MoveCarrierWin` is bounded by
  exactly the run-window term above.  `univBad` and `ambGoodAll` occur only as *conditions inside
  the set whose measure is bounded*, never as an assumption on their probability.

## What is not claimed, and why

`2m < N` is essential to this route, not an oversight.  `RecordClockTail.recTimeA_tail` is derived
from the deterministic excitation-occupation bound `ExcOcc.window_excOcc_sum`

    (N − 2m)·W ≤ Σ_i (excited steps of i in the window),

whose drift constant is `μ = (2p−1)(N − 2m)`.  For `N ≤ 2m` that inequality reads `0 ≤ Σ`, and its
regularity hypothesis `N r < K μ` is *unsatisfiable* (`recTimeA_tail_regime_empty` below).  The
`N ≤ 2m` regime — including the `N = m = 2` Berger–Procaccia case — therefore needs a genuinely
different excitation argument (positive excitation density at `N ≤ 2m`), which is not claimed
here.  `excitation_bound_trivial` records that the deterministic inequality carries no
information there.

No proof holes, no kernel bypass, no new axiom; closures are checked in
`RunWindowMeasuredAudit.lean` (source order) and are within
`{propext, Classical.choice, Quot.sound}`.
-/
import Swarm.AstarPosition
import Swarm.RecordClockTail

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmRecordMeas SwarmRecordMeas.Actual SwarmLogRatio
open Finset

namespace RunWindow

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 0. Bookkeeping -/

/-- `N` is positive, from the nonemptiness of `Fin N`. -/
theorem N_pos : 0 < N := by
  obtain ⟨k⟩ := ‹Nonempty (Fin N)›
  exact Nat.lt_of_le_of_lt (Nat.zero_le (k : ℕ)) k.isLt

/-- The drift constant `μ = (2p-1)(N-2m)` of `RecordClockTail.recTimeA_tail`. -/
noncomputable def runMu (N : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  (2 * p - 1) * ((N : ℝ) - 2 * m)

theorem runMu_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) {m : ℕ} (hmN : 2 * m < N) :
    0 < runMu N p m := by
  have hp : (0 : ℝ) < 2 * p - 1 := by linarith
  have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  unfold runMu
  exact mul_pos hp (by linarith)

/-- The drift constant is at most `N`: `μ = (2p-1)(N-2m) ≤ N`. -/
theorem runMu_le_Nat {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hmN : 2 * m < N) :
    runMu N p m ≤ (N : ℝ) := by
  have hp1' : 2 * p - 1 < 1 := by linarith
  have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  have hdiff : (0 : ℝ) < (N : ℝ) - 2 * m := by linarith
  unfold runMu
  calc (2 * p - 1) * ((N : ℝ) - 2 * m) ≤ 1 * ((N : ℝ) - 2 * m) :=
        mul_le_mul_of_nonneg_right hp1'.le hdiff.le
    _ ≤ (N : ℝ) := by linarith

/-- The scale condition `μ ≤ N r` of the automatic cutoff is automatic for every `r ≥ 1`. -/
theorem runMu_le_mul {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hmN : 2 * m < N)
    {r : ℕ} (hr : 1 ≤ r) : runMu N p m ≤ (N : ℝ) * (r : ℝ) := by
  have h1 := runMu_le_Nat (N := N) hp0 hp1 hmN
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith

/-! ## 1. The run event on the record window -/

/-- **The finite run event on the record window.**  Every walker's mark row has no run of `K`
consecutive unmarked sites below any level of the record window `[τ_r, τ_r + T·L]`. -/
def runWindow (p : ℝ) (m r T L K : ℕ) (U : Array N) : Prop :=
  ∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
    ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) K

/-- `RunsOK` is monotone in the level bound: a longer run-free prefix is a stronger event. -/
theorem runsOK_mono {ω : ℕ → Bool} {b b' K : ℕ} (hbb : b ≤ b') (h : SwarmRun.RunsOK ω b' K) :
    SwarmRun.RunsOK ω b K :=
  fun y hy => h y (le_trans hy hbb)

/-- **Failure on the window forces failure at the right end of the window.**  If the clock is at
most `B`, some window level `n + 3` is at most `B + T·L + 3`, and `RunsOK` monotonicity turns the
failure at that level into the failure at the *deterministic* level `B + T·L + 3`.  This is the
step that replaces a union over clock values by a single measured level. -/
theorem runWindow_compl_subset {p : ℝ} {m r T L K B : ℕ} {U : Array N}
    (hle : recTimeA p m U r ≤ B) (hbad : ¬ runWindow (N := N) p m r T L K U) :
    ∃ i : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U i) (B + T * L + 3) K := by
  rw [runWindow] at hbad
  push Not at hbad
  obtain ⟨n, hn, i, hi⟩ := hbad
  refine ⟨i, fun hrun => hi (runsOK_mono ?_ hrun)⟩
  have h2 : n < recTimeA p m U r + T * L := (Finset.mem_Ico.mp hn).2
  omega

/-- The two-alternative inclusion behind the measured bound: either the clock is late, or some
walker's run event fails at the deterministic level `B + T·L + 3`. -/
theorem runWindow_compl_subset_union {p : ℝ} {m r T L K B : ℕ} :
    {U : Array N | ¬ runWindow (N := N) p m r T L K U}
      ⊆ {U : Array N | B < recTimeA p m U r} ∪
        {U : Array N |
          ∃ i : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U i) (B + T * L + 3) K} := by
  intro U hU
  by_cases h : B < recTimeA p m U r
  · exact Or.inl h
  · exact Or.inr (runWindow_compl_subset (not_lt.mp h) hU)

/-! ## 2. The run-window measured, with the clock cutoff still explicit -/

/-- **The record-window run event measured with no clock-cutoff hypothesis, at an explicit
cutoff `B`.**  For `2m < N`, `2 ≤ m`, `K ≥ 1` and any `B ≥ 1` with `N r < B μ`, the probability
that the run event fails on the record window is at most the record-clock tail at `B` plus the
finite-carrier bound at level `B + T·L + 3`.

Both terms are proved, measured statements (`RecordClockTail.recTimeA_tail`,
`SwarmCarrier.arrayMeasure_carrier_compl_le`); the failure event itself is never assumed absent
and no union over clock values is taken. -/
theorem arrayMeasure_runWindow_compl_le_clock {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (hm : 2 ≤ m) (r T L K B : ℕ) (hK : 1 ≤ K) (hmN : 2 * m < N) (hB1 : 1 ≤ B)
    (hreg : (N : ℝ) * (r : ℝ) < (B : ℝ) * runMu N p m) :
    (arrayMeasure N).real {U : Array N | ¬ runWindow (N := N) p m r T L K U}
      ≤ 2 * (N : ℝ) * Real.exp
          (-((((B : ℝ) * runMu N p m - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2)
            / (16 * (B : ℝ)))
        + (N : ℝ) * (((B + T * L + 3 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
  have hsub := runWindow_compl_subset_union (N := N) (p := p) (m := m) (r := r) (T := T)
    (L := L) (K := K) (B := B)
  have hq : 0 ≤ (1 : ℝ) - (1 - p) ^ (m - 1) := by
    have h1 : (0 : ℝ) ≤ 1 - p := by linarith
    have h2 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
    linarith
  have hRHSnn : 0 ≤ (N : ℝ) * (((B + T * L + 3 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_nonneg hq K))
  calc (arrayMeasure N).real {U : Array N | ¬ runWindow (N := N) p m r T L K U}
      ≤ (arrayMeasure N).real ({U : Array N | B < recTimeA p m U r} ∪
          {U : Array N |
            ∃ i : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U i) (B + T * L + 3) K}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real {U : Array N | B < recTimeA p m U r}
          + (arrayMeasure N).real {U : Array N |
              ∃ i : Fin N, ¬ SwarmRun.RunsOK (siteMarks p m U i) (B + T * L + 3) K} :=
        measureReal_union_le _ _
    _ ≤ 2 * (N : ℝ) * Real.exp
          (-((((B : ℝ) * runMu N p m - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2)
            / (16 * (B : ℝ)))
        + (N : ℝ) * (((B + T * L + 3 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ K) := by
        refine add_le_add ?_ ?_
        · exact RecordClockTail.recTimeA_tail (N := N) hp0 hp1 (m := m) (r := r) (K := B)
            hmN hB1 hreg
        · exact ENNReal.toReal_le_of_le_ofReal hRHSnn
            (SwarmCarrier.arrayMeasure_carrier_compl_le (N := N) hp0 hp1 hm
              (B + T * L + 3) K hK)

/-! ## 3. The cutoff chosen automatically -/

/-- The automatic clock cutoff `B = ⌈2Nr/μ⌉₊ + 1`, a deterministic function of `N`, `p`, `m`, `r`
fixed before the run event is measured.  `⌈2Nr/μ⌉` puts the clock tail at its ballistic scale
(`ε = Bμ − Nr ≥ Nr`), the `+1` makes it a valid level. -/
noncomputable def clockCut (N : ℕ) (p : ℝ) (m r : ℕ) : ℕ :=
  ⌈2 * (N : ℝ) * (r : ℝ) / runMu N p m⌉₊ + 1

theorem one_le_clockCut (N : ℕ) (p : ℝ) (m r : ℕ) : 1 ≤ clockCut N p m r :=
  Nat.succ_le_succ (Nat.zero_le _)

theorem le_clockCut (N : ℕ) (p : ℝ) (m r : ℕ) :
    2 * (N : ℝ) * (r : ℝ) / runMu N p m ≤ ((clockCut N p m r : ℕ) : ℝ) := by
  have h1 : 2 * (N : ℝ) * (r : ℝ) / runMu N p m
      ≤ ((⌈2 * (N : ℝ) * (r : ℝ) / runMu N p m⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈2 * (N : ℝ) * (r : ℝ) / runMu N p m⌉₊ : ℕ) : ℝ)
      ≤ ((clockCut N p m r : ℕ) : ℝ) := by
    rw [clockCut]
    push_cast
    linarith
  linarith

/-- The automatic cutoff puts the clock tail's error at least one `N r` away from zero:
`2 N r ≤ B μ`, hence `ε = B μ − N r ≥ N r`. -/
theorem two_mul_le_clockCut_mul {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m r : ℕ) (hmN : 2 * m < N) :
    2 * (N : ℝ) * (r : ℝ) ≤ ((clockCut N p m r : ℕ) : ℝ) * runMu N p m := by
  have hμ : 0 < runMu N p m := runMu_pos hp0 hmN
  have h := le_clockCut N p m r
  rw [div_le_iff₀ hμ] at h
  linarith

/-- The automatic cutoff lies in the clock tail's regularity region. -/
theorem clockCut_reg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m r : ℕ) (hmN : 2 * m < N)
    (hr : 1 ≤ r) :
    (N : ℝ) * (r : ℝ) < (clockCut N p m r : ℝ) * runMu N p m := by
  have hNr : 0 < (N : ℝ) * (r : ℝ) := by
    have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos (N := N)
    have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    positivity
  have h1 := two_mul_le_clockCut_mul (N := N) hp0 m r hmN
  linarith

/-- The automatic cutoff is at most `2Nr/μ + 2`. -/
theorem clockCut_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m r : ℕ) (hmN : 2 * m < N) :
    ((clockCut N p m r : ℕ) : ℝ) ≤ 2 * (N : ℝ) * (r : ℝ) / runMu N p m + 2 := by
  have hx0 : 0 ≤ 2 * (N : ℝ) * (r : ℝ) / runMu N p m := by
    have hμ : 0 < runMu N p m := runMu_pos hp0 hmN
    positivity
  have h1 : ((⌈2 * (N : ℝ) * (r : ℝ) / runMu N p m⌉₊ : ℕ) : ℝ)
      < 2 * (N : ℝ) * (r : ℝ) / runMu N p m + 1 := Nat.ceil_lt_add_one hx0
  rw [clockCut]
  push_cast
  linarith

/-- The prefactor of the run-window term in the closed form `2Nr/μ + T·L + 5`. -/
theorem clockCut_window_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m r T L : ℕ) (hmN : 2 * m < N) :
    ((clockCut N p m r + T * L + 3 : ℕ) : ℝ)
      ≤ 2 * (N : ℝ) * (r : ℝ) / runMu N p m + (T * L + 5) := by
  have h := clockCut_le (N := N) hp0 m r hmN
  have hcc : ((clockCut N p m r + T * L + 3 : ℕ) : ℝ)
      = ((clockCut N p m r : ℕ) : ℝ) + ((T : ℝ) * (L : ℝ) + 3) := by
    push_cast
    ring
  rw [hcc]
  linarith

/-- **Scalar core of the automatic cutoff.**  With `2 N r ≤ B μ ≤ 4 N r`,

    rμ/(64N) ≤ ((Bμ − Nr)/N)²/(16B),

i.e. the clock tail at `B` decays at least like `exp(−rμ/(64N))`. -/
theorem exp_core {N' r B μ : ℝ} (hN : 0 < N') (hr : 0 < r) (hB : 0 < B) (hμ : 0 < μ)
    (h2 : 2 * N' * r ≤ B * μ) (h4 : B * μ ≤ 4 * (N' * r)) :
    r * μ / (64 * N') ≤ ((B * μ - N' * r) / N') ^ 2 / (16 * B) := by
  have hNr : 0 < N' * r := mul_pos hN hr
  have hA : r * μ / (64 * N') ≤ r ^ 2 / (16 * B) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h4]
  have hB1 : r ^ 2 / (16 * B) = (N' * r) ^ 2 / (16 * N' ^ 2 * B) := by
    field_simp
  have hC : (N' * r) ^ 2 / (16 * N' ^ 2 * B) ≤ (B * μ - N' * r) ^ 2 / (16 * N' ^ 2 * B) := by
    have hε : N' * r ≤ B * μ - N' * r := by linarith
    have hsq := pow_le_pow_left₀ hNr.le hε 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hD : (B * μ - N' * r) ^ 2 / (16 * N' ^ 2 * B)
      = ((B * μ - N' * r) / N') ^ 2 / (16 * B) := by
    rw [div_pow]
    field_simp
  linarith [hA, hB1, hC, hD]

/-- **The run-window complement measured with the automatic cutoff.**  For `2m < N`, `2 ≤ m`,
`K ≥ 1` and `r ≥ 1`,

    P(¬ runWindow) ≤ 2N exp(−rμ/(64N)) + N·(⌈2Nr/μ⌉₊ + T·L + 4)·(1−q)^K,

with `q = (1−p)^(m−1)`.  No clock cutoff, no union over clock values, no probability assumed. -/
theorem arrayMeasure_runWindow_compl_le_auto {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (hm : 2 ≤ m) (r T L K : ℕ) (hK : 1 ≤ K) (hmN : 2 * m < N) (hr : 1 ≤ r) :
    (arrayMeasure N).real {U : Array N | ¬ runWindow (N := N) p m r T L K U}
      ≤ 2 * (N : ℝ) * Real.exp (-((r : ℝ) * runMu N p m / (64 * (N : ℝ))))
        + (N : ℝ) * (((clockCut N p m r + T * L + 3 : ℕ) : ℝ)
            * (1 - (1 - p) ^ (m - 1)) ^ K) := by
  have hμ : 0 < runMu N p m := runMu_pos hp0 hmN
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos (N := N)
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNr : 0 < (N : ℝ) * (r : ℝ) := by positivity
  have hscale : runMu N p m ≤ (N : ℝ) * (r : ℝ) := runMu_le_mul hp0 hp1 hmN hr
  set B : ℝ := ((clockCut N p m r : ℕ) : ℝ) with hBdef
  have hB1 : 1 ≤ clockCut N p m r := one_le_clockCut N p m r
  have hBpos : 0 < B := by rw [hBdef]; exact_mod_cast hB1
  have hreg : (N : ℝ) * (r : ℝ) < B * runMu N p m := clockCut_reg hp0 m r hmN hr
  -- `B μ ≤ 4 N r`
  have hBmul : B * runMu N p m ≤ 4 * ((N : ℝ) * (r : ℝ)) := by
    have hle : B ≤ 2 * (N : ℝ) * (r : ℝ) / runMu N p m + 2 := clockCut_le hp0 m r hmN
    have h1 : (2 * (N : ℝ) * (r : ℝ) / runMu N p m + 2) * runMu N p m
        = 2 * ((N : ℝ) * (r : ℝ)) + 2 * runMu N p m := by
      field_simp
    have h2 : 2 * ((N : ℝ) * (r : ℝ)) + 2 * runMu N p m ≤ 4 * ((N : ℝ) * (r : ℝ)) := by
      linarith
    calc B * runMu N p m
        ≤ (2 * (N : ℝ) * (r : ℝ) / runMu N p m + 2) * runMu N p m :=
          mul_le_mul_of_nonneg_right hle hμ.le
      _ = 2 * ((N : ℝ) * (r : ℝ)) + 2 * runMu N p m := h1
      _ ≤ 4 * ((N : ℝ) * (r : ℝ)) := h2
  have hexp : (r : ℝ) * runMu N p m / (64 * (N : ℝ))
      ≤ ((B * runMu N p m - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2 / (16 * B) :=
    exp_core hN hr' hBpos hμ
      (two_mul_le_clockCut_mul (N := N) hp0 m r hmN) hBmul
  rw [hBdef] at hexp
  refine le_trans (arrayMeasure_runWindow_compl_le_clock (p := p) hp0 hp1 m hm r T L K
    (clockCut N p m r) hK hmN hB1 hreg) ?_
  refine add_le_add ?_ le_rfl
  have hmono : Real.exp
        (-((((B * runMu N p m - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2) / (16 * B)))
      ≤ Real.exp (-((r : ℝ) * runMu N p m / (64 * (N : ℝ)))) :=
    Real.exp_le_exp.2 (neg_le_neg hexp)
  have hscaled : 2 * (N : ℝ) * Real.exp
        (-((((B * runMu N p m - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2) / (16 * B)))
      ≤ 2 * (N : ℝ) * Real.exp (-((r : ℝ) * runMu N p m / (64 * (N : ℝ)))) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  simpa [hBdef, neg_div] using hscaled

/-! ## 4. Composition with the windowed movement carrier -/

/-- **The windowed movement carrier off the run-window term.**  For `2 ≤ m` and `2m < N`
there is a scale `L₀` such that for every `L ≥ L₀`, every block `(T, Cerr, r)` with
`(T+3)·L ≤ r`,

    P{ U ∈ recordCarrier ∩ univBadᶜ ∩ ambGoodAll  and  ¬ MoveCarrierWin at Astar r T L }
      ≤ 2N exp(−rμ/(64N)) + N·(⌈2Nr/μ⌉₊ + T·L + 4)·(1−q)^(Kc p L) .

`univBad` and `ambGoodAll` are *conditions on the arrays* in the set being measured; their
probabilities are never assumed.  The movement carrier itself is
`AstarPos.carrierMoveWin_of_univBad`. -/
theorem exists_measureReal_not_moveCarrierWin_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (hm : 2 ≤ m) (hmN : 2 * m < N) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (T : ℕ) (Cerr : ℝ) (r : ℕ), (T + 3) * L ≤ r →
      (arrayMeasure N).real
          {U : Array N |
            U ∈ RecClockLG.recordCarrier (N := N) p m r L ∧
            U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L ∧
            U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L ∧
            ¬ CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U}
        ≤ 2 * (N : ℝ) * Real.exp (-((r : ℝ) * runMu N p m / (64 * (N : ℝ))))
          + (N : ℝ) * (((clockCut N p m r + T * L + 3 : ℕ) : ℝ)
              * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)) := by
  have hN : 2 ≤ N := by omega
  obtain ⟨Lc, hLc⟩ := AstarPos.carrierMoveWin_of_univBad (p := p) hp0 hp1 (m := m) hm N hN
  obtain ⟨Lk, hLk⟩ := AstarPos.exists_Kc (p := p) hp0 hp1
  refine ⟨max Lc (max Lk 1), fun L hL T Cerr r hr => ?_⟩
  have hLc' : Lc ≤ L := le_trans (le_max_left _ _) hL
  have hLk' : Lk ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
  have hr1 : 1 ≤ r := by
    have h1 : 1 * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
    have h2 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    omega
  have hsub : {U : Array N |
        U ∈ RecClockLG.recordCarrier (N := N) p m r L ∧
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L ∧
        U ∈ Swarming.Enl.ambGoodAll (N := N) p m (r : ℤ) T L ∧
        ¬ CarrierWin.MoveCarrierWin (N := N) p m r T L (RecClockLG.Astar r T L) U}
      ⊆ {U : Array N | ¬ runWindow (N := N) p m r T L (AstarPos.Kc p L) U} := by
    rintro U ⟨hcarr, huniv, hamb, hnot⟩ hrun
    exact hnot (hLc L hLc' T Cerr r hr U hcarr huniv hamb hrun)
  exact le_trans (measureReal_mono hsub (measure_ne_top _ _))
    (arrayMeasure_runWindow_compl_le_auto (p := p) hp0 hp1 m hm r T L (AstarPos.Kc p L)
      hK hmN hr1)

/-! ## 5. The `N ≤ 2m` obstruction, exactly -/

/-- For `N ≤ 2m` the drift constant of the clock tail is non-positive. -/
theorem runMu_nonpos_of_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) {m : ℕ} (h : N ≤ 2 * m) :
    runMu N p m ≤ 0 := by
  have hp : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have h2 : (N : ℝ) - 2 * m ≤ 0 := by
    have hNm : (N : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h
    linarith
  unfold runMu
  exact mul_nonpos_of_nonneg_of_nonpos hp h2

/-- **The obstruction.**  The clock tail's regularity hypothesis `N r < K μ` — the only route
this file has to the record clock — is *unsatisfiable* for `N ≤ 2m` and `r ≥ 1`.  So the measured
run-window bound above provably cannot be instantiated in the `N ≤ 2m` regime, whatever the value
of `K`: a genuinely different excitation argument is required there. -/
theorem recTimeA_tail_regime_empty {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m r K : ℕ)
    (h : N ≤ 2 * m) (hr : 1 ≤ r) :
    ¬ ((N : ℝ) * (r : ℝ) < (K : ℝ) * runMu N p m) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos (N := N)
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNr : 0 < (N : ℝ) * (r : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have h1 : (K : ℝ) * runMu N p m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK (runMu_nonpos_of_le hp0 h)
  linarith

/-- The deterministic excitation-occupation bound is vacuous for `N ≤ 2m`: the inequality reads
`0 ≤ Σ`, hence is implied by `0 ≤ Σ` and carries no positive drift constant.  (Compare
`ExcOcc.window_excOcc_sum`, from which the clock tail is derived.) -/
theorem excitation_bound_trivial {m : ℕ} (h : N ≤ 2 * m) (W S : ℕ) :
    N * W ≤ 2 * m * W + S := by
  have h1 : N * W ≤ 2 * m * W := Nat.mul_le_mul_right W h
  omega

/-- The left side of the excitation-occupation bound vanishes for `N ≤ 2m`. -/
theorem exc_deficit_zero {m : ℕ} (h : N ≤ 2 * m) (W : ℕ) : (N - 2 * m) * W = 0 := by
  rw [Nat.sub_eq_zero_of_le h, Nat.zero_mul]

end RunWindow
