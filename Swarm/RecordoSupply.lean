/-
# (recordo) supply: the record-time clause from the proved ballistic lower bound

The paper (`main_1d_revised.tex`, §"Oscillation of the walks") defines

  `τ r = inf {n : max_i X_n^i = r}`,  `d r = r - min_i X_{τ r}^i`,

and derives

  (recordo)   `τ r ≤ 2 r / κ(m,p)`  for all sufficiently large `r`,   `d r / r → 0`  a.s.

from the ballistic lower bound `(lower)` and the diameter estimate `(diam)`.  In the current
Lean development the first clause is *not* derived: `RecordDefect.defect_div_tendsto_zero`
takes `τ r ≤ C r` as a hypothesis with the comment "the consequence of the ballistic lower
bound", and the tightness chain (`areas/tightness`, `hterm`) carries the whole of (recordo) as
a premise.

This file removes the time clause from that premise list:

* `runMax_le` / `tau_ge`: every walker starts at `0` and moves by unit steps, so
  `τ r ≥ r` (`RecordDefect` uses `τ r ≥ r` but does not prove it);
* `tau_le_of_speed`: a **one-walker** lower speed bound `κ/2 * n ≤ X_n^i` eventually implies
  `τ r ≤ C r` with the explicit `C = max (N₀+1) (4/κ + 2)` — this is the paper's
  "since `τ r ≥ r`, using `(lower)` …";
* `defect_div_tendsto_zero_of_speed` composes it with the diameter estimate `(diam)` to give
  the second clause `d_r / r → 0` with the time clause discharged;
* `recordo_blocks` states (recordo) in the block form the tightness interface consumes:
  for every `r`, for all sufficiently large `L`, all three inequalities of the paper's
  display (block) hold, with explicit `T` and `C₀ = B + T + 1`;
* `recordo_actual` instantiates the speed input with the unconditional actual-array ballistic
  lower bound `SwarmActualFront.ballistic_actual`.

* `GoodBlock`, `hterm_of_blocks`: the paper's three block inequalities as a predicate, and the
  implication "blocks for all large `L` ⇒ the tightness interface's doubling form
  `∀ L ≥ 1, ∃ j, Good`";
* `runMax_step`, `exists_runMax_eq`, `recTime`, `isRecord_recTime`: the record times exist
  (`Nat.find` of the first hitting time satisfies `IsRecord`), so nothing here is vacuous;
* `speed_actual`, `tau_linear_actual`, `recordo_actual`, `recordTimes_actual`,
  `hterm_actual`, `hterm_actual_exists`: the same statements for the actual array
  `Swarming.Trajectory.trajectory` on `Swarming.Uniform.arrayMeasure`, with the speed input taken
  from the *unconditional* `SwarmActualFront.ballistic_actual`.

The only residual hypothesis anywhere in this file is the diameter estimate
`(diam)`: `spread X n / n → 0` almost surely, i.e. the spread of the `N` walkers at time `n` is
`o(n)`.  That estimate is not proved here and is not proved in the repository
(`areas/martingale/README.md`: "the uniform occupation inputs; … and `(diam)`" is listed as
open).  No probability space is hidden: the block statement is a pathwise statement about a
single trajectory, and the almost-sure quantifier only enters in `recordo_actual`.
-/
import Swarm.ActualRecordFiltration
import Swarm.RecordDefect
import Swarm.ActualFront
import Swarm.DensReduction
import Swarm.BadCarrier

open Filter Topology MeasureTheory
open scoped BigOperators

namespace RecordoSupply

open RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### Unit steps, the start at `0`, and `τ r ≥ r` -/

/-- A unit-step walker started at `0` is at most at `n` at time `n`. -/
theorem le_time (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) (i : ι) : ∀ n : ℕ, X i n ≤ (n : ℤ) := by
  intro n
  induction n with
  | zero => simp [h0 i]
  | succ n ih =>
      have h : X i (n + 1) - X i n ≤ 1 := by
        calc X i (n + 1) - X i n ≤ |X i (n + 1) - X i n| := le_abs_self _
          _ = 1 := hne i n
      push_cast
      linarith

/-- The running maximum at time `n` is at most `n`. -/
theorem runMax_le (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) (n : ℕ) : runMax X n ≤ (n : ℤ) := by
  refine Finset.sup'_le _ _ fun i _ => le_time X hne h0 i n

/-- **`τ r ≥ r`**: the paper's "since `τ_r ≥ r`". -/
theorem tau_ge {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    (r : ℕ) : r ≤ τ r := by
  have h2 : runMax X (τ r) = (r : ℤ) := (hτ r).2
  have h3 : runMax X (τ r) ≤ ((τ r : ℕ) : ℤ) := runMax_le X hne h0 (τ r)
  have h4 : (r : ℤ) ≤ ((τ r : ℕ) : ℤ) := by rw [← h2]; exact h3
  exact_mod_cast h4

/-- If the running maximum has reached `r` by time `n`, the record time of level `r` is at
most `n`. -/
theorem tau_le_of_runMax_ge {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {r n : ℕ} (h : (r : ℤ) ≤ runMax X n) : τ r ≤ n := by
  by_contra hlt
  rw [not_le] at hlt
  have h' : runMax X n < (r : ℤ) := (hτ r).1 n hlt
  linarith

/-! ### The time clause from a one-walker speed bound -/

/-- **`τ r` grows at most linearly, from a single walker's lower speed bound.**

This is the paper's step "since `τ_r ≥ r`, using `(lower)` and `(diam)`, we obtain
`τ_r ≤ 2r/κ(m,p)`": only the *lower* bound is used here, and only for one walker. -/
theorem tau_le_of_speed {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → (τ r : ℝ) ≤ C * (r : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hspd
  refine ⟨max ((N₀ : ℝ) + 1) (4 / κ + 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 4 / κ + 2 := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  intro r hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  set n : ℕ := max N₀ ⌈2 * (r : ℝ) / κ⌉₊ with hn
  have hκne : κ ≠ 0 := ne_of_gt hκ
  -- the speed bound applies at `n`
  have hnN : N₀ ≤ n := le_max_left _ _
  have hkey := hN₀ n hnN
  -- and `n` is past `2r/κ`
  have hle_ceil : (2 * (r : ℝ) / κ) ≤ ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hceil_le : ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    rw [hn]
    push_cast
    exact le_max_right _ _
  have hnr : (r : ℝ) ≤ (κ / 2) * (n : ℝ) := by
    have hle2 : 2 * (r : ℝ) ≤ (n : ℝ) * κ := by
      have h' := hle_ceil
      rw [div_le_iff₀ hκ] at h'
      have hmono : ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) * κ ≤ (n : ℝ) * κ :=
        mul_le_mul_of_nonneg_right hceil_le (le_of_lt hκ)
      linarith
    linarith
  -- hence the running maximum has reached `r` by time `n`
  have hXr : (r : ℝ) ≤ (X i n : ℝ) := le_trans hnr hkey
  have hXrZ : (r : ℤ) ≤ X i n := by exact_mod_cast hXr
  have hrun : (r : ℤ) ≤ runMax X n := le_trans hXrZ (le_runMax n i)
  have hτn : τ r ≤ n := tau_le_of_runMax_ge hτ hrun
  -- and `n ≤ C r`
  have hnr_le : (n : ℝ) ≤ max ((N₀ : ℝ) + 1) (4 / κ + 2) * (r : ℝ) := by
    have h1 : (n : ℝ) ≤ max (N₀ : ℝ) (2 * (r : ℝ) / κ + 1) := by
      have hc : ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) < 2 * (r : ℝ) / κ + 1 :=
        Nat.ceil_lt_add_one (le_of_lt (by positivity : (0 : ℝ) < 2 * (r : ℝ) / κ))
      have : (n : ℝ) ≤ max (N₀ : ℝ) (2 * (r : ℝ) / κ + 1) := by
        rw [hn]
        push_cast
        exact max_le_max le_rfl (le_of_lt hc)
      exact this
    have h2 : (N₀ : ℝ) ≤ ((N₀ : ℝ) + 1) * (r : ℝ) := by nlinarith
    have h3 : 2 * (r : ℝ) / κ + 1 ≤ (4 / κ + 2) * (r : ℝ) := by
      have h4 : 2 * (r : ℝ) / κ ≤ (4 / κ) * (r : ℝ) := by
        have h5 : (4 / κ) * (r : ℝ) = 4 * (r : ℝ) / κ := by ring
        rw [h5]
        gcongr
        linarith
      nlinarith [h4, hr1]
    calc (n : ℝ) ≤ max (N₀ : ℝ) (2 * (r : ℝ) / κ + 1) := h1
      _ ≤ max (((N₀ : ℝ) + 1) * (r : ℝ)) ((4 / κ + 2) * (r : ℝ)) := by
        refine max_le_max h2 h3
      _ = max ((N₀ : ℝ) + 1) (4 / κ + 2) * (r : ℝ) := by
        rw [max_mul_of_nonneg _ _ (le_of_lt hrR)]
  have : (τ r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hτn
  exact le_trans this hnr_le

end RecordoSupply

/-! ### (recordo): the block form used by the tightness interface -/

namespace RecordoSupply

open RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Unit steps bound a walker below as well: `-n ≤ X_n^i`. -/
theorem neg_time_le (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) (i : ι) : ∀ n : ℕ, -((n : ℤ)) ≤ X i n := by
  intro n
  induction n with
  | zero => simp [h0 i]
  | succ n ih =>
      have h : -1 ≤ X i (n + 1) - X i n := by
        have h1 := hne i n
        have h2 := neg_abs_le (X i (n + 1) - X i n)
        linarith
      push_cast
      linarith

/-- The paper's defect is at most `r + τ r`. -/
theorem defect_le_level_add_tau {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0) (r : ℕ) :
    defect X τ r ≤ (r : ℤ) + ((τ r : ℕ) : ℤ) := by
  have hmin : -(((τ r : ℕ)) : ℤ) ≤ runMin X (τ r) := by
    show -(((τ r : ℕ)) : ℤ) ≤ (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => X i (τ r))
    exact Finset.le_inf' Finset.univ_nonempty (fun i => X i (τ r))
      (fun i _ => neg_time_le X hne h0 i (τ r))
  rw [defect]
  linarith

/-- **The second clause of (recordo) with the time clause discharged**: `d_r / r → 0`
follows from the diameter estimate `(diam)` and `τ r ≤ C r`, and the latter is now derived from
the one-walker speed bound instead of being assumed. -/
theorem defect_div_tendsto_zero_of_speed {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hspread : Tendsto (fun n : ℕ => spread X n / n) atTop (𝓝 0)) :
    Tendsto (fun r : ℕ => (defect X τ r : ℝ) / r) atTop (𝓝 0) := by
  obtain ⟨C, hC, hτC⟩ := tau_le_of_speed hτ hne h0 hκ hspd
  exact RecordDefect.defect_div_tendsto_zero hτ (tau_ge hτ hne h0) hC hτC hspread

/-- **The paper's display (block) for every fixed level and all large `L`.**

Explicit `T` and `C₀ = B + T + 1` with: for every starting level `r`, for all sufficiently large
`L`, the record advance is at most `T L`, the defect at `r + B L` is at most `L/2`
(`2 d ≤ L`), and the defect stays at most `C₀ L` throughout the block.  This is (recordo) in the
shape the tightness interface consumes; the third inequality is
`RecordDefect.block_defect_bound`, the first is `tau_le_of_speed`, and the second is the
diameter estimate. -/
theorem recordo_blocks {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hdlim : Tendsto (fun n : ℕ => (defect X τ n : ℝ) / n) atTop (𝓝 0))
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ T C₀ : ℕ, 1 ≤ T ∧ C₀ = B + T + 1 ∧ ∀ r : ℕ, ∀ᶠ L : ℕ in atTop,
      (τ (r + B * L) - τ r ≤ T * L) ∧
      (2 * defect X τ (r + B * L) ≤ (L : ℤ)) ∧
      (∀ u : ℕ, r ≤ u → u ≤ r + B * L → defect X τ u ≤ (C₀ : ℤ) * (L : ℤ)) := by
  obtain ⟨C, hC, hτC⟩ := tau_le_of_speed hτ hne h0 hκ hspd
  have hτge : ∀ r : ℕ, r ≤ τ r := tau_ge hτ hne h0
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  refine ⟨⌈C * (B : ℝ)⌉₊ + 2, B + (⌈C * (B : ℝ)⌉₊ + 2) + 1, by omega, rfl, fun r => ?_⟩
  set T : ℕ := ⌈C * (B : ℝ)⌉₊ + 2 with hTdef
  set C₀ : ℕ := B + T + 1 with hC₀def
  have hCT : C * (B : ℝ) < (T : ℝ) := by
    have h1 : C * (B : ℝ) ≤ ((⌈C * (B : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈C * (B : ℝ)⌉₊ : ℕ) : ℝ) < (T : ℝ) := by
      rw [hTdef]; push_cast; linarith
    linarith
  -- (1) the time clause, in reals
  have ha : ∀ᶠ L : ℕ in atTop,
      (τ (r + B * L) : ℝ) - (τ r : ℝ) ≤ (T : ℝ) * (L : ℝ) := by
    have hgap : (0 : ℝ) < (T : ℝ) - C * (B : ℝ) := by linarith
    have hevL : ∀ᶠ L : ℕ in atTop,
        ⌈(C * (r : ℝ) - (r : ℝ)) / ((T : ℝ) - C * (B : ℝ))⌉₊ ≤ L :=
      eventually_ge_atTop _
    filter_upwards [hevL, eventually_ge_atTop 1] with L hL hL1
    have hBL1 : 1 ≤ B * L := le_trans hL1 (Nat.le_mul_of_pos_left L (by omega : 0 < B))
    have hidx : 1 ≤ r + B * L := le_trans hBL1 (Nat.le_add_left (B * L) r)
    have hτBL : (τ (r + B * L) : ℝ) ≤ C * ((r : ℝ) + (B : ℝ) * (L : ℝ)) := by
      have h := hτC (r + B * L) hidx
      calc (τ (r + B * L) : ℝ) ≤ C * ((r + B * L : ℕ) : ℝ) := h
        _ = C * ((r : ℝ) + (B : ℝ) * (L : ℝ)) := by push_cast; ring
    have hr1 : (r : ℝ) ≤ (τ r : ℝ) := by exact_mod_cast hτge r
    have hbig : C * (r : ℝ) - (r : ℝ) ≤ ((T : ℝ) - C * (B : ℝ)) * (L : ℝ) := by
      have hceil : ((⌈(C * (r : ℝ) - (r : ℝ)) / ((T : ℝ) - C * (B : ℝ))⌉₊ : ℕ) : ℝ)
          ≤ (L : ℝ) := by exact_mod_cast hL
      have := le_trans (Nat.le_ceil ((C * (r : ℝ) - (r : ℝ)) / ((T : ℝ) - C * (B : ℝ)))) hceil
      rw [div_le_iff₀ hgap] at this
      linarith
    nlinarith [hτBL, hr1, hbig]
  -- (1') the time clause, as a natural-number inequality
  have haN : ∀ᶠ L : ℕ in atTop, τ (r + B * L) - τ r ≤ T * L := by
    filter_upwards [ha] with L hL
    have hmono : τ r ≤ τ (r + B * L) := RecordDefect.tau_mono hτ (Nat.le_add_right r (B * L))
    have hZ : ((τ (r + B * L) : ℤ) - (τ r : ℤ)) ≤ ((T * L : ℕ) : ℤ) := by
      have h' : ((τ (r + B * L) : ℤ) : ℝ) - ((τ r : ℤ) : ℝ) ≤ ((T * L : ℕ) : ℝ) := by
        push_cast
        exact hL
      exact_mod_cast h'
    have hsub : ((τ (r + B * L) - τ r : ℕ) : ℤ) = (τ (r + B * L) : ℤ) - (τ r : ℤ) := by
      push_cast [hmono]; ring
    have hZ' : ((τ (r + B * L) - τ r : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
      rw [hsub]; exact hZ
    exact_mod_cast hZ'
  -- (2) the halving clause
  have hb : ∀ᶠ L : ℕ in atTop, 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
    have heps : ∀ᶠ s : ℕ in atTop,
        (defect X τ s : ℝ) ≤ (1 / (8 * (B : ℝ))) * (s : ℝ) := by
      have hε : (0 : ℝ) < 1 / (8 * (B : ℝ)) := by positivity
      obtain ⟨S, hS⟩ := Metric.tendsto_atTop.1 hdlim (1 / (8 * (B : ℝ))) hε
      filter_upwards [eventually_ge_atTop (max S 1)] with s hs
      have hsS : S ≤ s := le_trans (le_max_left _ _) hs
      have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
      have h := hS s hsS
      rw [Real.dist_eq, sub_zero] at h
      have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
      have hlt : (defect X τ s : ℝ) / (s : ℝ) < 1 / (8 * (B : ℝ)) := (abs_lt.1 h).2
      rw [div_lt_iff₀ hspos] at hlt
      exact le_of_lt hlt
    obtain ⟨S, hS⟩ := eventually_atTop.1 heps
    filter_upwards [eventually_ge_atTop (max S (r + 1))] with L hL
    have hLle : L ≤ r + B * L := by
      have h1 : L ≤ B * L := Nat.le_mul_of_pos_left L (by omega : 0 < B)
      omega
    have hLS : S ≤ r + B * L :=
      le_trans (le_trans (le_max_left _ _) hL) hLle
    have h := hS (r + B * L) hLS
    have hLr1 : r + 1 ≤ L := le_trans (le_max_right _ _) hL
    have hLr : (r : ℝ) ≤ (B : ℝ) * (L : ℝ) := by
      have h2 : (r : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hLr1
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hB1 hLnn
      nlinarith [hmul, h2]
    have hcast : ((r + B * L : ℕ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
    have hquarter : (defect X τ (r + B * L) : ℝ) ≤ (L : ℝ) / 4 := by
      rw [hcast] at h
      have h1 : (1 / (8 * (B : ℝ))) * ((r : ℝ) + (B : ℝ) * (L : ℝ))
          ≤ (1 / (8 * (B : ℝ))) * (2 * ((B : ℝ) * (L : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h2 : (1 / (8 * (B : ℝ))) * (2 * ((B : ℝ) * (L : ℝ))) = (L : ℝ) / 4 := by
        field_simp
        ring
      linarith
    have h4 : ((defect X τ (r + B * L) : ℤ) : ℝ) * 4 ≤ ((L : ℤ) : ℝ) := by
      push_cast
      linarith
    have h4Z : defect X τ (r + B * L) * 4 ≤ (L : ℤ) := by exact_mod_cast h4
    linarith
  -- (3) the defect at the starting level is eventually below `L`
  have hc : ∀ᶠ L : ℕ in atTop, defect X τ r ≤ (L : ℤ) := by
    have hbound := defect_le_level_add_tau hτ hne h0 r
    filter_upwards [eventually_ge_atTop (r + τ r)] with L hL
    have hcast : ((r + τ r : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    push_cast at hcast
    linarith
  filter_upwards [haN, hb, hc] with L h1 h2 h3
  exact ⟨h1, h2, fun u hru huBL => RecordDefect.block_defect_bound hτ hne h3 h1 u hru huBL⟩

end RecordoSupply

/-! ### The actual array: (recordo) with the proved ballistic constant -/

namespace RecordoSupply

open RecordDefect
open Filter Topology MeasureTheory

/-- `liminf ≥ κ` gives the eventual one-sided bound at any strictly smaller level. -/
lemma eventually_lt_of_le_liminf {u : ℕ → ℝ} {C κ a : ℝ} (hC : ∀ n : ℕ, |u n| ≤ C)
    (h : κ ≤ liminf u atTop) (ha : a < κ) : ∀ᶠ n : ℕ in atTop, a < u n :=
  (le_liminf_iff (SwarmDens.isCoboundedUnder_ge_of_abs_le hC)
    (SwarmDens.isBoundedUnder_ge_of_abs_le hC)).mp h a ha

/-- Unit steps of the actual trajectory. -/
theorem actX_step {N : ℕ} (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) (i : Fin N) (n : ℕ) :
    |actX p m U i (n + 1) - actX p m U i n| = 1 := by
  rcases Swarming.Trajectory.pos_succ_eq_add_one_or_sub_one p m U i n with h | h
  · have h1 : actX p m U i (n + 1) - actX p m U i n = 1 := by
      simp only [actX]; omega
    rw [h1]; norm_num
  · have h1 : actX p m U i (n + 1) - actX p m U i n = -1 := by
      simp only [actX]; omega
    rw [h1]; norm_num

/-- **The speed input of `tau_le_of_speed`, for the actual array, unconditionally**: the
paper's `(lower)` in the eventual one-walker form. -/
theorem speed_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∀ i : Fin N, ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ) := by
  obtain ⟨κ, hκ, h⟩ := SwarmActualFront.ballistic_actual hp0 hp1 hm
  refine ⟨κ, hκ, fun N hN => ?_⟩
  filter_upwards [h N hN] with U hU
  intro i
  have hbound : ∀ n : ℕ, |Swarm.pos (SwarmActualFront.arrX (N := N) p m) n i U / (n : ℝ)| ≤ 1 :=
    fun n => SwarmDens.abs_pos_div_le_one (SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m) n U i
  have hev := eventually_lt_of_le_liminf hbound (hU i) (by linarith : κ / 2 < κ)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  rw [lt_div_iff₀ hn0] at hn
  have hpos : Swarm.pos (SwarmActualFront.arrX (N := N) p m) n i U = (actX p m U i n : ℝ) := rfl
  rw [hpos] at hn
  linarith

/-- **The paper's `τ_r ≤ C r` for the actual array**, with the ballistic constant: this is the
time clause of (recordo), formerly an assumption. -/
theorem tau_linear_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∀ (τ : ℕ → ℕ), IsRecord (actX p m U) τ →
        ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → (τ r : ℝ) ≤ C * (r : ℝ) := by
  obtain ⟨κ, hκ, h⟩ := speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, ?_⟩
  intro N _inst hN
  filter_upwards [h N hN] with U hU
  intro τ hτ
  exact tau_le_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ
    (hU (Classical.arbitrary (Fin N)))

/-- **The paper's (recordo) for the actual array**: the time clause is proved, and the defect
limit `d_r / r → 0` follows once the diameter estimate `(diam)` (`spread → 0`) is supplied. -/
theorem recordo_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∀ (τ : ℕ → ℕ), IsRecord (actX p m U) τ →
        (Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0)) →
          Tendsto (fun r : ℕ => (defect (actX p m U) τ r : ℝ) / (r : ℝ)) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, h⟩ := speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, ?_⟩
  intro N _inst hN
  filter_upwards [h N hN] with U hU
  intro τ hτ hspread
  exact defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ
    (hU (Classical.arbitrary (Fin N))) hspread

end RecordoSupply

/-! ## Axiom audit -/


/-! ### The `hterm` field shape: (recordo) in doubling form -/

namespace RecordoSupply

open RecordDefect
open Filter Topology MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The paper's three block inequalities for a record-time sequence `τ` and a defect `d`
(`2 d ≤ L` is the divisibility-free form of `d ≤ L/2`). -/
def GoodBlock (d : ℕ → ℤ) (τ : ℕ → ℕ) (T C₀ B : ℕ) (r L : ℕ) : Prop :=
  τ (r + B * L) - τ r ≤ T * L ∧
  2 * d (r + B * L) ≤ (L : ℤ) ∧
  (∀ u : ℕ, r ≤ u → u ≤ r + B * L → d u ≤ (C₀ : ℤ) * (L : ℤ))

/-- **Block goodness for all large `L` implies the doubling form** used by the tightness
interface's field `hterm`: for every level `L ≥ 1` some dyadic multiple `2^j L` is good. -/
theorem hterm_of_blocks {d : ℕ → ℤ} {τ : ℕ → ℕ} {T C₀ B : ℕ}
    (h : ∀ r : ℕ, ∀ᶠ L : ℕ in atTop, GoodBlock d τ T C₀ B r L) :
    ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ, GoodBlock d τ T C₀ B r (2 ^ j * L) := by
  intro r L hL
  have hunb : Tendsto (fun k : ℕ => 2 ^ k * L) atTop atTop := by
    have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hpos : (0 : ℕ) < L := by omega
    exact h2.atTop_mul_const' (by exact_mod_cast hpos)
  exact (hunb.eventually (h r)).exists

/-- **The `hterm` field of the tightness interface for the actual array's own records.**

For every block length coefficient `B ≥ 1` there are `T, C₀` such that, almost surely, for every
record-time sequence `τ` of the actual trajectory and every level `L ≥ 1`, some dyadic multiple
of `L` is a good block in the paper's sense.  The hypotheses are exactly `IsRecord` (the
definition of `τ`) and the diameter estimate `(diam)`; the time clause supplied by
`tau_le_of_speed` is no longer assumed. -/
theorem hterm_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ (B : ℕ), 1 ≤ B → ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ (τ : ℕ → ℕ),
        IsRecord (actX p m U) τ →
        Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) →
          ∃ T C₀ : ℕ, 1 ≤ T ∧ ∀ r L : ℕ, 1 ≤ L →
            ∃ j : ℕ, GoodBlock (defect (actX p m U) τ) τ T C₀ B r (2 ^ j * L) := by
  intro B hB N _inst hN
  obtain ⟨κ, hκ, h⟩ := speed_actual hp0 hp1 hm
  filter_upwards [h N hN] with U hU
  intro τ hτ hspread
  have hspeed := hU (Classical.arbitrary (Fin N))
  have hdlim := defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ
    hspeed hspread
  obtain ⟨T, C₀, hT, hC₀, hblocks⟩ :=
    recordo_blocks hτ (actX_step p m U) (actX_zero p m U) hκ hspeed hdlim B hB
  exact ⟨T, C₀, hT, hterm_of_blocks hblocks⟩

end RecordoSupply


/-! ### Non-vacuity: the record-time sequence exists for the actual array -/

namespace RecordoSupply

open RecordDefect
open Filter Topology MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem runMax_step (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (n : ℕ) : |runMax X (n + 1) - runMax X n| ≤ 1 := by
  have hstep_up : ∀ i : ι, X i (n + 1) ≤ X i n + 1 := by
    intro i
    have h := hne i n
    have h2 : X i (n + 1) - X i n ≤ 1 := le_trans (le_abs_self _) (le_of_eq h)
    linarith
  have hstep_dn : ∀ i : ι, X i n ≤ X i (n + 1) + 1 := by
    intro i
    have h := hne i n
    have h2 : -(X i (n + 1) - X i n) ≤ 1 := le_trans (neg_le_abs _) (le_of_eq h)
    linarith
  have h1 : runMax X (n + 1) ≤ runMax X n + 1 := by
    exact Finset.sup'_le (s := Finset.univ) (f := fun i => X i (n + 1)) Finset.univ_nonempty
      (fun i _ => by
        calc X i (n + 1) ≤ X i n + 1 := hstep_up i
          _ ≤ runMax X n + 1 := by linarith [le_runMax (X := X) n i])
  have h2 : runMax X n ≤ runMax X (n + 1) + 1 := by
    exact Finset.sup'_le (s := Finset.univ) (f := fun i => X i n) Finset.univ_nonempty
      (fun i _ => by
        calc X i n ≤ X i (n + 1) + 1 := hstep_dn i
          _ ≤ runMax X (n + 1) + 1 := by linarith [le_runMax (X := X) (n + 1) i])
  rw [abs_le]
  constructor <;> linarith

/-- If the running maximum reaches `r` by time `n`, some time `m ≤ n` attains it exactly. -/
theorem exists_runMax_eq (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) {r n : ℕ} (h : (r : ℤ) ≤ runMax X n) :
    ∃ m ≤ n, runMax X m = (r : ℤ) := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      have hr : (r : ℤ) ≤ 0 := by simpa [runMax_zero X h0] using h
      have : r = 0 := by omega
      subst this
      exact runMax_zero X h0
  | succ n ih =>
      by_cases hc : (r : ℤ) ≤ runMax X n
      · obtain ⟨m, hm, hval⟩ := ih hc
        exact ⟨m, le_trans hm (Nat.le_succ n), hval⟩
      · push_neg at hc
        have hstep := runMax_step X hne n
        have hub : runMax X (n + 1) ≤ (r : ℤ) := by
          have := (abs_le.1 hstep).2
          linarith
        exact ⟨n + 1, le_rfl, le_antisymm hub h⟩


/-- A one-walker speed bound makes the running maximum reach every level. -/
theorem exists_runMax_ge (X : ι → ℕ → ℤ) {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ)) (r : ℕ) :
    ∃ n : ℕ, (r : ℤ) ≤ runMax X n := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hspd
  set n : ℕ := max N₀ ⌈2 * (r : ℝ) / κ⌉₊ with hn
  have hnN : N₀ ≤ n := le_max_left _ _
  have hkey := hN₀ n hnN
  have hle_ceil : (2 * (r : ℝ) / κ) ≤ ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hceil_le : ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    rw [hn]; push_cast; exact le_max_right _ _
  have hle2 : 2 * (r : ℝ) ≤ (n : ℝ) * κ := by
    have h' := hle_ceil
    rw [div_le_iff₀ hκ] at h'
    have hmono : ((⌈2 * (r : ℝ) / κ⌉₊ : ℕ) : ℝ) * κ ≤ (n : ℝ) * κ :=
      mul_le_mul_of_nonneg_right hceil_le (le_of_lt hκ)
    linarith
  have hnr : (r : ℝ) ≤ (κ / 2) * (n : ℝ) := by linarith
  refine ⟨n, ?_⟩
  have hXr : (r : ℝ) ≤ (X i n : ℝ) := le_trans hnr hkey
  have hXrZ : (r : ℤ) ≤ X i n := by exact_mod_cast hXr
  exact le_trans hXrZ (le_runMax (X := X) n i)

/-- The record time of level `r`, as `Nat.find` of the first hitting time. -/
noncomputable def recTime (X : ι → ℕ → ℤ) (h : ∀ r : ℕ, ∃ n, runMax X n = (r : ℤ))
    (r : ℕ) : ℕ :=
  Nat.find (h r)

/-- **The `Nat.find` record times satisfy the paper's `IsRecord` description.** -/
theorem isRecord_recTime (X : ι → ℕ → ℤ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) (h : ∀ r : ℕ, ∃ n, runMax X n = (r : ℤ)) :
    IsRecord X (recTime X h) := by
  intro r
  constructor
  · intro n
    induction n with
    | zero =>
        intro hn
        have hneq := Nat.find_min (h r) hn
        rw [runMax_zero X h0] at hneq ⊢
        omega
    | succ n ih =>
        intro hn
        have hnr : n < recTime X h r := by omega
        have hprev : runMax X n < (r : ℤ) := ih hnr
        have hnot : runMax X (n + 1) ≠ (r : ℤ) := Nat.find_min (h r) hn
        have hub := (abs_le.1 (runMax_step X hne n)).2
        omega
  · exact Nat.find_spec (h r)


/-- **The paper's record times exist for the actual array, with the linear bound**: for almost
every array there is a sequence `τ` satisfying `IsRecord` (so the `hterm_actual` hypothesis is
inhabited) and `τ r ≤ C r`. -/
theorem recordTimes_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∃ τ : ℕ → ℕ, IsRecord (actX p m U) τ ∧
        ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → (τ r : ℝ) ≤ C * (r : ℝ) := by
  obtain ⟨κ, hκ, h⟩ := speed_actual hp0 hp1 hm
  refine ⟨κ, hκ, ?_⟩
  intro N _inst hN
  filter_upwards [h N hN] with U hU
  have hspd := hU (Classical.arbitrary (Fin N))
  have hreach : ∀ r : ℕ, ∃ n, runMax (actX p m U) n = (r : ℤ) := by
    intro r
    obtain ⟨n, hn⟩ := exists_runMax_ge (actX p m U) hκ hspd r
    obtain ⟨m, -, hm⟩ := exists_runMax_eq (actX p m U) (actX_step p m U) (actX_zero p m U) hn
    exact ⟨m, hm⟩
  refine ⟨recTime (actX p m U) hreach, isRecord_recTime _ (actX_step p m U) (actX_zero p m U) hreach, ?_⟩
  exact tau_le_of_speed (isRecord_recTime _ (actX_step p m U) (actX_zero p m U) hreach)
    (actX_step p m U) (actX_zero p m U) hκ hspd

/-- **The tightness interface's `hterm`, for the actual array, with the record times constructed
rather than assumed.** Modulo the diameter estimate `(diam)`, for almost every array there is a
record-time sequence such that every level `L ≥ 1` has a good dyadic multiple. -/
theorem hterm_actual_exists {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (B : ℕ) (hB : 1 ≤ B) :
    ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) →
        ∃ τ : ℕ → ℕ, IsRecord (actX p m U) τ ∧ ∃ T C₀ : ℕ, 1 ≤ T ∧
          ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ, GoodBlock (defect (actX p m U) τ) τ T C₀ B r (2 ^ j * L) := by
  intro N _inst hN
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  filter_upwards [hspeed N hN, hterm_actual hp0 hp1 hm B hB N hN] with U hU hU2 hspread
  have hspd := hU (Classical.arbitrary (Fin N))
  have hreach : ∀ r : ℕ, ∃ n, runMax (actX p m U) n = (r : ℤ) := by
    intro r
    obtain ⟨n, hn⟩ := exists_runMax_ge (actX p m U) hκ hspd r
    obtain ⟨m, -, hm⟩ := exists_runMax_eq (actX p m U) (actX_step p m U) (actX_zero p m U) hn
    exact ⟨m, hm⟩
  have hτ : IsRecord (actX p m U) (recTime (actX p m U) hreach) :=
    isRecord_recTime _ (actX_step p m U) (actX_zero p m U) hreach
  exact ⟨recTime (actX p m U) hreach, hτ, hU2 (recTime (actX p m U) hreach) hτ hspread⟩

end RecordoSupply


namespace RecordoSupply

open RecordDefect
open Filter Topology MeasureTheory

/-- **Packaged endpoint for the record-tightness lane, actual model, modulo `(diam)`.**

For almost every array, if the diameter estimate holds, then there is a record-time sequence `τ`
satisfying the paper's `IsRecord` description together with *all* the almost-sure inputs of
`areas/tightness` for the array's own record data:

* `τ r ≤ C r` (the time clause of (recordo));
* `d_r / r → 0` (the defect clause);
* the doubling form of block goodness at every level `L ≥ 1`, i.e. the shape of the interface
  field `hterm`, with explicit `T` and `C₀ = B + T + 1`.

So, for the actual model, both `hterm` and the defect clause of (recordo) follow from `(diam)`
alone; the only further stochastic input of the tightness chain is the fluid-limit block estimate
`(blkprob)` (field `hblk`), which is untouched here. -/
theorem record_tightness_inputs_actual {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (B : ℕ) (hB : 1 ≤ B) :
    ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0) →
        ∃ τ : ℕ → ℕ, IsRecord (actX p m U) τ ∧
          (∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → (τ r : ℝ) ≤ C * (r : ℝ)) ∧
          Tendsto (fun r : ℕ => (defect (actX p m U) τ r : ℝ) / (r : ℝ)) atTop (𝓝 0) ∧
          (∃ T C₀ : ℕ, 1 ≤ T ∧ ∀ r L : ℕ, 1 ≤ L →
            ∃ j : ℕ, GoodBlock (defect (actX p m U) τ) τ T C₀ B r (2 ^ j * L)) := by
  intro N _inst hN
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  filter_upwards [hspeed N hN, hterm_actual hp0 hp1 hm B hB N hN] with U hU hU2 hspread
  have hspd := hU (Classical.arbitrary (Fin N))
  have hreach : ∀ r : ℕ, ∃ n, runMax (actX p m U) n = (r : ℤ) := by
    intro r
    obtain ⟨n, hn⟩ := exists_runMax_ge (actX p m U) hκ hspd r
    obtain ⟨m, -, hm'⟩ := exists_runMax_eq (actX p m U) (actX_step p m U) (actX_zero p m U) hn
    exact ⟨m, hm'⟩
  have hτ : IsRecord (actX p m U) (recTime (actX p m U) hreach) :=
    isRecord_recTime _ (actX_step p m U) (actX_zero p m U) hreach
  refine ⟨recTime (actX p m U) hreach, hτ, ?_, ?_, hU2 (recTime (actX p m U) hreach) hτ hspread⟩
  · exact tau_le_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd
  · exact defect_div_tendsto_zero_of_speed hτ (actX_step p m U) (actX_zero p m U) hκ hspd hspread

end RecordoSupply

