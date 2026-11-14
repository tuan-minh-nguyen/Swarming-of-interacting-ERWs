/-
# Count-free maximal two-endpoint bounds at a genuine stopping index

This file proves the generic stopped-martingale window estimates requested by the WCJF
local-window sprint, in a form that is usable both abstractly (a real martingale and a
finite-valued stopping index) and in the actual record-clock application (a random start that is
*not* a stopping time but whose fibres are refined by an adapted family of disjoint bands).

For a real martingale `Q` in a filtration `ℱ` with increments bounded by `C`, `n ≥ 1`, `ε > 0`:

* `measureReal_stoppedWindow_le` — for a stopping index `σ` (`{σ ≤ t} ∈ ℱ t`),
  `μ.real {ω | ∃ s ≤ n, ∃ k ≤ n - s, ε ≤ |Q (σ ω + s + k) ω - Q (σ ω + s) ω|}`
    `≤ 2 (n+1)^2 exp (-(ε^2)/(4 n C^2))`;
* `measureReal_stoppedMax_le` — the single random start form,
  `μ.real {ω | ∃ k ≤ n, ε ≤ |Q (σ ω + k) ω - Q (σ ω) ω|}`
    `≤ 2 (n+1) exp (-(ε^2)/(4 n C^2))`;
* `measureReal_band_stoppedWindow_le` / `measureReal_band_stoppedMax_le` — the same two bounds
  on a set `G` covered by an adapted family of pairwise disjoint bands `B a`, each band refining
  the fibre `{σ = a}` on `G`.  **No measurability of `σ` is assumed at all**; this is the form
  that applies to the actual record clock, where the fibres are only known on `ReachAll` and
  through prefix events.

* `measureReal_band_stoppedWindow_le_of_carrier` / `..._of_carrier_global` — the same bound when
  the increment bound only holds on an adapted carrier `Car`; the price is one explicitly measured
  carrier-deficit set, handed back to the consumer;
* `measureReal_stoppedWindow_le_of_enat` / `measureReal_stoppedMax_le_of_enat` — the same bounds for
  an `ℕ∞`-valued clock `τ` (`Swarming.Enl.maxClock`) whose finite fibres are measurable and whose
  top fibre is null; the `ℕ`-valued reading is `τ.toNat`.

In every case the polynomial prefactor is **independent of the random start**: there is no
`A + 1` union factor over clock values, no truncation `σ ∧ A`, and no almost-sure bound on `σ`.

## Route (a genuine stopped estimate, not a union over clocks)

The estimate is *not* proved by truncating `σ` and unioning over the truncation levels.  It is
proved band-wise with an exact mass factor.  On the band `B a` (which is `ℱ a`-measurable) the
stopped window is a *deterministic* start window at time `a + s`, so the verified weighted cell
estimate `ShiftedAdvance.measureReal_cell_max_abs_shift_le_of_ptrunc`
(`Swarm/WeightedShiftCell.lean`) applies to the martingale increments
`ξ t = Q (t+1) - Q t` with start `a + s` and cell `B a`:

  `μ.real (B a ∩ {∃ k ≤ n, ε ≤ |Q (a+s+k) - Q (a+s)|})`
    `≤ μ.real (B a) * (2 (n+1) exp (-(ε^2)/(4 n C^2)))`.

That cell estimate conditions the *measure* on the cell (`ν = μ[|B a]`), transfers the vanishing
conditional mean by `ShiftedAdvance.condExp_eq_zero_cond_of_measurableSet`, and runs the verified
maximal Azuma bound `LocMart.measure_max_abs_psum_ge_le` under `ν`.  Conditioning is not a restart
or independence assertion: it is an exact change of measure, and the mass factor `μ.real (B a)` is
exactly what makes the countable sum over the bands converge with a single constant instead of
`A + 1`.  Summing the disjoint bands gives the stated count-free bound; the only union left is the
honest, deterministic union over the `n+1` window starts `s ≤ n` (present only in the two-endpoint
form).

## Provenance of the increment bound

`hbdd` below is a **pointwise** bound on the increments.  A bound which only holds on a
predictable carrier is *not* silently assumed away: it is not part of the generic statement, and a
consumer with a carrier must either restrict to the good set (which costs nothing for the
conclusion, by monotonicity of `μ.real`) or use the a.e.-carrier cell estimate
`ShiftedAdvance.measureReal_cell_max_abs_shift_le_of_ptrunc_ae`.

No `sorry`, no `admit`, no new axiom, no `native_decide`.
-/
import Swarm.WeightedShiftCell

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace StoppedWindow

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### The measured events -/

/-- The stopped two-endpoint window event: starting at the random time `σ`, over every window
`[σ + s, σ + s + k]` with `s ≤ n` and `k ≤ n - s`, the deviation exceeds `ε`. -/
def stoppedWindow (Q : ℕ → Ω → ℝ) (σ : Ω → ℕ) (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∃ s ≤ n, ∃ k ≤ n - s, ε ≤ |Q (σ ω + s + k) ω - Q (σ ω + s) ω|}

/-- The stopped maximum event at a single random start `σ`: some window of length `k ≤ n` after
`σ` deviates from `Q σ` by at least `ε`. -/
def stoppedMax (Q : ℕ → Ω → ℝ) (σ : Ω → ℕ) (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∃ k ≤ n, ε ≤ |Q (σ ω + k) ω - Q (σ ω) ω|}

/-- The window event on an adapted band `B a` at the deterministic start `a + s`. -/
def bandWindow (Q : ℕ → Ω → ℝ) (B : ℕ → Set Ω) (n : ℕ) (ε : ℝ) (s a : ℕ) : Set Ω :=
  B a ∩ {ω | ∃ k ≤ n, ε ≤ |Q (a + s + k) ω - Q (a + s) ω|}

/-- The one-start maximum event on an adapted band `B a` at the deterministic start `a`. -/
def bandMax (Q : ℕ → Ω → ℝ) (B : ℕ → Set Ω) (n : ℕ) (ε : ℝ) (a : ℕ) : Set Ω :=
  B a ∩ {ω | ∃ k ≤ n, ε ≤ |Q (a + k) ω - Q a ω|}

@[simp] lemma mem_stoppedWindow {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} {n : ℕ} {ε : ℝ} {ω : Ω} :
    ω ∈ stoppedWindow Q σ n ε ↔
      ∃ s ≤ n, ∃ k ≤ n - s, ε ≤ |Q (σ ω + s + k) ω - Q (σ ω + s) ω| :=
  Iff.rfl

@[simp] lemma mem_stoppedMax {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} {n : ℕ} {ε : ℝ} {ω : Ω} :
    ω ∈ stoppedMax Q σ n ε ↔ ∃ k ≤ n, ε ≤ |Q (σ ω + k) ω - Q (σ ω) ω| :=
  Iff.rfl

@[simp] lemma mem_bandWindow {Q : ℕ → Ω → ℝ} {B : ℕ → Set Ω} {n : ℕ} {ε : ℝ} {s a : ℕ}
    {ω : Ω} :
    ω ∈ bandWindow Q B n ε s a ↔
      ω ∈ B a ∧ ∃ k ≤ n, ε ≤ |Q (a + s + k) ω - Q (a + s) ω| :=
  Iff.rfl

@[simp] lemma mem_bandMax {Q : ℕ → Ω → ℝ} {B : ℕ → Set Ω} {n : ℕ} {ε : ℝ} {a : ℕ} {ω : Ω} :
    ω ∈ bandMax Q B n ε a ↔ ω ∈ B a ∧ ∃ k ≤ n, ε ≤ |Q (a + k) ω - Q a ω| :=
  Iff.rfl

/-- The exact fibres of a `ℕ`-valued function cover the whole space. -/
lemma iUnion_fibre_eq_univ (σ : Ω → ℕ) : (⋃ j, {ω | σ ω = j} : Set Ω) = Set.univ := by
  ext ω
  simp

/-- `stoppedMax ⊆ stoppedWindow`: the single-start event is the `s = 0` piece of the two-endpoint
event.  (Stated for completeness; the sharper bound for `stoppedMax` is proved separately.) -/
lemma stoppedMax_subset_stoppedWindow {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} {n : ℕ} {ε : ℝ} :
    stoppedMax Q σ n ε ⊆ stoppedWindow Q σ n ε := by
  rintro ω ⟨k, hk, hdev⟩
  exact ⟨0, Nat.zero_le n, k, by simpa using hk, by simpa using hdev⟩

/-! ### Fibre measurability of a finite-valued stopping index -/

/-- The exact fibre `{σ = j}` of a stopping index is measurable at every time `t ≥ j`. -/
lemma measurableSet_stopping_eq {σ : Ω → ℕ}
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t}) {j t : ℕ} (hjt : j ≤ t) :
    MeasurableSet[ℱ t] {ω | σ ω = j} := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have h : {ω : Ω | σ ω = 0} = {ω | σ ω ≤ 0} := by
      ext ω; simp
    rw [h]
    exact ℱ.mono (Nat.zero_le t) _ (hσ 0)
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h : {ω : Ω | σ ω = j' + 1} =
        {ω | σ ω ≤ j' + 1} ∩ {ω | σ ω ≤ j'}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
      omega
    rw [h]
    exact (ℱ.mono (by omega) _ (hσ (j' + 1))).inter (ℱ.mono (by omega) _ (hσ j')).compl

/-- Bridge: the raw condition `∀ t, {σ ≤ t} ∈ ℱ t` used in this file is Mathlib's
`IsStoppingTime` for the `WithTop ℕ`-valued coercion of `σ`. -/
lemma isStoppingTime_nat {σ : Ω → ℕ}
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t}) :
    MeasureTheory.IsStoppingTime ℱ fun ω => (σ ω : WithTop ℕ) := by
  intro i
  change MeasurableSet[ℱ i] {ω : Ω | (σ ω : WithTop ℕ) ≤ (i : WithTop ℕ)}
  have h : {ω : Ω | (σ ω : WithTop ℕ) ≤ (i : WithTop ℕ)} = {ω | σ ω ≤ i} := by
    ext ω
    exact WithTop.coe_le_coe
  rw [h]
  exact hσ i

/-! ### Martingale increments have vanishing conditional mean -/

/-- The increment process of `Q`. -/
def increments (Q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => Q (t + 1) ω - Q t ω

@[simp] lemma increments_apply (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    increments Q t ω = Q (t + 1) ω - Q t ω := rfl

/-- Increments of a martingale have vanishing conditional mean at the current time. -/
lemma martingale_increment_condExp (hQ : Martingale Q ℱ μ) (t : ℕ) :
    μ[increments Q t | ℱ t] =ᵐ[μ] 0 := by
  change μ[Q (t + 1) - Q t | ℱ t] =ᵐ[μ] 0
  have hsub := condExp_sub (hQ.integrable (t + 1)) (hQ.integrable t) (ℱ t)
  have h1 : μ[Q (t + 1) | ℱ t] =ᵐ[μ] Q t := hQ.condExp_ae_eq (Nat.le_succ t)
  have h2 : μ[Q t | ℱ t] =ᵐ[μ] Q t := hQ.condExp_ae_eq (le_refl t)
  filter_upwards [hsub, h1, h2] with ω hω h1 h2
  simp only [Pi.sub_apply] at hω
  simp only [Pi.zero_apply, hω, h1, h2, sub_self]

/-! ### The weighted single-band estimate -/

/-- **Weighted single-band bound.**  On an `ℱ a`-measurable band `B a` the deviation of the
window of length `k ≤ n` starting at the deterministic time `a + s` is controlled, *with the exact
mass factor* `μ.real (B a)`.  This is the piece that makes the sum over the bands converge. -/
lemma bandWindow_bound [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {B : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (s a : ℕ) :
    μ.real (bandWindow Q B n ε s a) ≤
      μ.real (B a) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) := by
  have hA : MeasurableSet[ℱ (a + s)] (B a) := ℱ.mono (Nat.le_add_right a s) _ (hBm a)
  have hξm : ∀ k : ℕ, StronglyMeasurable[ℱ (a + s + k + 1)] (increments Q (a + s + k)) := by
    intro k
    have h1 : StronglyMeasurable[ℱ (a + s + k + 1)] (Q (a + s + k + 1)) :=
      hQm (a + s + k + 1)
    have h2 : StronglyMeasurable[ℱ (a + s + k + 1)] (Q (a + s + k)) :=
      (hQm (a + s + k)).mono (ℱ.mono (Nat.le_succ _))
    exact h1.sub h2
  have hξi : ∀ k : ℕ, Integrable (increments Q (a + s + k)) μ := by
    intro k
    exact (hQi (a + s + k + 1)).sub (hQi (a + s + k))
  have hξ0 : ∀ k : ℕ, μ[increments Q (a + s + k) | ℱ (a + s + k)] =ᵐ[μ] 0 :=
    fun k => hQ0 (a + s + k)
  have hbdd' : ∀ k : ℕ, ∀ ω ∈ (Set.univ : Set Ω), |increments Q (a + s + k) ω| ≤ C := by
    intro k ω _
    exact hbdd (a + s + k) ω
  have hcell := ShiftedAdvance.measureReal_cell_max_abs_shift_le_of_ptrunc
    (μ := μ) (ℱ := ℱ) (s := a + s) (A := B a) hA
    (G := fun _ => Set.univ) (hG := fun _ => MeasurableSet.univ)
    (ξ := increments Q) hξm hξi hξ0 hC hbdd' hn hε
  have hempty : {ω : Ω | ∃ k < n, ω ∉ (Set.univ : Set Ω)} = ∅ := by
    ext ω
    simp
  rw [hempty, Set.inter_empty, measureReal_empty, add_zero] at hcell
  have htel : ∀ (k : ℕ) (ω : Ω),
      LocMart.psum (increments Q) (a + s + k) ω - LocMart.psum (increments Q) (a + s) ω
        = Q (a + s + k) ω - Q (a + s) ω := by
    intro k ω
    change LocMart.psum (fun t ω => Q (t + 1) ω - Q t ω) (a + s + k) ω -
      LocMart.psum (fun t ω => Q (t + 1) ω - Q t ω) (a + s) ω = _
    rw [ShiftedAdvance.psum_succ_sub, ShiftedAdvance.psum_succ_sub]
    ring
  have hset : B a ∩
      {ω | ∃ k ≤ n, ε ≤ |LocMart.psum (increments Q) (a + s + k) ω -
        LocMart.psum (increments Q) (a + s) ω|} = bandWindow Q B n ε s a := by
    ext ω
    simp only [mem_bandWindow, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, k, hk, hdev⟩
      exact ⟨h1, k, hk, by rw [← htel k ω]; exact hdev⟩
    · rintro ⟨h1, k, hk, hdev⟩
      exact ⟨h1, k, hk, by rw [htel k ω]; exact hdev⟩
  rw [hset] at hcell
  exact hcell

/-- The exact-fibre form of `bandWindow_bound`: the weighted cell bound on the fibre `{σ = j}`,
where the stopped window becomes the deterministic-start window at time `j + s`. -/
lemma fibreWindow_bound [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (s j : ℕ) :
    μ.real (bandWindow Q (fun a => {ω | σ ω = a}) n ε s j) ≤
      μ.real {ω | σ ω = j} *
        (2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) :=
  bandWindow_bound hQm hQi hQ0 hC hbdd
    (fun a => measurableSet_stopping_eq hσ (le_refl a)) hn hε s j

/-! ### Summing the bands: the count-free profile -/

/-- **The mass bookkeeping.**  If the bands `B a` are `ℱ a`-measurable and pairwise disjoint then
the union of the window events over all bands has probability at most the Azuma profile
`2 (n+1) exp (-(ε^2)/(4 n C^2))`, with no factor depending on the number of bands or on a cutoff
on the band index. -/
lemma band_iUnion_window_le [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {B : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (s : ℕ) :
    μ.real (⋃ a, bandWindow Q B n ε s a) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  set c₀ : ℝ := 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) with hc₀
  have hc₀pos : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hdisj : Pairwise (Function.onFun Disjoint B) := fun a b hab => hBdisj a b hab
  have hENN : ∑' a, μ (bandWindow Q B n ε s a) ≤ ENNReal.ofReal c₀ := by
    calc ∑' a, μ (bandWindow Q B n ε s a)
        ≤ ∑' a, ENNReal.ofReal c₀ * μ (B a) := by
          refine ENNReal.tsum_le_tsum fun a => ?_
          have h1 : μ (bandWindow Q B n ε s a)
              = ENNReal.ofReal (μ.real (bandWindow Q B n ε s a)) :=
            (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
          have h2 : μ.real (bandWindow Q B n ε s a) ≤ c₀ * μ.real (B a) := by
            rw [hc₀]
            refine (bandWindow_bound hQm hQi hQ0 hC hbdd hBm hn hε s a).trans (le_of_eq ?_)
            ring
          calc μ (bandWindow Q B n ε s a)
              = ENNReal.ofReal (μ.real (bandWindow Q B n ε s a)) := h1
            _ ≤ ENNReal.ofReal (c₀ * μ.real (B a)) := ENNReal.ofReal_le_ofReal h2
            _ = ENNReal.ofReal c₀ * ENNReal.ofReal (μ.real (B a)) := ENNReal.ofReal_mul hc₀pos
            _ = ENNReal.ofReal c₀ * μ (B a) := by
                rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      _ = ENNReal.ofReal c₀ * ∑' a, μ (B a) := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal c₀ * μ (⋃ a, B a) := by
          rw [measure_iUnion hdisj (fun a => ℱ.le a _ (hBm a))]
      _ ≤ ENNReal.ofReal c₀ * μ Set.univ :=
          mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
      _ = ENNReal.ofReal c₀ := by rw [measure_univ, mul_one]
  calc μ.real (⋃ a, bandWindow Q B n ε s a)
      = (μ (⋃ a, bandWindow Q B n ε s a)).toReal := rfl
    _ ≤ (∑' a, μ (bandWindow Q B n ε s a)).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN) (measure_iUnion_le _)
    _ ≤ (ENNReal.ofReal c₀).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = c₀ := ENNReal.toReal_ofReal hc₀pos

/-! ### The band form (no measurability of the random start) -/

/-- **Band-localised count-free two-endpoint bound.**  Let `B a` be an `ℱ a`-measurable,
pairwise disjoint family covering `G`, and suppose that on `G` each band refines the fibre of the
random start `σ`: `G ∩ B a ⊆ {σ = a}`.  Then

  `μ.real (G ∩ stoppedWindow Q σ n ε) ≤ 2 (n+1)^2 exp (-(ε^2)/(4 n C^2))`.

No measurability, integrability or finiteness of `σ` is assumed. -/
theorem measureReal_band_stoppedWindow_le [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {σ : Ω → ℕ} {B : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {G : Set Ω} (hG : G ⊆ ⋃ a, B a) (hBσ : ∀ a, G ∩ B a ⊆ {ω | σ ω = a})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (G ∩ stoppedWindow Q σ n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have hsub : G ∩ stoppedWindow Q σ n ε ⊆
      ⋃ s ∈ Finset.range (n + 1), ⋃ a, bandWindow Q B n ε s a := by
    rintro ω ⟨hωG, s, hs, k, hk, hdev⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hG hωG)
    have hσa : σ ω = a := hBσ a ⟨hωG, ha⟩
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hs)) ?_
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [mem_bandWindow]
    exact ⟨ha, k, le_trans hk (Nat.sub_le n s), by rwa [hσa] at hdev⟩
  have hb : ∀ s : ℕ, μ.real (⋃ a, bandWindow Q B n ε s a) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) :=
    fun s => band_iUnion_window_le hQm hQi hQ0 hC hbdd hBm hBdisj hn hε s
  calc μ.real (G ∩ stoppedWindow Q σ n ε)
      ≤ μ.real (⋃ s ∈ Finset.range (n + 1), ⋃ a, bandWindow Q B n ε s a) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ s ∈ Finset.range (n + 1), μ.real (⋃ a, bandWindow Q B n ε s a) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ Finset.range (n + 1),
          2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) :=
        Finset.sum_le_sum fun s _ => hb s
    _ = 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Band-localised count-free one-start bound.**  The `s = 0` piece of the two-endpoint event,
with the sharper profile `2 (n+1) exp (-(ε^2)/(4 n C^2))`. -/
theorem measureReal_band_stoppedMax_le [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {σ : Ω → ℕ} {B : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {G : Set Ω} (hG : G ⊆ ⋃ a, B a) (hBσ : ∀ a, G ∩ B a ⊆ {ω | σ ω = a})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (G ∩ stoppedMax Q σ n ε) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have hsub : G ∩ stoppedMax Q σ n ε ⊆ ⋃ a, bandMax Q B n ε a := by
    rintro ω ⟨hωG, k, hk, hdev⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hG hωG)
    have hσa : σ ω = a := hBσ a ⟨hωG, ha⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [mem_bandMax]
    exact ⟨ha, k, hk, by rwa [hσa] at hdev⟩
  have hband : ∀ a, bandMax Q B n ε a = bandWindow Q B n ε 0 a := by
    intro a
    ext ω
    simp only [mem_bandMax, mem_bandWindow, Nat.add_zero]
  calc μ.real (G ∩ stoppedMax Q σ n ε)
      ≤ μ.real (⋃ a, bandMax Q B n ε a) := measureReal_mono hsub (measure_ne_top μ _)
    _ = μ.real (⋃ a, bandWindow Q B n ε 0 a) := by simp only [hband]
    _ ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) :=
        band_iUnion_window_le hQm hQi hQ0 hC hbdd hBm hBdisj hn hε 0

/-! ### The stopping-index form -/

/-- **Count-free maximal two-endpoint deviation bound at a genuine stopping index.**

For a real martingale `Q` with increments bounded by `C`, a finite-valued stopping index `σ`,
`n ≥ 1` and `ε > 0`, the probability that some window `[σ + s, σ + s + k]` with `s ≤ n`,
`k ≤ n - s` contains a deviation of size `ε` is at most
`2 (n+1)^2 exp (-(ε^2)/(4 n C^2))` — with no dependence on `σ` beyond the stopping property.
It is proved fibre-wise with exact mass factors, so it is a stopped estimate and not a union bound
over the values of `σ`. -/
theorem measureReal_stoppedWindow_le [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedWindow Q σ n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have h := measureReal_band_stoppedWindow_le (Q := Q) (σ := σ)
    (B := fun a => {ω | σ ω = a})
    hQm hQi hQ0 hC hbdd
    (fun a => measurableSet_stopping_eq hσ (le_refl a))
    (fun a b hab => by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      exact hab (Nat.cast_injective (h1.symm.trans h2)))
    (by rw [iUnion_fibre_eq_univ])
    (fun a => Set.inter_subset_right) hn hε
  rwa [Set.univ_inter] at h

/-- **Count-free maximal one-start deviation bound at a genuine stopping index.** -/
theorem measureReal_stoppedMax_le [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedMax Q σ n ε) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have h := measureReal_band_stoppedMax_le (Q := Q) (σ := σ)
    (B := fun a => {ω | σ ω = a})
    hQm hQi hQ0 hC hbdd
    (fun a => measurableSet_stopping_eq hσ (le_refl a))
    (fun a b hab => by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      exact hab (Nat.cast_injective (h1.symm.trans h2)))
    (by rw [iUnion_fibre_eq_univ])
    (fun a => Set.inter_subset_right) hn hε
  rwa [Set.univ_inter] at h

/-! ### Martingale form -/

/-- The stopped window bound stated directly for a Mathlib `Martingale`. -/
theorem measureReal_stoppedWindow_le_of_martingale [IsProbabilityMeasure μ]
    {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} (hQ : Martingale Q ℱ μ)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedWindow Q σ n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) :=
  measureReal_stoppedWindow_le (fun t => hQ.stronglyMeasurable t) (fun t => hQ.integrable t)
    (martingale_increment_condExp hQ) hC hbdd hσ hn hε

/-- The stopped one-start bound stated directly for a Mathlib `Martingale`. -/
theorem measureReal_stoppedMax_le_of_martingale [IsProbabilityMeasure μ]
    {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} (hQ : Martingale Q ℱ μ)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hσ : ∀ t, MeasurableSet[ℱ t] {ω | σ ω ≤ t})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedMax Q σ n ε) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) :=
  measureReal_stoppedMax_le (fun t => hQ.stronglyMeasurable t) (fun t => hQ.integrable t)
    (martingale_increment_condExp hQ) hC hbdd hσ hn hε

/-- **Consistency check at a deterministic start.**  With `σ ≡ 0` the stopped bound must reduce to
the deterministic-start two-endpoint estimate; it does, with exactly the same profile. -/
theorem measureReal_window_le_const [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω : Ω | ∃ s ≤ n, ∃ k ≤ n - s, ε ≤ |Q (s + k) ω - Q s ω|} ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have hσ : ∀ t, MeasurableSet[ℱ t] {ω : Ω | (fun _ : Ω => 0) ω ≤ t} := by
    intro t
    have h : {ω : Ω | (fun _ : Ω => 0) ω ≤ t} = Set.univ := by
      ext ω; simp
    rw [h]
    exact MeasurableSet.univ
  have h := measureReal_stoppedWindow_le (σ := fun _ : Ω => 0) hQm hQi hQ0 hC hbdd hσ hn hε
  have hset : stoppedWindow Q (fun _ : Ω => 0) n ε =
      {ω : Ω | ∃ s ≤ n, ∃ k ≤ n - s, ε ≤ |Q (s + k) ω - Q s ω|} := by
    ext ω
    simp only [mem_stoppedWindow]
    constructor
    · rintro ⟨s, hs, k, hk, hdev⟩
      exact ⟨s, hs, k, hk, by simpa using hdev⟩
    · rintro ⟨s, hs, k, hk, hdev⟩
      exact ⟨s, hs, k, hk, by simpa using hdev⟩
  rw [hset] at h
  exact h

/-! ### Carrier-restricted increment bounds

In the actual WCJF model the increment bound on the local martingale is typically available only
on a measurable *carrier* (a good set of configurations), not pointwise everywhere.  The results
below keep that restriction explicit: the price is one explicitly measured carrier-deficit set,
which the consumer bounds separately.  Nothing is postulated about the carrier's probability.
-/

/-- The carrier-deficit set at window offset `s`: inside some band `B a`, the carrier fails
somewhere in the window `[a + s, a + s + n)`. -/
def bandCarrierDeficit (B Car : ℕ → Set Ω) (n s : ℕ) : Set Ω :=
  ⋃ a, (B a ∩ {ω | ∃ k < n, ω ∉ Car (a + s + k)})

/-- **Weighted single-band bound with a carrier-restricted increment bound.** -/
lemma bandWindow_bound_of_carrier [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ} {B Car : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hCarm : ∀ t, MeasurableSet[ℱ t] (Car t))
    (hbdd : ∀ t ω, ω ∈ Car t → |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (s a : ℕ) :
    μ.real (bandWindow Q B n ε s a) ≤
      μ.real (B a) * (2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
        μ.real (B a ∩ {ω | ∃ k < n, ω ∉ Car (a + s + k)}) := by
  have hA : MeasurableSet[ℱ (a + s)] (B a) := ℱ.mono (Nat.le_add_right a s) _ (hBm a)
  have hξm : ∀ k : ℕ, StronglyMeasurable[ℱ (a + s + k + 1)] (increments Q (a + s + k)) := by
    intro k
    have h1 : StronglyMeasurable[ℱ (a + s + k + 1)] (Q (a + s + k + 1)) :=
      hQm (a + s + k + 1)
    have h2 : StronglyMeasurable[ℱ (a + s + k + 1)] (Q (a + s + k)) :=
      (hQm (a + s + k)).mono (ℱ.mono (Nat.le_succ _))
    exact h1.sub h2
  have hξi : ∀ k : ℕ, Integrable (increments Q (a + s + k)) μ := by
    intro k
    exact (hQi (a + s + k + 1)).sub (hQi (a + s + k))
  have hξ0 : ∀ k : ℕ, μ[increments Q (a + s + k) | ℱ (a + s + k)] =ᵐ[μ] 0 :=
    fun k => hQ0 (a + s + k)
  have hbdd' : ∀ k : ℕ, ∀ ω ∈ Car (a + s + k), |increments Q (a + s + k) ω| ≤ C := by
    intro k ω hω
    exact hbdd (a + s + k) ω hω
  have hcell := ShiftedAdvance.measureReal_cell_max_abs_shift_le_of_ptrunc
    (μ := μ) (ℱ := ℱ) (s := a + s) (A := B a) hA
    (G := fun k => Car (a + s + k)) (hG := fun k => hCarm (a + s + k))
    (ξ := increments Q) hξm hξi hξ0 hC hbdd' hn hε
  have htel : ∀ (k : ℕ) (ω : Ω),
      LocMart.psum (increments Q) (a + s + k) ω - LocMart.psum (increments Q) (a + s) ω
        = Q (a + s + k) ω - Q (a + s) ω := by
    intro k ω
    change LocMart.psum (fun t ω => Q (t + 1) ω - Q t ω) (a + s + k) ω -
      LocMart.psum (fun t ω => Q (t + 1) ω - Q t ω) (a + s) ω = _
    rw [ShiftedAdvance.psum_succ_sub, ShiftedAdvance.psum_succ_sub]
    ring
  have hset : B a ∩
      {ω | ∃ k ≤ n, ε ≤ |LocMart.psum (increments Q) (a + s + k) ω -
        LocMart.psum (increments Q) (a + s) ω|} = bandWindow Q B n ε s a := by
    ext ω
    simp only [mem_bandWindow, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, k, hk, hdev⟩
      exact ⟨h1, k, hk, by rw [← htel k ω]; exact hdev⟩
    · rintro ⟨h1, k, hk, hdev⟩
      exact ⟨h1, k, hk, by rw [htel k ω]; exact hdev⟩
  rw [hset] at hcell
  exact hcell

/-- **Union over the bands at a fixed window offset, with carrier.** -/
lemma band_iUnion_window_le_of_carrier [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {B Car : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hCarm : ∀ t, MeasurableSet[ℱ t] (Car t))
    (hbdd : ∀ t ω, ω ∈ Car t → |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (s : ℕ) :
    μ.real (⋃ a, bandWindow Q B n ε s a) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
        μ.real (bandCarrierDeficit B Car n s) := by
  set c₀ : ℝ := 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) with hc₀
  have hc₀pos : 0 ≤ c₀ := by rw [hc₀]; positivity
  set bad : ℕ → Set Ω := fun a => B a ∩ {ω | ∃ k < n, ω ∉ Car (a + s + k)} with hbaddef
  have hbadmeas : ∀ a, MeasurableSet (bad a) := by
    intro a
    refine MeasurableSet.inter (ℱ.le a _ (hBm a)) ?_
    have h : {ω : Ω | ∃ k < n, ω ∉ Car (a + s + k)} = ⋃ k ∈ Finset.range n, (Car (a + s + k))ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Finset.mem_range, Set.mem_iUnion, Set.mem_compl_iff,
        exists_prop]
    rw [h]
    exact Finset.measurableSet_biUnion _ (fun k _ => (ℱ.le (a + s + k) _ (hCarm (a + s + k))).compl)
  have hbadisj : Pairwise (Function.onFun Disjoint bad) := by
    intro a b hab
    show Disjoint (bad a) (bad b)
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hBdisj a b hab)
  have hdisjB : Pairwise (Function.onFun Disjoint B) := fun a b hab => hBdisj a b hab
  have hfinite : ENNReal.ofReal c₀ * μ (⋃ a, B a) + μ (bandCarrierDeficit B Car n s) ≠ ∞ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _), ?_⟩
    exact measure_ne_top μ _
  have hterm : ∀ a, μ (bandWindow Q B n ε s a) ≤
      ENNReal.ofReal c₀ * μ (B a) + μ (bad a) := by
    intro a
    have h1 : μ (bandWindow Q B n ε s a)
        = ENNReal.ofReal (μ.real (bandWindow Q B n ε s a)) :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    have h2 : μ.real (bandWindow Q B n ε s a) ≤ c₀ * μ.real (B a) + μ.real (bad a) := by
      have hb := bandWindow_bound_of_carrier hQm hQi hQ0 hC hCarm hbdd hBm hn hε s a
      rw [hc₀]
      calc μ.real (bandWindow Q B n ε s a)
          ≤ μ.real (B a) * (2 * ((n : ℝ) + 1) *
              Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
              μ.real (B a ∩ {ω | ∃ k < n, ω ∉ Car (a + s + k)}) := hb
        _ = 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) * μ.real (B a) +
              μ.real (bad a) := by rw [hbaddef]; ring
    have h3 : ENNReal.ofReal (c₀ * μ.real (B a) + μ.real (bad a))
        = ENNReal.ofReal c₀ * μ (B a) + μ (bad a) := by
      rw [ENNReal.ofReal_add (mul_nonneg hc₀pos measureReal_nonneg) measureReal_nonneg,
        ENNReal.ofReal_mul hc₀pos, Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
        Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    calc μ (bandWindow Q B n ε s a)
        = ENNReal.ofReal (μ.real (bandWindow Q B n ε s a)) := h1
      _ ≤ ENNReal.ofReal (c₀ * μ.real (B a) + μ.real (bad a)) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal c₀ * μ (B a) + μ (bad a) := h3
  have hENN : ∑' a, μ (bandWindow Q B n ε s a) ≤
      ENNReal.ofReal c₀ * μ (⋃ a, B a) + μ (bandCarrierDeficit B Car n s) := by
    calc ∑' a, μ (bandWindow Q B n ε s a)
        ≤ ∑' a, (ENNReal.ofReal c₀ * μ (B a) + μ (bad a)) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal c₀ * ∑' a, μ (B a) + ∑' a, μ (bad a) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal c₀ * μ (⋃ a, B a) + μ (bandCarrierDeficit B Car n s) := by
          have hbadeq : (⋃ i, bad i) = bandCarrierDeficit B Car n s := by
            rw [hbaddef]
            rfl
          rw [measure_iUnion hdisjB (fun a => ℱ.le a _ (hBm a)),
            ← measure_iUnion hbadisj hbadmeas, hbadeq]
  have hle1 : μ.real (⋃ a, B a) ≤ 1 := by
    calc μ.real (⋃ a, B a) ≤ μ.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
      _ = 1 := by rw [Measure.real_def, measure_univ, ENNReal.toReal_one]
  have hsumle : μ (⋃ a, bandWindow Q B n ε s a) ≤ ∑' a, μ (bandWindow Q B n ε s a) :=
    measure_iUnion_le _
  have hne : ∑' a, μ (bandWindow Q B n ε s a) ≠ ∞ := ne_top_of_le_ne_top hfinite hENN
  calc μ.real (⋃ a, bandWindow Q B n ε s a)
      = (μ (⋃ a, bandWindow Q B n ε s a)).toReal := rfl
    _ ≤ (∑' a, μ (bandWindow Q B n ε s a)).toReal := ENNReal.toReal_mono hne hsumle
    _ ≤ (ENNReal.ofReal c₀ * μ (⋃ a, B a) + μ (bandCarrierDeficit B Car n s)).toReal :=
        ENNReal.toReal_mono hfinite hENN
    _ = (ENNReal.ofReal c₀ * μ (⋃ a, B a)).toReal +
          (μ (bandCarrierDeficit B Car n s)).toReal :=
        ENNReal.toReal_add
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) (measure_ne_top μ _)
    _ = c₀ * μ.real (⋃ a, B a) + μ.real (bandCarrierDeficit B Car n s) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₀pos]
        rfl
    _ ≤ c₀ + μ.real (bandCarrierDeficit B Car n s) := by
        have h : c₀ * μ.real (⋃ a, B a) ≤ c₀ := mul_le_of_le_one_right hc₀pos hle1
        linarith
    _ = 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
          μ.real (bandCarrierDeficit B Car n s) := by rw [hc₀]

/-- **Carrier-restricted count-free two-endpoint bound.**  The increment bound need only hold on
the adapted carrier `Car`; the price is one explicitly measured deficit set `Dfilter` containing
every band-carrier deficit. -/
theorem measureReal_band_stoppedWindow_le_of_carrier [IsProbabilityMeasure μ]
    {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} {B Car : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hCarm : ∀ t, MeasurableSet[ℱ t] (Car t))
    (hbdd : ∀ t ω, ω ∈ Car t → |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {G₀ : Set Ω} (hG : G₀ ⊆ ⋃ a, B a) (hBσ : ∀ a, G₀ ∩ B a ⊆ {ω | σ ω = a})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {Dfilter : Set Ω} (hD : ∀ s ∈ Finset.range (n + 1), bandCarrierDeficit B Car n s ⊆ Dfilter) :
    μ.real (G₀ ∩ stoppedWindow Q σ n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
        ((n : ℝ) + 1) * μ.real Dfilter := by
  have hsub : G₀ ∩ stoppedWindow Q σ n ε ⊆
      ⋃ s ∈ Finset.range (n + 1), ⋃ a, bandWindow Q B n ε s a := by
    rintro ω ⟨hωG, s, hs, k, hk, hdev⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (hG hωG)
    have hσa : σ ω = a := hBσ a ⟨hωG, ha⟩
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hs)) ?_
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [mem_bandWindow]
    exact ⟨ha, k, le_trans hk (Nat.sub_le n s), by rwa [hσa] at hdev⟩
  have hbs : ∀ s : ℕ, μ.real (⋃ a, bandWindow Q B n ε s a) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
        μ.real (bandCarrierDeficit B Car n s) :=
    fun s => band_iUnion_window_le_of_carrier hQm hQi hQ0 hC hCarm hbdd hBm hBdisj hn hε s
  have hmono : ∑ s ∈ Finset.range (n + 1), μ.real (bandCarrierDeficit B Car n s) ≤
      ((n : ℝ) + 1) * μ.real Dfilter := by
    have h1 : ∀ s ∈ Finset.range (n + 1),
        μ.real (bandCarrierDeficit B Car n s) ≤ μ.real Dfilter := by
      intro s hs
      exact measureReal_mono (hD s hs) (measure_ne_top μ _)
    calc ∑ s ∈ Finset.range (n + 1), μ.real (bandCarrierDeficit B Car n s)
        ≤ ∑ _s ∈ Finset.range (n + 1), μ.real Dfilter := Finset.sum_le_sum h1
      _ = ((n : ℝ) + 1) * μ.real Dfilter := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc μ.real (G₀ ∩ stoppedWindow Q σ n ε)
      ≤ μ.real (⋃ s ∈ Finset.range (n + 1), ⋃ a, bandWindow Q B n ε s a) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ s ∈ Finset.range (n + 1), μ.real (⋃ a, bandWindow Q B n ε s a) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ Finset.range (n + 1),
          (2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
            μ.real (bandCarrierDeficit B Car n s)) := Finset.sum_le_sum fun s _ => hbs s
    _ = ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
          ∑ s ∈ Finset.range (n + 1), μ.real (bandCarrierDeficit B Car n s) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) + ((n : ℝ) + 1) * μ.real Dfilter := by
        refine add_le_add le_rfl hmono
    _ = 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
          ((n : ℝ) + 1) * μ.real Dfilter := by ring

/-- **Carrier-restricted count-free two-endpoint bound, single deficit set.**  When each band
refines the fibre of `σ` *everywhere* (`B a ⊆ {σ = a}`), the carrier deficit is contained in the
single set `{ω | ∃ m < 2 n, ω ∉ Car (σ ω + m)}` of carrier failures in the window after `σ`. -/
theorem measureReal_band_stoppedWindow_le_of_carrier_global [IsProbabilityMeasure μ]
    {Q : ℕ → Ω → ℝ} {σ : Ω → ℕ} {B Car : ℕ → Set Ω}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hCarm : ∀ t, MeasurableSet[ℱ t] (Car t))
    (hbdd : ∀ t ω, ω ∈ Car t → |Q (t + 1) ω - Q t ω| ≤ C)
    (hBm : ∀ a, MeasurableSet[ℱ a] (B a))
    (hBdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    {G₀ : Set Ω} (hG : G₀ ⊆ ⋃ a, B a) (hBσ : ∀ a, B a ⊆ {ω | σ ω = a})
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (G₀ ∩ stoppedWindow Q σ n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
        ((n : ℝ) + 1) * μ.real {ω | ∃ m < 2 * n, ω ∉ Car (σ ω + m)} := by
  refine measureReal_band_stoppedWindow_le_of_carrier hQm hQi hQ0 hC hCarm hbdd hBm hBdisj
    hG (fun a => Set.Subset.trans Set.inter_subset_right (hBσ a)) hn hε ?_
  intro s hs ω hω
  rw [Finset.mem_range] at hs
  rw [bandCarrierDeficit] at hω
  obtain ⟨a, ha, k, hk, hkC⟩ := Set.mem_iUnion.1 hω
  have hσa : σ ω = a := hBσ a ha
  have hidx : σ ω + (s + k) = a + s + k := by rw [hσa]; omega
  simp only [Set.mem_ofPred_eq]
  exact ⟨s + k, by omega, by rwa [hidx]⟩

/-! ### Clocks valued in `ℕ∞` with a null top fibre

This is the shape of `Swarming.Enl.maxClock` (`results/lean/areas/filtration/StoppedClock.lean`):
an `ℕ∞`-valued clock whose finite fibres `{τ = a}` are measurable in `ℱ a` and whose top fibre
`{τ = ⊤}` is null.  The `ℕ`-valued reading `τ.toNat` has a junk value on `⊤`; that is harmless
because the top fibre is null, and the band form needs no stopping-time property of the reading.
-/

/-- **Count-free stopped window bound for an `ℕ∞`-valued clock with measurable finite fibres and
null top fibre.** -/
theorem measureReal_stoppedWindow_le_of_enat [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {τ : Ω → ℕ∞}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hτ : ∀ a : ℕ, MeasurableSet[ℱ a] {ω | τ ω = (a : ℕ∞)})
    (hτtop : μ {ω | τ ω = ⊤} = 0)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedWindow Q (fun ω => (τ ω).toNat) n ε) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have hbound := measureReal_band_stoppedWindow_le (Q := Q) (σ := fun ω => (τ ω).toNat)
    (B := fun a => {ω | τ ω = (a : ℕ∞)}) hQm hQi hQ0 hC hbdd hτ
    (fun a b hab => by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      exact hab (Nat.cast_injective (h1.symm.trans h2)))
    (G := {ω | τ ω ≠ ⊤})
    (fun ω hω => by
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hω
      exact ⟨a, ha.symm⟩)
    (fun a => by
      rintro ω ⟨-, ha⟩
      simp only [Set.mem_ofPred_eq]
      rw [ha, ENat.toNat_natCast])
    hn hε
  have htopzero : μ.real {ω | τ ω = ⊤} = 0 := by
    rw [Measure.real_def, hτtop, ENNReal.toReal_zero]
  calc μ.real (stoppedWindow Q (fun ω => (τ ω).toNat) n ε)
      ≤ μ.real ({ω | τ ω ≠ ⊤} ∩ stoppedWindow Q (fun ω => (τ ω).toNat) n ε) +
          μ.real {ω | τ ω = ⊤} := by
        have hsub : stoppedWindow Q (fun ω => (τ ω).toNat) n ε ⊆
            ({ω | τ ω ≠ ⊤} ∩ stoppedWindow Q (fun ω => (τ ω).toNat) n ε) ∪ {ω | τ ω = ⊤} := by
          intro ω hω
          by_cases h : τ ω = ⊤
          · exact Or.inr h
          · exact Or.inl ⟨h, hω⟩
        refine le_trans (measureReal_mono hsub (measure_ne_top μ _)) (measureReal_union_le _ _)
    _ = μ.real ({ω | τ ω ≠ ⊤} ∩ stoppedWindow Q (fun ω => (τ ω).toNat) n ε) := by
        rw [htopzero, add_zero]
    _ ≤ 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := hbound

/-- **Count-free stopped one-start bound for an `ℕ∞`-valued clock with measurable finite fibres
and null top fibre.** -/
theorem measureReal_stoppedMax_le_of_enat [IsProbabilityMeasure μ] {Q : ℕ → Ω → ℝ}
    {τ : Ω → ℕ∞}
    (hQm : ∀ t, StronglyMeasurable[ℱ t] (Q t))
    (hQi : ∀ t, Integrable (Q t) μ)
    (hQ0 : ∀ t, μ[increments Q t | ℱ t] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C) (hbdd : ∀ t ω, |Q (t + 1) ω - Q t ω| ≤ C)
    (hτ : ∀ a : ℕ, MeasurableSet[ℱ a] {ω | τ ω = (a : ℕ∞)})
    (hτtop : μ {ω | τ ω = ⊤} = 0)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (stoppedMax Q (fun ω => (τ ω).toNat) n ε) ≤
      2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := by
  have hbound := measureReal_band_stoppedMax_le (Q := Q) (σ := fun ω => (τ ω).toNat)
    (B := fun a => {ω | τ ω = (a : ℕ∞)}) hQm hQi hQ0 hC hbdd hτ
    (fun a b hab => by
      rw [Set.disjoint_left]
      rintro ω h1 h2
      exact hab (Nat.cast_injective (h1.symm.trans h2)))
    (G := {ω | τ ω ≠ ⊤})
    (fun ω hω => by
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hω
      exact ⟨a, ha.symm⟩)
    (fun a => by
      rintro ω ⟨-, ha⟩
      simp only [Set.mem_ofPred_eq]
      rw [ha, ENat.toNat_natCast])
    hn hε
  have htopzero : μ.real {ω | τ ω = ⊤} = 0 := by
    rw [Measure.real_def, hτtop, ENNReal.toReal_zero]
  calc μ.real (stoppedMax Q (fun ω => (τ ω).toNat) n ε)
      ≤ μ.real ({ω | τ ω ≠ ⊤} ∩ stoppedMax Q (fun ω => (τ ω).toNat) n ε) +
          μ.real {ω | τ ω = ⊤} := by
        have hsub : stoppedMax Q (fun ω => (τ ω).toNat) n ε ⊆
            ({ω | τ ω ≠ ⊤} ∩ stoppedMax Q (fun ω => (τ ω).toNat) n ε) ∪ {ω | τ ω = ⊤} := by
          intro ω hω
          by_cases h : τ ω = ⊤
          · exact Or.inr h
          · exact Or.inl ⟨h, hω⟩
        refine le_trans (measureReal_mono hsub (measure_ne_top μ _)) (measureReal_union_le _ _)
    _ = μ.real ({ω | τ ω ≠ ⊤} ∩ stoppedMax Q (fun ω => (τ ω).toNat) n ε) := by
        rw [htopzero, add_zero]
    _ ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) := hbound

end StoppedWindow
