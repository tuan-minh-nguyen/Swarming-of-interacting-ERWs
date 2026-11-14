/-
# Finite-scale `(Rlower)` and the record-advance block clause from `(lococc)`

The paper (`attachments/improving-and-polishing-the-wcjf/main_1d.tex`) proves the first
block inequality `(time)` of Proposition `tight` through the fluid limit `(Rlower)`:

  `(3/4) u ≤ C (2 R(u) + 5)`,   hence   `R(u) ≥ 3u/(8C) - 3`,

which for `u = T` exceeds `B + 2` under `(BTchoice)`.  The published proof obtains this
only after passing to a subsequence (Arzelà–Ascoli).  This file proves the same step
**directly at finite `L`**, with no compactness, no limit and no probability.

The single analytic input is the paper's `(lococc)` occupation estimate, specialised to
the initial time `s = τ_r` of the record window (which is what the argument actually
consumes; the paper's statement over all `τ_r ≤ s ≤ t` implies this form).
-/
import Swarm.FluidBlock
import Swarm.HblkTwo

open Finset
open scoped BigOperators

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LocalFluid

open RecordDefect RecordoSupply
open MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## 1. The individual running maxima `M^i_n = max_{t ≤ n} X^i_t` -/

/-- `M^i_n`, the paper's individual running maximum.  (`RecordDefect.runMax` is the
*spatial* maximum `max_i X^i_n`, so the temporal one has to be added.) -/
noncomputable def runMaxI (X : ι → ℕ → ℤ) (i : ι) : ℕ → ℤ
  | 0 => X i 0
  | n + 1 => max (runMaxI X i n) (X i (n + 1))

theorem runMaxI_zero (X : ι → ℕ → ℤ) (i : ι) : runMaxI X i 0 = X i 0 := rfl

theorem runMaxI_succ (X : ι → ℕ → ℤ) (i : ι) (n : ℕ) :
    runMaxI X i (n + 1) = max (runMaxI X i n) (X i (n + 1)) := rfl

theorem le_runMaxI (X : ι → ℕ → ℤ) (i : ι) : ∀ n : ℕ, X i n ≤ runMaxI X i n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      show X i (n + 1) ≤ runMaxI X i (n + 1)
      rw [runMaxI_succ]
      exact le_max_right _ _

theorem runMaxI_mono (X : ι → ℕ → ℤ) (i : ι) : Monotone (runMaxI X i) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [runMaxI_succ]; exact le_trans ih (le_max_left _ _)

/-- The individual running maximum never exceeds the paper's `R_n` (FluidBlock's
running maximum in time of the spatial maximum). -/
theorem runMaxI_le_rho (X : ι → ℕ → ℤ) (i : ι) : ∀ n : ℕ, runMaxI X i n ≤ FluidBlock.rho X n := by
  intro n
  induction n with
  | zero =>
      rw [runMaxI_zero, FluidBlock.rho_zero]
      exact le_runMax (X := X) 0 i
  | succ n ih =>
      rw [runMaxI_succ, FluidBlock.rho_succ]
      exact max_le (le_trans ih (le_max_left _ _))
        (le_trans (le_runMax (X := X) (n + 1) i) (le_max_right _ _))

/-- Before the record time of level `r`, every individual running maximum is at most `r`. -/
theorem runMaxI_le_of_le_tau (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (i : ι) {r n : ℕ} (hn : n ≤ τ r) : runMaxI X i n ≤ (r : ℤ) :=
  le_trans (runMaxI_le_rho X i n) (FluidBlock.rho_le_of_le_tau hτ hn)

/-- At the record time of level `r` the individual running maximum is at most `r`. -/
theorem runMaxI_tau_le (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ) (i : ι) (r : ℕ) :
    runMaxI X i (τ r) ≤ (r : ℤ) :=
  runMaxI_le_of_le_tau X hτ i le_rfl

/-! ## 2. Position bounds at the record time, from `{d_r ≤ L}` -/

theorem runMin_tau (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (r : ℕ) :
    runMin X (τ r) = (r : ℤ) - defect X τ r := by
  rw [defect]; ring

/-- On `{d_r ≤ L}` every walker sits at least `L` below the record level at time `τ_r`. -/
theorem tau_position_lower (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {r L : ℕ}
    (hdr : defect X τ r ≤ (L : ℤ)) (i : ι) :
    (r : ℤ) - (L : ℤ) ≤ X i (τ r) := by
  have h1 : runMin X (τ r) ≤ X i (τ r) := runMin_le (X := X) (τ r) i
  have h2 : runMin X (τ r) = (r : ℤ) - defect X τ r := runMin_tau X r
  linarith

/-- On `{d_r ≤ L}` every walker's running maximum at time `τ_r` is at least `r - L`. -/
theorem tau_runMaxI_lower (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {r L : ℕ}
    (hdr : defect X τ r ≤ (L : ℤ)) (i : ι) :
    (r : ℤ) - (L : ℤ) ≤ runMaxI X i (τ r) :=
  le_trans (tau_position_lower X hdr i) (le_runMaxI X i (τ r))

/-! ## 3. The paper's `(lococc)` at the initial record time -/

/-- The `(lococc)` drift bracket `(M^i_n - M^i_s) + (M^i_s - X^i_s)`. -/
noncomputable def occTerm (X : ι → ℕ → ℤ) (i : ι) (s n : ℕ) : ℝ :=
  ((runMaxI X i n : ℤ) : ℝ) - ((runMaxI X i s : ℤ) : ℝ)
    + (((runMaxI X i s : ℤ) : ℝ) - ((X i s : ℤ) : ℝ))

/-- The `(lococc)` initial-gap bracket `(M^i_s - M^j_s)_+`. -/
noncomputable def occGap (X : ι → ℕ → ℤ) (i j : ι) (s : ℕ) : ℝ :=
  max 0 (((runMaxI X i s : ℤ) : ℝ) - ((runMaxI X j s : ℤ) : ℝ))

/-- **The `(lococc)` input.**  This is the paper's estimate specialised to `s = τ_r`
(its `Σ_u 1{X^i_u ≤ M^j_u}` over `[τ_r, n)`), with the paper's structure
`C(·) + (n-τ_r)/8 + C_T L^{3/4}`.  It is a deterministic inequality along one path;
`C` is the paper's `T`-free coefficient and `C_T` its `T`-dependent one. -/
def LocOcc (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (C CT : ℝ) (T L r : ℕ) : Prop :=
  ∀ (i j : ι), i ≠ j → ∀ n : ℕ, τ r ≤ n → n ≤ τ r + T * L →
    (∑ u ∈ Finset.Ico (τ r) n, (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0))
      ≤ C * (occTerm X i (τ r) n + occGap X i j (τ r))
        + ((n - τ r : ℕ) : ℝ) / 8 + CT * (L : ℝ) ^ (3 / 4 : ℝ)

/-! ## 4. The pair-sum: for each `u` at least one of the two indicators fires -/

theorem one_le_pair_indicator (X : ι → ℕ → ℤ) (i j : ι) (u : ℕ) :
    (1 : ℝ) ≤ (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0)
      + (if X j u ≤ runMaxI X i u then (1 : ℝ) else 0) := by
  by_cases h1 : X i u ≤ runMaxI X j u
  · have h0 : (0 : ℝ) ≤ (if X j u ≤ runMaxI X i u then (1 : ℝ) else 0) := by
      split <;> norm_num
    rw [if_pos h1]; linarith
  · have h1' : runMaxI X j u < X i u := not_le.mp h1
    have h2 : X j u ≤ runMaxI X i u := by
      have a1 : X j u ≤ runMaxI X j u := le_runMaxI X j u
      have a2 : X i u ≤ runMaxI X i u := le_runMaxI X i u
      linarith
    rw [if_neg h1, if_pos h2]; norm_num

/-- Summing the two directions of one pair gives back the whole window length. -/
theorem pair_occupation_lower (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (i j : ι) {r n : ℕ}
    (hn : τ r ≤ n) :
    ((n - τ r : ℕ) : ℝ) ≤
      (∑ u ∈ Finset.Ico (τ r) n, (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0))
      + (∑ u ∈ Finset.Ico (τ r) n, (if X j u ≤ runMaxI X i u then (1 : ℝ) else 0)) := by
  have h := Finset.sum_le_sum (s := Finset.Ico (τ r) n)
    (f := fun u => (1 : ℝ))
    (g := fun u => (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0)
      + (if X j u ≤ runMaxI X i u then (1 : ℝ) else 0))
    (fun u _ => one_le_pair_indicator X i j u)
  rw [Finset.sum_add_distrib] at h
  have hone : (∑ _u ∈ Finset.Ico (τ r) n, (1 : ℝ)) = ((n - τ r : ℕ) : ℝ) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  rwa [hone] at h

/-! ## 5. Finite-scale `(Rlower)` -/

/-- The two `(lococc)` brackets of a pair, together with the two position bounds, are at
most `2 R + 6 L` where `R = ρ(τ_r + a) - r`. -/
theorem bracket_pair_bound (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ) {r L a : ℕ}
    (hdr : defect X τ r ≤ (L : ℤ)) (i j : ι) :
    (occTerm X i (τ r) (τ r + a) + occGap X i j (τ r))
        + (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r))
      ≤ 2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ) := by
  have hUi : ((runMaxI X i (τ r) : ℤ) : ℝ) ≤ (r : ℝ) := by
    have := runMaxI_tau_le X hτ i r; exact_mod_cast this
  have hUj : ((runMaxI X j (τ r) : ℤ) : ℝ) ≤ (r : ℝ) := by
    have := runMaxI_tau_le X hτ j r; exact_mod_cast this
  have hLi : (r : ℝ) - (L : ℝ) ≤ ((runMaxI X i (τ r) : ℤ) : ℝ) := by
    have := tau_runMaxI_lower X hdr i; exact_mod_cast this
  have hLj : (r : ℝ) - (L : ℝ) ≤ ((runMaxI X j (τ r) : ℤ) : ℝ) := by
    have := tau_runMaxI_lower X hdr j; exact_mod_cast this
  have hXi : (r : ℝ) - (L : ℝ) ≤ ((X i (τ r) : ℤ) : ℝ) := by
    have := tau_position_lower X hdr i; exact_mod_cast this
  have hXj : (r : ℝ) - (L : ℝ) ≤ ((X j (τ r) : ℤ) : ℝ) := by
    have := tau_position_lower X hdr j; exact_mod_cast this
  have hR : (r : ℝ) ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) := by
    have := FluidBlock.le_rho_of_tau_le hτ (Nat.le_add_right (τ r) a)
    exact_mod_cast this
  have hNi : ((runMaxI X i (τ r + a) : ℤ) : ℝ) ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) := by
    have := runMaxI_le_rho X i (τ r + a); exact_mod_cast this
  have hNj : ((runMaxI X j (τ r + a) : ℤ) : ℝ) ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) := by
    have := runMaxI_le_rho X j (τ r + a); exact_mod_cast this
  have hmax1 : occGap X i j (τ r) ≤ (L : ℝ) := by
    refine max_le ?_ ?_
    · linarith
    · linarith
  have hmax2 : occGap X j i (τ r) ≤ (L : ℝ) := by
    refine max_le ?_ ?_
    · linarith
    · linarith
  simp only [occTerm]
  linarith

/-- **Finite-scale `(Rlower)`.**  On `{d_r ≤ L}` and on `(lococc)`, the record level held at
time `τ_r + a` has advanced by at least `(3a)/(8C) - 3L - (C_T/C) L^{3/4}`.  No limit,
no subsequence, no probability. -/
theorem rho_advance (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ) {C CT : ℝ}
    (hC : 0 < C) {T L r a : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) {i j : ι} (hij : i ≠ j) (ha : a ≤ T * L) :
    (3 : ℝ) / 8 * ((a : ℝ) / C) - 3 * (L : ℝ) - (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ)
      ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ) := by
  have hs : τ r ≤ τ r + a := Nat.le_add_right _ _
  have ha' : τ r + a ≤ τ r + T * L := Nat.add_le_add_left ha (τ r)
  have h1 := hocc i j hij (τ r + a) hs ha'
  have h2 := hocc j i (Ne.symm hij) (τ r + a) hs ha'
  have h12 := pair_occupation_lower (X := X) (τ := τ) i j hs
  have hbr := bracket_pair_bound X (a := a) hτ hdr i j
  have hcast : ((τ r + a - τ r : ℕ) : ℝ) = (a : ℝ) := by
    rw [Nat.add_sub_cancel_left]
  rw [hcast] at h1 h2 h12
  -- the summed occupation inequality
  have hP : occTerm X i (τ r) (τ r + a) + occGap X i j (τ r)
      + (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r))
      ≤ 2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ) := hbr
  have hsum : (a : ℝ) ≤ C * (occTerm X i (τ r) (τ r + a) + occGap X i j (τ r)
      + (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r)))
      + (a : ℝ) / 4 + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    set P : ℝ := occTerm X i (τ r) (τ r + a) + occGap X i j (τ r)
      + (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r)) with hPdef
    have e1 : C * (occTerm X i (τ r) (τ r + a) + occGap X i j (τ r))
        + C * (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r)) = C * P := by
      rw [hPdef]; ring
    linarith [h1, h2, h12, e1]
  have hmul : C * (occTerm X i (τ r) (τ r + a) + occGap X i j (τ r)
      + (occTerm X j (τ r) (τ r + a) + occGap X j i (τ r)))
      ≤ C * (2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left hP hC.le
  have hdiva : (3 : ℝ) / 4 * (a : ℝ)
      ≤ C * (2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ))
        + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by linarith [hsum, hmul]
  -- divide by `C` and halve
  have hdiv : (3 : ℝ) / 4 * (a : ℝ) / C
      ≤ (2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ))
        + 2 * (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [div_le_iff₀ hC]
    have e2 : ((2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ))
        + 2 * (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ)) * C
        = C * (2 * (((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) - (r : ℝ)) + 6 * (L : ℝ))
          + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      field_simp
    rw [e2]
    exact hdiva
  have e3 : (3 : ℝ) / 4 * (a : ℝ) / C = 2 * ((3 : ℝ) / 8 * ((a : ℝ) / C)) := by
    rw [show (2 : ℝ) * ((3 : ℝ) / 8 * ((a : ℝ) / C)) = (3 : ℝ) / 4 * ((a : ℝ) / C) by ring,
      mul_div_assoc]
  linarith [hdiv, e3]

/-! ## 6. Integer consequences of `rho_advance` -/

/-- Dividing `rho_advance` by `L`: the coefficient is `3T/(8C)`. -/
theorem rpow_quarter_mul {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) ^ (1 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) = (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  rw [← Real.rpow_add hLpos]
  have h : (1 : ℝ) / 4 + 3 / 4 = 1 := by norm_num
  rw [h, Real.rpow_one]

/-- The transparent form of the numerical threshold: `d L^{1/4} ≥ C_T/C` implies the
`L^{3/4}`-form `d L ≥ (C_T/C) L^{3/4}`.  Hence `d > 0` makes the threshold hold for all
large `L`, with the paper's `L^{-1/4}` loss. -/
theorem threshold_of_quarter {d cE : ℝ} {L : ℕ} (hL : 1 ≤ L)
    (h : d * (L : ℝ) ^ (1 / 4 : ℝ) ≥ cE) :
    d * (L : ℝ) ≥ cE * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hEpos : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := (Real.rpow_pos_of_pos hLpos _).le
  have hmul := mul_le_mul_of_nonneg_right h hEpos
  rwa [mul_assoc, rpow_quarter_mul hL] at hmul

/-- The level `r + L` lies strictly below `r + 2L`, as integers. -/
theorem level_add_lt (r L : ℕ) (hL : 1 ≤ L) :
    (r : ℤ) + (L : ℤ) < ((r + 2 * L : ℕ) : ℤ) := by
  have h : r + L < r + 2 * L := by omega
  exact_mod_cast h

/-- **The record advance (the paper's `(time)` clause from `(lococc)`).** -/
theorem tau_advance_of_locOcc (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0)
    {C CT : ℝ} (hC : 0 < C) {T B L r : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : (3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ)) * (L : ℝ) ^ (1 / 4 : ℝ) ≥ CT / C) :
    τ (r + B * L) ≤ τ r + T * L := by
  have hnum' : (3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ)) * (L : ℝ)
      ≥ (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ) :=
    threshold_of_quarter hL hnum
  have hra := rho_advance X (a := T * L) hτ hC hocc hdr hij le_rfl
  have hid : (3 : ℝ) / 8 * (((T * L : ℕ) : ℝ) / C)
      = (3 * (T : ℝ) / (8 * C)) * (L : ℝ) := by
    push_cast
    field_simp
  rw [hid] at hra
  have hBL : ((B * L : ℕ) : ℝ) = (B : ℝ) * (L : ℝ) := by push_cast; ring
  have hE := hnum'
  have hR : ((B * L : ℕ) : ℝ) ≤ ((FluidBlock.rho X (τ r + T * L) : ℤ) : ℝ) - (r : ℝ) := by
    rw [hBL]
    nlinarith [hra, hE]
  have hR' : (B : ℝ) * (L : ℝ) ≤ ((FluidBlock.rho X (τ r + T * L) : ℤ) : ℝ) - (r : ℝ) := by
    rw [← hBL]; exact hR
  have hZ : ((B * L : ℕ) : ℤ) ≤ (FluidBlock.rho X (τ r + T * L) : ℤ) - (r : ℤ) := by
    have hcast : (((B * L : ℕ) : ℤ) : ℝ)
        ≤ (((FluidBlock.rho X (τ r + T * L) : ℤ) - (r : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith [hR']
    exact_mod_cast hcast
  have hrho : ((r + B * L : ℕ) : ℤ) ≤ FluidBlock.rho X (τ r + T * L) := by
    have h1 : ((r + B * L : ℕ) : ℤ) = (r : ℤ) + ((B * L : ℕ) : ℤ) := by push_cast; ring
    rw [h1]
    linarith [hZ]
  exact (FluidBlock.tau_le_iff_rho_le hτ hne h0).mpr hrho

/-! ## 7. The `(fluidmax)` lag bound: no walker stays `L` below the record -/

/-- If the held record level reaches `c` by time `n`, then some walker's individual
running maximum at time `n` is at least `c`. -/
theorem exists_runMaxI_of_le_rho (X : ι → ℕ → ℤ) {c n : ℕ}
    (h : (c : ℤ) ≤ FluidBlock.rho X n) : ∃ j, (c : ℤ) ≤ runMaxI X j n := by
  obtain ⟨k, hk, hkr⟩ := FluidBlock.exists_le_runMax_of_le_rho X h
  obtain ⟨j, -, hval⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun i => X i k)
  refine ⟨j, le_trans ?_ (runMaxI_mono X j hk)⟩
  calc (c : ℤ) ≤ runMax X k := hkr
    _ = X j k := hval
    _ ≤ runMaxI X j k := le_runMaxI X j k

/-- **The finite-scale first half of `(fluidmax)`.**  On `(lococc)` and `{d_r ≤ L}`, if the
record has advanced by `2L` at time `τ_r + a`, then by time `τ_r + b` **every** walker's
running maximum exceeds the level `r + L`: a walker lagging a full `L` behind the record
would occupy `40CL` steps inside the leader's running maximum, which `(lococc)` bounds by
`12CL`.  This is the paper's `m_i(u) = x_i(u)` for `u ≥ 64C` at `ε = 1`, without limits. -/
theorem runMaxI_gt_of_locOcc (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {C CT : ℝ} (hC : 0 < C) {T L r : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀) {a b : ℕ} (hab : a ≤ b) (haT : a ≤ T * L)
    (hbT : b ≤ T * L)
    (hlead : 2 * (L : ℝ) ≤ (3 : ℝ) / 8 * ((a : ℝ) / C) - 3 * (L : ℝ)
      - (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ))
    (hcount : 4 * C * (L : ℝ) + (b : ℝ) / 8 + CT * (L : ℝ) ^ (3 / 4 : ℝ)
      < ((b - a : ℕ) : ℝ)) :
    ∀ i : ι, (r : ℤ) + (L : ℤ) < runMaxI X i (τ r + b) := by
  intro i
  -- the leader
  have hra := rho_advance X (a := a) hτ hC hocc hdr hij haT
  have hlead' : ((r : ℝ) + 2 * (L : ℝ))
      ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) := by
    linarith [hra, hlead]
  have hZ : ((r + 2 * L : ℕ) : ℤ) ≤ FluidBlock.rho X (τ r + a) := by
    have hcast : (((r + 2 * L : ℕ) : ℤ) : ℝ) ≤ ((FluidBlock.rho X (τ r + a) : ℤ) : ℝ) := by
      push_cast
      linarith [hlead']
    exact_mod_cast hcast
  obtain ⟨j, hj⟩ := exists_runMaxI_of_le_rho X (n := τ r + a) hZ
  by_contra hcon
  simp only [not_lt] at hcon
  -- the lagging walker is a different walker
  by_cases hEq : i = j
  · subst hEq
    have hmono : runMaxI X i (τ r + a) ≤ runMaxI X i (τ r + b) :=
      runMaxI_mono X i (Nat.add_le_add_left hab (τ r))
    have hstep := level_add_lt r L hL
    linarith [hmono, hj, hcon, hstep]
  · -- every step of `[τ_r + a, τ_r + b)` is counted
    have hoccb := hocc i j hEq (τ r + b) (Nat.le_add_right _ _)
      (Nat.add_le_add_left hbT (τ r))
    -- the walker stays at most `r + L`
    have hstep_le : ∀ u : ℕ, u ≤ τ r + b → X i u ≤ (r : ℤ) + (L : ℤ) := by
      intro u hu
      exact le_trans (le_runMaxI X i u)
        (le_trans (runMaxI_mono X i hu) hcon)
    -- the leader's running maximum is at least `r + 2L` from time `τ_r + a` on
    have hlead_le : ∀ u : ℕ, τ r + a ≤ u → ((r + 2 * L : ℕ) : ℤ) ≤ runMaxI X j u := by
      intro u hu
      exact le_trans hj (runMaxI_mono X j hu)
    have hind : ∀ u ∈ Finset.Ico (τ r + a) (τ r + b),
        (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0) = 1 := by
      intro u hu
      rw [Finset.mem_Ico] at hu
      refine if_pos ?_
      have h1 := hstep_le u (le_of_lt hu.2)
      have h2 := hlead_le u hu.1
      have h3 := level_add_lt r L hL
      linarith
    -- the count
    have hcard : (∑ _u ∈ Finset.Ico (τ r + a) (τ r + b), (1 : ℝ)) = ((b - a : ℕ) : ℝ) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      have h : τ r + b - (τ r + a) = b - a := by omega
      rw [h]
    have hsecond : ((b - a : ℕ) : ℝ)
        ≤ ∑ u ∈ Finset.Ico (τ r + a) (τ r + b),
            (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0) := by
      rw [← hcard]
      exact Finset.sum_le_sum (fun u hu => le_of_eq (hind u hu).symm)
    have hconsec := Finset.sum_Ico_consecutive
      (fun u => (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0))
      (show τ r ≤ τ r + a by omega) (show τ r + a ≤ τ r + b by omega)
    have hnonneg : (0 : ℝ) ≤ ∑ u ∈ Finset.Ico (τ r) (τ r + a),
        (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0) :=
      Finset.sum_nonneg (fun u _ => by split <;> norm_num)
    have hcount_lower : ((b - a : ℕ) : ℝ)
        ≤ ∑ u ∈ Finset.Ico (τ r) (τ r + b),
            (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0) := by
      linarith [hsecond, hconsec, hnonneg]
    -- the `(lococc)` upper bound on the same sum
    have hUtau : ((runMaxI X i (τ r) : ℤ) : ℝ) ≤ (r : ℝ) := by
      have := runMaxI_tau_le X hτ i r; exact_mod_cast this
    have hLtau : (r : ℝ) - (L : ℝ) ≤ ((runMaxI X i (τ r) : ℤ) : ℝ) := by
      have := tau_runMaxI_lower X hdr i; exact_mod_cast this
    have hXtau : (r : ℝ) - (L : ℝ) ≤ ((X i (τ r) : ℤ) : ℝ) := by
      have := tau_position_lower X hdr i; exact_mod_cast this
    have hJtau : (r : ℝ) - (L : ℝ) ≤ ((runMaxI X j (τ r) : ℤ) : ℝ) := by
      have := tau_runMaxI_lower X hdr j; exact_mod_cast this
    have hUb : ((runMaxI X i (τ r + b) : ℤ) : ℝ) ≤ (r : ℝ) + (L : ℝ) := by
      have := hcon; exact_mod_cast this
    have hgap : occGap X i j (τ r) ≤ (L : ℝ) := by
      refine max_le ?_ ?_
      · linarith
      · linarith
    have hterm : occTerm X i (τ r) (τ r + b) ≤ 3 * (L : ℝ) := by
      simp only [occTerm]
      linarith
    have hbrk : occTerm X i (τ r) (τ r + b) + occGap X i j (τ r) ≤ 4 * (L : ℝ) := by
      linarith
    have hupper : (∑ u ∈ Finset.Ico (τ r) (τ r + b),
          (if X i u ≤ runMaxI X j u then (1 : ℝ) else 0))
        ≤ 4 * C * (L : ℝ) + (b : ℝ) / 8 + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hmul : C * (occTerm X i (τ r) (τ r + b) + occGap X i j (τ r))
          ≤ C * (4 * (L : ℝ)) := mul_le_mul_of_nonneg_left hbrk hC.le
      have hcastb : ((τ r + b - τ r : ℕ) : ℝ) = (b : ℝ) := by
        rw [Nat.add_sub_cancel_left]
      rw [hcastb] at hoccb
      nlinarith [hoccb, hmul]
    linarith [hcount_lower, hupper, hcount]

/-! ## 8. Measure-level reduction for the advance clause -/

/-- **The advance clause needs only `(lococc)`.**  Since `HblkTwo.BadTime` already contains
`d_r ≤ L`, the complement of `(lococc)` dominates the whole bad event. -/
theorem measure_badTime_le_locOcc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hτ : ∀ ω, IsRecord (X ω) (τ ω))
    (hne : ∀ ω (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (h0 : ∀ ω (i : ι), X ω i 0 = 0)
    {C CT : ℝ} (hC : 0 < C) {T B L r : ℕ} (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : (3 * (T : ℝ) / (8 * C) - 3 - (B : ℝ)) * (L : ℝ) ^ (1 / 4 : ℝ) ≥ CT / C) :
    μ {ω | HblkTwo.BadTime B T ((fun u => (defect (X ω) (τ ω) u).toNat), τ ω) r L}
      ≤ μ {ω | ¬ LocOcc (X ω) (τ ω) C CT T L r} := by
  apply measure_mono
  intro ω hbad hocc
  obtain ⟨hd, hadv⟩ := hbad
  have hdr : defect (X ω) (τ ω) r ≤ (L : ℤ) := by
    have h2 : ((defect (X ω) (τ ω) r).toNat : ℤ) = defect (X ω) (τ ω) r :=
      Int.toNat_of_nonneg (defect_nonneg (hτ ω) r)
    have h1 : ((defect (X ω) (τ ω) r).toNat : ℤ) ≤ (L : ℤ) := by exact_mod_cast hd
    rw [h2] at h1
    exact h1
  have ha := tau_advance_of_locOcc (X ω) (hτ ω) (hne ω) (h0 ω) hC hocc hdr hL hij hnum
  exact absurd ha (not_le.mpr hadv)

end LocalFluid

/-! ## Axiom audit (source order) -/


