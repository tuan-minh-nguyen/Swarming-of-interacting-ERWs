/-
# The halving clause from a coalescence time in the sharp subwindow `[τ_r+64⌈C⌉L, τ_{r+BL}]`

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, the proof of Proposition
`tight` between displays `(fluidmax)` and `(block)`.  The source obtains the second block
inequality `d_{r+BL} ≤ L/2` only after Arzelà–Ascoli, through `(coincide)` and `(meet)`; the
finite-`L` version of that step is the *existence of one coalescence time*.  The public
`Swarm/HalvingResidual.lean` package states the residual as

  `GoodHalf`: carrier `{d_r ≤ L}` + a local field + **one** `s ∈ [τ_r, τ_{r+BL}]` with
  `spread(s) ≤ εL` **and a lag bound on all of `[s, τ_r+TL]`**.

The lag bound there is a *hypothesis*.  It is however not available on the whole record window:
`LagFromMart.lag_le_window` gives only `η = L + ⌈C_T L^{3/4}⌉` (the `+L` is genuine, because at
`n = τ_r` a walker can be a full `d_r ≤ L` below its historical maximum), while
`LagFromMart.lag_le_sub` gives the sharp `η = ⌈C_T L^{3/4}⌉` **only on the subwindow
`[τ_r + 64⌈C⌉L, τ_r+TL]`**.

This file removes the lag hypothesis from the good event altogether:

* `LocalClauses` — the clauses of Proposition `local` that the gluing actually consumes
  (`(loccoord)`, `(locmove)`, potential monotonicity/unit increment, `(lococc)`), with the lag
  clause *absent*; `LocalClauses.toField` rebuilds `Glue.LocalField` from `(locmart)` by
  `LagFromMart.localField_of_mart`;
* `Wst_le_of_sep_lag`, `join_gap_of_top_lag`, `spread_univ_le_lag`,
  `halving_input_of_window_lag`, `halving_of_coalesce_lag` — the public deterministic join
  chain of `JoinSub.lean`, re-run with the lag allowance `η` **decoupled** from the local
  field's parameter `ηF`, so that the field need only be built with the coarse `L + η`;
* `tau_advance_lower`, `tau_advance_lower_mul`, `sharp_entry_le_tau` — the nearest-neighbour
  lower bound on the record clock (`τ_y ≥ τ_x + (y-x)`), which places the candidate
  coalescence time `s = τ_{r+BL}` inside the sharp subwindow as soon as `64⌈C⌉ ≤ B`;
* `halving_of_coalesce_sharp` — the halving input `2 d_{r+BL} ≤ L` from a coalescence time
  `s ∈ [τ_r+64⌈C⌉L, τ_{r+BL}]` with `spread(s) ≤ εL`, with the lag bound on `[s, τ_r+TL]`
  **derived** from `(locmart)`+`(lococc)` by `LagFromMart.lag_le_sub`;
* `EndGood` — the literal good event: carrier, the Proposition-`local` clauses, `(locmart)`,
  the explicit numerical thresholds and one coalescence time in the sharp subwindow.  It
  contains no lag bound, no `∃ H`-level lag, no stationarity, no invariance, no start law and
  no `dT` bound;
* `not_badHalf_of_endGood`, `measure_badHalf_le_endGood_ae`,
  `halfClauseAt_of_endGood` — `¬BadHalf` and the literal `SourceTightAvail.HalfClauseAt`
  from a profile bound on `BadTime ∪ (EndGood)ᶜ` on the actual array;
* `sharp_window_forces_T` — the numerical premise `64⌈C⌉ ≤ T` is *forced* by the sharp good
  event together with `¬BadTime`, so it is not silently dropped;
* `not_threshold_of_allowance_ge_L` — the obstruction: an allowance `η ≥ L` (which is what
  `lag_le_window` supplies on the whole window) is incompatible with the halving thresholds
  `(1+2C)^N(1+N(4C+4))(ε₀+ε₁+ε₂) ≤ 1/4`, since they force `ε₁ ≤ 1/4` while `η ≥ L` forces
  `ε₁ ≥ 1`.  So the whole-window form of the lag hypothesis is not merely inconvenient: it
  cannot be fed the (locmart)-derived allowance at all, and the coalescence time has to be
  sought in the sharp subwindow.

Scope.  Everything below is deterministic except for the two measure-theoretic set inclusions
at the end, which are the same `measure_mono` argument as the public
`HalvingResidual.measure_badHalf_le`.  What is *not* proved here is the remaining literal
stochastic input: a profile bound for `{d_{r+BL} > εL}` (equivalently, for the complement of
the coalescence event) on the actual array `Swarming.Uniform.arrayMeasure N`.  That is the
source's `d_{r+BL}/L → 0`, obtained there only after passing to a subsequence; this file does
not assume, fake or shortcut it, and no claim about `MainClaim` is made.
-/
import Swarm.JoinSub
import Swarm.HalvingResidual
import Swarm.HalvingClause

open Finset MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators ENNReal

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The record clock advances at least one level per step

The paper uses this without comment ("we obtain the lower bound from the nearest-neighbour
property", proof of `tight`).  It is what makes `s = τ_{r+BL}` a legitimate coalescence time in
the sharp subwindow. -/

/-- One step changes the spatial maximum by at most one. -/
theorem runMax_succ_le {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (n : ℕ) :
    runMax X (n + 1) ≤ runMax X n + 1 := by
  have h : ∀ i : ι, X i (n + 1) ≤ runMax X n + 1 := by
    intro i
    have h1 : X i (n + 1) - X i n ≤ 1 := (abs_le.mp (le_of_eq (hne i n))).2
    have h2 := RecordDefect.le_runMax (X := X) n i
    linarith
  simp only [RecordDefect.runMax]
  exact Finset.sup'_le _ _ (fun i _ => h i)

/-- The spatial maximum grows at most linearly in time. -/
theorem runMax_le_add {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (n : ℕ) :
    runMax X n ≤ runMax X 0 + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := runMax_succ_le hne n
      push_cast
      linarith

/-- The running record level grows at most linearly in time. -/
theorem rho_le_add {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (n : ℕ) :
    FluidBlock.rho X n ≤ FluidBlock.rho X 0 + (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [FluidBlock.rho_succ, max_le_iff]
      constructor
      · push_cast
        linarith
      · have h1 := runMax_le_add hne (n + 1)
        have h2 : runMax X 0 ≤ FluidBlock.rho X 0 := le_of_eq (FluidBlock.rho_zero X).symm
        push_cast at h1 ⊢
        linarith

/-- The running record level grows at most one per step. -/
theorem rho_le_add_of_le {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (m : ℕ) :
    ∀ d : ℕ, FluidBlock.rho X (m + d) ≤ FluidBlock.rho X m + (d : ℤ) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep : m + (d + 1) = (m + d) + 1 := Nat.add_succ m d
      rw [hstep, FluidBlock.rho_succ, max_le_iff]
      constructor
      · push_cast
        linarith
      · have h1 : runMax X (m + d + 1) ≤ runMax X (m + d) + 1 := runMax_succ_le hne (m + d)
        have h2 : runMax X (m + d) ≤ FluidBlock.rho X (m + d) :=
          FluidBlock.le_rho X (le_refl (m + d))
        push_cast at h1 ⊢
        linarith

/-- **The nearest-neighbour lower bound on the record clock**: to raise the record by `y - x`
levels takes at least `y - x` steps. -/
theorem tau_advance_lower {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {x y : ℕ} (hxy : x ≤ y) :
    τ x + (y - x) ≤ τ y := by
  have hx : FluidBlock.rho X (τ x) = (x : ℤ) := FluidBlock.rho_tau hτ x
  have hy : FluidBlock.rho X (τ y) = (y : ℤ) := FluidBlock.rho_tau hτ y
  have ht : τ x ≤ τ y := tau_mono hτ hxy
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
  have h3 : FluidBlock.rho X (τ x + d) ≤ FluidBlock.rho X (τ x) + (d : ℤ) :=
    rho_le_add_of_le hne (τ x) d
  rw [← hd, hy, hx] at h3
  have h3' : y ≤ x + d := by
    have h4 : ((y : ℤ)) ≤ ((x + d : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h4
  omega

/-- The `B L`-level lower bound on the elapsed record time: `τ_{r+BL} ≥ τ_r + BL`. -/
theorem tau_advance_lower_mul {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (B L r : ℕ) :
    τ r + B * L ≤ τ (r + B * L) := by
  have h := tau_advance_lower hτ hne (x := r) (y := r + B * L) (Nat.le_add_right r (B * L))
  rwa [Nat.add_sub_cancel_left] at h

/-- The endpoint `τ_{r+BL}` lies in the sharp subwindow `[τ_r + 64⌈C⌉L, τ_r + TL]` as soon as
`64⌈C⌉ ≤ B`, with no condition on `T` yet. -/
theorem sharp_entry_le_tau {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {B L r : ℕ} {C : ℝ}
    (hB : 64 * Nat.ceil C ≤ B) :
    τ r + 64 * Nat.ceil C * L ≤ τ (r + B * L) := by
  have h1 : 64 * Nat.ceil C * L ≤ B * L := Nat.mul_le_mul_right L hB
  have h2 := tau_advance_lower_mul (X := X) hτ hne B L r
  omega

/-! ## 2. The Proposition-`local` clauses without the lag clause -/

/-- The clauses of Proposition `local` that the finite-`L` gluing consumes: the potential
monotonicity/unit-increment facts, `(loccoord)`, `(locmove)` (with the source's half-open time
set) and `(lococc)`.  The lag clause (second half of `(fluidmax)`) is deliberately **absent**:
it is derived from `(locmart)` below, on the subwindow where it is sharp. -/
structure LocalClauses (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ)
    (C CT : ℝ) (T L r : ℕ) : Prop where
  /-- The potential is nondecreasing in the spatial variable. -/
  hmono : ∀ (A : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → H A n x ≤ H A n y
  /-- The potential grows at least as fast as the identity. -/
  hunit : ∀ (A : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H A n y - H A n x
  /-- The paper's `(loccoord)`. -/
  hcoord : ∀ (A : Finset ι) (n : ℕ), A.Nonempty → A ≠ Finset.univ → τ r ≤ n → n ≤ τ r + T * L →
    ∀ a0 b0 : ℤ, (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 → b0 ≤ sMaxM X A n →
    ((H A n b0 - H A n a0 : ℤ) : ℝ) ≤ C * ((b0 - a0 : ℤ) : ℝ) + CT * (L : ℝ) ^ (3 / 4 : ℝ)
  /-- The paper's `(locmove)`, with `(sep)` required on the half-open set `[s,t)` only. -/
  wmove : ∀ (A : Finset ι) (s t : ℕ), A.Nonempty → A ≠ Finset.univ → τ r ≤ s → s ≤ t →
    t ≤ τ r + T * L → (∀ u : ℕ, s ≤ u → u < t → Sep X A (Finset.univ \ A) u) →
    Wst H X A (Finset.univ \ A) t - Wst H X A (Finset.univ \ A) s
      ≤ C * (((sMaxM X A s : ℤ) : ℝ) - ((sMin X A s : ℤ) : ℝ)) - ((t - s : ℕ) : ℝ) / C
        + CT * (L : ℝ) ^ (3 / 4 : ℝ)
  /-- The paper's `(lococc)` at the initial record time. -/
  occ : LocOcc X τ C CT T L r

/-- A `LocalField` **with its lag clause derived** from `(locmart)`: the field is built at the
coarse allowance `L + η` that `LagFromMart.lag_le_window` supports on the whole window.  The
sharp `η` is used separately, at the individual times where `lag_le_sub` applies. -/
theorem LocalClauses.toField {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {C CT μ : ℝ} {T L r : ℕ} (h : LocalClauses X τ H C CT T L r)
    (hτ : IsRecord X τ) (hM : MartClause X τ A μ CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) {η : ℕ} (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ)) :
    LocalField X τ H C CT T L r (L + η) :=
  localField_of_mart X h.hmono h.hunit h.hcoord h.wmove h.occ hτ hM hdr hη

/-- The paper's `Wst_le_of_sep` comparison, with the lag allowance at the single time `n`
supplied separately from the local field's own parameter.  (The public
`Glue.Wst_le_of_sep` reads the lag off `LocalField.lag`, which is only sharp on the subwindow;
here the caller supplies `hlagJ` from `LagFromMart.lag_le_sub` at the time it needs.) -/
theorem Wst_le_of_sep_lag {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {C CT : ℝ} {T L r ηF : ℕ} (hLF : LocalField X τ H C CT T L r ηF) (hC : 0 ≤ C)
    {I J : Finset ι} {n : ℕ} {η : ℕ}
    (hsep : Sep X I J n) (hI' : I ≠ Finset.univ) (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J n)
    (hlagJ : ∀ j ∈ J, runMaxI X j n - X j n ≤ (η : ℤ)) :
    Wst H X I J n ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ)
      + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H I n (X j n)) : ℤ) = H I n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hLF.hmono I n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H I n (X j n)) hj0
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      ≤ ((H I n (sMax X I n) : ℤ) : ℝ) := by
    rw [div_le_iff₀ hcard]
    have hb : ∀ i ∈ I, H I n (X i n) ≤ H I n (sMax X I n) := by
      intro i hi
      exact hLF.hmono I n (le_sMax hI hi)
    calc (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ))
        ≤ ∑ _i ∈ I, ((H I n (sMax X I n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
      _ = ((H I n (sMax X I n) : ℤ) : ℝ) * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb0 : sMax X I n ≤ sMaxM X I n :=
    sMax_le hI (fun i hi => le_trans (le_runMaxI X i n) (le_sMaxM hI hi))
  have hle0 : sMax X J n ≤ sMax X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    have hle3 : sMin X I n ≤ sMax X I n := sMin_le_sMaxX hI
    linarith
  have hcoord := hLF.hcoord I n hI hI' h1 h2 (sMax X J n) (sMax X I n) hlo hle0 hb0
  have hcast1 : (((sMax X I n - sMax X J n : ℤ)) : ℝ)
      = ((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ)
        + (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) := by
    unfold spreadS
    push_cast
    ring
  have hlagJ' : (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) ≤ (η : ℝ) := by
    have h := sMaxM_sub_sMax_le hJ hlagJ
    exact_mod_cast h
  have hcoord' : ((H I n (sMax X I n) - H I n (sMax X J n) : ℤ) : ℝ)
      ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ) + (η : ℝ))
        + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hcast1] at hcoord
    have hmul : C * (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ))
        ≤ C * (η : ℝ) := mul_le_mul_of_nonneg_left hlagJ' hC
    linarith
  have hsplit2 : ((H I n (sMax X I n) : ℤ) : ℝ) - ((H I n (sMax X J n) : ℤ) : ℝ)
      = ((H I n (sMax X I n) - H I n (sMax X J n) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [Wst_of_nonempty (H := H) (X := X) (I := I) (n := n) hJ, hsup]
  linarith [hcoord', havg, hsplit2]

/-- **The join-gap step of the order-statistic induction**, with the local field's parameter
`ηF` decoupled from the lag allowance `η` used in the geometry.  This is
`JoinStep.join_gap_of_top_sub` with the field's `η` replaced by `ηF`; the proof uses the field
only for `(loccoord)`/`(locmove)`/potential monotonicity, and the lag only through `hlagw`. -/
theorem join_gap_of_top_lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r ηF η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r ηF) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {β₀ b : ℝ} (hβ₀ : (spreadS X Finset.univ n₀ : ℝ) ≤ β₀)
    {k : ℕ} (hIH : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ I : Finset ι, I.card = k →
      TopBlock X I u → (spreadS X I u : ℝ) ≤ b)
    {n : ℕ} (hn : n₀ ≤ n) (hn' : n ≤ n₁)
    {I : Finset ι} (hIcard : I.card = k) (hIne : I.Nonempty) (hI' : I ≠ Finset.univ)
    (htop : TopBlock X I n) :
    ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ) ≤ Gstep C CT L η β₀ b := by
  classical
  have hβ₀nn : 0 ≤ β₀ := by
    have h0 : (0 : ℝ) ≤ (spreadS X (Finset.univ : Finset ι) n₀ : ℝ) := by
      have := spreadS_nonneg (X := X) (S := (Finset.univ : Finset ι)) (n := n₀)
        Finset.univ_nonempty
      exact_mod_cast this
    linarith
  have hJne : (Finset.univ \ I).Nonempty :=
    Finset.sdiff_nonempty.mpr (by simpa using hI')
  have hpos : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ i, 0 ≤ X i u := by
    intro u hu0 hu1 i
    exact pos_nonneg hτ hne hdr (le_trans hn₀ hu0) (le_trans hu1 hn₁) hr
  have hwin : τ r ≤ n := le_trans hn₀ hn
  have hlagJ : ∀ j ∈ Finset.univ \ I, runMaxI X j n - X j n ≤ (η : ℤ) :=
    fun j _ => hlagw j n hn hn'
  have hlagJu : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ j ∈ Finset.univ \ I,
      runMaxI X j u - X j u ≤ (η : ℤ) :=
    fun u hu0 hu1 j _ => hlagw j u hu0 hu1
  rcases Classical.em (Sep X I (Finset.univ \ I) n) with hsep | hnsep
  · -- **branch 1**: `(sep)` holds at `n`; use the run start and `(locmove)`
    have hWn : ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ)
        ≤ Wst H X I (Finset.univ \ I) n :=
      Wst_ge_gap hLF.hmono hLF.hunit hsep
    obtain ⟨u, hu0, hun, hrun, hfirst⟩ :=
      exists_run_start (P := fun w => Sep X I (Finset.univ \ I) w) hn hsep
    have hu_n₁ : u ≤ n₁ := le_trans hun hn'
    have htop_u : ∀ w, u ≤ w → w ≤ n → TopBlock X I w := by
      intro w h1 h2
      have hs := hrun w h1 h2
      intro i hi j hj
      have hjJ : j ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
      have := hs.2.2.2 i hi j hjJ
      exact le_trans (le_runMaxI X j w) (by linarith)
    have hspread_u : (spreadS X I u : ℝ) ≤ b :=
      hIH u hu0 hu_n₁ I hIcard (htop_u u le_rfl hun)
    have hgapu : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) ≤ max 2 β₀ := by
      rcases eq_or_lt_of_le hu0 with heq | hlt
      · have h1 : sMin X I u - sMaxM X (Finset.univ \ I) u ≤
            sMin X I u - sMax X (Finset.univ \ I) u := by
          have : sMax X (Finset.univ \ I) u ≤ sMaxM X (Finset.univ \ I) u :=
            sMax_le hJne (fun j hj => le_trans (le_runMaxI X j u) (le_sMaxM hJne hj))
          linarith
        have h2 := gap_le_spread_univ (X := X) (I := I) (n := u) hIne hJne
        have h3 : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ)
            ≤ (spreadS X Finset.univ u : ℝ) := by
          have : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ)
              ≤ ((sMin X I u - sMax X (Finset.univ \ I) u : ℤ) : ℝ) := by
            exact_mod_cast h1
          linarith
        have h4 : (spreadS X Finset.univ u : ℝ) ≤ β₀ := by
          rw [← heq]; exact hβ₀
        exact le_trans h3 (le_trans h4 (le_max_right _ _))
      · have hu1 : 1 ≤ u := by omega
        have hposm : ∀ i, 0 ≤ X i (u - 1) := by
          intro i
          have hle : n₀ ≤ u - 1 := by omega
          have hle' : u - 1 ≤ n₁ := by omega
          exact hpos (u - 1) hle hle' i
        have hnot : ¬ Sep X I (Finset.univ \ I) (u - 1) := hfirst hlt
        have h2 : sMin X I u - sMaxM X (Finset.univ \ I) u ≤ 2 :=
          gap_at_failure hne hIne hI' hu1 hposm hnot
        have : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by
          exact_mod_cast h2
        refine le_trans this (le_trans ?_ (le_max_left _ _))
        norm_num
    have hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X (Finset.univ \ I) u := by
      obtain ⟨j, hj, hval⟩ := exists_sMax (X := X) (S := Finset.univ \ I) (n := u) hJne
      rw [hval]
      exact pos_ge_range hτ hne hdr (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁)
    have hWu : Wst H X I (Finset.univ \ I) u
        ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hbase := Wst_le_of_sep_lag hLF hC.le (I := I) (J := Finset.univ \ I) (n := u)
        (η := η) (hrun u le_rfl hun) hI' (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁) hlo
        (fun j hj => hlagw j u hu0 hu_n₁)
      have hcast : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) ≤ max 2 β₀ := hgapu
      have hmono : C * ((spreadS X I u : ℝ)
          + ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) + (η : ℝ))
          ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith
      linarith [hbase, hmono]
    have hhalf : ∀ w, u ≤ w → w < n → Sep X I (Finset.univ \ I) w :=
      fun w h1 h2 => hrun w h1 (le_of_lt h2)
    have hmove := hLF.wmove I u n hIne hI' (le_trans hn₀ hu0) hun
      (le_trans hn' hn₁) hhalf
    have hR : ((sMaxM X I u : ℝ) - (sMin X I u : ℝ)) ≤ (spreadS X I u : ℝ) + (η : ℝ) := by
      have h1 : sMaxM X I u ≤ sMax X I u + (η : ℤ) := by
        have h2 := sMaxM_sub_sMax_le (X := X) (J := I) (n := u) hIne
          (fun i hi => hlagw i u hu0 hu_n₁)
        linarith
      have h1' : ((sMaxM X I u : ℤ) : ℝ) ≤ ((sMax X I u : ℤ) : ℝ) + (η : ℝ) := by
        exact_mod_cast h1
      have h2' : ((spreadS X I u : ℤ) : ℝ)
          = ((sMax X I u : ℤ) : ℝ) - ((sMin X I u : ℤ) : ℝ) := by
        unfold spreadS
        push_cast
        ring
      linarith
    have hWn_le : Wst H X I (Finset.univ \ I) n
        ≤ Wst H X I (Finset.univ \ I) u + C * ((spreadS X I u : ℝ) + (η : ℝ))
          + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hmul : C * (((sMaxM X I u : ℤ) : ℝ) - ((sMin X I u : ℤ) : ℝ))
          ≤ C * ((spreadS X I u : ℝ) + (η : ℝ)) := mul_le_mul_of_nonneg_left hR hC.le
      have hneg : (0 : ℝ) ≤ ((n - u : ℕ) : ℝ) / C := by positivity
      linarith [hmove, hmul]
    have hfin : ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ)
        ≤ 2 * C * (b + β₀ + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hb : C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ))
          ≤ C * (b + β₀ + (η : ℝ) + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        have hmax : max 2 β₀ ≤ β₀ + 2 := by
          rcases le_total (2:ℝ) β₀ with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        linarith
      have hA : C * ((spreadS X I u : ℝ) + (η : ℝ)) ≤ C * (b + (η : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith
      nlinarith [hWn, hWu, hWn_le, hb, hA, hβ₀nn]
    exact le_trans hfin (le_max_right _ _)
  · -- **branch 2**: `(sep)` fails at `n`
    have hgap := not_sep_gap_le (X := X) (η := η) (I := I) (n := n) hIne hJne
      (hpos n hn hn') hlagJ hnsep
    have : ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ) ≤ 1 + (η : ℝ) := by
      exact_mod_cast hgap
    exact le_trans this (le_Gstep C CT L η β₀ b)

/-- **The top-block induction with the lag allowance decoupled**: a copy of
`JoinStep.spread_univ_le_sub` for a local field built at the coarse `ηF` and the sharp lag `η`. -/
theorem spread_univ_le_lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r ηF η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r ηF) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η (spreadS X Finset.univ n₀ : ℝ) (β k) ≤ β (k + 1)) :
    ∀ n, n₀ ≤ n → n ≤ n₁ →
      (spreadS X Finset.univ n : ℝ)
        ≤ β (Finset.univ : Finset ι).card := by
  classical
  set β₀ : ℝ := (spreadS X Finset.univ n₀ : ℝ) with hβ₀def
  have hβ₀ : (spreadS X Finset.univ n₀ : ℝ) ≤ β₀ := le_rfl
  have hmain : ∀ k, 1 ≤ k → k ≤ (Finset.univ : Finset ι).card →
      ∀ n, n₀ ≤ n → n ≤ n₁ → ∀ I : Finset ι, I.card = k →
        TopBlock X I n → (spreadS X I n : ℝ) ≤ β k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro hnk n hn hn' I hIcard _
        have hzero : spreadS X I n = 0 := spread_singleton hIcard
        rw [hzero]
        push_cast
        simpa using hβ1
    | succ k hk ih =>
        intro hnk n hn hn' I' hI'card htop'
        have hI'pos : 0 < I'.card := by rw [hI'card]; omega
        obtain ⟨i0, hi0, hmin⟩ := exists_sMin (X := X) (S := I') (n := n)
          (Finset.card_pos.mp hI'pos)
        set I : Finset ι := I'.erase i0 with hIdef
        have hIcard : I.card = k := by
          rw [hIdef, Finset.card_erase_of_mem hi0]; omega
        have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
        have hI' : I ≠ Finset.univ := by
          intro hc
          have : I.card = (Finset.univ : Finset ι).card := by rw [hc]
          omega
        have hsub : I ⊆ I' := Finset.erase_subset _ _
        have htopI : TopBlock X I n := by
          intro i hi j hj
          by_cases hji : j = i0
          · rw [hji, ← hmin]
            exact sMin_le (X := X) (S := I') (n := n) ⟨i0, hi0⟩ (hsub hi)
          · exact htop' i (hsub hi) j
              (fun hmem => hj (Finset.mem_erase.mpr ⟨hji, hmem⟩))
        have hgap := join_gap_of_top_lag hτ hne hLF hC hdr hr hn₀ hn₁ hlagw hβ₀
          (fun u hu0 hu1 J hJcard hJtop => ih (by omega) u hu0 hu1 J hJcard hJtop)
          hn hn' hIcard hIne hI' htopI
        have hminI : ∀ j ∈ I, X i0 n ≤ X j n := by
          intro j hj
          rw [← hmin]
          exact sMin_le (X := X) (S := I') (n := n) ⟨i0, hi0⟩ (hsub hj)
        have hspread := spreadS_insert_min (X := X) (S := I) (i := i0) (n := n) hIne hminI
        rw [show insert i0 I = I' from by rw [hIdef, Finset.insert_erase hi0]] at hspread
        have hJne : (Finset.univ \ I).Nonempty :=
          Finset.sdiff_nonempty.mpr (by simpa using hI')
        have hsMax : sMax X (Finset.univ \ I) n = X i0 n := by
          refine sMax_eq_of_mem_le ?_ ?_
          · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i0, ?_⟩
            rw [hIdef]
            exact Finset.notMem_erase i0 I'
          · intro j hj
            obtain ⟨-, hjI⟩ := Finset.mem_sdiff.mp hj
            by_cases hji : j = i0
            · rw [hji]
            · have hj' : j ∉ I' := by
                intro hmem
                exact hjI (Finset.mem_erase.mpr ⟨hji, hmem⟩)
              exact htop' i0 hi0 j hj'
        have hIle : (spreadS X I n : ℝ) ≤ β k := ih (by omega) n hn hn' I hIcard htopI
        have hsum : (spreadS X I' n : ℝ)
            ≤ β k + Gstep C CT L η β₀ (β k) := by
          have hcast : (spreadS X I' n : ℝ)
              = (spreadS X I n : ℝ)
                + ((sMin X I n - X i0 n : ℤ) : ℝ) := by
            rw [hspread]; push_cast; ring
          have hgap' : ((sMin X I n - X i0 n : ℤ) : ℝ) ≤ Gstep C CT L η β₀ (β k) := by
            rw [← hsMax]; exact hgap
          linarith
        exact le_trans hsum (hstep k hk)
  intro n hn hn'
  have h := hmain (Finset.univ : Finset ι).card (Finset.card_pos.mpr Finset.univ_nonempty)
    le_rfl n hn hn' Finset.univ (by simp) (topBlock_univ X n)
  simpa using h

/-- **The terminal-at-record halving input with the decoupled lag allowance.** -/
theorem halving_input_of_window_lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r ηF η B : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r ηF) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η (spreadS X Finset.univ n₀ : ℝ) (β k) ≤ β (k + 1))
    (hββ : β (Finset.univ : Finset ι).card ≤ (L : ℝ) / 2)
    (hrec0 : n₀ ≤ τ (r + B * L)) (hrec1 : τ (r + B * L) ≤ n₁) :
    2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  have hspread := spread_univ_le_lag hτ hne hLF hC hdr hr hn₀ hn₁ hlagw hβ1 hstep
    (τ (r + B * L)) hrec0 hrec1
  exact twomul_defect_le_of_spread hτ (le_trans hspread hββ)

/-- **Halving from one coalescence time, with the lag bound derived.**  Same conclusion as
`JoinStep.halving_of_coalesce`, but the field is built at the coarse `ηF` and the lag bound
that the join consumes is the sharp `η`, supplied on `[s, τ_r+TL]` (in the intended use this is
`LagFromMart.lag_le_sub`, available as soon as `s ≥ τ_r + 64⌈C⌉L`). -/
theorem halving_of_coalesce_lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r ηF η B : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r ηF) {ε₀ : ℝ} (hC : 0 < C) (hCT : 0 ≤ CT)
    (hε₀ : 0 ≤ ε₀)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {s : ℕ} (hs₀ : τ r ≤ s)
    (hs : (spreadS X (Finset.univ : Finset ι) s : ℝ) ≤ ε₀ * (L : ℝ))
    (hlagw : ∀ (i : ι) (m : ℕ), s ≤ m → m ≤ τ r + T * L → runMaxI X i m - X i m ≤ (η : ℤ))
    {ε₁ ε₂ : ℝ} (hη : (η : ℝ) ≤ ε₁ * (L : ℝ))
    (hL3 : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε₂ * (L : ℝ))
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hsmall : (1 + 2 * C) ^ (Finset.univ : Finset ι).card
      * ((1 + ((Finset.univ : Finset ι).card : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) ≤ 1 / 4)
    (hlarge : (1 + 2 * C) ^ (Finset.univ : Finset ι).card
      * (((Finset.univ : Finset ι).card : ℝ) * (1 + 4 * C)) ≤ (L : ℝ) / 4)
    (hrecT : τ (r + B * L) ≤ τ r + T * L) (hrecB : s ≤ τ (r + B * L)) :
    2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  have hspreadnn : (0 : ℝ) ≤ (spreadS X (Finset.univ : Finset ι) s : ℝ) := by
    have := spreadS_nonneg (X := X) (S := (Finset.univ : Finset ι)) (n := s) Finset.univ_nonempty
    exact_mod_cast this
  refine halving_input_of_window_lag (η := η) (ηF := ηF)
    (β := betaOf C CT L η (spreadS X (Finset.univ : Finset ι) s : ℝ))
    hτ hne hLF hC hdr hr hs₀ (le_rfl : τ r + T * L ≤ τ r + T * L) hlagw ?_ ?_ ?_ hrecB hrecT
  · exact betaOf_nonneg (C := C) (CT := CT) (L := L) (η := η)
      (s := (spreadS X (Finset.univ : Finset ι) s : ℝ)) (le_of_lt hC) hCT hspreadnn 1
  · exact betaOf_step (C := C) (CT := CT) (L := L) (η := η)
      (s := (spreadS X (Finset.univ : Finset ι) s : ℝ)) (le_of_lt hC) hCT hspreadnn
  · exact betaOf_le_half (C := C) (CT := CT) (L := L) (η := η)
      (N := (Finset.univ : Finset ι).card) (s := (spreadS X (Finset.univ : Finset ι) s : ℝ))
      (le_of_lt hC) hCT hspreadnn hs hη hL3 hε₀ hε₁ hε₂ hsmall hlarge

/-- **Halving from one coalescence time in the sharp subwindow, with the lag bound derived.**

Everything the join consumes is present: the carrier `{d_r ≤ L}`, the Proposition-`local`
clauses (`(loccoord)`, `(locmove)`, potential monotonicity, `(lococc)`) at the source constants,
the martingale clause `(locmart)`, the explicit numerical thresholds of `JoinSub.betaOf_le_half`,
the advance deadline `τ_{r+BL} ≤ τ_r+TL`, and **one** time `s ∈ [τ_r+64⌈C⌉L, τ_{r+BL}]` with
`spread(s) ≤ ε L`.  The lag allowance `η` is not assumed on any window: it is derived at each
time of `[s, τ_r+TL]` from `(locmart)`+`(lococc)` by `LagFromMart.lag_le_sub`, which applies
because `s` begins after `64⌈C⌉L`; this is exactly the subwindow on which the paper's
`(fluidmax)` is sharp. -/
theorem halving_of_coalesce_sharp {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η B : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hclauses : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hHT : 0 ≤ CT) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    (hL1 : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : Numerics C CT L)
    (hT64 : 64 * Nat.ceil C ≤ T) (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {s : ℕ} (hs₀ : τ r + 64 * Nat.ceil C * L ≤ s)
    (hs : (spreadS X (Finset.univ : Finset ι) s : ℝ)
      ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ))
    (hη : (η : ℝ) ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ))
    (hLmin : HalfLmin C (Finset.univ : Finset ι).card ≤ (L : ℝ))
    (hrecT : τ (r + B * L) ≤ τ r + T * L) (hrecB : s ≤ τ (r + B * L)) :
    2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  have hLF : LocalField X τ H C CT T L r (L + η) := hclauses.toField hτ hM hdr hηdef
  have hlagw : ∀ (i : ι) (m : ℕ), s ≤ m → m ≤ τ r + T * L → runMaxI X i m - X i m ≤ (η : ℤ) := by
    intro i m hsm hmT
    exact lag_le_sub X hτ hM hC hclauses.occ hdr hL1 hij hnum hT64 hηdef
      (le_trans hs₀ hsm) hmT i
  have hsτ : τ r ≤ s := le_trans (Nat.le_add_right (τ r) (64 * Nat.ceil C * L)) hs₀
  exact halving_of_coalesce_lag hτ hne hLF hC hHT (HalfEps_nonneg hC _) hdr hr hsτ
    hs hlagw hη (le_trans hηdef hη) (HalfEps_nonneg hC _)
    (HalfEps_nonneg hC _) (halfEps_threshold hC _) (halfLmin_threshold hC hLmin) hrecT hrecB

/-! ## 3. The literal good event and the halving clause

`EndGood` is the paper's `𝒢_{r,L,T} ∩ {d_r ≤ L}` **plus one coalescence time in the sharp
subwindow**.  It carries the carrier, the Proposition-`local` clauses at the source constants,
`(locmart)`, the explicit numerical thresholds and that one time — and nothing else: in
particular no lag bound, no invariant/stationary/fixed start law, no `dT` bound, no `η = 0`,
no independence of a stationary future.

`NoCoalescence` is the *complement*, written in the form in which it is the residual estimate:
for every admissible deterministic package there is no small-spread time in the sharp subwindow.
`endGood_iff_not_noCoalescence` says the two are exact complements over the carrier, and
`measure_badHalf_le_noCoalescence` then shows that the halving clause reduces to the advance
clause plus `μ {NoCoalescence}` alone. -/

/-- **The good event of the halving clause**, with the coalescence time required only in the
sharp subwindow `[τ_r+64⌈C⌉L, τ_{r+BL}]` and with no lag hypothesis. -/
def EndGood (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (B T L r : ℕ) : Prop :=
  defect X τ r ≤ (L : ℤ) ∧
    ∃ (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (C CT μ : ℝ) (η : ℕ),
      0 < C ∧ 0 ≤ CT ∧ 1 ≤ L ∧ 64 * Nat.ceil C ≤ B ∧ 64 * Nat.ceil C ≤ T ∧
        HalfLmin C (Finset.univ : Finset ι).card ≤ (L : ℝ) ∧
        Numerics C CT L ∧
        CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) ∧
        (η : ℝ) ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ) ∧
        LocalClauses X τ H C CT T L r ∧
        MartClause X τ A μ CT T L r ∧
        ∃ s : ℕ, τ r + 64 * Nat.ceil C * L ≤ s ∧ s ≤ τ (r + B * L) ∧
          (spreadS X (Finset.univ : Finset ι) s : ℝ)
            ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ)

/-- **The exact remaining literal stochastic estimate.**

For the record window at `(B,T,L,r)`, this says: *for every* choice of potential `H`, clock `A`
and constants `(C, C_T, μ, η)` satisfying the deterministic package — the Proposition-`local`
clauses `(loccoord)`, `(locmove)`, potential monotonicity/unit increment, `(lococc)`, the
martingale clause `(locmart)`, the explicit numerical thresholds and the `η`-range — there is
**no** integer time `s ∈ [τ_r+64⌈C⌉L, τ_{r+BL}]` at which the whole-pack spread is at most `εL`
(`ε = HalfEps C |ι|`).

This is the finite-`L`, uniform-in-the-package form of the source's conclusion `d_{r+BL}/L → 0`
from the proof of Proposition `tight` (obtained there after Arzelà–Ascoli, `(coincide)` and
`(meet)`).  It contains no probability: it is a property of a single trajectory.  Over the
carrier it is exactly the complement of `EndGood`, and `measure_badHalf_le_noCoalescence` shows
that it is the only remaining input to the halving clause beyond the advance clause. -/
def NoCoalescence (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (B T L r : ℕ) : Prop :=
  ∀ (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (C CT μ : ℝ) (η : ℕ),
    0 < C → 0 ≤ CT → 64 * Nat.ceil C ≤ B → 64 * Nat.ceil C ≤ T →
      HalfLmin C (Finset.univ : Finset ι).card ≤ (L : ℝ) →
      Numerics C CT L →
      CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) →
      (η : ℝ) ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ) →
      LocalClauses X τ H C CT T L r → MartClause X τ A μ CT T L r →
      ¬ ∃ s : ℕ, τ r + 64 * Nat.ceil C * L ≤ s ∧ s ≤ τ (r + B * L) ∧
        (spreadS X (Finset.univ : Finset ι) s : ℝ)
          ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ)

/-- The `HalfLmin` size condition forces `L ≥ 1`. -/
theorem one_le_of_halfLmin_le {C : ℝ} {N L : ℕ} (hC : 0 < C) (hN : 1 ≤ N)
    (h : HalfLmin C N ≤ (L : ℝ)) : 1 ≤ L := by
  have h1 : (1 : ℝ) ≤ HalfLmin C N := by
    unfold HalfLmin
    have hA : (1 : ℝ) ≤ (1 + 2 * C) ^ N := one_le_pow₀ (by linarith)
    have hB : (1 : ℝ) ≤ (N : ℝ) * (1 + 4 * C) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have h1c : (1 : ℝ) ≤ 1 + 4 * C := by linarith
      nlinarith
    nlinarith [hA, hB]
  have h2 : (1 : ℝ) ≤ (L : ℝ) := le_trans h1 h
  exact_mod_cast h2

/-- `EndGood` is exactly the carrier together with the negation of `NoCoalescence`. -/
theorem endGood_iff_not_noCoalescence {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {B T L r : ℕ} :
    EndGood (ι := ι) X τ B T L r ↔
      defect X τ r ≤ (L : ℤ) ∧ ¬ NoCoalescence X τ B T L r := by
  constructor
  · rintro ⟨hdr, H, A, C, CT, μ, η, hC, hHT, hL1, hB, hT, hLmin, hnum, hηdef, hη,
      hcl, hM, s, hs, hrec, hsp⟩
    refine ⟨hdr, ?_⟩
    intro hNC
    exact hNC H A C CT μ η hC hHT hB hT hLmin hnum hηdef hη hcl hM ⟨s, hs, hrec, hsp⟩
  · rintro ⟨hdr, hNC⟩
    by_contra hcon
    apply hNC
    intro H A C CT μ η hC hHT hB hT hLmin hnum hηdef hη hcl hM hs
    exact hcon ⟨hdr, H, A, C, CT, μ, η, hC, hHT,
      one_le_of_halfLmin_le hC (Finset.card_pos.mpr Finset.univ_nonempty) hLmin,
      hB, hT, hLmin, hnum, hηdef, hη, hcl, hM, hs⟩

/-- `EndGood` plus the first block inequality rules out `BadHalf`: this is the paper's second
block inequality `(half)` from the coalescence time alone. -/
theorem not_badHalf_of_endGood {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {B T L r : ℕ} {i₀ j₀ : ι}
    (hij : i₀ ≠ j₀) (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hr : (T + 3) * L ≤ r) (hgood : EndGood (ι := ι) X τ B T L r)
    (hadv : ¬ HblkTwo.BadTime B T (fun u => (defect X τ u).toNat, τ) r L) :
    ¬ HblkTwo.BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  obtain ⟨hdr, H, A, C, CT, μ, η, hC, hHT, hL1, -, hT64, hLmin, hnum, hηdef, hη,
    hclauses, hM, s, hs₀, hsB, hspread⟩ := hgood
  have hrecT : τ (r + B * L) ≤ τ r + T * L := by
    by_contra hc
    exact hadv ⟨Int.toNat_le.mpr hdr, Nat.lt_of_not_le hc⟩
  have hdef : 2 * defect X τ (r + B * L) ≤ (L : ℤ) :=
    halving_of_coalesce_sharp hτ hne hclauses hM hC hHT hdr hr hL1 hij hnum hT64 hηdef
      hs₀ hspread hη hLmin hrecT hsB
  exact Glue.not_badHalf_of_defect_le hτ hdef

/-- **Measure level, almost-everywhere record structure.**  The mass of the halving bad event
is at most the mass of the advance bad event plus the mass of `(EndGood)ᶜ`.  The null set of
non-record trajectories is added explicitly and is `0` by the hypothesis. -/
theorem measure_badHalf_le_endGood_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω)) {B T L r : ℕ} (hr : (T + 3) * L ≤ r) :
    μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} +
        μ {ω | ¬ EndGood (ι := ι) (X ω) (τ ω) B T L r} := by
  have hnull : μ {ω | ¬ IsRecord (X ω) (τ ω)} = 0 := ae_iff.mp hτ
  set A : Set Ω := {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat,
    τ ω) r L} with hA
  set Bh : Set Ω := {ω | ¬ IsRecord (X ω) (τ ω)} with hBh
  set C : Set Ω := {ω | ¬ EndGood (ι := ι) (X ω) (τ ω) B T L r} with hC
  have hsub : {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ⊆ (A ∪ Bh) ∪ C := by
    intro ω hω
    by_cases hb : HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L
    · exact Or.inl (Or.inl hb)
    · by_cases hrec : IsRecord (X ω) (τ ω)
      · refine Or.inr ?_
        intro hg
        exact not_badHalf_of_endGood hij hrec (hne ω) hr hg hb hω
      · exact Or.inl (Or.inr hrec)
  calc μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ≤ μ ((A ∪ Bh) ∪ C) := measure_mono hsub
    _ ≤ μ (A ∪ Bh) + μ C := measure_union_le _ _
    _ ≤ (μ A + μ Bh) + μ C := by
        exact add_le_add (measure_union_le (μ := μ) A Bh) (le_refl (μ C))
    _ = μ A + μ C := by rw [hBh, hnull]; simp

/-- **The halving bad event is contained in the advance bad event together with
`NoCoalescence`.**  This is the exact decomposition of the halving clause: the local-good field,
the potential clauses, the numerical thresholds and `(locmart)` do **not** appear in the
residual, because `NoCoalescence` quantifies over them.  Hence the only stochastic input to the
halving clause, beyond the advance clause already needed for the first block inequality, is the
single named estimate `μ {NoCoalescence}` — the finite-`L` form of `d_{r+BL}/L → 0`. -/
theorem measure_badHalf_le_noCoalescence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω)) {B T L r : ℕ} (hr : (T + 3) * L ≤ r) :
    μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} +
        μ {ω | NoCoalescence (X ω) (τ ω) B T L r} := by
  have hnull : μ {ω | ¬ IsRecord (X ω) (τ ω)} = 0 := ae_iff.mp hτ
  have hsub : {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ⊆ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
        ∪ ({ω | ¬ IsRecord (X ω) (τ ω)}
          ∪ {ω | NoCoalescence (X ω) (τ ω) B T L r}) := by
    intro ω hω
    by_cases hb : HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L
    · exact Or.inl hb
    · by_cases hrec : IsRecord (X ω) (τ ω)
      · refine Or.inr (Or.inr ?_)
        intro H A C CT ν η hC hHT hB hT hLmin hnum hηdef hη hcl hM hs
        have hcarrier : defect (X ω) (τ ω) r ≤ (L : ℤ) := by
          have h1 : ((defect (X ω) (τ ω) r).toNat : ℤ) = defect (X ω) (τ ω) r :=
            Int.toNat_of_nonneg (defect_nonneg hrec r)
          have h2 : ((defect (X ω) (τ ω) r).toNat : ℕ) ≤ L := hω.1
          have h3 : ((defect (X ω) (τ ω) r).toNat : ℤ) ≤ (L : ℤ) := by exact_mod_cast h2
          rw [h1] at h3
          exact h3
        have hend : EndGood (ι := ι) (X ω) (τ ω) B T L r :=
          ⟨hcarrier, H, A, C, CT, ν, η, hC, hHT,
            one_le_of_halfLmin_le hC (Finset.card_pos.mpr Finset.univ_nonempty) hLmin,
            hB, hT, hLmin, hnum, hηdef, hη, hcl, hM, hs⟩
        exact not_badHalf_of_endGood hij hrec (hne ω) hr hend hb hω
      · exact Or.inr (Or.inl hrec)
  calc μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ≤ μ ({ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
          ∪ ({ω | ¬ IsRecord (X ω) (τ ω)}
            ∪ {ω | NoCoalescence (X ω) (τ ω) B T L r})) := measure_mono hsub
    _ ≤ μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
          + μ ({ω | ¬ IsRecord (X ω) (τ ω)}
            ∪ {ω | NoCoalescence (X ω) (τ ω) B T L r}) := measure_union_le _ _
    _ ≤ μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
          + (μ {ω | ¬ IsRecord (X ω) (τ ω)}
            + μ {ω | NoCoalescence (X ω) (τ ω) B T L r}) := by
        exact add_le_add le_rfl (measure_union_le _ _)
    _ = μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
          + μ {ω | NoCoalescence (X ω) (τ ω) B T L r} := by rw [hnull]; simp

/-! ## 4. The literal array-level halving clause

This is the same instantiation as the public `HalvingClause.halfClauseAt_of_goodHalf`, with the
good event replaced by `EndGood`: the lag hypothesis is gone and the coalescence time sits in
the sharp subwindow. -/

end JoinStep

namespace JoinStep

open RecordDefect RecordoSupply HblkTwo HblkFinal FluidBlock
open Swarming Swarming.Uniform SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The literal source halving clause from `(EndGood)`.**  A profile bound on
`BadTime ∪ (EndGood)ᶜ` on the actual array — the literal `Swarming.Uniform.arrayMeasure N`,
`actX p m U`, `recTimeA p m U` — at the source-general constants `B ≤ C₀ − T − 1` gives
`SourceTightAvail.HalfClauseAt`.  `EndGood` carries no lag bound and no `∃`-time over the whole
window: only the Proposition-`local` clauses, `(locmart)`, the thresholds, the carrier and one
coalescence time in `[τ_r+64⌈C⌉L, τ_{r+BL}]`. -/
theorem halfClauseAt_of_endGood {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hB : 2 ≤ B) (hC₀ : B + T + 1 ≤ C₀)
    (P : ℕ → ℝ≥0∞)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U : Array N | HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r ℓ}
        + (arrayMeasure N) {U : Array N |
            ¬ EndGood (ι := Fin N) (actX p m U) (recTimeA p m U) B T ℓ r} ≤ P ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ P := by
  intro ℓ hℓ r hr
  have hr3 : (T + 3) * ℓ ≤ r := by
    have h1 : T + 3 ≤ C₀ := by omega
    exact le_trans (Nat.mul_le_mul_right ℓ h1) hr
  have hij : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    have h2 : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  have hmain := measure_badHalf_le_endGood_ae (ι := Fin N) (arrayMeasure N)
    (X := fun U => actX p m U) (τ := fun U => recTimeA p m U) hij
    (fun U => actX_step p m U) (ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN)
    (B := B) (T := T) (L := ℓ) (r := r) hr3
  have hset : ∀ U : Array N,
      HblkTwo.BadHalf B (fun u => (defect (actX p m U) (recTimeA p m U) u).toNat,
        fun r => recTimeA p m U r) r ℓ
        = HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ := fun _ => rfl
  simp only [hset] at hmain
  exact le_trans hmain (hP ℓ hℓ r hr)

/-- **The literal source halving clause from the single remaining estimate `NoCoalescence`.**

On the actual array — literal `Swarming.Uniform.arrayMeasure N`, `actX p m U`, `recTimeA p m U`
— the halving clause follows from a profile bound on

  `BadTime ∪ NoCoalescence(actX, recTimeA, B, T, ℓ, r)`,

i.e. exactly the advance clause plus the estimate that no admissible deterministic package admits
a small-spread time in the sharp subwindow.  No local-good field, no lag bound, no stationarity,
no invariance, no start law and no `dT` bound appears in the hypothesis. -/
theorem halfClauseAt_of_noCoalescence {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hB : 2 ≤ B) (hC₀ : B + T + 1 ≤ C₀)
    (P : ℕ → ℝ≥0∞)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U : Array N | HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r ℓ}
        + (arrayMeasure N) {U : Array N |
            NoCoalescence (actX p m U) (recTimeA p m U) B T ℓ r} ≤ P ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ P := by
  intro ℓ hℓ r hr
  have hr3 : (T + 3) * ℓ ≤ r := by
    have h1 : T + 3 ≤ C₀ := by omega
    exact le_trans (Nat.mul_le_mul_right ℓ h1) hr
  have hij : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    have h2 : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  have hmain := measure_badHalf_le_noCoalescence (ι := Fin N) (arrayMeasure N)
    (X := fun U => actX p m U) (τ := fun U => recTimeA p m U) hij
    (fun U => actX_step p m U) (ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN)
    (B := B) (T := T) (L := ℓ) (r := r) hr3
  have hset : ∀ U : Array N,
      HblkTwo.BadHalf B (fun u => (defect (actX p m U) (recTimeA p m U) u).toNat,
        fun r => recTimeA p m U r) r ℓ
        = HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ := fun _ => rfl
  simp only [hset] at hmain
  exact le_trans hmain (hP ℓ hℓ r hr)

end JoinStep

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 5. The two obstructions: the `+L` in the whole-window lag cannot be fed to the
halving thresholds, and the sharp window forces the source's `T ≥ 64⌈C⌉`

`LagFromMart.lag_le_window` proves the whole-window bound `M^i_n − X^i_n ≤ η + L`, and the `L`
is not slack: before `τ_r + 64⌈C⌉L` the martingale comparison has not had time to act, so a
walker may be a full `d_r ≤ L` below the record it held earlier.  The two lemmas below say,
first, that such an allowance is *incompatible* with the halving thresholds, and second, that
the sharp good event of §3 can only hold when `T ≥ 64⌈C⌉` — the paper's numerical requirement,
which is therefore visible rather than silently dropped. -/

/-- **Obstruction: a lag allowance `≥ L` is incompatible with the halving thresholds.**

The thresholds of `JoinSub.betaOf_le_half` force `ε₁ ≤ 1/4` (because
`(1+2C)^N(1+N(4C+4)) ≥ 1`), whereas any allowance `η ≥ L` together with `η ≤ ε₁ L` forces
`ε₁ ≥ 1`.  Hence the whole-window form of the lag hypothesis — which is exactly what
`lag_le_window` supports — cannot be instantiated at all, and the coalescence time has to be
sought in the sharp subwindow of `lag_le_sub`. -/
theorem not_threshold_of_allowance_ge_L {C : ℝ} {N : ℕ} {ε₀ ε₁ ε₂ : ℝ} {L η : ℕ}
    (hC : 0 < C) (hN : 1 ≤ N) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hsmall : (1 + 2 * C) ^ N * ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) ≤ 1 / 4)
    (hL1 : 1 ≤ L) (hlag : (L : ℝ) ≤ (η : ℝ)) (hη : (η : ℝ) ≤ ε₁ * (L : ℝ)) : False := by
  have hA : (1 : ℝ) ≤ (1 + 2 * C) ^ N := one_le_pow₀ (by linarith)
  have hB : (1 : ℝ) ≤ 1 + (N : ℝ) * (4 * C + 4) := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) * (4 * C + 4) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ 4 * C + 4 := by linarith
      positivity
    linarith
  have hS : (0 : ℝ) ≤ ε₀ + ε₁ + ε₂ := by linarith
  have hprod : (1 : ℝ) ≤ (1 + 2 * C) ^ N * (1 + (N : ℝ) * (4 * C + 4)) := by
    have h := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1) (le_trans (by norm_num) hA)
    simpa using h
  have hquarter : ε₁ ≤ 1 / 4 := by
    have h1 : ε₀ + ε₁ + ε₂
        ≤ (1 + 2 * C) ^ N * ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) := by
      have h := mul_le_mul_of_nonneg_right hprod hS
      nlinarith [h]
    linarith
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have h1le : (1 : ℝ) ≤ ε₁ := by
    have h2 : (L : ℝ) ≤ ε₁ * (L : ℝ) := le_trans hlag hη
    nlinarith [h2, hLpos]
  linarith

/-- **The sharp good event forces the source's `T ≥ 64⌈C⌉`.**  If a coalescence time
`s ≥ τ_r + 64⌈C⌉L` exists below the endpoint `τ_{r+BL}`, then `¬BadTime` (whose content is the
advance deadline `τ_{r+BL} ≤ τ_r + TL`) implies `64⌈C⌉ ≤ T`.  So the subwindow requirement of
`(fluidmax)` is a consequence of the good event, not an extra assumption, and no block
arithmetic silently omits it. -/
theorem sharp_window_forces_T {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {C : ℝ} {B T L r s : ℕ}
    (hL1 : 1 ≤ L) (hs : τ r + 64 * Nat.ceil C * L ≤ s) (hs2 : s ≤ τ (r + B * L))
    (hrecT : τ (r + B * L) ≤ τ r + T * L) : 64 * Nat.ceil C ≤ T := by
  have h1 : τ r + 64 * Nat.ceil C * L ≤ τ r + T * L := le_trans (le_trans hs hs2) hrecT
  have h2 : 64 * Nat.ceil C * L ≤ T * L := by omega
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

/-- **The source's `(BTchoice)` satisfies the sharp-window requirement `64⌈C⌉ ≤ B`.**

The paper picks `B > (1+64C)(1+b)^N + 2` with `b = C^2` and `C ≥ 1` (increasing the
`(loccoord)` coefficient is allowed).  Since `b ≥ 1` and `N ≥ 2`, `(1+b)^N ≥ 4`, hence
`B > 4(1+64C) + 2 = 256C + 6 ≥ 64C + 64 > 64⌈C⌉`.  So the coalescence window
`[τ_r+64⌈C⌉L, τ_{r+BL}]` used in `EndGood` is non-empty for the paper's own constants; the
requirement is not an extra restriction on the block arithmetic. -/
theorem source_B_compatible {C b : ℝ} {N B : ℕ} (hC1 : 1 ≤ C) (hb : 1 ≤ b) (hN : 2 ≤ N)
    (hB : (1 + 64 * C) * (1 + b) ^ N + 2 < (B : ℝ)) : 64 * Nat.ceil C ≤ B := by
  have hpow : (4 : ℝ) ≤ (1 + b) ^ N := by
    have h2 : (1 + b) ^ 2 ≤ (1 + b) ^ N := pow_le_pow_right₀ (by linarith) hN
    nlinarith [h2, hb]
  have h4 : 4 * (1 + 64 * C) ≤ (1 + 64 * C) * (1 + b) ^ N := by
    have h0 : (0 : ℝ) ≤ 1 + 64 * C := by linarith
    nlinarith
  have hreal : (64 : ℝ) * (C + 1) ≤ (B : ℝ) := by nlinarith
  have hceil : (64 * Nat.ceil C : ℕ) < B := by
    have hc := Nat.ceil_lt_add_one (a := C) (by linarith : (0:ℝ) ≤ C)
    have hcast : ((64 * Nat.ceil C : ℕ) : ℝ) < (B : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  omega

/-- The ceiling of the (locmart) error is at most `εL` as soon as `x + 1 ≤ εL`. -/
theorem ceil_le_of_add_one {x ε L : ℝ} (hx : 0 ≤ x) (h : x + 1 ≤ ε * L) :
    ((Nat.ceil x : ℕ) : ℝ) ≤ ε * L := by
  have h2 := Nat.ceil_lt_add_one (a := x) hx
  linarith

/-- For fixed constants the sharp allowance is admissible at scale `L`: if the (locmart) error
is at most `εL/2` and `εL/2 ≥ 1`, then `⌈C_T L^{3/4}⌉ ≤ εL`.  So the numeric condition of
`EndGood` is the honest `o(L)` requirement and is non-vacuous for all large `L`; no `η = 0`
and no `ε = 1` is used anywhere. -/
theorem sharp_allowance_of_half {CT ε L : ℝ} (hCT : 0 ≤ CT) (hL : 0 ≤ L)
    (h1 : 2 * (CT * L ^ (3 / 4 : ℝ)) ≤ ε * L)
    (h2 : 2 ≤ ε * L) : ((Nat.ceil (CT * L ^ (3 / 4 : ℝ)) : ℕ) : ℝ) ≤ ε * L := by
  refine ceil_le_of_add_one (mul_nonneg hCT (Real.rpow_nonneg hL _)) ?_
  linarith

end JoinStep
