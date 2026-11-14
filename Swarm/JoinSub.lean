/-
# Finite-`L` joins with the lag bound required only after `64⌈C⌉L`, and the explicit halving arithmetic

The deterministic join induction of the public `Swarm/JoinCore.lean` consumes the
local-good field clause `LocalField.lag` on the **whole** record window `[τ_r, τ_r+TL]`.
`LagFromMart.lean` proves that clause can be *derived* from the paper's `(locmart)` +
`(lococc)`, but only with two different strengths:

* `η = ⌈C_T L^{3/4}⌉` on the subwindow `[τ_r + 64⌈C⌉L, τ_r+TL]` (`LagFromMart.lag_le_sub`);
* `η = L + ⌈C_T L^{3/4}⌉` on all of `[τ_r, τ_r+TL]` (`LagFromMart.lag_le_window`) — the `L`
  is not slack, because at `n = τ_r` the lag *is* `d_r`, which may equal `L` on the carrier.

This file

* re-runs the two join steps with the lag bound as an **explicit subwindow hypothesis**
  `hlagw` (`join_gap_of_top_sub`, `spread_univ_le_sub`, `halving_input_of_window_sub`), so
  that the sharp `η = O(L^{3/4})` is usable.  The proofs are the public ones; only the three
  `hLF.lag` call sites change, each gaining the window membership it needs;
* supplies the **explicit geometric sequence** `betaOf` that JoinCore left as the abstract
  hypothesis `hstep` (`betaOf`, `muOf`, `betaOf_step`, `betaOf_le`), together with the
  explicit numerical thresholds that make its `N`-th term at most `L/2`
  (`betaOf_le_half`): for `ε₀, ε₁, ε₂ ≥ 0`,
  `(1+2C)^N (1 + N(4C+3)) (ε₀+ε₁+ε₂) ≤ 1/4` and `(1+2C)^N N (1+4C) ≤ L/4`
  give `β N ≤ L/2` whenever the entry spread is `≤ ε₀ L`, `η ≤ ε₁ L`, `C_T L^{3/4} ≤ ε₂ L`;
* composes the two into `halving_of_coalesce`: **if the pack has spread at most `ε₀L` at some
  integer time `s ∈ [τ_r, τ_{r+BL}]`, and `τ_{r+BL} ≤ τ_r + TL`, then `2 d_{r+BL} ≤ L`.**
  This is precisely the halving input `Glue.not_badHalf_of_defect_le` consumes.

What this file does **not** do: supply the existence of that coalescence time.  The explicit
thresholds show why: the induction needs an *entry* spread of order `L/(2(1+2C)^N)`, and no
clause of Proposition `local` bounds the pack spread at any time — the source obtains
coalescence only after passing to the fluid limit.  The residual is stated in
`HalvingResidual.lean`.
-/
import Swarm.LagStep
import Swarm.JoinCore
import Swarm.LagFromMart

open Finset
open scoped BigOperators

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The join-gap step of the induction.**  Let `I` be a nonempty proper block of `k`
largest positions at time `n`, all inside the subwindow `[n₀,n₁] ⊆ [τ_r, τ_r+TL]` of a
record window on which `d_r ≤ L` and the local-good field holds.  If every block of `k`
largest positions has spread at most `b` throughout the window, then the separation of `I`
from the rest of the pack at `n` is at most `Gstep` of `(β₀, b)`. -/
theorem join_gap_of_top_sub {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
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
    -- the paper's `(Wpos)` at `n`
    have hWn : ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ)
        ≤ Wst H X I (Finset.univ \ I) n :=
      Wst_ge_gap hLF.hmono hLF.hunit hsep
    -- the start `u` of the final `(sep)`-run before `n`
    obtain ⟨u, hu0, hun, hrun, hfirst⟩ :=
      exists_run_start (P := fun w => Sep X I (Finset.univ \ I) w) hn hsep
    have hu_n₁ : u ≤ n₁ := le_trans hun hn'
    -- `I` is a top block at every time of the run
    have htop_u : ∀ w, u ≤ w → w ≤ n → TopBlock X I w := by
      intro w h1 h2
      have hs := hrun w h1 h2
      intro i hi j hj
      have hjJ : j ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
      have := hs.2.2.2 i hi j hjJ
      exact le_trans (le_runMaxI X j w) (by linarith)
    have hspread_u : (spreadS X I u : ℝ) ≤ b :=
      hIH u hu0 hu_n₁ I hIcard (htop_u u le_rfl hun)
    -- the separation at `u`
    have hgapu : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) ≤ max 2 β₀ := by
      rcases eq_or_lt_of_le hu0 with heq | hlt
      · -- `u = n₀`: the gap is at most the whole-pack spread at the window start
        have h1 : sMin X I u - sMaxM X (Finset.univ \ I) u ≤
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
      · -- `u > n₀`: `(sep)` failed at `u-1`, so the gap is at most `2`
        have hu1 : 1 ≤ u := by omega
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
    -- `(loccoord)` gives the value of `W` at the run start `u`
    have hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X (Finset.univ \ I) u := by
      obtain ⟨j, hj, hval⟩ := exists_sMax (X := X) (S := Finset.univ \ I) (n := u) hJne
      rw [hval]
      exact pos_ge_range hτ hne hdr (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁)
    have hWu : Wst H X I (Finset.univ \ I) u
        ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hbase := Wst_le_of_sep hLF hC.le (I := I) (J := Finset.univ \ I) (n := u)
        (hrun u le_rfl hun) hI' (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁) hlo
      have hcast : ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) ≤ max 2 β₀ := hgapu
      have hmono : C * ((spreadS X I u : ℝ)
          + ((sMin X I u - sMaxM X (Finset.univ \ I) u : ℤ) : ℝ) + (η : ℝ))
          ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith
      linarith [hbase, hmono]
    -- the drift term of `(locmove)` from `u` to `n`
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
    -- assemble
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

/-! ## 3. The order-statistic induction -/

/-- **The top-block induction (the paper's `(coincide)` for the whole pack).**

On the record window with `d_r ≤ L`, inside the subwindow `[n₀,n₁] ⊆ [τ_r, τ_r+TL]`, if the
whole-pack spread is at most `β₀` at `n₀`, then it is at most `β N` throughout, where `β` is
any sequence with `β 1 ≥ 0` and the geometric step `β (k+1) ≥ β k + Gstep(β₀, β k)`.

This is the finite-`L` form of the paper's induction over the order statistics of the pack;
`N` steps, one per order statistic, no more. -/
theorem spread_univ_le_sub {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
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
        -- the lowest member of the block, and the block with it removed
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
        -- the join-gap step at level `k`
        have hgap := join_gap_of_top_sub hτ hne hLF hC hdr hr hn₀ hn₁ hlagw hβ₀
          (fun u hu0 hu1 J hJcard hJtop => ih (by omega) u hu0 hu1 J hJcard hJtop)
          hn hn' hIcard hIne hI' htopI
        -- the spread identity for inserting the lowest member
        have hminI : ∀ j ∈ I, X i0 n ≤ X j n := by
          intro j hj
          rw [← hmin]
          exact sMin_le (X := X) (S := I') (n := n) ⟨i0, hi0⟩ (hsub hj)
        have hspread := spreadS_insert_min (X := X) (S := I) (i := i0) (n := n) hIne hminI
        rw [show insert i0 I = I' from by rw [hIdef, Finset.insert_erase hi0]] at hspread
        -- the pack maximum outside `I` is the removed lowest member
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


/-! ## 4. The terminal halving input with a subwindow lag bound -/

/-- **The terminal-at-record corollary**, with the lag bound required only on the subwindow
`[n₀,n₁]`.  Same statement as `JoinCore.halving_input_of_window`, with `hlagw` in place of the
field clause `LocalField.lag` on all of `[τ_r, τ_r+TL]`. -/
theorem halving_input_of_window_sub {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r η B : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η (spreadS X Finset.univ n₀ : ℝ) (β k) ≤ β (k + 1))
    (hββ : β (Finset.univ : Finset ι).card ≤ (L : ℝ) / 2)
    (hrec0 : n₀ ≤ τ (r + B * L)) (hrec1 : τ (r + B * L) ≤ n₁) :
    2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  have hspread := spread_univ_le_sub hτ hne hLF hC hdr hr hn₀ hn₁ hlagw hβ1 hstep
    (τ (r + B * L)) hrec0 hrec1
  exact twomul_defect_le_of_spread hτ (le_trans hspread hββ)

/-! ## 5. The explicit geometric sequence and its numerical thresholds -/

/-- The additive constant of the geometric join bound:
`μ = (1+η) + 2C(s+η+2) + 2 C_T L^{3/4}`, where `s = spread(n₀)`. -/
noncomputable def muOf (C CT : ℝ) (L η : ℕ) (s : ℝ) : ℝ :=
  (1 + (η : ℝ)) + 2 * C * (s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ)

/-- The explicit sequence of the join induction: `β 0 = s` (the entry spread) and
`β (k+1) = (1+2C) β k + μ`.  Its step dominates `Gstep` by `betaOf_step`. -/
noncomputable def betaOf (C CT : ℝ) (L η : ℕ) (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => (1 + 2 * C) * betaOf C CT L η s k + muOf C CT L η s

theorem betaOf_succ (C CT : ℝ) (L η : ℕ) (s : ℝ) (k : ℕ) :
    betaOf C CT L η s (k + 1)
      = (1 + 2 * C) * betaOf C CT L η s k + muOf C CT L η s := rfl

theorem muOf_nonneg {C CT : ℝ} {L η : ℕ} {s : ℝ} (hC : 0 ≤ C) (hCT : 0 ≤ CT) (hs : 0 ≤ s) :
    0 ≤ muOf C CT L η s := by
  unfold muOf
  have h1 : (0 : ℝ) ≤ (η : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ s + (η : ℝ) + 2 := by linarith
  have : 0 ≤ 2 * C * (s + (η : ℝ) + 2) := by positivity
  have : 0 ≤ 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  linarith

theorem betaOf_nonneg {C CT : ℝ} {L η : ℕ} {s : ℝ} (hC : 0 ≤ C) (hCT : 0 ≤ CT) (hs : 0 ≤ s) :
    ∀ k, 0 ≤ betaOf C CT L η s k := by
  intro k
  induction k with
  | zero => simpa [betaOf] using hs
  | succ k ih =>
      rw [betaOf_succ]
      have hμ := muOf_nonneg (C := C) (CT := CT) (L := L) (η := η) (s := s) hC hCT hs
      have : 0 ≤ (1 + 2 * C) * betaOf C CT L η s k := by
        have : 0 ≤ 1 + 2 * C := by linarith
        exact mul_nonneg this ih
      linarith

/-- `Gstep` is dominated by the affine form `2C b + μ`. -/
theorem Gstep_le_muOf {C CT : ℝ} {L η : ℕ} {s b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hCT : 0 ≤ CT) :
    Gstep C CT L η s b ≤ 2 * C * b + muOf C CT L η s := by
  unfold Gstep muOf
  have h1 : (0 : ℝ) ≤ 1 + (η : ℝ) := by positivity
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ 2 * C * (b + s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have h3 : (0 : ℝ) ≤ b + s + (η : ℝ) + 2 := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C * (b + s + (η : ℝ) + 2) := by positivity
    have h5 : (0 : ℝ) ≤ 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
    linarith
  rw [max_le_iff]
  constructor
  · linarith
  · linarith

/-- **`hstep` of the join induction, discharged by `betaOf`.** -/
theorem betaOf_step {C CT : ℝ} {L η : ℕ} {s : ℝ} (hC : 0 ≤ C) (hCT : 0 ≤ CT) (hs : 0 ≤ s) :
    ∀ k, 1 ≤ k →
      betaOf C CT L η s k + Gstep C CT L η s (betaOf C CT L η s k)
        ≤ betaOf C CT L η s (k + 1) := by
  intro k _
  rw [betaOf_succ]
  have hb := betaOf_nonneg (C := C) (CT := CT) (L := L) (η := η) (s := s) hC hCT hs k
  have hgs := Gstep_le_muOf (C := C) (CT := CT) (L := L) (η := η) (s := s) (b := betaOf C CT L η s k)
    hC hb hs hCT
  linarith

/-- Explicit geometric bound: `β k ≤ (1+2C)^k (s + k μ)`. -/
theorem betaOf_le {C CT : ℝ} {L η : ℕ} {s : ℝ} (hC : 0 ≤ C) (hCT : 0 ≤ CT) (hs : 0 ≤ s) :
    ∀ k, betaOf C CT L η s k ≤ (1 + 2 * C) ^ k * (s + (k : ℝ) * muOf C CT L η s) := by
  intro k
  induction k with
  | zero => simp [betaOf]
  | succ k ih =>
      rw [betaOf_succ]
      have hμ := muOf_nonneg (C := C) (CT := CT) (L := L) (η := η) (s := s) hC hCT hs
      have hA : (1 : ℝ) ≤ 1 + 2 * C := by linarith
      have hAk : (0 : ℝ) ≤ (1 + 2 * C) ^ k := by positivity
      have hstep : (1 + 2 * C) * ((1 + 2 * C) ^ k * (s + (k : ℝ) * muOf C CT L η s))
          + muOf C CT L η s
          ≤ (1 + 2 * C) ^ (k + 1) * (s + ((k : ℝ) + 1) * muOf C CT L η s) := by
        rw [pow_succ]
        have h1 : (1 + 2 * C) * ((1 + 2 * C) ^ k * (s + (k : ℝ) * muOf C CT L η s))
            = (1 + 2 * C) ^ k * (1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s) := by ring
        rw [h1]
        have hexp : (1 + 2 * C) ^ k * (1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s)
            = (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s)) := by ring
        rw [hexp]
        have hkey : (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s)) + muOf C CT L η s
            ≤ (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s))
              + (1 + 2 * C) ^ k * muOf C CT L η s := by
          have : (1 : ℝ) ≤ (1 + 2 * C) ^ k := one_le_pow₀ hA
          nlinarith [hμ]
        calc (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s)) + muOf C CT L η s
            ≤ (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s))
              + (1 + 2 * C) ^ k * muOf C CT L η s := hkey
          _ = (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s) + muOf C CT L η s) := by
              ring
          _ ≤ (1 + 2 * C) ^ k * ((1 + 2 * C) * (s + ((k : ℝ) + 1) * muOf C CT L η s)) := by
              refine mul_le_mul_of_nonneg_left ?_ hAk
              have : (1 + 2 * C) * (s + (k : ℝ) * muOf C CT L η s) + muOf C CT L η s
                  ≤ (1 + 2 * C) * (s + ((k : ℝ) + 1) * muOf C CT L η s) := by
                have h2 : (0 : ℝ) ≤ muOf C CT L η s := hμ
                nlinarith
              linarith
          _ = (1 + 2 * C) ^ (k + 1) * (s + ((k : ℝ) + 1) * muOf C CT L η s) := by
              rw [pow_succ]; ring
      have hthis := mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ 1 + 2 * C)
      push_cast
      linarith

/-- Auxiliary: the additive constant is at most `(ε₀+ε₁+ε₂)·L·(4C+4) + (1+4C)`. -/
theorem muOf_le {C CT : ℝ} {L η : ℕ} {s : ℝ} {ε₀ ε₁ ε₂ : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hsL : s ≤ ε₀ * (L : ℝ)) (hη : (η : ℝ) ≤ ε₁ * (L : ℝ))
    (hL3 : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε₂ * (L : ℝ))
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) :
    muOf C CT L η s ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) + (1 + 4 * C) := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hS : (0 : ℝ) ≤ ε₀ + ε₁ + ε₂ := by linarith
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hSL : (0 : ℝ) ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) := mul_nonneg hS hLnn
  -- `2C(s+η+2) ≤ 2C(ε₀L+ε₁L+2) = 2C(ε₀+ε₁)L + 4C`
  have hstep2 : 2 * C * (s + (η : ℝ) + 2) ≤ 2 * C * (ε₀ + ε₁) * (L : ℝ) + 4 * C := by
    have h1 : s + (η : ℝ) + 2 ≤ ε₀ * (L : ℝ) + ε₁ * (L : ℝ) + 2 := by linarith
    have h2 : 2 * C * (s + (η : ℝ) + 2) ≤ 2 * C * (ε₀ * (L : ℝ) + ε₁ * (L : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h1 h2C
    have h3 : 2 * C * (ε₀ * (L : ℝ) + ε₁ * (L : ℝ) + 2)
        = 2 * C * (ε₀ + ε₁) * (L : ℝ) + 4 * C := by ring
    linarith
  -- `2C(ε₀+ε₁)L ≤ 4C(ε₀+ε₁+ε₂)L`
  have hstep2' : 2 * C * (ε₀ + ε₁) * (L : ℝ) ≤ 4 * C * ((ε₀ + ε₁ + ε₂) * (L : ℝ)) := by
    have hsum : ε₀ + ε₁ ≤ 2 * (ε₀ + ε₁ + ε₂) := by linarith
    nlinarith [mul_nonneg h2C hSL, mul_le_mul_of_nonneg_right hsum hLnn, mul_nonneg h2C hLnn]
  have hstep3 : 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ 2 * ε₂ * (L : ℝ) := by linarith
  have hstep3' : 2 * ε₂ * (L : ℝ) ≤ 2 * ((ε₀ + ε₁ + ε₂) * (L : ℝ)) := by
    have : ε₂ ≤ ε₀ + ε₁ + ε₂ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hLnn]
  have hstep1 : (η : ℝ) ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) := by
    have h1 : ε₁ ≤ ε₀ + ε₁ + ε₂ := by linarith
    have h2 : ε₁ * (L : ℝ) ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hLnn
    have h3 : (ε₀ + ε₁ + ε₂) * (L : ℝ) ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) := by
      have : (1 : ℝ) ≤ 4 * C + 4 := by linarith
      nlinarith [hSL]
    linarith
  have hstep1' : (1 : ℝ) + (η : ℝ) ≤ 1 + (ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) := by linarith
  unfold muOf
  linarith

/-- **The explicit numerical threshold for `hββ`.**

If the entry spread is at most `ε₀ L`, the lag at most `ε₁ L`, the error `C_T L^{3/4}` at most
`ε₂ L` (all `ε ≥ 0`), and
`(1+2C)^N (1 + N(4C+4)) (ε₀+ε₁+ε₂) ≤ 1/4` and `(1+2C)^N N (1+4C) ≤ L/4`,
then `β N ≤ L/2`.  Every constant is explicit; `N = |ι|`.  In particular no `η = 0` is used
and the `C_T L^{3/4}` term is kept. -/
theorem betaOf_le_half {C CT : ℝ} {L η N : ℕ} {s : ℝ} {ε₀ ε₁ ε₂ : ℝ}
    (hC : 0 ≤ C) (hCT : 0 ≤ CT) (hs : 0 ≤ s) (hsL : s ≤ ε₀ * (L : ℝ))
    (hη : (η : ℝ) ≤ ε₁ * (L : ℝ))
    (hL3 : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε₂ * (L : ℝ))
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hsmall : (1 + 2 * C) ^ N * ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) ≤ 1 / 4)
    (hlarge : (1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)) ≤ (L : ℝ) / 4) :
    betaOf C CT L η s N ≤ (L : ℝ) / 2 := by
  have hA : (0 : ℝ) < 1 + 2 * C := by linarith
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hS : (0 : ℝ) ≤ ε₀ + ε₁ + ε₂ := by linarith
  have hμ := muOf_le (C := C) (CT := CT) (L := L) (η := η) (s := s)
    (ε₀ := ε₀) (ε₁ := ε₁) (ε₂ := ε₂) hC hs hsL hη hL3 hε₀ hε₁ hε₂
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  -- `s + N μ ≤ (1 + N(4C+4))(ε₀+ε₁+ε₂) L + N(1+4C)`
  have h2 : s + (N : ℝ) * muOf C CT L η s
      ≤ ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) * (L : ℝ) + (N : ℝ) * (1 + 4 * C) := by
    have hmul : (N : ℝ) * muOf C CT L η s
        ≤ (N : ℝ) * ((ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) + (1 + 4 * C)) :=
      mul_le_mul_of_nonneg_left hμ hN0
    have hs' : s ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) := by
      have h1 : ε₀ ≤ ε₀ + ε₁ + ε₂ := by linarith
      have h2 : ε₀ * (L : ℝ) ≤ (ε₀ + ε₁ + ε₂) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hLnn
      linarith
    have hfac : (ε₀ + ε₁ + ε₂) * (L : ℝ) ≤ ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) * (L : ℝ) := by
      have h1 : (1 : ℝ) ≤ 1 + (N : ℝ) * (4 * C + 4) := by
        have : (0 : ℝ) ≤ (N : ℝ) * (4 * C + 4) := by positivity
        linarith
      nlinarith [mul_nonneg hS hLnn]
    have h3 : (N : ℝ) * ((ε₀ + ε₁ + ε₂) * (L : ℝ) * (4 * C + 4) + (1 + 4 * C))
        = (N : ℝ) * (4 * C + 4) * ((ε₀ + ε₁ + ε₂) * (L : ℝ)) + (N : ℝ) * (1 + 4 * C) := by ring
    rw [h3] at hmul
    have h4 : ((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) * (L : ℝ)
        = (ε₀ + ε₁ + ε₂) * (L : ℝ) + (N : ℝ) * (4 * C + 4) * ((ε₀ + ε₁ + ε₂) * (L : ℝ)) := by ring
    linarith
  have h3 : (1 + 2 * C) ^ N * (s + (N : ℝ) * muOf C CT L η s)
      ≤ (1 + 2 * C) ^ N * (((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) * (L : ℝ))
        + (1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)) := by
    have hpos : (0 : ℝ) < (1 + 2 * C) ^ N := pow_pos hA N
    have := mul_le_mul_of_nonneg_left h2 hpos.le
    nlinarith [this]
  have h4 : (1 + 2 * C) ^ N * (((1 + (N : ℝ) * (4 * C + 4)) * (ε₀ + ε₁ + ε₂)) * (L : ℝ))
      ≤ (L : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hsmall hLnn
    linarith
  have h5 : (1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)) ≤ (L : ℝ) / 4 := hlarge
  have h6 : betaOf C CT L η s N ≤ (1 + 2 * C) ^ N * (s + (N : ℝ) * muOf C CT L η s) :=
    betaOf_le (C := C) (CT := CT) (L := L) (η := η) (s := s) hC hCT hs N
  linarith

/-! ## 6. The halving input from a coalescence time -/

/-- **Halving from one small-spread time.**

Let `s` be an integer time in `[τ_r, τ_{r+BL}]` at which the whole-pack spread is at most
`ε₀ L`, let the lag be at most `ε₁ L` on `[s, τ_r+TL]`, let `C_T L^{3/4} ≤ ε₂ L`, let
`0 ≤ C_T`, and let `τ_{r+BL} ≤ τ_r + TL` (the first block inequality).  Under the two explicit
numerical thresholds of `betaOf_le_half`, the paper's second block inequality
`2 d_{r+BL} ≤ L` holds.

So **the whole halving clause is reduced to the existence of one small-spread time before
`τ_{r+BL}`**; nothing else in the deterministic chain is missing. -/
theorem halving_of_coalesce {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η B : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) {ε₀ : ℝ} (hC : 0 < C) (hCT : 0 ≤ CT) (hε₀ : 0 ≤ ε₀)
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
  refine halving_input_of_window_sub (β := betaOf C CT L η (spreadS X (Finset.univ : Finset ι) s : ℝ))
    hτ hne hLF hC hdr hr hs₀ (le_rfl : τ r + T * L ≤ τ r + T * L) hlagw ?_ ?_ ?_ hrecB hrecT
  · exact betaOf_nonneg (C := C) (CT := CT) (L := L) (η := η)
      (s := (spreadS X (Finset.univ : Finset ι) s : ℝ)) (le_of_lt hC) hCT hspreadnn 1
  · exact betaOf_step (C := C) (CT := CT) (L := L) (η := η)
      (s := (spreadS X (Finset.univ : Finset ι) s : ℝ)) (le_of_lt hC) hCT hspreadnn
  · exact betaOf_le_half (C := C) (CT := CT) (L := L) (η := η)
      (N := (Finset.univ : Finset ι).card) (s := (spreadS X (Finset.univ : Finset ι) s : ℝ))
      (le_of_lt hC) hCT hspreadnn hs hη hL3 hε₀ hε₁ hε₂ hsmall hlarge

/-! ## 5b. Why the whole-window lag route cannot work -/

/-- **The entry-spread obstruction of the join route.**

Any geometric sequence that satisfies the join-induction step (with `s` the entry spread) and is
at most `L/2` at the `N`-th order statistic (`N ≥ 2`) necessarily satisfies
`2 C (s + η + 2) + 2 C_T L^{3/4} ≤ L/2`.

Consequently the join induction can only produce the halving input from an entry spread of
order `L/(4C)`.  Applied with the entry at `n₀ = τ_r` (`s = d_r`) this rules the route out
whenever `d_r ≳ L/(4C)`: the carrier is `{d_r ≤ L}`, so a `d_r` near `L` can never be handled by
the whole-window form.  This is why the lag has to be the subwindow-sharp one and why an
independent small-spread time is needed. -/
theorem join_route_entry_bound {C CT : ℝ} {L η N : ℕ} {s : ℝ} {β : ℕ → ℝ}
    (hC : 0 ≤ C) (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η s (β k) ≤ β (k + 1))
    (hββ : β N ≤ (L : ℝ) / 2) (hN : 2 ≤ N) :
    2 * C * (s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) / 2 := by
  -- the sequence is monotone
  have hmono : ∀ k l : ℕ, 1 ≤ k → k ≤ l → β k ≤ β l := by
    intro k l hk hkl
    induction l, hkl using Nat.le_induction with
    | base => exact le_rfl
    | succ l hkl ih =>
        have h1 : β l ≤ β (l + 1) := by
          have hs := hstep l (by omega)
          have h2 : 0 ≤ Gstep C CT L η s (β l) := Gstep_nonneg C CT L η s (β l)
          linarith
        linarith
  have hb2 : β 2 ≤ β N := hmono 2 N (by norm_num) hN
  have hstep1 : β 1 + Gstep C CT L η s (β 1) ≤ β 2 := hstep 1 le_rfl
  have hG : 2 * C * (s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ)
      ≤ Gstep C CT L η s (β 1) := by
    have hC1 : 0 ≤ 2 * C := by linarith
    have hraw : 2 * C * (s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ)
        ≤ 2 * C * (β 1 + s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      nlinarith [mul_nonneg hC1 hβ1]
    show _ ≤ max (1 + (η : ℝ))
      (2 * C * (β 1 + s + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ))
    exact le_trans hraw (le_max_right _ _)
  linarith

end JoinStep

/-! ## Axiom audit (source order) -/


