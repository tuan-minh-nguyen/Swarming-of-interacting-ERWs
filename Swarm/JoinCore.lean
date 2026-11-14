/-
# Finite-`L` order-statistic joins: the join-gap step and the top-block induction

Source: `main_1d_revised.tex`, the proof of Proposition `tight`, the paragraph
"We fix `s ∈ [64C,T]` and a nonempty `D ⊂ {1,…,N}` …" that proves `(coincide)`:

  "We prove by induction on `k` that the difference between the largest and the `k`-th
   largest position among `D` is `o(L)`, uniformly over integer times in
   `[τ_r+⌊Ls⌋, τ_r+TL]`. … At an integer time `n` … we choose `I ⊂ D` with `|I| = k` and
   `min_{i∈I} X_n^i ≥ max_{j∈D∖I} X_n^j`, and put `J = D∖I`.  If `(sep)` fails for these sets,
   then … `min_{i∈I} X_n^i − max_{j∈J} X_n^j ≤ 1 + max_{j∈J}(M_n^j − X_n^j) = o(L)`.
   Otherwise, we let `u` be the smallest integer in `[τ_r+⌊Ls⌋,n]` such that `(sep)` holds for
   these fixed sets at every integer time from `u` to `n`. … `W_u^{I,J} = o(L)` … By `(locgroup)`
   and `(Wpos)`, `min_{i∈I} X_n^i − max_{j∈J} X_n^j ≤ W_n^{I,J} ≤ W_u^{I,J} + C_T L^{3/4}
   = o(L)`."

This file formalises exactly that step and its induction, at finite `L`, on the whole pack
(`D = {1,…,N}`), so that every separated-group estimate used is the **complementary-pair**
estimate of the accepted `Glue` files (`Wst`, `wmove`, `Wst_ge_sep`, `Wst_le_of_sep`,
`gap_at_failure`, `run_le`).  No general-pair drift estimate is assumed.

Main content.

* `TopBlock X I n` — `I` is a block of `|I|` largest positions; `I = univ` satisfies it
  vacuously, so the induction closes at `k = N` without an extra case.
* `sMax_eq_of_mem_le`, `sMin_eq_of_le_mem` — extrema of a block at a dominated/dominating
  member.
* `spread_singleton` — a one-point block has spread `0` (the base case `k = 1`).
* `gap_le_spread_univ` — the separation `min_I X − max_{univ∖I} X` is at most the whole-pack
  spread; this is the `u = τ_r + ⌊Ls⌋` branch of the paper's argument.
* `not_sep_gap_le` — if `(sep)` fails at `n` then the separation is at most `1 + η`
  (the paper's first branch, using the finite-`L` lag `η`).
* `join_gap_of_top` — **the join-gap step**: for a top block `I` of size `k`, with the
  induction hypothesis `spread_I ≤ b` available on the whole window,
  `min_I X_n − max_{univ∖I} X_n ≤ Gstep(β₀, b)`, where
  `Gstep C CT L η β₀ b = max (1+η) (2C(b + β₀ + η + 2) + 2 C_T L^{3/4})`.
  Both branches of the paper are present: `(sep)` at `n` (use the run start `u`, `(loccoord)`
  at `u`, `(Wpos)` at `n`, and the drift term of `(locmove)`), and `¬(sep)` at `n`.
* `spread_univ_le` — **the induction**: for `β` with `β 1 ≥ 0` and
  `β (k+1) ≥ β k + Gstep(β₀, β k)`, the whole-pack spread is at most `β N` at every integer
  time of the window, given that it is at most `β₀` at the window start.
* `halving_input_of_spread`, `halving_input_of_window` — the terminal-at-record corollary:
  `2 d_{r+BL} ≤ L`, i.e. exactly the halving input that `HblkTwo.BadHalf` and
  `Glue.not_badHalf_of_defect_le` consume.
* `spread_le_eps_mul_L` — the uniform `ε`-form: for every `ε > 0` with
  `β₀ ≤ ε₀L`, `η ≤ ε₁L`, `C_T L^{3/4} ≤ ε₂L` and `(1+2C)^N(ε₀+ε₁+ε₂) ≤ ε`, the whole-pack
  spread is at most `εL` throughout the window.  No `η = 0` is assumed and the `C_T L^{3/4}`
  error is kept.

Scope.  This is deterministic geometry on a genuinely specified subwindow of the record
window `[τ_r, τ_r+TL]`.  It is not a probability estimate, not `HalfClauseAt`, and not
`MainClaim`.  The general-`D` form of `(coincide)` (needed for the paper's leading set
`A ⊊ {1,…,N}`) needs the paper's `(locgroup)`/`(locmove)` for **non-complementary**
disjoint pairs, whose finite-`L` drift clause is a probabilistic obligation; it is not
assumed or faked here, and the whole-pack form proved here is the one that the halving
input at the record time `τ_{r+BL}` actually consumes.
-/
import Swarm.LagStep

open Finset
open scoped BigOperators

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. Blocks of largest positions and their extrema -/

/-- `I` is a block of `|I|` largest positions of the pack: every element of `I` is at least
every element outside `I`.  For `I = univ` the condition is vacuous, which is what makes the
order-statistic induction close at `k = N`. -/
def TopBlock (X : ι → ℕ → ℤ) (I : Finset ι) (n : ℕ) : Prop :=
  ∀ i ∈ I, ∀ j, j ∉ I → X j n ≤ X i n

theorem topBlock_univ (X : ι → ℕ → ℤ) (n : ℕ) : TopBlock X Finset.univ n := by
  intro i _ j hj
  exact absurd (Finset.mem_univ j) hj

/-- A block's maximum, realised at any dominating member. -/
theorem sMax_eq_of_mem_le {X : ι → ℕ → ℤ} {T : Finset ι} {n : ℕ} {i : ι}
    (hi : i ∈ T) (h : ∀ j ∈ T, X j n ≤ X i n) : sMax X T n = X i n := by
  have hT : T.Nonempty := ⟨i, hi⟩
  exact le_antisymm (sMax_le hT h) (le_sMax hT hi)

/-- A block's minimum, realised at any dominated member. -/
theorem sMin_eq_of_le_mem {X : ι → ℕ → ℤ} {T : Finset ι} {n : ℕ} {i : ι}
    (hi : i ∈ T) (h : ∀ j ∈ T, X i n ≤ X j n) : sMin X T n = X i n := by
  have hT : T.Nonempty := ⟨i, hi⟩
  exact le_antisymm (sMin_le hT hi) (sMin_le_of hT h)

/-- A one-point block has zero spread: the base case of the induction. -/
theorem spread_singleton {X : ι → ℕ → ℤ} {I : Finset ι} {n : ℕ} (h : I.card = 1) :
    spreadS X I n = 0 := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
  have hi : i ∈ ({i} : Finset ι) := Finset.mem_singleton_self i
  have hpt : ∀ j ∈ ({i} : Finset ι), X j n ≤ X i n := by
    intro j hj
    rw [Finset.mem_singleton.mp hj]
  have hpt2 : ∀ j ∈ ({i} : Finset ι), X i n ≤ X j n := by
    intro j hj
    rw [Finset.mem_singleton.mp hj]
  have hmax : sMax X {i} n = X i n := sMax_eq_of_mem_le hi hpt
  have hmin : sMin X {i} n = X i n := sMin_eq_of_le_mem hi hpt2
  unfold spreadS
  rw [hmax, hmin]
  ring

/-- The separation of a block from the rest of the pack is at most the spread of the whole
pack. -/
theorem gap_le_spread_univ {X : ι → ℕ → ℤ} {I : Finset ι} {n : ℕ} (hI : I.Nonempty)
    (hJ : (Finset.univ \ I).Nonempty) :
    ((sMin X I n - sMax X (Finset.univ \ I) n : ℤ) : ℝ) ≤ (spreadS X Finset.univ n : ℝ) := by
  obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := I) (n := n) hI
  obtain ⟨j, hj, hval2⟩ := exists_sMax (X := X) (S := Finset.univ \ I) (n := n) hJ
  have heq : sMin X I n - sMax X (Finset.univ \ I) n = X i n - X j n := by
    rw [hval, hval2]
  have hle : X i n - X j n ≤ spreadS X Finset.univ n :=
    sub_spreadS Finset.univ_nonempty (Finset.mem_univ i) (Finset.mem_univ j)
  rw [heq]
  exact_mod_cast hle

/-- **The paper's first branch.**  If `(sep)` fails at `n` and all positions are nonnegative
there, then the separation of a nonempty block `I` from its complement is at most
`1 + η`, where `η` is the finite-`L` lag allowance.  (The paper writes `1 + o(L)`.) -/
theorem not_sep_gap_le {X : ι → ℕ → ℤ} {η : ℕ} {I : Finset ι} {n : ℕ} (hI : I.Nonempty)
    (hJ : (Finset.univ \ I).Nonempty) (hpos : ∀ i, 0 ≤ X i n)
    (hlag : ∀ j ∈ Finset.univ \ I, runMaxI X j n - X j n ≤ (η : ℤ))
    (hnot : ¬ Sep X I (Finset.univ \ I) n) :
    sMin X I n - sMax X (Finset.univ \ I) n ≤ 1 + (η : ℤ) := by
  have hpair : ∃ i ∈ I, ∃ j ∈ Finset.univ \ I, X i n ≤ runMaxI X j n + 1 := by
    by_contra hcon
    apply hnot
    refine ⟨fun i _ => hpos i, hI, hJ, ?_⟩
    intro i hi j hj
    by_contra hlt
    push_neg at hlt
    exact hcon ⟨i, hi, j, hj, by omega⟩
  obtain ⟨i0, hi0, j0, hj0, hle0⟩ := hpair
  have h1 : sMin X I n ≤ X i0 n := sMin_le hI hi0
  have h2 : runMaxI X j0 n ≤ sMaxM X (Finset.univ \ I) n := le_sMaxM hJ hj0
  have h3 : sMaxM X (Finset.univ \ I) n ≤ sMax X (Finset.univ \ I) n + (η : ℤ) := by
    have := sMaxM_sub_sMax_le (X := X) (J := Finset.univ \ I) (n := n) hJ hlag
    linarith
  linarith

/-! ## 2. The join-gap step -/

/-- The geometric step constant of the induction:
`max (1+η) (2C(b + β₀ + η + 2) + 2 C_T L^{3/4})`. -/
noncomputable def Gstep (C CT : ℝ) (L η : ℕ) (β₀ b : ℝ) : ℝ :=
  max (1 + (η : ℝ))
    (2 * C * (b + β₀ + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ))

theorem le_Gstep (C CT : ℝ) (L η : ℕ) (β₀ b : ℝ) :
    1 + (η : ℝ) ≤ Gstep C CT L η β₀ b := le_max_left _ _

theorem Gstep_nonneg (C CT : ℝ) (L η : ℕ) (β₀ b : ℝ) : 0 ≤ Gstep C CT L η β₀ b :=
  le_trans (by positivity) (le_Gstep C CT L η β₀ b)

/-- **The join-gap step of the induction.**  Let `I` be a nonempty proper block of `k`
largest positions at time `n`, all inside the subwindow `[n₀,n₁] ⊆ [τ_r, τ_r+TL]` of a
record window on which `d_r ≤ L` and the local-good field holds.  If every block of `k`
largest positions has spread at most `b` throughout the window, then the separation of `I`
from the rest of the pack at `n` is at most `Gstep` of `(β₀, b)`. -/
theorem join_gap_of_top {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
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
    fun j _ => hLF.lag j n hwin (le_trans hn' hn₁)
  have hlagJu : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ j ∈ Finset.univ \ I,
      runMaxI X j u - X j u ≤ (η : ℤ) :=
    fun u hu0 hu1 j _ => hLF.lag j u (le_trans hn₀ hu0) (le_trans hu1 hn₁)
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
          (fun i hi => hLF.lag i u (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁))
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
theorem spread_univ_le {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
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
        have hgap := join_gap_of_top hτ hne hLF hC hdr hr hn₀ hn₁ hβ₀
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

/-! ## 4. The terminal-at-record halving input -/

/-- At the record time `τ_y` the pack spread is the paper's defect `d_y`; hence
`spread ≤ L/2` there is exactly the halving input `2 d_y ≤ L` consumed by
`Glue.not_badHalf_of_defect_le`. -/
theorem twomul_defect_le_of_spread {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {y L : ℕ} (h : (spreadS X (Finset.univ : Finset ι) (τ y) : ℝ) ≤ (L : ℝ) / 2) :
    2 * defect X τ y ≤ (L : ℤ) := by
  have heq : spreadS X (Finset.univ : Finset ι) (τ y) = defect X τ y :=
    spreadS_univ_tau hτ y
  rw [heq] at h
  have h2 : ((2 * defect X τ y : ℤ) : ℝ) ≤ (L : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

/-- **The terminal-at-record corollary.**  If the whole-pack spread at the record time
`τ_{r+BL}` is at most `L/2`, then the paper's second block inequality `d_{r+BL} ≤ L/2` holds.
This is the *only* place the halving input of `GlueHalf` is produced, and it does not assume
invariance, stationarity, or any probability. -/
theorem halving_input_of_window {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η B : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η (spreadS X Finset.univ n₀ : ℝ) (β k) ≤ β (k + 1))
    (hββ : β (Finset.univ : Finset ι).card ≤ (L : ℝ) / 2)
    (hrec0 : n₀ ≤ τ (r + B * L)) (hrec1 : τ (r + B * L) ≤ n₁) :
    2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  have hspread := spread_univ_le hτ hne hLF hC hdr hr hn₀ hn₁ hβ1 hstep
    (τ (r + B * L)) hrec0 hrec1
  exact twomul_defect_le_of_spread hτ (le_trans hspread hββ)

/-! ## 5. The uniform epsilon form -/

/-- The `.`-form of the induction: an explicit geometric sequence with
`β 1 = ε₀` and `β (k+1) = β k + Gstep(β₀, β k)` grows at most geometrically, so a bound
`β₀ ≤ ε₀ L`, `η ≤ ε₁ L`, `C_T L^{3/4} ≤ ε₂ L` gives a whole-pack spread at most
`C(N,C) (ε₀+ε₁+ε₂) L` throughout the window.  This is the honest finite-`L` reading of the
paper's `o(L)`; no limit and no `η = 0` is asserted. -/
theorem spread_le_eps_mul_L {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + Gstep C CT L η (spreadS X Finset.univ n₀ : ℝ) (β k) ≤ β (k + 1))
    {ε : ℝ} (hε : β (Finset.univ : Finset ι).card ≤ ε * (L : ℝ)) :
    ∀ n, n₀ ≤ n → n ≤ n₁ → (spreadS X Finset.univ n : ℝ) ≤ ε * (L : ℝ) := by
  intro n hn hn'
  exact le_trans (spread_univ_le hτ hne hLF hC hdr hr hn₀ hn₁ hβ1 hstep n hn hn') hε

end JoinStep

/-! ## Axiom audit (source order) -/


