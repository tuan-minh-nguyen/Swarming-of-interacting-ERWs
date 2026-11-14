/-
# Scoped finite-`L` sharp-meet and merge geometry

The sharp lag is derived at the left run endpoint through `lag_le_sub`; the
movement clause stays half-open and right-end separation is a distinct premise.
The coarse corollaries dominate the gap by the whole-pack spread. They do not
construct a coalescence time, estimate `NoCoalescence`, or establish
impossibility of other finite-`L` routes.

No probability, invariant or stationary law, block clause, `dT` tightness or
velocity statement is supplied. Stale draft comments claiming an uncompiled
coalescence loop were removed during promotion; no theorem statement or proof
body was changed.
-/

import Swarm.EndpointHalving

open Finset
open scoped BigOperators

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. Inserting one walker into a top block -/

theorem sMax_insert_of_nonempty {X : ι → ℕ → ℤ} {D : Finset ι} {j : ι} {n : ℕ}
    (hD : D.Nonempty) (hj : j ∉ D) :
    sMax X (insert j D) n = max (X j n) (sMax X D n) := by
  have hS : (insert j D).Nonempty := Finset.insert_nonempty j D
  refine le_antisymm ?_ ?_
  · refine sMax_le hS (fun i hi => ?_)
    rcases Finset.mem_insert.mp hi with rfl | hiD
    · exact le_max_left _ _
    · exact le_trans (le_sMax hD hiD) (le_max_right _ _)
  · refine max_le ?_ ?_
    · exact le_sMax hS (Finset.mem_insert_self j D)
    · exact sMax_le hD (fun i hi => le_sMax hS (Finset.mem_insert_of_mem hi))

theorem sMin_insert_of_nonempty {X : ι → ℕ → ℤ} {D : Finset ι} {j : ι} {n : ℕ}
    (hD : D.Nonempty) (hj : j ∉ D) :
    sMin X (insert j D) n = min (X j n) (sMin X D n) := by
  have hS : (insert j D).Nonempty := Finset.insert_nonempty j D
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · exact sMin_le (X := X) (S := insert j D) (n := n) hS (Finset.mem_insert_self j D)
    · obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := D) (n := n) hD
      rw [hval]
      exact sMin_le (X := X) (S := insert j D) (n := n) hS (Finset.mem_insert_of_mem hi)
  · obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := insert j D) (n := n) hS
    rw [hval]
    rcases Finset.mem_insert.mp hi with rfl | hiD
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (sMin_le hD hiD)

/-- Adding one walker that is not above the block's maximum and not more than `b` below its
minimum increases the spread by at most `b`. -/
theorem spreadS_insert_le {X : ι → ℕ → ℤ} {D : Finset ι} {j : ι} {n : ℕ} {b : ℤ}
    (hD : D.Nonempty) (hj : j ∉ D) (hb : 0 ≤ b) (hmax : X j n ≤ sMax X D n)
    (hmin : sMin X D n ≤ X j n + b) :
    spreadS X (insert j D) n ≤ spreadS X D n + b := by
  have h1 : sMax X (insert j D) n = max (X j n) (sMax X D n) :=
    sMax_insert_of_nonempty hD hj
  have h2 : sMin X (insert j D) n = min (X j n) (sMin X D n) :=
    sMin_insert_of_nonempty hD hj
  have h3 : max (X j n) (sMax X D n) = sMax X D n := max_eq_right hmax
  have h4 : sMin X D n - b ≤ X j n := by linarith
  have h5 : sMin X D n - b ≤ min (X j n) (sMin X D n) := le_min h4 (by linarith)
  unfold spreadS
  rw [h1, h2, h3]
  linarith [h5]

/-! ## 2. The sharp meet bound `(meet)` at finite `L` -/

/-- **The paper's `(meet)` at finite `L`, with the sharp lag.**

`(sep)` for the split `(D, Dᶜ)` at both endpoints and on the half-open set `[s,t)` gives the
stated sharp bound. The gap `min_D X_s − max_{Dᶜ} M_s` is non-negative by `(sep)` and is
retained in the bound; callers must supply its upper estimate.
The lag is the sharp `η` of `(fluidmax)`, available on the subwindow `s ≥ τ_r+64⌈C⌉L` only; it is
supplied at the single time `s` by `lag_le_sub`. -/
theorem run_le_sharp {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hcl : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hHT : 0 ≤ CT) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    (hL1 : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : Numerics C CT L)
    (hT64 : 64 * Nat.ceil C ≤ T) (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {s t : ℕ} (hs0 : τ r + 64 * Nat.ceil C * L ≤ s) (hst : s < t) (ht : t ≤ τ r + T * L)
    (hsep : ∀ u, s ≤ u → u < t → Sep X D (Finset.univ \ D) u)
    (hsep_t : Sep X D (Finset.univ \ D) t) :
    ((t - s : ℕ) : ℝ)
      ≤ 2 * C ^ 2 * (((spreadS X D s : ℤ) : ℝ)
          + ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + (η : ℝ))
        + 2 * C * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hsr : τ r ≤ s := le_trans (Nat.le_add_right _ _) hs0
  have hsT : s ≤ τ r + T * L := le_trans (le_of_lt hst) ht
  have hLF : LocalField X τ H C CT T L r (L + η) := hcl.toField hτ hM hdr hηdef
  have hspread_nn : (0 : ℝ) ≤ ((spreadS X D s : ℤ) : ℝ) := by
    have h := spreadS_nonneg (X := X) (S := D) (n := s) hD
    exact_mod_cast h
  have hLag : ∀ j ∈ D, runMaxI X j s - X j s ≤ (η : ℤ) := fun j _ =>
    lag_le_sub X hτ hM hC hcl.occ hdr hL1 hij hnum hT64 hηdef hs0 hsT j
  have hLagJ : ∀ j ∈ Finset.univ \ D, runMaxI X j s - X j s ≤ (η : ℤ) := fun j _ =>
    lag_le_sub X hτ hM hC hcl.occ hdr hL1 hij hnum hT64 hηdef hs0 hsT j
  · have hsep_s : Sep X D (Finset.univ \ D) s := hsep s le_rfl hst
    -- `(Wpos)` at the right endpoint `t`
    have hWt : 0 ≤ Wst H X D (Finset.univ \ D) t :=
      Wst_nonneg_of_sep hLF.hmono hLF.hunit hsep_t
    -- `(locmove)` on the half-open set
    have hw := hLF.wmove D s t hD hD' hsr (le_of_lt hst) ht hsep
    -- `(loccoord)` in `W` form at the left endpoint, with the sharp `η`
    have hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X (Finset.univ \ D) s := by
      obtain ⟨i, hi, hval⟩ := exists_sMax (X := X) (S := Finset.univ \ D) (n := s)
        (Finset.sdiff_nonempty.mpr (by simpa using hD'))
      rw [hval]
      exact pos_ge_range (X := X) hτ hne hdr hsr hsT
    -- the gap at `s` is non-negative by `(sep)` (the displayed gap is at least `2`)
    have hgap0 : (0 : ℝ) ≤ ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) := by
      have h1 : sMaxM X (Finset.univ \ D) s + 2 ≤ sMin X D s := (hsep_s).gap
      have h3 : ((sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + 2 ≤ ((sMin X D s : ℤ) : ℝ) := by
        exact_mod_cast h1
      have h2 : (((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ)) : ℝ)
          = ((sMin X D s : ℤ) : ℝ) - ((sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) := by
        push_cast; ring
      rw [h2]
      linarith only [h3]
    have hWs := Wst_le_of_sep_lag (ηF := L + η) (η := η) hLF hC.le hsep_s hD' hsr hsT
      hlo hLagJ
    have hWs' : Wst H X D (Finset.univ \ D) s
        ≤ C * (((spreadS X D s : ℤ) : ℝ)
            + ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + (η : ℝ))
          + CT * (L : ℝ) ^ (3 / 4 : ℝ) := hWs
    -- the `(locmove)` right-hand side
    have hR : (((sMaxM X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ))
        ≤ ((spreadS X D s : ℤ) : ℝ) + (η : ℝ) := by
      have h2 : sMaxM X D s - sMax X D s ≤ (η : ℤ) := sMaxM_sub_sMax_le hD hLag
      have h3 : ((sMaxM X D s - sMax X D s : ℤ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast h2
      have h4 : ((spreadS X D s : ℤ) : ℝ)
          = ((sMax X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ) := by
        unfold spreadS; push_cast; ring
      have h5 : (((sMaxM X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ))
          = ((sMaxM X D s - sMax X D s : ℤ) : ℝ)
            + (((sMax X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ)) := by push_cast; ring
      rw [h5, h4]
      linarith
    set G : ℝ := ((spreadS X D s : ℤ) : ℝ)
      + ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + (η : ℝ) with hGdef
    have hGG : ((spreadS X D s : ℤ) : ℝ) + (η : ℝ) ≤ G := by
      rw [hGdef]; linarith
    have hCm : C * (((sMaxM X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ)) ≤ C * G :=
      mul_le_mul_of_nonneg_left (le_trans hR hGG) hC.le
    have hw' : Wst H X D (Finset.univ \ D) t - Wst H X D (Finset.univ \ D) s
        ≤ C * G - ((t - s : ℕ) : ℝ) / C + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      linarith [hw, hCm]
    have hWs2 : Wst H X D (Finset.univ \ D) s ≤ C * G + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hGdef]; linarith [hWs']
    have hdiv : ((t - s : ℕ) : ℝ) / C ≤ 2 * C * G + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      linarith [hw', hWt, hWs2]
    have hCf : ((t - s : ℕ) : ℝ) = C * (((t - s : ℕ) : ℝ) / C) := by
      field_simp
    have hfin : C * (((t - s : ℕ) : ℝ) / C)
        ≤ C * (2 * C * G + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv hC.le
    rw [hCf, hGdef] at *
    nlinarith [hfin, hGdef]

/-! ## 3. The post-failure meet bound and one merge round

The sharp meet bound of §2 carries the *gap* `min_D X_s − max_{Dᶜ} M_s` (which `(sep)` only
bounds *below*, by `2`).  That gap is the finite-`L` face of the source's `o(L)`: it is the
one quantity the deterministic clause package does **not** control, and it is exactly what the
compactness argument supplies at each merge (the limit coincidence `x_i = x_j`).  Away from the
first time of an analysis window the gap collapses to `2`, because `(sep)` failed at `s−1` and
the walks move by one step (`Glue.gap_at_failure`, no lag needed): this is the source's
"If `s>0` … `min_{i∈A}X_s^i ≤ max_{j∈A^c}M_s^j + 2`". -/

/-- **The post-failure meet bound.**  At the *start* `v` of a `(sep)`-run whose predecessor
fails, the gap term collapses to `2`, so `(meet)` reads
`t − v ≤ 2C²(spread_D(v) + 2 + 2η) + 2C·C_T L^{3/4}`. -/
theorem run_le_sharp_failure {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hcl : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hHT : 0 ≤ CT) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    (hL1 : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : Numerics C CT L)
    (hT64 : 64 * Nat.ceil C ≤ T) (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {v t : ℕ} (hv1 : 1 ≤ v) (hs0 : τ r + 64 * Nat.ceil C * L ≤ v) (hst : v < t)
    (ht : t ≤ τ r + T * L)
    (hnot : ¬ Sep X D (Finset.univ \ D) (v - 1))
    (hsep : ∀ u, v ≤ u → u < t → Sep X D (Finset.univ \ D) u)
    (hsep_t : Sep X D (Finset.univ \ D) t) :
    ((t - v : ℕ) : ℝ)
      ≤ 2 * C ^ 2 * (((spreadS X D v : ℤ) : ℝ) + 2 + 2 * (η : ℝ))
        + 2 * C * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hsr : τ r ≤ v := le_trans (Nat.le_add_right _ _) hs0
  have hsT : v ≤ τ r + T * L := le_trans (le_of_lt hst) ht
  have hce : 1 ≤ Nat.ceil C := by
    have h := Nat.ceil_pos.mpr hC
    omega
  have hvτ : τ r ≤ v - 1 := by
    have : τ r + 1 ≤ v := by
      have h1 : 1 * 1 ≤ Nat.ceil C * L := Nat.mul_le_mul hce hL1
      have h2 : τ r + 1 ≤ τ r + 64 * Nat.ceil C * L := by
        have : 64 * Nat.ceil C * L = 64 * (Nat.ceil C * L) := by ring
        nlinarith
      omega
    omega
  have hvT : v - 1 ≤ τ r + T * L := by omega
  have hpos : ∀ i, 0 ≤ X i (v - 1) := fun i => pos_nonneg (X := X) hτ hne hdr hvτ hvT hr
  have hgap : sMin X D v - sMaxM X (Finset.univ \ D) v ≤ (2 : ℤ) :=
    gap_at_failure (X := X) hne hD hD' hv1 hpos hnot
  have hgapR : ((sMin X D v - sMaxM X (Finset.univ \ D) v : ℤ) : ℝ) ≤ 2 := by
    exact_mod_cast hgap
  have hmain := run_le_sharp (η := η) hτ hne hcl hM hC hHT hdr hr hL1 hij hnum hT64 hηdef
    hD hD' hs0 hst ht hsep hsep_t
  have hη0 : (0 : ℝ) ≤ (η : ℝ) := by positivity
  have hsp : (0 : ℝ) ≤ ((spreadS X D v : ℤ) : ℝ) := by
    have h := spreadS_nonneg (X := X) (S := D) (n := v) hD
    exact_mod_cast h
  have hCnn : (0 : ℝ) ≤ C ^ 2 := by positivity
  have hkey : ((spreadS X D v : ℤ) : ℝ)
      + ((sMin X D v - sMaxM X (Finset.univ \ D) v : ℤ) : ℝ) + (η : ℝ)
      ≤ ((spreadS X D v : ℤ) : ℝ) + 2 + 2 * (η : ℝ) := by linarith
  have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 2 * C ^ 2)
  linarith [hmain, this]

/-- **A separated top block must merge within the bound.**  If `(sep)` holds at `s`, the gap at
`s` is at most `Bg`, and the integer step allowance `R` exceeds the sharp meet bound, then
`(sep)` fails at some time in `(s, s+R]`.  This is the source's `(meet)` as a *stopping*
statement: the run cannot reach the end of any window of length `R`. -/
theorem exists_failure_of_gap {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hcl : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hHT : 0 ≤ CT) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    (hL1 : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : Numerics C CT L)
    (hT64 : 64 * Nat.ceil C ≤ T) (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {s : ℕ} (hs0 : τ r + 64 * Nat.ceil C * L ≤ s)
    (hsep_s : Sep X D (Finset.univ \ D) s)
    {Bg : ℝ} (hBg : ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) ≤ Bg)
    {R : ℕ} (_hR1 : 1 ≤ R)
    (hstep : 2 * C ^ 2 * (((spreadS X D s : ℤ) : ℝ) + Bg + (η : ℝ))
      + 2 * C * CT * (L : ℝ) ^ (3 / 4 : ℝ) < (R : ℝ))
    (hRT : s + R ≤ τ r + T * L) :
    ∃ t, s < t ∧ t ≤ s + R ∧ ¬ Sep X D (Finset.univ \ D) t := by
  by_contra hcon
  push_neg at hcon
  have hsep : ∀ u, s ≤ u → u < s + R → Sep X D (Finset.univ \ D) u := by
    intro u h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact hsep_s
    · exact hcon u hlt (by omega)
  have hsep_t : Sep X D (Finset.univ \ D) (s + R) := hcon (s + R) (by omega) le_rfl
  have hmain := run_le_sharp (η := η) hτ hne hcl hM hC hHT hdr hr hL1 hij hnum hT64 hηdef
    hD hD' hs0 (by omega) hRT hsep hsep_t
  have hsub : ((spreadS X D s : ℤ) : ℝ)
      + ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + (η : ℝ)
      ≤ ((spreadS X D s : ℤ) : ℝ) + Bg + (η : ℝ) := by linarith
  have hmono : ((s + R - s : ℕ) : ℝ) ≤ (R : ℝ) := by simp
  have hb := mul_le_mul_of_nonneg_left hsub (by positivity : (0:ℝ) ≤ 2 * C ^ 2)
  rw [Nat.add_sub_cancel_left] at hmain
  linarith [hmain, hb, hstep]

/-! ### 3.1 One merge round

The top block `D` gains its best outside walker.  Two regimes: if `(sep)` already fails, the
walker is at the block's level at the same time (no time is spent); if `(sep)` holds, the
failure time is at most `R` steps away and the block's spread can only have grown by `2` per
step.  In both cases `insert j D` is again a **top block** of `D.card + 1` walkers. -/

/-- The best walker outside a top block, and the fact that adjoining it keeps a top block. -/
theorem exists_best_outside {X : ι → ℕ → ℤ} {D : Finset ι} {n : ℕ}
    (hD' : D ≠ Finset.univ) (htop : TopBlock X D n) :
    ∃ j, j ∉ D ∧ (∀ j' : ι, j' ∉ D → X j' n ≤ X j n) ∧ TopBlock X (insert j D) n := by
  have hJ : (Finset.univ \ D).Nonempty := Finset.sdiff_nonempty.mpr (by simpa using hD')
  obtain ⟨j, hj, hval⟩ := exists_sMax (X := X) (S := Finset.univ \ D) (n := n) hJ
  have hjn : j ∉ D := (Finset.mem_sdiff.mp hj).2
  refine ⟨j, hjn, ?_, ?_⟩
  · intro j' hj'
    have hmem : j' ∈ Finset.univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j', hj'⟩
    rw [← hval]
    exact le_sMax hJ hmem
  · intro i hi i' hi'
    have hi'D : i' ∉ D := by
      intro hcin; exact hi' (Finset.mem_insert_of_mem hcin)
    rcases Finset.mem_insert.mp hi with rfl | hiD
    · have hmem : i' ∈ Finset.univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i', hi'D⟩
      rw [← hval]
      exact le_sMax hJ hmem
    · exact htop i hiD i' hi'D

/-- **The merge without spending time.**  If `(sep)` fails for `(D, Dᶜ)` at `n`, then adjoining
the best outside walker keeps a top block and increases the spread by at most `1 + η`. -/
theorem merge_at_start {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hcl : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r) (hL1 : 1 ≤ L)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {n : ℕ} (hn0 : τ r + 64 * Nat.ceil C * L ≤ n) (hnT : n ≤ τ r + T * L)
    (htop : TopBlock X D n) (hnot : ¬ Sep X D (Finset.univ \ D) n) :
    ∃ j, j ∉ D ∧ TopBlock X (insert j D) n ∧ (insert j D).card = D.card + 1 ∧
      spreadS X (insert j D) n ≤ spreadS X D n + (1 + (η : ℤ)) := by
  obtain ⟨j, hjn, hbest, htop'⟩ := exists_best_outside hD' htop
  have hJ : (Finset.univ \ D).Nonempty := Finset.sdiff_nonempty.mpr (by simpa using hD')
  have hsr : τ r ≤ n := le_trans (Nat.le_add_right _ _) hn0
  have hposn : ∀ i ∈ D, 0 ≤ X i n := fun i _ => pos_nonneg (X := X) hτ hne hdr hsr hnT hr
  have hpair : ∃ i ∈ D, ∃ j' ∈ Finset.univ \ D, X i n ≤ runMaxI X j' n + 1 := by
    by_contra hcon
    apply hnot
    refine ⟨hposn, hD, hJ, ?_⟩
    intro i hi j' hj'
    by_contra hle
    push_neg at hle
    exact hcon ⟨i, hi, j', hj', by omega⟩
  obtain ⟨i, hi, j', hj', hle⟩ := hpair
  have hj'D : j' ∉ D := (Finset.mem_sdiff.mp hj').2
  have hlag : runMaxI X j' n - X j' n ≤ (η : ℤ) :=
    lag_le_sub X hτ hM hC hcl.occ hdr hL1 hij hnum hT64 hηdef hn0 hnT j'
  have hlagJ : ∀ x ∈ Finset.univ \ D, runMaxI X x n - X x n ≤ (η : ℤ) := fun x _ =>
    lag_le_sub X hτ hM hC hcl.occ hdr hL1 hij hnum hT64 hηdef hn0 hnT x
  have hsmax : sMax X (Finset.univ \ D) n = X j n := by
    rw [sMax_of_nonempty hJ]
    exact le_antisymm (Finset.sup'_le hJ _ (fun x hx => hbest x (Finset.mem_sdiff.mp hx).2))
      (Finset.le_sup' (fun x => X x n) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjn⟩))
  have hMax : sMaxM X (Finset.univ \ D) n ≤ X j n + (η : ℤ) := by
    have h := sMaxM_sub_sMax_le (X := X) (J := Finset.univ \ D) (n := n) hJ hlagJ
    linarith [hsmax]
  have hmin_le : sMin X D n ≤ X j n + (1 + (η : ℤ)) := by
    have h1 : sMin X D n ≤ X i n := sMin_le hD hi
    have h2 : runMaxI X j' n ≤ sMaxM X (Finset.univ \ D) n := le_sMaxM (X := X) (n := n) hJ hj'
    omega
  have hmax : X j n ≤ sMax X D n := by
    obtain ⟨i0, hi0, hval⟩ := exists_sMin (X := X) (S := D) (n := n) hD
    have h1 : X j n ≤ X i0 n := htop i0 hi0 j hjn
    rw [← hval] at h1
    exact le_trans h1 (sMin_le_sMaxX hD)
  exact ⟨j, hjn, htop', Finset.card_insert_of_notMem hjn,
    spreadS_insert_le hD hjn (by omega) hmax hmin_le⟩

/-! ## 4. Coarse gap domination by whole-pack spread

`run_le_sharp` retains the explicit gap `min_D X_s − max_{Dᶜ} M_s`. The following
lemmas bound it above by the whole-pack spread and record the resulting coarse
meet estimate. No compactness or coalescence premise is added. These bounds do
not supply an `o(L)` small-spread time, and they are not an impossibility proof
for finite-`L` arguments not formalised here. The post-failure sharp bound is a
separate case in which the gap is bounded by `2`. -/

/-- The gap is at most the whole-pack spread: the only bound the clause package supplies. -/
theorem gap_le_spread_univ_of_top {X : ι → ℕ → ℤ} {D : Finset ι} {n : ℕ} (hD : D.Nonempty)
    (hD' : D ≠ Finset.univ) :
    sMin X D n - sMaxM X (Finset.univ \ D) n ≤ spreadS X Finset.univ n := by
  have hJ : (Finset.univ \ D).Nonempty := Finset.sdiff_nonempty.mpr (by simpa using hD')
  have h1 : sMax X (Finset.univ \ D) n ≤ sMaxM X (Finset.univ \ D) n :=
    sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
  have h2 : sMin X D n - sMax X (Finset.univ \ D) n ≤ spreadS X Finset.univ n := by
    have h := JoinStep.gap_le_spread_univ (X := X) (I := D) (n := n) hD hJ
    exact_mod_cast h
  omega

/-- **The meet bound with the only available gap bound.**  A `(sep)`-run of the split `(D, Dᶜ)`
lasts at most `2C²(2·spread_ι(s) + η) + 2C C_T L^{3/4}` steps — proportional to the *whole-pack*
spread at the run start, not to the block's spread.  Combined with `spreadS_le_of_le` and the
carrier `d_r ≤ L` this is `O(C²·L)`: the deterministic clauses time each merge by the whole-pack
spread. This particular coarse route does not produce an `o(L)` coalescence time;
other finite-`L` arguments are neither ruled out nor supplied here. -/
theorem run_le_sharp_coarse {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ}
    (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hcl : LocalClauses X τ H C CT T L r) (hM : MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hHT : 0 ≤ CT) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    (hL1 : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : Numerics C CT L)
    (hT64 : 64 * Nat.ceil C ≤ T) (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {s t : ℕ} (hs0 : τ r + 64 * Nat.ceil C * L ≤ s) (hst : s < t) (ht : t ≤ τ r + T * L)
    (hsep : ∀ u, s ≤ u → u < t → Sep X D (Finset.univ \ D) u)
    (hsep_t : Sep X D (Finset.univ \ D) t) :
    ((t - s : ℕ) : ℝ)
      ≤ 2 * C ^ 2 * (2 * ((spreadS X Finset.univ s : ℤ) : ℝ) + (η : ℝ))
        + 2 * C * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hmain := run_le_sharp (η := η) hτ hne hcl hM hC hHT hdr hr hL1 hij hnum hT64 hηdef
    hD hD' hs0 hst ht hsep hsep_t
  have hgap : ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ)
      ≤ ((spreadS X Finset.univ s : ℤ) : ℝ) := by
    have h := gap_le_spread_univ_of_top (X := X) (D := D) (n := s) hD hD'
    exact_mod_cast h
  have hkey : ((spreadS X D s : ℤ) : ℝ)
      + ((sMin X D s - sMaxM X (Finset.univ \ D) s : ℤ) : ℝ) + (η : ℝ)
      ≤ 2 * ((spreadS X Finset.univ s : ℤ) : ℝ) + (η : ℝ) := by
    have hsp : ((spreadS X D s : ℤ) : ℝ) ≤ ((spreadS X Finset.univ s : ℤ) : ℝ) := by
      have h := spreadS_subset (X := X) (S := D) (T := Finset.univ) (n := s) hD
        (Finset.subset_univ D)
      exact_mod_cast h
    linarith
  have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 2 * C ^ 2)
  linarith [hmain, this]
