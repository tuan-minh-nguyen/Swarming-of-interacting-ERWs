/-
# The sharp `(coincide)` after `64⌈C⌉L`: class spread from the measured clauses

`M4Coincide.stickyOn_of_grid` (public `CoincideFluid`) needs `Glue.LocalField` with a
**whole-window** lag clause `LocalField.lag`, i.e. `runMaxI X i n - X i n ≤ η` for every
`n ∈ [τ_r, τ_r + TL]`.  That clause is not provable with `η = o(L)`: `LagFromMart.lag_le_window`
gives only `L + ⌈C_T L^{3/4}⌉` on the whole window (the `+L` is genuine, because at `n = τ_r`
the lag *is* `d_r ≤ L`), while the sharp bound `LagFromMart.lag_le_sub`
`runMaxI X i n - X i n ≤ ⌈C_T L^{3/4}⌉` holds only on the subwindow
`[τ_r + 64⌈C⌉L, τ_r + TL]`.

This file removes the whole-window lag from the class-spread induction of `CoincideClass`:
the local field may be built at *any* allowance `ηF` (in practice the coarse
`L + ⌈C_T L^{3/4}⌉` of `LocalClauses.toField`), and the sharp allowance `η` enters only
through an explicit hypothesis `hlagw` on `[n₀, n₁]` with `n₀ = τ_r + 64⌈C⌉L`.  The price is
that the induction must start at `n₀ ≤ s`, which is exactly the source's own window origin
`m_i(u) = x_i(u)` for `u ≥ 64C`: **no coincidence is claimed before `64⌈C⌉L`**.

* `Wpot_le_of_sep_lag`, `gap_le_of_localGood_lag`, `spreadS_le_of_localGood_lag`,
  `spreadS_le_scaled_lag`, `classSpread_tendsto_lag` — the sharp versions of the public
  `M4Coincide` class-spread chain.  They strictly generalise the public statements: the
  public `spreadS_le_of_localGood` etc. are recovered by taking `n₀ = τ_r`,
  `n₁ = τ_r + TL` and `hlagw` from `LocalField.lag`.
* `pairwise_of_grid_lag`, `stickyOn_of_grid_sharp`, `coincideOn_of_grid_sharp` — the
  pairwise `(4.8)` and the fluid `(coincide)` from knotwise convergence, now with the
  honest window origin `64⌈C⌉`.
* `stickyOn_of_clauses` — the same conclusion from the *measured* clauses
  `JoinStep.LocalClauses + JoinStep.MartClause` (plus `(locgroup)`, the carrier `d_r ≤ L`,
  the numerical thresholds and `η_n/L_n → 0`): the field is built by
  `LocalClauses.toField` and the sharp lag by `LagFromMart.lag_le_sub`, so neither
  `LocalField` nor its lag is left as a premise.

Scope.  Deterministic (no probability, no `arrayMeasure`, no `NoCoalescence`, no
stationarity).  The remaining inputs are named: the literal record and step-one paths, the
Proposition-`local` clauses, `(locmart)`, `(locgroup)`, the carrier `{d_r ≤ L}`, the
numerical thresholds, the vanishing normalized allowance and knotwise convergence of the
scaled positions (or, for the fluid form, the lifted limit).  Nothing here is a velocity,
a tightness statement, or a claim about actual trajectories.
-/
import Swarm.CoincideFluid
import Swarm.EndpointHalving
import Swarm.LagFromMart

open Finset Filter Topology
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Sharp

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid M4Coincide

/-! ## 1. The potential comparison with a separately supplied lag -/

/-- `(loccoord)` for `Wpot`, the paper's "apply `(loccoord)` with `A = J^c`" step: on `(sep)`,
`W_n^{I,J} ≤ C·(spread_I(n) + gap_J(n) + η) + C_T L^{3/4}`, where
`gap_J(n) = min_I X_n − max_J M_n ≥ 2` is the separation (not the record lag). -/
theorem Wpot_le_of_sep_lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ}
    {T L r ηF η : ℕ} (hLF : LocalField X τ H C CT T L r ηF) (hC : 0 ≤ C) {A I J : Finset ι}
    {n : ℕ} (hIA : I ⊆ A) (hsep : Sep X I J n) (hAne : A ≠ Finset.univ)
    (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J n)
    (hlagS : ∀ j ∈ J, runMaxI X j n - X j n ≤ (η : ℤ)) :
    Wpot H X A I J n ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ)
      + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  have hAne' : A.Nonempty := hI.mono hIA
  have hsup : (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) :=
    sup_H_eq hLF.hmono hJ
  rw [Wpot_of_nonempty (H := H) (X := X) (A := A) (I := I) (n := n) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      ≤ ((H A n (sMax X I n) : ℤ) : ℝ) := by
    rw [div_le_iff₀ hcard]
    have hb : ∀ i ∈ I, H A n (X i n) ≤ H A n (sMax X I n) := by
      intro i hi
      exact hLF.hmono A n (le_sMax hI hi)
    calc (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ))
        ≤ ∑ _i ∈ I, ((H A n (sMax X I n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
      _ = ((H A n (sMax X I n) : ℤ) : ℝ) * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb0 : sMax X I n ≤ sMaxM X A n :=
    le_trans (sMax_le_sMaxM hI n) (sMaxM_mono hI hIA n)
  have hle0 : sMax X J n ≤ sMax X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    have hle3 : sMin X I n ≤ sMax X I n := sMin_le_sMaxX hI
    linarith
  have hcoord := hLF.hcoord A n hAne' hAne h1 h2 (sMax X J n) (sMax X I n) hlo hle0 hb0
  have hlagJ : (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) ≤ (η : ℝ) := by
    have h := sMaxM_sub_sMax_le hJ hlagS
    exact_mod_cast h
  have hcast1 : (((sMax X I n - sMax X J n : ℤ)) : ℝ)
      = ((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ)
        + (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) := by
    unfold spreadS
    push_cast
    ring
  have hcoord' : ((H A n (sMax X I n) - H A n (sMax X J n) : ℤ) : ℝ)
      ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ) + (η : ℝ))
        + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hcast1] at hcoord
    have hmul : C * (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ))
        ≤ C * (η : ℝ) := mul_le_mul_of_nonneg_left hlagJ hC
    linarith
  have hsplit2 : ((H A n (sMax X I n) : ℤ) : ℝ) - ((H A n (sMax X J n) : ℤ) : ℝ)
      = ((H A n (sMax X I n) - H A n (sMax X J n) : ℤ) : ℝ) := by push_cast; ring
  linarith [hcoord', havg, hsplit2]


/-! ## 2. The class-spread induction with the sharp post-`64⌈C⌉L` lag -/

theorem gap_le_of_localGood_lag
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r ηF η : ℕ}
    (hLF : LocalField X τ H C CT T L r ηF) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {D : Finset ι} (hD : D.Nonempty) {s n : ℕ} (hs : n₀ ≤ s) (hsn : s ≤ n)
    (hn : n ≤ n₁)
    {k : ℕ} {E : ℝ}
    (hE : ∀ (v : ℕ) (S : Finset ι), s ≤ v → v ≤ n → S ⊆ D → S.Nonempty → S.card = k →
      (∀ i ∈ S, ∀ j ∈ D, j ∉ S → X j v ≤ X i v) → ((spreadS X S v : ℤ) : ℝ) ≤ E)
    (hE0 : ((spreadS X D s : ℤ) : ℝ) ≤ E)
    {v : ℕ} (hsv : s ≤ v) (hvn : v ≤ n)
    {S : Finset ι} (hSD : S ⊆ D) (hSne : S.Nonempty) (hJSne : (D \ S).Nonempty)
    (hScard : S.card = k) (hSupper : ∀ i ∈ S, ∀ j ∈ D, j ∉ S → X j v ≤ X i v) :
    ((sMin X S v - sMax X (D \ S) v : ℤ) : ℝ) ≤
      C * (E + (η : ℝ) + 2) + 2 * (CT * (L : ℝ) ^ (3 / 4 : ℝ)) + ((η : ℝ) + 2) := by
  classical
  set a : ℝ := CT * (L : ℝ) ^ (3 / 4 : ℝ) with ha_def
  have hann : 0 ≤ a := by
    rw [ha_def]
    exact mul_nonneg hCT (Real.rpow_nonneg (Nat.cast_nonneg L) _)
  have hCnn : 0 ≤ C := le_trans zero_le_one hC1
  have hηnn : (0 : ℝ) ≤ (η : ℝ) := Nat.cast_nonneg η
  set J : Finset ι := D \ S with hJdef
  have hJne : J.Nonempty := by rw [hJdef]; exact hJSne
  have hDJ : D = S ∪ J := by rw [hJdef]; exact (Finset.union_sdiff_of_subset hSD).symm
  have hvn₁ : v ≤ n₁ := le_trans hvn hn
  have hnT : n ≤ τ r + T * L := le_trans hn hn₁
  have hvnT : v ≤ τ r + T * L := le_trans hvn₁ hn₁
  have hpos : ∀ x, s ≤ x → x ≤ n → ∀ i, 0 ≤ X i x := fun x h1 h2 i =>
    pos_nonneg hτ hne hdr (le_trans (le_trans hn₀ hs) h1) (le_trans (le_trans h2 hn) hn₁) hrT
  have hposv : ∀ i ∈ S, 0 ≤ X i v := fun i hi => hpos v hsv hvn i
  have hrange : ∀ x, s ≤ x → x ≤ n → ∀ i,
      (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ X i x := fun x h1 h2 i =>
    pos_ge_range hτ hne hdr (le_trans (le_trans hn₀ hs) h1) (le_trans (le_trans h2 hn) hn₁)
  have hlag : ∀ x, s ≤ x → x ≤ n → sMaxM X J x - sMax X J x ≤ (η : ℤ) := fun x h1 h2 =>
    sMaxM_sub_sMax_le hJne (fun j hj => hlagw j x (le_trans hs h1) (le_trans h2 hn))
  have hlagv : sMaxM X J v - sMax X J v ≤ (η : ℤ) := hlag v hsv hvn
  have hcastη : ((sMaxM X J v : ℤ) : ℝ) - ((sMax X J v : ℤ) : ℝ) ≤ (η : ℝ) := by
    exact_mod_cast hlagv
  have hnn2 : ∀ (i : ι) (x : ℕ), X i (x + 1) ≤ X i x + 1 := by
    intro i x
    have h := hne i x
    have h1 : X i (x + 1) - X i x ≤ (1 : ℤ) := by
      have h2 := le_abs_self (X i (x + 1) - X i x)
      rw [h] at h2; exact h2
    omega
  have hgoal : ((sMin X S v - sMax X J v : ℤ) : ℝ) ≤ C * (E + (η : ℝ) + 2) + 2 * a
      + ((η : ℝ) + 2) := by
    by_cases hsepv : Sep X S J v
    · -- Case 2: `(sep)` holds at `v`
      have hIA : S ⊆ Finset.univ \ J := by
        intro i hi
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ i, fun hc => (Finset.mem_sdiff.mp hc).2 hi⟩
      have hAne : Finset.univ \ J ≠ (Finset.univ : Finset ι) := by
        intro h
        have hja : hJne.choose ∉ Finset.univ \ J :=
          fun hc => (Finset.mem_sdiff.mp hc).2 hJne.choose_spec
        rw [h] at hja
        exact hja (Finset.mem_univ _)
      have hWv : ((sMin X S v - sMax X J v : ℤ) : ℝ)
          ≤ Wpot H X (Finset.univ \ J) S J v := Wpot_ge_gap hLF.hmono hLF.hunit hsepv
      set F : Finset ℕ := (Finset.Icc s v).filter (fun x => ¬ Sep X S J x) with hFdef
      by_cases hF : F.Nonempty
      · -- a last failing time `w` exists; use `w + 1`
        set w : ℕ := F.max' hF with hwdef
        have hwF : w ∈ F := Finset.max'_mem F hF
        have hwmem : s ≤ w ∧ w ≤ v := Finset.mem_Icc.mp (Finset.mem_filter.mp hwF).1
        have hwfail : ¬ Sep X S J w := (Finset.mem_filter.mp hwF).2
        have hsep_after : ∀ x, w < x → x ≤ v → Sep X S J x := by
          intro x h1 h2
          by_contra hcon
          have hxF : x ∈ F :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans hwmem.1 (le_of_lt h1), h2⟩, hcon⟩
          have := Finset.le_max' F x hxF
          omega
        have hwlt : w < v := by
          rcases lt_or_eq_of_le hwmem.2 with h | h
          · exact h
          · exact absurd (h ▸ hsepv) hwfail
        have hsu : s ≤ w + 1 := by omega
        have hu_le_v : w + 1 ≤ v := hwlt
        have hsep_u : Sep X S J (w + 1) := hsep_after (w + 1) (Nat.lt_succ_self w) hu_le_v
        -- the separation at `w + 1` is at most `2`
        have hgapu : sMin X S (w + 1) - sMaxM X J (w + 1) ≤ 2 := by
          have hexf : ∃ i ∈ S, ∃ j ∈ J, X i w < runMaxI X j w + 2 := by
            by_contra hc
            apply hwfail
            refine ⟨fun i hi => hpos w hwmem.1 (le_trans hwmem.2 hvn) i, hSne, hJne, ?_⟩
            intro i hi j hj
            by_contra hcon
            exact hc ⟨i, hi, j, hj, by omega⟩
          obtain ⟨i', hiS, j', hjJ, hij⟩ := hexf
          obtain ⟨i0, hi0S, hmin0⟩ := exists_sMin (X := X) (S := S) (n := w) hSne
          have h1 : sMin X S (w + 1) ≤ X i0 (w + 1) := sMin_le hSne hi0S
          have h2 : X i0 (w + 1) ≤ X i0 w + 1 := hnn2 i0 w
          have h3 : X i0 w = sMin X S w := hmin0.symm
          have h4 : sMin X S w ≤ X i' w := sMin_le hSne hiS
          have h5 : runMaxI X j' w ≤ runMaxI X j' (w + 1) := runMaxI_mono X j' (by omega)
          have h6 : runMaxI X j' (w + 1) ≤ sMaxM X J (w + 1) := le_sMaxM hJne hjJ
          omega
        have hSupper_u : ∀ i ∈ S, ∀ j ∈ D, j ∉ S → X j (w + 1) ≤ X i (w + 1) :=
          upper_of_sep hDJ hsep_u
        have hspread_u : ((spreadS X S (w + 1) : ℤ) : ℝ) ≤ E :=
          hE (w + 1) S hsu (le_trans hu_le_v hvn) hSD hSne hScard hSupper_u
        have hmaxrange : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J (w + 1) := by
          refine le_trans (hrange (w + 1) hsu (le_trans hu_le_v hvn) hJne.choose) (le_sMax hJne hJne.choose_spec)
        have hWu := Wpot_le_of_sep_lag (A := Finset.univ \ J) (I := S) (J := J) (η := η) hLF hCnn hIA
          hsep_u hAne (le_trans (le_trans hn₀ hs) hsu) (le_trans (le_trans hu_le_v hvn) hnT) hmaxrange
          (fun j hj => hlagw j (w + 1) (le_trans hs hsu) (le_trans hu_le_v hvn₁))
        have hgr := hgrow S J (w + 1) v hSne hJne (Finset.disjoint_sdiff)
          (le_trans (le_trans hn₀ hs) hsu) hu_le_v hvnT
          (fun x h1 h2 => hsep_after x h1 (le_of_lt h2))
        have hgapuR : ((sMin X S (w + 1) - sMaxM X J (w + 1) : ℤ) : ℝ) ≤ 2 := by
          exact_mod_cast hgapu
        have hposu : (0 : ℝ) ≤ ((sMin X S (w + 1) - sMaxM X J (w + 1) : ℤ) : ℝ) := by
          have h2 : (0 : ℤ) ≤ sMin X S (w + 1) - sMaxM X J (w + 1) := by
            have hg := hsep_u.gap
            linarith
          exact_mod_cast h2
        have hspread' : ((spreadS X S (w + 1) : ℤ) : ℝ)
            + ((sMin X S (w + 1) - sMaxM X J (w + 1) : ℤ) : ℝ) + (η : ℝ)
            ≤ E + (η : ℝ) + 2 := by linarith
        have hmul := mul_le_mul_of_nonneg_left hspread' hCnn
        linarith [hWv, hWu, hgr, hmul]
      · -- no failure in `[s,v]`: `(sep)` holds throughout and the initial spread is used
        have hemp : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
        have hseps : ∀ x, s ≤ x → x ≤ v → Sep X S J x := by
          intro x h1 h2
          by_contra hcon
          have hxF : x ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hcon⟩
          rw [hemp] at hxF
          exact absurd hxF (by simp)
        have hmaxrange : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMin X D s :=
          sMin_le_of hD (fun i _ => hrange s le_rfl hsn i)
        have hW0 := Wpot_start (D := D) (I := S) (J := J) hLF hCnn hD hSne hJne hSD
          (fun j hj => (Finset.mem_sdiff.mp hj).1) hIA (le_trans hn₀ hs)
          (le_trans (le_trans hsn hn) hn₁) hmaxrange
        have hgr := hgrow S J s v hSne hJne (Finset.disjoint_sdiff) (le_trans hn₀ hs) hsv hvnT
          (fun x h1 h2 => hseps x h1 (le_of_lt h2))
        have hWv' : ((sMin X S v - sMax X J v : ℤ) : ℝ)
            ≤ Wpot H X (Finset.univ \ J) S J s + a := by
          rw [← ha_def] at hgr
          linarith [hWv, hgr]
        have hmul : C * ((spreadS X D s : ℤ) : ℝ) ≤ C * E := mul_le_mul_of_nonneg_left hE0 hCnn
        rw [← ha_def] at hW0
        nlinarith [hW0, hWv', hmul, hηnn, hann]
    · -- Case 1: `(sep)` fails at `v`
      have hexf : ∃ i ∈ S, ∃ j ∈ J, X i v < runMaxI X j v + 2 := by
        by_contra hc
        apply hsepv
        refine ⟨hposv, hSne, hJne, ?_⟩
        intro i hi j hj
        by_contra hcon
        exact hc ⟨i, hi, j, hj, by omega⟩
      obtain ⟨i, hiS, j, hjJ, hij⟩ := hexf
      have h1 : sMin X S v ≤ X i v := sMin_le hSne hiS
      have h2 : X i v ≤ runMaxI X j v + 1 := by omega
      have h3 : runMaxI X j v ≤ sMaxM X J v := le_sMaxM hJne hjJ
      have h4 : sMin X S v - sMaxM X J v ≤ 2 := by omega
      have h4' : ((sMin X S v - sMaxM X J v : ℤ) : ℝ) ≤ 2 := by exact_mod_cast h4
      have h5 : ((sMin X S v - sMax X J v : ℤ) : ℝ)
          = ((sMin X S v - sMaxM X J v : ℤ) : ℝ)
            + (((sMaxM X J v : ℤ) : ℝ) - ((sMax X J v : ℤ) : ℝ)) := by
        push_cast; ring
      have hEnn : 0 ≤ E := le_trans (by exact_mod_cast spreadS_nonneg hSne)
        (hE v S hsv hvn hSD hSne hScard hSupper)
      rw [h5]
      nlinarith [h4', hcastη, hCnn, hEnn, hηnn, hann]
  have hfinal : ((sMin X S v - sMax X (D \ S) v : ℤ) : ℝ)
      = ((sMin X S v - sMax X J v : ℤ) : ℝ) := by rw [hJdef]
  rw [hfinal]
  rw [ha_def] at hgoal
  exact hgoal

theorem spreadS_le_of_localGood_lag
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r ηF η : ℕ}
    (hLF : LocalField X τ H C CT T L r ηF) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {D : Finset ι} (hD : D.Nonempty)
    {s n : ℕ} (hs : n₀ ≤ s) (hsn : s ≤ n) (hn : n ≤ n₁) :
    ((spreadS X D n : ℤ) : ℝ) ≤ ((1 + C) ^ D.card - 1) *
      (C * (((spreadS X D s : ℤ) : ℝ) + (η : ℝ) + 2)
        + 2 * (CT * (L : ℝ) ^ (3 / 4 : ℝ)) + ((η : ℝ) + 2)) := by
  classical
  set a : ℝ := CT * (L : ℝ) ^ (3 / 4 : ℝ) with ha_def
  set E0 : ℝ := ((spreadS X D s : ℤ) : ℝ) with hE0def
  set B : ℝ := C * (E0 + (η : ℝ) + 2) + 2 * a + ((η : ℝ) + 2) with hBdef
  have hann : 0 ≤ a := by
    rw [ha_def]
    exact mul_nonneg hCT (Real.rpow_nonneg (Nat.cast_nonneg L) _)
  have hηnn : (0 : ℝ) ≤ (η : ℝ) := Nat.cast_nonneg η
  have hE0nn : 0 ≤ E0 := by
    rw [hE0def]
    exact_mod_cast spreadS_nonneg hD
  have hCnn : 0 ≤ C := le_trans zero_le_one hC1
  have hBnn : 0 ≤ B := by rw [hBdef]; nlinarith
  have main : ∀ k : ℕ, ∀ (v : ℕ) (I : Finset ι), s ≤ v → v ≤ n → I ⊆ D → I.Nonempty →
      I.card = k → (∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j v ≤ X i v) →
      ((spreadS X I v : ℤ) : ℝ) ≤ ((1 + C) ^ k - 1) * B := by
    intro k
    induction k with
    | zero =>
      intro v I _ _ _ hIne hcard _
      exact absurd (Finset.card_eq_zero.mp hcard) hIne.ne_empty
    | succ k ih =>
      intro v I hsv hvn hID hIne hcard hupper
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- a group of rank `1` has zero spread
        rcases hk0 with rfl
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
        have hspread0 : ((spreadS X {i} v : ℤ) : ℝ) = 0 := by
          have hne1 : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
          have hmax : sMax X {i} v = X i v := by
            rw [sMax_of_nonempty hne1]; simp
          have hmin : sMin X {i} v = X i v := by
            rw [sMin_of_nonempty hne1]; simp
          unfold spreadS
          rw [hmax, hmin]
          simp
        rw [hspread0]
        have hnn : (0 : ℝ) ≤ ((1 + C) ^ 1 - 1) * B := by
          have h1 : (0 : ℝ) ≤ (1 + C) ^ 1 - 1 := by
            have : ((1 + C) ^ 1 : ℝ) = 1 + C := pow_one _
            rw [this]; linarith
          exact mul_nonneg h1 hBnn
        simpa using hnn
      · -- the induction step, split off the minimum of `I`
        have hE0le : E0 ≤ ((1 + C) ^ k - 1) * B := by
          have h1 : (1 : ℝ) ≤ (1 + C) ^ k := one_le_pow₀ (by linarith)
          have h2 : C ≤ (1 + C) ^ k - 1 := by
            have hb : (1 : ℝ) ≤ 1 + C := by linarith
            have hmono : (1 + C) ^ 1 ≤ (1 + C) ^ k :=
              pow_le_pow_right₀ hb hkpos
            rw [pow_one] at hmono
            linarith
          have h2' : C * B ≤ ((1 + C) ^ k - 1) * B := mul_le_mul_of_nonneg_right h2 hBnn
          have h3 : E0 ≤ C * B := by rw [hBdef]; nlinarith
          linarith
        obtain ⟨i0, hi0I, hmin⟩ := Finset.exists_min_image I (fun i => X i v) hIne
        set S : Finset ι := I.erase i0 with hSdef
        have hScard : S.card = k := by
          rw [hSdef, Finset.card_erase_of_mem hi0I, hcard]
          omega
        have hSne : S.Nonempty := by
          rw [← Finset.card_pos, hScard]
          omega
        have hSD : S ⊆ D := fun i hi => hID (Finset.mem_of_mem_erase hi)
        have hIS : I = insert i0 S := by rw [hSdef]; exact (Finset.insert_erase hi0I).symm
        have hmemS : ∀ i ∈ S, i ∈ I := fun i hi => Finset.mem_of_mem_erase hi
        have hSup : ∀ i ∈ S, ∀ j ∈ D, j ∉ S → X j v ≤ X i v := by
          intro i hi j hjD hjS
          by_cases hji : j ∈ I
          · have hji0 : j = i0 := by
              by_contra hne'
              exact hjS (by rw [hSdef]; exact Finset.mem_erase.mpr ⟨hne', hji⟩)
            rw [hji0]; exact hmin i (hmemS i hi)
          · exact hupper i (hmemS i hi) j hjD hji
        have hi0DS : i0 ∈ D \ S := by
          refine Finset.mem_sdiff.mpr ⟨hID hi0I, ?_⟩
          rw [hSdef]
          exact fun h => (Finset.mem_erase.mp h).1 rfl
        have hDSne : (D \ S).Nonempty := ⟨i0, hi0DS⟩
        have hSp := gap_le_of_localGood_lag hLF hgrow hC1 hCT hτ hne hdr hrT hn₀ hn₁ hlagw
          hD hs hsn hn
          (k := k) (E := ((1 + C) ^ k - 1) * B) (fun w S' h1 h2 h3 h4 h5 h6 =>
            ih w S' h1 h2 h3 h4 h5 h6) hE0le hsv hvn hSD hSne hDSne hScard hSup
        rw [← ha_def] at hSp
        have hspread_eq : spreadS X I v = spreadS X S v + (sMin X S v - X i0 v) := by
          rw [hIS]
          exact spreadS_insert_min hSne (fun j hj => hmin j (hmemS j hj))
        have hsMax_eq : sMax X (D \ S) v = X i0 v := by
          refine le_antisymm (sMax_le hDSne (fun j hj => ?_)) (le_sMax hDSne hi0DS)
          rw [Finset.mem_sdiff] at hj
          by_cases hji : j ∈ I
          · have hji0 : j = i0 := by
              by_contra hne'
              exact hj.2 (by rw [hSdef]; exact Finset.mem_erase.mpr ⟨hne', hji⟩)
            rw [hji0]
          · exact hupper i0 hi0I j hj.1 hji
        have hcast : ((spreadS X I v : ℤ) : ℝ)
            = ((spreadS X S v : ℤ) : ℝ) + (((sMin X S v - X i0 v) : ℤ) : ℝ) := by
          rw [hspread_eq]; push_cast; ring
        have hcast2 : ((sMin X S v - X i0 v : ℤ) : ℝ)
            = ((sMin X S v - sMax X (D \ S) v : ℤ) : ℝ) := by rw [hsMax_eq]
        rw [hcast, hcast2]
        have hihS : ((spreadS X S v : ℤ) : ℝ) ≤ ((1 + C) ^ k - 1) * B :=
          ih v S hsv hvn hSD hSne hScard hSup
        have hkey : C * ((η : ℝ) + 2) + 2 * a + ((η : ℝ) + 2) ≤ C * B := by
          rw [hBdef]; nlinarith
        have ht1 : (1 : ℝ) ≤ (1 + C) ^ k := one_le_pow₀ (by linarith)
        have hstep : ((1 + C) ^ k - 1) * B
            + (C * (((1 + C) ^ k - 1) * B + (η : ℝ) + 2) + 2 * a + ((η : ℝ) + 2))
            ≤ ((1 + C) ^ (k + 1) - 1) * B := by
          rw [pow_succ]
          nlinarith [hkey, hBnn, ht1]
        linarith [hihS, hSp, hstep]
  have hmain : ((spreadS X D n : ℤ) : ℝ) ≤ ((1 + C) ^ D.card - 1) * B :=
    main D.card n D hsn le_rfl (Finset.Subset.refl D) hD rfl (fun i _ j hjD hji => absurd hjD hji)
  simp only [hBdef, hE0def, ha_def] at hmain ⊢
  exact hmain
theorem spreadS_le_scaled_lag
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r ηF η : ℕ}
    (hLF : LocalField X τ H C CT T L r ηF) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlagw : ∀ (i : ι) (m : ℕ), n₀ ≤ m → m ≤ n₁ → runMaxI X i m - X i m ≤ (η : ℤ))
    {D : Finset ι} (hD : D.Nonempty) {s n : ℕ} (hs : n₀ ≤ s) (hsn : s ≤ n)
    (hn : n ≤ n₁) {ε0 ε1 ε2 : ℝ}
    (hstart : ((spreadS X D s : ℤ) : ℝ) ≤ ε0 * (L : ℝ))
    (hη : (η : ℝ) ≤ ε1 * (L : ℝ))
    (hct : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 * (L : ℝ)) :
    ((spreadS X D n : ℤ) : ℝ) ≤ ((1 + C) ^ D.card - 1) *
      (C * ((ε0 + ε1) * (L : ℝ) + 2) + 2 * (ε2 * (L : ℝ)) + (ε1 * (L : ℝ) + 2)) := by
  have hmain := spreadS_le_of_localGood_lag hLF hgrow hC1 hCT hτ hne hdr hrT hn₀ hn₁ hlagw
    hD hs hsn hn
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hstep : C * (((spreadS X D s : ℤ) : ℝ) + (η : ℝ) + 2)
      + 2 * (CT * (L : ℝ) ^ (3 / 4 : ℝ)) + ((η : ℝ) + 2)
      ≤ C * ((ε0 + ε1) * (L : ℝ) + 2) + 2 * (ε2 * (L : ℝ)) + (ε1 * (L : ℝ) + 2) := by
    have h1 : ((spreadS X D s : ℤ) : ℝ) + (η : ℝ) + 2 ≤ (ε0 + ε1) * (L : ℝ) + 2 := by
      linarith [hstart, hη]
    have h2 : C * (((spreadS X D s : ℤ) : ℝ) + (η : ℝ) + 2)
        ≤ C * ((ε0 + ε1) * (L : ℝ) + 2) := mul_le_mul_of_nonneg_left h1 hC0
    have h3 : 2 * (CT * (L : ℝ) ^ (3 / 4 : ℝ)) ≤ 2 * (ε2 * (L : ℝ)) := by linarith
    linarith [h2, h3, hη]
  have hpow : (0 : ℝ) ≤ (1 + C) ^ D.card - 1 := by
    have : (1 : ℝ) ≤ (1 + C) ^ D.card := one_le_pow₀ (by linarith)
    linarith
  exact le_trans hmain (mul_le_mul_of_nonneg_left hstep hpow)
/-- **The source's `(4.8)` along a scale sequence, in the shape consumed by
`Coalesce.hpair_of_class_spread`.**  If on every scale the local-good field and `(locgroup)`
hold on the record window of level `r n`, the class spread at the grid time of the fluid time
`s` is `ε₀·L`, the record lag is `ε₁·L` and the additive error is `ε₂·L`, with
`ε₀, ε₁, ε₂ → 0`, then there is one vanishing sequence `ε` with

  `spread_D(τ_n(r n) + ⌊L_n t⌋) ≤ ε n · L_n`   for every `s ≤ t ≤ T`

for every finite group `D`.  Applying it to the coincidence class `{k | x_k(s) = x_i(s)}` of
the fluid limit supplies exactly the `hclass` premise of `Coalesce.hpair_of_class_spread`
(the remaining input there is the grid convergence at the single time `s`). -/
theorem classSpread_tendsto_lag
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r ηF η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (ηF n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ), τ n (r n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (r n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (η n : ℤ))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε0 ε1 ε2 : ℕ → ℝ}
    (hε0t : Tendsto ε0 atTop (𝓝 0)) (hε1t : Tendsto ε1 atTop (𝓝 0))
    (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s) (hsT : s ≤ Tn)
    (hTn : Tn ≤ (T : ℝ))
    (hstart : ∀ n, ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * s⌋₊) : ℤ) : ℝ)
      ≤ ε0 n * (scale n))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (t : ℝ), s ≤ t → t ≤ Tn →
        ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) ≤ ε n * (scale n) := by
  classical
  set K : ℝ := ((1 + C) ^ D.card - 1) * (2 * C + 2) with hKdef
  refine ⟨fun n => ((1 + C) ^ D.card - 1) * (C * (ε0 n + ε1 n) + 2 * ε2 n + ε1 n)
    + K / (scale n), ?_, ?_⟩
  · -- the vanishing sequence
    have hcast : Tendsto (fun n => ((scale n : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hscaleTop
    have hinv : Tendsto (fun n => (((scale n : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := hcast.inv_tendsto_atTop
    have hK : Tendsto (fun n => K / (scale n : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul K
    have hA : Tendsto (fun n => C * (ε0 n + ε1 n) + 2 * ε2 n + ε1 n) atTop (𝓝 0) := by
      have h := (((hε0t.add hε1t).const_mul C).add (hε2t.const_mul 2)).add hε1t
      simpa using h
    have hB : Tendsto (fun n => ((1 + C) ^ D.card - 1) * (C * (ε0 n + ε1 n) + 2 * ε2 n + ε1 n))
        atTop (𝓝 0) := by
      simpa using hA.const_mul ((1 + C) ^ D.card - 1)
    simpa using hB.add hK
  · intro n t hst htT
    have hLpos : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have ht0 : (0 : ℝ) ≤ t := le_trans hs0 hst
    have htT' : t ≤ (T : ℝ) := le_trans htT hTn
    have hsle : ⌊(scale n : ℝ) * s⌋₊ ≤ ⌊(scale n : ℝ) * t⌋₊ :=
      Nat.floor_mono (mul_le_mul_of_nonneg_left hst hLpos.le)
    have hfloor_le : ⌊(scale n : ℝ) * t⌋₊ ≤ T * scale n := by
      have h1 : (scale n : ℝ) * t ≤ (scale n : ℝ) * T :=
        mul_le_mul_of_nonneg_left htT' hLpos.le
      have h2 : ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * T :=
        le_trans (Nat.floor_le (mul_nonneg hLpos.le ht0)) h1
      have h3 : ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ ((T * scale n : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h3
    have h64n : τ n (r n) + 64 * Nat.ceil C * scale n ≤ τ n (r n) + ⌊(scale n : ℝ) * s⌋₊ := by
      refine Nat.add_le_add_left ?_ _
      have hLs : ((64 * Nat.ceil C * scale n : ℕ) : ℝ) ≤ (scale n : ℝ) * s := by
        have h1 : ((64 * Nat.ceil C : ℕ) : ℝ) ≤ s := by push_cast; exact hs64
        have h2 : ((64 * Nat.ceil C : ℕ) : ℝ) * (scale n : ℝ) ≤ s * (scale n : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
        calc ((64 * Nat.ceil C * scale n : ℕ) : ℝ)
            = ((64 * Nat.ceil C : ℕ) : ℝ) * (scale n : ℝ) := by push_cast; ring
          _ ≤ s * (scale n : ℝ) := h2
          _ = (scale n : ℝ) * s := by ring
      exact Nat.le_floor hLs
    have hbase := spreadS_le_scaled_lag (hLF n) (hgrow n) hC1 (hCT n) (hτ n) (hne n)
      (hdr n) (hrT n) (n₀ := τ n (r n) + 64 * Nat.ceil C * scale n)
      (n₁ := τ n (r n) + T * scale n) (Nat.le_add_right _ _) (le_refl _)
      (hlagw n) hD h64n
      (Nat.add_le_add_left hsle _) (Nat.add_le_add_left hfloor_le _) (hstart n) (hη n) (hct n)
    have key : (((1 + C) ^ D.card - 1) * (C * (ε0 n + ε1 n) + 2 * ε2 n + ε1 n)
          + K / (scale n : ℝ)) * (scale n : ℝ)
        = ((1 + C) ^ D.card - 1) *
          (C * ((ε0 n + ε1 n) * (scale n : ℝ) + 2) + 2 * (ε2 n * (scale n : ℝ))
            + (ε1 n * (scale n : ℝ) + 2)) := by
      rw [hKdef]
      field_simp
      ring
    show ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ)
        ≤ (((1 + C) ^ D.card - 1) * (C * (ε0 n + ε1 n) + 2 * ε2 n + ε1 n)
          + K / (scale n : ℝ)) * (scale n : ℝ)
    rw [key]
    exact hbase

end M4Sharp
