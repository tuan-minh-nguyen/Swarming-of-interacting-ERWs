/-
# Finite-L gluing II: the meet (run) lemma, the failure gap, and coalescence before the deadline

Deterministic only; continues `GlueCore`.  Main results:

* `run_le` — the paper's `(meet)` at finite `L`: if `(sep)` holds with `I = A`, `J = Aᶜ` at
  every integer time of `[s,t]`, then `t − s ≤ C·(W_s + C·(spread_A(s) + η) + C_T L^{3/4})`.
* `exists_run_start` — the start `v` of the final `(sep)` run before `n`.
* `gap_at_failure` — at that start, if it is not the first time of the analysis window, the
  separation is at most `2` (the nearest-neighbour step at `v−1`).
* `spreadS_le_of_le` — the crude growth bound `spread(n) ≤ spread(m) + 2(n−m)`.

`spread_bound` (the induction) is in `GlueCoalesce`.
-/
import Swarm.GlueCore

open Finset
open scoped BigOperators

namespace Glue

open RecordDefect LocalFluid MeasureTheory

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. One-step bounds and monotonicity of the extrema -/

theorem sMaxM_mono {X : ι → ℕ → ℤ} {S : Finset ι} (hS : S.Nonempty) {m n : ℕ} (hmn : m ≤ n) :
    sMaxM X S m ≤ sMaxM X S n := by
  refine sMaxM_le hS (fun i hi => ?_)
  exact le_trans (runMaxI_mono X i hmn) (le_sMaxM hS hi)

theorem sMin_step {X : ι → ℕ → ℤ} (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {S : Finset ι} (hS : S.Nonempty) (m : ℕ) :
    sMin X S (m + 1) ≤ sMin X S m + 1 := by
  obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := S) (n := m) hS
  have hone : X i (m + 1) ≤ X i m + 1 := by
    have h1 : |X i (m + 1) - X i m| ≤ 1 := le_of_eq (hne i m)
    have := (abs_le.1 h1).2
    linarith
  have h2 : sMin X S (m + 1) ≤ X i (m + 1) := sMin_le hS hi
  rw [hval]
  linarith

theorem sMin_mono_step {X : ι → ℕ → ℤ} (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {S : Finset ι} (hS : S.Nonempty) {m n : ℕ} (hmn : m ≤ n) :
    sMin X S n ≤ sMin X S m + ((n - m : ℕ) : ℤ) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      have h1 : sMin X S (n + 1) ≤ sMin X S n + 1 := sMin_step hne hS n
      have hcast : ((n + 1 - m : ℕ) : ℤ) = ((n - m : ℕ) : ℤ) + 1 := by
        have h : n + 1 - m = (n - m) + 1 := by omega
        rw [h]; push_cast; ring
      rw [hcast]
      linarith

/-- The crude growth bound: the spread of any subfamily grows by at most two per unit time. -/
theorem spreadS_le_of_le {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {S : Finset ι} (hS : S.Nonempty)
    {m n : ℕ} (hmn : m ≤ n) :
    spreadS X S n ≤ spreadS X S m + 2 * ((n - m : ℕ) : ℤ) := by
  obtain ⟨i, hi, hmax⟩ := exists_sMax (X := X) (S := S) (n := n) hS
  obtain ⟨j, hj, hmin⟩ := exists_sMin (X := X) (S := S) (n := n) hS
  have h1 : X i n ≤ X i m + ((n - m : ℕ) : ℤ) := FluidBlock.step_le_add (X := X) hne i hmn
  have h2 : X j m - ((n - m : ℕ) : ℤ) ≤ X j n := step_lower (X := X) hne j hmn
  have h3 : X i m ≤ sMax X S m := le_sMax hS hi
  have h4 : sMin X S m ≤ X j m := sMin_le hS hj
  unfold spreadS
  rw [hmax, hmin]
  linarith

/-! ## 2. Start of the final `(sep)` run -/

/-- The start `v` of the final run of `P` ending at `n`, inside `[s,n]`. -/
theorem exists_run_start {P : ℕ → Prop} {s n : ℕ} (hsn : s ≤ n) (hPn : P n) :
    ∃ v, s ≤ v ∧ v ≤ n ∧ (∀ w, v ≤ w → w ≤ n → P w) ∧ (s < v → ¬ P (v - 1)) := by
  classical
  have hex : ∃ t : ℕ, s ≤ t ∧ t ≤ n ∧ ∀ w, t ≤ w → w ≤ n → P w :=
    ⟨n, hsn, le_rfl, fun w h1 h2 => by
      have hwn : w = n := by omega
      rw [hwn]; exact hPn⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1,
    (Nat.find_spec hex).2.2, ?_⟩
  intro hlt hP
  have hQ : s ≤ Nat.find hex - 1 ∧ Nat.find hex - 1 ≤ n ∧
      ∀ w, Nat.find hex - 1 ≤ w → w ≤ n → P w := by
    refine ⟨Nat.le_pred_of_lt hlt, le_trans (Nat.sub_le _ _) (Nat.find_spec hex).2.1, ?_⟩
    intro w h1 h2
    by_cases hw : w = Nat.find hex - 1
    · rw [hw]; exact hP
    · have hw' : Nat.find hex ≤ w := by omega
      exact (Nat.find_spec hex).2.2 w hw' h2
  have hcon : Nat.find hex ≤ Nat.find hex - 1 := Nat.find_min' hex hQ
  omega

/-! ## 3. The meet lemma -/

/-- **The paper's `(meet)` at finite `L`.**

The separation hypothesis is the *closed* interval `∀ u ∈ [s,t]`: this is **stronger** than the
source's `(locmove)`, which only requires `(sep)` on the half-open `[s,t)`.  The extra endpoint is
used twice and visibly: `Wst_nonneg_of_sep` is applied at `t` (the paper's `(Wpos)` at the right
endpoint, which the paper's own argument also does), and so the final `t`-instance is needed.
The half-open-only form is `run_le_of_half`. -/
theorem run_le {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {C CT : ℝ}
    {T L r η : ℕ} (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    {A : Finset ι} (hA : A.Nonempty) (hA' : A ≠ Finset.univ) {s t : ℕ} {Wb : ℝ}
    (hs : τ r ≤ s) (hst : s ≤ t) (ht : t ≤ τ r + T * L)
    (hsep : ∀ u, s ≤ u → u ≤ t → Sep X A (Finset.univ \ A) u)
    (hWs : Wst H X A (Finset.univ \ A) s ≤ Wb) :
    ((t - s : ℕ) : ℝ)
      ≤ C * (Wb + C * (((spreadS X A s : ℤ) : ℝ) + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ)) := by
  have hWt : 0 ≤ Wst H X A (Finset.univ \ A) t :=
    Wst_nonneg_of_sep hLF.hmono hLF.hunit (hsep t hst le_rfl)
  -- the source's `(locmove)` only needs `(sep)` on the half-open interval
  have hhalf : ∀ u : ℕ, s ≤ u → u < t → Sep X A (Finset.univ \ A) u :=
    fun u h1 h2 => hsep u h1 (le_of_lt h2)
  have hw := hLF.wmove A s t hA hA' hs hst ht hhalf
  have hR : (((sMaxM X A s : ℤ) : ℝ) - ((sMin X A s : ℤ) : ℝ))
      ≤ ((spreadS X A s : ℤ) : ℝ) + (η : ℝ) := by
    have h1 : sMaxM X A s ≤ sMax X A s + (η : ℤ) := by
      have h2 := sMaxM_sub_sMax_le (X := X) hA (fun i hi => hLF.lag i s hs (le_trans hst ht))
      linarith
    have h1' : ((sMaxM X A s : ℤ) : ℝ) ≤ ((sMax X A s : ℤ) : ℝ) + (η : ℝ) := by
      exact_mod_cast h1
    have h2' : ((spreadS X A s : ℤ) : ℝ)
        = ((sMax X A s : ℤ) : ℝ) - ((sMin X A s : ℤ) : ℝ) := by
      unfold spreadS
      push_cast
      ring
    linarith
  have hmul : C * (((sMaxM X A s : ℤ) : ℝ) - ((sMin X A s : ℤ) : ℝ))
      ≤ C * (((spreadS X A s : ℤ) : ℝ) + (η : ℝ)) := mul_le_mul_of_nonneg_left hR hC.le
  have hdiv : ((t - s : ℕ) : ℝ) / C
      ≤ Wb + C * (((spreadS X A s : ℤ) : ℝ) + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    linarith
  calc ((t - s : ℕ) : ℝ) = C * (((t - s : ℕ) : ℝ) / C) := by field_simp
    _ ≤ C * (Wb + C * (((spreadS X A s : ℤ) : ℝ) + (η : ℝ))
          + CT * (L : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hC.le

/-- **The failure gap.**  If `(sep)` fails at `v−1` while all positions are nonnegative, then at
time `v` the separation `min_A X_v − max_{Aᶜ} M_v` is at most `2`. -/
theorem gap_at_failure {X : ι → ℕ → ℤ} (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {A : Finset ι} {v : ℕ} (hA : A.Nonempty) (hA' : A ≠ Finset.univ) (hv : 1 ≤ v)
    (hpos : ∀ i, 0 ≤ X i (v - 1)) (hnot : ¬ Sep X A (Finset.univ \ A) (v - 1)) :
    sMin X A v - sMaxM X (Finset.univ \ A) v ≤ 2 := by
  have hJne : (Finset.univ \ A).Nonempty := Finset.sdiff_nonempty.mpr (by simpa using hA')
  have hpair : ∃ i ∈ A, ∃ j ∈ Finset.univ \ A, X i (v - 1) ≤ runMaxI X j (v - 1) + 1 := by
    by_contra hcon
    apply hnot
    refine ⟨fun i _ => hpos i, hA, hJne, ?_⟩
    intro i hi j hj
    by_contra hlt
    push_neg at hlt
    exact hcon ⟨i, hi, j, hj, by omega⟩
  obtain ⟨i0, hi0, j0, hj0, hle0⟩ := hpair
  have h1 : sMin X A (v - 1) ≤ X i0 (v - 1) := sMin_le hA hi0
  have h3 : runMaxI X j0 (v - 1) ≤ sMaxM X (Finset.univ \ A) (v - 1) := le_sMaxM (X := X) (n := v - 1) hJne hj0
  have h4 : sMaxM X (Finset.univ \ A) (v - 1) ≤ sMaxM X (Finset.univ \ A) v := by
    refine sMaxM_mono hJne ?_
    omega
  have h5 : sMin X A v ≤ sMin X A (v - 1) + 1 := by
    have h := sMin_step hne hA (v - 1)
    have hv' : v - 1 + 1 = v := by omega
    rwa [hv'] at h
  linarith

/-- **`(meet)` from the source's half-open clause plus the endpoint.**  This is the exact
decomposition: `hsep` is the source's `(locmove)` hypothesis (`∀ u ∈ [s,t)`) and `hsep_t` is the
separate `(Wpos)` endpoint instance at `t` that `run_le` also needs. -/
theorem run_le_of_half {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {C CT : ℝ}
    {T L r η : ℕ} (hLF : LocalField X τ H C CT T L r η) (hC : 0 < C)
    {A : Finset ι} (hA : A.Nonempty) (hA' : A ≠ Finset.univ) {s t : ℕ} {Wb : ℝ}
    (hs : τ r ≤ s) (hst : s ≤ t) (ht : t ≤ τ r + T * L)
    (hsep : ∀ u, s ≤ u → u < t → Sep X A (Finset.univ \ A) u)
    (hsep_t : Sep X A (Finset.univ \ A) t)
    (hWs : Wst H X A (Finset.univ \ A) s ≤ Wb) :
    ((t - s : ℕ) : ℝ)
      ≤ C * (Wb + C * (((spreadS X A s : ℤ) : ℝ) + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ)) :=
  run_le hLF hC hA hA' hs hst ht
    (fun u h1 h2 => by
      rcases lt_or_eq_of_le h2 with h3 | h3
      · exact hsep u h1 h3
      · rw [h3]; exact hsep_t)
    hWs

end Glue
