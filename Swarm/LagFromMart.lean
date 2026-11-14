/-
# Finite-`L` lag from `(locmart)`: `η = O(L^{3/4})` on the subwindow after `64⌈C⌉L`

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, proof of Proposition
`local` (display `(locmart)`) and proof of Proposition `tight`, display `(fluidmax)`:

  `|M_t^i − M_s^i| ≤ C_T L^{3/4}`  and  `max_i sup_{64C ≤ u ≤ T} (M^i_{τ_r+⌊Lu⌋} − X^i_{τ_r+⌊Lu⌋})/L → 0`.

`(locmart)` is certified for the literal record clock in the public `Swarm/RecordClockLocal.lean`
(every walker, eventual `exp(−c L^{1/16})` complement).  Nobody had yet *used* it to provision
the lag clause `LocalField.lag`, which is a carrier of every deterministic gluing file.  This
file does exactly that, at finite `L`, with no limit and no `η = 0`:

* `MartClause` — the paper's `(locmart)` in the two-sided compensated form
  `|(X^i_t − X^i_s) − μ (A^i_t − A^i_s)| ≤ C_T L^{3/4}` with a **nondecreasing integer clock**
  `A^i` (`A^i_n` is the paper's `Σ_{t<n} 1{excited}` count).  Only the two one-sided
  consequences are consumed below, and both follow from the displayed absolute value.
* `MartClause.down` — `X^i_s − X^i_t ≤ C_T L^{3/4}` for `τ_r ≤ s ≤ t ≤ τ_r + T L`: the walker
  cannot fall back by more than `C_T L^{3/4}` inside the window.  This single inequality is
  the finite-`L` surrogate for the source's monotonicity of the fluid limit `x_i`
  (`(fluid)`: `0 ≤ x_i(t) − x_i(s)`).
* `runMaxI_le_of_forall_le` — a pointwise bound bounds the running maximum.
* `lag_le_sub` — **the main result**: on `(lococc)`, `{d_r ≤ L}`, `Numerics C C_T L`
  (`C_T L^{3/4} ≤ C L`) and `64⌈C⌉ ≤ T`, for *every* walker and *every* integer time
  `n ∈ [τ_r + 64⌈C⌉L, τ_r + TL]`,
  `M^i_n − X^i_n ≤ η` with `η = ⌈C_T L^{3/4}⌉`.
  So the second half of `(fluidmax)` is *proved*, not assumed: the lag allowance is
  `η = O(L^{3/4}) = o(L)` on the genuine source subwindow.
* `lag_le_window` — the complementary whole-window bound `M^i_n − X^i_n ≤ L + ⌈C_T L^{3/4}⌉`
  on `[τ_r, τ_r + TL]`.  The `+L` is not slack in the argument: at `n = τ_r` the lag *is*
  `d_r`, which may be as large as `L`.  This is why the sharp bound is stated on the
  subwindow only, and it is the reason the deterministic join files (which demand the lag
  clause on all of `[τ_r, τ_r+TL]`) cannot be fed with a small `η`; see `JoinSub.lean`.
* `pos_gt_level_sub_mart` — the position form: `X^i_n > r + L − η` on the subwindow.  This is
  the finite-`L` content of the source's `m_i(u) = x_i(u)` for `u ≥ 64C`, obtained **without**
  the `htop` maximality premise of `LagStep.pos_gt_level_sub` (that premise is the limit
  statement `x_i` nondecreasing and is not available at finite `L`).
* `localField_of_mart` — assembles a literal `Glue.LocalField` from the potential clauses
  plus `(locmart)`, with `η = L + ⌈C_T L^{3/4}⌉` and with the lag clause *derived*.

Scope.  Deterministic; no probability, no stationarity, no `η = 0`.  The remaining carrier is
`MartClause`/`LocOcc`/the potential clauses themselves (the local-good event of Proposition
`local`), not the lag.
-/
import Swarm.LagStep

open Finset
open scoped BigOperators

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The `(locmart)` clause and its two one-sided consequences -/

/-- The paper's first `(locmart)` display in compensated two-sided form:
`|(X^i_t − X^i_s) − μ (A^i_t − A^i_s)| ≤ C_T L^{3/4}` for all `τ_r ≤ s ≤ t ≤ τ_r + T L`,
where the integer clock `A^i` is nondecreasing.  For the literal swarm,
`A^i_n = Σ_{t<n} 1{Σ_{j≠i} L^j_t(X^i_t) ≥ m}` and `μ = 2p−1`
(display `(mart)`), so this is the source's own clause; `RecordClockLocal` certifies it on an
event of complement at most `C_T e^{−c_T L^{1/16}}`. -/
structure MartClause (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (A : ι → ℕ → ℕ) (μ CT : ℝ)
    (T L r : ℕ) : Prop where
  /-- The drift `μ = 2p−1` is positive. -/
  hμ : 0 < μ
  /-- The compensator clock is nondecreasing in time. -/
  hA : ∀ i, Monotone (A i)
  /-- The `(locmart)` bound. -/
  hbound : ∀ (i : ι) (s t : ℕ), τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    |(((X i t : ℤ) : ℝ) - ((X i s : ℤ) : ℝ))
        - μ * (((A i t : ℕ) : ℝ) - ((A i s : ℕ) : ℝ))| ≤ CT * (L : ℝ) ^ (3 / 4 : ℝ)

/-- Upward consequence of `(locmart)`: the ascent is bounded by the compensated drift. -/
theorem MartClause.up (h : MartClause X τ A μ CT T L r) {i : ι} {s t : ℕ}
    (h1 : τ r ≤ s) (h2 : s ≤ t) (h3 : t ≤ τ r + T * L) :
    ((X i t : ℤ) : ℝ) - ((X i s : ℤ) : ℝ)
      ≤ μ * (((A i t : ℕ) : ℝ) - ((A i s : ℕ) : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hb := (abs_le.mp (h.hbound i s t h1 h2 h3)).2
  linarith

/-- Downward consequence of `(locmart)`: inside the window a walker cannot fall back by more
than `C_T L^{3/4}`.  This is the finite-`L` replacement for the monotonicity of the fluid
limit `x_i` used in the source's derivation of `(fluidmax)`. -/
theorem MartClause.down (h : MartClause X τ A μ CT T L r) {i : ι} {s t : ℕ}
    (h1 : τ r ≤ s) (h2 : s ≤ t) (h3 : t ≤ τ r + T * L) :
    ((X i s : ℤ) : ℝ) - ((X i t : ℤ) : ℝ) ≤ CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hb := (abs_le.mp (h.hbound i s t h1 h2 h3)).1
  have hmono : ((A i s : ℕ) : ℝ) ≤ ((A i t : ℕ) : ℝ) := by
    exact_mod_cast h.hA i h2
  have hpos : 0 ≤ μ * (((A i t : ℕ) : ℝ) - ((A i s : ℕ) : ℝ)) := by
    have : 0 ≤ ((A i t : ℕ) : ℝ) - ((A i s : ℕ) : ℝ) := by linarith
    exact mul_nonneg h.hμ.le this
  linarith

/-- Integer form of `MartClause.down`: `X^i_u − X^i_n ≤ η` for `τ_r ≤ u ≤ n` in the window,
whenever the real allowance `C_T L^{3/4}` is at most `η`. -/
theorem lag_step (h : MartClause X τ A μ CT T L r) {i : ι} {u n : ℕ} (h1 : τ r ≤ u)
    (h2 : u ≤ n) (h3 : n ≤ τ r + T * L) {η : ℕ} (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ)) :
    X i u - X i n ≤ (η : ℤ) := by
  have hd := h.down (i := i) h1 h2 h3
  have hcast : ((X i u - X i n : ℤ) : ℝ) ≤ (η : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

/-! ## 2. Bounding the running maximum -/

/-- A pointwise bound bounds the individual running maximum. -/
theorem runMaxI_le_of_forall_le {X : ι → ℕ → ℤ} {i : ι} {n : ℕ} {c : ℤ}
    (h : ∀ u, u ≤ n → X i u ≤ c) : runMaxI X i n ≤ c := by
  induction n with
  | zero => simpa [runMaxI_zero] using h 0 le_rfl
  | succ n ih =>
      rw [runMaxI_succ]
      exact max_le (ih (fun u hu => h u (Nat.le_succ_of_le hu))) (h (n + 1) le_rfl)

/-! ## 3. The sharp lag bound on the subwindow after `64⌈C⌉L` -/

/-- **The second half of `(fluidmax)`, at finite `L`, on the source subwindow.**

On `(lococc)`, `{d_r ≤ L}`, the numerical allowance `C_T L^{3/4} ≤ C L` and `64⌈C⌉ ≤ T`, for
every walker `i` and every integer `n ∈ [τ_r + 64⌈C⌉L, τ_r + TL]`,

  `M^i_n − X^i_n ≤ ⌈C_T L^{3/4}⌉`,

i.e. `η = O(L^{3/4}) = o(L)` and no `η = 0` is asserted.  The proof combines the certified
level bound `runMaxI_gt_level_of_le` (every running maximum over the subwindow exceeds
`r + L`) with `(locmart)`: an earlier position exceeds `X^i_n` by at most `C_T L^{3/4}`, and
positions before `τ_r` do not exceed the record level `r`, which the level bound dominates. -/
theorem lag_le_sub (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {A : ι → ℕ → ℕ} {μ CT : ℝ}
    (hτ : IsRecord X τ) (hM : MartClause X τ A μ CT T L r)
    {C : ℝ} (hC : 0 < C) (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT : 64 * Nat.ceil C ≤ T)
    {η : ℕ} (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {n : ℕ} (hn : τ r + 64 * Nat.ceil C * L ≤ n) (hnT : n ≤ τ r + T * L) (i : ι) :
    runMaxI X i n - X i n ≤ (η : ℤ) := by
  have hlev : (r : ℤ) + (L : ℤ) < runMaxI X i n :=
    runMaxI_gt_level_of_le X hτ hC hocc hdr hL hij hnum hT hn i
  -- every position up to `n` is below `max r (X_n + η)`
  have hpoint : ∀ u, u ≤ n → X i u ≤ max (r : ℤ) (X i n + (η : ℤ)) := by
    intro u hu
    rcases le_total u (τ r) with h1 | h1
    · have h2 : runMaxI X i u ≤ (r : ℤ) := runMaxI_le_of_le_tau X hτ i h1
      have h3 : X i u ≤ runMaxI X i u := le_runMaxI X i u
      exact le_trans h3 (le_trans h2 (le_max_left _ _))
    · have h2 : X i u - X i n ≤ (η : ℤ) := lag_step hM h1 hu hnT hη
      refine le_trans ?_ (le_max_right _ _)
      linarith
  have hmax : runMaxI X i n ≤ max (r : ℤ) (X i n + (η : ℤ)) :=
    runMaxI_le_of_forall_le hpoint
  -- hence the second branch of the maximum must be the large one
  have hXL : (r : ℤ) + (L : ℤ) < X i n + (η : ℤ) := by
    rcases max_cases (r : ℤ) (X i n + (η : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hmax; linarith
    · rw [he] at hmax; linarith
  have hfin : max (r : ℤ) (X i n + (η : ℤ)) - X i n ≤ (η : ℤ) := by
    rcases max_cases (r : ℤ) (X i n + (η : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  linarith

/-- Position form of the lag bound, i.e. the finite-`L` content of `m_i(u) = x_i(u)` for
`u ≥ 64C` from `(fluidmax)`: on the subwindow every walker sits strictly above
`r + L − η`.  Unlike `LagStep.pos_gt_level_sub` this needs **no** `htop` maximality premise. -/
theorem pos_gt_level_sub_mart (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {A : ι → ℕ → ℕ} {μ CT : ℝ}
    (hτ : IsRecord X τ) (hM : MartClause X τ A μ CT T L r)
    {C : ℝ} (hC : 0 < C) (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT : 64 * Nat.ceil C ≤ T)
    {η : ℕ} (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {n : ℕ} (hn : τ r + 64 * Nat.ceil C * L ≤ n) (hnT : n ≤ τ r + T * L) (i : ι) :
    (r : ℝ) + (L : ℝ) - (η : ℝ) < (X i n : ℝ) := by
  have hlev : (r : ℤ) + (L : ℤ) < runMaxI X i n :=
    runMaxI_gt_level_of_le X hτ hC hocc hdr hL hij hnum hT hn i
  have hlag : runMaxI X i n - X i n ≤ (η : ℤ) :=
    lag_le_sub X hτ hM hC hocc hdr hL hij hnum hT hη hn hnT i
  have h1 : (r : ℤ) + (L : ℤ) - (η : ℤ) < X i n := by linarith
  have h2 : (((r : ℤ) + (L : ℤ) - (η : ℤ) : ℤ) : ℝ) < ((X i n : ℤ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith
/-! ## 4. The whole-window lag bound (with the unavoidable `+L`) -/

/-- On the **whole** record window the lag is at most `L + ⌈C_T L^{3/4}⌉`.  The `L` cannot be
removed: at `n = τ_r` the lag equals `d_r`, which may be as large as `L` on the carrier
`{d_r ≤ L}`.  (This is exactly why the sharp bound of `lag_le_sub` is a subwindow statement,
and why the deterministic join files need their lag clause restricted to the subwindow.) -/
theorem lag_le_window (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {A : ι → ℕ → ℕ} {μ CT : ℝ}
    (hτ : IsRecord X τ) (hM : MartClause X τ A μ CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) {η : ℕ}
    (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {n : ℕ} (hn : τ r ≤ n) (hnT : n ≤ τ r + T * L) (i : ι) :
    runMaxI X i n - X i n ≤ (η : ℤ) + (L : ℤ) := by
  have hpoint : ∀ u, u ≤ n → X i u ≤ max (r : ℤ) (X i n + (η : ℤ)) := by
    intro u hu
    rcases le_total u (τ r) with h1 | h1
    · have h2 : runMaxI X i u ≤ (r : ℤ) := runMaxI_le_of_le_tau X hτ i h1
      have h3 : X i u ≤ runMaxI X i u := le_runMaxI X i u
      exact le_trans h3 (le_trans h2 (le_max_left _ _))
    · have h2 : X i u - X i n ≤ (η : ℤ) := lag_step hM h1 hu hnT hη
      refine le_trans ?_ (le_max_right _ _)
      linarith
  have hmax : runMaxI X i n ≤ max (r : ℤ) (X i n + (η : ℤ)) :=
    runMaxI_le_of_forall_le hpoint
  -- the position at `n` is at most `L + η` below the record level `r`
  have hlow : (r : ℤ) - (L : ℤ) ≤ X i (τ r) := tau_position_lower X hdr i
  have hdown : X i (τ r) - X i n ≤ (η : ℤ) := lag_step hM le_rfl hn hnT hη
  have hXL : (r : ℤ) - X i n ≤ (η : ℤ) + (L : ℤ) := by linarith
  have hfin' : max (r : ℤ) (X i n + (η : ℤ)) - X i n ≤ (η : ℤ) + (L : ℤ) := by
    rcases max_cases (r : ℤ) (X i n + (η : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  linarith

/-! ## 5. Provisioning the deterministic gluing field -/

/-- **A literal `Glue.LocalField` whose lag clause is *derived*, not assumed.**

Given the potential clauses of Proposition `local` (`(loccoord)` as `hcoord`, `(locmove)` as
`wmove`, the spatial monotonicity/unit-increment facts), the occupation estimate `(lococc)`,
the martingale estimate `(locmart)` and the carrier `{d_r ≤ L}`, the local-good field holds
with `η = L + ⌈C_T L^{3/4}⌉`.  The lag clause — a carrier of every deterministic gluing file —
is produced here by `lag_le_window`; nothing else about probabilities is assumed. -/
theorem localField_of_mart (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ CT C : ℝ} {T L r : ℕ}
    (hmono : ∀ (B : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → H B n x ≤ H B n y)
    (hunit : ∀ (B : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H B n y - H B n x)
    (hcoord : ∀ (B : Finset ι) (n : ℕ), B.Nonempty → B ≠ Finset.univ → τ r ≤ n →
      n ≤ τ r + T * L → ∀ a0 b0 : ℤ, (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
      b0 ≤ sMaxM X B n →
      ((H B n b0 - H B n a0 : ℤ) : ℝ) ≤ C * ((b0 - a0 : ℤ) : ℝ) + CT * (L : ℝ) ^ (3 / 4 : ℝ))
    (wmove : ∀ (B : Finset ι) (s t : ℕ), B.Nonempty → B ≠ Finset.univ → τ r ≤ s → s ≤ t →
      t ≤ τ r + T * L → (∀ u : ℕ, s ≤ u → u < t → Sep X B (Finset.univ \ B) u) →
      Wst H X B (Finset.univ \ B) t - Wst H X B (Finset.univ \ B) s
        ≤ C * (((sMaxM X B s : ℤ) : ℝ) - ((sMin X B s : ℤ) : ℝ)) - ((t - s : ℕ) : ℝ) / C
          + CT * (L : ℝ) ^ (3 / 4 : ℝ))
    (hocc : LocOcc X τ C CT T L r) (hτ : IsRecord X τ)
    (hM : MartClause X τ A μ CT T L r) (hdr : defect X τ r ≤ (L : ℤ)) {η : ℕ}
    (hη : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ)) :
    LocalField X τ H C CT T L r (L + η) := by
  refine ⟨hmono, hunit, hcoord, wmove, ?_, hocc⟩
  intro i n h1 h2
  have h := lag_le_window X hτ hM hdr hη h1 h2 i
  have hcast : ((L + η : ℕ) : ℤ) = (L : ℤ) + (η : ℤ) := by push_cast; ring
  rw [hcast]
  linarith

end JoinStep

/-! ## Axiom audit (source order) -/


