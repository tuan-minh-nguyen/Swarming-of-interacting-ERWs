/-
# Finite-L lag at the paper's levels `24 C L` and `64 C L`

Source: `main_1d_revised.tex`, the proof of Proposition `tight` after `(Rlower)`:

  "By `(Rlower)`, we can choose `j` with `m_j(24C) > 2`.  If `m_i(64C) ≤ 1` for some `i ≠ j`,
   then `x_i(u) ≤ 1 < m_j(u)` for every `u ∈ [24C,64C]` ... a contradiction, so we have
   `m_i(64C) > 1` for every `i`.  Using `(fluid)` and `m_i(0) ≤ 0`, we conclude
   `m_i(u) = x_i(u)` for `64C ≤ u ≤ T`."

The accepted `LocalFluid.runMaxI_gt_of_locOcc` is the finite-`L`, limit-free form of the
first half at level `1`: on `(lococc)` and `{d_r ≤ L}`, if the record has advanced by `2L` at
time `τ_r + a` then by time `τ_r + b` *every* walker's individual running maximum exceeds
`r + L`.  It carries exact numerical premises.  This file

* instantiates it at the paper's scale with **explicit integers** `a = 24⌈C⌉L`,
  `b = 64⌈C⌉L`, reducing both numerical premises to the single transparent threshold
  `numerics : C_T L^{3/4} ≤ C L` (the paper's `L^{-1/4}` allowance) plus the window
  requirement `64⌈C⌉ ≤ T` (enlarging `T` is allowed, and the later join phases of the
  paper use `B,T ≥ 64C` anyway);
* derives the *persistent* level bound `r + L < M^i_n` for every integer `n` in the
  subwindow `[τ_r + 64⌈C⌉L, τ_r + T L]`, hence the position lower bound
  `r + L - η < X^i_n` once the finite-`L` lag `η` is available;
* isolates the exact carrier of the local-good field's `lag` clause: it transfers from the
  single time `τ_r + 64⌈C⌉L` to the whole subwindow as soon as each walker's position at
  `n` is maximal over `[64⌈C⌉L, n]` (the discrete counterpart of `(fluid)`'s monotonicity
  of `x_i`, which is what the paper uses in `m_i(u) = max{m_i(64C), x_i(u)} = x_i(u)`);
* records the uniform epsilon form `η ≤ ε L`.

Nothing here is probabilistic, and nothing asserts the lag `η = 0`, that `(lococc)` alone
forces `o(L)` lag, or any good-event probability.
-/
import Swarm.GlueHalf

open Finset
open scoped BigOperators

namespace JoinStep

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The running maximum over a shifted range -/

/-- If every position of walker `i` after time `m` and up to `n` is at most `c`, then the
running maximum at `n` is at most `max (M_i m) c`.  This is the elementary decomposition
behind the paper's `m_i(u) = max{m_i(0), x_i(u)}`. -/
theorem runMaxI_le_max_of {X : ι → ℕ → ℤ} {i : ι} {m n : ℕ} (hmn : m ≤ n) {c : ℤ}
    (h : ∀ u, m < u → u ≤ n → X i u ≤ c) :
    runMaxI X i n ≤ max (runMaxI X i m) c := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_max_left _ _
  | succ n hmn ih =>
      have hsucc : runMaxI X i (n + 1) = max (runMaxI X i n) (X i (n + 1)) :=
        runMaxI_succ X i n
      have hprev : runMaxI X i n ≤ max (runMaxI X i m) c :=
        ih (fun u hu1 hu2 => h u hu1 (Nat.le_succ_of_le hu2))
      have hnew : X i (n + 1) ≤ c := h (n + 1) (by omega) le_rfl
      rw [hsucc]
      calc max (runMaxI X i n) (X i (n + 1))
          ≤ max (max (runMaxI X i m) c) c := max_le_max hprev hnew
        _ = max (runMaxI X i m) c := by rw [max_assoc, max_self]

/-! ## 2. The lag carrier of the local-good field -/

/-- The finite-`L` lag of walker `i` at time `n`: `M^i_n − X^i_n`. -/
noncomputable def lagI (X : ι → ℕ → ℤ) (i : ι) (n : ℕ) : ℤ := runMaxI X i n - X i n

theorem lagI_eq (X : ι → ℕ → ℤ) (i : ι) (n : ℕ) :
    lagI X i n = runMaxI X i n - X i n := rfl

/-- **Transfer of the lag bound across a subwindow.**  If at the start `m` of the subwindow
the individual lag is at most `η`, and the position at `n` is maximal for walker `i` over
`[m,n]`, then the lag is at most `η` at `n`.  This is the exact discrete content of the
paper's step `m_i(u) = max{m_i(64C), x_i(u)} = x_i(u)`: `x_i` nondecreasing makes `n` a
top time of `[m,n]`, and `m_i(64C) = x_i(64C)` is the starting lag bound.  `η = 0` is not
asserted; monotonicity of the fluid path is replaced by its literal finite-`L` consequence
`htop` as an explicit premise. -/
theorem lag_le_of_lag_start {X : ι → ℕ → ℤ} {i : ι} {η : ℕ} {m n : ℕ} (hmn : m ≤ n)
    (hstart : lagI X i m ≤ (η : ℤ))
    (htop : ∀ u, m ≤ u → u ≤ n → X i u ≤ X i n) :
    lagI X i n ≤ (η : ℤ) := by
  have h1 : runMaxI X i n ≤ max (runMaxI X i m) (X i n) :=
    runMaxI_le_max_of hmn (fun u hu1 hu2 => htop u (le_of_lt hu1) hu2)
  have h2 : X i m ≤ X i n := htop m le_rfl hmn
  have h3 : lagI X i m = runMaxI X i m - X i m := rfl
  have h4 : lagI X i n = runMaxI X i n - X i n := rfl
  have hη : (0 : ℤ) ≤ (η : ℤ) := by exact_mod_cast Nat.zero_le η
  have hstart' : runMaxI X i m - X i m ≤ (η : ℤ) := hstart
  have hstep : max (runMaxI X i m) (X i n) - X i n ≤ (η : ℤ) := by
    rcases max_cases (runMaxI X i m) (X i n) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith
    · rw [he]; linarith
  rw [h4]
  linarith

/-! ## 3. The paper's `24C`/`64C` instantiation -/

/-- The single numerical threshold of this file: the `L^{3/4}` error is dominated by `C L`,
i.e. exactly the paper's `L^{-1/4}` allowance `C_T L^{3/4} = C·L·L^{-1/4}`. -/
def Numerics (C CT : ℝ) (L : ℕ) : Prop := CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ C * (L : ℝ)

/-- **`(fluidmax)` first half at the paper's scale.**  On `(lococc)` and `{d_r ≤ L}`, with
`64⌈C⌉ ≤ T` and `C_T L^{3/4} ≤ C L`, by time `τ_r + 64⌈C⌉L` every walker's individual
running maximum exceeds the level `r + L`.  This is the finite-`L` statement "`m_i(64C) > 1`"
of the paper, with the integers `24⌈C⌉L`, `64⌈C⌉L` in place of the real thresholds
`24C·L`, `64C·L`. -/
theorem runMaxI_gt_level (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {C CT : ℝ} (hC : 0 < C) {T L r : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT : 64 * Nat.ceil C ≤ T) :
    ∀ i : ι, (r : ℤ) + (L : ℤ) < runMaxI X i (τ r + 64 * Nat.ceil C * L) := by
  classical
  set k : ℕ := Nat.ceil C with hk
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hEpos : (0 : ℝ) < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hkC : C ≤ (k : ℝ) := Nat.le_ceil C
  have hCk : (1 : ℕ) ≤ k := by
    have hpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hC hkC
    exact_mod_cast hpos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hCk
  -- the `L^{3/4}` budget divided by `C`
  have hdiv : (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    simpa [mul_comm, Numerics] using hnum
  have hCL : C * (L : ℝ) ≤ (k : ℝ) * (L : ℝ) :=
    mul_le_mul_of_nonneg_right hkC hLpos.le
  -- the two numerical premises of `runMaxI_gt_of_locOcc`
  have hlead : 2 * (L : ℝ) ≤ (3 : ℝ) / 8 * (((24 * k * L : ℕ) : ℝ) / C)
      - 3 * (L : ℝ) - (CT / C) * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have hcast : ((24 * k * L : ℕ) : ℝ) = 24 * (k : ℝ) * (L : ℝ) := by push_cast; ring
    rw [hcast]
    have hratio : (24 * (k : ℝ) * (L : ℝ)) / C = 24 * ((k : ℝ) / C) * (L : ℝ) := by
      field_simp
    rw [hratio]
    have h9 : (3 : ℝ) / 8 * (24 * ((k : ℝ) / C) * (L : ℝ))
        = 9 * (((k : ℝ) / C) * (L : ℝ)) := by ring
    rw [h9]
    have hkCpos : 1 ≤ (k : ℝ) / C := by
      rw [le_div_iff₀ hC]; linarith
    have hmono : (L : ℝ) ≤ ((k : ℝ) / C) * (L : ℝ) := by
      calc (L : ℝ) = 1 * (L : ℝ) := (one_mul _).symm
        _ ≤ ((k : ℝ) / C) * (L : ℝ) := mul_le_mul_of_nonneg_right hkCpos hLpos.le
    linarith
  have hcount : 4 * C * (L : ℝ) + ((64 * k * L : ℕ) : ℝ) / 8
      + CT * (L : ℝ) ^ (3 / 4 : ℝ) < (((64 * k * L) - 24 * k * L : ℕ) : ℝ) := by
    have hsub : (64 * k * L) - 24 * k * L = 40 * k * L := by
      rw [← Nat.sub_mul, show 64 * k - 24 * k = 40 * k by omega]
    have hcastb : ((64 * k * L : ℕ) : ℝ) = 64 * (k : ℝ) * (L : ℝ) := by push_cast; ring
    have hcasta : (((64 * k * L) - 24 * k * L : ℕ) : ℝ) = 40 * (k : ℝ) * (L : ℝ) := by
      rw [hsub]; push_cast; ring
    have h8 : ((64 * k * L : ℕ) : ℝ) / 8 = 8 * ((k : ℝ) * (L : ℝ)) := by
      rw [hcastb]; ring
    have h4 : 4 * C * (L : ℝ) = 4 * (C * (L : ℝ)) := by ring
    have h40 : (40 : ℝ) * (k : ℝ) * (L : ℝ) = 40 * ((k : ℝ) * (L : ℝ)) := by ring
    rw [h8, hcasta, h4, h40]
    have hxpos : (0 : ℝ) < (k : ℝ) * (L : ℝ) := by
      have : (0 : ℝ) < (k : ℝ) := by linarith
      exact mul_pos this hLpos
    have hy : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (k : ℝ) * (L : ℝ) := le_trans hnum hCL
    nlinarith [hCL, hy, hxpos]
  have hab : 24 * k * L ≤ 64 * k * L :=
    Nat.mul_le_mul_right L (Nat.mul_le_mul_right k (by norm_num))
  have hkL : 64 * k * L ≤ T * L := Nat.mul_le_mul_right L hT
  exact LocalFluid.runMaxI_gt_of_locOcc X hτ hC hocc hdr hL hij hab
    (le_trans hab hkL) hkL hlead hcount

/-- The level bound persists: at every integer time of the subwindow
`[τ_r + 64⌈C⌉L, τ_r + T L]` every walker's running maximum still exceeds `r + L`. -/
theorem runMaxI_gt_level_of_le (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {C CT : ℝ} (hC : 0 < C) {T L r : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT : 64 * Nat.ceil C ≤ T)
    {n : ℕ} (hn : τ r + 64 * Nat.ceil C * L ≤ n) :
    ∀ i : ι, (r : ℤ) + (L : ℤ) < runMaxI X i n := by
  have hlev := runMaxI_gt_level X hτ hC hocc hdr hL hij hnum hT
  intro i
  exact lt_of_lt_of_le (hlev i) (runMaxI_mono X i hn)

/-- Position lower bound in the lag subwindow: the level bound plus a lag bound `η` puts
every walker strictly above `r + L − η` at every integer time of the subwindow.  This is the
finite-`L` form of the paper's `m_i(u) = x_i(u)`, `u ≥ 64C`, used inside the record window. -/
theorem pos_gt_level_sub (X : ι → ℕ → ℤ) {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {C CT : ℝ} (hC : 0 < C) {T L r : ℕ} (hocc : LocOcc X τ C CT T L r)
    (hdr : defect X τ r ≤ (L : ℤ)) (hL : 1 ≤ L) {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : Numerics C CT L) (hT : 64 * Nat.ceil C ≤ T)
    {η : ℕ} (hlag : ∀ i : ι, lagI X i (τ r + 64 * Nat.ceil C * L) ≤ (η : ℤ))
    {n : ℕ} (hn : τ r + 64 * Nat.ceil C * L ≤ n)
    (htop : ∀ i : ι, ∀ u, τ r + 64 * Nat.ceil C * L ≤ u → u ≤ n → X i u ≤ X i n) :
    ∀ i : ι, (r : ℝ) + (L : ℝ) - (η : ℝ) < (X i n : ℝ) := by
  intro i
  have hlev := runMaxI_gt_level_of_le X hτ hC hocc hdr hL hij hnum hT hn i
  have hlag' : runMaxI X i n - X i n ≤ (η : ℤ) :=
    lag_le_of_lag_start hn (hlag i) (htop i)
  have : (r : ℤ) + (L : ℤ) - (η : ℤ) < X i n := by linarith
  have hcast : (((r : ℤ) + (L : ℤ) - (η : ℤ) : ℤ) : ℝ) < (X i n : ℝ) := by exact_mod_cast this
  push_cast at hcast
  linarith

/-! ## 4. The uniform epsilon allowance -/

/-- If the finite-`L` lag allowance is at most `ε L`, then at integer scale the paper's
`M^i_n − X^i_n = o(L)` is recovered as `M^i_n − X^i_n ≤ ε L`, uniformly over the subwindow.
No `η = 0` and no limit is asserted. -/
theorem lag_le_eps_mul_L {X : ι → ℕ → ℤ} {i : ι} {η : ℕ} {L : ℕ} {ε : ℝ}
    (h : lagI X i L ≤ (η : ℤ)) (hε : (η : ℝ) ≤ ε * (L : ℝ)) :
    ((lagI X i L : ℤ) : ℝ) ≤ ε * (L : ℝ) := by
  have : ((lagI X i L : ℤ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast h
  linarith

end JoinStep

/-! ## Axiom audit (source order) -/


