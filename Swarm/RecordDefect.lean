/-
The record/defect combinatorics of §2.4 of `main_1d_revised.tex` (Proposition `tight`).

The paper defines, for `r ≥ 0`,
  `τ_r = inf {n : max_i X_n^i = r}`,   `d_r = r - min_i X_{τ_r}^i`,
and then uses three purely combinatorial facts in the proof of the block estimate:

* `τ_r ≥ r` and (nearest-neighbour) `d_u ≤ (u - r) + d_r + (τ_u - τ_r)` for `u ≥ r`;
* hence, on `{d_r ≤ L}` and `{τ_{r+BL} - τ_r ≤ TL}`, the *third* inequality of (block):
  `max_{r ≤ u ≤ r+BL} d_u ≤ (B + T + 1) L`;
* `d_r ≥ 0`.

* and finally the paper's (recordo): if the spread `max_i X_n^i - min_i X_n^i` is `o(n)`
  and the record times grow at most linearly, then `d_r / r → 0`.

All of these are proved for an abstract nearest-neighbour walker family with prescribed
record times.  Nothing probabilistic is assumed: `τ` is an arbitrary sequence of integers
satisfying the first-hitting description `IsRecord`, which is how the paper uses these
facts (the probabilistic content is in the finiteness of `τ_r`).
-/
import Swarm.Imports

open Filter Topology MeasureTheory
open scoped BigOperators

namespace RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The running maximum `M_n = max_i X_n^i`. -/
noncomputable def runMax (X : ι → ℕ → ℤ) (n : ℕ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => X i n

/-- The running minimum `min_i X_n^i`. -/
noncomputable def runMin (X : ι → ℕ → ℤ) (n : ℕ) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => X i n

/-- `τ` is the sequence of record times: `τ r` is the first time the running maximum is `r`. -/
def IsRecord (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, (∀ n, n < τ r → runMax X n < (r : ℤ)) ∧ runMax X (τ r) = (r : ℤ)

/-- The paper's defect `d_r = r - min_i X_{τ_r}^i`. -/
noncomputable def defect (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (r : ℕ) : ℤ :=
  (r : ℤ) - runMin X (τ r)

variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

lemma le_runMax (n : ℕ) (i : ι) : X i n ≤ runMax X n :=
  Finset.le_sup' (fun i => X i n) (Finset.mem_univ i)

lemma runMin_le (n : ℕ) (i : ι) : runMin X n ≤ X i n :=
  Finset.inf'_le (fun i => X i n) (Finset.mem_univ i)

lemma runMin_le_runMax (n : ℕ) : runMin X n ≤ runMax X n :=
  le_trans (runMin_le n (Classical.arbitrary ι)) (le_runMax n _)

/-- Nearest-neighbour steps imply the walker cannot be lower than `X i m - (k - m)` at time `k`. -/
theorem step_lower (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (i : ι) :
    ∀ {m k : ℕ}, m ≤ k → X i m - ((k - m : ℕ) : ℤ) ≤ X i k := by
  intro m k hmk
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
      have hstep : X i k - 1 ≤ X i (k + 1) := by
        have h1 : |X i (k + 1) - X i k| ≤ 1 := le_of_eq (hne i k)
        have := (abs_le.1 h1).1
        linarith
      have hcast : ((k + 1 - m : ℕ) : ℤ) = ((k - m : ℕ) : ℤ) + 1 := by
        have : k + 1 - m = (k - m) + 1 := by omega
        rw [this]
        push_cast
        ring
      rw [hcast]
      linarith

/-- `τ` is monotone in the record level. -/
theorem tau_mono (hτ : IsRecord X τ) : Monotone τ := by
  intro r r' hr
  by_contra hlt
  rw [not_le] at hlt
  have h1 := (hτ r).1 (τ r') hlt
  have h2 := (hτ r').2
  have : (r : ℤ) ≤ (r' : ℤ) := by exact_mod_cast hr
  linarith

/-- `d_r ≥ 0`: at the record time the minimum does not exceed the maximum `r`. -/
theorem defect_nonneg (hτ : IsRecord X τ) (r : ℕ) : 0 ≤ defect X τ r := by
  rw [defect, ← (hτ r).2]
  linarith [runMin_le_runMax (X := X) (τ r)]

/-- **Key combinatorial estimate**: the defect at a later record level is controlled by the
defect at `r`, the number of extra levels, and the elapsed record time. -/
theorem defect_le (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {r u : ℕ} (hru : r ≤ u) :
    defect X τ u ≤ ((u : ℤ) - (r : ℤ)) + defect X τ r
      + ((τ u : ℤ) - (τ r : ℤ)) := by
  have hmono : τ r ≤ τ u := tau_mono hτ hru
  obtain ⟨j, -, hval⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty (fun i => X i (τ u))
  -- the minimiser at time `τ u` is at most `Δ` below its own position at time `τ r`
  have hlow : X j (τ r) - ((τ u : ℤ) - (τ r : ℤ)) ≤ X j (τ u) := by
    have h := step_lower hne j hmono
    have hcast : ((τ u - τ r : ℕ) : ℤ) = (τ u : ℤ) - (τ r : ℤ) := by
      push_cast [hmono]; ring
    linarith
  have hminr : runMin X (τ r) ≤ X j (τ r) := runMin_le _ _
  have hkey : runMin X (τ r) - ((τ u : ℤ) - (τ r : ℤ)) ≤ runMin X (τ u) := by
    have hval' : runMin X (τ u) = X j (τ u) := hval
    rw [hval']
    linarith
  rw [defect, defect]
  linarith

/-- **Third inequality of (block)** in Proposition `tight`: if the defect at level `r` is at
most `L` and the record advance from `r` to `r + B L` takes at most `T L` steps, then the defect
stays below `(B + T + 1) L` for every intermediate level. -/
theorem block_defect_bound (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {L B T r : ℕ} (hr : defect X τ r ≤ (L : ℤ))
    (hτBL : τ (r + B * L) - τ r ≤ T * L) :
    ∀ u : ℕ, r ≤ u → u ≤ r + B * L → defect X τ u ≤ ((B + T + 1 : ℕ) : ℤ) * (L : ℤ) := by
  intro u hru huBL
  have hmono : τ r ≤ τ u := tau_mono hτ hru
  have hmono2 : τ u ≤ τ (r + B * L) := tau_mono hτ huBL
  have helapsed : ((τ u : ℤ) - (τ r : ℤ)) ≤ ((T * L : ℕ) : ℤ) := by
    have h1 : ((τ u - τ r : ℕ) : ℤ) ≤ ((τ (r + B * L) - τ r : ℕ) : ℤ) := by
      exact_mod_cast Nat.sub_le_sub_right hmono2 (τ r)
    have h2 : ((τ (r + B * L) - τ r : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
      exact_mod_cast hτBL
    have h3 : ((τ u - τ r : ℕ) : ℤ) = (τ u : ℤ) - (τ r : ℤ) := by
      push_cast [hmono]; ring
    linarith
  have hlevels : ((u : ℤ) - (r : ℤ)) ≤ ((B * L : ℕ) : ℤ) := by
    have : u - r ≤ B * L := by omega
    have h2 : ((u - r : ℕ) : ℤ) ≤ ((B * L : ℕ) : ℤ) := by exact_mod_cast this
    have h3 : ((u - r : ℕ) : ℤ) = (u : ℤ) - (r : ℤ) := by push_cast [hru]; ring
    linarith
  have key := defect_le hτ hne hru
  have hBL : ((B * L : ℕ) : ℤ) = (B : ℤ) * (L : ℤ) := by push_cast; ring
  have hTL : ((T * L : ℕ) : ℤ) = (T : ℤ) * (L : ℤ) := by push_cast; ring
  have htarget : ((B + T + 1 : ℕ) : ℤ) * (L : ℤ)
      = (B : ℤ) * (L : ℤ) + (T : ℤ) * (L : ℤ) + (L : ℤ) := by push_cast; ring
  rw [htarget]
  linarith [defect_nonneg hτ r]

/-- The spread `max_i X_n^i - min_i X_n^i` of the configuration. -/
noncomputable def spread (X : ι → ℕ → ℤ) (n : ℕ) : ℝ :=
  ((runMax X n - runMin X n : ℤ) : ℝ)

/-- At a record time the defect **is** the spread. -/
theorem defect_eq_spread (hτ : IsRecord X τ) (r : ℕ) :
    (defect X τ r : ℝ) = spread X (τ r) := by
  have h := (hτ r).2
  rw [defect, spread, h]

/-- **Equation (recordo)** of the paper: if the spread is `o(n)` and the record times grow at
most linearly (`τ_r ≤ C r`, the consequence of the ballistic lower bound), then `d_r / r → 0`. -/
theorem defect_div_tendsto_zero (hτ : IsRecord X τ) (hτge : ∀ r, r ≤ τ r)
    {C : ℝ} (hC : 0 < C) (hτC : ∀ r : ℕ, 1 ≤ r → (τ r : ℝ) ≤ C * (r : ℝ))
    (hlim : Tendsto (fun n => spread X n / n) atTop (𝓝 0)) :
    Tendsto (fun r => (defect X τ r : ℝ) / r) atTop (𝓝 0) := by
  have hτtop : Tendsto τ atTop atTop := tendsto_atTop_mono hτge tendsto_id
  have hcomp : Tendsto (fun r => spread X (τ r) / (τ r)) atTop (𝓝 0) := hlim.comp hτtop
  have hu : Tendsto (fun r => |spread X (τ r) / (τ r)|) atTop (𝓝 0) := by
    have h : Tendsto (fun r => |spread X (τ r) / (τ r)|) atTop (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto (0 : ℝ)).comp hcomp
    simpa using h
  have hCu : Tendsto (fun r : ℕ => C * |spread X (τ r) / (τ r)|) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℕ => C * |spread X (τ r) / (τ r)|) atTop (𝓝 (C * 0)) :=
      Tendsto.mul (tendsto_const_nhds (x := C)) hu
    simpa using h
  have hbound : ∀ r : ℕ,
      |spread X (τ r) / (r : ℝ)| ≤ C * |spread X (τ r) / (τ r)| := by
    intro r
    rcases Nat.eq_zero_or_pos r with hzero | hr0
    · subst hzero
      simp only [Nat.cast_zero, div_zero, abs_zero]
      exact mul_nonneg (le_of_lt hC) (abs_nonneg _)
    · have hrC : (τ r : ℝ) ≤ C * (r : ℝ) := hτC r hr0
      have hr0' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
      have hτ0pos : 0 < τ r := lt_of_lt_of_le hr0 (hτge r)
      have hτ0' : (0 : ℝ) < (τ r : ℝ) := by exact_mod_cast hτ0pos
      have hτr_le : (τ r : ℝ) / (r : ℝ) ≤ C := by
        rw [div_le_iff₀ hr0']
        linarith
      have h1nn : (0 : ℝ) ≤ (τ r : ℝ) / (r : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt hr0')
      have hstep : |spread X (τ r) / (r : ℝ)|
          = |spread X (τ r) / (τ r : ℝ)| * ((τ r : ℝ) / (r : ℝ)) := by
        rw [← abs_of_nonneg h1nn, ← abs_mul]
        congr 1
        field_simp
      rw [hstep]
      calc |spread X (τ r) / (τ r : ℝ)| * ((τ r : ℝ) / (r : ℝ))
          ≤ |spread X (τ r) / (τ r : ℝ)| * C :=
            mul_le_mul_of_nonneg_left hτr_le (abs_nonneg _)
        _ = C * |spread X (τ r) / (τ r)| := by ring
  have hmain : Tendsto (fun r => spread X (τ r) / (r : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using
      squeeze_zero (fun r => abs_nonneg (spread X (τ r) / (r : ℝ))) hbound hCu
  refine hmain.congr' ?_
  filter_upwards with r
  rw [defect_eq_spread hτ r]


end RecordDefect
