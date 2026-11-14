/-
# Finite-L gluing I: spread, the separated-pair predicate, and the potential bridge

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, Proposition `local`
(displays `(sep)`, `(locgroup)`, `(locmove)`, `(loccoord)`, `(Wpos)`) and the proof of
Proposition `tight` after `(Rlower)`.

This file contains no probability.  It sets up

* `sMax`, `sMin`, `sMaxM`, `spreadS` — extrema of a subfamily of walkers and the spread of
  such a subfamily at one integer time;
* `Sep X I J n` — the paper's display `(sep)` in pairwise form
  (`min_{i∈I} X_n^i ≥ max_{j∈J} M_n^j + 2` and `min_i X_n^i ≥ 0`);
* `Wst H X I J n` — the paper's potential difference
  `W_n^{I,J} = |I|^{-1} Σ_{i∈I} H_n^{I}(X_n^i) − max_{j∈J} H_n^{I}(X_n^j)`
  (the paper writes `H_n^{J^c}`; every use below has `J = univ \ I`, so `J^c = I`);
* `LocalField` — the **local-good field** at scale `(r,L,T)`: the paper's clauses `(loccoord)`
  (as `hcoord`), `(locmove)` (as `wmove`, with the source's **half-open** time set
  `∀ u ∈ [s,t)`), the spatial monotonicity/unit-increment facts of the potential (`hmono`,
  `hunit`), the finite-L lag bound `lag` (the second half of the paper's `(fluidmax)`) and the
  occupation input `(lococc)` (`LocalFluid.LocOcc`).  The stronger *closed*-interval separation
  `∀ u ∈ [s,t]` is never smuggled into this field: where a consumer needs the endpoint too
  (`Glue.run_le` uses `(Wpos)` at `t`), that premise is an explicit argument of that consumer.

From `hmono`/`hunit`/`hcoord` we **derive** the two comparisons the gluing uses:

* `Wst_nonneg_of_sep` — `0 ≤ W_n^{I,J}` on `(sep)` (the paper's `(Wpos)`);
* `Wst_le_of_sep` — on `(sep)`, `W_n^{I,J} ≤ C·(spread_I(n) + gap_J(n) + η) + C_T L^{3/4}`
  where `gap_J(n) = min_I X_n − max_J M_n` is the *separation*, i.e. the paper's
  "apply `(loccoord)` with `A = J^c`" step.  Note the separation, not the lag, is what
  `(loccoord)` bounds; the lag enters only through `max_J M − max_J X ≤ η`.
-/
import Swarm.LocalFluidAdvance

open Finset
open scoped BigOperators

namespace Glue

set_option linter.unusedSectionVars false

open RecordDefect LocalFluid MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. Extrema of a subfamily -/

/-- Maximum position over a subfamily at time `n` (`0` on the empty set). -/
noncomputable def sMax (X : ι → ℕ → ℤ) (S : Finset ι) (n : ℕ) : ℤ :=
  if h : S.Nonempty then S.sup' h (fun i => X i n) else 0

/-- Minimum position over a subfamily at time `n` (`0` on the empty set). -/
noncomputable def sMin (X : ι → ℕ → ℤ) (S : Finset ι) (n : ℕ) : ℤ :=
  if h : S.Nonempty then S.inf' h (fun i => X i n) else 0

/-- Maximum of the individual running maxima over a subfamily at time `n`. -/
noncomputable def sMaxM (X : ι → ℕ → ℤ) (S : Finset ι) (n : ℕ) : ℤ :=
  if h : S.Nonempty then S.sup' h (fun i => runMaxI X i n) else 0

/-- The spread of a subfamily at one integer time. -/
noncomputable def spreadS (X : ι → ℕ → ℤ) (S : Finset ι) (n : ℕ) : ℤ :=
  sMax X S n - sMin X S n

theorem sMax_of_nonempty {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (h : S.Nonempty) :
    sMax X S n = S.sup' h (fun i => X i n) := by
  unfold sMax
  rw [dif_pos h]

theorem sMin_of_nonempty {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (h : S.Nonempty) :
    sMin X S n = S.inf' h (fun i => X i n) := by
  unfold sMin
  rw [dif_pos h]

theorem sMaxM_of_nonempty {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (h : S.Nonempty) :
    sMaxM X S n = S.sup' h (fun i => runMaxI X i n) := by
  unfold sMaxM
  rw [dif_pos h]

theorem le_sMax {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {i : ι} (hi : i ∈ S) :
    X i n ≤ sMax X S n := by
  rw [sMax_of_nonempty hS]
  exact Finset.le_sup' (f := fun i => X i n) hi

theorem sMin_le {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {i : ι} (hi : i ∈ S) :
    sMin X S n ≤ X i n := by
  rw [sMin_of_nonempty hS]
  exact Finset.inf'_le (f := fun i => X i n) hi

theorem le_sMaxM {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {i : ι} (hi : i ∈ S) :
    runMaxI X i n ≤ sMaxM X S n := by
  rw [sMaxM_of_nonempty hS]
  exact Finset.le_sup' (f := fun i => runMaxI X i n) hi

theorem sMax_le {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {a : ℤ}
    (h : ∀ i ∈ S, X i n ≤ a) : sMax X S n ≤ a := by
  rw [sMax_of_nonempty hS]
  exact Finset.sup'_le hS (f := fun i => X i n) h

theorem sMin_le_of {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {a : ℤ}
    (h : ∀ i ∈ S, a ≤ X i n) : a ≤ sMin X S n := by
  rw [sMin_of_nonempty hS]
  exact Finset.le_inf' hS (f := fun i => X i n) h

theorem sMaxM_le {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {a : ℤ}
    (h : ∀ i ∈ S, runMaxI X i n ≤ a) : sMaxM X S n ≤ a := by
  rw [sMaxM_of_nonempty hS]
  exact Finset.sup'_le hS (f := fun i => runMaxI X i n) h

theorem exists_sMax {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) :
    ∃ i ∈ S, sMax X S n = X i n := by
  rw [sMax_of_nonempty hS]
  exact Finset.exists_mem_eq_sup' hS _

theorem exists_sMin {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) :
    ∃ i ∈ S, sMin X S n = X i n := by
  rw [sMin_of_nonempty hS]
  exact Finset.exists_mem_eq_inf' hS _

theorem exists_sMaxM {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) :
    ∃ i ∈ S, sMaxM X S n = runMaxI X i n := by
  rw [sMaxM_of_nonempty hS]
  exact Finset.exists_mem_eq_sup' hS _

theorem spreadS_nonneg {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) :
    0 ≤ spreadS X S n := by
  have hle : sMin X S n ≤ sMax X S n :=
    le_trans (sMin_le (X := X) (n := n) hS hS.choose_spec)
      (le_sMax (X := X) (n := n) hS hS.choose_spec)
  unfold spreadS
  linarith

theorem sub_spreadS {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {i j : ι}
    (hi : i ∈ S) (hj : j ∈ S) : X i n - X j n ≤ spreadS X S n := by
  have h1 : X i n ≤ sMax X S n := le_sMax hS hi
  have h2 : sMin X S n ≤ X j n := sMin_le hS hj
  unfold spreadS
  linarith

theorem spreadS_le {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) {d : ℤ}
    (h : ∀ i ∈ S, ∀ j ∈ S, X i n - X j n ≤ d) : spreadS X S n ≤ d := by
  obtain ⟨i, hi, hmax⟩ := exists_sMax (X := X) (S := S) (n := n) hS
  obtain ⟨j, hj, hmin⟩ := exists_sMin (X := X) (S := S) (n := n) hS
  unfold spreadS
  rw [hmax, hmin]
  exact h i hi j hj

theorem sMin_le_sMaxX {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) :
    sMin X S n ≤ sMax X S n :=
  le_trans (sMin_le hS hS.choose_spec) (le_sMax hS hS.choose_spec)

theorem spreadS_subset {X : ι → ℕ → ℤ} {S T : Finset ι} {n : ℕ} (hS : S.Nonempty)
    (hST : S ⊆ T) : spreadS X S n ≤ spreadS X T n := by
  have hT : T.Nonempty := hS.mono hST
  refine spreadS_le hS ?_
  intro i hi j hj
  exact sub_spreadS hT (hST hi) (hST hj)

theorem sMax_insert {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) (i : ι) :
    sMax X (insert i S) n = max (X i n) (sMax X S n) := by
  have hins : (insert i S).Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  refine le_antisymm (sMax_le hins ?_) (max_le ?_ ?_)
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact le_max_left _ _
    · exact le_trans (le_sMax hS hj') (le_max_right _ _)
  · exact le_sMax hins (Finset.mem_insert_self _ _)
  · exact sMax_le hS (fun j hj => le_sMax hins (Finset.mem_insert_of_mem hj))

theorem sMin_insert {X : ι → ℕ → ℤ} {S : Finset ι} {n : ℕ} (hS : S.Nonempty) (i : ι) :
    sMin X (insert i S) n = min (X i n) (sMin X S n) := by
  have hins : (insert i S).Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  refine le_antisymm (le_min ?_ ?_) (sMin_le_of hins ?_)
  · exact sMin_le hins (Finset.mem_insert_self _ _)
  · exact sMin_le_of hS (fun j hj => sMin_le hins (Finset.mem_insert_of_mem hj))
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (sMin_le hS hj')

/-- Splitting a family at one of its minima: the spread of `insert i S` is the spread of `S`
plus the gap from the new minimum up to `S`. -/
theorem spreadS_insert_min {X : ι → ℕ → ℤ} {S : Finset ι} {i : ι} {n : ℕ} (hS : S.Nonempty)
    (hmin : ∀ j ∈ S, X i n ≤ X j n) :
    spreadS X (insert i S) n = spreadS X S n + (sMin X S n - X i n) := by
  have hle : X i n ≤ sMin X S n := sMin_le_of hS hmin
  have hmax : sMax X (insert i S) n = sMax X S n := by
    rw [sMax_insert hS i]
    exact max_eq_right (le_trans hle (le_trans (sMin_le (X := X) (n := n) hS hS.choose_spec)
      (le_sMax (X := X) (n := n) hS hS.choose_spec)))
  have hmin' : sMin X (insert i S) n = X i n := by
    rw [sMin_insert hS i]
    exact min_eq_left hle
  unfold spreadS
  rw [hmax, hmin']
  ring

/-! ## 2. Positions stay in the paper's window range -/

/-- Upper bound: within `T L` steps of the record time of level `r` no walker exceeds `r + T L`. -/
theorem pos_le (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r T L n : ℕ} {i : ι} (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L) :
    X i n ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) := by
  have hstep := FluidBlock.step_le_add (X := X) hne i h1
  have hcast : ((n - τ r : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have h := Nat.sub_le_sub_right h2 (τ r)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hbase : X i (τ r) ≤ (r : ℤ) := le_trans (le_runMax (X := X) (τ r) i) (le_of_eq (hτ r).2)
  linarith

/-- Lower bound: on `{d_r ≤ L}` and within `T L` steps of `τ r` no walker is below
`r − L − T L`. -/
theorem pos_ge (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r L n : ℕ} {i : ι} (hdr : defect X τ r ≤ (L : ℤ)) (h1 : τ r ≤ n) :
    (r : ℤ) - (L : ℤ) - ((n - τ r : ℕ) : ℤ) ≤ X i n := by
  have hstep := step_lower (X := X) hne i h1
  have hbase : (r : ℤ) - (L : ℤ) ≤ X i (τ r) := tau_position_lower (X := X) hdr i
  linarith

/-- The paper's range condition `r − (T+2)L ≤ X_n^i` used by `(loccoord)`. -/
theorem pos_ge_range (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r T L n : ℕ} {i : ι} (hdr : defect X τ r ≤ (L : ℤ)) (h1 : τ r ≤ n)
    (h2 : n ≤ τ r + T * L) :
    (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ X i n := by
  have h : (r : ℤ) - (L : ℤ) - ((n - τ r : ℕ) : ℤ) ≤ X i n :=
    pos_ge (X := X) (i := i) hτ hne hdr h1
  have hcast : ((n - τ r : ℕ) : ℤ) ≤ ((T * L : ℕ) : ℤ) := by
    have hle := Nat.sub_le_sub_right h2 (τ r)
    rw [Nat.add_sub_cancel_left] at hle
    exact_mod_cast hle
  have hL : (((T + 2) * L : ℕ) : ℤ) = ((T * L : ℕ) : ℤ) + 2 * (L : ℤ) := by
    push_cast
    ring
  rw [hL]
  linarith

/-- Positivity inside the window, under the paper's `r ≥ (T+3)L`. -/
theorem pos_nonneg (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {r T L n : ℕ} {i : ι} (hdr : defect X τ r ≤ (L : ℤ)) (h1 : τ r ≤ n)
    (h2 : n ≤ τ r + T * L) (hr : (T + 3) * L ≤ r) :
    0 ≤ X i n := by
  have h : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ X i n :=
    pos_ge_range (X := X) (i := i) hτ hne hdr h1 h2
  have hr' : (((T + 2) * L : ℕ) : ℤ) ≤ (r : ℤ) := by
    have h1' : (T + 2) * L ≤ r := le_trans (Nat.mul_le_mul_right L (by omega)) hr
    exact_mod_cast h1'
  linarith

/-! ## 3. The separated-pair predicate `(sep)` -/

/-- The paper's `(sep)` for disjoint groups `I`, `J` at time `n`. -/
def Sep (X : ι → ℕ → ℤ) (I J : Finset ι) (n : ℕ) : Prop :=
  (∀ i ∈ I, 0 ≤ X i n) ∧ I.Nonempty ∧ J.Nonempty ∧
    ∀ i ∈ I, ∀ j ∈ J, runMaxI X j n + 2 ≤ X i n

theorem Sep.nonempty_left {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} (h : Sep X I J n) :
    I.Nonempty := h.2.1

theorem Sep.nonempty_right {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} (h : Sep X I J n) :
    J.Nonempty := h.2.2.1

theorem Sep.gap {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} (h : Sep X I J n) :
    sMaxM X J n + 2 ≤ sMin X I n := by
  obtain ⟨i, hi, hmin⟩ := exists_sMin (X := X) (S := I) (n := n) h.nonempty_left
  have hkey : sMaxM X J n + 2 ≤ X i n := by
    have h1 : sMaxM X J n ≤ X i n - 2 :=
      sMaxM_le h.nonempty_right (fun j hj => by linarith [h.2.2.2 i hi j hj])
    linarith
  rw [hmin]
  exact hkey

theorem Sep.pos {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} (h : Sep X I J n) {i : ι}
    (hi : i ∈ I) : 0 ≤ X i n := h.1 i hi

theorem Sep.gap_nonneg {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} (h : Sep X I J n) :
    2 ≤ sMin X I n - sMaxM X J n := by
  have := h.gap
  linarith

/-! ## 4. The potential difference `W` and the local-good field -/

/-- The paper's `W_n^{I,J}` with `H_n^{J^c}` replaced by `H I n`; every use has `J = univ \ I`. -/
noncomputable def Wst (H : Finset ι → ℕ → ℤ → ℤ) (X : ι → ℕ → ℤ) (I J : Finset ι)
    (n : ℕ) : ℝ :=
  if hJ : J.Nonempty then
    (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      - ((J.sup' hJ (fun j => H I n (X j n)) : ℤ) : ℝ)
  else 0

theorem Wst_of_nonempty {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ}
    (hJ : J.Nonempty) :
    Wst H X I J n = (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      - ((J.sup' hJ (fun j => H I n (X j n)) : ℤ) : ℝ) := by
  unfold Wst
  rw [dif_pos hJ]

/-- The **local-good field** of Proposition `local` at scale `(r,L,T)`, in the exact form the
deterministic gluing consumes.  `H` is the paper's `H_n^A` (spatial potential), `C` the paper's
`T`-free coefficient, `C_T` its `T`-dependent one and `η` the finite-L lag allowance (second
half of the paper's `(fluidmax)`). -/
structure LocalField (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ)
    (C CT : ℝ) (T L r : ℕ) (η : ℕ) : Prop where
  /-- The potential is nondecreasing in the spatial variable. -/
  hmono : ∀ (A : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → H A n x ≤ H A n y
  /-- The potential grows at least as fast as the identity (`h^w ≥ 1` in the paper). -/
  hunit : ∀ (A : Finset ι) (n : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H A n y - H A n x
  /-- The paper's `(loccoord)`. -/
  hcoord : ∀ (A : Finset ι) (n : ℕ), A.Nonempty → A ≠ Finset.univ → τ r ≤ n → n ≤ τ r + T * L →
    ∀ a0 b0 : ℤ, (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 → b0 ≤ sMaxM X A n →
    ((H A n b0 - H A n a0 : ℤ) : ℝ) ≤ C * ((b0 - a0 : ℤ) : ℝ) + CT * (L : ℝ) ^ (3 / 4 : ℝ)
  /-- The paper's `(locmove)`, stated for complementary groups **with the source's half-open
  time set**: `(sep)` is required at every integer `u ∈ [s,t)` only.  (`(locmove)`'s conclusion
  is `W_t − W_s ≤ … − (t−s)/C + …`, and the paper's proof sums the per-step drift over
  `u = s, …, t−1`.)  Consumers that also need `(sep)` at the right endpoint `t` — e.g. to apply
  `(Wpos)` there — must carry that as their own premise; see `Glue.run_le`. -/
  wmove : ∀ (A : Finset ι) (s t : ℕ), A.Nonempty → A ≠ Finset.univ → τ r ≤ s → s ≤ t →
    t ≤ τ r + T * L → (∀ u : ℕ, s ≤ u → u < t → Sep X A (Finset.univ \ A) u) →
    Wst H X A (Finset.univ \ A) t - Wst H X A (Finset.univ \ A) s
      ≤ C * (((sMaxM X A s : ℤ) : ℝ) - ((sMin X A s : ℤ) : ℝ)) - ((t - s : ℕ) : ℝ) / C
        + CT * (L : ℝ) ^ (3 / 4 : ℝ)
  /-- The finite-L lag bound: the second half of the paper's `(fluidmax)`. -/
  lag : ∀ (i : ι) (n : ℕ), τ r ≤ n → n ≤ τ r + T * L → runMaxI X i n - X i n ≤ (η : ℤ)
  /-- The paper's `(lococc)` at the initial record time. -/
  occ : LocOcc X τ C CT T L r

/-! ### 4.1 `max_J M − max_J X ≤ η` -/

theorem sMaxM_sub_sMax_le {X : ι → ℕ → ℤ} {J : Finset ι} {n : ℕ} (hJ : J.Nonempty)
    {η : ℕ} (hlag : ∀ j ∈ J, runMaxI X j n - X j n ≤ (η : ℤ)) :
    sMaxM X J n - sMax X J n ≤ (η : ℤ) := by
  obtain ⟨i, hi, hval⟩ := exists_sMaxM (X := X) (S := J) (n := n) hJ
  have h1 : runMaxI X i n - X i n ≤ (η : ℤ) := hlag i hi
  have h2 : X i n ≤ sMax X J n := le_sMax hJ hi
  rw [hval]
  linarith

/-! ### 4.2 The two derived comparisons -/

/-- `(Wpos)`: on `(sep)` the potential difference dominates the position gap. -/
theorem Wst_nonneg_of_sep {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ}
    (hmono : ∀ (A : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H A m x ≤ H A m y)
    (hunit : ∀ (A : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H A m y - H A m x)
    (hsep : Sep X I J n) :
    0 ≤ Wst H X I J n := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H I n (X j n)) : ℤ) = H I n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hmono I n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H I n (X j n)) hj0
  rw [Wst_of_nonempty (H := H) (X := X) (I := I) (n := n) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : ((H I n (sMin X I n) : ℤ) : ℝ)
      ≤ (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ)) / (I.card : ℝ) := by
    rw [le_div_iff₀ hcard]
    have hb : ∀ i ∈ I, H I n (sMin X I n) ≤ H I n (X i n) := by
      intro i hi
      exact hmono I n (sMin_le hI hi)
    calc ((H I n (sMin X I n) : ℤ) : ℝ) * (I.card : ℝ)
        = ∑ _i ∈ I, ((H I n (sMin X I n) : ℤ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
  have hle3 : sMax X J n ≤ sMin X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    linarith
  have hunit' : ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)
      ≤ ((H I n (sMin X I n) : ℤ) : ℝ) - ((H I n (sMax X J n) : ℤ) : ℝ) := by
    exact_mod_cast hunit I n hle3
  have hnonneg : (0 : ℝ) ≤ ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ sMin X I n - sMax X J n := by linarith
    exact_mod_cast this
  linarith

/-- `(Wpos)` in gap form: on `(sep)` the position gap is dominated by the potential difference. -/
theorem Wst_ge_gap {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ}
    (hmono : ∀ (A : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H A m x ≤ H A m y)
    (hunit : ∀ (A : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H A m y - H A m x)
    (hsep : Sep X I J n) :
    ((sMin X I n - sMax X J n : ℤ) : ℝ) ≤ Wst H X I J n := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H I n (X j n)) : ℤ) = H I n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hmono I n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H I n (X j n)) hj0
  rw [Wst_of_nonempty (H := H) (X := X) (I := I) (n := n) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : ((H I n (sMin X I n) : ℤ) : ℝ)
      ≤ (∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ)) / (I.card : ℝ) := by
    rw [le_div_iff₀ hcard]
    have hb : ∀ i ∈ I, H I n (sMin X I n) ≤ H I n (X i n) := by
      intro i hi
      exact hmono I n (sMin_le hI hi)
    calc ((H I n (sMin X I n) : ℤ) : ℝ) * (I.card : ℝ)
        = ∑ _i ∈ I, ((H I n (sMin X I n) : ℤ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ I, ((H I n (X i n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
  have hle3 : sMax X J n ≤ sMin X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    linarith
  have hunit' : ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)
      ≤ ((H I n (sMin X I n) : ℤ) : ℝ) - ((H I n (sMax X J n) : ℤ) : ℝ) := by
    exact_mod_cast hunit I n hle3
  have hcast : ((sMin X I n - sMax X J n : ℤ) : ℝ)
      = ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-- The paper's `(loccoord)` comparison for `W`: on `(sep)`,
`W_n^{I,J} ≤ C·(spread_I(n) + gap_J(n) + η) + C_T L^{3/4}` with
`gap_J(n) = min_I X_n − max_J M_n ≥ 2`. -/
theorem Wst_le_of_sep {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {C CT : ℝ}
    {T L r η : ℕ} (hLF : LocalField X τ H C CT T L r η) (hC : 0 ≤ C) {I J : Finset ι} {n : ℕ}
    (hsep : Sep X I J n) (hI' : I ≠ Finset.univ) (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J n) :
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
  have hb0 : sMax X I n ≤ sMaxM X I n := sMax_le hI (fun i hi => le_trans (le_runMaxI X i n) (le_sMaxM hI hi))
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
  have hlagJ : (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) ≤ (η : ℝ) := by
    have h := sMaxM_sub_sMax_le hJ (fun j hj => hLF.lag j n h1 h2)
    exact_mod_cast h
  have hcoord' : ((H I n (sMax X I n) - H I n (sMax X J n) : ℤ) : ℝ)
      ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ) + (η : ℝ))
        + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hcast1] at hcoord
    have hmul : C * (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ))
        ≤ C * (η : ℝ) := mul_le_mul_of_nonneg_left hlagJ hC
    linarith
  have hsplit2 : ((H I n (sMax X I n) : ℤ) : ℝ) - ((H I n (sMax X J n) : ℤ) : ℝ)
      = ((H I n (sMax X I n) - H I n (sMax X J n) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [Wst_of_nonempty (H := H) (X := X) (I := I) (n := n) hJ, hsup]
  linarith [hcoord', havg, hsplit2]

end Glue
