/-
# Finite-scale `(coincide)` for an arbitrary block of walkers

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, Proposition `local`
and the proof of Proposition `tight`, Section 4.1 (the order-statistic induction proving
`(coincide)`) together with Section 4.2 (leader persistence) and Section 5.1 (the finite
number of meets).

The accepted deterministic packages (`Glue`, `JoinStep`) prove the order-statistic
induction only for the **whole pack** `D = univ`, because their drift clause `(locmove)`
is stated for the complementary pair `(A, Aᶜ)` and their potential `Glue.Wst` uses the
potential family indexed by the block `A` itself.  The source's Section 4.1 induction,
however, is run on an **arbitrary** nonempty `D ⊂ {1,…,N}`, at its top blocks `I ⊊ D`
with `J = D \ I`, and uses `(locgroup)`, which the source states for **all disjoint
nonempty** `I, J`, with the potential `H^{J^c}`; see `main_1d.tex` lines 1006–1010
(`locgroup`), 1189–1194 (its proof), and 1326–1334 (its use inside `(coincide)`).

This file supplies exactly that gap, deterministically and at finite `L`:

* `Wpot H X A I J n` — the paper's `W_n^{I,J}` with the potential family `A = Jᶜ` kept as
  a separate argument, so that general (not necessarily complementary) `I, J` are
  handled.  `Glue.Wst` is the special case `A = I`.
* `Wpot_nonneg_of_sep`, `Wpot_ge_gap` — `(Wpos)`, and `Wpot_le_of_sep` — the `(loccoord)`
  comparison, both for general `A`.
* `not_sep_gap_le_gen`, `gap_at_failure_gen` — the two `(sep)`-failure facts of the
  source (the "`1 + o(L)`" and the post-failure "`2`") for general disjoint `I, J`.
* `BlockClauses` — `JoinStep.LocalClauses` plus the source's `(locgroup)`, i.e. the
  honest general-pair drift clause; the accepted `(locmove)` is not used and is not
  smuggled into `(locgroup)`.
* `join_gap_of_block` — the join-gap step of the induction for a top block `I ⊊ D` of an
  arbitrary ambient block `D`.
* `spread_block_le` — **the paper's `(coincide)` for a general block**: the spread of
  `D` is bounded by `β D.card` throughout the subwindow, where `β` is any sequence with
  `β 1 ≥ 0` and the source's geometric step.
* `spread_block_univ` — the `D = univ` instance, matching the accepted whole-pack form.
* `block_push`, `block_spread_of_top` — the merge/persistence corollaries (Section 4.2
  and 5.1): adjoining the best outside walker keeps a top block, raises the cardinality
  by one and the spread by at most `1 + η`, and the enlarged block's spread is again
  bounded by the corresponding `β` on the remaining window.

No probability, no limit, no `NoCoalescence`, and no stationary/invariant input appears.
-/
import Swarm.FreshCoalesce

open Finset
open scoped BigOperators

namespace BlkCoin

open RecordDefect LocalFluid MeasureTheory Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The potential `W^{I,J}` with the source's potential family `A = Jᶜ` -/

/-- The paper's `W_n^{I,J}` with the potential family `A` (the source takes `A = Jᶜ`) kept
explicit.  `Glue.Wst H X I J n` is the case `A = I`, which is the same thing only for
complementary pairs. -/
noncomputable def Wpot (H : Finset ι → ℕ → ℤ → ℤ) (X : ι → ℕ → ℤ)
    (A I J : Finset ι) (n : ℕ) : ℝ :=
  if hJ : J.Nonempty then
    (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      - ((J.sup' hJ (fun j => H A n (X j n)) : ℤ) : ℝ)
  else 0

theorem Wpot_of_nonempty {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A I J : Finset ι}
    {n : ℕ} (hJ : J.Nonempty) :
    Wpot H X A I J n = (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      - ((J.sup' hJ (fun j => H A n (X j n)) : ℤ) : ℝ) := by
  unfold Wpot
  rw [dif_pos hJ]

/-- `(Wpos)` for a general potential family: on `(sep)` the potential difference is
nonnegative.  This is `Glue.Wst_nonneg_of_sep` with the potential index decoupled from the
block index. -/
theorem Wpot_nonneg_of_sep {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A I J : Finset ι}
    {n : ℕ}
    (hmono : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H B m x ≤ H B m y)
    (hunit : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H B m y - H B m x)
    (hsep : Sep X I J n) :
    0 ≤ Wpot H X A I J n := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hmono A n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H A n (X j n)) hj0
  rw [Wpot_of_nonempty (H := H) (X := X) (A := A) (I := I) (n := n) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : ((H A n (sMin X I n) : ℤ) : ℝ)
      ≤ (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ) := by
    rw [le_div_iff₀ hcard]
    have hb : ∀ i ∈ I, H A n (sMin X I n) ≤ H A n (X i n) := by
      intro i hi
      exact hmono A n (sMin_le hI hi)
    calc ((H A n (sMin X I n) : ℤ) : ℝ) * (I.card : ℝ)
        = ∑ _i ∈ I, ((H A n (sMin X I n) : ℤ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
  have hle3 : sMax X J n ≤ sMin X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    linarith
  have hunit' : ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)
      ≤ ((H A n (sMin X I n) : ℤ) : ℝ) - ((H A n (sMax X J n) : ℤ) : ℝ) := by
    exact_mod_cast hunit A n hle3
  have hnonneg : (0 : ℝ) ≤ ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ sMin X I n - sMax X J n := by linarith
    exact_mod_cast this
  linarith

/-- `(Wpos)` in gap form for a general potential family. -/
theorem Wpot_ge_gap {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A I J : Finset ι}
    {n : ℕ}
    (hmono : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H B m x ≤ H B m y)
    (hunit : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H B m y - H B m x)
    (hsep : Sep X I J n) :
    ((sMin X I n - sMax X J n : ℤ) : ℝ) ≤ Wpot H X A I J n := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hmono A n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H A n (X j n)) hj0
  rw [Wpot_of_nonempty (H := H) (X := X) (A := A) (I := I) (n := n) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : ((H A n (sMin X I n) : ℤ) : ℝ)
      ≤ (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ) := by
    rw [le_div_iff₀ hcard]
    have hb : ∀ i ∈ I, H A n (sMin X I n) ≤ H A n (X i n) := by
      intro i hi
      exact hmono A n (sMin_le hI hi)
    calc ((H A n (sMin X I n) : ℤ) : ℝ) * (I.card : ℝ)
        = ∑ _i ∈ I, ((H A n (sMin X I n) : ℤ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
  have hle3 : sMax X J n ≤ sMin X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    have hle4 : sMin X I n ≤ sMax X I n := sMin_le_sMaxX hI
    linarith
  have hunit' : ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)
      ≤ ((H A n (sMin X I n) : ℤ) : ℝ) - ((H A n (sMax X J n) : ℤ) : ℝ) := by
    exact_mod_cast hunit A n hle3
  have hcast : ((sMin X I n - sMax X J n : ℤ) : ℝ)
      = ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  linarith [hunit', havg, hsup]

/-- The `(loccoord)` comparison for a general potential family: on `(sep)`,
`W_n^{I,J} ≤ C·(spread_I(n) + (min_I X_n − max_J M_n) + η) + C_T L^{3/4}`.
The potential family `A` must contain `I` (so that `(loccoord)` can be applied at
`b_0 = max_I X_n`) and must be a nonempty proper subset of the index set. -/
theorem Wpot_le_of_sep {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} {A I J : Finset ι} {n : ℕ}
    (hcoord : ∀ (B : Finset ι) (m : ℕ), B.Nonempty → B ≠ Finset.univ →
      τ r ≤ m → m ≤ τ r + T * L →
      ∀ a0 b0 : ℤ, (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 → b0 ≤ sMaxM X B m →
      ((H B m b0 - H B m a0 : ℤ) : ℝ) ≤ C * ((b0 - a0 : ℤ) : ℝ) + CT * (L : ℝ) ^ (3 / 4 : ℝ))
    (hmono : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H B m x ≤ H B m y)
    (hC : 0 ≤ C)
    (hsep : Sep X I J n) (hIA : I ⊆ A) (hAne : A.Nonempty) (hA' : A ≠ Finset.univ)
    (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J n)
    (hlag : ∀ j ∈ J, runMaxI X j n - X j n ≤ (η : ℤ)) :
    Wpot H X A I J n ≤ C * (((spreadS X I n : ℤ) : ℝ)
      + ((sMin X I n - sMaxM X J n : ℤ) : ℝ) + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  have hsup : (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) := by
    refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
    · intro j hj
      exact hmono A n (le_sMax hJ hj)
    · rw [hval]
      exact Finset.le_sup' (f := fun j => H A n (X j n)) hj0
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ)) / (I.card : ℝ)
      ≤ ((H A n (sMax X I n) : ℤ) : ℝ) := by
    rw [div_le_iff₀ hcard]
    have hb : ∀ i ∈ I, H A n (X i n) ≤ H A n (sMax X I n) := by
      intro i hi
      exact hmono A n (le_sMax hI hi)
    calc (∑ i ∈ I, ((H A n (X i n) : ℤ) : ℝ))
        ≤ ∑ _i ∈ I, ((H A n (sMax X I n) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
      _ = ((H A n (sMax X I n) : ℤ) : ℝ) * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb0 : sMax X I n ≤ sMaxM X A n := by
    have h1' : sMax X I n ≤ sMax X A n := by
      refine sMax_le hI (fun i hi => ?_)
      exact le_sMax hAne (hIA hi)
    refine le_trans h1' (sMax_le hAne (fun i hi => le_trans (le_runMaxI X i n) (le_sMaxM hAne hi)))
  have hle0 : sMax X J n ≤ sMax X I n := by
    have hg := hsep.gap
    have hle2 : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    have hle4 : sMin X I n ≤ sMax X I n := sMin_le_sMaxX hI
    linarith
  have hcoord' := hcoord A n hAne hA' h1 h2 (sMax X J n) (sMax X I n) hlo hle0 hb0
  have hcast1 : (((sMax X I n - sMax X J n : ℤ)) : ℝ)
      = ((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ)
        + (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) := by
    unfold spreadS
    push_cast
    ring
  have hlagJ : (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)) ≤ (η : ℝ) := by
    have h := sMaxM_sub_sMax_le (X := X) (J := J) (n := n) hJ hlag
    exact_mod_cast h
  have hmul : C * (((sMaxM X J n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ))
      ≤ C * (η : ℝ) := mul_le_mul_of_nonneg_left hlagJ hC
  have hcoord'' : ((H A n (sMax X I n) - H A n (sMax X J n) : ℤ) : ℝ)
      ≤ C * (((spreadS X I n : ℤ) : ℝ) + ((sMin X I n - sMaxM X J n : ℤ) : ℝ) + (η : ℝ))
        + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hcast1] at hcoord'
    linarith [hcoord', hmul]
  have hsplit2 : ((H A n (sMax X I n) : ℤ) : ℝ) - ((H A n (sMax X J n) : ℤ) : ℝ)
      = ((H A n (sMax X I n) - H A n (sMax X J n) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [Wpot_of_nonempty (H := H) (X := X) (A := A) (I := I) (n := n) hJ, hsup]
  linarith [hcoord'', havg, hsplit2]

/-! ## 2. The two `(sep)`-failure facts for general disjoint groups -/

/-- **The paper's first branch** (`main_1d.tex`, the `(coincide)` proof): if `(sep)` fails
at `n` for disjoint nonempty `I, J` while all positions are nonnegative, then the
separation is at most `1 + η`.  `JoinStep.not_sep_gap_le` is the complementary case. -/
theorem not_sep_gap_le_gen {X : ι → ℕ → ℤ} {η : ℕ} {I J : Finset ι} {n : ℕ}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hpos : ∀ i, 0 ≤ X i n)
    (hlag : ∀ j ∈ J, runMaxI X j n - X j n ≤ (η : ℤ))
    (hnot : ¬ Sep X I J n) :
    sMin X I n - sMax X J n ≤ 1 + (η : ℤ) := by
  have hpair : ∃ i ∈ I, ∃ j ∈ J, X i n ≤ runMaxI X j n + 1 := by
    by_contra hcon
    apply hnot
    refine ⟨fun i _ => hpos i, hI, hJ, ?_⟩
    intro i hi j hj
    by_contra hlt
    push_neg at hlt
    exact hcon ⟨i, hi, j, hj, by omega⟩
  obtain ⟨i0, hi0, j0, hj0, hle0⟩ := hpair
  have h1 : sMin X I n ≤ X i0 n := sMin_le hI hi0
  have h2 : runMaxI X j0 n ≤ sMaxM X J n := le_sMaxM hJ hj0
  have h3 : sMaxM X J n ≤ sMax X J n + (η : ℤ) := by
    have := sMaxM_sub_sMax_le (X := X) (J := J) (n := n) hJ hlag
    linarith
  linarith

/-- **The post-failure gap.**  If `(sep)` for general `I, J` fails at `v - 1` while all
positions are nonnegative there, then at `v` the separation is at most `2`
(nearest-neighbour motion plus monotonicity of the running maxima).
`Glue.gap_at_failure` is the complementary case. -/
theorem gap_at_failure_gen {X : ι → ℕ → ℤ} (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    {I J : Finset ι} {v : ℕ} (hI : I.Nonempty) (hJ : J.Nonempty) (hv : 1 ≤ v)
    (hpos : ∀ i, 0 ≤ X i (v - 1)) (hnot : ¬ Sep X I J (v - 1)) :
    sMin X I v - sMaxM X J v ≤ 2 := by
  have hpair : ∃ i ∈ I, ∃ j ∈ J, X i (v - 1) ≤ runMaxI X j (v - 1) + 1 := by
    by_contra hcon
    apply hnot
    refine ⟨fun i _ => hpos i, hI, hJ, ?_⟩
    intro i hi j hj
    by_contra hlt
    push_neg at hlt
    exact hcon ⟨i, hi, j, hj, by omega⟩
  obtain ⟨i0, hi0, j0, hj0, hle0⟩ := hpair
  have h1 : sMin X I (v - 1) ≤ X i0 (v - 1) := sMin_le hI hi0
  have h3 : runMaxI X j0 (v - 1) ≤ sMaxM X J (v - 1) := le_sMaxM hJ hj0
  have h4 : sMaxM X J (v - 1) ≤ sMaxM X J v := sMaxM_mono hJ (by omega)
  have h5 : sMin X I v ≤ sMin X I (v - 1) + 1 := by
    have h := sMin_step hne hI (v - 1)
    have hv' : v - 1 + 1 = v := by omega
    rwa [hv'] at h
  linarith

end BlkCoin

namespace BlkCoin

open RecordDefect LocalFluid MeasureTheory Glue

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 3. Top blocks of an arbitrary ambient block `D` -/

/-- `I` is a block of `|I|` largest positions **inside `D`**: every element of `I` is
dominates every element of `D \ I`.  `JoinStep.TopBlock` is the case `D = univ`. -/
def TopBlockIn (X : ι → ℕ → ℤ) (D I : Finset ι) (n : ℕ) : Prop :=
  I ⊆ D ∧ ∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j n ≤ X i n

theorem topBlockIn_self (X : ι → ℕ → ℤ) (D : Finset ι) (n : ℕ) : TopBlockIn X D D n :=
  ⟨subset_rfl, fun i _ j hjD hji => absurd hjD hji⟩

/-- The separation of a block from the rest **of `D`** is at most the spread of `D`. -/
theorem gap_le_spread_of_subset {X : ι → ℕ → ℤ} {D I : Finset ι} {n : ℕ}
    (hI : I.Nonempty) (hID : I ⊆ D) (hJ : (D \ I).Nonempty) :
    sMin X I n - sMax X (D \ I) n ≤ spreadS X D n := by
  have hD : D.Nonempty := hI.mono hID
  obtain ⟨j0, hj0, -⟩ := exists_sMax (X := X) (S := D \ I) (n := n) hJ
  have hj0D : j0 ∈ D := (Finset.mem_sdiff.mp hj0).1
  have h1 : sMin X D n ≤ sMin X I n := by
    obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := I) (n := n) hI
    rw [hval]
    exact sMin_le hD (hID hi)
  have h2 : sMin X D n ≤ X j0 n := sMin_le hD hj0D
  have h3 : X j0 n ≤ sMax X (D \ I) n := le_sMax hJ hj0
  have h4 : sMin X I n ≤ sMax X D n := by
    obtain ⟨i, hi, hval⟩ := exists_sMin (X := X) (S := I) (n := n) hI
    rw [hval]
    exact le_sMax hD (hID hi)
  unfold spreadS
  linarith

/-! ## 4. The source's `(locgroup)` for general disjoint groups -/

/-- `JoinStep.LocalClauses` together with the source's `(locgroup)` for **all** disjoint
nonempty groups `I, J`, with the potential `H^{Jᶜ}`.  This is exactly the clause the
paper states (`main_1d.tex`, display `(locgroup)`) and exactly the clause its `(coincide)`
induction consumes; `(locmove)` is not equivalent to it on non-complementary pairs. -/
structure BlockClauses (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ)
    (C CT : ℝ) (T L r : ℕ) : Prop where
  /-- `(loccoord)`, `(locmove)`, `(lococc)`, potential monotonicity and `h^w ≥ 1`. -/
  base : JoinStep.LocalClauses X τ H C CT T L r
  /-- The paper's `(locgroup)`: for disjoint nonempty `I, J`, if `(sep)` holds at every
  integer time of `[s,t)` then the potential difference `W^{I,J}` grows by at most
  `C_T L^{3/4}`. -/
  group : ∀ (I J : Finset ι), Disjoint I J → I.Nonempty → J.Nonempty →
    ∀ s t : ℕ, τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Sep X I J u) →
    Wpot H X (Finset.univ \ J) I J t - Wpot H X (Finset.univ \ J) I J s
      ≤ CT * (L : ℝ) ^ (3 / 4 : ℝ)

/-! ## 5. The join-gap step for a top block of `D` -/

/-- **The join-gap step of the source's `(coincide)`, for a general ambient block `D`.**

Let `I ⊊ D` be a block of `k` largest positions of `D` at time `n`, all inside the
subwindow `[n₀,n₁] ⊆ [τ_r, τ_r + TL]` of a record window with `d_r ≤ L`.  If every block of
`k` largest positions of `D` has spread at most `b` throughout the window, then the
separation of `I` from `D \ I` at `n` is at most the geometric step
`Gstep C CT L η β₀ b = max (1+η) (2C(b + β₀ + η + 2) + 2 C_T L^{3/4})`.

Both branches of the source are present: `(sep)` at `n` (run start `u`, `(loccoord)` at `u`,
`(Wpos)` at `n`, and the `(locgroup)` drift from `u` to `n`), and `¬(sep)` at `n`
(then the separation is at most `1 + η`). -/
theorem join_gap_of_block {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hBC : BlockClauses X τ H C CT T L r) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    {D : Finset ι} {β₀ b : ℝ} (hb0 : 0 ≤ b) (hβ₀ : (spreadS X D n₀ : ℝ) ≤ β₀)
    (hlag : ∀ (i : ι) (u : ℕ), n₀ ≤ u → u ≤ n₁ → runMaxI X i u - X i u ≤ (η : ℤ))
    {k : ℕ} (hIH : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ I : Finset ι, I.card = k →
      TopBlockIn X D I u → (spreadS X I u : ℝ) ≤ b)
    {n : ℕ} (hn : n₀ ≤ n) (hn' : n ≤ n₁)
    {I : Finset ι} (hIcard : I.card = k) (hID : I ⊆ D) (hIne : I.Nonempty) (hI' : I ≠ D)
    (htop : ∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j n ≤ X i n) :
    ((sMin X I n - sMax X (D \ I) n : ℤ) : ℝ) ≤ JoinStep.Gstep C CT L η β₀ b := by
  classical
  have hD : D.Nonempty := hIne.mono hID
  have hβ₀nn : 0 ≤ β₀ := by
    have h0 : (0 : ℝ) ≤ (spreadS X D n₀ : ℝ) := by
      have := spreadS_nonneg (X := X) (S := D) (n := n₀) hD
      exact_mod_cast this
    linarith
  have hJne : (D \ I).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hI' (Finset.Subset.antisymm hID hsub)
  -- the potential family `A = (D \ I)ᶜ`
  have hIA : I ⊆ Finset.univ \ (D \ I) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun hc => (Finset.mem_sdiff.mp hc).2 hi⟩
  have hAne : (Finset.univ \ (D \ I)).Nonempty := hIne.mono hIA
  have hA' : (Finset.univ \ (D \ I)) ≠ Finset.univ := by
    intro hc
    have hsub : Finset.univ ⊆ Finset.univ \ (D \ I) := by rw [hc]
    obtain ⟨j, hj⟩ := hJne
    exact (Finset.mem_sdiff.mp (hsub (Finset.mem_univ j))).2 hj
  have hdisj : Disjoint I (D \ I) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_sdiff.mp hi').2 hi
  have hpos : ∀ u, n₀ ≤ u → u ≤ n₁ → ∀ i, 0 ≤ X i u := by
    intro u hu0 hu1 i
    exact pos_nonneg hτ hne hdr (le_trans hn₀ hu0) (le_trans hu1 hn₁) hr
  have hwin : τ r ≤ n := le_trans hn₀ hn
  rcases Classical.em (Sep X I (D \ I) n) with hsep | hnsep
  · -- **branch 1**: `(sep)` holds at `n`
    have hWn : ((sMin X I n - sMax X (D \ I) n : ℤ) : ℝ)
        ≤ Wpot H X (Finset.univ \ (D \ I)) I (D \ I) n :=
      Wpot_ge_gap hBC.base.hmono hBC.base.hunit hsep
    obtain ⟨u, hu0, hun, hrun, hfirst⟩ :=
      exists_run_start (P := fun w => Sep X I (D \ I) w) hn hsep
    have hu_n₁ : u ≤ n₁ := le_trans hun hn'
    have htop_u : ∀ w, u ≤ w → w ≤ n → TopBlockIn X D I w := by
      intro w h1 h2
      refine ⟨hID, ?_⟩
      intro i hi j hj hji
      have hjJ : j ∈ D \ I := Finset.mem_sdiff.mpr ⟨hj, hji⟩
      have hs := hrun w h1 h2
      have hg := hs.2.2.2 i hi j hjJ
      exact le_trans (le_runMaxI X j w) (by linarith)
    have hspread_u : (spreadS X I u : ℝ) ≤ b :=
      hIH u hu0 hu_n₁ I hIcard (htop_u u le_rfl hun)
    -- the separation at the run start
    have hgapu : ((sMin X I u - sMaxM X (D \ I) u : ℤ) : ℝ) ≤ max 2 β₀ := by
      have hle : sMin X I u - sMaxM X (D \ I) u ≤ sMin X I u - sMax X (D \ I) u := by
        have hmm : sMax X (D \ I) u ≤ sMaxM X (D \ I) u :=
          sMax_le hJne (fun j hj => le_trans (le_runMaxI X j u) (le_sMaxM hJne hj))
        linarith
      rcases eq_or_lt_of_le hu0 with heq | hlt
      · have h2 := gap_le_spread_of_subset (X := X) (D := D) (I := I) (n := u) hIne hID hJne
        have h4 : (spreadS X D u : ℝ) ≤ β₀ := by rw [← heq]; exact hβ₀
        have h3 : ((sMin X I u - sMax X (D \ I) u : ℤ) : ℝ) ≤ (spreadS X D u : ℝ) := by
          exact_mod_cast h2
        have h5 : ((sMin X I u - sMaxM X (D \ I) u : ℤ) : ℝ)
            ≤ (spreadS X D u : ℝ) := by
          have : ((sMin X I u - sMaxM X (D \ I) u : ℤ) : ℝ)
              ≤ ((sMin X I u - sMax X (D \ I) u : ℤ) : ℝ) := by exact_mod_cast hle
          linarith
        exact le_trans h5 (le_trans h4 (le_max_right _ _))
      · have hu1 : 1 ≤ u := by omega
        have hposm : ∀ i, 0 ≤ X i (u - 1) := by
          intro i
          exact hpos (u - 1) (by omega) (by omega) i
        have hnot : ¬ Sep X I (D \ I) (u - 1) := hfirst hlt
        have h2 : sMin X I u - sMaxM X (D \ I) u ≤ 2 :=
          gap_at_failure_gen hne hIne hJne hu1 hposm hnot
        have h3 : ((sMin X I u - sMaxM X (D \ I) u : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by
          exact_mod_cast h2
        refine le_trans h3 (le_trans ?_ (le_max_left _ _))
        norm_num
    -- `(loccoord)` at the run start
    have hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X (D \ I) u := by
      obtain ⟨j, hj, hval⟩ := exists_sMax (X := X) (S := D \ I) (n := u) hJne
      rw [hval]
      exact pos_ge_range hτ hne hdr (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁)
    have hWu : Wpot H X (Finset.univ \ (D \ I)) I (D \ I) u
        ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hbase := Wpot_le_of_sep (X := X) (A := Finset.univ \ (D \ I)) (I := I) (J := D \ I)
        (n := u) hBC.base.hcoord hBC.base.hmono hC.le
        (hrun u le_rfl hun) hIA hAne hA' (le_trans hn₀ hu0) (le_trans hu_n₁ hn₁) hlo
        (fun j _ => hlag j u hu0 hu_n₁)
      have hmono : C * ((spreadS X I u : ℝ)
          + ((sMin X I u - sMaxM X (D \ I) u : ℤ) : ℝ) + (η : ℝ))
          ≤ C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith
      linarith [hbase, hmono]
    -- the `(locgroup)` drift of `W` from `u` to `n`
    have hhalf : ∀ w, u ≤ w → w < n → Sep X I (D \ I) w :=
      fun w h1 h2 => hrun w h1 (le_of_lt h2)
    have hgrp := hBC.group I (D \ I) hdisj hIne hJne u n (le_trans hn₀ hu0) hun
      (le_trans hn' hn₁) hhalf
    -- assemble
    have hfin : ((sMin X I n - sMax X (D \ I) n : ℤ) : ℝ)
        ≤ 2 * C * (b + β₀ + (η : ℝ) + 2) + 2 * CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
      have hb : C * ((spreadS X I u : ℝ) + max 2 β₀ + (η : ℝ))
          ≤ C * (b + β₀ + (η : ℝ) + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        have hmax : max 2 β₀ ≤ β₀ + 2 := by
          rcases le_total (2 : ℝ) β₀ with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        linarith
      have hmid : C * (b + β₀ + (η : ℝ) + 2)
          ≤ 2 * C * (b + β₀ + (η : ℝ) + 2) := by
        have h1 : (0 : ℝ) ≤ b + β₀ + (η : ℝ) + 2 := by linarith
        nlinarith [h1, hC.le]
      linarith [hWn, hWu, hgrp, hb, hmid]
    exact le_trans hfin (le_max_right _ _)
  · -- **branch 2**: `(sep)` fails at `n`
    have hgap := not_sep_gap_le_gen (X := X) (η := η) (I := I) (J := D \ I) (n := n) hIne hJne
      (hpos n hn hn') (fun j _ => hlag j n hn hn') hnsep
    have hcast : ((sMin X I n - sMax X (D \ I) n : ℤ) : ℝ) ≤ 1 + (η : ℝ) := by
      exact_mod_cast hgap
    exact le_trans hcast (JoinStep.le_Gstep C CT L η β₀ b)

end BlkCoin

namespace BlkCoin

open RecordDefect LocalFluid MeasureTheory Glue

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 6. The source's `(coincide)` for an arbitrary block -/

/-- **The order-statistic induction on an arbitrary block: the paper's `(coincide)`.**

Fix a nonempty `D ⊆ {1,…,N}` and a subwindow `[n₀,n₁] ⊆ [τ_r, τ_r + TL]` of a record window
with `d_r ≤ L` on which the local field and the sharp lag `η` hold.  Then the spread of `D`
is at most `β D.card` throughout the subwindow, where `β` is any sequence with `β 1 ≥ 0`
and the source's geometric step
`β (k+1) ≥ β k + Gstep C CT L η (spread_D n₀) (β k)`.

This is `main_1d.tex` lines 1300–1340 — "we prove by induction on `k` that the difference
between the largest and the `k`-th largest position among `D` is `o(L)`, uniformly over
integer times in `[τ_r+⌊Ls⌋, τ_r+TL]`" — for a general block `D`, which requires the
source's `(locgroup)` for non-complementary groups (`BlockClauses.group`).
`JoinStep.spread_univ_le` is the `D = univ` case. -/
theorem spread_block_le {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hBC : BlockClauses X τ H C CT T L r) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    {D : Finset ι} (hD : D.Nonempty)
    (hlag : ∀ (i : ι) (u : ℕ), n₀ ≤ u → u ≤ n₁ → runMaxI X i u - X i u ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + JoinStep.Gstep C CT L η (spreadS X D n₀ : ℝ) (β k)
      ≤ β (k + 1)) :
    ∀ n, n₀ ≤ n → n ≤ n₁ → (spreadS X D n : ℝ) ≤ β D.card := by
  classical
  -- the geometric sequence is nonnegative at every index `k ≥ 1`
  have hβnn : ∀ k, 1 ≤ k → 0 ≤ β k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hβ1
    | succ k hk ih =>
        have h1 := hstep k hk
        have h2 := JoinStep.Gstep_nonneg C CT L η (spreadS X D n₀ : ℝ) (β k)
        linarith
  have hmain : ∀ k, 1 ≤ k → k ≤ D.card → ∀ n, n₀ ≤ n → n ≤ n₁ →
      ∀ I : Finset ι, I.card = k → TopBlockIn X D I n → (spreadS X I n : ℝ) ≤ β k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro _hnk n _hn _hn' I hIcard _
        have hzero : spreadS X I n = 0 := JoinStep.spread_singleton hIcard
        rw [hzero]
        push_cast
        simpa using hβ1
    | succ k hk ih =>
        intro hnk n hn hn' I' hI'card htop'
        obtain ⟨hI'D, htop'max⟩ := htop'
        have hI'pos : 0 < I'.card := by rw [hI'card]; omega
        obtain ⟨i0, hi0, hmin⟩ := exists_sMin (X := X) (S := I') (n := n)
          (Finset.card_pos.mp hI'pos)
        set I : Finset ι := I'.erase i0 with hIdef
        have hIcard : I.card = k := by
          rw [hIdef, Finset.card_erase_of_mem hi0]; omega
        have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
        have hsub : I ⊆ I' := Finset.erase_subset _ _
        have hID : I ⊆ D := fun i hi => hI'D (hsub hi)
        have hI'ne : I ≠ D := by
          intro hc
          have h1 : I.card = D.card := by rw [hc]
          have h2 : D.card ≥ I'.card := Finset.card_le_card hI'D
          omega
        have htopI : ∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j n ≤ X i n := by
          intro i hi j hj hji
          by_cases hji0 : j = i0
          · rw [hji0, ← hmin]
            exact sMin_le ⟨i0, hi0⟩ (hsub hi)
          · exact htop'max i (hsub hi) j hj
              (fun hmem => hji (Finset.mem_erase.mpr ⟨hji0, hmem⟩))
        -- the join-gap step at level `k`
        have hgap := join_gap_of_block hτ hne hBC hC hdr hr hn₀ hn₁
          (D := D) (β₀ := (spreadS X D n₀ : ℝ)) (b := β k) (hβnn k hk) le_rfl hlag
          (fun u hu0 hu1 J hJcard hJtop => ih (by omega) u hu0 hu1 J hJcard hJtop)
          hn hn' hIcard hID hIne hI'ne htopI
        -- the spread identity for inserting the lowest member
        have hminI : ∀ j ∈ I, X i0 n ≤ X j n := by
          intro j hj
          rw [← hmin]
          exact sMin_le ⟨i0, hi0⟩ (hsub hj)
        have hspread := Glue.spreadS_insert_min (X := X) (S := I) (i := i0) (n := n)
          hIne hminI
        rw [show insert i0 I = I' from by rw [hIdef, Finset.insert_erase hi0]] at hspread
        -- the pack maximum outside `I` (inside `D`) is the removed lowest member
        have hsMax : sMax X (D \ I) n = X i0 n := by
          refine JoinStep.sMax_eq_of_mem_le ?_ ?_
          · refine Finset.mem_sdiff.mpr ⟨hI'D hi0, ?_⟩
            rw [hIdef]
            exact Finset.notMem_erase i0 I'
          · intro j hj
            obtain ⟨hjD, hjI⟩ := Finset.mem_sdiff.mp hj
            by_cases hji : j = i0
            · rw [hji]
            · have hj' : j ∉ I' := by
                intro hmem
                exact hjI (Finset.mem_erase.mpr ⟨hji, hmem⟩)
              exact htop'max i0 hi0 j hjD hj'
        have hIle : (spreadS X I n : ℝ) ≤ β k :=
          ih (by omega) n hn hn' I hIcard ⟨hID, htopI⟩
        have hsum : (spreadS X I' n : ℝ)
            ≤ β k + JoinStep.Gstep C CT L η (spreadS X D n₀ : ℝ) (β k) := by
          have hcast : (spreadS X I' n : ℝ)
              = (spreadS X I n : ℝ) + ((sMin X I n - X i0 n : ℤ) : ℝ) := by
            rw [hspread]; push_cast; ring
          have hgap' : ((sMin X I n - X i0 n : ℤ) : ℝ)
              ≤ JoinStep.Gstep C CT L η (spreadS X D n₀ : ℝ) (β k) := by
            rw [← hsMax]; exact hgap
          linarith
        exact le_trans hsum (hstep k hk)
  intro n hn hn'
  have h := hmain D.card (Finset.card_pos.mpr hD) le_rfl n hn hn' D rfl
    (topBlockIn_self X D n)
  simpa using h

/-- The `.`-form of the block induction: with the geometric sequence `β` normalised to
`ε L`, the spread of the block `D` is at most `ε L` throughout the subwindow.  No `η = 0`
is asserted and the `C_T L^{3/4}` error is retained inside `Gstep`. -/
theorem spread_block_le_eps {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hBC : BlockClauses X τ H C CT T L r) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    {D : Finset ι} (hD : D.Nonempty)
    (hlag : ∀ (i : ι) (u : ℕ), n₀ ≤ u → u ≤ n₁ → runMaxI X i u - X i u ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + JoinStep.Gstep C CT L η (spreadS X D n₀ : ℝ) (β k)
      ≤ β (k + 1))
    {ε : ℝ} (hε : β D.card ≤ ε * (L : ℝ)) :
    ∀ n, n₀ ≤ n → n ≤ n₁ → (spreadS X D n : ℝ) ≤ ε * (L : ℝ) := by
  intro n hn hn'
  exact le_trans (spread_block_le hτ hne hBC hC hdr hr hn₀ hn₁ hD hlag hβ1 hstep n hn hn') hε

/-- The `D = univ` instance of the block induction: the whole-pack form of the source's
`(coincide)`, now derived from the general-pair `(locgroup)` rather than from
`(locmove)`.  Compare `JoinStep.spread_univ_le`, which uses the complementary-pair
`(locmove)` and therefore cannot serve the source's general-`D` induction. -/
theorem spread_univ_le_of_block {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hBC : BlockClauses X τ H C CT T L r) (hC : 0 < C)
    (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r)
    {n₀ n₁ : ℕ} (hn₀ : τ r ≤ n₀) (hn₁ : n₁ ≤ τ r + T * L)
    (hlag : ∀ (i : ι) (u : ℕ), n₀ ≤ u → u ≤ n₁ → runMaxI X i u - X i u ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hstep : ∀ k, 1 ≤ k → β k + JoinStep.Gstep C CT L η
      (spreadS X (Finset.univ : Finset ι) n₀ : ℝ) (β k) ≤ β (k + 1)) :
    ∀ n, n₀ ≤ n → n ≤ n₁ →
      (spreadS X (Finset.univ : Finset ι) n : ℝ) ≤ β (Finset.univ : Finset ι).card :=
  spread_block_le hτ hne hBC hC hdr hr hn₀ hn₁ Finset.univ_nonempty hlag hβ1 hstep

end BlkCoin

namespace BlkCoin

open RecordDefect LocalFluid MeasureTheory Glue

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 7. One merge round of the source's Section 5.1, with persistence -/

/-- **One merge round, with the Section 4.2 persistence attached.**

Let `D` be a block of largest positions of the pack at a time `n` of the record window, and
suppose `(sep)` for `(D, Dᶜ)` **fails** at `n`.  Then the source's merge step
(`main_1d.tex`, the paragraph after `(meet)`, and Section 5.1) adjoins the best outside
walker: `insert j D` is again a block of largest positions, has one more walker, and its
spread at `n` is at most `spread_D(n) + 1 + η`.

What is new here is the **persistence**: the enlarged block satisfies the same
order-statistic bound `β` as the block induction on the rest of the window
`[n, n₁] ⊆ [τ_r, τ_r+TL]`, so a later merge round can start from a block whose spread is
already known to be `o(L)` instead of merely `O(L)`.  That is exactly the input that the
iterated merging of Section 5.1 consumes before `(coincide)` may be applied.

`β` is any geometric sequence with `β 1 ≥ 0` and the step condition, required uniformly
over the (finitely many) outsiders `j ∉ D`. -/
theorem merge_round_persist {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ}
    {A : ι → ℕ → ℕ} {μ C CT : ℝ} {T L r η : ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hBC : BlockClauses X τ H C CT T L r) (hM : JoinStep.MartClause X τ A μ CT T L r)
    (hC : 0 < C) (hdr : defect X τ r ≤ (L : ℤ)) (hr : (T + 3) * L ≤ r) (hL1 : 1 ≤ L)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : JoinStep.Numerics C CT L) (hT64 : 64 * ⌈C⌉₊ ≤ T)
    (hηdef : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    {D : Finset ι} (hD : D.Nonempty) (hD' : D ≠ Finset.univ)
    {n : ℕ} (hn0 : τ r + 64 * ⌈C⌉₊ * L ≤ n) (hnT : n ≤ τ r + T * L)
    (htop : JoinStep.TopBlock X D n) (hnot : ¬ Sep X D (Finset.univ \ D) n)
    {n₁ : ℕ} (hnn₁ : n ≤ n₁) (hn₁ : n₁ ≤ τ r + T * L)
    (hlag : ∀ (i : ι) (u : ℕ), n ≤ u → u ≤ n₁ → runMaxI X i u - X i u ≤ (η : ℤ))
    {β : ℕ → ℝ} (hβ1 : 0 ≤ β 1)
    (hβstep : ∀ j : ι, j ∉ D → ∀ k, 1 ≤ k →
      β k + JoinStep.Gstep C CT L η (spreadS X (insert j D) n : ℝ) (β k) ≤ β (k + 1)) :
    ∃ j, j ∉ D ∧ JoinStep.TopBlock X (insert j D) n ∧ (insert j D).card = D.card + 1 ∧
      spreadS X (insert j D) n ≤ spreadS X D n + (1 + (η : ℤ)) ∧
      ∀ m, n ≤ m → m ≤ n₁ → (spreadS X (insert j D) m : ℝ) ≤ β (D.card + 1) := by
  obtain ⟨j, hjn, htop', hcard, hspread⟩ :=
    JoinStep.merge_at_start hτ hne hBC.base hM hC hdr hr hL1 hij hnum hT64 hηdef
      hD hD' hn0 hnT htop hnot
  refine ⟨j, hjn, htop', hcard, hspread, ?_⟩
  have hn_τ : τ r ≤ n := le_trans (Nat.le_add_right _ _) hn0
  have hpers := spread_block_le hτ hne hBC hC hdr hr hn_τ hn₁
    (Finset.insert_nonempty j D) hlag hβ1 (hβstep j hjn)
  intro m hm0 hm1
  have h := hpers m hm0 hm1
  rwa [hcard] at h

end BlkCoin

namespace BlkCoin

open RecordDefect LocalFluid MeasureTheory Glue

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 8. Cross-checks against the accepted complementary-pair lemmas

The general-pair statements above must *specialise* to the accepted ones on complementary
pairs; these three lemmas are the consistency checks, and they pin the convention
`W^{I,J} = Wpot H X (Jᶜ) I J`. -/

/-- With the potential family equal to the block, `Wpot` is the accepted `Glue.Wst`. -/
theorem Wpot_self {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {I J : Finset ι} {n : ℕ} :
    Wpot H X I I J n = Wst H X I J n := rfl

/-- The general-pair failure bound specialises to `JoinStep.not_sep_gap_le`. -/
theorem not_sep_gap_le_gen_consistency {X : ι → ℕ → ℤ} {η : ℕ} {I : Finset ι} {n : ℕ}
    (hI : I.Nonempty) (hJ : (Finset.univ \ I).Nonempty) (hpos : ∀ i, 0 ≤ X i n)
    (hlag : ∀ j ∈ Finset.univ \ I, runMaxI X j n - X j n ≤ (η : ℤ))
    (hnot : ¬ Sep X I (Finset.univ \ I) n) :
    sMin X I n - sMax X (Finset.univ \ I) n ≤ 1 + (η : ℤ) :=
  not_sep_gap_le_gen hI hJ hpos hlag hnot

/-- The general-pair post-failure gap specialises to `Glue.gap_at_failure`. -/
theorem gap_at_failure_gen_consistency {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {A : Finset ι} {v : ℕ}
    (hA : A.Nonempty) (hA' : A ≠ Finset.univ) (hv : 1 ≤ v)
    (hpos : ∀ i, 0 ≤ X i (v - 1)) (hnot : ¬ Sep X A (Finset.univ \ A) (v - 1)) :
    sMin X A v - sMaxM X (Finset.univ \ A) v ≤ 2 :=
  gap_at_failure_gen hne hA (Finset.sdiff_nonempty.mpr (by simpa using hA')) hv hpos hnot

end BlkCoin
