/-
# Finite-scale `(coincide)`: the class-spread induction

Source: `main_1d_revised.tex`, proof of Proposition `tight`, the step proving `(coincide)`,
i.e. the finite-`L` induction on the rank `k` inside the window
`[τ_r + ⌊Ls⌋, τ_r + TL]`.

The paper's argument is entirely finite-scale: for a group `D` it proves by induction on `k`
that the gap between the largest and the `k`-th largest position among `D` is `o(L)`,
uniformly over the integer times of the window.  The induction step uses `(loccoord)` at the
last time the separation `(sep)` was recovered, `(locgroup)` across the separated stretch,
`(Wpos)` at the target time, and the nearest-neighbour property to bound the gap at the
recovery time.

This file formalises that finite-scale induction abstractly, for the `W`-potential
`Wpot H X (univ \ J) I J` of `GlueCore`'s local-good field (`H` = the paper's `H_n^A`), the
paper's `(sep)`, `(Wpos)`, `(loccoord)` and `(locgroup)`.  No probability, no limit, no
compactness.  The output is the finite-`L` **class-spread bound**

  `spread_D(n) ≤ ((1+C)^{|D|} - 1) · (C·(spread_D(s) + η + 2) + 2 C_T L^{3/4} + η + 2)`

for every group `D` and every pair of window times `s ≤ n`.  With `spread_D(s) = o(L)` and
`η = o(L)` this is exactly the paper's `(4.8)` for the coincidence class, hence the missing
finite-scale input of `Coalesce.hpair_of_class_spread`; it also gives the source's
`(coincide)` statement after dividing by `L`.
-/
import Swarm.GlueCore

open Finset Filter Topology
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Coincide

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid

/-! ## 0. Extrema helpers -/

theorem sMax_le_sMax_of_subset {X : ι → ℕ → ℤ} {S T : Finset ι} (hS : S.Nonempty)
    (hST : S ⊆ T) (n : ℕ) : sMax X S n ≤ sMax X T n := by
  exact sMax_le hS (fun i hi => le_sMax ⟨hS.choose, hST hS.choose_spec⟩ (hST hi))

theorem sMaxM_mono {X : ι → ℕ → ℤ} {S T : Finset ι} (hS : S.Nonempty) (hST : S ⊆ T)
    (n : ℕ) : sMaxM X S n ≤ sMaxM X T n := by
  exact sMaxM_le hS (fun i hi => le_sMaxM ⟨hS.choose, hST hS.choose_spec⟩ (hST hi))

theorem sMax_le_sMaxM {X : ι → ℕ → ℤ} {S : Finset ι} (hS : S.Nonempty) (n : ℕ) :
    sMax X S n ≤ sMaxM X S n :=
  sMax_le hS (fun i hi => le_trans (le_runMaxI X i n) (le_sMaxM hS hi))

/-- If `I` consists of the largest positions of `D`, its maximum is the maximum of `D`. -/
theorem sMax_eq_of_upper {X : ι → ℕ → ℤ} {D I : Finset ι} {n : ℕ} (hI : I.Nonempty)
    (hID : I ⊆ D) (hupper : ∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j n ≤ X i n) :
    sMax X I n = sMax X D n := by
  refine le_antisymm (sMax_le_sMax_of_subset hI hID n) ?_
  refine sMax_le ⟨hI.choose, hID hI.choose_spec⟩ (fun j hj => ?_)
  by_cases hji : j ∈ I
  · exact le_sMax hI hji
  · exact le_trans (hupper hI.choose hI.choose_spec j hj hji) (le_sMax hI hI.choose_spec)

/-- `(sep)` makes `I` an upper group of `D` when `D` is split as `I ∪ J`. -/
theorem upper_of_sep {X : ι → ℕ → ℤ} {D I J : Finset ι} {n : ℕ} (hDJ : D = I ∪ J)
    (hsep : Sep X I J n) : ∀ i ∈ I, ∀ j ∈ D, j ∉ I → X j n ≤ X i n := by
  intro i hi j hj hji
  have hjJ : j ∈ J := by
    rw [hDJ] at hj
    rcases Finset.mem_union.mp hj with h | h
    · exact absurd h hji
    · exact h
  have h2 : X j n ≤ runMaxI X j n := le_runMaxI X j n
  have h3 := hsep.2.2.2 i hi j hjJ
  linarith

/-! ## 1. The paper's potential with the true complement index -/

/-- The paper's `W_n^{I,J} = |I|^{-1} Σ_{i∈I} H_n^{J^c}(X_n^i) - max_{j∈J} H_n^{J^c}(X_n^j)`,
with the complement `J^c` passed explicitly as `A`.  `Glue.Wst` is the case `A = I`, which
covers the paper's complementary groups `J = univ \ I`; the `(coincide)` induction runs over
proper subgroups `J = D \ I` of the coincidence class `D`, where the potential is indexed by
the larger set `J^c = univ \ J`. -/
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

/-- Monotonicity turns `max_j H(X^j)` into `H(max_j X^j)`. -/
theorem sup_H_eq {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A J : Finset ι} {n : ℕ}
    (hmono : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H B m x ≤ H B m y)
    (hJ : J.Nonempty) :
    (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) := by
  obtain ⟨j0, hj0, hval⟩ := exists_sMax (X := X) (S := J) (n := n) hJ
  refine le_antisymm (Finset.sup'_le hJ _ ?_) ?_
  · intro j hj
    exact hmono A n (le_sMax hJ hj)
  · rw [hval]
    exact Finset.le_sup' (f := fun j => H A n (X j n)) hj0

/-! ## 2. `(Wpos)` and `(loccoord)` for `Wpot` -/

/-- `(Wpos)`: on `(sep)` the gap `min_I X - max_J X` is dominated by the potential. -/
theorem Wpot_ge_gap {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A I J : Finset ι} {n : ℕ}
    (hmono : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → H B m x ≤ H B m y)
    (hunit : ∀ (B : Finset ι) (m : ℕ) {x y : ℤ}, x ≤ y → y - x ≤ H B m y - H B m x)
    (hsep : Sep X I J n) :
    ((sMin X I n - sMax X J n : ℤ) : ℝ) ≤ Wpot H X A I J n := by
  have hI := hsep.nonempty_left
  have hJ := hsep.nonempty_right
  have hsup : (J.sup' hJ (fun j => H A n (X j n)) : ℤ) = H A n (sMax X J n) :=
    sup_H_eq hmono hJ
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
  have hcast : ((sMin X I n - sMax X J n : ℤ) : ℝ)
      = ((sMin X I n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-- `(loccoord)` for `Wpot`, the paper's "apply `(loccoord)` with `A = J^c`" step: on `(sep)`,
`W_n^{I,J} ≤ C·(spread_I(n) + gap_J(n) + η) + C_T L^{3/4}`, where
`gap_J(n) = min_I X_n − max_J M_n ≥ 2` is the separation (not the record lag). -/
theorem Wpot_le_of_sep {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ}
    {T L r η : ℕ} (hLF : LocalField X τ H C CT T L r η) (hC : 0 ≤ C) {A I J : Finset ι}
    {n : ℕ} (hIA : I ⊆ A) (hsep : Sep X I J n) (hAne : A ≠ Finset.univ)
    (h1 : τ r ≤ n) (h2 : n ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMax X J n) :
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
    have h := sMaxM_sub_sMax_le hJ (fun j hj => hLF.lag j n h1 h2)
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

/-! ## 3. The initial-time bound (the `u = s` branch of the source) -/

/-- At the window start, `(loccoord)` bounds `W` by the *internal spread of the whole
coincidence class* `D` (the source's `W_u^{I,J} ≤ C (max_D X_u − min_D X_u) + C_T L^{3/4}`),
not by the separation gap.  This is the only place where the initial small spread of `D`
enters the induction. -/
theorem Wpot_start {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ}
    {T L r η : ℕ} (hLF : LocalField X τ H C CT T L r η) (hC : 0 ≤ C) {D I J : Finset ι}
    (hD : D.Nonempty) (hI : I.Nonempty) (hJ : J.Nonempty) (hID : I ⊆ D) (hJD : J ⊆ D)
    (hIA : I ⊆ Finset.univ \ J) {s : ℕ} (hs : τ r ≤ s) (hsT : s ≤ τ r + T * L)
    (hlo : (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ sMin X D s) :
    Wpot H X (Finset.univ \ J) I J s ≤ C * ((spreadS X D s : ℤ) : ℝ)
      + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
  set A : Finset ι := Finset.univ \ J with hAdef
  have hAne' : A.Nonempty := hI.mono hIA
  have hAne : A ≠ Finset.univ := by
    intro h
    obtain ⟨j, hj⟩ := hJ
    have hja : j ∉ A := by
      rw [hAdef, Finset.mem_sdiff]
      exact fun hc => hc.2 hj
    rw [h] at hja
    exact hja (Finset.mem_univ j)
  have hsup : (J.sup' hJ (fun j => H A s (X j s)) : ℤ) = H A s (sMax X J s) :=
    sup_H_eq hLF.hmono hJ
  rw [Wpot_of_nonempty (H := H) (X := X) (A := A) (I := I) (n := s) hJ, hsup]
  have hcard : (0 : ℝ) < (I.card : ℝ) := by
    have h : 0 < I.card := Finset.card_pos.mpr hI
    exact_mod_cast h
  have havg : (∑ i ∈ I, ((H A s (X i s) : ℤ) : ℝ)) / (I.card : ℝ)
      ≤ ((H A s (sMax X I s) : ℤ) : ℝ) := by
    rw [div_le_iff₀ hcard]
    have hb : ∀ i ∈ I, H A s (X i s) ≤ H A s (sMax X I s) := by
      intro i hi; exact hLF.hmono A s (le_sMax hI hi)
    calc (∑ i ∈ I, ((H A s (X i s) : ℤ) : ℝ))
        ≤ ∑ _i ∈ I, ((H A s (sMax X I s) : ℤ) : ℝ) :=
          Finset.sum_le_sum (fun i hi => by exact_mod_cast hb i hi)
      _ = ((H A s (sMax X I s) : ℤ) : ℝ) * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb0 : sMax X I s ≤ sMaxM X A s :=
    le_trans (sMax_le_sMaxM hI s) (sMaxM_mono hI hIA s)
  have hle0 : sMin X D s ≤ sMax X I s :=
    le_trans (sMin_le hD (hID hI.choose_spec)) (le_sMax hI hI.choose_spec)
  have hcoord := hLF.hcoord A s hAne' hAne hs hsT (sMin X D s) (sMax X I s) hlo hle0 hb0
  have hcoord' : ((H A s (sMax X I s) : ℤ) : ℝ) - ((H A s (sMin X D s) : ℤ) : ℝ)
      ≤ C * (((sMax X I s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ))
        + CT * (L : ℝ) ^ (3 / 4 : ℝ) := by
    have e1 : ((H A s (sMax X I s) - H A s (sMin X D s) : ℤ) : ℝ)
        = ((H A s (sMax X I s) : ℤ) : ℝ) - ((H A s (sMin X D s) : ℤ) : ℝ) := by
      push_cast; ring
    have e2 : ((sMax X I s - sMin X D s : ℤ) : ℝ)
        = ((sMax X I s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ) := by push_cast; ring
    rw [e1, e2] at hcoord
    exact hcoord
  have hspan : ((sMax X I s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ)
      ≤ ((spreadS X D s : ℤ) : ℝ) := by
    have h1 : sMax X I s ≤ sMax X D s := sMax_le_sMax_of_subset hI hID s
    have h1' : ((sMax X I s : ℤ) : ℝ) ≤ ((sMax X D s : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : ((sMax X D s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ)
        = ((spreadS X D s : ℤ) : ℝ) := by
      unfold spreadS; push_cast; ring
    linarith
  have hsplit : ((H A s (sMax X I s) : ℤ) : ℝ) - ((H A s (sMax X J s) : ℤ) : ℝ)
      = ((H A s (sMax X I s) - H A s (sMax X J s) : ℤ) : ℝ) := by push_cast; ring
  have hmono2 : ((H A s (sMin X D s) : ℤ) : ℝ) ≤ ((H A s (sMax X J s) : ℤ) : ℝ) := by
    have h2 : sMin X D s ≤ sMax X J s :=
      le_trans (sMin_le hD (hJD hJ.choose_spec)) (le_sMax hJ hJ.choose_spec)
    exact_mod_cast hLF.hmono A s h2
  have hmul : C * (((sMax X I s : ℤ) : ℝ) - ((sMin X D s : ℤ) : ℝ))
      ≤ C * ((spreadS X D s : ℤ) : ℝ) := mul_le_mul_of_nonneg_left hspan hC
  linarith [hcoord', havg, hsplit, hmul, hmono2]

/-! ## 4. `(locgroup)`: the potential does not grow across a separated stretch -/

/-- The paper's `(locgroup)`: if `(sep)` holds at every integer time of `[s,t)`, then
`W_t^{I,J} − W_s^{I,J} ≤ C_T L^{3/4}`.  Stated for the true-complement potential and for
arbitrary disjoint nonempty `I, J`. -/
def GroupGrow (H : Finset ι → ℕ → ℤ → ℤ) (X : ι → ℕ → ℤ) (τ : ℕ → ℕ)
    (CT : ℝ) (T L r : ℕ) : Prop :=
  ∀ (I J : Finset ι) (s t : ℕ), I.Nonempty → J.Nonempty → Disjoint I J →
    τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    (∀ u : ℕ, s ≤ u → u < t → Sep X I J u) →
    Wpot H X (Finset.univ \ J) I J t ≤ Wpot H X (Finset.univ \ J) I J s
      + CT * (L : ℝ) ^ (3 / 4 : ℝ)


/-! ## 5. One induction step: the gap at a single time -/

/-- **The induction step of the source's `(coincide)`.**  If every upper group of `D` of rank
`k` has spread at most `E` at every integer time of `[s,n]`, then at any such time the gap
between an upper group `S` of rank `k` and its complement `D \ S` is at most
`C(E + η + 2) + 2 C_T L^{3/4} + (η + 2)`.

The two cases are the paper's: either `(sep)` fails at the target time (then the gap is at
most the record lag plus one), or it holds and one walks back to the last failing time `w`;
at `w + 1` the failure at `w` and the nearest-neighbour property bound the separation by `2`,
`(loccoord)` bounds `W`, `(locgroup)` carries it to `v`, and `(Wpos)` converts it back to the
gap.  When no failure exists the initial small spread of `D` is used instead. -/
theorem gap_le_of_localGood
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r η : ℕ}
    (hLF : LocalField X τ H C CT T L r η) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {D : Finset ι} (hD : D.Nonempty) {s n : ℕ} (hs : τ r ≤ s) (hsn : s ≤ n)
    (hn : n ≤ τ r + T * L)
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
  have hvnT : v ≤ τ r + T * L := le_trans hvn hn
  have hpos : ∀ x, s ≤ x → x ≤ n → ∀ i, 0 ≤ X i x := fun x h1 h2 i =>
    pos_nonneg hτ hne hdr (le_trans hs h1) (le_trans h2 hn) hrT
  have hposv : ∀ i ∈ S, 0 ≤ X i v := fun i hi => hpos v hsv hvn i
  have hrange : ∀ x, s ≤ x → x ≤ n → ∀ i,
      (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ X i x := fun x h1 h2 i =>
    pos_ge_range hτ hne hdr (le_trans hs h1) (le_trans h2 hn)
  have hlag : ∀ x, s ≤ x → x ≤ n → sMaxM X J x - sMax X J x ≤ (η : ℤ) := fun x h1 h2 =>
    sMaxM_sub_sMax_le hJne (fun j hj => hLF.lag j x (le_trans hs h1) (le_trans h2 hn))
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
        have hWu := Wpot_le_of_sep (A := Finset.univ \ J) (I := S) (J := J) hLF hCnn hIA
          hsep_u hAne (le_trans hs hsu) (le_trans hu_le_v hvnT) hmaxrange
        have hgr := hgrow S J (w + 1) v hSne hJne (Finset.disjoint_sdiff) (le_trans hs hsu)
          hu_le_v hvnT
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
          (fun j hj => (Finset.mem_sdiff.mp hj).1) hIA hs (le_trans hsn hn) hmaxrange
        have hgr := hgrow S J s v hSne hJne (Finset.disjoint_sdiff) hs hsv hvnT
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

/-! ## 6. The finite-scale `(coincide)` class-spread theorem -/

/-- **The source's `(coincide)` at finite `L`.**  On the local-good field of Proposition
`local` (with `(locgroup)` supplied by `hgrow`) plus the finite-`L` lag bound `η`, the spread
of *any* group `D` of walkers at any two window times `s ≤ n` satisfies

  `spread_D(n) ≤ ((1+C)^{|D|} − 1) · ( C (spread_D(s) + η + 2) + 2 C_T L^{3/4} + η + 2 )`.

The multiplicative factor is exponential in the *group size* `|D|` only, never in the window
length: this is exactly the content of the paper's induction on the rank, and the reason the
`o(L)` errors survive.  With `spread_D(s) = o(L)` and `η = o(L)` the right-hand side is
`o(L)`, which is the paper's `(4.8)` for the coincidence class `D`. -/
theorem spreadS_le_of_localGood
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r η : ℕ}
    (hLF : LocalField X τ H C CT T L r η) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {D : Finset ι} (hD : D.Nonempty)
    {s n : ℕ} (hs : τ r ≤ s) (hsn : s ≤ n) (hn : n ≤ τ r + T * L) :
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
        have hSp := gap_le_of_localGood hLF hgrow hC1 hCT hτ hne hdr hrT hD hs hsn hn
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

/-! ## 7. The scaled form: `(4.8)` with vanishing errors -/

/-- **The source's `(4.8)` for a group `D`, with the three errors kept explicit.**  If the
class spread at the window start, the record lag and the additive `(locgroup)`/`(loccoord)`
error are at most `ε₀L`, `ε₁L` and `ε₂L`, then the class spread at every later window time is
at most `((1+C)^{|D|} − 1) · ( C((ε₀+ε₁)L + 2) + 2ε₂L + (ε₁L + 2) )`.  The right-hand side is
`L · ((1+C)^{|D|} − 1)(C(ε₀+ε₁) + 2ε₂ + ε₁) + O(1)`, hence `o(L)` as soon as the three errors
vanish. -/
theorem spreadS_le_scaled
    {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r η : ℕ}
    (hLF : LocalField X τ H C CT T L r η) (hgrow : GroupGrow H X τ CT T L r)
    (hC1 : 1 ≤ C) (hCT : 0 ≤ CT)
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hdr : defect X τ r ≤ (L : ℤ)) (hrT : (T + 3) * L ≤ r)
    {D : Finset ι} (hD : D.Nonempty) {s n : ℕ} (hs : τ r ≤ s) (hsn : s ≤ n)
    (hn : n ≤ τ r + T * L) {ε0 ε1 ε2 : ℝ}
    (hstart : ((spreadS X D s : ℤ) : ℝ) ≤ ε0 * (L : ℝ))
    (hη : (η : ℝ) ≤ ε1 * (L : ℝ))
    (hct : CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 * (L : ℝ)) :
    ((spreadS X D n : ℤ) : ℝ) ≤ ((1 + C) ^ D.card - 1) *
      (C * ((ε0 + ε1) * (L : ℝ) + 2) + 2 * (ε2 * (L : ℝ)) + (ε1 * (L : ℝ) + 2)) := by
  have hmain := spreadS_le_of_localGood hLF hgrow hC1 hCT hτ hne hdr hrT hD hs hsn hn
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
theorem classSpread_tendsto
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (η n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε0 ε1 ε2 : ℕ → ℝ}
    (hε0t : Tendsto ε0 atTop (𝓝 0)) (hε1t : Tendsto ε1 atTop (𝓝 0))
    (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ Tn) (hTn : Tn ≤ (T : ℝ))
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
    have hbase := spreadS_le_scaled (hLF n) (hgrow n) hC1 (hCT n) (hτ n) (hne n)
      (hdr n) (hrT n) hD (Nat.le_add_right _ _) (Nat.add_le_add_left hsle _)
      (Nat.add_le_add_left hfloor_le _) (hstart n) (hη n) (hct n)
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
