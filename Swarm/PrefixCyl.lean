/-
# Prefix cylinders of the finite-window family: the general `K ≤ n` forgetting projection

`HorizonWindow.FinHorizonWindow` is the residual family

  `(★ K n)  μ (Φ ⁻¹' (finStrict K ∩ pathPat n ⁻¹' C))
              = π (srSet N m) · arrayMeasure {U | posPath U ∈ finStrict K ∩ pathPat n ⁻¹' C}`

for every `K`, every window width `n` and every measurable `C` of the `n + 1` window positions.
This file isolates the **prefix-cylinder** part of that family, i.e. the sets `C` that read only
the first `K + 1` positions when `K ≤ n`, and proves that on that part the window width `n` is
irrelevant: the member `(★ K n)` at a prefix cylinder *is* the member `(★ K K)`.  Nothing is
computed numerically here and no `K ≥ 3` chain-side or array-side mass is claimed.

Main results (all unconditional, no `sorry`, no custom axiom, `π` an arbitrary measure):

* `restrictPat h`: the forgetting projection `(Fin (n+1) → Fin N → ℤ) → (Fin (K+1) → Fin N → ℤ)`
  for `h : K ≤ n`; it is functorial (`restrictPat_refl`, `restrictPat_comp`) and measurable
  (`measurable_restrictPat`, `measurableSet_restrictPat_preimage`).
* `pathPat_restrictPat`: `pathPat n` followed by the projection **is** `pathPat K`.
* `finStrictPat`: the finite-pattern form of `finStrict`, and
  `finStrict_eq_preimage_finStrictPat`: `finStrict K` is literally the preimage of the finite
  pattern set under `pathPat K`.  Together with `pathPat_restrictPat` this gives
  `mem_finStrict_iff_restrict_pattern`: the infinite-time event `finStrict K` is read off the
  *projected* window `restrictPat h (pathPat n X)` alone.  `finStrictPat_eq_image` records the
  exact sense in which the projection sees `finStrict` at horizon `n`: the image of the
  `n`-horizon strict patterns lands inside the `K`-horizon strict patterns
  (`restrictPat_mem_finStrictPat`), and the *set* `finStrictPat K` is exactly the image of
  `finStrictPat n`, so no strict pattern at horizon `K` is lost by widening the window.
* `inter_pathPat_prefix`: for **any** ambient set `A` of paths,
  `A ∩ pathPat n ⁻¹' (restrictPat h ⁻¹' C) = A ∩ pathPat K ⁻¹' C`.  Applied with `A = finStrict K`
  this is `finStrict_inter_prefix`, the set identity behind the window reduction; applied with
  `A = finStrict n` it is the same statement for the wider strictness horizon.
* `FinHorizonWindowPrefix` / `FinHorizonWindowDiag`: the prefix sub-family and the diagonal
  (`n = K`) family, and `finHorizonWindowPrefix_iff_diag`: **the prefix sub-family of
  `FinHorizonWindow` is exactly its diagonal** — the width `n ≥ K` adds nothing once `C` reads
  only the first `K + 1` positions.  `finHorizonWindowPrefix_of_window` is the trivial inclusion
  from the full window family.
* `arrayMeasure_finStrict_prefix_pattern`: the resulting horizon-`K` word sum for a width-`n`
  prefix cylinder, so that the member at `(K, n ≥ K, prefix C)` is computed by the same finite
  sum over `Fin K → JumpVec N` as the diagonal.  The point of the identity is that the pattern
  test is the *projected* one; the word weight is still the `K`-step weight `pathW p K q`.
  `arrayMeasure_finStrict_n_prefix_pattern` is the companion with the wide strictness horizon
  `n`: the pattern test is then `restrictPat h (patOf q)`, i.e. the projection, while the weight
  stays the `n`-step weight — this is exactly where the width `n` survives.
* `finStrictTail`: the *tail* `K < t ≤ n` of the wider strictness horizon, with
  `finStrict_eq_inter_tail` (`finStrict n = finStrict K ∩ finStrictTail K n`) and
  `finStrict_n_inter_prefix_eq_tail`.  `window_diag_mass_eq_n_add_tail` is the resulting tower
  identity: the diagonal member mass is the width-`n` prefix member mass *plus* the mass of the
  tail-violating part, and the tail set does not involve `C`.  `prefix_cylinder_subset`,
  `arrayMass_finStrict_n_prefix_le`, `measure_finStrict_n_prefix_le` record the monotonicity that
  goes with it.  This is the honest sense in which the width `n > K` still matters: not through
  the pattern test, but through tail positivity.
* `restrictPat_preimage_comp`: nested prefix reductions collapse to the single reduction.

Word-level ("all `K`") correspondence used by the above:

* `posAt_seqOf_prefixWord`, `posSeqFin_prefixWord`: a strictly positive word of length `n` has a
  strictly positive prefix of length `K ≤ n`;
* `patOf_prefixWord`: the pattern of the prefix word is the projection of the pattern, i.e.
  `restrictPat h (patOf q) = patOf (prefixWord h q)`.

Scope / what is **not** claimed (compiled witnesses are given):

* `not_prefix_cylinder_pattern` (pattern level) and `not_prefix_cylinder_array` (array level):
  a `C` that genuinely reads position `> K` is **not** a prefix cylinder at all, so the full
  window family at width `n > K` is strictly richer than the diagonal family; the reduction is
  only for prefix `C`.  The witnesses are the two nearest-neighbour paths `0,1,0` and `0,1,2`,
  both in `finStrict 1`, which agree on the first two positions and are separated by the third;
  `jbox_nonempty`, `posPath_one_of_box`, `posPath_two_of_box_UD`, `posPath_two_of_box_UU` supply
  the two witness arrays of the actual `arrayMeasure`.  No unrestricted `n > K` reduction, no
  `n > K` mass value, no `K ≥ 3` statement, no `hstruct` and no all-`B` completion is claimed.
-/
import Swarm.HorizonWindow
import Swarm.ArrayWordDecomp

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmPrefix

open SwarmFinHorizon SwarmArrayWords SwarmFreshArray SwarmFreshPos SwarmFresh SimJump SimJump.Record
open Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-! ## 1. The forgetting projection on finite patterns -/

/-- The forgetting projection: a pattern of `n + 1` positions is restricted to its first `K + 1`
positions. -/
def restrictPat {K n : ℕ} (h : K ≤ n) (P : Fin (n + 1) → Fin N → ℤ) :
    Fin (K + 1) → Fin N → ℤ :=
  fun k i => P ⟨(k : ℕ), by have := k.2; omega⟩ i

theorem restrictPat_apply {K n : ℕ} (h : K ≤ n) (P : Fin (n + 1) → Fin N → ℤ)
    (k : Fin (K + 1)) (i : Fin N) :
    restrictPat (N := N) h P k i = P ⟨(k : ℕ), by have := k.2; omega⟩ i := rfl

/-- The projection at `K = n` is the identity. -/
theorem restrictPat_refl (n : ℕ) (P : Fin (n + 1) → Fin N → ℤ) :
    restrictPat (N := N) (le_refl n) P = P := by
  funext k i
  rfl

/-- The projections compose. -/
theorem restrictPat_comp {K L n : ℕ} (h₁ : K ≤ L) (h₂ : L ≤ n)
    (P : Fin (n + 1) → Fin N → ℤ) :
    restrictPat (N := N) (le_trans h₁ h₂) P
      = restrictPat (N := N) h₁ (restrictPat (N := N) h₂ P) := by
  funext k i
  rfl

/-- Function-level form of `restrictPat_comp`. -/
theorem restrictPat_comp_fun {K L n : ℕ} (h₁ : K ≤ L) (h₂ : L ≤ n) :
    restrictPat (N := N) (K := K) (n := n) (le_trans h₁ h₂)
      = (restrictPat (N := N) (K := K) (n := L) h₁)
        ∘ (restrictPat (N := N) (K := L) (n := n) h₂) := by
  funext P
  exact restrictPat_comp h₁ h₂ P

/-- Nested prefix reductions are the single reduction to the smaller horizon. -/
theorem restrictPat_preimage_comp {K L n : ℕ} (h₁ : K ≤ L) (h₂ : L ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    restrictPat (N := N) (K := K) (n := n) (le_trans h₁ h₂) ⁻¹' C
      = restrictPat (N := N) (K := L) (n := n) h₂
          ⁻¹' (restrictPat (N := N) (K := K) (n := L) h₁ ⁻¹' C) := by
  rw [← Set.preimage_comp, restrictPat_comp_fun]

/-- The forgetting projection is measurable. -/
theorem measurable_restrictPat {K n : ℕ} (h : K ≤ n) :
    Measurable (restrictPat (N := N) (K := K) (n := n) h) := by
  refine measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun i => ?_
  have hk : Measurable fun P : Fin (n + 1) → Fin N → ℤ =>
      P ⟨(k : ℕ), by have := k.2; omega⟩ := measurable_pi_apply _
  exact (measurable_pi_apply i).comp hk

/-- A measurable base pattern set has a measurable prefix cylinder.  (This is the measurability
condition on `C` under which the window reduction is stated: `C` measurable at the base level, so
that `restrictPat h ⁻¹' C` is a measurable set of window patterns.) -/
theorem measurableSet_restrictPat_preimage {K n : ℕ} (h : K ≤ n)
    {C : Set (Fin (K + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    MeasurableSet (restrictPat (N := N) h ⁻¹' C) :=
  hC.preimage (measurable_restrictPat h)

/-! ## 2. `pathPat n` followed by the projection is `pathPat K` -/

/-- **The pattern of the first `K + 1` positions is the projection of the pattern of the first
`n + 1` positions.** -/
theorem pathPat_restrictPat {K n : ℕ} (h : K ≤ n) (X : ℕ → Fin N → ℤ) :
    restrictPat (N := N) h (pathPat (N := N) n X) = pathPat (N := N) K X := by
  funext k i
  rfl

/-- Function-level form: `pathPat n` followed by the projection **is** `pathPat K`. -/
theorem pathPat_comp_restrictPat {K n : ℕ} (h : K ≤ n) :
    (restrictPat (N := N) (K := K) (n := n) h) ∘ (pathPat (N := N) n)
      = pathPat (N := N) K := by
  funext X
  exact pathPat_restrictPat h X

/-! ## 3. `finStrict K` is a finite-pattern preimage, read through any wider window -/

/-- The finite-pattern form of `finStrict K`: position `0` is the level and every positive time up
to `K` is strictly above it. -/
def finStrictPat (K : ℕ) : Set (Fin (K + 1) → Fin N → ℤ) :=
  {P | (∀ i, P ⟨0, Nat.succ_pos K⟩ i = 0) ∧
    ∀ (k : Fin (K + 1)), 1 ≤ (k : ℕ) → ∀ i, 0 < P k i}

theorem mem_finStrictPat {K : ℕ} {P : Fin (K + 1) → Fin N → ℤ} :
    P ∈ finStrictPat (N := N) K ↔
      (∀ i, P ⟨0, Nat.succ_pos K⟩ i = 0) ∧
        ∀ (k : Fin (K + 1)), 1 ≤ (k : ℕ) → ∀ i, 0 < P k i :=
  Iff.rfl

/-- **`finStrict K` is literally the preimage of a finite pattern set** under `pathPat K`. -/
theorem finStrict_eq_preimage_finStrictPat (K : ℕ) :
    finStrict (N := N) K = pathPat (N := N) K ⁻¹' finStrictPat (N := N) K := by
  ext X
  constructor
  · rintro ⟨h0, hpos⟩
    refine ⟨?_, ?_⟩
    · intro i
      exact h0 i
    · intro k hk i
      exact hpos (k : ℕ) hk (by have := k.2; omega) i
  · rintro ⟨h0, hpos⟩
    refine ⟨fun i => h0 i, fun n hn hnK i => ?_⟩
    exact hpos ⟨n, by omega⟩ hn i

/-- Pointwise form of `finStrict_eq_preimage_finStrictPat`. -/
theorem mem_finStrict_iff_pattern {K : ℕ} {X : ℕ → Fin N → ℤ} :
    X ∈ finStrict (N := N) K ↔ pathPat (N := N) K X ∈ finStrictPat (N := N) K := by
  rw [finStrict_eq_preimage_finStrictPat]
  rfl

/-- **The finite test that `finStrict K` performs reads only the first `K + 1` positions, even when
the path is presented through the wider window `n ≥ K`.** -/
theorem mem_finStrict_iff_restrict_pattern {K n : ℕ} (h : K ≤ n) {X : ℕ → Fin N → ℤ} :
    X ∈ finStrict (N := N) K
      ↔ restrictPat (N := N) h (pathPat (N := N) n X) ∈ finStrictPat (N := N) K := by
  rw [mem_finStrict_iff_pattern, pathPat_restrictPat]

/-- Every `n`-horizon strict pattern projects to a `K`-horizon strict pattern (`K ≤ n`). -/
theorem restrictPat_mem_finStrictPat {K n : ℕ} (h : K ≤ n)
    {Q : Fin (n + 1) → Fin N → ℤ} (hQ : Q ∈ finStrictPat (N := N) n) :
    restrictPat (N := N) h Q ∈ finStrictPat (N := N) K := by
  obtain ⟨h0, hpos⟩ := hQ
  refine ⟨fun i => h0 i, fun k hk i => ?_⟩
  exact hpos ⟨(k : ℕ), by have := k.2; omega⟩ hk i

/-- The extension of a `K`-horizon pattern to an `n`-horizon pattern: the first `K + 1` positions
are kept and the remaining ones are made strictly increasing (hence positive). -/
def extendPat {K n : ℕ} (_h : K ≤ n) (P : Fin (K + 1) → Fin N → ℤ) :
    Fin (n + 1) → Fin N → ℤ :=
  fun k i => if hk : (k : ℕ) ≤ K then P ⟨(k : ℕ), by omega⟩ i else ((k : ℕ) : ℤ) + 1

/-- Value of the extension on the kept positions. -/
theorem extendPat_apply_of_le {K n : ℕ} (h : K ≤ n) (P : Fin (K + 1) → Fin N → ℤ)
    {k : Fin (n + 1)} (hk : (k : ℕ) ≤ K) (i : Fin N) :
    extendPat (N := N) h P k i = P ⟨(k : ℕ), by omega⟩ i := by
  simp only [extendPat, dif_pos hk]

/-- Value of the extension beyond the kept positions. -/
theorem extendPat_apply_of_gt {K n : ℕ} (h : K ≤ n) (P : Fin (K + 1) → Fin N → ℤ)
    {k : Fin (n + 1)} (hk : ¬ (k : ℕ) ≤ K) (i : Fin N) :
    extendPat (N := N) h P k i = ((k : ℕ) : ℤ) + 1 := by
  simp only [extendPat, dif_neg hk]

/-- On the first `K + 1` positions the extension and the kept pattern have the same values. -/
theorem extendPat_succAbove {K n : ℕ} (h : K ≤ n) (P : Fin (K + 1) → Fin N → ℤ)
    (k : Fin (K + 1)) (i : Fin N) :
    extendPat (N := N) h P ⟨(k : ℕ), Nat.lt_of_lt_of_le k.2 (Nat.succ_le_succ h)⟩ i = P k i := by
  have hk : ((⟨(k : ℕ), Nat.lt_of_lt_of_le k.2 (Nat.succ_le_succ h)⟩ : Fin (n + 1)) : ℕ) ≤ K :=
    Nat.le_of_lt_succ k.2
  rw [extendPat_apply_of_le h P hk i]

/-- The extension projects back to the pattern it extends. -/
theorem restrictPat_extendPat {K n : ℕ} (h : K ≤ n) (P : Fin (K + 1) → Fin N → ℤ) :
    restrictPat (N := N) h (extendPat (N := N) h P) = P := by
  funext k i
  exact extendPat_succAbove h P k i

/-- A strict `K`-horizon pattern extends to a strict `n`-horizon pattern. -/
theorem extendPat_mem_finStrictPat {K n : ℕ} (h : K ≤ n)
    {P : Fin (K + 1) → Fin N → ℤ} (hP : P ∈ finStrictPat (N := N) K) :
    extendPat (N := N) h P ∈ finStrictPat (N := N) n := by
  obtain ⟨h0, hpos⟩ := hP
  refine ⟨fun i => ?_, fun k hk i => ?_⟩
  · have hzero : ((0 : ℕ)) ≤ K := Nat.zero_le K
    rw [extendPat_apply_of_le h P hzero i]
    exact h0 i
  · have hk1 : 1 ≤ (k : ℕ) := hk
    by_cases hle : (k : ℕ) ≤ K
    · rw [extendPat_apply_of_le h P hle i]
      exact hpos ⟨(k : ℕ), by have := k.2; omega⟩ hk1 i
    · rw [extendPat_apply_of_gt h P hle i]
      have hcast : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
      linarith

/-- **No strict pattern is lost by widening the window**: the `K`-horizon strict patterns are
exactly the projections of the `n`-horizon strict patterns. -/
theorem finStrictPat_eq_image {K n : ℕ} (h : K ≤ n) :
    finStrictPat (N := N) K = restrictPat (N := N) h '' finStrictPat (N := N) n := by
  ext P
  constructor
  · intro hP
    exact ⟨extendPat (N := N) h P, extendPat_mem_finStrictPat h hP,
      restrictPat_extendPat h P⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact restrictPat_mem_finStrictPat h hQ

/-! ## 4. The prefix-cylinder set identity on path space -/

/-- **The core set identity.**  For any ambient set `A` of paths and any base pattern set `C`,
the width-`n` prefix cylinder over `C` is the width-`K` cylinder over `C`. -/
theorem inter_pathPat_prefix {K n : ℕ} (h : K ≤ n) (A : Set (ℕ → Fin N → ℤ))
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    A ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = A ∩ pathPat (N := N) K ⁻¹' C := by
  have hcomp : (fun X : ℕ → Fin N → ℤ =>
      restrictPat (N := N) h (pathPat (N := N) n X)) = pathPat (N := N) K :=
    pathPat_comp_restrictPat h
  rw [Set.preimage_preimage, hcomp]

/-- The same with the strictness horizon `K`: the width is irrelevant. -/
theorem finStrict_inter_prefix {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C :=
  inter_pathPat_prefix (N := N) h _ C

/-- The same with the strictness horizon `n` (the wider strictness event): again the width is
irrelevant, only the pattern test is projected. -/
theorem finStrict_n_inter_prefix {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    finStrict (N := N) n ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = finStrict (N := N) n ∩ pathPat (N := N) K ⁻¹' C :=
  inter_pathPat_prefix (N := N) h _ C

/-- The prefix cylinder itself (without any strictness condition). -/
theorem pathPat_preimage_restrictPat {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = pathPat (N := N) K ⁻¹' C := by
  have hcomp : (fun X : ℕ → Fin N → ℤ =>
      restrictPat (N := N) h (pathPat (N := N) n X)) = pathPat (N := N) K :=
    pathPat_comp_restrictPat h
  rw [Set.preimage_preimage, hcomp]

/-! ## 5. Word-level prefix correspondence (general `K ≤ n`) -/

/-- The prefix word of length `K` of a word of length `n`. -/
def prefixWord {K n : ℕ} (h : K ≤ n) (q : Fin n → JumpVec N) : Fin K → JumpVec N :=
  fun k => q ⟨(k : ℕ), by have := k.2; omega⟩

/-- On the common time range, the prefix word and the word define the same jump sequence. -/
theorem seqOf_prefixWord {K n : ℕ} (h : K ≤ n) (q : Fin n → JumpVec N) {t : ℕ} (ht : t < K) :
    seqOf (prefixWord (N := N) h q) t = seqOf q t := by
  have htn : t < n := by omega
  simp only [seqOf, dif_pos htn, dif_pos ht, prefixWord]

/-- Positions up to `K` agree for a word and its prefix. -/
theorem posAt_seqOf_prefixWord {K n : ℕ} (h : K ≤ n) (q : Fin n → JumpVec N) {t : ℕ}
    (ht : t ≤ K) (i : Fin N) :
    posAt (seqOf (prefixWord (N := N) h q)) t i = posAt (seqOf q) t i := by
  unfold posAt
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [seqOf_prefixWord (N := N) (K := K) (n := n) h q (t := j) (by omega)]

/-- **Strict positivity is prefix-closed**: the prefix word of a strictly positive word is strictly
positive. -/
theorem posSeqFin_prefixWord {K n : ℕ} (h : K ≤ n) {q : Fin n → JumpVec N}
    (hq : PosSeqFin q) : PosSeqFin (prefixWord (N := N) h q) := by
  intro k hk i
  have hkK : (k : ℕ) ≤ K := Nat.le_of_lt_succ k.2
  have hkn : (k : ℕ) < n + 1 := by omega
  rw [posAt_seqOf_prefixWord (N := N) (K := K) (n := n) h q (t := (k : ℕ)) hkK i]
  exact hq ⟨(k : ℕ), hkn⟩ hk i

/-- **The pattern of the prefix word is the projection of the pattern.** -/
theorem patOf_prefixWord {K n : ℕ} (h : K ≤ n) (q : Fin n → JumpVec N) :
    restrictPat (N := N) h (patOf (N := N) q) = patOf (N := N) (prefixWord (N := N) h q) := by
  funext k i
  have hkK : (k : ℕ) ≤ K := Nat.le_of_lt_succ k.2
  exact (posAt_seqOf_prefixWord (N := N) (K := K) (n := n) h q (t := (k : ℕ)) hkK i).symm

/-! ## 6. The window family on prefix cylinders is its diagonal -/

/-- The prefix-cylinder sub-family of `FinHorizonWindow`: only `C` that read the first `K + 1`
positions, tested at a window width `n ≥ K`. -/
def FinHorizonWindowPrefix (p : ℝ) (π : Measure (RecState N m)) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) : Prop :=
  ∀ (K n : ℕ) (h : K ≤ n) (C : Set (Fin (K + 1) → Fin N → ℤ)), MeasurableSet C →
    μ (Φ ⁻¹' (finStrict (N := N) K
        ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)))
      = π (srSet N m) * (arrayMeasure N)
          {U : Array N | posPath p m U ∈ finStrict (N := N) K
            ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)}

/-- The diagonal (`n = K`) slice of the window family. -/
def FinHorizonWindowDiag (p : ℝ) (π : Measure (RecState N m)) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) : Prop :=
  ∀ (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)), MeasurableSet C →
    μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C))
      = π (srSet N m) * (arrayMeasure N)
          {U : Array N | posPath p m U ∈ finStrict (N := N) K
            ∩ pathPat (N := N) K ⁻¹' C}

/-- **A single member at a prefix cylinder is the diagonal member**: both sides of `(★ K n)` are
literally the corresponding sides of `(★ K K)`. -/
theorem finHorizonWindow_prefix_member_iff {p : ℝ} {π : Measure (RecState N m)} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) (K n : ℕ) (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (μ (Φ ⁻¹' (finStrict (N := N) K
          ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)))
        = π (srSet N m) * (arrayMeasure N)
            {U : Array N | posPath p m U ∈ finStrict (N := N) K
              ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)})
      ↔ (μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C))
        = π (srSet N m) * (arrayMeasure N)
            {U : Array N | posPath p m U ∈ finStrict (N := N) K
              ∩ pathPat (N := N) K ⁻¹' C}) := by
  simp only [finStrict_inter_prefix h C]

/-- **The prefix sub-family of `FinHorizonWindow` is exactly its diagonal.**  Restricting `C` to
read only the first `K + 1` positions reduces every member at a window width `n ≥ K` to the member
at width `K`. -/
theorem finHorizonWindowPrefix_iff_diag {p : ℝ} {π : Measure (RecState N m)} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) :
    FinHorizonWindowPrefix (N := N) (m := m) p π μ Φ
      ↔ FinHorizonWindowDiag (N := N) (m := m) p π μ Φ := by
  constructor
  · intro H K C hC
    have hrefl : restrictPat (N := N) (K := K) (n := K) (le_refl K) ⁻¹' C = C := by
      ext P
      simp only [Set.mem_preimage, restrictPat_refl]
    have h := H K K (le_refl K) C hC
    rwa [hrefl] at h
  · intro H K n hKn C hC
    rw [finStrict_inter_prefix hKn C]
    exact H K C hC

/-- The full window family contains the prefix sub-family (immediate). -/
theorem finHorizonWindowPrefix_of_window {p : ℝ} {π : Measure (RecState N m)} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ))
    (h : FinHorizonWindow (N := N) (m := m) p π μ Φ) :
    FinHorizonWindowPrefix (N := N) (m := m) p π μ Φ := by
  intro K n hKn C hC
  have hmeas : MeasurableSet (restrictPat (N := N) hKn ⁻¹' C) :=
    measurableSet_restrictPat_preimage hKn hC
  have hm := h K n _ hmeas
  rwa [finStrict_inter_prefix hKn C] at hm

/-- **The diagonal family is a necessary condition for the full window family**: it is the
prefix sub-family, which the full family contains. -/
theorem finHorizonWindowDiag_of_window {p : ℝ} {π : Measure (RecState N m)} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ))
    (h : FinHorizonWindow (N := N) (m := m) p π μ Φ) :
    FinHorizonWindowDiag (N := N) (m := m) p π μ Φ :=
  (finHorizonWindowPrefix_iff_diag (N := N) (m := m) (p := p) (π := π) μ Φ).mp
    (finHorizonWindowPrefix_of_window (N := N) (m := m) μ Φ h)

/-- Member-level form: from the full window family one gets every diagonal member, and the
diagonal member at `(K, K)` is *the same number* as the width-`n` prefix member at `(K, n)`. -/
theorem finHorizonWindowDiag_member {p : ℝ} {π : Measure (RecState N m)} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ))
    (h : FinHorizonWindow (N := N) (m := m) p π μ Φ) (K : ℕ)
    {C : Set (Fin (K + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C))
      = π (srSet N m) * (arrayMeasure N)
          {U : Array N | posPath p m U ∈ finStrict (N := N) K
            ∩ pathPat (N := N) K ⁻¹' C} :=
  h K K C hC

/-- The measurability bookkeeping: a prefix cylinder is measurable as soon as its base is. -/
theorem measurableSet_prefix_cylinder {K n : ℕ} (h : K ≤ n)
    {C : Set (Fin (K + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    MeasurableSet (finStrict (N := N) K
      ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)) :=
  (measurableSet_finStrict K).inter
    ((measurableSet_restrictPat_preimage h hC).preimage (measurable_pathPat n))

/-! ## 7. The array mass at a prefix cylinder, in word-sum form -/

/-- **The horizon-`K` word sum for a width-`n` prefix cylinder** (`K ≤ n`): the member at
`(K, n, prefix C)` is computed by the same finite sum over `Fin K → JumpVec N` as the diagonal. -/
theorem arrayMeasure_finStrict_prefix_pattern {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m K n : ℕ) (h : K ≤ n) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K
        ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)}
      = ∑ q : Fin K → JumpVec N,
          if PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ C
            then ENNReal.ofReal (pathW p K q (startState (N := N) m)) else 0 := by
  rw [finStrict_inter_prefix h C, arrayMeasure_finStrict_pattern p hp0 hp1 m K C]

/-- **The same reduction with the wider strictness horizon `n`**: the pattern test is the
*projected* one, so it is read on the prefix pattern `restrictPat h (patOf q)$, while the weight
stays the `n`-step word weight.  This is the piece of the `n > K` bookkeeping that is genuinely
about `n`: the pattern condition passes to the projection, the weight does not. -/
theorem arrayMeasure_finStrict_n_prefix_pattern {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m K n : ℕ) (h : K ≤ n) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) n
        ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)}
      = ∑ q : Fin n → JumpVec N,
          if PosSeqFin (N := N) q ∧ restrictPat (N := N) h (patOf (N := N) q) ∈ C
            then ENNReal.ofReal (pathW p n q (startState (N := N) m)) else 0 := by
  rw [arrayMeasure_finStrict_pattern p hp0 hp1 m n (restrictPat (N := N) h ⁻¹' C)]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : PosSeqFin (N := N) q ∧ patOf (N := N) q ∈ restrictPat (N := N) h ⁻¹' C
  · rw [if_pos hq, if_pos ⟨hq.1, hq.2⟩]
  · rw [if_neg hq, if_neg (fun h => hq ⟨h.1, h.2⟩)]

/-! ## 8. The unrestricted (`n > K`) reduction fails: compiled witnesses

The reduction above is for prefix `C` only.  A `C` that genuinely reads a position `> K` is not a
prefix cylinder at all, and the window mass at width `n > K` is *not* a function of the diagonal
window mass.  Both witnesses use the two nearest-neighbour paths `0,1,0` and `0,1,2`, which agree
on the first two positions, both lie in `finStrict 1`, and are distinguished by the third
position. -/

/-- The all-right pattern on `K + 1` positions: position `k` is `k`. -/
def upPatK (K : ℕ) (N : ℕ) : Fin (K + 1) → Fin N → ℤ := fun k _ => ((k : ℕ) : ℤ)

/-- The all-right pattern on `K + 1` positions is a strict `K`-horizon pattern. -/
theorem upPatK_mem_finStrictPat (K : ℕ) : upPatK K N ∈ finStrictPat (N := N) K := by
  constructor
  · intro i
    simp [upPatK]
  · intro k hk i
    have hk1 : (0 : ℤ) < ((k : ℕ) : ℤ) := by
      have h1 : (1 : ℤ) ≤ ((k : ℕ) : ℤ) := by exact_mod_cast hk
      linarith
    simpa [upPatK] using hk1

/-- The all-right pattern `0, 1, 2` on three positions. -/
def upPat (N : ℕ) : Fin 3 → Fin N → ℤ := fun k _ => ((k : ℕ) : ℤ)

/-- The zig-zag pattern `0, 1, 0`: right then left. -/
def zigPat (N : ℕ) : Fin 3 → Fin N → ℤ :=
  fun k _ => if (k : ℕ) = 2 then 0 else ((k : ℕ) : ℤ)

/-- The projection of the zig-zag pattern is the all-right pattern on two positions. -/
theorem restrictPat_zigPat :
    restrictPat (N := N) (show 1 ≤ 2 by omega) (zigPat N) = upPatK 1 N := by
  funext k i
  fin_cases k <;> simp [zigPat, upPatK, restrictPat]

/-- The projection of the all-right three-position pattern is the same two-position pattern. -/
theorem restrictPat_upPat :
    restrictPat (N := N) (show 1 ≤ 2 by omega) (upPat N) = upPatK 1 N := by
  funext k i
  fin_cases k <;> simp [upPat, upPatK, restrictPat]

/-- The two witness patterns agree on the first two positions. -/
theorem restrictPat_zigPat_eq_upPat :
    restrictPat (N := N) (show 1 ≤ 2 by omega) (zigPat N)
      = restrictPat (N := N) (show 1 ≤ 2 by omega) (upPat N) := by
  rw [restrictPat_zigPat, restrictPat_upPat]

/-- The measurable pattern set that reads the third position. -/
def zeroAtTwo : Set (Fin 3 → Fin N → ℤ) := {P | ∀ i, P ⟨2, by omega⟩ i = 0}

theorem measurableSet_zeroAtTwo : MeasurableSet (zeroAtTwo (N := N)) := by
  have h : zeroAtTwo (N := N) = ⋂ i : Fin N,
      (fun P : Fin 3 → Fin N → ℤ => P ⟨2, by omega⟩ i) ⁻¹' ({0} : Set ℤ) := by
    ext P
    simp [zeroAtTwo]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_singleton (0 : ℤ)).preimage
      ((measurable_pi_apply i).comp (measurable_pi_apply _))

theorem zigPat_mem_zeroAtTwo : zigPat N ∈ zeroAtTwo (N := N) := by
  intro i
  simp [zigPat]

theorem upPat_not_mem_zeroAtTwo (hN : 0 < N) : upPat N ∉ zeroAtTwo (N := N) := by
  intro h
  have hh := h ⟨0, hN⟩
  simp [upPat] at hh

/-- **Pattern-level non-reduction.**  The `K = 1`, width-`2` window set
`restrictPat ⁻¹' finStrictPat 1 ∩ {P | P 2 = 0}` is not the `K = 1`, width-`1` window set of any
base pattern set `C'`: the patterns `0,1,0` and `0,1,2` agree on the first two positions, both
project into `finStrictPat 1`, and are separated by the third position. -/
theorem not_prefix_cylinder_pattern (hN : 0 < N) :
    ¬ ∃ C' : Set (Fin 2 → Fin N → ℤ),
      restrictPat (N := N) (show 1 ≤ 2 by omega) ⁻¹' finStrictPat (N := N) 1
          ∩ zeroAtTwo (N := N)
        = restrictPat (N := N) (show 1 ≤ 2 by omega)
            ⁻¹' (finStrictPat (N := N) 1 ∩ C') := by
  rintro ⟨C', hC'⟩
  have hzig : zigPat N ∈ restrictPat (N := N) (show 1 ≤ 2 by omega) ⁻¹' finStrictPat (N := N) 1
      ∩ zeroAtTwo (N := N) := by
    refine ⟨?_, zigPat_mem_zeroAtTwo⟩
    rw [Set.mem_preimage, restrictPat_zigPat]
    exact upPatK_mem_finStrictPat 1
  rw [hC'] at hzig
  have hmem : restrictPat (N := N) (show 1 ≤ 2 by omega) (upPat N) ∈ C' := by
    rw [← restrictPat_zigPat_eq_upPat]
    exact hzig.2
  have hmem' : upPat N ∈ restrictPat (N := N) (show 1 ≤ 2 by omega)
      ⁻¹' (finStrictPat (N := N) 1 ∩ C') := by
    refine ⟨?_, hmem⟩
    rw [restrictPat_upPat]
    exact upPatK_mem_finStrictPat 1
  rw [← hC'] at hmem'
  exact upPat_not_mem_zeroAtTwo hN hmem'.2

/-! ### The array-level witness -/

/-- The word `right, left`. -/
def wordUD (N : ℕ) : Fin 2 → JumpVec N :=
  fun k => if (k : ℕ) = 0 then (fun _ => true) else (fun _ => false)

/-- The word `right, right`. -/
def wordUU (N : ℕ) : Fin 2 → JumpVec N := fun _ => (fun _ => true)

theorem wordUD_zero : wordUD N ⟨0, by omega⟩ = (fun _ => true) := by
  simp [wordUD]

theorem wordUD_one : wordUD N ⟨1, by omega⟩ = (fun _ => false) := by
  simp [wordUD]

theorem wordUU_zero : wordUU N ⟨0, by omega⟩ = (fun _ => true) := by
  funext i
  rfl

theorem wordUU_one : wordUU N ⟨1, by omega⟩ = (fun _ => true) := by
  funext i
  rfl

/-- Every jump box of the actual array law is non-empty. -/
theorem jbox_nonempty {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m k : ℕ)
    (q : Fin k → JumpVec N) : (jbox p m k q).Nonempty := by
  have hpos : 0 < pathW p k q (startState (N := N) m) := pathW_pos hp0 hp1 m k q
  have hne : (arrayMeasure N) (jbox p m k q) ≠ 0 := by
    rw [mass_jbox_pathW hp0 hp1 m k q]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hne (by rw [h]; simp)

/-- One `right` jump from a fresh level puts the walker at level `1`. -/
theorem posAt_extendPath_one {q : Fin 2 → JumpVec N} (hq0 : q ⟨0, by omega⟩ = (fun _ => true))
    (i : Fin N) : posAt (extendPath q) 1 i = 1 := by
  rw [posAt_succ, posAt_zero, zero_add]
  have h0 : extendPath q 0 i = true := by
    rw [extendPath_apply q (n := 0) (by omega), hq0]
  rw [h0]
  norm_num

/-- `right` then `left`: back to level `0`. -/
theorem posAt_extendPath_two_UD {q : Fin 2 → JumpVec N}
    (hq0 : q ⟨0, by omega⟩ = (fun _ => true))
    (hq1 : q ⟨1, by omega⟩ = (fun _ => false)) (i : Fin N) :
    posAt (extendPath q) 2 i = 0 := by
  rw [posAt_succ, posAt_extendPath_one hq0 i]
  have h1 : extendPath q 1 i = false := by
    rw [extendPath_apply q (n := 1) (by omega), hq1]
  rw [h1]
  norm_num

/-- `right` then `right`: level `2`. -/
theorem posAt_extendPath_two_UU {q : Fin 2 → JumpVec N}
    (hq0 : q ⟨0, by omega⟩ = (fun _ => true))
    (hq1 : q ⟨1, by omega⟩ = (fun _ => true)) (i : Fin N) :
    posAt (extendPath q) 2 i = 2 := by
  rw [posAt_succ, posAt_extendPath_one hq0 i]
  have h1 : extendPath q 1 i = true := by
    rw [extendPath_apply q (n := 1) (by omega), hq1]
  rw [h1]
  norm_num

/-- On a box whose first letter is `right`, every walker is at level `1` at time `1`. -/
theorem posPath_one_of_box {p : ℝ} {q : Fin 2 → JumpVec N}
    (hq0 : q ⟨0, by omega⟩ = (fun _ => true)) {ω : Array N} (hbox : ω ∈ jbox p m 2 q)
    (i : Fin N) : posPath p m ω 1 i = 1 := by
  show (trajectory p m ω 1).pos i = 1
  rw [array_trajectory_pos_eq_wordCyl p m q hbox (by omega) i]
  exact posAt_extendPath_one hq0 i

/-- On a box with letters `right, left`, every walker is at level `0` at time `2`. -/
theorem posPath_two_of_box_UD {p : ℝ} {q : Fin 2 → JumpVec N}
    (hq0 : q ⟨0, by omega⟩ = (fun _ => true))
    (hq1 : q ⟨1, by omega⟩ = (fun _ => false)) {ω : Array N} (hbox : ω ∈ jbox p m 2 q)
    (i : Fin N) : posPath p m ω 2 i = 0 := by
  show (trajectory p m ω 2).pos i = 0
  rw [array_trajectory_pos_eq_wordCyl p m q hbox (le_refl 2) i]
  exact posAt_extendPath_two_UD hq0 hq1 i

/-- On a box with letters `right, right`, every walker is at level `2` at time `2`. -/
theorem posPath_two_of_box_UU {p : ℝ} {q : Fin 2 → JumpVec N}
    (hq0 : q ⟨0, by omega⟩ = (fun _ => true))
    (hq1 : q ⟨1, by omega⟩ = (fun _ => true)) {ω : Array N} (hbox : ω ∈ jbox p m 2 q)
    (i : Fin N) : posPath p m ω 2 i = 2 := by
  show (trajectory p m ω 2).pos i = 2
  rw [array_trajectory_pos_eq_wordCyl p m q hbox (le_refl 2) i]
  exact posAt_extendPath_two_UU hq0 hq1 i

/-- **Array-level non-reduction.**  The `K = 1`, width-`2` window set that reads the third position
is not the `K = 1`, width-`1` window set of any base pattern set `C'`.  The two witness arrays sit
in the jump boxes of `right, left` and `right, right`; both are at level `1` at time `1` (so both lie
in `finStrict 1`), they agree on the first two positions, and the third position is `0` versus
`2`. -/
theorem not_prefix_cylinder_array {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (hN : 0 < N) :
    ¬ ∃ C' : Set (Fin 2 → Fin N → ℤ),
      {U : Array N | posPath p m U ∈ finStrict (N := N) 1
          ∩ pathPat (N := N) 2 ⁻¹' zeroAtTwo (N := N)}
        = {U : Array N | posPath p m U ∈ finStrict (N := N) 1
          ∩ pathPat (N := N) 1 ⁻¹' C'} := by
  classical
  rintro ⟨C', hC'⟩
  obtain ⟨ω₁, hbox₁⟩ := jbox_nonempty (N := N) hp0 hp1 m 2 (wordUD N)
  obtain ⟨ω₂, hbox₂⟩ := jbox_nonempty (N := N) hp0 hp1 m 2 (wordUU N)
  -- both arrays are in `finStrict 1`
  have hfs₁ : posPath p m ω₁ ∈ finStrict (N := N) 1 := by
    refine ⟨fun i => posPath_zero p m ω₁ i, fun n hn hn1 i => ?_⟩
    have hn1' : n = 1 := by omega
    rw [hn1']
    rw [posPath_one_of_box (p := p) (m := m) (wordUD_zero (N := N)) hbox₁ i]
    norm_num
  have hfs₂ : posPath p m ω₂ ∈ finStrict (N := N) 1 := by
    refine ⟨fun i => posPath_zero p m ω₂ i, fun n hn hn1 i => ?_⟩
    have hn1' : n = 1 := by omega
    rw [hn1']
    rw [posPath_one_of_box (p := p) (m := m) (wordUU_zero (N := N)) hbox₂ i]
    norm_num
  -- the two arrays agree on the first two positions
  have hpatOne : pathPat (N := N) 1 (posPath p m ω₁)
      = pathPat (N := N) 1 (posPath p m ω₂) := by
    funext k i
    fin_cases k
    · exact (posPath_zero p m ω₁ i).trans (posPath_zero p m ω₂ i).symm
    · exact (posPath_one_of_box (p := p) (m := m) (wordUD_zero (N := N)) hbox₁ i).trans
        (posPath_one_of_box (p := p) (m := m) (wordUU_zero (N := N)) hbox₂ i).symm
  -- the first array is in the width-`2` window set
  have hS₁ : ω₁ ∈ {U : Array N | posPath p m U ∈ finStrict (N := N) 1
      ∩ pathPat (N := N) 2 ⁻¹' zeroAtTwo (N := N)} := by
    refine ⟨hfs₁, fun i => ?_⟩
    exact posPath_two_of_box_UD (p := p) (m := m) (wordUD_zero (N := N)) (wordUD_one (N := N))
      hbox₁ i
  have hR₁ : ω₁ ∈ {U : Array N | posPath p m U ∈ finStrict (N := N) 1
      ∩ pathPat (N := N) 1 ⁻¹' C'} := by
    rw [← hC']
    exact hS₁
  have hmem₁ : pathPat (N := N) 1 (posPath p m ω₁) ∈ C' := hR₁.2
  have hmem₂ : pathPat (N := N) 1 (posPath p m ω₂) ∈ C' := by
    rw [← hpatOne]
    exact hmem₁
  have hS₂ : ω₂ ∈ {U : Array N | posPath p m U ∈ finStrict (N := N) 1
      ∩ pathPat (N := N) 2 ⁻¹' zeroAtTwo (N := N)} := by
    rw [hC']
    exact ⟨hfs₂, hmem₂⟩
  have hzero : posPath p m ω₂ 2 ⟨0, hN⟩ = 0 := hS₂.2 ⟨0, hN⟩
  have htwo : posPath p m ω₂ 2 ⟨0, hN⟩ = 2 :=
    posPath_two_of_box_UU (p := p) (m := m) (wordUU_zero (N := N)) (wordUU_one (N := N))
      hbox₂ ⟨0, hN⟩
  rw [htwo] at hzero
  exact absurd hzero (by norm_num)

/-! ## 9. The exact tail content of the wider strictness horizon

`finStrict n` is `finStrict K` conjoined with positivity on the *tail* times `K < t ≤ n`.  That
tail condition is independent of `C`, so for prefix cylinders the wider member splits exactly into
the diagonal set and a `C`-weighted tail term.  This is the precise statement of what the `n > K`
part of the window family adds: not a new pattern condition, but tail positivity. -/

/-- Positivity on the tail times `K < t ≤ n`. -/
def finStrictTail (K n : ℕ) : Set (ℕ → Fin N → ℤ) :=
  {X | ∀ t, K < t → t ≤ n → ∀ i, 0 < X t i}

theorem mem_finStrictTail {K n : ℕ} {X : ℕ → Fin N → ℤ} :
    X ∈ finStrictTail (N := N) K n ↔ ∀ t, K < t → t ≤ n → ∀ i, 0 < X t i :=
  Iff.rfl

/-- The tail condition is measurable. -/
theorem measurableSet_finStrictTail (K n : ℕ) :
    MeasurableSet (finStrictTail (N := N) K n) := by
  have heq : finStrictTail (N := N) K n
      = ⋂ (t : {t : ℕ // K < t ∧ t ≤ n}), ⋂ i : Fin N,
          {X : ℕ → Fin N → ℤ | 0 < X t.1 i} := by
    ext X
    constructor
    · intro h
      exact Set.mem_iInter.mpr fun t => Set.mem_iInter.mpr fun i => h t t.2.1 t.2.2 i
    · intro h t htK htn i
      exact Set.mem_iInter.mp (Set.mem_iInter.mp h ⟨t, htK, htn⟩) i
  rw [heq]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (measurable_eval (N := N) t.1 i)

/-- **`finStrict n` is `finStrict K` plus tail positivity** (`K ≤ n`). -/
theorem finStrict_eq_inter_tail {K n : ℕ} (h : K ≤ n) :
    finStrict (N := N) n = finStrict (N := N) K ∩ finStrictTail (N := N) K n := by
  ext X
  constructor
  · intro hX
    refine ⟨finStrict_antitone h hX, ?_⟩
    intro t htK htn i
    exact hX.2 t (by omega) htn i
  · rintro ⟨hXK, hXtail⟩
    refine ⟨hXK.1, fun t ht htn i => ?_⟩
    by_cases htK : t ≤ K
    · exact hXK.2 t ht htK i
    · exact hXtail t (by omega) htn i

/-- **The prefix cylinder at the wider strictness horizon, split by the tail.** -/
theorem finStrict_n_inter_prefix_eq_tail {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    finStrict (N := N) n ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C)
          ∩ finStrictTail (N := N) K n := by
  rw [finStrict_n_inter_prefix h C, finStrict_eq_inter_tail h]
  ext X
  simp only [Set.mem_inter_iff]
  tauto

/-- The width-`n` prefix cylinder sits inside the width-`K` cylinder: widening the strictness
horizon while keeping the pattern test at the first `K + 1` positions can only shrink the event. -/
theorem prefix_cylinder_subset {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    finStrict (N := N) n ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      ⊆ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C := by
  rw [finStrict_n_inter_prefix h C]
  exact fun X hX => ⟨finStrict_antitone h hX.1, hX.2⟩

/-- The array mass of the wider prefix cylinder is at most the mass of the diagonal one. -/
theorem arrayMass_finStrict_n_prefix_le {p : ℝ} (m : ℕ) {K n : ℕ} (h : K ≤ n)
    (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) n
        ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)}
      ≤ (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) K
        ∩ pathPat (N := N) K ⁻¹' C} :=
  measure_mono (Set.preimage_mono (prefix_cylinder_subset h C))

/-- The same monotonicity for an arbitrary ambient law and measurable path map. -/
theorem measure_finStrict_n_prefix_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Φ : Ω → (ℕ → Fin N → ℤ)) {K n : ℕ} (h : K ≤ n) (C : Set (Fin (K + 1) → Fin N → ℤ)) :
    μ (Φ ⁻¹' (finStrict (N := N) n
        ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)))
      ≤ μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C)) :=
  measure_mono (Set.preimage_mono (prefix_cylinder_subset h C))

/-- **The tower identity for a prefix cylinder.**  The diagonal member mass is the width-`n`
prefix member mass plus the mass of the tail-violating part.  The tail set does not involve `C`;
the `C`-dependence of both terms is through the same base pattern set. -/
theorem window_diag_mass_eq_n_add_tail {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) {K n : ℕ} (h : K ≤ n)
    {C : Set (Fin (K + 1) → Fin N → ℤ)} (hC : MeasurableSet C) (hΦ : Measurable Φ) :
    μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C))
      = μ (Φ ⁻¹' (finStrict (N := N) n
            ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)))
        + μ (Φ ⁻¹' (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ
            ∩ pathPat (N := N) K ⁻¹' C)) := by
  classical
  have hK : (finStrict (N := N) K : Set (ℕ → Fin N → ℤ))
      = finStrict (N := N) n ∪ (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ) := by
    rw [finStrict_eq_inter_tail h]
    ext X
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hsplit : finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C
      = (finStrict (N := N) n ∩ pathPat (N := N) K ⁻¹' C)
        ∪ (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ
            ∩ pathPat (N := N) K ⁻¹' C) := by
    conv_lhs => rw [hK]
    rw [Set.union_inter_distrib_right]
  have hpath : finStrict (N := N) n ∩ pathPat (N := N) n ⁻¹' (restrictPat (N := N) h ⁻¹' C)
      = finStrict (N := N) n ∩ pathPat (N := N) K ⁻¹' C := by
    rw [pathPat_preimage_restrictPat h C]
  have hdisj : Disjoint (finStrict (N := N) n ∩ pathPat (N := N) K ⁻¹' C)
      (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ
        ∩ pathPat (N := N) K ⁻¹' C) := by
    rw [Set.disjoint_left]
    intro X hX hY
    have htail : X ∈ finStrictTail (N := N) K n := by
      have hXn : X ∈ finStrict (N := N) n := hX.1
      rw [finStrict_eq_inter_tail h] at hXn
      exact hXn.2
    exact hY.1.2 htail
  have hmeas2 : MeasurableSet (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ
      ∩ pathPat (N := N) K ⁻¹' C) :=
    ((measurableSet_finStrict K).inter (measurableSet_finStrictTail K n).compl).inter
      (hC.preimage (measurable_pathPat K))
  have hdisjPre : Disjoint (Φ ⁻¹' (finStrict (N := N) n ∩ pathPat (N := N) K ⁻¹' C))
      (Φ ⁻¹' (finStrict (N := N) K ∩ (finStrictTail (N := N) K n)ᶜ
        ∩ pathPat (N := N) K ⁻¹' C)) := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro X hX hY
    exact hdisj hX hY
  rw [hpath, hsplit, Set.preimage_union, measure_union hdisjPre (hΦ hmeas2)]

end SwarmPrefix


/-! ## Axiom audit -/


