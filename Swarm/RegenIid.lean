/-
# Regeneration blocks are independent and identically distributed

The last step of `main_1d_revised.tex` §3.2 (Proposition `regen`) is:

> "We obtain the last equality by taking `B` to be the whole path space.  Summing
> over `d,t`, we conclude that the translated future after `τ_D` has law `P^*` and
> is independent of `(D, τ_D, (X_n^i)_{0 ≤ n ≤ τ_D})`.  By iteration, the
> successive distance and duration increments are independent and identically
> distributed with the joint law of `(D, τ_D)`."

This file isolates the abstract content of that iteration.  The data are

* `Z k` — the contents of the `k`-th regeneration block (distance, duration, and
  the path segment), a random element of a measurable space `S`;
* `Q` — the law of one block under the conditioned path law `P^*`.

The single hypothesis `FreshBlocks Z Q` says: for every `n`, conditionally on the
joint contents of the first `n` blocks, the `n`-th block has law `Q` and is
independent of that past.  This is exactly the paper's `(factor)`: the block
contents are measurable functionals of the past up to `τ_{z_n}`, and the
translated future after `τ_{z_n}` is independent of that past with law `P^*`.

Conclusion (`prod_finset`, `indep_of_fresh`, `ident_distrib_of_fresh`): for every
finite set of block indices the joint law of the selected blocks is the product
of `Q`, hence any two blocks of the sequence are independent and identically
distributed with law `Q`.  This supplies the `hDindep`/`hDid` (and `hTindep`/
`hTid`) hypotheses of `results/lean/RenewalStrongLaw.lean`.

Every declaration is checked by `verify.sh` and `Audit.lean` (`#print axioms`).
-/
import Swarm.Imports
import Swarm.KacDisjoint

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace KacFormula

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {S : Type*} [MeasurableSpace S]

/-- The joint contents of the first `n` regeneration blocks. -/
def joint (Z : ℕ → Ω → S) (n : ℕ) : Ω → (Fin n → S) := fun ω i => Z i ω

lemma measurable_joint {Z : ℕ → Ω → S} (hZ : ∀ k, Measurable (Z k)) (n : ℕ) :
    Measurable (joint Z n) :=
  measurable_pi_lambda _ fun i => hZ i

/-- **Renewal structure hypothesis**: conditionally on the first `n` block contents,
the `n`-th block has law `Q` and is independent of the past. -/
def FreshBlocks (μ : Measure Ω) (Z : ℕ → Ω → S) (Q : Measure S) : Prop :=
  (∀ k, Measurable (Z k)) ∧
    ∀ (n : ℕ) (E : Set (Fin n → S)) (C : Set S), MeasurableSet E → MeasurableSet C →
      μ (joint Z n ⁻¹' E ∩ Z n ⁻¹' C) = μ (joint Z n ⁻¹' E) * Q C

/-- The prefix described by the first `n` blocks is the intersection over `range n`. -/
lemma joint_pi_preimage (Z : ℕ → Ω → S) (n : ℕ) (t : ℕ → Set S) :
    joint Z n ⁻¹' (Set.univ.pi (fun i : Fin n => t i))
      = ⋂ i ∈ Finset.range n, Z i ⁻¹' t i := by
  ext ω
  simp only [mem_preimage, joint, Set.mem_pi, Set.mem_univ, true_implies, mem_iInter,
    Finset.mem_range]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · rintro h i
    exact h i i.isLt

lemma measurableSet_pi_fin {t : ℕ → Set S} (ht : ∀ i, MeasurableSet (t i)) (n : ℕ) :
    MeasurableSet (Set.univ.pi (fun i : Fin n => t i)) := by
  refine MeasurableSet.pi Set.countable_univ ?_
  intro i _
  exact ht i

/-- **Product law on initial segments.** -/
lemma prod_initial {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) (t : ℕ → Set S) (ht : ∀ i, MeasurableSet (t i)) (n : ℕ) :
    μ (⋂ i ∈ Finset.range n, Z i ⁻¹' t i) = ∏ i ∈ Finset.range n, Q (t i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (⋂ i ∈ Finset.range (n + 1), Z i ⁻¹' t i)
        = joint Z n ⁻¹' (Set.univ.pi (fun i : Fin n => t i)) ∩ Z n ⁻¹' t n := by
      rw [joint_pi_preimage]
      ext ω
      simp only [mem_inter_iff, mem_iInter, Finset.mem_range]
      constructor
      · intro hh
        exact ⟨fun i hi => hh i (by omega), hh n (Nat.lt_succ_self n)⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h' | h'
        · exact h1 i h'
        · subst h'
          exact h2
    rw [hsplit, h.2 n _ _ (measurableSet_pi_fin ht n) (ht n), joint_pi_preimage, ih,
      Finset.prod_range_succ]

/-- **Product law on an arbitrary finite set of blocks.** -/
lemma prod_finset {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) (s : Finset ℕ) (t : ℕ → Set S) (ht : ∀ i, MeasurableSet (t i)) :
    μ (⋂ i ∈ s, Z i ⁻¹' t i) = ∏ i ∈ s, Q (t i) := by
  set n := s.sup id + 1 with hn
  have hsub : s ⊆ Finset.range n := by
    intro i hi
    simp only [Finset.mem_range, hn]
    have hle := Finset.le_sup (f := id) hi
    simp only [id] at hle
    omega
  set t' : ℕ → Set S := fun i => if i ∈ s then t i else univ with ht'def
  have ht' : ∀ i, MeasurableSet (t' i) := by
    intro i
    by_cases hi : i ∈ s
    · simp only [t', hi, if_true]
      exact ht i
    · simp only [t', hi, if_false]
      exact MeasurableSet.univ
  have hset : (⋂ i ∈ Finset.range n, Z i ⁻¹' t' i) = ⋂ i ∈ s, Z i ⁻¹' t i := by
    ext ω
    simp only [mem_iInter, Finset.mem_range]
    constructor
    · intro hh i hi
      have h1 := hh i (Finset.mem_range.mp (hsub hi))
      simpa only [t', hi, if_true] using h1
    · intro hh i hi
      by_cases his : i ∈ s
      · simpa only [t', his, if_true] using hh i his
      · simp only [t', his, if_false, mem_preimage, mem_univ]
  have hprod1 : ∏ i ∈ Finset.range n, Q (t' i) = ∏ i ∈ s, Q (t' i) := by
    refine (Finset.prod_subset (s₁ := s) (s₂ := Finset.range n) ?_ ?_).symm
    · intro i hi
      simpa using hsub hi
    · intro i _ his
      simp only [t', his, if_false]
      exact measure_univ
  have hprod2 : ∏ i ∈ s, Q (t' i) = ∏ i ∈ s, Q (t i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [t', hi, if_true]
  rw [← hset, prod_initial h t' ht' n, hprod1, hprod2]

/-- Each block has law `Q`. -/
theorem iid_marginal {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) (n : ℕ) : μ.map (Z n) = Q := by
  refine Measure.ext fun C hC => ?_
  rw [Measure.map_apply (h.1 n) hC]
  have hkey := prod_finset h {n} (fun i => if i = n then C else univ) ?_
  · simpa using hkey
  · intro i
    by_cases hi : i = n
    · simp only [hi, if_true]
      exact hC
    · simp only [hi, if_false]
      exact MeasurableSet.univ

/-- Any two distinct blocks are independent. -/
theorem indep_of_fresh {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) {i j : ℕ} (hij : i ≠ j) : IndepFun (Z i) (Z j) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  set t : ℕ → Set S := fun k => if k = i then A else if k = j then B else univ with ht
  have htmeas : ∀ k, MeasurableSet (t k) := by
    intro k
    simp only [ht]
    split_ifs
    · exact hA
    · exact hB
    · exact MeasurableSet.univ
  have hkey := prod_finset h ({i, j} : Finset ℕ) t htmeas
  have hji : ¬ (j = i) := Ne.symm hij
  have hset : (⋂ k ∈ ({i, j} : Finset ℕ), Z k ⁻¹' t k) = Z i ⁻¹' A ∩ Z j ⁻¹' B := by
    ext ω
    simp only [mem_iInter, Finset.mem_insert, Finset.mem_singleton, mem_inter_iff, mem_preimage,
      ht]
    constructor
    · intro hh
      refine ⟨?_, ?_⟩
      · simpa using hh i (Or.inl rfl)
      · have h1 := hh j (Or.inr rfl)
        simpa [hji] using h1
    · rintro ⟨h1, h2⟩ k (rfl | rfl)
      · simpa using h1
      · simp only [hji, if_false, if_true]
        exact h2
  have hprod : (∏ k ∈ ({i, j} : Finset ℕ), Q (t k)) = Q A * Q B := by
    rw [Finset.prod_insert (by simp [hij]), Finset.prod_singleton]
    simp only [ht, hji, if_false, if_true]
  rw [hset, hprod] at hkey
  rw [hkey, ← Measure.map_apply (h.1 i) hA, ← Measure.map_apply (h.1 j) hB,
    iid_marginal h i, iid_marginal h j]

/-- Distinct blocks are identically distributed with law `Q`. -/
theorem ident_distrib_of_fresh {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) (i j : ℕ) : IdentDistrib (Z i) (Z j) μ μ :=
  IdentDistrib.mk (h.1 i).aemeasurable (h.1 j).aemeasurable
    (by rw [iid_marginal h i, iid_marginal h j])

/-- **Bridge to the renewal strong law.**  For any real-valued block functional `d`
(for instance the regeneration distance, the regeneration duration, or a pair of
them), the sequence `k ↦ d (Z k)` is pairwise independent, identically distributed,
and integrable whenever `d` is integrable under the block law `Q`.  These are
literally the hypotheses `hDindep`, `hDid`, `hDint`, `hTindep`, `hTid`, `hTint` of
`RenewalStrongLaw.renewal_strong_law` in `results/lean/`. -/
theorem renewal_block_hypotheses {Z : ℕ → Ω → S} {Q : Measure S} [IsProbabilityMeasure Q]
    (h : FreshBlocks μ Z Q) (d : S → ℝ) (hd : Measurable d) (hint : Integrable d Q) :
    (Pairwise fun i j => IndepFun (fun ω => d (Z i ω)) (fun ω => d (Z j ω)) μ) ∧
      (∀ i, IdentDistrib (fun ω => d (Z i ω)) (fun ω => d (Z 0 ω)) μ μ) ∧
      Integrable (fun ω => d (Z 0 ω)) μ := by
  refine ⟨fun i j hij => ?_, fun i => ?_, ?_⟩
  · have h1 : IndepFun (Z i) (Z j) μ := indep_of_fresh h hij
    simpa only [Function.comp_def] using h1.comp hd hd
  · have h1 : IdentDistrib (Z i) (Z 0) μ μ := ident_distrib_of_fresh h i 0
    simpa only [Function.comp_def] using h1.comp hd
  · have h0 : Integrable d (μ.map (Z 0)) := by rw [iid_marginal h 0]; exact hint
    exact h0.comp_measurable (h.1 0)

end KacFormula
