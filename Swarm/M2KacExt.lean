/-
# Kac's inequality for a one-sided system through an invertible extension

## What the Kac/record chain in `areas/kac/` still needs

`KacFormula.kac_lintegral_le_one` (`Swarm/KacDisjoint.lean`) bounds the mean return time
by `1` for an **invertible** measure-preserving `e : Ω ≃ᵐ Ω`:

    `∫⁻ ω in A, retTime e A ω ≤ 1`,  hence  `E_{P(·|A)}[D] ≤ 1/P(A)`.

`SwarmFront.record_ED_of_invariant_mass` (`Swarm/KacBridge.lean`) instantiates the
mass `P(A) = π(srSet) · P(V)` and states in its header that the *two-sided* Kolmogorov
extension of the record Markov chain — that is, an invertible stationary version of the
one-sided record chain — is what the campaign does not have.

This file isolates that residual in both directions:

* `kac_tsum_le_one_of_extension`, `kac_lintegral_le_one_of_extension`: an **invertible
  measure-preserving extension which factors the one-sided map** carries the Kac inequality
  to the one-sided system, with no further input.  Consequently the whole Kac step reduces to
  the existence of such an extension: nothing else in the one-sided statement is missing.
* `oneSided_kac_lintegral_le_one`: a **complete concrete instance**.  The one-sided i.i.d. bit
  shift is neither injective nor invertible, yet its Kac inequality follows from the
  two-sided shift through the transfer theorem (the two-sided product law and its
  invertible shift are the verified `areas/kac/TwoSided.lean`).
* `tower_sets_meet`, `tower_not_pairwiseDisjoint`: the paper's **disjointness proof is not
  available one-sidedly**.  For the one-sided i.i.d. shift (a measure-preserving, everywhere
  non-injective map) the translated tail sets `T^k(A ∩ {D > k})` genuinely intersect:
  two distinct tower points with `k₁ = 1 ≠ 2 = k₂` map to the same `z`.  Hence no manipulation
  of the one-sided tail sums replaces the extension; `KacDisjoint`'s injectivity is used, not
  decorative.
* `falseSet_subset_translate`, `measure_translate_ge`, `translate_tsum_linear`: the failure is
  not marginal.  **Every** translate `T^k(A ∩ {D > k})`, `k ≥ 1`, contains the whole cylinder
  `{z | z 0 = false}`, so each translate already carries mass `ν {false}` and the partial sums
  of the translate masses grow at least linearly.  The one-sided disjointness computation
  therefore yields no bound at all — it is not that it gives a wrong finite answer.

## Exact residual

`SwarmM2Kac.kac_path_ED_of_extension` records, as one theorem with the extension as an explicit
hypothesis, precisely the missing input of the Kac step: an invertible measure-preserving system
factoring the one-sided stationary record chain.  (Kac's lemma itself is true for every
conservative measure-preserving transformation; what the campaign lacks is a *proof* for the
one-sided record chain, and the disjointness proof below shows why the extension is the
available route.)  Mathlib has projective-limit *uniqueness*
(`MeasureTheory.IsProjectiveLimit.unique`) and the additive cylinder content
(`MeasureTheory.projectiveFamilyContent`) but not Kolmogorov's extension theorem, so the
obligation is exactly "existence of the projective limit of the stationary window laws".

No `sorry`, no `admit`, no custom axiom, no `native_decide`.  Axiom reports are in
`M2Audit.lean`.
-/
import Swarm.KacPaperED
import Swarm.Kac.TwoSided
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

namespace SwarmM2Kac

/-! ## 1. Return times pass through a commuting factor map -/

section Factor

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Iterates of a commuting pair commute with the factor map. -/
theorem iterate_commute {f : Ω → Ω} {g : Ω' → Ω'} {π : Ω' → Ω}
    (hcomm : ∀ x, π (g x) = f (π x)) (k : ℕ) (x : Ω') :
    π ((g^[k]) x) = (f^[k]) (π x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]

/-- `g` has returned to `π ⁻¹' A` at time `k` iff `f` has returned to `A` at time `k`,
read through the factor map. -/
theorem preimage_return_iff {f : Ω → Ω} {g : Ω' → Ω'} {π : Ω' → Ω}
    (hcomm : ∀ x, π (g x) = f (π x)) (A : Set Ω) (k : ℕ) (x : Ω') :
    (g^[k]) x ∈ π ⁻¹' A ↔ (f^[k]) (π x) ∈ A := by
  rw [Set.mem_preimage, iterate_commute hcomm k x]

/-- `g` has *not* returned during the first `k` steps iff the same holds for `f`. -/
theorem noReturn_preimage_iff {f : Ω → Ω} {g : Ω' → Ω'} {π : Ω' → Ω}
    (hcomm : ∀ x, π (g x) = f (π x)) (A : Set Ω) (k : ℕ) :
    π ⁻¹' (KacFormula.noReturn f A k) = KacFormula.noReturn g (π ⁻¹' A) k := by
  ext x
  simp only [KacFormula.noReturn, mem_ofPred_eq, mem_preimage]
  exact ⟨fun h j hj hjk hmem => h j hj hjk ((preimage_return_iff hcomm A j x).mp hmem),
    fun h j hj hjk hmem => h j hj hjk ((preimage_return_iff hcomm A j x).mpr hmem)⟩

/-- **The first-return time is computed through a factor map.** -/
theorem retTime_preimage {f : Ω → Ω} {g : Ω' → Ω'} {π : Ω' → Ω}
    (hcomm : ∀ x, π (g x) = f (π x)) (A : Set Ω) (x : Ω') :
    KacFormula.retTime g (π ⁻¹' A) x = KacFormula.retTime f A (π x) := by
  have hpt : ∀ k : ℕ, (0 < k ∧ (g^[k]) x ∈ π ⁻¹' A) ↔ (0 < k ∧ (f^[k]) (π x) ∈ A) := by
    intro k
    rw [preimage_return_iff hcomm A k x]
  have hiff : (∃ k : ℕ, 0 < k ∧ (g^[k]) x ∈ π ⁻¹' A)
      ↔ (∃ k : ℕ, 0 < k ∧ (f^[k]) (π x) ∈ A) := exists_congr hpt
  unfold KacFormula.retTime
  by_cases h1 : ∃ k : ℕ, 0 < k ∧ (g^[k]) x ∈ π ⁻¹' A
  · have h2 : ∃ k : ℕ, 0 < k ∧ (f^[k]) (π x) ∈ A := hiff.mp h1
    rw [dif_pos h1, dif_pos h2]
    have hle1 : Nat.find h1 ≤ Nat.find h2 := Nat.find_min' h1 ((hpt _).mpr (Nat.find_spec h2))
    have hle2 : Nat.find h2 ≤ Nat.find h1 := Nat.find_min' h2 ((hpt _).mp (Nat.find_spec h1))
    rw [show Nat.find h1 = Nat.find h2 from by omega]
  · have h2 : ¬ ∃ k : ℕ, 0 < k ∧ (f^[k]) (π x) ∈ A := fun h => h1 (hiff.mpr h)
    rw [dif_neg h1, dif_neg h2]

end Factor

/-! ## 2. Kac's inequality transfers from an invertible extension to the one-sided system -/

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **Kac's inequality, tail-sum form, through an invertible extension.**

Let `π : Ω' → Ω` be a measure-preserving factor map, `g` an invertible measure-preserving
self-map of `Ω'` and `f` a self-map of `Ω` with `π ∘ g = f ∘ π`.  Then the one-sided tail
sums `Σ_k μ (A ∩ {D_f > k})` obey Kac's bound.  Only the existence of the extension is used;
`f` itself need not be injective, invertible or measurable. -/
theorem kac_tsum_le_one_of_extension {f : Ω → Ω} (hf : Measurable f) {g : Ω' ≃ᵐ Ω'}
    (hg : MeasurePreserving (g : Ω' → Ω') μ' μ')
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ)
    (hcomm : ∀ x, π (g x) = f (π x)) (A : Set Ω) (hA : MeasurableSet A) :
    ∑' k : ℕ, μ (A ∩ KacFormula.noReturn f A k) ≤ 1 := by
  have hA' : MeasurableSet (π ⁻¹' A) := hA.preimage hπ.measurable
  have hbase := KacFormula.kac_tsum_le_one g hg (π ⁻¹' A) hA'
  have hpre : ∀ B : Set Ω, MeasurableSet B → μ' (π ⁻¹' B) = μ B := by
    intro B hB
    rw [← Measure.map_apply hπ.measurable hB, hπ.map_eq]
  have hterm : ∀ k : ℕ, μ (A ∩ KacFormula.noReturn f A k)
      = μ' (π ⁻¹' A ∩ KacFormula.noReturn g (π ⁻¹' A) k) := by
    intro k
    have hB : MeasurableSet (A ∩ KacFormula.noReturn f A k) :=
      hA.inter (KacFormula.measurableSet_noReturn hf hA k)
    have hset : π ⁻¹' (A ∩ KacFormula.noReturn f A k)
        = π ⁻¹' A ∩ KacFormula.noReturn g (π ⁻¹' A) k := by
      rw [← noReturn_preimage_iff hcomm A k]
      rfl
    rw [← hpre _ hB, hset]
  calc ∑' k : ℕ, μ (A ∩ KacFormula.noReturn f A k)
      = ∑' k : ℕ, μ' (π ⁻¹' A ∩ KacFormula.noReturn g (π ⁻¹' A) k) := tsum_congr hterm
    _ ≤ 1 := hbase

/-- **Kac's inequality, integral form, through an invertible extension**: the mean return
time of the one-sided set `A` is at most `1`. -/
theorem kac_lintegral_le_one_of_extension {f : Ω → Ω} (hf : Measurable f) {g : Ω' ≃ᵐ Ω'}
    (hg : MeasurePreserving (g : Ω' → Ω') μ' μ')
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ)
    (hcomm : ∀ x, π (g x) = f (π x)) (A : Set Ω) (hA : MeasurableSet A) :
    ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1 := by
  have hA' : MeasurableSet (π ⁻¹' A) := hA.preimage hπ.measurable
  have hbase := KacFormula.kac_lintegral_le_one g hg (π ⁻¹' A) hA'
  have hF : Measurable fun ω => (KacFormula.retTime f A ω : ℝ≥0∞) :=
    (KacFormula.measurable_enat_coe.comp (KacFormula.measurable_retTime hf hA))
  have hstep : ∫⁻ x in π ⁻¹' A, (KacFormula.retTime g (π ⁻¹' A) x : ℝ≥0∞) ∂μ'
      = ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ := by
    rw [setLIntegral_congr_fun hA' (fun x _ => by rw [retTime_preimage hcomm])]
    rw [← lintegral_indicator hA', ← lintegral_indicator hA]
    have hfun : (π ⁻¹' A).indicator (fun x => (KacFormula.retTime f A (π x) : ℝ≥0∞))
        = fun x => A.indicator (fun ω => (KacFormula.retTime f A ω : ℝ≥0∞)) (π x) := by
      funext x
      by_cases hx : π x ∈ A <;> simp [Set.indicator, hx]
    rw [hfun]
    exact hπ.lintegral_comp (hF.indicator hA)
  rw [← hstep]
  exact hbase

end Transfer

/-! ## 3. The one-sided i.i.d. bit shift: a complete concrete instance

The one-sided shift of a bit sequence is measure preserving for the product law, but it is
**neither injective nor invertible**.  Its Kac inequality nevertheless holds, and it is obtained
from the two-sided shift of `areas/kac/TwoSided.lean` through the transfer theorem above. -/

section Concrete

/-- The one-sided left shift of a bit sequence. -/
def shiftℕ : (ℕ → Bool) → (ℕ → Bool) := fun x n => x (n + 1)

theorem measurable_shiftℕ : Measurable shiftℕ := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

/-- **The one-sided shift preserves the product law** — every hypothesis of the one-sided
record setting except invertibility. -/
theorem measurePreserving_shiftℕ {ν : Measure Bool} [IsProbabilityMeasure ν] :
    MeasurePreserving shiftℕ (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  refine ⟨measurable_shiftℕ, ?_⟩
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν)
    (f := fun n : ℕ => n + 1) (fun a b hab => Nat.succ_injective (by simpa using hab))
  exact h

/-- The one-sided shift is not injective. -/
theorem shiftℕ_not_injective : ¬ Function.Injective shiftℕ := by
  intro hinj
  have hx : shiftℕ (fun _ : ℕ => true) = shiftℕ (fun n : ℕ => n ≠ 0) := by
    funext n
    simp [shiftℕ]
  have heq := hinj hx
  have h0 := congrFun heq 0
  simp at h0

/-- The restriction map from the two-sided to the one-sided bit sequence is
measure preserving. -/
theorem measurePreserving_restrict {ν : Measure Bool} [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : ℤ → Bool => fun n : ℕ => z (n : ℤ))
      (Measure.infinitePi fun _ : ℤ => ν) (Measure.infinitePi fun _ : ℕ => ν) := by
  refine ⟨measurable_pi_iff.mpr (fun n => measurable_pi_apply (n : ℤ)), ?_⟩
  have h := Measure.map_infinitePi_infinitePi_of_inj (ι := ℤ) (α := ℕ)
    (Ω := fun _ : ℤ => Bool) (P := fun _ : ℤ => ν) (f := fun n : ℕ => (n : ℤ))
    (fun a b hab => Nat.cast_injective hab)
  exact h

/-- **Kac's inequality for the one-sided i.i.d. bit shift**, proved through its invertible
two-sided extension.  This is the transfer theorem instantiated end to end: the one-sided
shift is neither injective nor invertible, and no disjointness argument is available for it
(see `tower_not_pairwiseDisjoint`). -/
theorem oneSided_kac_lintegral_le_one {ν : Measure Bool} [IsProbabilityMeasure ν]
    (A : Set (ℕ → Bool)) (hA : MeasurableSet A) :
    ∫⁻ x in A, (KacFormula.retTime shiftℕ A x : ℝ≥0∞) ∂(Measure.infinitePi fun _ : ℕ => ν)
      ≤ 1 := by
  have hcomm : ∀ z : ℤ → Bool,
      (fun n : ℕ => KacFormula.shift z (n : ℤ)) = shiftℕ (fun n : ℕ => z (n : ℤ)) := by
    intro z
    funext n
    simp [KacFormula.shift, shiftℕ]
  exact kac_lintegral_le_one_of_extension measurable_shiftℕ
    KacFormula.measurePreserving_shift measurePreserving_restrict hcomm A hA

end Concrete

/-! ## 4. The disjointness proof is not available one-sidedly

`KacFormula.kac_tsum_eq_iUnion` identifies the tail sum with the measure of
`⋃ k, θ^k '' (A ∩ {D > k})` and needs those translates to be pairwise disjoint; disjointness
comes from injectivity of `θ`.  For the one-sided shift, which is measure preserving and
non-injective, they are **not** disjoint: two tower points with different exponents meet. -/

section Tower

/-- `(shiftℕ)^[k]` reads the coordinate at distance `k`. -/
theorem shiftℕ_iterate_apply (k n : ℕ) (x : ℕ → Bool) : (shiftℕ^[k]) x n = x (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [shiftℕ]
      rw [ih]
      congr 1
      omega

/-- The return set: the bit at the origin is `true`. -/
def hitSet : Set (ℕ → Bool) := {x | x 0 = true}

theorem measurableSet_hitSet : MeasurableSet hitSet := by
  have h : hitSet = (fun x : ℕ → Bool => x 0) ⁻¹' {true} := rfl
  rw [h]
  exact (measurable_pi_apply (X := fun _ : ℕ => Bool) 0) (measurableSet_singleton true)

theorem mem_hitSet_iff (x : ℕ → Bool) : x ∈ hitSet ↔ x 0 = true := Iff.rfl

theorem shiftℕ_iterate_mem (k : ℕ) (x : ℕ → Bool) : (shiftℕ^[k]) x ∈ hitSet ↔ x k = true := by
  rw [mem_hitSet_iff, shiftℕ_iterate_apply]
  simp

/-- First tower point: bits at `0` and `2`. -/
def y₁ : ℕ → Bool := fun n => n = 0 ∨ n = 2

/-- Second tower point: bits at `0` and `3`. -/
def y₂ : ℕ → Bool := fun n => n = 0 ∨ n = 3

/-- The common tower image: the bit at `1`. -/
def z₀ : ℕ → Bool := fun n => n = 1

theorem retTime_y₁ : KacFormula.retTime shiftℕ hitSet y₁ = 2 := by
  unfold KacFormula.retTime
  have h : ∃ k : ℕ, 0 < k ∧ (shiftℕ^[k]) y₁ ∈ hitSet :=
    ⟨2, by norm_num, by rw [shiftℕ_iterate_mem]; simp [y₁]⟩
  rw [dif_pos h]
  have hfind : Nat.find h = 2 := by
    rw [Nat.find_eq_iff h]
    refine ⟨⟨by norm_num, by rw [shiftℕ_iterate_mem]; simp [y₁]⟩, ?_⟩
    intro n hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · intro hc; exact absurd hc.1 (by norm_num)
    · intro hc
      rw [shiftℕ_iterate_mem] at hc
      simp [y₁] at hc
  rw [hfind]
  norm_num

theorem retTime_y₂ : KacFormula.retTime shiftℕ hitSet y₂ = 3 := by
  unfold KacFormula.retTime
  have h : ∃ k : ℕ, 0 < k ∧ (shiftℕ^[k]) y₂ ∈ hitSet :=
    ⟨3, by norm_num, by rw [shiftℕ_iterate_mem]; simp [y₂]⟩
  rw [dif_pos h]
  have hfind : Nat.find h = 3 := by
    rw [Nat.find_eq_iff h]
    refine ⟨⟨by norm_num, by rw [shiftℕ_iterate_mem]; simp [y₂]⟩, ?_⟩
    intro n hn
    have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl
    · intro hc; exact absurd hc.1 (by norm_num)
    · intro hc
      rw [shiftℕ_iterate_mem] at hc
      simp [y₂] at hc
    · intro hc
      rw [shiftℕ_iterate_mem] at hc
      simp [y₂] at hc
  rw [hfind]
  norm_num

theorem shift_one_y₁ : (shiftℕ^[1]) y₁ = z₀ := by
  funext n
  rw [shiftℕ_iterate_apply]
  simp only [y₁, z₀]
  by_cases h : n = 1
  · subst h; norm_num
  · have h2 : n + 1 ≠ 2 := by omega
    simp [h2, h]

theorem shift_two_y₂ : (shiftℕ^[2]) y₂ = z₀ := by
  funext n
  rw [shiftℕ_iterate_apply]
  simp only [y₂, z₀]
  by_cases h : n = 1
  · subst h; norm_num
  · have h2 : n + 2 ≠ 3 := by omega
    simp [h2, h]

/-- **The two tower points collide**: `T^1 y₁ = T^2 y₂` although `y₁ ≠ y₂`, and both are
tower points (`yᵢ ∈ A ∩ {D > kᵢ}` with `k₁ = 1 < 2 = k₂`). -/
theorem tower_collision :
    (shiftℕ^[1]) y₁ = (shiftℕ^[2]) y₂ ∧ y₁ ∈ hitSet ∧ y₂ ∈ hitSet ∧
      KacFormula.retTime shiftℕ hitSet y₁ = 2 ∧
        KacFormula.retTime shiftℕ hitSet y₂ = 3 := by
  refine ⟨by rw [shift_one_y₁, shift_two_y₂], ?_, ?_, retTime_y₁, retTime_y₂⟩
  · rw [mem_hitSet_iff]; simp [y₁]
  · rw [mem_hitSet_iff]; simp [y₂]

/-- **The translated tail sets of the one-sided shift meet.** -/
theorem tower_sets_meet :
    z₀ ∈ (shiftℕ^[1]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet 1) ∧
      z₀ ∈ (shiftℕ^[2]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet 2) := by
  constructor
  · refine ⟨y₁, ⟨tower_collision.2.1, ?_⟩, shift_one_y₁⟩
    intro j hj hj1 hmem
    rw [shiftℕ_iterate_mem] at hmem
    have hj' : j = 1 := by omega
    subst hj'
    simp [y₁] at hmem
  · refine ⟨y₂, ⟨tower_collision.2.2.1, ?_⟩, shift_two_y₂⟩
    intro j hj hj2 hmem
    rw [shiftℕ_iterate_mem] at hmem
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl <;> simp [y₂] at hmem

/-- **The disjointness step cannot be run on the one-sided system.**  For the one-sided i.i.d.
bit shift — measure preserving, everywhere non-injective, not invertible — the translates
`T^k (A ∩ {D > k})` are **not** pairwise disjoint, so `KacFormula.kac_tsum_eq_iUnion` has no
one-sided analogue by disjointness.  The invertible extension in the transfer theorem is
therefore the substantive input, not a technical convenience. -/
theorem tower_not_pairwiseDisjoint :
    ¬ Pairwise (Function.onFun Disjoint
      fun k : ℕ => (shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) := by
  intro h
  have hd : Disjoint ((shiftℕ^[1]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet 1))
      ((shiftℕ^[2]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet 2)) := h (by norm_num)
  rw [Set.disjoint_left] at hd
  exact hd (a := z₀) tower_sets_meet.1 tower_sets_meet.2

end Tower


/-! ## 5. The paper's `(ED)` for a one-sided stationary system with an invertible extension

`SwarmKac.kac_path_ED` (`Swarm/KacPaperED.lean`) concludes
`1 ≤ E^*D ≤ 1/(π(F)P(V)) < ∞` from an **invertible** measure-preserving shift `e` of the
one-sided space.  That invertibility enters only through
`KacFormula.kac_cond_mean_le`.  Supplying instead the Kac bound obtained from an invertible
extension, the whole numerical chain of `Swarm/KacMean.lean` goes through verbatim for a
merely measurable one-sided map `f`.  This is the exact shape in which the record chain needs
it: `f` is the one-sided record shift, and the extension is the missing stationary version. -/

section OneSidedED

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Type*} [MeasurableSpace P]

/-- The conditioning identity `E_{P(·|A)}[D] = E^*[g]`, for a one-sided map `f`.  This is
`KacFormula.kac_conditional_mean_eq` with the invertible `e` removed: its proof never used
invertibility, only the factorisation `(factor)` and the identity `D = g ∘ Φ`. -/
theorem condMean_eq_oneSided {f : Ω → Ω} (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞)) :
    ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = ∫⁻ p, (g p : ℝ≥0∞) ∂ν := by
  have hgc : Measurable fun p => (g p : ℝ≥0∞) :=
    (show Measurable fun n : ℕ => (n : ℝ≥0∞) from by fun_prop).comp hg
  have hmap := KacFormula.map_restrict_eq_smul_of_factorization (μ := μ) Φ hΦ A hA ν hfac
  have h1 : ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A)
      = (μ A)⁻¹ * ∫⁻ ω in A, (g (Φ ω) : ℝ≥0∞) ∂μ := by
    rw [lintegral_smul_measure]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [hD ω]
    simp
  rw [h1, KacFormula.lintegral_restrict_comp Φ hΦ A ν (μ A) (fun p => (g p : ℝ≥0∞)) hgc hmap]
  have hne : μ A ≠ 0 := ne_of_gt hApos
  have hne_top : μ A ≠ ⊤ := measure_ne_top μ A
  rw [← mul_assoc, ENNReal.inv_mul_cancel hne hne_top, one_mul]

/-- `E_{P(·|A)}[D] ≤ 1/P(A)` from the Kac bound `∫_A D ≤ 1` alone.  This is where
`KacFormula.kac_cond_mean_le` uses invertibility; here the bound is the hypothesis. -/
theorem condMean_le_of_bound {f : Ω → Ω} (A : Set Ω) (hA : MeasurableSet A)
    (hbound : ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ ≤ 1) :
    ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) ≤ (μ A)⁻¹ := by
  rw [lintegral_smul_measure, smul_eq_mul]
  have hrestrict : ∫⁻ ω, (KacFormula.retTime f A ω : ℝ≥0∞) ∂(μ.restrict A)
      = ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ := rfl
  rw [hrestrict]
  calc (μ A)⁻¹ * ∫⁻ ω in A, (KacFormula.retTime f A ω : ℝ≥0∞) ∂μ
      ≤ (μ A)⁻¹ * 1 := by gcongr
    _ = (μ A)⁻¹ := mul_one _

/-- **The paper's `E^*D ≤ 1/(π(F)P(V))` for a one-sided system**: the extension supplies the
Kac bound, `(factor)` and `D = g ∘ Φ` do the rest. -/
theorem kac_path_bound_of_extension {f : Ω → Ω} (hf : Measurable f)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {g₀ : Ω' ≃ᵐ Ω'} (hg₀ : MeasurePreserving (g₀ : Ω' → Ω') μ' μ')
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ) (hcomm : ∀ x, π (g₀ x) = f (π x))
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : pf ≠ 0) (hpv : pv ≠ 0) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    ∫⁻ p, (g p : ℝ≥0∞) ∂ν ≤ (pf * pv)⁻¹ := by
  rw [← condMean_eq_oneSided Φ hΦ ν A hA hApos hfac g hg hD]
  have hbound := kac_lintegral_le_one_of_extension hf hg₀ hπ hcomm A hA
  have hle := condMean_le_of_bound (μ := μ) A hA hbound
  simpa [hmass] using hle

/-- **The paper's `(ED)`, `1 ≤ E^*D < ∞`, for a one-sided stationary system with an invertible
measure-preserving extension.**  All conclusions of `SwarmKac.kac_path_ED` hold with the
invertible map living on the extension rather than on the one-sided space. -/
theorem kac_path_ED_of_extension {f : Ω → Ω} (hf : Measurable f)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {g₀ : Ω' ≃ᵐ Ω'} (hg₀ : MeasurePreserving (g₀ : Ω' → Ω') μ' μ')
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ) (hcomm : ∀ x, π (g₀ x) = f (π x))
    (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P) [IsProbabilityMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < μ A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ p, 1 ≤ g p)
    (hD : ∀ ω, KacFormula.retTime f A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pf pv : ℝ≥0∞) (hpf : 0 < pf) (hpv : 0 < pv) (hpft : pf ≠ ⊤) (hpvt : pv ≠ ⊤)
    (hmass : μ A = pf * pv) :
    Integrable (fun p => (g p : ℝ)) ν ∧
      1 ≤ ∫ p, (g p : ℝ) ∂ν ∧
        ∫ p, (g p : ℝ) ∂ν ≤ ((pf * pv)⁻¹).toReal := by
  have hmain := kac_path_bound_of_extension hf hg₀ hπ hcomm Φ hΦ ν A hA hApos hfac g hg hD
    pf pv hpf.ne' hpv.ne' hpft hpvt hmass
  have hlt : ∫⁻ p, (g p : ℝ≥0∞) ∂ν < ⊤ :=
    lt_of_le_of_lt hmain (ENNReal.inv_lt_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne'))
  have hint : Integrable (fun p => (g p : ℝ)) ν :=
    SwarmKac.integrable_natCast_of_lintegral_ne_top hg hlt.ne
  refine ⟨hint, SwarmKac.one_le_integral_of_one_le hint hg1, ?_⟩
  rw [SwarmKac.integral_natCast_eq_toReal hg hlt.ne]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 (ENNReal.mul_pos hpf.ne' hpv.ne').ne')
    hmain

end OneSidedED

/-! ## 6. The one-sided translates do not even have small mass

The collision of §4 is not an isolated coincidence.  For the one-sided bit shift, **every**
translate `T^k (A ∩ {D > k})` with `k ≥ 1` contains the whole cylinder `{z : z 0 = false}`:
a point `z` with `z 0 = false` is the image of the tower point obtained by prepending a single
`1` and then `k` zeros.  Consequently each translate has mass at least `ν {false}`, and the
partial sums of the translate masses grow at least linearly — the one-sided analogue of the
disjointness computation of `KacFormula.kac_tsum_eq_iUnion` yields no bound at all, not merely
a false one. -/

section TranslateMass

/-- Prepend a `1` and then `k` zeros to a bit sequence. -/
def prepend (k : ℕ) (z : ℕ → Bool) : ℕ → Bool :=
  fun n => if n = 0 then true else if n ≤ k then false else z (n - k)

theorem prepend_zero (k : ℕ) (z : ℕ → Bool) : prepend k z 0 = true := by
  simp [prepend]

theorem prepend_pos_le {k j : ℕ} (z : ℕ → Bool) (hj : 0 < j) (hjk : j ≤ k) :
    prepend k z j = false := by
  simp [prepend, hj.ne', hjk]

theorem prepend_in_hitSet (k : ℕ) (z : ℕ → Bool) : prepend k z ∈ hitSet := by
  rw [mem_hitSet_iff]
  exact prepend_zero k z

theorem prepend_noReturn {k : ℕ} (hk : 1 ≤ k) (z : ℕ → Bool) :
    KacFormula.noReturn shiftℕ hitSet k (prepend k z) := by
  intro j hj hjk hmem
  rw [shiftℕ_iterate_mem] at hmem
  rw [prepend_pos_le z hj hjk] at hmem
  exact Bool.false_ne_true hmem

theorem iterate_prepend {k : ℕ} (hk : 1 ≤ k) {z : ℕ → Bool} (hz : z 0 = false) :
    (shiftℕ^[k]) (prepend k z) = z := by
  funext n
  rw [shiftℕ_iterate_apply]
  by_cases hn : n = 0
  · subst hn
    have h1 : prepend k z k = false := prepend_pos_le z (by omega) (le_refl k)
    rw [Nat.zero_add, h1]
    exact hz.symm
  · have hpos : ¬ (n + k = 0) := by omega
    have hnk : ¬ (n + k ≤ k) := by omega
    simp only [prepend, hpos, hnk, if_false]
    congr 1
    omega

/-- **Every translate sweeps the complementary cylinder.** -/
theorem falseSet_subset_translate {k : ℕ} (hk : 1 ≤ k) :
    {z : ℕ → Bool | z 0 = false}
      ⊆ (shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k) := by
  intro z hz
  exact ⟨prepend k z, ⟨prepend_in_hitSet k z, prepend_noReturn hk z⟩,
    iterate_prepend hk hz⟩

theorem measurableSet_falseSet :
    MeasurableSet {z : ℕ → Bool | z 0 = false} := by
  have h : {z : ℕ → Bool | z 0 = false} = (fun z : ℕ → Bool => z 0) ⁻¹' {false} := rfl
  rw [h]
  exact (measurable_pi_apply (X := fun _ : ℕ => Bool) 0) (measurableSet_singleton false)

/-- The mass of the complementary cylinder is `ν {false}`. -/
theorem measure_falseSet {ν : Measure Bool} [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ => ν) {z : ℕ → Bool | z 0 = false} = ν {false} := by
  have h : {z : ℕ → Bool | z 0 = false} = (fun z : ℕ → Bool => z 0) ⁻¹' {false} := rfl
  rw [h, ← Measure.map_apply (measurable_pi_apply (X := fun _ : ℕ => Bool) 0)
    (measurableSet_singleton false), Measure.infinitePi_map_eval]

/-- **Each one-sided translate has mass at least `ν {false}`.** -/
theorem measure_translate_ge {ν : Measure Bool} [IsProbabilityMeasure ν] {k : ℕ}
    (hk : 1 ≤ k) :
    ν {false} ≤ (Measure.infinitePi fun _ : ℕ => ν)
      ((shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) := by
  rw [← measure_falseSet (ν := ν)]
  exact measure_mono (falseSet_subset_translate hk)

/-- **The translate masses grow at least linearly**, so the one-sided disjointness computation
cannot produce a finite bound. -/
theorem translate_tsum_linear {ν : Measure Bool} [IsProbabilityMeasure ν] (N : ℕ) :
    (N : ℝ≥0∞) * ν {false} ≤
      ∑' k : ℕ, (Measure.infinitePi fun _ : ℕ => ν)
        ((shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      ν {false} ≤ (Measure.infinitePi fun _ : ℕ => ν)
        ((shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) :=
    fun k hk => measure_translate_ge (Finset.mem_Icc.mp hk).1
  calc (N : ℝ≥0∞) * ν {false} = ∑ _k ∈ Finset.Icc 1 N, ν {false} := by
        have hcard : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (Measure.infinitePi fun _ : ℕ => ν)
          ((shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑' k : ℕ, (Measure.infinitePi fun _ : ℕ => ν)
          ((shiftℕ^[k]) '' (hitSet ∩ KacFormula.noReturn shiftℕ hitSet k)) :=
        ENNReal.sum_le_tsum _

end TranslateMass

end SwarmM2Kac
