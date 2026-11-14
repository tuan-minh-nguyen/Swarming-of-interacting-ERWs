/-
# Kac's return-time bound by the disjoint-set argument

This file formalises a step of `main_1d_revised.tex` §3.2 (proof of
Proposition `regen`, the paragraph following `(factor)`) that converts the
stationary record chain of Proposition `front` into a **finite mean regeneration
distance**:

> "We prove the required return-time inequality directly, following the
> disjoint-set argument for Kac's formula. We claim that the sets
> `θ^k(A ∩ {D > k})`, `k ≥ 0`, are pairwise disjoint, up to `P_π`-null sets. …
> By invariance and monotone convergence,
> `∫_A D dP_π = Σ_{k≥0} P_π(A ∩ {D > k}) = P_π(∪_k θ^k(A ∩ {D > k})) ≤ 1`.
> Since the concatenated path has law `P^*` conditional on `A`, we obtain
> `E^*D = (1/P_π(A)) ∫_A D dP_π ≤ 1/(π(F)P(V)) < ∞`."

The abstract content is this.  Let `Ω` be a probability space, `θ : Ω ≃ᵐ Ω` an
invertible measure-preserving map (in the paper: the left shift on the two-sided
stationary sequence of record states and path segments), `A` a measurable set
(in the paper: `A = {Y_0 ∈ F, X_n^i > 0 for all i, n ≥ 1}`), and
`D = retTime θ A` the first positive return time to `A` (`⊤` if there is none).

Main results (`kac_tsum_le_one`, `kac_lintegral_le_one`):

* `Σ_{k≥0} μ (A ∩ {D > k}) ≤ 1`, and
* `∫_A D dμ ≤ 1`  (as a lower Lebesgue integral, `D` being `ℕ∞`-valued).

Consequences: `D < ∞` almost surely on `A` (`ae_retTime_lt_top`, i.e. Poincaré
recurrence on `A`), the real-valued bound `∫_A D dμ ≤ 1`
(`kac_integral_toReal_le_one`), and hence that the mean of `D` under the
conditioned law `(μ A)⁻¹ • μ.restrict A` is at most `1/μ(A)`
(`kac_cond_mean_le`).  With the paper's identification `μ(A) = π(F) P(V)` this is
exactly `E^*D ≤ 1/(π(F)P(V))`.

Every declaration is checked by `verify.sh` and `Audit.lean` (`#print axioms`). -/
import Swarm.Imports

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace KacFormula

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `noReturn f A k` is the set of points from which the orbit of `f` has not
returned to `A` during the first `k` steps.  It is the paper's `{D > k}`. -/
def noReturn (f : Ω → Ω) (A : Set Ω) (k : ℕ) : Set Ω :=
  {ω | ∀ j, 0 < j → j ≤ k → f^[j] ω ∉ A}

/-- The first positive return time to `A` under `f`, as an `ℕ∞`-valued function;
the value `⊤` means that the orbit never returns to `A`. -/
noncomputable def retTime (f : Ω → Ω) (A : Set Ω) (ω : Ω) : ℕ∞ :=
  if h : ∃ k : ℕ, 0 < k ∧ f^[k] ω ∈ A then (Nat.find h : ℕ∞) else ⊤

lemma noReturn_zero (f : Ω → Ω) (A : Set Ω) : noReturn f A 0 = univ := by
  ext ω
  simp only [noReturn, mem_ofPred_eq, mem_univ, iff_true]
  intro j hj hj0
  omega

lemma measurableSet_noReturn {f : Ω → Ω} (hf : Measurable f) {A : Set Ω}
    (hA : MeasurableSet A) (k : ℕ) : MeasurableSet (noReturn f A k) := by
  have h : noReturn f A k = ⋂ j ∈ Finset.Icc 1 k, (f^[j]) ⁻¹' Aᶜ := by
    ext ω
    simp only [noReturn, mem_ofPred_eq, mem_iInter, Finset.mem_Icc, mem_preimage, mem_compl_iff]
    constructor
    · intro h j hj
      exact h j hj.1 hj.2
    · intro h j hj1 hjk
      exact h j ⟨hj1, hjk⟩
  rw [h]
  exact Finset.measurableSet_biInter _ fun j _ => hA.compl.preimage (hf.iterate j)

/-- `D > k` iff there is no return during the first `k` steps. -/
lemma lt_retTime_iff {f : Ω → Ω} {A : Set Ω} {ω : Ω} {k : ℕ} :
    (k : ℕ∞) < retTime f A ω ↔ noReturn f A k ω := by
  unfold retTime noReturn
  split_ifs with h
  · constructor
    · intro hlt j hj hjk hmem
      have h1 : Nat.find h ≤ j := Nat.find_min' h ⟨hj, hmem⟩
      have h2 : k < Nat.find h := by exact_mod_cast hlt
      omega
    · intro hnr
      obtain ⟨hpos, hmem⟩ := Nat.find_spec h
      by_contra hcon
      simp only [not_lt] at hcon
      have hcon' : Nat.find h ≤ k := by exact_mod_cast hcon
      exact hnr (Nat.find h) hpos hcon' hmem
  · constructor
    · intro _ j hj _ hmem
      exact h ⟨j, hj, hmem⟩
    · intro _
      exact ENat.natCast_lt_top k

/-- The first return time is never zero. -/
lemma retTime_ne_zero {f : Ω → Ω} {A : Set Ω} {ω : Ω} : retTime f A ω ≠ 0 := by
  unfold retTime
  split_ifs with h
  · obtain ⟨hpos, -⟩ := Nat.find_spec h
    exact_mod_cast hpos.ne'
  · exact (ENat.natCast_ne_top 0).symm

/-- The level set `{D ≤ k}` is the event of a return within the first `k` steps. -/
lemma le_retTime_iff {f : Ω → Ω} {A : Set Ω} {ω : Ω} {k : ℕ} :
    retTime f A ω ≤ (k : ℕ∞) ↔ ∃ j, 0 < j ∧ j ≤ k ∧ f^[j] ω ∈ A := by
  unfold retTime
  split_ifs with h
  · rw [ENat.natCast_le_natCast, Nat.find_le_iff]
    constructor
    · rintro ⟨j, hjk, hj, hmem⟩
      exact ⟨j, hj, hjk, hmem⟩
    · rintro ⟨j, hj, hjk, hmem⟩
      exact ⟨j, hjk, hj, hmem⟩
  · constructor
    · intro hle
      exact absurd hle (not_le.mpr (ENat.natCast_lt_top k))
    · rintro ⟨j, hj, -, hmem⟩
      exact absurd ⟨j, hj, hmem⟩ h

/-- `retTime f A` is measurable for measurable `f` and `A`. -/
lemma measurable_retTime {f : Ω → Ω} (hf : Measurable f) {A : Set Ω}
    (hA : MeasurableSet A) : Measurable (retTime f A) := by
  have hle : ∀ m : ℕ, MeasurableSet (retTime f A ⁻¹' (Set.Iic (m : ℕ∞))) := by
    intro m
    have h : retTime f A ⁻¹' (Set.Iic (m : ℕ∞)) = ⋃ j ∈ Finset.Icc 1 m, (f^[j]) ⁻¹' A := by
      ext ω
      simp only [mem_preimage, mem_Iic, le_retTime_iff, mem_iUnion, Finset.mem_Icc]
      exact ⟨fun ⟨j, hj, hjm, hmem⟩ => ⟨j, ⟨hj, hjm⟩, hmem⟩,
        fun ⟨j, ⟨hj, hjm⟩, hmem⟩ => ⟨j, hj, hjm, hmem⟩⟩
    rw [h]
    exact Finset.measurableSet_biUnion _ fun j _ => hA.preimage (hf.iterate j)
  rw [ENat.measurable_iff]
  intro m
  rcases m with _ | p
  · have h : retTime f A ⁻¹' ({((0 : ℕ) : ℕ∞)} : Set ℕ∞) = ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      simpa using (retTime_ne_zero (f := f) (A := A) (ω := ω))
    rw [h]
    exact MeasurableSet.empty
  · have h : retTime f A ⁻¹' ({((p + 1 : ℕ) : ℕ∞)} : Set ℕ∞)
        = retTime f A ⁻¹' (Set.Iic ((p + 1 : ℕ) : ℕ∞))
          \ retTime f A ⁻¹' (Set.Iic (p : ℕ∞)) := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_sdiff, mem_Iic]
      constructor
      · intro h0
        refine ⟨le_of_eq h0, fun hc => ?_⟩
        rw [h0] at hc
        rw [ENat.natCast_le_natCast] at hc
        omega
      · rintro ⟨h1, h2⟩
        rcases eq_or_ne (retTime f A ω) ⊤ with ht | ht
        · rw [ht] at h1
          exact absurd h1 (not_le.mpr (ENat.natCast_lt_top (p + 1)))
        · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp ht
          have h1' : j ≤ p + 1 := by
            rw [← hj] at h1
            rwa [ENat.natCast_le_natCast] at h1
          have h2' : ¬ j ≤ p := by
            intro hc
            exact h2 (by rw [← hj]; exact_mod_cast hc)
          have : j = p + 1 := by omega
          rw [← hj, this]
    rw [h]
    exact (hle (p + 1)).diff (hle p)

/-- The layer-cake identity for `ℕ∞`-valued random variables: the total mass of the
tails is the value. -/
lemma tsum_ite_lt (n : ℕ∞) :
    (∑' k : ℕ, if (k : ℕ∞) < n then (1 : ℝ≥0∞) else 0) = (n : ℝ≥0∞) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  have hpart : ∀ N : ℕ, ∑ a ∈ Finset.range N, (if (a : ℕ∞) < n then (1 : ℝ≥0∞) else 0)
      = (((Finset.range N).filter (fun a : ℕ => (a : ℕ∞) < n)).card : ℝ≥0∞) := by
    intro N
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [hpart]
  rcases eq_or_ne n ⊤ with rfl | hn
  · have h : ∀ N : ℕ, ((Finset.range N).filter (fun a : ℕ => (a : ℕ∞) < ⊤)).card = N := by
      intro N
      have hfil : (Finset.range N).filter (fun a : ℕ => (a : ℕ∞) < ⊤) = Finset.range N :=
        Finset.filter_true_of_mem fun a _ => ENat.natCast_lt_top a
      rw [hfil, Finset.card_range]
    simp only [h, ENat.toENNReal_top]
    exact ENNReal.iSup_natCast
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hn
    have h : ∀ N : ℕ, ((Finset.range N).filter (fun a : ℕ => (a : ℕ∞) < (m : ℕ∞))).card = min N m := by
      intro N
      have hfil : (Finset.range N).filter (fun a : ℕ => (a : ℕ∞) < (m : ℕ∞)) = Finset.range (min N m) := by
        apply Finset.ext
        intro a
        simp only [Finset.mem_filter, Finset.mem_range, ENat.natCast_lt_natCast]
        omega
      rw [hfil, Finset.card_range]
    simp only [h, ENat.toENNReal_coe]
    refine le_antisymm (iSup_le fun N => ?_) (le_iSup_of_le m (by simp))
    exact_mod_cast min_le_right N m

/-- The integral of a `0/1` function with measurable support. -/
lemma lintegral_ite_one {μ : Measure Ω} {p : Ω → Prop} (hp : MeasurableSet {ω | p ω}) :
    ∫⁻ ω, (if p ω then (1 : ℝ≥0∞) else 0) ∂μ = μ {ω | p ω} := by
  have h : (fun ω => if p ω then (1 : ℝ≥0∞) else 0) = {ω | p ω}.indicator 1 := by
    funext ω
    simp only [Set.indicator, Pi.one_apply]
    by_cases hω : p ω <;> simp [hω]
  rw [h, lintegral_indicator hp]
  simp only [Pi.one_apply]
  rw [setLIntegral_const, one_mul]

section Kac

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The coercion `ℕ∞ → ℝ≥0∞` is measurable (the source carries the discrete
measurable structure). -/
lemma measurable_enat_coe : Measurable (fun x : ℕ∞ => (x : ℝ≥0∞)) := fun _ _ => trivial

/-- **The cycle decomposition of the disjoint-set argument** (paper §3.2): the total
mass of the tails `A ∩ {D > k}` equals the measure of the union of the translates
`θ^k (A ∩ {D > k})`, `k ≥ 0`.  These translates are pairwise disjoint because a
return of `θ^kω = θ^ℓω'` with `k < ℓ` forces `D(ω') ≤ ℓ - k ≤ ℓ`. -/
theorem kac_tsum_eq_iUnion (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∑' k : ℕ, μ (A ∩ noReturn (e : Ω → Ω) A k)
      = μ (⋃ k, (e : Ω → Ω)^[k] '' (A ∩ noReturn (e : Ω → Ω) A k)) := by
  set φ : Ω → Ω := (e : Ω → Ω) with hφ
  set ψ : Ω → Ω := (e.symm : Ω → Ω) with hψ
  have hφmeas : Measurable φ := e.measurable
  have hψmeas : Measurable ψ := e.symm.measurable
  have hφι : Function.Injective φ := e.injective
  have hψφ : ∀ n : ℕ, ∀ x, ψ^[n] (φ^[n] x) = x := fun n =>
    Function.LeftInverse.iterate (g := ψ) (f := φ) (fun x => e.symm_apply_apply x) n
  have hφψ : ∀ n : ℕ, ∀ x, φ^[n] (ψ^[n] x) = x := fun n =>
    Function.LeftInverse.iterate (g := φ) (f := ψ) (fun x => e.apply_symm_apply x) n
  have hψmp : MeasurePreserving ψ μ μ := by
    have h := MeasurableEquiv.measurePreserving_symm μ e
    rw [he.map_eq] at h
    exact h
  set S : ℕ → Set Ω := fun k => A ∩ noReturn φ A k with hS
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k =>
    hA.inter (measurableSet_noReturn hφmeas hA k)
  have himg : ∀ k, φ^[k] '' S k = ψ^[k] ⁻¹' S k := by
    intro k
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [show ψ^[k] (φ^[k] x) = x from hψφ k x]
    · intro hy
      exact ⟨ψ^[k] y, hy, hφψ k y⟩
  have hμU : ∀ k, μ (φ^[k] '' S k) = μ (S k) := by
    intro k
    rw [himg k]
    exact (hψmp.iterate k).measure_preimage (hSmeas k).nullMeasurableSet
  have hUmeas : ∀ k, MeasurableSet (φ^[k] '' S k) := by
    intro k
    rw [himg k]
    exact (hSmeas k).preimage (hψmeas.iterate k)
  have hdisj : Pairwise (Function.onFun Disjoint fun k => φ^[k] '' S k) := by
    intro k ℓ hkℓ
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hxk hxℓ
    obtain ⟨ω, ⟨hωA, hωn⟩, hωx⟩ := hxk
    obtain ⟨ω', ⟨hω'A, hω'n⟩, hω'x⟩ := hxℓ
    have heq : φ^[k] ω = φ^[ℓ] ω' := by rw [hωx, hω'x]
    rcases lt_or_gt_of_ne hkℓ with hk | hk
    · have hidx : φ^[k] (φ^[ℓ - k] ω') = φ^[k] ω := by
        have h1 : φ^[k] (φ^[ℓ - k] ω') = φ^[k + (ℓ - k)] ω' :=
          (Function.iterate_add_apply φ k (ℓ - k) ω').symm
        rw [h1, Nat.add_sub_cancel' hk.le, heq]
      have hback : φ^[ℓ - k] ω' = ω := Function.Injective.iterate hφι k hidx
      exact hω'n (ℓ - k) (by omega) (by omega) (hback ▸ hωA)
    · have hidx : φ^[ℓ] (φ^[k - ℓ] ω) = φ^[ℓ] ω' := by
        have h1 : φ^[ℓ] (φ^[k - ℓ] ω) = φ^[ℓ + (k - ℓ)] ω :=
          (Function.iterate_add_apply φ ℓ (k - ℓ) ω).symm
        rw [h1, Nat.add_sub_cancel' hk.le, heq]
      have hback : φ^[k - ℓ] ω = ω' := Function.Injective.iterate hφι ℓ hidx
      exact hωn (k - ℓ) (by omega) (by omega) (hback ▸ hω'A)
  have hstep : ∀ k, μ (A ∩ noReturn φ A k) = μ (φ^[k] '' S k) := by
    intro k
    rw [hS]
    exact (hμU k).symm
  calc ∑' k : ℕ, μ (A ∩ noReturn φ A k)
      = ∑' k : ℕ, μ (φ^[k] '' S k) := tsum_congr hstep
    _ = μ (⋃ k, φ^[k] '' S k) := (measure_iUnion hdisj hUmeas).symm

/-- **Kac's inequality, disjoint-set form** (paper §3.2):
`Σ_{k≥0} μ (A ∩ {D > k}) ≤ 1`. -/
theorem kac_tsum_le_one (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∑' k : ℕ, μ (A ∩ noReturn (e : Ω → Ω) A k) ≤ 1 := by
  rw [kac_tsum_eq_iUnion e he A hA]
  exact (measure_mono (subset_univ _)).trans (le_of_eq measure_univ)

/-- **Kac's formula, equality form**: if the translates `θ^k(A ∩ {D > k})` sweep out
the whole space (the "cycle decomposition" covering hypothesis), then
`∫_A D dP = 1` exactly, i.e. `E_{P(·|A)}[D] = 1/P(A)`. -/
theorem kac_tsum_eq_one_of_sweeps (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A)
    (hsweep : ⋃ k, (e : Ω → Ω)^[k] '' (A ∩ noReturn (e : Ω → Ω) A k) = univ) :
    ∑' k : ℕ, μ (A ∩ noReturn (e : Ω → Ω) A k) = 1 := by
  rw [kac_tsum_eq_iUnion e he A hA, hsweep, measure_univ]

/-- **Kac's inequality, integral form** (paper §3.2): `∫_A D dμ ≤ 1`. -/
theorem kac_lintegral_le_one (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫⁻ ω in A, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂μ ≤ 1 := by
  set D : Ω → ℕ∞ := retTime (e : Ω → Ω) A with hDdef
  have hD : Measurable D := measurable_retTime e.measurable hA
  have hkey : ∀ ω : Ω, (D ω : ℝ≥0∞)
      = ∑' k : ℕ, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) :=
    fun ω => (tsum_ite_lt (D ω)).symm
  have hmeas : ∀ k : ℕ, MeasurableSet {ω : Ω | (k : ℕ∞) < D ω} := fun k =>
    hD (show MeasurableSet (Set.Ioi (k : ℕ∞)) from trivial)
  have hrewrite : ∀ k : ℕ, {ω : Ω | (k : ℕ∞) < D ω} ∩ A = A ∩ noReturn (e : Ω → Ω) A k := by
    intro k
    ext ω
    simp only [mem_inter_iff, hDdef, lt_retTime_iff]
    tauto
  calc ∫⁻ ω in A, (D ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑' k : ℕ, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) ∂(μ.restrict A) := by
        simp only [hkey]
    _ = ∑' k : ℕ, ∫⁻ ω, (if (k : ℕ∞) < D ω then (1 : ℝ≥0∞) else 0) ∂(μ.restrict A) :=
        lintegral_tsum fun k => (measurable_const.ite (hmeas k) measurable_const).aemeasurable
    _ = ∑' k : ℕ, (μ.restrict A) {ω : Ω | (k : ℕ∞) < D ω} := by
        refine tsum_congr fun k => ?_
        exact lintegral_ite_one (hmeas k)
    _ = ∑' k : ℕ, μ (A ∩ noReturn (e : Ω → Ω) A k) := by
        refine tsum_congr fun k => ?_
        rw [Measure.restrict_apply (hmeas k), hrewrite k]
    _ ≤ 1 := kac_tsum_le_one e he A hA

/-- **Poincaré recurrence from Kac's inequality**: on `A` the return time is almost
surely finite. -/
theorem ae_retTime_lt_top (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(μ.restrict A), (retTime (e : Ω → Ω) A ω : ℝ≥0∞) < ⊤ := by
  have hD : Measurable (retTime (e : Ω → Ω) A) := measurable_retTime e.measurable hA
  refine ae_lt_top (measurable_enat_coe.comp hD) ?_
  exact ne_top_of_le_ne_top (by simp) (kac_lintegral_le_one e he A hA)

/-- **Real-valued Kac inequality**: `∫_A D dμ ≤ 1`. -/
theorem kac_integral_toReal_le_one (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω in A, (retTime (e : Ω → Ω) A ω : ℝ≥0∞).toReal ∂μ ≤ 1 := by
  have hD : Measurable (retTime (e : Ω → Ω) A) := measurable_retTime e.measurable hA
  have hint : ∫ ω in A, (retTime (e : Ω → Ω) A ω : ℝ≥0∞).toReal ∂μ
      = (∫⁻ ω in A, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂μ).toReal := by
    simpa only [Function.comp_apply] using
      integral_toReal (μ := μ.restrict A)
        (f := fun ω => (retTime (e : Ω → Ω) A ω : ℝ≥0∞))
        (measurable_enat_coe.comp hD).aemeasurable (ae_retTime_lt_top e he A hA)
  rw [hint]
  exact (ENNReal.toReal_mono (by simp) (kac_lintegral_le_one e he A hA)).trans_eq (by simp)

/-- **Kac's formula, mean form** (paper §3.2): under the law conditioned on `A`,
the mean return time is at most `1/μ(A)`.  With `μ(A) = π(F) P(V)` this is the
paper's `E^*D ≤ 1/(π(F)P(V))`. -/
theorem kac_cond_mean_le (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫⁻ ω, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂((μ A)⁻¹ • μ.restrict A) ≤ (μ A)⁻¹ := by
  rw [lintegral_smul_measure]
  calc (μ A)⁻¹ * ∫⁻ ω, (retTime (e : Ω → Ω) A ω : ℝ≥0∞) ∂(μ.restrict A)
      ≤ (μ A)⁻¹ * 1 := by
        gcongr
        exact kac_lintegral_le_one e he A hA
    _ = (μ A)⁻¹ := mul_one _

end Kac

end KacFormula
