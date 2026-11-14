/-
Abstract measure-theoretic core for the strong construction of the interacting
excited random walks (area (a): iid-uniform-array model and enlarged filtration).

Contents:
* `measurable_of_countable_pieces`: a function obtained by evaluating a family of
  measurable functions at a random countable-valued index is measurable.
* `indep_iInter_comp`: products of coordinate events over an injective finite
  family of coordinates of an iid family.
* `indep_fresh_finset`: an event determined by the coordinates of a finite set `S`
  is independent of the coordinates of an injective finite family avoiding `S`.
* `measure_le_of_uniform`: uniform law computation `μ {U ≤ a} = ofReal a` on `(0,1)`.
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SwarmIID

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- If `f` takes each of its values on a measurable set and each `U i` is measurable, then
`ω ↦ U (f ω) ω` is measurable. -/
theorem measurable_of_countable_pieces {ι : Type*} [Countable ι] {α : Type*} [MeasurableSpace α]
    (U : ι → Ω → α) (hU : ∀ i, Measurable (U i)) (f : Ω → ι)
    (hf : ∀ i, MeasurableSet {ω | f ω = i}) :
    Measurable fun ω => U (f ω) ω := by
  intro s hs
  have h : (fun ω => U (f ω) ω) ⁻¹' s = ⋃ i, {ω | f ω = i} ∩ U i ⁻¹' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hω => ⟨f ω, rfl, hω⟩, fun ⟨i, hi, hω⟩ => by rw [hi]; exact hω⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => (hf i).inter (hU i hs)

/-- Product formula for coordinate events along an injective finite family in an iid family. -/
theorem indep_iInter_comp {ι : Type*} [DecidableEq ι] {κ : Type*} [Fintype κ]
    {U : ι → Ω → ℝ} (hU : iIndepFun U μ) {f : κ → ι} (hf : Function.Injective f)
    (I : κ → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    μ (⋂ i, U (f i) ⁻¹' I i) = ∏ i, μ (U (f i) ⁻¹' I i) := by
  have h := hU.precomp hf
  exact h.meas_iInter (fun i => MeasurableSpace.measurableSet_comap.2 ⟨I i, hI i, rfl⟩)

/-- An event determined by the coordinates in a finite set `S` is independent of the coordinates
of an injective finite family avoiding `S`. -/
theorem indep_fresh_finset {ι : Type*} [DecidableEq ι] {κ : Type*} [Fintype κ]
    {U : ι → Ω → ℝ} (hU : iIndepFun U μ) (hmeas : ∀ i, Measurable (U i))
    {S : Finset ι} {f : κ → ι} (hf : Function.Injective f) (hS : ∀ i, f i ∉ S)
    (A : Set (S → ℝ)) (hA : MeasurableSet A) (I : κ → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    μ ((fun ω (j : S) => U j ω) ⁻¹' A ∩ ⋂ i, U (f i) ⁻¹' I i)
      = μ ((fun ω (j : S) => U j ω) ⁻¹' A) * ∏ i, μ (U (f i) ⁻¹' I i) := by
  classical
  set T : Finset ι := Finset.univ.image f with hT
  have hmem : ∀ i : κ, f i ∈ T := by
    intro i
    rw [hT]
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a haS haT
    rw [hT] at haT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 haT
    exact hS i haS
  set C : Set (T → ℝ) := {g | ∀ i : κ, g ⟨f i, hmem i⟩ ∈ I i} with hC
  have hCmeas : MeasurableSet C := by
    have h1 : ∀ i : κ, MeasurableSet {g : T → ℝ | g ⟨f i, hmem i⟩ ∈ I i} := fun i =>
      (hI i).preimage (measurable_pi_apply (⟨f i, hmem i⟩ : T))
    have : C = ⋂ i : κ, {g : T → ℝ | g ⟨f i, hmem i⟩ ∈ I i} := by
      ext g
      simp [hC]
    rw [this]
    exact MeasurableSet.iInter h1
  have hind := hU.indepFun_finset S T hdisj hmeas
  have hmain := hind.meas_inter
    (s := (fun ω (j : S) => U j ω) ⁻¹' A) (t := (fun ω (j : T) => U j ω) ⁻¹' C)
    (MeasurableSpace.measurableSet_comap.2 ⟨A, hA, rfl⟩)
    (MeasurableSpace.measurableSet_comap.2 ⟨C, hCmeas, rfl⟩)
  have hTeq : (fun ω (j : T) => U j ω) ⁻¹' C = ⋂ i, U (f i) ⁻¹' I i := by
    ext ω
    simp [hC]
  have hprod : μ (⋂ i, U (f i) ⁻¹' I i) = ∏ i, μ (U (f i) ⁻¹' I i) :=
    indep_iInter_comp hU hf I hI
  rw [hTeq] at hmain
  rw [hprod] at hmain
  exact hmain

/-- A random variable with law the uniform distribution on `(0,1)` has
`μ {ω | U ω < a} = ofReal a` for `a ≤ 1`. -/
theorem measure_lt_of_uniform {U : Ω → ℝ} (hmeas : Measurable U)
    (hlaw : μ.map U = volume.restrict (Set.Ioo (0 : ℝ) 1)) {a : ℝ}
    (ha1 : a ≤ 1) :
    μ {ω | U ω < a} = ENNReal.ofReal a := by
  have hm : MeasurableSet (Set.Iio a) := measurableSet_Iio
  change μ (U ⁻¹' Set.Iio a) = ENNReal.ofReal a
  rw [← Measure.map_apply hmeas hm, hlaw, Measure.restrict_apply hm, Set.inter_comm]
  have hset : Set.Ioo (0 : ℝ) 1 ∩ Set.Iio a = Set.Ioo (0 : ℝ) a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩
      exact ⟨⟨h0, lt_of_lt_of_le h2 ha1⟩, h2⟩
  rw [hset, Real.volume_Ioo, sub_zero]

end SwarmIID
