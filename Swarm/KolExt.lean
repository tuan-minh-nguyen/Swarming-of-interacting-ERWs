/-
# Kolmogorov extension for countable products of compact metrizable factors

Mathlib has the projective family / projective limit interfaces
(`MeasureTheory.IsProjectiveMeasureFamily`, `MeasureTheory.IsProjectiveLimit`,
`MeasureTheory.IsProjectiveLimit.unique`) and the additive content of the
cylinders (`MeasureTheory.projectiveFamilyContent`), but not the existence
of the projective limit (its own documentation says that Kolmogorov's extension
theorem and Ionescu-Tulcea for arbitrary index sets are not yet in Mathlib).

This file proves existence for a countable index set when every factor carries
a compact second-countable (T2) topology whose Borel σ-algebra is the given
one.  The argument is the weak-compactness one:

* the space of probability measures on a compact space is compact
  (`MeasureTheory.instCompactSpaceProbabilityMeasure`), so the filter
  `atTop.map (fun I => (P I).map windowEmb)` has a cluster point `ν`;
* for a finite `J`, the set of probability measures whose `J`-marginal is
  `P J` is closed, and it is eventually true of the window measures by
  projectivity;
* hence `ν.map J.restrict = P J` for every finite `J`, i.e. `ν` is a
  projective limit.

No portmanteau / regularity argument is needed: pushforward by a continuous map
is continuous on probability measures, and a cluster point against an
eventually-constant filter is unique in a T2 space.

`exists_unique_isProjectiveLimit` adds uniqueness (Mathlib's
`IsProjectiveLimit.unique`).

The `stationary` section specialises to a constant factor space indexed by `ℤ`
and proves that a **shift-stationary** projective family (the formal content of
"the stopped-record window laws come from a stationary process") has a
**shift-invariant** projective limit.  That supplies the measure-preserving
invertible system, together with its one-sided factor, which the Kac step of the
regeneration argument consumes (`Swarm/M2KacExt.lean`).
-/
import Swarm.Imports
import Mathlib.Topology.Metrizable.Urysohn

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace SwarmKol

section basic

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, Nonempty (α i)]

/-- The projection `Π i, α i → Π i : I, α i` is measurable. -/
theorem measurable_finsetRestrict (I : Finset ι) :
    Measurable (I.restrict : (Π i, α i) → (Π i : I, α i)) := by
  apply measurable_pi_lambda
  intro j
  simpa only [Finset.restrict_def] using measurable_pi_apply (j : ι)

/-- Extend a window `Π j : I, α j` to the full product by an arbitrary value off `I`. -/
noncomputable def windowEmb (I : Finset ι) : (Π j : I, α j) → (Π i, α i) := by
  classical
  exact fun y i => if h : i ∈ I then y ⟨i, h⟩ else Classical.arbitrary (α i)

theorem measurable_windowEmb (I : Finset ι) : Measurable (windowEmb (α := α) I) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases h : i ∈ I
  · have hfun : (fun y => windowEmb (α := α) I y i) = fun y => y ⟨i, h⟩ := by
      funext y; simp only [windowEmb, dif_pos h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun y => windowEmb (α := α) I y i) = fun _ => Classical.arbitrary (α i) := by
      funext y; simp only [windowEmb, dif_neg h]
    rw [hfun]
    exact measurable_const

/-- Restricting a window extension to a sub-window is the canonical projection. -/
theorem restrict_windowEmb (I J : Finset ι) (hJI : J ⊆ I) :
    (J.restrict : (Π i, α i) → (Π j : J, α j)) ∘ windowEmb (α := α) I
      = Finset.restrict₂ hJI := by
  classical
  funext y j
  simp only [Function.comp_apply, windowEmb, Finset.restrict_def, Finset.restrict₂_def,
    dif_pos (hJI j.2)]

variable {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

/-- The `J`-marginal of the window extension of `P I` is `P J` when `J ⊆ I`. -/
theorem map_windowEmb_restrict (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) (hJI : J ⊆ I) :
    ((P I).map (windowEmb (α := α) I)).map (J.restrict) = P J := by
  have hcomp : ((P I).map (windowEmb (α := α) I)).map (J.restrict)
      = (P I).map (Finset.restrict₂ hJI) := by
    rw [Measure.map_map (measurable_finsetRestrict (α := α) J)
      (measurable_windowEmb (α := α) I), restrict_windowEmb (α := α) I J hJI]
  rw [hcomp, hP I J hJI]

end basic

section topology

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)]

/-- The projection `Π i, α i → Π i : I, α i` is continuous. -/
theorem continuous_finsetRestrict (I : Finset ι) :
    Continuous (I.restrict : (Π i, α i) → (Π i : I, α i)) := by
  apply continuous_pi
  intro j
  simpa only [Finset.restrict_def] using continuous_apply (j : ι)

end topology

section main

variable {ι : Type*} [Countable ι]
variable {α : ι → Type*} [∀ i, TopologicalSpace (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, T2Space (α i)] [∀ i, CompactSpace (α i)] [∀ i, SecondCountableTopology (α i)]
  [∀ i, BorelSpace (α i)] [∀ i, Nonempty (α i)]
variable {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

/-- **Kolmogorov extension, countable index, compact metrizable factors.** -/
theorem exists_isProjectiveLimit (hP : IsProjectiveMeasureFamily P)
    (hprob : ∀ J, IsProbabilityMeasure (P J)) :
    ∃ μ : Measure (Π i, α i), IsProjectiveLimit μ P := by
  classical
  obtain ⟨ν, -, hν⟩ := IsCompact.exists_mapClusterPt
    (u := fun I : Finset ι => (⟨(P I).map (windowEmb (α := α) I),
      Measure.isProbabilityMeasure_map (measurable_windowEmb (α := α) I).aemeasurable⟩ :
        ProbabilityMeasure (Π i, α i)))
    (f := (atTop : Filter (Finset ι)))
    (isCompact_univ (X := ProbabilityMeasure (Π i, α i))) (by simp)
  refine ⟨(ν : Measure (Π i, α i)), fun J => ?_⟩
  -- the set of probability measures with the correct `J`-marginal is closed
  set gJ : ProbabilityMeasure (Π i, α i) → ProbabilityMeasure (Π j : J, α j) :=
    fun μ => ProbabilityMeasure.map μ
      (measurable_finsetRestrict (α := α) J).aemeasurable with hgJ
  have hcont : Continuous gJ :=
    ProbabilityMeasure.continuous_map (continuous_finsetRestrict (α := α) J)
  have hclosed : IsClosed {μ : ProbabilityMeasure (Π i, α i) | gJ μ = ⟨P J, hprob J⟩} :=
    isClosed_eq hcont continuous_const
  have heventually : ∀ᶠ I in (atTop : Filter (Finset ι)),
      (⟨(P I).map (windowEmb (α := α) I),
        Measure.isProbabilityMeasure_map
          (measurable_windowEmb (α := α) I).aemeasurable⟩ : ProbabilityMeasure (Π i, α i))
        ∈ {μ : ProbabilityMeasure (Π i, α i) | gJ μ = ⟨P J, hprob J⟩} := by
    filter_upwards [Filter.eventually_atTop.2 ⟨J, fun I hI => hI⟩] with I hI
    refine ProbabilityMeasure.toMeasure_injective ?_
    simp only [hgJ, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
    exact map_windowEmb_restrict hP I J hI
  have hmem := hclosed.mem_of_mapClusterPt hν heventually
  have hcon := congrArg (fun μ : ProbabilityMeasure (Π j : J, α j) =>
    (μ : Measure (Π j : J, α j))) hmem
  simpa only [hgJ, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk] using hcon

/-- **Uniqueness form:** the projective limit exists and is unique. -/
theorem exists_unique_isProjectiveLimit (hP : IsProjectiveMeasureFamily P)
    (hprob : ∀ J, IsProbabilityMeasure (P J)) :
    ∃ μ : Measure (Π i, α i), IsProjectiveLimit μ P ∧ ∀ ν, IsProjectiveLimit ν P → ν = μ := by
  obtain ⟨μ, hμ⟩ := exists_isProjectiveLimit hP hprob
  exact ⟨μ, hμ, fun ν hν => IsProjectiveLimit.unique hν hμ⟩

end main

/-! ### The stationary two-sided extension -/

section stationary

variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [T2Space β] [CompactSpace β]
  [SecondCountableTopology β] [BorelSpace β] [Nonempty β]

/-- The shift of a bi-infinite path by `k` places to the left: `pathShift k x i = x (i - k)`. -/
def pathShift (k : ℤ) : (ℤ → β) → (ℤ → β) := fun x i => x (i - k)

theorem measurable_pathShift (k : ℤ) : Measurable (pathShift (β := β) k) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (i - k)

theorem pathShift_comp_neg (k : ℤ) :
    (pathShift (β := β) (-k)) ∘ (pathShift (β := β) k) = id := by
  funext x i
  simp only [Function.comp_apply, pathShift, id]
  congr 1
  omega

theorem pathShift_comp_neg' (k : ℤ) :
    (pathShift (β := β) k) ∘ (pathShift (β := β) (-k)) = id := by
  funext x i
  simp only [Function.comp_apply, pathShift, id]
  congr 1
  omega

/-- The shift of the two-sided path space as a measurable equivalence. -/
noncomputable def pathShiftEquiv (k : ℤ) : (ℤ → β) ≃ᵐ (ℤ → β) where
  toFun := pathShift k
  invFun := pathShift (-k)
  left_inv x := congrFun (pathShift_comp_neg (β := β) k) x
  right_inv x := congrFun (pathShift_comp_neg' (β := β) k) x
  measurable_toFun := measurable_pathShift k
  measurable_invFun := measurable_pathShift (-k)

theorem sub_mem_of_mem_image {k j : ℤ} {I : Finset ℤ}
    (hj : j ∈ I.image (fun i => i + k)) : j - k ∈ I := by
  classical
  rw [Finset.mem_image] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  simpa using hi

/-- Reindex a window law on `I` to the shifted window `I + k`. -/
def winReindex (k : ℤ) (I : Finset ℤ) :
    (Π j : I, β) → (Π j : I.image (fun i => i + k), β) := by
  classical
  exact fun y j => y ⟨j.1 - k, sub_mem_of_mem_image j.2⟩

theorem measurable_winReindex (k : ℤ) (I : Finset ℤ) :
    Measurable (winReindex (β := β) k I) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply _

/-- The restricted shift is the window reindexing. -/
theorem restrict_comp_pathShift (k : ℤ) (I : Finset ℤ) :
    ((I.image (fun i => i + k)).restrict :
        (ℤ → β) → (Π j : I.image (fun i => i + k), β))
      ∘ pathShift (β := β) k = (winReindex (β := β) k I) ∘ (I.restrict) := by
  classical
  funext x j
  rfl

variable {P : ∀ J : Finset ℤ, Measure (Π j : J, β)}

/-- **Stationarity of the two-sided extension.**  A shift-stationary projective family of
window laws (the formal content of "the window laws of a stationary process") has a
shift-invariant projective limit.  Together with `exists_isProjectiveLimit` this produces the
invertible measure-preserving two-sided system. -/
theorem map_pathShift_eq (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => β) P)
    (hprob : ∀ J, IsProbabilityMeasure (P J))
    (hstat : ∀ (k : ℤ) (I : Finset ℤ),
      P (I.image (fun i => i + k)) = (P I).map (winReindex (β := β) k I))
    {ν : Measure (ℤ → β)} (hν : IsProjectiveLimit (α := fun _ : ℤ => β) ν P) (k : ℤ) :
    ν.map (pathShift (β := β) k) = ν := by
  classical
  have hfin : ∀ J, IsFiniteMeasure (P J) := fun J => ⟨by
    rw [(hprob J).measure_univ]; exact ENNReal.one_lt_top⟩
  haveI := hfin
  refine IsProjectiveLimit.unique (α := fun _ : ℤ => β) (P := P) (fun I => ?_) hν
  -- reparametrise the index set as a shifted window
  have hI' : (I.image (fun i => i + (-k))).image (fun i => i + k) = I := by
    ext j
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      simpa using hb
    · intro hj
      exact ⟨j + (-k), ⟨j, hj, rfl⟩, by omega⟩
  rw [← hI']
  rw [Measure.map_map (measurable_finsetRestrict (α := fun _ : ℤ => β) _)
    (measurable_pathShift k), restrict_comp_pathShift]
  rw [← Measure.map_map (measurable_winReindex k _)
    (measurable_finsetRestrict (α := fun _ : ℤ => β) _), hν _, hstat k _]

/-- **The stationary two-sided extension exists.** -/
theorem exists_stationary_isProjectiveLimit
    (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => β) P)
    (hprob : ∀ J, IsProbabilityMeasure (P J))
    (hstat : ∀ (k : ℤ) (I : Finset ℤ),
      P (I.image (fun i => i + k)) = (P I).map (winReindex (β := β) k I)) :
    ∃ ν : Measure (ℤ → β), IsProjectiveLimit (α := fun _ : ℤ => β) ν P ∧
      IsProbabilityMeasure ν ∧ ∀ k : ℤ, ν.map (pathShift (β := β) k) = ν := by
  obtain ⟨ν, hν⟩ := exists_isProjectiveLimit (α := fun _ : ℤ => β) hP hprob
  exact ⟨ν, hν, hν.isProbabilityMeasure, fun k => map_pathShift_eq hP hprob hstat hν k⟩

end stationary

end SwarmKol
