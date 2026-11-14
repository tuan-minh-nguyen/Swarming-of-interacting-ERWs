/-
The conditional law of the next step in the enlarged filtration of the actual
interacting trajectory: the paper's §2.1 display

  "conditionally on `𝓕_n`, the coordinates `U^i(X_n^i, L_n^i(X_n^i))` are independent
   uniform on `(0,1)`"

for the actual `Swarming.Trajectory.trajectory` on the concrete i.i.d.-uniform array.

`enl_fresh_law` is the unconditional form of that statement: for **every** event
`G` of the enlarged filtration `enlFilt p m n` and every family of measurable boxes
`I i`,

  `μ (G ∩ {U (departureCoord n i) ∈ I i  ∀ i}) = (∏ i, |I i|) * μ G`.

No independence of the future array from the past is assumed: it is derived from the
i.i.d. structure of the array and the fact that the coordinates read at time `n` are
*fresh* (not in `prefRead n γ`).

The per-piece form `enl_fresh_law_piece` is the same statement with `G` restricted to
one prefix `γ` (`prefAgree p m γ ∩ B`), and is the shape used when the thresholds are
state-dependent.

There is no proof hole and no custom axiom in this file.
-/
import Swarm.Imports
import Swarm.UniformArray
import Swarm.Trajectory
import Swarm.FreshIndependence
import Swarm.EnlFilt

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- The coordinate read by walker `i` at time `n`, as a function of the position prefix
`γ` up to time `n`. -/
noncomputable def fr (n : ℕ) (γ : Pref N n) (i : Fin N) : Fin N × ℤ × ℕ :=
  (i, ext γ n i, localTime (fun s => ext γ s i) n (ext γ n i))

lemma fr_injective (n : ℕ) (γ : Pref N n) : Function.Injective (fr (N := N) n γ) := by
  intro i j h
  have h1 := congrArg (fun c : Fin N × ℤ × ℕ => c.1) h
  simpa [fr] using h1

/-- The coordinate read at time `n` is **fresh**: it has not been read before. -/
lemma fr_notMem_prefRead (n : ℕ) (γ : Pref N n) (i : Fin N) :
    fr (N := N) n γ i ∉ prefRead n γ := by
  rw [fr, mem_prefRead]
  rintro ⟨t, ht, hx, hk⟩
  -- the read at time `t < n` at site `X_t = X_n` has a strictly smaller visit number
  have hlt : localTime (fun s => ext γ s i) t (ext γ n i)
      < localTime (fun s => ext γ s i) n (ext γ n i) := by
    refine Swarming.Trajectory.localTime_lt_of_visit (X := fun s => ext γ s i) ht ?_
    rfl
  omega

/-- A set measurable in the revealed coordinates of a prefix is ambient measurable. -/
lemma measurableSet_of_cyl {n : ℕ} {γ : Pref N n} {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B) : MeasurableSet B := by
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  rw [← hBeq]
  exact hBs.preimage (measurable_pi_lambda _ fun c =>
    measurable_pi_apply (X := fun _ : Fin N × ℤ × ℕ => ℝ) (a := (c : Fin N × ℤ × ℕ)))

/-- The value read at time `n` by walker `i` is a measurable function of the array. -/
lemma measurable_value_read (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Measurable fun U : Array N => U (departureCoord p m U n i) :=
  Swarming.Fair.measurable_value_at_departure (i := i)
    ((Swarming.Fair.measurable_trajectory p m n).1 i) (Swarming.Fair.measurable_trajectory p m n).2

/-- On the piece `{path = γ}` the coordinate read at time `n` is `fr n γ i`. -/
lemma departureCoord_of_prefAgree (p : ℝ) (m : ℕ) {n : ℕ} {γ : Pref N n} {U : Array N}
    (hU : U ∈ prefAgree p m γ) (i : Fin N) :
    departureCoord p m U n i = fr (N := N) n γ i := by
  rw [departCoord_eq, fr]
  have hpos : ext γ n i = (trajectory p m U n).pos i := ext_prefOf_of_mem hU le_rfl i
  have hell : localTime (fun s => ext γ s i) n (ext γ n i)
      = (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
    rw [Swarming.Trajectory.ell_eq_localTime, hpos]
    exact localTime_congr (X := fun s => ext γ s i)
      (Y := fun s => (trajectory p m U s).pos i) (n := n)
      (fun s hs => ext_prefOf_of_mem hU hs i)
  rw [hpos, ← hell, hpos]

/-- **The paper's §2.1 display on one piece of the enlarged filtration**: given that the
path follows `γ` and an event of the revealed coordinates before time `n`, the
coordinates read at time `n` are independent uniform. -/
theorem enl_fresh_law_piece (p : ℝ) (m : ℕ) (n : ℕ) (γ : Pref N n) {B : Set (Array N)}
    (hB : MeasurableSet[cylAt (N := N) (prefRead n γ)] B)
    (I : Fin N → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (prefAgree p m γ ∩ B ∩ ⋂ i, {U : Array N | U (fr (N := N) n γ i) ∈ I i}) =
      (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B) := by
  classical
  obtain ⟨Bs, hBs, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hB
  set A : Set (prefRead n γ → ℝ) :=
    {g : prefRead n γ → ℝ | ∀ t : Fin (n + 1),
        (trajectory p m (extendArr g) t.1).pos = γ t} ∩ Bs with hA
  have hAmeas : MeasurableSet A :=
    (measurableSet_prefRead_preimage p m γ).inter hBs
  have hbase : prefAgree p m γ ∩ B =
      (fun U (c : prefRead n γ) => U c) ⁻¹' A := by
    rw [← hBeq]
    ext U
    rw [prefAgree_preimage p m γ]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hA]
  have hpre : (fun U (c : prefRead n γ) => U c) ⁻¹' A ⊆ prefAgree p m γ := by
    rw [prefAgree_preimage p m γ]
    apply Set.preimage_mono
    intro g hg
    exact hg.1
  have hfull : prefAgree p m γ ∩ B ∩
      ⋂ i, {U : Array N | U (fr (N := N) n γ i) ∈ I i} =
      (fun U (c : prefRead n γ) => U c) ⁻¹' A ∩
        ⋂ i, (fun U : Array N => U (fr (N := N) n γ i)) ⁻¹' I i := by
    rw [hbase]
    ext U
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage]
  have hind := SwarmIID.indep_fresh_finset (μ := arrayMeasure N) (array_independent N)
    (fun c => measurable_pi_apply c) (fr_injective n γ) (fr_notMem_prefRead n γ) A hAmeas I hI
  have hprod : ∀ i, arrayMeasure N ((fun U : Array N => U (fr (N := N) n γ i)) ⁻¹' I i)
      = uniform01 (I i) := fun i => arrayMeasure_preimage_set N (fr (N := N) n γ i) (I i) (hI i)
  rw [hfull, hind, hbase]
  simp only [hprod]
  rw [mul_comm]

/-- **The conditional law of the next step in the enlarged filtration** (the paper's §2.1
display, unconditional form): for every event `G` of `𝓕_n` and every family of measurable
boxes, the coordinates read at time `n` are independent uniform over `G`. -/
theorem enl_fresh_law (p : ℝ) (m : ℕ) (n : ℕ) (G : Set (Array N))
    (hG : MeasurableSet[enlMeas p m n] G) (I : Fin N → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    arrayMeasure N (G ∩ ⋂ i, {U : Array N | U (departureCoord p m U n i) ∈ I i}) =
      (∏ i, uniform01 (I i)) * arrayMeasure N G := by
  classical
  choose B hB hEq using hG
  set C : Set (Array N) := ⋂ i, {U : Array N | U (departureCoord p m U n i) ∈ I i} with hC
  -- on each piece the fresh boxes are the boxes in `fr n γ`
  have hpiece : ∀ γ : Pref N n,
      arrayMeasure N (prefAgree p m γ ∩ (B γ ∩ C)) =
        (∏ i, uniform01 (I i)) * arrayMeasure N (prefAgree p m γ ∩ B γ) := by
    intro γ
    have hset : prefAgree p m γ ∩ (B γ ∩ C) =
        prefAgree p m γ ∩ B γ ∩ ⋂ i, {U : Array N | U (fr (N := N) n γ i) ∈ I i} := by
      ext U
      simp only [hC, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun i => by
          rw [← departureCoord_of_prefAgree p m h1 i]; exact h3 i⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun i => by
          rw [departureCoord_of_prefAgree p m h1 i]; exact h3 i⟩
    rw [hset]
    exact enl_fresh_law_piece p m n γ (hB γ) I hI
  -- the pieces partition `G ∩ C`
  have hGunion : G = ⋃ γ : Pref N n, (prefAgree p m γ ∩ B γ) := by
    ext U
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨prefOf p m n U, prefAgree_prefOf U, ?_⟩
      have h3 : U ∈ prefAgree p m (prefOf p m n U) ∩ G := ⟨prefAgree_prefOf U, h⟩
      rw [hEq (prefOf p m n U)] at h3
      exact h3.2
    · rintro ⟨γ, h1, h2⟩
      have h3 : U ∈ prefAgree p m γ ∩ G := by rw [hEq γ]; exact ⟨h1, h2⟩
      exact h3.2
  have hpart : G ∩ C = ⋃ γ : Pref N n, (prefAgree p m γ ∩ (B γ ∩ C)) := by
    rw [hGunion]
    rw [Set.iUnion_inter]
    congr 1
    funext γ
    exact Set.inter_assoc _ _ _
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun γ : Pref N n => prefAgree p m γ ∩ (B γ ∩ C))) := by
    intro γ γ' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by
      funext t
      rw [← h1 t, ← h2 t])
  have hC' : MeasurableSet C := by
    refine MeasurableSet.iInter fun i => ?_
    exact (hI i).preimage (measurable_value_read p m n i)
  have hmeas : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ (B γ ∩ C)) :=
    fun γ => (measurableSet_prefAgree_ambient p m γ).inter
      ((measurableSet_of_cyl (hB γ)).inter hC')
  rw [hpart, measure_iUnion hdisj hmeas]
  simp only [hpiece]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hdisjB : Pairwise (Function.onFun Disjoint (fun γ : Pref N n => prefAgree p m γ ∩ B γ)) := by
    intro γ γ' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro U ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (by funext t; rw [← h1 t, ← h2 t])
  have hmeasB : ∀ γ : Pref N n, MeasurableSet (prefAgree p m γ ∩ B γ) :=
    fun γ => (measurableSet_prefAgree_ambient p m γ).inter (measurableSet_of_cyl (hB γ))
  rw [hGunion, measure_iUnion hdisjB hmeasB]

end Swarming.Enl
