/-
Countable i.i.d. Uniform(0,1) arrays for the strong construction of the walks.
The measure is the actual countable infinite product, not an assumption about its existence.
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory Set

namespace Swarming.Uniform

/-- Lebesgue measure restricted to `(0,1)`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Ioo 0 1)

instance uniform01_isProbabilityMeasure : IsProbabilityMeasure uniform01 := by
  apply IsProbabilityMeasure.mk
  rw [uniform01, Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

/-- A countable array indexed by walker, lattice site, and departure number. -/
abbrev Array (N : ℕ) := (Fin N × ℤ × ℕ) → ℝ

/-- The product probability measure on the array. -/
noncomputable def arrayMeasure (N : ℕ) : Measure (Array N) :=
  Measure.infinitePi (fun _ => uniform01)

instance arrayMeasure_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (arrayMeasure N) := by
  unfold arrayMeasure
  infer_instance

lemma arrayMeasure_preimage_set (N : ℕ) (c : Fin N × ℤ × ℕ) (I : Set ℝ)
    (hI : MeasurableSet I) :
    arrayMeasure N ((fun ω : Array N => ω c) ⁻¹' I) = uniform01 I := by
  have hmap : Measure.map (fun ω : Array N => ω c) (arrayMeasure N) = uniform01 :=
    Measure.infinitePi_map_eval (fun _ => uniform01) c
  calc
    arrayMeasure N ((fun ω : Array N => ω c) ⁻¹' I) =
        (Measure.map (fun ω : Array N => ω c) (arrayMeasure N)) I :=
      (Measure.map_apply (measurable_pi_apply c) hI).symm
    _ = uniform01 I := by rw [hmap]

/-- Coordinate projections are independent under the product measure. -/
theorem array_independent (N : ℕ) :
    iIndepFun (fun c (ω : Array N) => ω c) (arrayMeasure N) := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

lemma uniform01_Iio {u : ℝ} (hu1 : u ≤ 1) : uniform01 (Iio u) = ENNReal.ofReal u := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iio]
  have hset : Iio u ∩ Ioo 0 1 = Ioo 0 u := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨hxu, hx0, hx1⟩
      exact ⟨hx0, hxu⟩
    · rintro ⟨hx0, hxu⟩
      exact ⟨hxu, hx0, hxu.trans_le hu1⟩
  rw [hset, Real.volume_Ioo]
  norm_num

lemma arrayMeasure_preimage_Iio (N : ℕ) (c : Fin N × ℤ × ℕ)
    {u : ℝ} (hu1 : u ≤ 1) :
    arrayMeasure N ((fun ω : Array N => ω c) ⁻¹' Iio u) = ENNReal.ofReal u := by
  have hmap : Measure.map (fun ω : Array N => ω c) (arrayMeasure N) = uniform01 :=
    Measure.infinitePi_map_eval (fun _ => uniform01) c
  calc
    arrayMeasure N ((fun ω : Array N => ω c) ⁻¹' Iio u) =
        (Measure.map (fun ω : Array N => ω c) (arrayMeasure N)) (Iio u) :=
      (Measure.map_apply (measurable_pi_apply c) measurableSet_Iio).symm
    _ = uniform01 (Iio u) := by rw [hmap]
    _ = ENNReal.ofReal u := uniform01_Iio hu1

/-- Finite cylinders of distinct coordinates have the product of their Uniform(0,1)
probabilities.  The explicit coordinate-injection hypothesis rules out repeated coordinates. -/
theorem arrayMeasure_cylinder {N : ℕ} {c : Fin N → Fin N × ℤ × ℕ}
    (hc : Function.Injective c) {u : Fin N → ℝ} (_hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    arrayMeasure N (⋂ i, (fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) =
      ∏ i, ENNReal.ofReal (u i) := by
  have hInd : iIndepFun (fun i (ω : Array N) => ω (c i)) (arrayMeasure N) :=
    (array_independent N).precomp hc
  have h := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd (Finset.univ : Finset (Fin N))
    (sets := fun i => Iio (u i)) (fun i _ => measurableSet_Iio)
  calc
    arrayMeasure N (⋂ i, (fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) =
        ∏ i, arrayMeasure N ((fun ω : Array N => ω (c i)) ⁻¹' Iio (u i)) := by simpa using h
    _ = ∏ i, ENNReal.ofReal (u i) := by
      congr 1
      ext i
      exact arrayMeasure_preimage_Iio N (c i) (hu1 i)

/-- A singleton has zero uniform measure. -/
lemma uniform01_singleton {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : uniform01 {α} = 0 := by
  have hi : {α} ∩ Ioo 0 1 = {α} := by
    apply Set.inter_eq_left.mpr
    exact Set.singleton_subset_iff.mpr ⟨hα0, hα1⟩
  rw [uniform01, Measure.restrict_apply (measurableSet_singleton α), hi, Real.volume_singleton]

/-- Uniform law with a right-closed threshold: `P(U ≤ α) = α`. -/
lemma uniform01_Iic {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    uniform01 (Iic α) = ENNReal.ofReal α := by
  have hset : Iic α = Iio α ∪ {α} := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact lt_or_eq_of_le hx
    · intro hx
      rcases hx with hx | rfl
      · exact le_of_lt hx
      · exact le_rfl
  have hd : Disjoint (Iio α) {α} := by
    apply Set.disjoint_left.mpr
    intro x hx hxs
    simp only [Set.mem_singleton_iff] at hxs
    subst x
    exact (lt_irrefl α hx)
  calc
    uniform01 (Iic α) = uniform01 (Iio α) + uniform01 {α} := by
      rw [hset, measure_union hd (measurableSet_singleton α)]
    _ = ENNReal.ofReal α + 0 := by rw [uniform01_Iio hα1.le, uniform01_singleton hα0 hα1]
    _ = ENNReal.ofReal α := add_zero _

/-- Uniform law with a right-open threshold: `P(U > α) = 1 - α`. -/
lemma uniform01_Ioi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    uniform01 (Ioi α) = ENNReal.ofReal (1 - α) := by
  have h := prob_compl_eq_one_sub (μ := uniform01) (s := Iic α) measurableSet_Iic
  rw [← compl_Iic, h, uniform01_Iic hα0 hα1]
  simpa only [ENNReal.ofReal_one] using
    (ENNReal.ofReal_sub (p := 1) (show 0 ≤ α by linarith)).symm


end Swarming.Uniform


