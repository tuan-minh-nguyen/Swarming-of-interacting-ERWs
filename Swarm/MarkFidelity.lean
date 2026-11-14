/-
  **Fidelity of the site-mark model.**

  The paper's drives the dynamics with an i.i.d. uniform array `U^j(x,k)`,
  `1 ≤ j ≤ N`, `x ∈ ℤ`, `k ≥ 1`, and defines the site marks

      B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p},      omega_j(x) = 1/2 + (p-1/2) B_j(x).

  This file proves that this construction produces exactly the objects used in
  `MarkProcess.lean`/`MarkMoments.lean`:

  * `blockMeasure_map_markB`: for one site, the law of the mark `U ↦ 1{∀k, U k > p}`
    under the uniform block law on `(0,1)^{m-1}` is Bernoulli`((1-p)^{m-1})`;
  * `uniformArray_map_marks`: consequently the site marks of the uniform array are i.i.d.
    Bernoulli`((1-p)^{m-1})`, i.e. their joint law is `markMeasure (boolMeasure q)`;
  * `hof_paper_recursion`: the process `hof` of `MarkMoments.lean` satisfies the paper's
    Poisson recursion `h(x) = (1 + (1 - omega(x)) h(x-1))/omega(x)` with
    `omega(x) = 1/2 + (p-1/2) B(x)`, so it is the paper's `h_j`.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### The uniform block law and the law of one mark -/

/-- The law of the `m-1` uniform coordinates governing the departures of a walker from one site. -/
def blockMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioo (0:ℝ) 1))

lemma isProbabilityMeasure_restrict_Ioo :
    IsProbabilityMeasure (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  constructor
  simp [Real.volume_Ioo]

lemma isProbabilityMeasure_blockMeasure (k : ℕ) : IsProbabilityMeasure (blockMeasure k) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  unfold blockMeasure
  infer_instance

/-- The site mark of one block of uniforms: `1` iff all `m-1` uniforms exceed `p`. -/
def markB (k : ℕ) (p : ℝ) (u : Fin k → ℝ) : Bool := decide (∀ i, p < u i)

lemma markB_preimage_true (k : ℕ) (p : ℝ) :
    (markB k p) ⁻¹' {true} = {u : Fin k → ℝ | ∀ i, p < u i} := by
  ext u; simp [markB]

lemma markB_preimage_false (k : ℕ) (p : ℝ) :
    (markB k p) ⁻¹' {false} = {u : Fin k → ℝ | ∀ i, p < u i}ᶜ := by
  ext u; simp [markB]

lemma measurableSet_markB (k : ℕ) (p : ℝ) :
    MeasurableSet {u : Fin k → ℝ | ∀ i, p < u i} := by
  have hset : {u : Fin k → ℝ | ∀ i, p < u i} = ⋂ i, {u : Fin k → ℝ | p < u i} := by
    ext u; simp
  rw [hset]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

lemma measurable_markB (k : ℕ) (p : ℝ) : Measurable (markB k p) := by
  apply measurable_to_countable
  intro y
  by_cases hy : ∀ i, p < y i
  · have hyv : markB k p y = true := by simp [markB, hy]
    rw [hyv, markB_preimage_true k p]
    exact measurableSet_markB k p
  · have hyv : markB k p y = false := by simp [markB, hy]
    rw [hyv, markB_preimage_false k p]
    exact (measurableSet_markB k p).compl

/-- **The mark of one site**: the uniform block gives the site's mark with probability
`(1-p)^k` (here `k = m-1`). -/
lemma blockMeasure_markB_measure {k : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    blockMeasure k {u : Fin k → ℝ | ∀ i, p < u i} = ENNReal.ofReal ((1 - p) ^ k) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  haveI : IsProbabilityMeasure (blockMeasure k) := isProbabilityMeasure_blockMeasure k
  -- the box `(0,1)^k` carries full mass
  have hB : blockMeasure k (Set.univ.pi (fun _ => Set.Ioo (0:ℝ) 1)) = 1 := by
    rw [blockMeasure, Measure.pi_pi (fun _ : Fin k => volume.restrict (Set.Ioo (0:ℝ) 1))
      (fun _ => Set.Ioo (0:ℝ) 1)]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_self, Real.volume_Ioo]
    norm_num
  have hBm : MeasurableSet (Set.univ.pi (fun _ : Fin k => Set.Ioo (0:ℝ) 1)) :=
    MeasurableSet.univ_pi (fun i => measurableSet_Ioo)
  have hBc : blockMeasure k (Set.univ.pi (fun _ : Fin k => Set.Ioo (0:ℝ) 1))ᶜ = 0 := by
    rw [measure_compl hBm (measure_ne_top _ _), hB, measure_univ]
    simp
  have hSe : {u : Fin k → ℝ | ∀ i, p < u i} ∩ Set.univ.pi (fun _ => Set.Ioo (0:ℝ) 1)
      = Set.univ.pi (fun _ => Set.Ioo p 1) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Ioo]
    exact ⟨fun h i => ⟨h.1 i, (h.2 i).2⟩,
      fun h => ⟨fun i => (h i).1, fun i => ⟨lt_trans hp0 (h i).1, (h i).2⟩⟩⟩
  have hsplit := measure_inter_add_sdiff (μ := blockMeasure k)
    (s := {u : Fin k → ℝ | ∀ i, p < u i}) hBm
  have hzero : blockMeasure k ({u : Fin k → ℝ | ∀ i, p < u i}
      \ Set.univ.pi (fun _ => Set.Ioo (0:ℝ) 1)) = 0 :=
    measure_mono_null (Set.diff_subset_compl _ _) hBc
  rw [hSe] at hsplit
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  rw [blockMeasure, Measure.pi_pi (fun _ : Fin k => volume.restrict (Set.Ioo (0:ℝ) 1))
    (fun _ => Set.Ioo p 1)]
  have hfac : ∀ i : Fin k, volume.restrict (Set.Ioo (0:ℝ) 1) (Set.Ioo p 1)
      = ENNReal.ofReal (1 - p) := by
    intro i
    rw [Measure.restrict_apply measurableSet_Ioo,
      show Set.Ioo p 1 ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo p 1 by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioo]
        exact ⟨fun h => h.1, fun h => ⟨h, ⟨lt_trans hp0 h.1, h.2⟩⟩⟩, Real.volume_Ioo]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 - p)]

/-- Every set of `Bool` is measurable, so a measure on `Bool` is determined by the masses of
`{true}` and `{false}`. -/
lemma measure_bool_eq {μ ν : Measure Bool} (ht : μ {true} = ν {true})
    (hf : μ {false} = ν {false}) : μ = ν := by
  ext s _
  have hcases : s = ∅ ∨ s = {true} ∨ s = {false} ∨ s = Set.univ := by
    by_cases h1 : true ∈ s <;> by_cases h2 : false ∈ s
    · exact Or.inr (Or.inr (Or.inr (by ext b; cases b <;> simp_all)))
    · exact Or.inr (Or.inl (by ext b; cases b <;> simp_all))
    · exact Or.inr (Or.inr (Or.inl (by ext b; cases b <;> simp_all)))
    · exact Or.inl (by ext b; cases b <;> simp_all)
  rcases hcases with rfl | rfl | rfl | rfl
  · simp
  · rw [ht]
  · rw [hf]
  · have h1 : μ Set.univ = μ {true} + μ {false} := by
      rw [show (Set.univ : Set Bool) = {true} ∪ {false} by ext b; cases b <;> simp,
        measure_union (by simp) (measurableSet_singleton _)]
    have h2 : ν Set.univ = ν {true} + ν {false} := by
      rw [show (Set.univ : Set Bool) = {true} ∪ {false} by ext b; cases b <;> simp,
        measure_union (by simp) (measurableSet_singleton _)]
    rw [h1, h2, ht, hf]

/-- **The law of one site mark** is Bernoulli`((1-p)^k)`. -/
theorem blockMeasure_map_markB {k : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (blockMeasure k).map (markB k p) = boolMeasure ((1 - p) ^ k) := by
  haveI := isProbabilityMeasure_restrict_Ioo
  haveI : IsProbabilityMeasure (blockMeasure k) := isProbabilityMeasure_blockMeasure k
  have hq0 : (0:ℝ) ≤ (1 - p) ^ k := by positivity
  have hq1 : (1 - p) ^ k ≤ 1 := by
    have h0 : (0:ℝ) ≤ 1 - p := by linarith
    have h1 : 1 - p ≤ 1 := by linarith
    exact pow_le_one₀ h0 h1
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ k)) :=
    isProbabilityMeasure_boolMeasure hq0 hq1
  refine measure_bool_eq ?_ ?_
  · rw [Measure.map_apply (measurable_markB k p) (measurableSet_singleton true),
      markB_preimage_true, blockMeasure_markB_measure hp0 hp1, boolMeasure_true]
  · rw [Measure.map_apply (measurable_markB k p) (measurableSet_singleton false),
      markB_preimage_false, measure_compl (measurableSet_markB k p)
      (measure_ne_top _ _), blockMeasure_markB_measure hp0 hp1, measure_univ,
      boolMeasure_false, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0]

/-- **The site marks of the paper's uniform array are i.i.d. Bernoulli`((1-p)^{m-1})`.** -/
theorem uniformArray_map_marks {m : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (Measure.infinitePi (fun _ : ℕ => blockMeasure (m - 1))).map
        (fun (ω : ℕ → Fin (m - 1) → ℝ) (x : ℕ) => markB (m - 1) p (ω x))
      = markMeasure (boolMeasure ((1 - p) ^ (m - 1))) := by
  haveI : IsProbabilityMeasure (blockMeasure (m - 1)) := isProbabilityMeasure_blockMeasure _
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => blockMeasure (m - 1))
    (f := fun _ (u : Fin (m - 1) → ℝ) => markB (m - 1) p u)
    (fun _ => measurable_markB _ _)
  rw [h]
  simp only [blockMeasure_map_markB hp0 hp1]
  rfl

/-! ### The paper's Poisson recursion -/

/-- `hof` satisfies the paper's recursion `h(x) = (1 + (1 - omega(x)) h(x-1))/omega(x)` with the
two-valued weight `omega(x) = 1/2 + (p - 1/2) B(x)`. -/
theorem hof_paper_recursion {p : ℝ} (hp0 : p ≠ 0) (hp2 : p ≠ 1/2) (ω : ℕ → Bool) (n : ℕ) :
    hof p ω (n + 1)
      = (1 + (1 - (if ω (n + 1) then p else 1/2)) * hof p ω n)
        / (if ω (n + 1) then p else 1/2) := by
  rw [hof_succ]
  cases hb : ω (n + 1)
  · simp only [hb, if_false, Bool.false_eq_true, hstep_false]
    field_simp
    ring
  · simp only [hb, if_true, hstep_true]
    field_simp

end

end SwarmMarks
