/-
# The `n = 0` half of the finite-horizon residual `(★ 0)` for the canonical enriched chain

`FinHorizonHstruct.lean` proves that `hstruct` follows from the finite-horizon family `(★ K)`.
Here the `K = 0` member is *proved* for the canonical chain of `InfSeg.lean`:
`chainLaw (infLaw pairLaw π)`, i.e. the enriched Ionescu–Tulcea trajectory assembled into
`SwarmConcat.Chain`, with the arbitrary probability `π` on record states.  At `K = 0` the event
`finStrict 0` is exactly `X 0 ≡ 0`, the `Y_0 ∈ F` half of `strictPos`, so `(★ 0)` reads

  `μ (Φ ⁻¹' (X 0 ≡ 0)) = π(F) · 1 = π(F)`.

The proof is the model's own start-set computation: every atom of the enriched step `asegK y`
has a segment starting at the record state's own position array (`segOf_p_zero`), those positions
vanish exactly on `F = srSet` (`segOf_p_zero_srSet` and `ofRecState_pos`), and the atom weights
sum to one (`tsum_hitW`).  Nothing about invariance of `π` is used, and no other member of the
family is claimed.
-/
import Swarm.FinHorizonHstruct
import Swarm.InfSegCompat

open MeasureTheory Set
open scoped ENNReal
open SimJump
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec SwarmFresh SwarmFreshPos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFinHorizon

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The set of enriched states whose segment starts at the all-zero position array: the ambient
form of `X 0 ≡ 0`. -/
def SegStartZero (N m : ℕ) : Set (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  {a | ∀ i, a.1.p 0 i = 0}

theorem measurableSet_segStartZero (N m : ℕ) : MeasurableSet (SegStartZero N m) := by
  have h : SegStartZero N m
      = ⋂ i, {a : SwarmConcat.Seg N × SwarmRec.RecState N m | a.1.p 0 i = 0} := by
    ext a
    simp [SegStartZero]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_eq_fun
    ((SwarmConcat.measurable_seg_p (N := N) 0 i).comp measurable_fst) measurable_const

/-- **The one-step start computation.**  From a record state `y` the enriched step starts at the
all-zero array exactly when `y ∈ F`, and then carries all of its mass there. -/
theorem segStartZero_mass (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : RecState N m) :
    SwarmSegKernel.asegK p hm y (SegStartZero N m) = if y ∈ srSet N m then 1 else 0 := by
  classical
  rw [SwarmSegKernel.asegK_apply p hm y (measurableSet_segStartZero N m)]
  by_cases hy : y ∈ srSet N m
  · rw [if_pos hy]
    have hterm : ∀ pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
            (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y)
                ∈ SegStartZero N m then 1 else 0)
          = ENNReal.ofReal (RecKernel.hitW p pq.2 y) := by
      intro pq
      have hmem : (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y)
          ∈ SegStartZero N m :=
        fun i => SwarmSegKernel.segOf_p_zero_srSet hy pq.1 pq.2 i
      rw [if_pos hmem, mul_one]
    simp only [hterm]
    exact SwarmDHStruct.tsum_hitW p hm hp hp1 y
  · rw [if_neg hy]
    have hterm : ∀ pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
            (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y)
                ∈ SegStartZero N m then 1 else 0) = 0 := by
      intro pq
      rw [if_neg, mul_zero]
      intro hmem
      apply hy
      intro i
      have h := hmem i
      rw [SwarmSegKernel.segOf_p_zero, SwarmSegKernel.ofRecState_pos] at h
      have hz : (y.val.1 i : ℕ) = 0 := by omega
      show y.val.1 i ≤ 0
      omega
    simp only [hterm, tsum_zero]

/-- The same computation, read at the level of the first coordinate's law. -/
theorem infLaw_segStartZero_mass (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] :
    SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π
        {A | (A 0).1 ∈ {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}}
      = π (srSet N m) := by
  classical
  have hmeas : MeasurableSet {a : SwarmInfSeg.Pair N m | a.1 ∈
      {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}} := by
    have h : {a : SwarmInfSeg.Pair N m | a.1 ∈
        {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}} = SegStartZero N m := rfl
    rw [h]
    exact measurableSet_segStartZero N m
  rw [show {A : ℕ → SwarmInfSeg.Pair N m | (A 0).1 ∈
        {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}}
      = (fun x : ℕ → SwarmInfSeg.Pair N m => x 0) ⁻¹'
          {a : SwarmInfSeg.Pair N m | a.1 ∈
            {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}} from rfl,
    ← Measure.map_apply (measurable_pi_apply 0) hmeas,
    SwarmInfSeg.map_eval_zero p hm hp hp1 π,
    SwarmSegKernel.pairLaw, Measure.bind_apply hmeas
      (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm).aemeasurable]
  have hcongr : ∀ y : RecState N m,
      SwarmSegKernel.asegK p hm y {a : SwarmInfSeg.Pair N m | a.1 ∈
        {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}} = if y ∈ srSet N m then 1 else 0 :=
    fun y => segStartZero_mass p hm hp hp1 y
  rw [lintegral_congr hcongr]
  have h5 : ∫⁻ y, (if y ∈ srSet N m then (1 : ℝ≥0∞) else 0) ∂π = π (srSet N m) := by
    have h : (fun y : RecState N m => if y ∈ srSet N m then (1 : ℝ≥0∞) else 0)
        = (srSet N m).indicator (fun _ => 1) := rfl
    rw [h, lintegral_indicator (μ := π) (SwarmRec.measurableSet_srSet N m) (fun _ => 1),
      setLIntegral_const]
    simp
  exact h5

/-- **`(★ 0)` for the canonical chain.**  With `Φ c = fun n i => c.X n i` the concatenated path of
the assembled chain, the mass of `Φ ⁻¹' (finStrict 0)` — i.e. of the `Y_0 ∈ F` half of `hstruct` —
is `π(F) · P(finStrict 0) = π(F)`, for an arbitrary probability `π` on record states. -/
theorem chainLaw_infLaw_finStrict_zero (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] :
    SwarmChainAssemble.chainLaw (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
        {c : SwarmConcat.Chain N |
          (fun n i => c.X n i) ∈ finStrict (N := N) 0}
      = π (srSet N m) *
          (arrayMeasure N) {U : Array N | posPath p m U ∈ finStrict (N := N) 0} := by
  classical
  have hX0 : ∀ (c : SwarmConcat.Chain N) (i : Fin N), c.X 0 i = (c.seg 0).p 0 i := by
    intro c i
    have h := SwarmConcat.Chain.X_record c 0 i
    rw [SwarmConcat.Chain.cum_zero] at h
    simpa using h
  have hset : {c : SwarmConcat.Chain N | (fun n i => c.X n i) ∈ finStrict (N := N) 0}
      = {c | ∀ i, (c.seg 0).p 0 i = 0} := by
    ext c
    rw [mem_ofPred_eq, mem_finStrict]
    constructor
    · rintro ⟨h0, -⟩ i
      rw [← hX0 c i]
      exact h0 i
    · intro h0
      exact ⟨fun i => by rw [hX0 c i]; exact h0 i,
        fun n hn h0n _ => absurd h0n (by omega)⟩
  have hmeas : MeasurableSet {c : SwarmConcat.Chain N | ∀ i, (c.seg 0).p 0 i = 0} := by
    have h : {c : SwarmConcat.Chain N | ∀ i, (c.seg 0).p 0 i = 0}
        = ⋂ i, {c : SwarmConcat.Chain N | (c.seg 0).p 0 i = 0} := by
      ext c
      simp
    rw [h]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun
      (SwarmConcat.measurable_chain_p 0 0 i) measurable_const
  have hEq : (SwarmChainAssemble.chainOf ⁻¹'
        {c : SwarmConcat.Chain N | ∀ i, (c.seg 0).p 0 i = 0})
      =ᵐ[SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π]
      {A | (A 0).1 ∈ {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0}} := by
    filter_upwards [SwarmInfSeg.trajCompat_ae p hm hp hp1 π] with A hA
    show (SwarmChainAssemble.chainOf A ∈ {c : SwarmConcat.Chain N | ∀ i, (c.seg 0).p 0 i = 0})
      = ((A 0).1 ∈ {s : SwarmConcat.Seg N | ∀ i, s.p 0 i = 0})
    rw [mem_ofPred_eq, mem_ofPred_eq, SwarmChainAssemble.chainOf_seg_of_compat hA 0]
  rw [hset, SwarmChainAssemble.chainLaw_apply _ hmeas,
    measure_congr (μ := SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) hEq,
    infLaw_segStartZero_mass p hm hp hp1 π, arrayMass_finStrict_zero, mul_one]

end SwarmFinHorizon
