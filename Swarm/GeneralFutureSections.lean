/-
Pointwise measured-section recursions for general enriched futures.

The accepted `GeneralEnrichedFuture` module expands the terminal record of a
finite window. Here the same exact `partialTraj` kernel is split after any
observed prefix, leaving an arbitrary measurable section at a later horizon.
No array/chain equality, independence, stationarity, or raw-word simplification
is assumed.
-/
import Swarm.GeneralEnrichedFuture

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmGeneralFuture

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The successor finite-prefix kernel is the actual `pairK`, with the old prefix
inserted deterministically by `prefixSnoc`. -/
theorem partialTraj_succ_apply_pairK (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {r : ℕ}
    (v : SwarmFinFuture.Prefix (N := N) (m := m) r)
    {E : Set (SwarmFinFuture.Prefix (N := N) (m := m) (r + 1))}
    (hE : MeasurableSet E) :
    (Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
        (SwarmInfSeg.homK (N := N) (m := m) p hm) r (r + 1) v) E =
      (SwarmSegKernel.pairK (N := N) (m := m) p hm
        (v ⟨r, Finset.mem_Iic.2 le_rfl⟩))
        {a | SwarmFinFuture.prefixSnoc v a ∈ E} := by
  letI : ∀ n, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm n) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply' _
    (f := IicProdIoc (X := fun _ => SwarmInfSeg.Pair N m) r (r + 1))
    measurable_IicProdIoc v hE]
  rw [Kernel.id_prod_apply' _ _ (hE.preimage measurable_IicProdIoc)]
  have hset : MeasurableSet (Prod.mk v ⁻¹'
      IicProdIoc (X := fun _ => SwarmInfSeg.Pair N m) r (r + 1) ⁻¹' E) :=
    hE.preimage (measurable_IicProdIoc.comp (measurable_const.prodMk measurable_id))
  rw [Kernel.map_apply' (SwarmInfSeg.homK (N := N) (m := m) p hm r)
    (f := MeasurableEquiv.piSingleton (X := fun _ => SwarmInfSeg.Pair N m) r)
    (MeasurableEquiv.measurable _) v hset]
  rw [SwarmInfSeg.homK, Kernel.comap_apply]
  congr 1
  ext a
  change IicProdIoc (X := fun _ => SwarmInfSeg.Pair N m) r (r + 1)
      (v, (MeasurableEquiv.piSingleton (X := fun _ => SwarmInfSeg.Pair N m) r) a) ∈ E ↔
    SwarmFinFuture.prefixSnoc v a ∈ E
  have hfun : IicProdIoc (X := fun _ => SwarmInfSeg.Pair N m) r (r + 1)
      (v, (MeasurableEquiv.piSingleton (X := fun _ => SwarmInfSeg.Pair N m) r) a) =
    SwarmFinFuture.prefixSnoc v a := by
    funext i
    by_cases hi : (i : ℕ) ≤ r
    · simp [IicProdIoc_def, hi, SwarmFinFuture.prefixSnoc]
    · have hir : (i : ℕ) = r + 1 := by
        have := Finset.mem_Iic.1 i.2
        omega
      simp [IicProdIoc_def, hir, SwarmFinFuture.prefixSnoc,
        MeasurableEquiv.piSingleton]
  rw [hfun]

/-- Integration against the atomic enriched one-record law, with no restriction
on the measurable integrand. -/

theorem lintegral_asegK_weighted (p : ℝ) (hm : 1 ≤ m)
    (y : SwarmRec.RecState N m) {F : SwarmInfSeg.Pair N m → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ a, F a ∂(SwarmSegKernel.asegK (N := N) p hm y) =
      ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
          F (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) := by
  rw [SwarmSegKernel.asegK, lintegral_sum_measure]
  exact tsum_congr fun pq => by
    rw [lintegral_smul_measure, lintegral_dirac' _ hF]
    rfl

/-- **General weighted successor section.**  After an arbitrary observed prefix,
the one-step finite-future kernel is the sum over every duration and word.  The
integrand may read the complete enlarged prefix; no raw-time/record-time
identification or future independence is used. -/
theorem partialTraj_succ_lintegral_hitW (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {r : ℕ}
    (v : SwarmFinFuture.Prefix (N := N) (m := m) r)
    {F : SwarmFinFuture.Prefix (N := N) (m := m) (r + 1) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ w, F w ∂(Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
        (SwarmInfSeg.homK (N := N) (m := m) p hm) r (r + 1) v) =
      ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
        ENNReal.ofReal (RecKernel.hitW p pq.2
          (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2) * F (prefixNext p hm v pq) := by
  letI : ∀ n, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm n) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  have hsnoc : Measurable (fun a : SwarmInfSeg.Pair N m =>
      SwarmFinFuture.prefixSnoc v a) :=
    SwarmFinFuture.measurable_prefixSnoc.comp (measurable_const.prodMk measurable_id)
  have hmap : (Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
        (SwarmInfSeg.homK (N := N) (m := m) p hm) r (r + 1) v) =
      (SwarmSegKernel.pairK (N := N) (m := m) p hm
        (v ⟨r, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun a => SwarmFinFuture.prefixSnoc v a) := by
    ext E hE
    rw [Measure.map_apply hsnoc hE]
    exact partialTraj_succ_apply_pairK p hm hp hp1 v hE
  rw [hmap, lintegral_map hF hsnoc, SwarmSegKernel.pairK_apply,
    lintegral_asegK_weighted p hm _
      (F := fun a => F (SwarmFinFuture.prefixSnoc v a)) (hF.comp hsnoc)]
  exact tsum_congr fun pq => rfl

/-- A finite trajectory at a strict cut is the integral of its later section
against the one-step prefix law.  This generic form avoids unfolding any
model-specific record data. -/
theorem partialTraj_apply_eq_integral_succ {X : ℕ → Type*}
    [∀ i, MeasurableSpace (X i)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {r n : ℕ} (hrn : r < n)
    (v : Π i : Finset.Iic r, X i) {E : Set (Π i : Finset.Iic n, X i)}
    (hE : MeasurableSet E) :
    (Kernel.partialTraj κ r n v) E = ∫⁻ w,
      (Kernel.partialTraj κ (r + 1) n w) E ∂(Kernel.partialTraj κ r (r + 1) v) := by
  rw [← Kernel.partialTraj_comp_partialTraj (Nat.le_succ r) (Nat.succ_le_of_lt hrn),
    Kernel.comp_apply' _ _ _ hE]

/-- **Arbitrary raw window after an arbitrary enriched prefix.**  Expanding one
further record leaves a `hitW`-weighted sum of the genuine remaining
`partialTraj` section.  Thus `K`, `C`, the initial law, and the complete observed
prefix are retained, while `r < n` keeps the later enriched future explicit. -/
theorem chainLaw_window_eq_hitW_partialTraj (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {K r n : ℕ} (hK : K ≤ n) (hrn : r < n)
    {C : Set (Fin (n + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π)
        (SwarmFinFuture.chainWindow K n C) =
      ∫⁻ v : SwarmFinFuture.Prefix (N := N) (m := m) r,
        (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
          ENNReal.ofReal (RecKernel.hitW p pq.2
            (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2) *
            (Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
              (SwarmInfSeg.homK (N := N) (m := m) p hm) (r + 1) n
              (prefixNext p hm v pq)) (SwarmFinFuture.prefixWindow K n C))
        ∂((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) := by
  letI : ∀ n, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm n) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  rw [chainLaw_window_eq_partialTraj p hm hp hp1 π hK (Nat.le_of_lt hrn) hC]
  refine lintegral_congr fun v => ?_
  rw [partialTraj_apply_eq_integral_succ (X := fun _ => SwarmInfSeg.Pair N m)
    (SwarmInfSeg.homK (N := N) (m := m) p hm) hrn v
    (SwarmFinFuture.measurableSet_prefixWindow hC)]
  exact partialTraj_succ_lintegral_hitW p hm hp hp1 v
    (Kernel.measurable_coe _ (SwarmFinFuture.measurableSet_prefixWindow hC))

end SwarmGeneralFuture
