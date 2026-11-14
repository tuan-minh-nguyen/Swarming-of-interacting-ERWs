/-
Finite initial-law transport for the actual enriched record chain.

The raw uniform array has the fixed `startState`; it has no record-law parameter.
The arbitrary record law `π` enters instead through `pairLaw π = π.bind asegK`,
which is the initial law of `infLaw π`.  This module supplies the missing finite
reindexing glue between that trajectory and `chainVec`, without stationarity,
future independence, or any StandardBorelSpace instance.
-/
import Swarm.GeneralEnrichedFuture

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmInitialTransport

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Reindex a vector of length `n+1` by the finite interval `Iic n`. -/
def finToPrefix {β : Type*} {n : ℕ} (v : Fin (n + 1) → β) :
    (Π _i : Finset.Iic n, β) :=
  fun i => v ⟨i, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- The inverse reindexing from `Iic n` to `Fin (n+1)`. -/
def prefixToFin {β : Type*} {n : ℕ} (v : Π _i : Finset.Iic n, β) :
    Fin (n + 1) → β :=
  fun j => v ⟨j, Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.2)⟩

theorem measurable_finToPrefix {β : Type*} [MeasurableSpace β] {n : ℕ} :
    Measurable (finToPrefix (β := β) (n := n)) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply _

theorem measurable_prefixToFin {β : Type*} [MeasurableSpace β] {n : ℕ} :
    Measurable (prefixToFin (β := β) (n := n)) := by
  exact measurable_pi_lambda _ fun j => measurable_pi_apply _

/-- The two finite indexations are measurably equivalent. -/
noncomputable def finPrefixEquiv {β : Type*} [MeasurableSpace β] (n : ℕ) :
    (Fin (n + 1) → β) ≃ᵐ (Π _i : Finset.Iic n, β) where
  toFun := finToPrefix
  invFun := prefixToFin
  left_inv v := by
    funext j
    rfl
  right_inv v := by
    funext i
    rfl
  measurable_toFun := measurable_finToPrefix
  measurable_invFun := measurable_prefixToFin

@[simp] theorem finPrefixEquiv_apply {β : Type*} [MeasurableSpace β] {n : ℕ}
    (v : Fin (n + 1) → β) : finPrefixEquiv n v = finToPrefix v := rfl

@[simp] theorem finPrefixEquiv_symm_apply {β : Type*} [MeasurableSpace β] {n : ℕ}
    (v : Π _i : Finset.Iic n, β) : (finPrefixEquiv n).symm v = prefixToFin v := rfl

/-- `finToPrefix` inserts an atom as the constant length-one record. -/
theorem finToPrefix_const_one {β : Type*} [MeasurableSpace β] (a : β) :
    finToPrefix (fun _ : Fin 1 => a) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => β)).symm a := by
  funext i
  have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
    Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2))
  subst hi
  rfl

/-- The zeroth finite marginal is exactly the one-vector chain law, on the
nose after the canonical reindexing. -/
theorem infLaw_prefix_zero_eq_chainVec (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) 0)) =
      (SwarmChain.chainVec (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) 1).map finToPrefix := by
  letI hKall : ∀ n, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm n) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  letI hpair : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    SwarmInfSeg.isProbabilityMeasure_pairLaw p hm hp hp1 π
  have h := SwarmGeneralFuture.trajMeasure_map_frestrictLe_eq_comp
    (SwarmInfSeg.homK (N := N) (m := m) p hm)
    (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) 0
  change ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) 0)) = _ at h
  rw [h, Kernel.partialTraj_self, Measure.id_comp]
  rw [SwarmChain.chainVec_succ, SwarmChain.chainStep_zero,
    Measure.map_map measurable_finToPrefix SwarmChain.measurable_fin1_const]
  congr 1


/-- Reindexing the last vector coordinate gives the last `Iic` coordinate. -/
@[simp] theorem finToPrefix_last {β : Type*} {n : ℕ} (v : Fin (n + 1) → β) :
    finToPrefix v ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = v (Fin.last n) := rfl

/-- The two append operations agree under finite reindexing. -/
theorem finToPrefix_snoc {n : ℕ} (v : Fin (n + 1) → SwarmInfSeg.Pair N m)
    (a : SwarmInfSeg.Pair N m) :
    finToPrefix (SwarmChain.snocF v a) =
      SwarmFinFuture.prefixSnoc (finToPrefix v) a := by
  funext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [finToPrefix, SwarmFinFuture.prefixSnoc, SwarmChain.snocF, hi,
      Nat.lt_succ_of_le hi]
  · have hi' : (i : ℕ) = n + 1 := by
      have htop := Finset.mem_Iic.mp i.2
      omega
    simp [finToPrefix, SwarmFinFuture.prefixSnoc, SwarmChain.snocF, hi']

/-- **Finite trajectory/`chainVec` glue.**  Every finite marginal of the actual
Ionescu--Tulcea trajectory is the corresponding finite Markov-chain vector law,
with no stationarity or invariance assumption on the initial record law. -/
theorem infLaw_prefix_eq_chainVec (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n)) =
      (SwarmChain.chainVec (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)).map finToPrefix := by
  letI hK : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  letI hpair : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    SwarmInfSeg.isProbabilityMeasure_pairLaw p hm hp hp1 π
  induction n with
  | zero => exact infLaw_prefix_zero_eq_chainVec p hm hp hp1 π
  | succ n ih =>
      ext E hE
      have hEvec : MeasurableSet (finToPrefix ⁻¹' E) := hE.preimage measurable_finToPrefix
      have hEpair : MeasurableSet {q : SwarmFinFuture.Prefix (N := N) (m := m) n ×
          SwarmInfSeg.Pair N m | SwarmFinFuture.prefixSnoc q.1 q.2 ∈ E} :=
        hE.preimage SwarmFinFuture.measurable_prefixSnoc
      have hF : Measurable (fun v : SwarmFinFuture.Prefix (N := N) (m := m) n =>
          (SwarmSegKernel.pairK (N := N) (m := m) p hm
            (v ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
            {a | SwarmFinFuture.prefixSnoc v a ∈ E}) := by
        let κlast : Kernel (SwarmFinFuture.Prefix (N := N) (m := m) n)
            (SwarmInfSeg.Pair N m) :=
          (SwarmSegKernel.pairK (N := N) (m := m) p hm).comap
            (fun v => v ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)
        have hm := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
          (κ := κlast) hEpair
        exact hm
      rw [SwarmFinFuture.infLaw_prefix_succ_apply p hm hp hp1 π hE]
      rw [Measure.map_apply measurable_finToPrefix hE,
        SwarmChain.chainVec_succ_succ, Measure.map_apply SwarmChain.measurable_snocF hEvec,
        Measure.compProd_apply (SwarmChain.measurable_snocF hEvec)]
      rw [ih, lintegral_map hF measurable_finToPrefix]
      apply lintegral_congr
      intro v
      rw [SwarmChain.lastK_apply]
      change (SwarmSegKernel.pairK (N := N) (m := m) p hm (v (Fin.last n)))
          {a | SwarmFinFuture.prefixSnoc (finToPrefix v) a ∈ E} =
        (SwarmSegKernel.pairK (N := N) (m := m) p hm (v (Fin.last n)))
          {a | finToPrefix (SwarmChain.snocF v a) ∈ E}
      congr 1
      ext a
      change SwarmFinFuture.prefixSnoc (finToPrefix v) a ∈ E ↔
        finToPrefix (SwarmChain.snocF v a) ∈ E
      rw [finToPrefix_snoc]


/-- Reindexing twice in opposite directions cancels on measures. -/
theorem map_prefixToFin_map_finToPrefix {β : Type*} [MeasurableSpace β] {n : ℕ}
    (μ : Measure (Fin (n + 1) → β)) :
    (μ.map finToPrefix).map prefixToFin = μ := by
  rw [Measure.map_map measurable_prefixToFin measurable_finToPrefix]
  have hfun : (prefixToFin ∘ finToPrefix) = (id : (Fin (n + 1) → β) → _) := by
    funext v
    exact (finPrefixEquiv n).left_inv v
  rw [hfun, Measure.map_id]

/-- The finite chain vector law is the initial atom followed by the exact
`partialTraj` future, with the finite index sets identified. -/
theorem chainVec_eq_trajMap (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    SwarmChain.chainVec (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1) =
      ((Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
        (SwarmInfSeg.homK (N := N) (m := m) p hm) 0 n).map prefixToFin) ∘ₘ
        (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
          (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 => SwarmInfSeg.Pair N m)).symm := by
  letI hKall : ∀ n, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm n) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  letI hpair : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    SwarmInfSeg.isProbabilityMeasure_pairLaw p hm hp hp1 π
  have hglue := infLaw_prefix_eq_chainVec p hm hp hp1 π n
  have hmapped := congrArg
    (fun μ : Measure (SwarmFinFuture.Prefix (N := N) (m := m) n) =>
      μ.map prefixToFin) hglue
  rw [map_prefixToFin_map_finToPrefix] at hmapped
  have htraj := SwarmGeneralFuture.trajMeasure_map_frestrictLe_eq_comp
    (SwarmInfSeg.homK (N := N) (m := m) p hm)
    (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) n
  change ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n)) = _ at htraj
  have hleft :
      (((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n)).map prefixToFin) =
      ((Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
        (SwarmInfSeg.homK (N := N) (m := m) p hm) 0 n).map prefixToFin) ∘ₘ
        (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
          (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 => SwarmInfSeg.Pair N m)).symm := by
    rw [htraj, Measure.map_comp _ _ measurable_prefixToFin]
  exact hmapped.symm.trans hleft

/-- The enriched one-record initialisation as a genuine measurable kernel into
`Iic 0` prefixes. -/
noncomputable def recordStartKernel (p : ℝ) (hm : 1 ≤ m) :
    Kernel (SwarmRec.RecState N m) (SwarmFinFuture.Prefix (N := N) (m := m) 0) :=
  (Kernel.mk (SwarmSegKernel.asegK (N := N) (m := m) p hm)
    (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm)).map
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => SwarmInfSeg.Pair N m)).symm

theorem recordStartKernel_apply (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    recordStartKernel p hm y = (SwarmSegKernel.asegK (N := N) (m := m) p hm y).map
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => SwarmInfSeg.Pair N m)).symm := by
  exact Kernel.map_apply _ (MeasurableEquiv.measurable _) y

/-- The exact finite future from a record state, including its first enriched
atom and all subsequent actual `pairK` transitions. -/
noncomputable def initialFiniteKernel (p : ℝ) (hm : 1 ≤ m) (n : ℕ) :
    Kernel (SwarmRec.RecState N m) (Fin (n + 1) → SwarmInfSeg.Pair N m) :=
  ((Kernel.partialTraj (X := fun _ => SwarmInfSeg.Pair N m)
    (SwarmInfSeg.homK (N := N) (m := m) p hm) 0 n).map prefixToFin) ∘ₖ
      recordStartKernel p hm

/-- A Dirac record-state law has the expected one-record enriched law. -/
theorem pairLaw_dirac (p : ℝ) (hm : 1 ≤ m) (y : SwarmRec.RecState N m) :
    SwarmSegKernel.pairLaw (N := N) (m := m) p hm (Measure.dirac y) =
      SwarmSegKernel.asegK (N := N) (m := m) p hm y := by
  exact Measure.dirac_bind (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm) y

/-- The explicit initialization/future kernel is exactly the Dirac-start
`chainVec` used by the finite raw-prefix calculations. -/
theorem initialFiniteKernel_apply (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : SwarmRec.RecState N m) (n : ℕ) :
    initialFiniteKernel p hm n y =
      SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1) := by
  letI : IsProbabilityMeasure (Measure.dirac y) := inferInstance
  have h := chainVec_eq_trajMap p hm hp hp1 (Measure.dirac y) n
  rw [pairLaw_dirac] at h
  unfold initialFiniteKernel
  rw [Kernel.comp_apply, recordStartKernel_apply]
  exact h.symm

/-- **Arbitrary-`π` measure transport.**  Mixing the record-state law before
constructing the enriched chain is exactly integrating the explicit finite
initialization/future kernel. -/
theorem chainVec_pairLaw_eq_bind (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ) :
    SwarmChain.chainVec (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1) =
      π.bind (initialFiniteKernel p hm n) := by
  rw [chainVec_eq_trajMap p hm hp hp1 π n]
  have hstart :
      (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map
          (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 => SwarmInfSeg.Pair N m)).symm =
        (recordStartKernel p hm) ∘ₘ π := by
    ext E hE
    rw [Measure.map_apply (MeasurableEquiv.measurable _) hE,
      SwarmSegKernel.pairLaw,
      Measure.bind_apply ((MeasurableEquiv.measurable _) hE)
        (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm).aemeasurable,
      Measure.bind_apply hE (Kernel.aemeasurable _)]
    apply lintegral_congr
    intro y
    rw [recordStartKernel_apply, Measure.map_apply (MeasurableEquiv.measurable _) hE]
  rw [hstart, Measure.comp_assoc]
  rfl

/-- **Arbitrary-`π` integration of every finite-chain event.** -/
theorem chainVec_pairLaw_apply_eq_lintegral (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ)
    {E : Set (Fin (n + 1) → SwarmInfSeg.Pair N m)} (hE : MeasurableSet E) :
    (SwarmChain.chainVec (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)) E =
      ∫⁻ y, (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)) E ∂π := by
  rw [chainVec_pairLaw_eq_bind p hm hp hp1 π n,
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro y
  rw [initialFiniteKernel_apply p hm hp hp1 y n]

/-- **Arbitrary-`π` integration of every measurable finite-chain weight.**
This is the integration interface needed by raw-prefix sums whose integrand
retains duration, endpoint and future data. -/
theorem chainVec_pairLaw_lintegral_eq (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π] (n : ℕ)
    {F : (Fin (n + 1) → SwarmInfSeg.Pair N m) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, F v ∂(SwarmChain.chainVec
        (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)) =
      ∫⁻ y, ∫⁻ v, F v ∂(SwarmChain.chainVec
        (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (n + 1)) ∂π := by
  rw [chainVec_pairLaw_eq_bind p hm hp hp1 π n,
    Measure.lintegral_bind (initialFiniteKernel p hm n).measurable.aemeasurable hF.aemeasurable]
  apply lintegral_congr
  intro y
  rw [initialFiniteKernel_apply p hm hp hp1 y n]

end SwarmInitialTransport
