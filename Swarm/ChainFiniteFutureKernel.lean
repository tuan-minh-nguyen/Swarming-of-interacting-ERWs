/-
# Actual finite-cylinder and next-kernel forms of arbitrary chain windows

For `K ≤ n` and every measurable `C` on raw positions `0,…,n`, `prefixWindow K n C` is a
measurable set of the first `n+1` enriched atoms.  On the canonical compatible trajectory its
membership is exactly the chain event `finStrict K ∩ pathPat n ⁻¹' C`.  Consequently the actual
`chainLaw (infLaw π)` mass is the mass under the actual `Iic n` marginal.  At positive width it
is also the one-step `pairK` integral over the `Iic (n-1)` marginal, using the actual append map
`prefixSnoc`; no product-law or future-independence assertion is made.

The specialised `chainLaw_three_window_eq_pairK_succ` retains the full arbitrary `C` for `K=3`
at every successor width `n≥3`.  It is a chain-side kernel reduction only: no array mass,
stationarity, hstruct, regeneration or invariant-π conclusion is claimed.
-/
import Swarm.ChainFiniteFuture

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFinFuture

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-! ## Measurability of the actual chain path -/

theorem measurable_chain_cum (k : ℕ) :
    Measurable (fun c : SwarmConcat.Chain N => c.cum k) := by
  induction k with
  | zero => simpa only [SwarmConcat.Chain.cum_zero] using
      (measurable_const : Measurable (fun _ : SwarmConcat.Chain N => (0 : ℕ)))
  | succ k ih =>
      rw [show (fun c : SwarmConcat.Chain N => c.cum (k + 1)) =
          fun c => c.cum k + (c.seg k).dur from
        funext fun c => SwarmConcat.Chain.cum_succ c k]
      exact ih.add (SwarmConcat.measurable_chain_dur k)

theorem measurable_chain_X (t : ℕ) (i : Fin N) :
    Measurable (fun c : SwarmConcat.Chain N => c.X t i) := by
  unfold SwarmConcat.Chain.X SwarmConcat.Chain.blk
  refine Measurable.find (p := fun k (c : SwarmConcat.Chain N) => t < c.cum (k + 1))
    (f := fun k (c : SwarmConcat.Chain N) => (k : ℤ) + (c.seg k).p (t - c.cum k) i) ?_ ?_
    (fun c : SwarmConcat.Chain N => c.exists_cum_gt t)
  · intro k
    exact measurable_const.add ((measurable_seg_p_dyn i).comp
      ((SwarmConcat.measurable_chain_seg k).prodMk
        (measurable_const.sub (measurable_chain_cum k))))
  · intro k
    exact measurableSet_lt measurable_const (measurable_chain_cum (k + 1))

/-- The actual concatenated raw path is measurable. -/
noncomputable def chainPath (c : SwarmConcat.Chain N) : ℕ → Fin N → ℤ :=
  fun t i => c.X t i

theorem measurable_chainPath : Measurable (chainPath (N := N)) := by
  exact measurable_pi_iff.mpr fun t => measurable_pi_iff.mpr fun i => measurable_chain_X t i

/-! ## The same arbitrary window on chains and finite enriched prefixes -/

/-- An arbitrary raw-time chain window, with no restriction on `C`. -/
def chainWindow (K n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)) :
    Set (SwarmConcat.Chain N) :=
  chainPath ⁻¹' (SwarmFinHorizon.finStrict (N := N) K ∩
    SwarmFinHorizon.pathPat (N := N) n ⁻¹' C)

/-- The corresponding set of finite enriched records. -/
def prefixWindow (K n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)) :
    Set (Prefix (N := N) (m := m) n) :=
  prefixPath ⁻¹' (SwarmFinHorizon.finStrict (N := N) K ∩
    SwarmFinHorizon.pathPat (N := N) n ⁻¹' C)

theorem measurableSet_chainWindow {K n : ℕ}
    {C : Set (Fin (n + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    MeasurableSet (chainWindow (N := N) K n C) :=
  ((SwarmFinHorizon.measurableSet_finStrict K).inter
    (hC.preimage (SwarmFinHorizon.measurable_pathPat n))).preimage measurable_chainPath

theorem measurableSet_prefixWindow {K n : ℕ}
    {C : Set (Fin (n + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    MeasurableSet (prefixWindow (N := N) (m := m) K n C) :=
  ((SwarmFinHorizon.measurableSet_finStrict K).inter
    (hC.preimage (SwarmFinHorizon.measurable_pathPat n))).preimage measurable_prefixPath

/-- Compatibility turns the finite-prefix description into the actual chain event literally. -/
theorem mem_prefixWindow_iff_chain {K n : ℕ} (hK : K ≤ n)
    {C : Set (Fin (n + 1) → Fin N → ℤ)} {A : ℕ → SwarmInfSeg.Pair N m}
    (hA : SwarmChainAssemble.TrajCompat A) :
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A ∈
        prefixWindow (N := N) (m := m) K n C ↔
      SwarmChainAssemble.chainOf A ∈ chainWindow (N := N) K n C := by
  let v : Prefix (N := N) (m := m) n :=
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A
  let c : SwarmConcat.Chain N := SwarmChainAssemble.chainOf A
  have hX : ∀ t, t ≤ n → ∀ i, prefixPath v t i = chainPath c t i := by
    intro t ht i
    exact prefixX_eq_chain_X hA ht i
  have hpat : SwarmFinHorizon.pathPat (N := N) n (prefixPath v) =
      SwarmFinHorizon.pathPat (N := N) n (chainPath c) := by
    funext t i
    exact hX (t : ℕ) (by have := t.2; omega) i
  have hstrict : prefixPath v ∈ SwarmFinHorizon.finStrict (N := N) K ↔
      chainPath c ∈ SwarmFinHorizon.finStrict (N := N) K := by
    constructor
    · rintro ⟨h0, hpos⟩
      refine ⟨fun i => ?_, fun t ht htK i => ?_⟩
      · rw [← hX 0 (Nat.zero_le n) i]
        exact h0 i
      · rw [← hX t (le_trans htK hK) i]
        exact hpos t ht htK i
    · rintro ⟨h0, hpos⟩
      refine ⟨fun i => ?_, fun t ht htK i => ?_⟩
      · rw [hX 0 (Nat.zero_le n) i]
        exact h0 i
      · rw [hX t (le_trans htK hK) i]
        exact hpos t ht htK i
  change prefixPath v ∈ SwarmFinHorizon.finStrict (N := N) K ∩
      SwarmFinHorizon.pathPat (N := N) n ⁻¹' C ↔
    chainPath c ∈ SwarmFinHorizon.finStrict (N := N) K ∩
      SwarmFinHorizon.pathPat (N := N) n ⁻¹' C
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  rw [hstrict, hpat]

/-- **The arbitrary window mass is exactly the actual finite enriched marginal mass.** -/
theorem chainLaw_window_eq_prefix (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {K n : ℕ} (hK : K ≤ n) {C : Set (Fin (n + 1) → Fin N → ℤ)} (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) (chainWindow K n C) =
      ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (prefixWindow K n C) := by
  rw [SwarmChainAssemble.chainLaw_apply _ (measurableSet_chainWindow hC),
    Measure.map_apply
      (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) n)
      (measurableSet_prefixWindow hC)]
  apply measure_congr
  filter_upwards [SwarmInfSeg.trajCompat_ae p hm hp hp1 π] with A hA
  apply propext
  change SwarmChainAssemble.chainOf A ∈ chainWindow K n C ↔
    Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n A ∈ prefixWindow K n C
  exact (mem_prefixWindow_iff_chain hK hA).symm

/-! ## The exact next-atom Markov-kernel interface -/

/-- Append one actual enriched atom to a record of atoms `0,…,r`. -/
def prefixSnoc {r : ℕ} (v : Prefix (N := N) (m := m) r) (a : SwarmInfSeg.Pair N m) :
    Prefix (N := N) (m := m) (r + 1) :=
  fun i => if h : (i : ℕ) ≤ r then v ⟨i, Finset.mem_Iic.2 h⟩ else a

theorem measurable_prefixSnoc {r : ℕ} :
    Measurable (fun q : Prefix (N := N) (m := m) r × SwarmInfSeg.Pair N m =>
      prefixSnoc q.1 q.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : (i : ℕ) ≤ r
  · rw [show (fun q : Prefix (N := N) (m := m) r × SwarmInfSeg.Pair N m =>
          prefixSnoc q.1 q.2 i) = fun q => q.1 ⟨i, Finset.mem_Iic.2 h⟩ from
        funext fun q => by simp only [prefixSnoc, h, dif_pos]]
    exact (measurable_pi_apply (⟨i, Finset.mem_Iic.2 h⟩ : ↥(Finset.Iic r))).comp measurable_fst
  · rw [show (fun q : Prefix (N := N) (m := m) r × SwarmInfSeg.Pair N m =>
          prefixSnoc q.1 q.2 i) = fun q => q.2 from
        funext fun q => by simp [prefixSnoc, h]]
    exact measurable_snd

/-- Appending the actual next coordinate gives the actual longer finite restriction. -/
theorem prefixSnoc_frestrictLe {r : ℕ} (A : ℕ → SwarmInfSeg.Pair N m) :
    prefixSnoc (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r A) (A (r + 1)) =
      Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) (r + 1) A := by
  funext i
  by_cases h : (i : ℕ) ≤ r
  · simp only [prefixSnoc, h, dif_pos, Preorder.frestrictLe_apply]
  · have hi : (i : ℕ) = r + 1 := by
      have hu := Finset.mem_Iic.1 i.2
      omega
    simp [prefixSnoc, h, Preorder.frestrictLe_apply, hi]

/-- **The actual finite marginal recursion.** Every measurable event of the first `r+2`
enriched atoms has a one-step `pairK` integral over the law of the first `r+1` atoms. -/
theorem infLaw_prefix_succ_apply (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {r : ℕ} {E : Set (Prefix (N := N) (m := m) (r + 1))} (hE : MeasurableSet E) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) (r + 1))) E =
      ∫⁻ v : Prefix (N := N) (m := m) r,
        (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨r, Finset.mem_Iic.2 le_rfl⟩)) {a | prefixSnoc v a ∈ E}
        ∂((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) := by
  let D : Set (Prefix (N := N) (m := m) r × SwarmInfSeg.Pair N m) :=
    (fun q => prefixSnoc q.1 q.2) ⁻¹' E
  have hD : MeasurableSet D := hE.preimage measurable_prefixSnoc
  have hpre : (fun A : ℕ → SwarmInfSeg.Pair N m =>
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r A, A (r + 1))) ⁻¹' D =
      (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) (r + 1)) ⁻¹' E := by
    ext A
    change prefixSnoc (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r A)
      (A (r + 1)) ∈ E ↔ _
    rw [prefixSnoc_frestrictLe]
    rfl
  rw [Measure.map_apply
    (Preorder.measurable_frestrictLe (X := fun _ => SwarmInfSeg.Pair N m) (r + 1)) hE]
  have h := SwarmInfSeg.cyl_measure p hm hp hp1 π r hD
  rw [hpre] at h
  exact h

/-- **Positive-width windows as an actual `pairK` integral.**  The integrand is the conditional
next-atom event after the whole observed prefix; it is not asserted to be constant or independent
of that prefix. -/
theorem chainLaw_window_eq_pairK_succ (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {K r : ℕ} (hK : K ≤ r + 1) {C : Set (Fin (r + 1 + 1) → Fin N → ℤ)}
    (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) (chainWindow K (r + 1) C) =
      ∫⁻ v : Prefix (N := N) (m := m) r,
        (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨r, Finset.mem_Iic.2 le_rfl⟩))
          {a | prefixSnoc v a ∈ prefixWindow K (r + 1) C}
        ∂((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) := by
  rw [chainLaw_window_eq_prefix p hm hp hp1 π hK hC]
  exact infLaw_prefix_succ_apply p hm hp hp1 π (measurableSet_prefixWindow hC)

/-- **K = 3, arbitrary successor width at least three, and arbitrary measurable C.** -/
theorem chainLaw_three_window_eq_pairK_succ (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {r : ℕ} (hr : 3 ≤ r + 1) {C : Set (Fin (r + 1 + 1) → Fin N → ℤ)}
    (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) (chainWindow 3 (r + 1) C) =
      ∫⁻ v : Prefix (N := N) (m := m) r,
        (SwarmSegKernel.pairK (N := N) (m := m) p hm
          (v ⟨r, Finset.mem_Iic.2 le_rfl⟩))
          {a | prefixSnoc v a ∈ prefixWindow 3 (r + 1) C}
        ∂((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) :=
  chainLaw_window_eq_pairK_succ p hm hp hp1 π hr hC

end SwarmFinFuture


