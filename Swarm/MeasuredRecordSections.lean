/-
Measured raw windows after one appended enriched record.

Generalising the special three/four-step index calculations, the raw path before
an appended record's onset is unchanged, while every position in its half-open
record interval is read from that record.  These facts need no stationarity,
fresh start, first-record support, unit duration, or restriction on dimension.
They are then used to split the arbitrary-`C`, arbitrary-`K`, arbitrary-`π`
one-record measured window without cancelling any future or record mass.
-/
import Swarm.GeneralFutureSections
import Swarm.RawRecordBlocks

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmMeasuredRecord

open SwarmFinFuture SwarmGeneralFuture SimJump.Record SwarmRec

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Appending an atom changes no old cumulative record time. -/
theorem prefixCum_snoc_of_le {r : ℕ} (v : Prefix (N := N) (m := m) r)
    (a : SwarmInfSeg.Pair N m) : ∀ k : ℕ, k ≤ r + 1 →
      prefixCum (prefixSnoc v a) k = prefixCum v k := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hkr : k ≤ r := by omega
      rw [prefixCum_succ_of_le _ (by omega : k ≤ r + 1),
        prefixCum_succ_of_le v hkr, ih (by omega)]
      congr 1
      simp [prefixSnoc, hkr]

/-- The new cumulative endpoint is the old onset plus the actual segment duration. -/
theorem prefixCum_snoc_new_end {r : ℕ} (v : Prefix (N := N) (m := m) r)
    (a : SwarmInfSeg.Pair N m) :
    prefixCum (prefixSnoc v a) (r + 2) = prefixCum v (r + 1) + a.1.dur := by
  rw [prefixCum_succ_of_le _ (le_refl (r + 1)),
    prefixCum_snoc_of_le v a (r + 1) le_rfl]
  simp [prefixSnoc]

/-- Before the new onset, both the selected old block and its value are unchanged. -/
theorem prefixX_snoc_of_before_new {r : ℕ} (v : Prefix (N := N) (m := m) r)
    (a : SwarmInfSeg.Pair N m) {t : ℕ}
    (ht : t < prefixCum v (r + 1)) (i : Fin N) :
    prefixX (prefixSnoc v a) t i = prefixX v t i := by
  let b := prefixBlk v t
  have hb : b ≤ r := prefixBlk_le v ht
  have hblocks : prefixBlk (prefixSnoc v a) t = b := by
    apply prefixBlk_of_between (n := r + 1) (t := t) (k := b)
    · rw [prefixCum_snoc_of_le v a b (by omega)]
      exact prefixCum_blk_le v t
    · rw [prefixCum_snoc_of_le v a (b + 1) (by omega)]
      exact prefixBlk_spec v t
  unfold prefixX
  simp only [hblocks, show prefixBlk v t = b from rfl, dif_pos hb,
    dif_pos (show b ≤ r + 1 by omega)]
  rw [prefixCum_snoc_of_le v a b (by omega)]
  simp [prefixSnoc, hb]

/-- Every raw position in the new half-open record interval, including either
interior or onset, has the exact enriched segment formula. -/
theorem prefixX_snoc_of_new_block {r : ℕ} (v : Prefix (N := N) (m := m) r)
    (a : SwarmInfSeg.Pair N m) {t : ℕ}
    (hlo : prefixCum v (r + 1) ≤ t)
    (hhi : t < prefixCum v (r + 1) + a.1.dur) (i : Fin N) :
    prefixX (prefixSnoc v a) t i =
      (r + 1 : ℤ) + a.1.p (t - prefixCum v (r + 1)) i := by
  rw [prefixX_of_between (prefixSnoc v a) (k := r + 1) (by omega) ?_ ?_]
  · rw [prefixCum_snoc_of_le v a (r + 1) le_rfl]
    simp [prefixSnoc]
  · rwa [prefixCum_snoc_of_le v a (r + 1) le_rfl]
  · rwa [prefixCum_snoc_new_end]

/-- Finite bounded raw patterns before the new onset do not read the appended atom. -/
theorem pathPat_snoc_of_before_new {r b : ℕ} (v : Prefix (N := N) (m := m) r)
    (a : SwarmInfSeg.Pair N m) (hb : b < prefixCum v (r + 1)) :
    SwarmFinHorizon.pathPat (N := N) b (prefixPath (prefixSnoc v a)) =
      SwarmFinHorizon.pathPat (N := N) b (prefixPath v) := by
  funext t i
  exact prefixX_snoc_of_before_new v a
    (lt_of_le_of_lt (Fin.is_le t) hb) i


/-- On actual first-record support, the new enriched endpoint has the raw word's
exact duration. -/
theorem prefixCum_prefixNext_new_end_of_firstRecord (p : ℝ) (hm : 1 ≤ m) {r : ℕ}
    (v : Prefix (N := N) (m := m) r) (pq : (k : ℕ) × (Fin k → JumpVec N))
    (hk : 0 < pq.1)
    (hq : FirstRecord (extendPath pq.2) pq.1
      (ofRecState (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2)) :
    prefixCum (prefixNext p hm v pq) (r + 2) = prefixCum v (r + 1) + pq.1 := by
  rw [prefixNext, prefixCum_snoc_new_end,
    SwarmFreshCyl.segOf_dur_of_firstRecord hk pq.2 hq]

/-- The appended raw segment formula on first-record support: the endpoint state
is the actual preceding endpoint, and the local raw offset can be any strict
interior offset as well as the onset. -/
theorem prefixX_prefixNext_of_new_block (p : ℝ) (hm : 1 ≤ m) {r t : ℕ}
    (v : Prefix (N := N) (m := m) r) (pq : (k : ℕ) × (Fin k → JumpVec N))
    (hk : 0 < pq.1)
    (hq : FirstRecord (extendPath pq.2) pq.1
      (ofRecState (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2))
    (hlo : prefixCum v (r + 1) ≤ t)
    (hhi : t < prefixCum v (r + 1) + pq.1) (i : Fin N) :
    prefixX (prefixNext p hm v pq) t i = (r + 1 : ℤ) +
      (SwarmSegKernel.segOf (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2 pq.1 pq.2).p
        (t - prefixCum v (r + 1)) i := by
  rw [prefixNext]
  refine prefixX_snoc_of_new_block v _ hlo ?_ i
  rwa [SwarmFreshCyl.segOf_dur_of_firstRecord hk pq.2 hq]

/-- A later finite trajectory kernel evaluated on an event that is measurable
using only its supplied bounded prefix is the corresponding Dirac section.  No
Borel-space or nonempty-carrier instance is needed. -/
theorem partialTraj_apply_bounded_prefix {X : ℕ → Type*}
    [∀ i, MeasurableSpace (X i)]
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] {r n : ℕ} (hrn : r + 1 ≤ n)
    (v : Π i : Finset.Iic (r + 1), X i)
    {D : Set (Π i : Finset.Iic (r + 1), X i)} (hD : MeasurableSet D) :
    (Kernel.partialTraj κ (r + 1) n v) (Preorder.frestrictLe₂ (π := X) hrn ⁻¹' D) =
      if v ∈ D then 1 else 0 := by
  have hmap := Kernel.partialTraj_map_frestrictLe₂_apply
    (κ := κ) (a := r + 1) (b := r + 1) (c := n) v hrn
  have hm := congrArg (fun μ : Measure (Π i : Finset.Iic (r + 1), X i) => μ D) hmap
  rw [Measure.map_apply (Preorder.measurable_frestrictLe₂ hrn) hD,
    Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_apply' _ hD] at hm
  simpa [Set.indicator] using hm

/-- For an arbitrary Ionescu--Tulcea trajectory, every bounded-prefix event has
the same mass at every longer finite horizon. -/
theorem trajMeasure_longPrefix_bounded_apply {X : Type*} [MeasurableSpace X]
    (κ : (n : ℕ) → Kernel (Π _i : Finset.Iic n, X) X)
    [∀ n, IsMarkovKernel (κ n)] (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    {r n : ℕ} (hrn : r + 1 ≤ n)
    {D : Set (Π _i : Finset.Iic (r + 1), X)} (hD : MeasurableSet D) :
    ((Kernel.trajMeasure (X := fun _ => X) μ₀ κ).map
        (Preorder.frestrictLe (π := fun _ => X) n))
        (Preorder.frestrictLe₂ (π := fun _ => X) hrn ⁻¹' D) =
      ((Kernel.trajMeasure (X := fun _ => X) μ₀ κ).map
        (Preorder.frestrictLe (π := fun _ => X) (r + 1))) D := by
  have hmap : Measurable (Preorder.frestrictLe₂ (π := fun _ => X) hrn) :=
    Preorder.measurable_frestrictLe₂ hrn
  have hrest : Measurable (Preorder.frestrictLe (π := fun _ => X) n) :=
    Preorder.measurable_frestrictLe (X := fun _ => X) n
  rw [← Measure.map_apply hmap hD, Measure.map_map hmap hrest]
  rfl

/-- For an actual enriched trajectory, every bounded event has the same mass at
every longer finite horizon. -/
theorem infLaw_longPrefix_bounded_apply (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {r n : ℕ} (hrn : r + 1 ≤ n)
    {D : Set (Prefix (N := N) (m := m) (r + 1))} (hD : MeasurableSet D) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) hrn ⁻¹' D) =
      ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) (r + 1))) D := by
  letI : ∀ j, IsMarkovKernel (SwarmInfSeg.homK (N := N) (m := m) p hm j) :=
    SwarmInfSeg.isMarkovKernel_homK p hm hp hp1
  letI : IsProbabilityMeasure (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) :=
    SwarmInfSeg.isProbabilityMeasure_pairLaw p hm hp hp1 π
  exact trajMeasure_longPrefix_bounded_apply
    (X := SwarmInfSeg.Pair N m) (SwarmInfSeg.homK (N := N) (m := m) p hm)
      (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π) hrn hD

/-- **Measured bounded-prefix/one-record identity.**  For arbitrary probability
`π`, arbitrary `N`, `m≥1`, arbitrary longer horizon `n≥r+1`, and every measurable
event `D` of the first `r+2` enriched atoms, the actual `n`-marginal mass is the
atomic `hitW` sum after the complete `r`-prefix.  The longer future plays no role
because the *bounded event itself* is a restriction preimage, not because of an
independence or stationarity assumption. -/
theorem infLaw_longPrefix_bounded_eq_hitW (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    {r n : ℕ} (hrn : r + 1 ≤ n)
    {D : Set (Prefix (N := N) (m := m) (r + 1))} (hD : MeasurableSet D) :
    ((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
        (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) n))
        (Preorder.frestrictLe₂ (π := fun _ => SwarmInfSeg.Pair N m) hrn ⁻¹' D) =
      ∫⁻ v : Prefix (N := N) (m := m) r,
        (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
          ENNReal.ofReal (RecKernel.hitW p pq.2
            (v ⟨r, Finset.mem_Iic.2 le_rfl⟩).2) *
            (if prefixNext p hm v pq ∈ D then 1 else 0))
        ∂((SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
          (Preorder.frestrictLe (π := fun _ => SwarmInfSeg.Pair N m) r)) := by
  rw [infLaw_longPrefix_bounded_apply p hm hp hp1 π hrn hD]
  exact infLaw_prefix_succ_apply_hitW p hm hp hp1 π hD

end SwarmMeasuredRecord
