/-`BlockAggregate` computes the *terminal* block endpoint law at every `r`, and `JointTwo` the
joint law of two consecutive endpoints.  This file does the general finite cylinder: the law of
the whole path of partial block endpoints.

* `pathOf hm y t r w : (i : Fin (r+1)) → RecState N m × ℕ` — the partial endpoints of the tuple
  `w`: the nested record states and cumulative record times after `0, 1, …, r` blocks.  The last
  coordinate is `endptF` (`pathOf_last`).
* `blockPathLaw p hm y t r` — the finite path law: the sum over `r`-tuples of words of the
  product of the `hitW` weights, located at `pathOf`.
* `blockPathLaw_apply` — its exact test-set formula.
* `blockPathLaw_last` — **the last-coordinate marginal of the block path law is exactly the
  `r`-fold iterate of the lifted stopped record kernel** from `(y, t)`.  This is the
  kernel-iterate identification for path marginals.
* `path_law_of_block_stat` — the actual-array version: given the geometric block decomposition
  (pairwise disjointness of the block boxes, almost sure covering) and a statistic `S` of the
  array that is the block path on each box, the law of `S` is `blockPathLaw`.

The residual is exactly the same three geometric inputs as at `r = 1` (where they are theorems,
see `R1Consistency.lean`).  Nothing here is `Bridge.JointLawIdentity` (that is the law of the
whole infinite record sequence on the stopped-path space, which additionally needs the
countable-cylinder extension), and nothing here asserts `Swarm.Ballistic`, `RegenAvailable`,
`MainClaim`, `(diam)` or a common speed.
-/
import Swarm.JointTwo

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M6Aggr

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec
open M5FirstBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### The path of partial block endpoints -/

/-- The partial block endpoints of a tuple of words: index `i` is the record state and record time
after the first `i` blocks. -/
noncomputable def pathOf {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) :
    (r : ℕ) → (Fin r → Word N) → ((i : Fin (r + 1)) → RecState N m × ℕ)
  | 0, _ => fun _ => (y, t)
  | r + 1, w => Fin.cons (y, t)
      (pathOf hm (out hm (w 0).2 y) (t + (w 0).1) r (fun i => w i.succ))

@[simp] theorem pathOf_succ {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    (w : Fin (r + 1) → Word N) :
    pathOf hm y t (r + 1) w = Fin.cons (y, t)
      (pathOf hm (out hm (w 0).2 y) (t + (w 0).1) r (fun i => w i.succ)) := rfl

theorem pathOf_zero_coord {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    (w : Fin r → Word N) : pathOf hm y t r w 0 = (y, t) := by
  cases r with
  | zero => rfl
  | succ r => rw [pathOf_succ]; simp

/-- The last coordinate of the block path is the terminal block endpoint. -/
theorem pathOf_last {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (t : ℕ) (w : Fin r → Word N),
      pathOf hm y t r w (Fin.last r) = endptF hm y t r w := by
  intro r
  induction r with
  | zero => intro y t w; rfl
  | succ r ih =>
      intro y t w
      rw [pathOf_succ]
      have hlast : Fin.last (r + 1) = Fin.succ (Fin.last r) := rfl
      rw [hlast, Fin.cons_succ, ih]
      rw [endptF, endptF]
      simp only [runOutF_succ, totLen_succ, Nat.add_assoc]

/-! ### The block path law -/

/-- The finite-dimensional law of the record path up to `r` blocks, started at `(y, t)`: the sum
over all `r`-tuples of words of the product of the stopped record weights, located at the path of
partial endpoints.  Tuples with a block that is not a first-record path carry weight zero. -/
noncomputable def blockPathLaw (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ)
    (r : ℕ) : Measure ((i : Fin (r + 1)) → RecState N m × ℕ) :=
  Measure.sum (fun w : Fin r → Word N =>
    ENNReal.ofReal (blockProdF p hm y r w) • Measure.dirac (pathOf hm y t r w))

theorem blockPathLaw_apply (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    {A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)} (hA : MeasurableSet A) :
    blockPathLaw p hm y t r A
      = ∑' w : Fin r → Word N,
          ENNReal.ofReal (blockProdF p hm y r w) *
            (if pathOf hm y t r w ∈ A then 1 else 0) := by
  classical
  rw [blockPathLaw, Measure.sum_apply _ hA]
  refine tsum_congr fun w => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]

/-- **The last-coordinate marginal of the block path law is the `r`-fold iterate of the lifted
stopped record kernel.** -/
theorem blockPathLaw_last {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (t : ℕ) (r : ℕ)
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    blockPathLaw p hm y t r {g | g (Fin.last r) ∈ A}
      = ((SwarmKB.step (hitKKernelT p hm))^[r] (Measure.dirac (y, t))) A := by
  have hset : {g : (i : Fin (r + 1)) → RecState N m × ℕ | g (Fin.last r) ∈ A}
      = (fun g => g (Fin.last r)) ⁻¹' A := rfl
  rw [hset, blockPathLaw_apply p hm y t r (hA.preimage (measurable_pi_apply (Fin.last r))),
    step_iterate_dirac_apply p hp0 hp1 hm r y t hA]
  refine tsum_congr fun w => ?_
  rw [Set.mem_preimage, pathOf_last]

/-! ### The block path law at the actual array -/

/-- The piece of the array space on which the `r`-block box of `w` is followed and the block path
of `w` falls in `A`. -/
noncomputable def pathPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    (A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)) (w : Fin r → Word N) : Set (Array N) :=
  if pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A
    then jbox p m (totLen r w) (concatF r w) else ∅

theorem measurableSet_pathPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (r : ℕ)
    {A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)} (w : Fin r → Word N) :
    MeasurableSet (pathPiece (N := N) p hm r A w) := by
  classical
  unfold pathPiece
  split
  · exact measurableSet_jbox p m (totLen r w) (concatF r w)
  · exact MeasurableSet.empty

/-- **The finite-dimensional record path law at the actual array**, given the geometric block
decomposition: if the first-record `r`-block boxes are pairwise disjoint, cover almost every
array, and the array statistic `S` is the block path on each box, then the law of `S` is
`blockPathLaw`. -/
theorem path_law_of_block_stat {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (r : ℕ)
    (hdisj : ∀ w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, w ≠ w' →
      Disjoint (jbox p m (totLen r w.1) (concatF r w.1))
        (jbox p m (totLen r w'.1) (concatF r w'.1)))
    (hcover : ∀ᵐ U ∂(arrayMeasure N), ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      U ∈ jbox p m (totLen r w.1) (concatF r w.1))
    (S : Array N → ((i : Fin (r + 1)) → RecState N m × ℕ))
    (hS : ∀ (w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}) (U : Array N),
      U ∈ jbox p m (totLen r w.1) (concatF r w.1) →
        S U = pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1)
    {A : Set ((i : Fin (r + 1)) → RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | S U ∈ A}
      = blockPathLaw p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r A := by
  classical
  have hset : {U : Array N | S U ∈ A} =ᵐ[arrayMeasure N]
      {U : Array N | ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        U ∈ jbox p m (totLen r w.1) (concatF r w.1) ∧
          pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A} := by
    filter_upwards [hcover] with U hU
    apply propext
    constructor
    · intro hSA
      obtain ⟨w, hw⟩ := hU
      exact ⟨w, hw, by rw [← hS w U hw]; exact hSA⟩
    · rintro ⟨w, hw, hmem⟩
      show S U ∈ A
      rw [hS w U hw]
      exact hmem
  rw [measure_congr hset]
  have hunion : {U : Array N | ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        U ∈ jbox p m (totLen r w.1) (concatF r w.1) ∧
          pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A}
      = ⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          pathPiece (N := N) p hm r A w.1 := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, pathPiece]
    constructor
    · rintro ⟨w, hw, hmem⟩
      exact ⟨w, by rw [if_pos hmem]; exact hw⟩
    · rintro ⟨w, hw⟩
      by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
      · rw [if_pos hmem] at hw
        exact ⟨w, hw, hmem⟩
      · rw [if_neg hmem] at hw
        exact absurd hw (Set.notMem_empty U)
  rw [hunion]
  have hdisjg : ∀ w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, w ≠ w' →
      Disjoint (pathPiece (N := N) p hm r A w.1) (pathPiece (N := N) p hm r A w'.1) := by
    intro w w' hne
    simp only [pathPiece]
    by_cases hw : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · by_cases hw' : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_pos hw, if_pos hw']
        exact hdisj w w' hne
      · rw [if_pos hw, if_neg hw']
        exact disjoint_bot_right
    · by_cases hw' : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_neg hw, if_pos hw']
        exact disjoint_bot_left
      · rw [if_neg hw, if_neg hw']
        exact disjoint_bot_right
  rw [measure_iUnion hdisjg (fun w => measurableSet_pathPiece p hm r w.1)]
  have hsub := tsum_subtype_eq_of_eq_zero
    {w : Fin r → Word N | FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}
    (fun w => ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w) *
      (if pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A then 1 else 0))
    (fun w hw => by
      rw [blockProdF_eq_zero_of_not_frChain p hm r (SwarmRecordMeas.StartLaw.zeroState hm) w hw,
        ENNReal.ofReal_zero, zero_mul])
  refine Eq.trans (tsum_congr (fun w => ?_))
    (hsub.trans (blockPathLaw_apply p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r hA).symm)
  simp only [pathPiece]
  by_cases hmem : pathOf hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
  · rw [if_pos hmem, if_pos hmem, mass_jbox_concatF hp0 hp1 hm r w.1 w.2]
    exact (mul_one _).symm
  · rw [if_neg hmem, if_neg hmem, measure_empty, mul_zero]

end M6Aggr
