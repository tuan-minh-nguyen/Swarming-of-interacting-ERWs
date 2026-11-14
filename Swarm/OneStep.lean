/-
# The one-step recursion of the M6 block path law

`M6Aggr.blockPathLaw p hm y t r` is the law of the `r`-block record path
`pathOf hm y t r w`, a sum over `r`-tuples of finite jump words of the product of the stopped
record weights.  This file proves the **narrow one-step recursion**: the `(r+1)`-block path law
is the `r`-block path law composed with one step of the time-extended stopped record kernel
`hitKKernelT`, i.e. the prefix is distributed as the `r`-block law, the appended coordinate is
drawn from `hitKKernelT p hm` *at the prefix's last coordinate* (record state *and* absolute record
time), and the two are glued by `appendFun`.

The statement uses the `Iic r`-shaped indexing (`pathIic`, `appendFun`) in which the appended
coordinate is literally the last one and `homFam κ r` is the Mathlib/`PathLaw` kernel
`κ ∘ (last coordinate)`; `M6Step.blockPathLawIic_eq_blockPathLaw` re-indexes to the `Fin (r+1)`
shape of `M6Aggr.blockPathLaw`, and `M6Step.blockPathLawIic_eq_trajWindow` performs the induction
against the Ionescu–Tulcea window recursion `M6Aggr.homTraj_window_succ`.

The last-block algebra is `Fin.snoc`-based: for `q = (a, w)`,
`blockProdF … (r+1) (snoc w a) = blockProdF … r w * hitW p a.2 (runOutF … r w)` and
`pathIic … (r+1) (snoc w a) = appendFun (pathIic … r w) (out hm a.2 (runOutF … r w),
t + totLen r w + a.1)`, so the absolute time and the nested state are those of the prefix, and the
new block's weight `hitW p a.2 (runOutF …)` is exactly the mass of `hitKInfT p hm` at the prefix's
endpoint.  The sum over the last block is *not* replaced by anything: `hitKInfT` is unfolded as a
countable sum of weighted Diracs (`hitKInfT_eq_sum`), and both sides are compared as measures.

No `sorry`, no new axioms.
-/
import Swarm.RecordPathBridgeM2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M6Step

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec M5FirstBlock M6Aggr

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### The `Iic`-shaped block path law -/

/-- The `r`-block record path law with its coordinates indexed by `Finset.Iic r` instead of
`Fin (r+1)`: the same sum over `r`-tuples of words, with the same weights. -/
noncomputable def blockPathLawIic (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ)
    (r : ℕ) : Measure ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) :=
  Measure.sum (fun w : Fin r → Word N =>
    ENNReal.ofReal (blockProdF p hm y r w) • Measure.dirac (pathIic hm y t r w))

/-! ### Elementary facts about the endpoint, the kernel and countable sums -/

@[simp] theorem endptF_fst {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t r : ℕ)
    (w : Fin r → Word N) : (endptF hm y t r w).1 = runOutF hm y r w := rfl

@[simp] theorem endptF_snd {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t r : ℕ)
    (w : Fin r → Word N) : (endptF hm y t r w).2 = t + totLen r w := rfl

/-- At `r = 0` the block product is `1`. -/
@[simp] theorem blockProdF_zero {m : ℕ} (p : ℝ) (hm : 1 ≤ m) (y : RecState N m)
    (w : Fin 0 → Word N) : blockProdF p hm y 0 w = 1 := rfl

/-- At `r = 0` the `Iic 0`-shaped block path is the constant path. -/
@[simp] theorem pathIic_zero {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ)
    (w : Fin 0 → Word N) : pathIic hm y t 0 w = fun _ => (y, t) := rfl

/-- The last coordinate of the `Iic r`-shaped path of a tuple is the tuple's endpoint. -/
theorem pathIic_last {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    (w : Fin r → Word N) :
    pathIic hm y t r w ⟨r, Finset.mem_Iic.mpr le_rfl⟩ = endptF hm y t r w := by
  rw [pathIic_apply]
  exact pathOf_last hm r y t w

/-- The horizon-free stopped record measure, unfolded as a countable sum over single words. -/
theorem hitKInfT_eq_sum {m : ℕ} (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ) :
    hitKInfT p hm z =
      Measure.sum (fun a : Word N =>
        ENNReal.ofReal (hitW p a.2 z.1) • Measure.dirac (out hm a.2 z.1, z.2 + a.1)) := rfl

/-- The block product is nonnegative. -/
theorem blockProdF_nonneg (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (w : Fin r → Word N), 0 ≤ blockProdF p hm y r w := by
  intro r
  induction r with
  | zero => intro y w; exact zero_le_one
  | succ r ih =>
      intro y w
      rw [blockProdF_succ]
      exact mul_nonneg (hitW_nonneg p hp0 hp1 (w 0).2 y) (ih _ _)

/-- `Fin.snoc` as an `Equiv`, evaluated on a pair. -/
theorem snocEquiv_apply_pair {n : ℕ} (q : Word N × (Fin n → Word N)) :
    (Fin.snocEquiv (fun _ => Word N)) q = Fin.snoc q.2 q.1 := by
  funext x
  rw [Fin.snocEquiv_apply]

/-- A scalar pulls out of a countable sum of measures. -/
theorem smul_sum_measure {α : Type*} [MeasurableSpace α] {ι : Type*}
    {a : ℝ≥0∞} {μ : ι → Measure α} :
    a • (Measure.sum μ) = Measure.sum (fun i => a • μ i) := by
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul, ENNReal.tsum_mul_left]

/-- Pushing a measurable map through a countable sum of weighted Dirac masses. -/
theorem map_sum_smul_dirac {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ι : Type*} {c : ι → ℝ≥0∞} {p : ι → X} {g : X → Y} (hg : Measurable g) :
    (Measure.sum (fun i => c i • Measure.dirac (p i))).map g
      = Measure.sum (fun i => c i • Measure.dirac (g (p i))) := by
  rw [Measure.map_sum hg.aemeasurable]
  refine sum_measure_congr (fun i => ?_)
  rw [Measure.map_smul]
  congr 1
  ext s hs
  rw [Measure.map_apply hg hs, Measure.dirac_apply' _ (hs.preimage hg), Measure.dirac_apply' _ hs]
  rfl

/-! ### The one-step recursion -/

/-- **The narrow one-step recursion of the M6 block path law.**

The `(r+1)`-block record path law is obtained from the `r`-block path law by drawing one step of
the time-extended stopped record kernel at the prefix's last coordinate and appending it as the
new last coordinate.  Both sides are stated as measures on the `Iic (r+1)`-shaped path space.

The decomposition is `Fin.snoc`: a tuple of `r+1` blocks is a pair `(a, w)` (last block, prefix),
the weight factors as `blockProdF … r w * hitW p a.2 (runOutF … r w)`, the appended coordinate is
`(out hm a.2 (runOutF … r w), t + totLen r w + a.1)` — the prefix's nested state and absolute
record time, advanced by the last block — and `hitKInfT p hm` at the prefix endpoint is exactly
the sum of those weighted Diracs. -/
theorem blockPathLawIic_succ (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) :
    blockPathLawIic (N := N) p hm y t (r + 1)
      = (blockPathLawIic (N := N) p hm y t r ⊗ₘ homFam (hitKKernelT p hm) r).map
          (fun q : ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) × (RecState N m × ℕ) =>
            appendFun q.1 q.2) := by
  classical
  haveI hK : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT (N := N) (m := m) p hp0 hp1 hm
  -- the common expression: prefix law × one weighted Dirac for the last block, appended
  set Φ : Word N × (Fin r → Word N) →
      Measure ((i : ↥(Finset.Iic (r + 1))) → RecState N m × ℕ) :=
    fun q => (ENNReal.ofReal (blockProdF p hm y r q.2) *
        ENNReal.ofReal (hitW p q.1.2 (runOutF hm y r q.2))) •
      Measure.dirac (appendFun (pathIic hm y t r q.2)
        (out hm q.1.2 (runOutF hm y r q.2), t + totLen r q.2 + q.1.1)) with hΦ
  -- left-hand side: split the tuple of blocks into prefix and last block
  have hL : blockPathLawIic (N := N) p hm y t (r + 1) = Measure.sum Φ := by
    rw [blockPathLawIic]
    refine Eq.trans (sum_measure_equiv (Fin.snocEquiv (fun _ => Word N))
      (fun W : Fin (r + 1) → Word N =>
        ENNReal.ofReal (blockProdF p hm y (r + 1) W) •
          Measure.dirac (pathIic hm y t (r + 1) W))).symm ?_
    refine sum_measure_congr (fun q => ?_)
    rw [snocEquiv_apply_pair, hΦ]
    rw [blockProdF_snoc p hm r y q.2 q.1,
      pathIic_snoc hm r y t q.2 q.1,
      ENNReal.ofReal_mul (blockProdF_nonneg p hp0 hp1 hm r y q.2)]
  -- right-hand side: unfold the prefix law, distribute the compProd, push the map inside
  have hR : (blockPathLawIic (N := N) p hm y t r ⊗ₘ homFam (hitKKernelT p hm) r).map
      (fun q : ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) × (RecState N m × ℕ) =>
        appendFun q.1 q.2) = Measure.sum Φ := by
    have h1 : blockPathLawIic (N := N) p hm y t r
        = Measure.sum (fun w : Fin r → Word N =>
            ENNReal.ofReal (blockProdF p hm y r w) • Measure.dirac (pathIic hm y t r w)) := rfl
    rw [h1, Measure.compProd_sum_left]
    rw [Measure.map_sum (f := fun q : ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) ×
        (RecState N m × ℕ) => appendFun q.1 q.2)
      (measurable_appendFun (X := RecState N m × ℕ) (r := r)).aemeasurable]
    trans Measure.sum (fun w : Fin r → Word N => Measure.sum (fun a : Word N => Φ (a, w)))
    · -- one prefix block: `(c • δ_g) ⊗ₘ κ`, mapped by `appendFun`
      refine sum_measure_congr (fun w => ?_)
      rw [Measure.compProd_smul_left, M6Aggr.dirac_compProd_map,
        SimJump.RecKernel.homFam_apply, pathIic_last,
        SimJump.RecKernel.hitKKernelT_apply, hitKInfT_eq_sum]
      rw [Measure.map_smul]
      rw [Measure.map_map (measurable_appendFun (X := RecState N m × ℕ) (r := r))
        (by fun_prop : Measurable (Prod.mk (pathIic hm y t r w)))]
      rw [show ((fun q : ((i : ↥(Finset.Iic r)) → RecState N m × ℕ) × (RecState N m × ℕ) =>
            appendFun q.1 q.2) ∘ Prod.mk (pathIic hm y t r w))
          = (fun z => appendFun (pathIic hm y t r w) z) from rfl]
      rw [map_sum_smul_dirac (measurable_appendFun_right (pathIic hm y t r w)), smul_sum_measure]
      refine sum_measure_congr (fun a => ?_)
      rw [smul_smul]
      simp only [hΦ, endptF_fst, endptF_snd]
    · -- the double sum is the pair sum
      rw [Measure.sum_comm (fun (w : Fin r → Word N) (a : Word N) => Φ (a, w))]
      rw [Measure.sum_sum (fun (a : Word N) (w : Fin r → Word N) => Φ (a, w))]
  rw [hL, hR]

end M6Step
