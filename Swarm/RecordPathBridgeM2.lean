/-
# The record-path bridge: `blockPathLaw` is the finite window of the stopped-record Ionescu–Tulcea law

Main result (below): for `1/2 < p < 1`, `m ≥ 1`, `r : ℕ`,

`M6Aggr.blockPathLaw p hm (zeroState hm) 0 r`
  `= (SimJump.RecKernel.recordTrajT p hp0.le hp1.le hm (Measure.dirac (zeroState hm, 0))).map`
      `(fun ω : ℕ → RecState N m × ℕ => fun i : Fin (r+1) => ω i)`.

Strategy (a projective/full-horizon one, see the swarm board): the two laws are compared as
*families* of finite windows.  The Ionescu–Tulcea side is identified, through Mathlib's
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, with a family of `Iic r`-indexed
measures satisfying a one-step "append at the end" recursion with kernel `hitKKernelT`; the M6
side is proved to satisfy the *same* recursion by a finite re-indexing of its defining sum over
word tuples (`Fin.snoc`).  Equality of the families follows by induction on `r`.
-/
import Swarm.BlockPathLaw
import Swarm.M2WindowLaw

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M6Aggr

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec
open M5FirstBlock

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### Appending a coordinate at the end of a `Iic r`-indexed path -/

/-- Append a new last coordinate to a path indexed by `Iic r`, giving a path indexed by
`Iic (r+1)`. -/
def appendFun {X : Type*} (f : (i : ↥(Finset.Iic r)) → X) (z : X) : (i : ↥(Finset.Iic (r + 1))) → X :=
  fun i => if h : (i : ℕ) ≤ r then f ⟨i, Finset.mem_Iic.mpr h⟩ else z

theorem appendFun_apply_le {X : Type*} {r : ℕ} (f : (i : ↥(Finset.Iic r)) → X) (z : X)
    (i : ↥(Finset.Iic (r + 1))) (h : (i : ℕ) ≤ r) :
    appendFun f z i = f ⟨i, Finset.mem_Iic.mpr h⟩ := by
  simp only [appendFun, dif_pos h]

theorem appendFun_apply_gt {X : Type*} {r : ℕ} (f : (i : ↥(Finset.Iic r)) → X) (z : X)
    (i : ↥(Finset.Iic (r + 1))) (h : ¬ (i : ℕ) ≤ r) : appendFun f z i = z := by
  simp only [appendFun, dif_neg h]

theorem measurable_appendFun {X : Type*} [MeasurableSpace X] {r : ℕ} :
    Measurable (fun p : ((i : ↥(Finset.Iic r)) → X) × X => appendFun p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : (i : ℕ) ≤ r
  · simp only [appendFun, dif_pos h]
    exact (measurable_pi_apply (⟨(i : ℕ), Finset.mem_Iic.mpr h⟩ : ↥(Finset.Iic r))).comp
      measurable_fst
  · simp only [appendFun, dif_neg h]
    exact measurable_snd

/-- Appending a fixed coordinate is measurable. -/
theorem measurable_appendFun_right {X : Type*} [MeasurableSpace X] {r : ℕ}
    (f : (i : ↥(Finset.Iic r)) → X) : Measurable (fun z : X => appendFun f z) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : (i : ℕ) ≤ r
  · simp only [appendFun, dif_pos h]
    exact measurable_const
  · simp only [appendFun, dif_neg h]
    exact measurable_id

/-- The `Iic (r+1)` path built from the restriction to `Iic r` and the last coordinate. -/
theorem frestrictLe_succ_eq_appendFun {X : Type*} {r : ℕ} (x : ℕ → X) :
    Preorder.frestrictLe (r + 1) x
      = appendFun (Preorder.frestrictLe r x) (x (r + 1)) := by
  funext i
  by_cases h : (i : ℕ) ≤ r
  · rw [appendFun_apply_le _ _ _ h]
    rfl
  · rw [appendFun_apply_gt _ _ _ h]
    have hi : (i : ℕ) = r + 1 := by
      have := i.2
      simp only [Finset.mem_Iic] at this
      omega
    rw [Preorder.frestrictLe_apply]
    exact congrArg x hi

/-! ### The Ionescu–Tulcea window recursion

The `Iic r`-window of the path law of a time-homogeneous Markov kernel satisfies the one-step
recursion "append a coordinate drawn from `κ` at the last coordinate". -/
theorem homTraj_window_succ {X : Type*} [MeasurableSpace X]
    (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ] (r : ℕ) :
    (homTraj κ μ).map (Preorder.frestrictLe (r + 1))
      = ((homTraj κ μ).map (Preorder.frestrictLe r) ⊗ₘ homFam κ r).map
          (fun p : ((i : ↥(Finset.Iic r)) → X) × X => appendFun p.1 p.2) := by
  haveI : ∀ n, IsMarkovKernel (homFam κ n) := fun n => homFam.instIsMarkovKernel κ n
  have hkey : (homTraj κ μ).map (Preorder.frestrictLe r) ⊗ₘ homFam κ r
      = (homTraj κ μ).map (fun x => (Preorder.frestrictLe r x, x (r + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => X) (μ₀ := μ) (κ := homFam κ) (a := r)
  have hpair : Measurable (fun x : ℕ → X => (Preorder.frestrictLe r x, x (r + 1))) := by
    fun_prop
  have hApp : Measurable (fun p : ((i : ↥(Finset.Iic r)) → X) × X => appendFun p.1 p.2) :=
    measurable_appendFun
  rw [hkey, Measure.map_map hApp hpair]
  exact Measure.map_congr (ae_of_all _ fun x => by
    simp only [Function.comp_apply]
    exact frestrictLe_succ_eq_appendFun x)


/-! ### Splitting a block tuple at its last block -/


/-- `Fin.snoc` unfolds at the head. -/
theorem snoc_eq_cons {n : ℕ} {β : Type*} (w : Fin (n + 1) → β) (a : β) :
    (@Fin.snoc (n+1) (fun _ => β) w a)
      = Fin.cons (w 0) (@Fin.snoc n (fun _ => β) (fun i => w i.succ) a) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero]; simp
  · intro j
    rw [Fin.cons_succ]
    simp only [Fin.snoc, Fin.val_succ]
    by_cases h : (j : ℕ) < n
    · rw [dif_pos (by omega), dif_pos (by omega)]
      rfl
    · rw [dif_neg (by omega), dif_neg (by omega)]

/-- The tail of a `Fin.snoc` is a `Fin.snoc`. -/
theorem snoc_tail {n : ℕ} {β : Type*} (w : Fin (n + 1) → β) (a : β) :
    (fun i : Fin (n+1) => (@Fin.snoc (n+1) (fun _ => β) w a) i.succ)
      = @Fin.snoc n (fun _ => β) (fun i => w i.succ) a := by
  rw [snoc_eq_cons w a]
  funext i
  rw [Fin.cons_succ]

/-- The head of a `Fin.snoc` is the head of the tuple. -/
theorem snoc_head {n : ℕ} {β : Type*} (w : Fin (n + 1) → β) (a : β) :
    (@Fin.snoc (n+1) (fun _ => β) w a) 0 = w 0 := by
  rw [snoc_eq_cons w a, Fin.cons_zero]

theorem snoc_zero_eq {β : Type*} (w : Fin 0 → β) (a : β) :
    ((@Fin.snoc 0 (fun _ => β) w a) : Fin 1 → β) = fun _ => a := by
  funext i
  have h : (i : ℕ) = 0 := by omega
  rw [show i = 0 from Fin.ext h]
  have hlast : (@Fin.snoc 0 (fun _ => β) w a) (Fin.last 0) = a :=
    @Fin.snoc_last 0 (fun _ => β) a w
  rw [show (Fin.last 0 : Fin 1) = 0 from Fin.ext rfl] at hlast
  exact hlast

theorem totLen_snoc (r : ℕ) (w : Fin r → Word N) (a : Word N) :
    totLen (r + 1) (Fin.snoc w a) = totLen r w + a.1 := by
  induction r with
  | zero =>
    rw [snoc_zero_eq, totLen_succ]
    simp [totLen]
  | succ r ih =>
    rw [totLen_succ, snoc_head, snoc_tail, ih, totLen_succ]
    omega

theorem runOutF_snoc (hm : 1 ≤ m) (r : ℕ) (y : RecState N m) (w : Fin r → Word N)
    (a : Word N) :
    runOutF hm y (r + 1) (Fin.snoc w a) = out hm a.2 (runOutF hm y r w) := by
  induction r generalizing y with
  | zero =>
    rw [snoc_zero_eq, runOutF_succ]
    simp [runOutF]
  | succ r ih =>
    rw [runOutF_succ, snoc_head, snoc_tail, ih, runOutF_succ]

theorem blockProdF_snoc (p : ℝ) (hm : 1 ≤ m) (r : ℕ) (y : RecState N m) (w : Fin r → Word N)
    (a : Word N) :
    blockProdF p hm y (r + 1) (Fin.snoc w a)
      = blockProdF p hm y r w * hitW p a.2 (runOutF hm y r w) := by
  induction r generalizing y with
  | zero =>
    rw [snoc_zero_eq, blockProdF_succ]
    simp [blockProdF, runOutF]
  | succ r ih =>
    rw [blockProdF_succ, snoc_head, snoc_tail, ih, blockProdF_succ, runOutF_succ, mul_assoc]

/-- The `Iic r`-indexed version of the partial block path. -/
noncomputable def pathIic (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) (w : Fin r → Word N) :
    (i : ↥(Finset.Iic r)) → RecState N m × ℕ :=
  fun i => pathOf hm y t r w ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

theorem pathIic_apply (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ) (w : Fin r → Word N)
    (i : ↥(Finset.Iic r)) :
    pathIic hm y t r w i = pathOf hm y t r w ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩ := rfl

/-- **Prefix property of the block path**: the first `r+1` coordinates of the `(r+1)`-block path
are the `r`-block path. -/
theorem pathOf_snoc_prefix (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (t : ℕ) (w : Fin r → Word N) (a : Word N) (i : Fin (r + 1)),
      pathOf hm y t (r + 1) (Fin.snoc w a) i.castSucc = pathOf hm y t r w i := by
  intro r
  induction r with
  | zero =>
    intro y t w a i
    have hi : (i : Fin 1) = 0 := Fin.ext (by omega)
    rw [show i = 0 from hi]
    rw [show (0 : Fin 1).castSucc = (0 : Fin 2) from rfl]
    rw [pathOf_succ, Fin.cons_zero]
    rfl
  | succ r ih =>
    intro y t w a i
    rw [snoc_eq_cons w a]
    cases i using Fin.cases with
    | zero =>
      rw [show (Fin.castSucc (0 : Fin (r + 2)) : Fin (r + 3)) = 0 from rfl]
      rw [pathOf_succ, Fin.cons_zero, pathOf_succ, Fin.cons_zero]
    | succ j =>
      rw [Fin.castSucc_succ, pathOf_succ, pathOf_succ]
      simp only [Fin.cons_succ]
      exact ih (out hm (w 0).2 y) (t + (w 0).1) (fun i => w i.succ) a j

/-- **Last-coordinate decomposition of the block path.** -/
theorem pathIic_snoc (hm : 1 ≤ m) (r : ℕ) (y : RecState N m) (t : ℕ) (w : Fin r → Word N)
    (a : Word N) :
    pathIic hm y t (r + 1) (Fin.snoc w a)
      = appendFun (pathIic hm y t r w)
          (out hm a.2 (runOutF hm y r w), t + totLen r w + a.1) := by
  funext i
  by_cases hi : (i : ℕ) ≤ r
  · rw [appendFun_apply_le _ _ _ hi, pathIic_apply, pathIic_apply]
    exact pathOf_snoc_prefix hm r y t w a ⟨i.1, Nat.lt_succ_of_le hi⟩
  · rw [appendFun_apply_gt _ _ _ hi, pathIic_apply]
    have hlast : (i : ℕ) = r + 1 := by
      have := i.2; simp only [Finset.mem_Iic] at this; omega
    rw [show (⟨(i : ℕ), Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩ : Fin (r + 2)) = Fin.last (r + 1)
      from Fin.ext hlast]
    rw [pathOf_last, endptF, runOutF_snoc, totLen_snoc, Nat.add_assoc]


/-! ### Elementary algebra of `Measure.sum` -/

section GenericSum

variable {α : Type*} [MeasurableSpace α]

/-- Reindexing a countable sum of measures along an equivalence. -/
theorem sum_measure_equiv {ι ι' : Type*} (e : ι ≃ ι') (f : ι' → Measure α) :
    Measure.sum (fun i => f (e i)) = Measure.sum f := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  exact Equiv.tsum_eq e (fun i' => f i' s)

/-- Pointwise equal families have equal `Measure.sum`. -/
theorem sum_measure_congr {ι : Type*} {μ ν : ι → Measure α} (h : ∀ i, μ i = ν i) :
    Measure.sum μ = Measure.sum ν := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  exact tsum_congr fun i => by rw [h i]

/-- A constant scalar pulls out of a countable sum of measures. -/
theorem sum_measure_smul {ι : Type*} (c : ℝ≥0∞) (μ : ι → Measure α) :
    Measure.sum (fun i => c • μ i) = c • Measure.sum μ := by
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul]
  rw [ENNReal.tsum_mul_left]

/-- A Dirac mass composed with a kernel. -/
theorem dirac_compProd_map {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (a : α) (η : Kernel α β) [IsSFiniteKernel η] :
    Measure.dirac a ⊗ₘ η = (η a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_dirac,
    Measure.map_apply measurable_prodMk_left hs]

end GenericSum

end M6Aggr
