/-`M5FirstBlock.mass_twoBlock_firstRecord` factorises the array mass of a *fixed* concatenation of
two prescribed first-record words into a product of two `hitW` weights.  This file pushes that
product formula to an arbitrary finite number `r` of blocks (`mass_jbox_concatF`), in the
tuple-indexed form `Fin r → Word N` that the `r`-fold iterate of the stopped record kernel is
indexed by.

Nothing here is a statement about the canonical record times `recTimeA` of the actual array, and
nothing here asserts `Swarm.Ballistic`, `RegenAvailable`, `MainClaim` or a common speed.
-/
import Swarm.ActualTwoBlock

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

/-! ### Tuples of finite jump words -/

/-- A finite jump word: its length together with the jumps.  An `abbrev` so that the tuple
types `Fin r → Word N` and `Fin r → ((k : ℕ) × (Fin k → JumpVec N))` are interchangeable. -/
abbrev Word (N : ℕ) : Type := (k : ℕ) × (Fin k → JumpVec N)

/-- A `Word` is a `ℕ`-indexed sigma of finite types, hence countable. -/
instance countableWord (N : ℕ) : Countable (Word N) := by
  unfold Word
  infer_instance

/-- The total number of jumps in a tuple of words. -/
noncomputable def totLen {N : ℕ} : (r : ℕ) → (Fin r → Word N) → ℕ
  | 0, _ => 0
  | r + 1, w => (w 0).1 + totLen r (fun i => w i.succ)

/-- The concatenation of a tuple of words, as a single word. -/
noncomputable def concatF {N : ℕ} :
    (r : ℕ) → (w : Fin r → Word N) → Fin (totLen r w) → JumpVec N
  | 0, _ => fun i => i.elim0
  | r + 1, w => catWord (w 0).2 (concatF r (fun i => w i.succ))

@[simp] theorem totLen_succ (r : ℕ) (w : Fin (r + 1) → Word N) :
    totLen (r + 1) w = (w 0).1 + totLen r (fun i => w i.succ) := rfl

@[simp] theorem concatF_succ (r : ℕ) (w : Fin (r + 1) → Word N) :
    concatF (r + 1) w = catWord (w 0).2 (concatF r (fun i => w i.succ)) := rfl

/-- The tail of a concatenated tuple is the concatenation of the tail. -/
theorem extJump_concatF_shift (r : ℕ) (w : Fin (r + 1) → Word N) :
    (fun t => extJump (totLen (r + 1) w) (concatF (r + 1) w) (t + (w 0).1))
      = extJump (totLen r (fun i => w i.succ)) (concatF r (fun i => w i.succ)) :=
  extJump_cat_shift (w 0).2 (concatF r (fun i => w i.succ))

/-- The head of a concatenated tuple is the first word. -/
theorem extJump_concatF_head (r : ℕ) (w : Fin (r + 1) → Word N) {t : ℕ}
    (ht : t < (w 0).1) :
    extJump (totLen (r + 1) w) (concatF (r + 1) w) t = extJump (w 0).1 (w 0).2 t :=
  extJump_cat_head (w 0).2 (concatF r (fun i => w i.succ)) ht

/-! ### The real-valued block factorisation of the chain's path weight -/

/-- **The path weight of a concatenation factors over the two blocks**, with the second factor
started from the state reached after the first block. -/
theorem pathW_cat (p : ℝ) (m : ℕ) {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N)
    (q₂ : Fin k₂ → JumpVec N) (s : SimJump.State N m) :
    pathW p (k₁ + k₂) (catWord q₁ q₂) s =
      pathW p k₁ q₁ s * pathW p k₂ q₂ (SimJump.evolveFun (extJump k₁ q₁) k₁ s) := by
  rw [pathW_eq_pathWFun_ext' p m (k₁ + k₂) (catWord q₁ q₂) s, pathWFun_add,
    extJump_cat_shift, evolveFun_cat_head,
    pathWFun_congr (m := m) p (u := extJump (k₁ + k₂) (catWord q₁ q₂))
      (u' := extJump k₁ q₁) (k := k₁) (fun t ht => extJump_cat_head q₁ q₂ ht) s,
    ← pathW_eq_pathWFun_ext' p m k₁ q₁ s,
    ← pathW_eq_pathWFun_ext' p m k₂ q₂ (SimJump.evolveFun (extJump k₁ q₁) k₁ s)]

/-! ### The running record state, the block weight and the first-record predicate

All three are defined by recursion on the number of blocks, so that the `r + 1` case is
*definitionally* the head block followed by the tail tuple. -/

/-- The compact record state reached after the first `r` blocks of a tuple. -/
noncomputable def runOutF {N : ℕ} {m : ℕ} (hm : 1 ≤ m) :
    (y : RecState N m) → (r : ℕ) → (Fin r → Word N) → RecState N m
  | y, 0, _ => y
  | y, r + 1, w => runOutF hm (out hm (w 0).2 y) r (fun i => w i.succ)

/-- The product of the stopped record weights of the blocks of a tuple. -/
noncomputable def blockProdF {N : ℕ} {m : ℕ} (p : ℝ) (hm : 1 ≤ m) :
    (y : RecState N m) → (r : ℕ) → (Fin r → Word N) → ℝ
  | y, 0, _ => 1
  | y, r + 1, w => hitW p (w 0).2 y * blockProdF p hm (out hm (w 0).2 y) r
      (fun i => w i.succ)

/-- Every block of the tuple is a first-record path from the running record state. -/
def FRChainF {N : ℕ} {m : ℕ} (hm : 1 ≤ m) :
    (y : RecState N m) → (r : ℕ) → (Fin r → Word N) → Prop
  | y, 0, _ => True
  | y, r + 1, w => Record.FirstRecord (Record.extendPath (w 0).2) (w 0).1
        (Record.ofRecState y) ∧
      FRChainF hm (out hm (w 0).2 y) r (fun i => w i.succ)

@[simp] theorem runOutF_succ {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (w : Fin (r + 1) → Word N) :
    runOutF hm y (r + 1) w = runOutF hm (out hm (w 0).2 y) r (fun i => w i.succ) := rfl

@[simp] theorem blockProdF_succ {m : ℕ} (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (w : Fin (r + 1) → Word N) :
    blockProdF p hm y (r + 1) w
      = hitW p (w 0).2 y * blockProdF p hm (out hm (w 0).2 y) r (fun i => w i.succ) := rfl

theorem frChainF_succ {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (w : Fin (r + 1) → Word N) :
    FRChainF hm y (r + 1) w ↔
      Record.FirstRecord (Record.extendPath (w 0).2) (w 0).1 (Record.ofRecState y) ∧
        FRChainF hm (out hm (w 0).2 y) r (fun i => w i.succ) :=
  Iff.rfl

/-! ### The `r`-block path-weight factorisation -/

/-- **The path weight of a concatenated tuple is the product of the blocks' stopped record
weights**, for every `r`, provided each block is a first-record path from the running state. -/
theorem pathW_concatF (p : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (w : Fin r → Word N), FRChainF hm y r w →
      pathW p (totLen r w) (concatF r w) (Record.ofRecState y) = blockProdF p hm y r w := by
  intro r
  induction r with
  | zero => intro y w _; rfl
  | succ r ih =>
      intro y w hFR
      obtain ⟨h0, hrest⟩ := (frChainF_succ hm y r w).mp hFR
      show pathW p ((w 0).1 + totLen r (fun i => w i.succ))
          (catWord (w 0).2 (concatF r (fun i => w i.succ))) (Record.ofRecState y)
        = blockProdF p hm y (r + 1) w
      rw [pathW_cat, blockProdF_succ,
        hitW_of_firstRecord p (w 0).2 y h0,
        ← pathW_normalize p m (totLen r (fun i => w i.succ)) (concatF r (fun i => w i.succ))
          (SimJump.evolveFun (extJump (w 0).1 (w 0).2) (w 0).1 (Record.ofRecState y)),
        show Record.normalize (SimJump.evolveFun (extJump (w 0).1 (w 0).2) (w 0).1
            (Record.ofRecState y)) = Record.ofRecState (out hm (w 0).2 y) from by
          rw [extJump_eq_extendPath, ← ofRecState_out hm (w 0).2 y h0],
        ih (out hm (w 0).2 y) (fun i => w i.succ) hrest]

/-- **The exact actual-array mass of an `r`-block concatenation** is the product of the blocks'
stopped record weights, at the compatible start law `zeroState`. -/
theorem mass_jbox_concatF {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (r : ℕ) (w : Fin r → Word N)
    (hFR : FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w) :
    arrayMeasure N (jbox p m (totLen r w) (concatF r w))
      = ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w) := by
  rw [mass_jbox_pathW hp0 hp1 m (totLen r w) (concatF r w),
    ← ofRecState_zeroState m hm,
    pathW_concatF p hm r (SwarmRecordMeas.StartLaw.zeroState hm) w hFR]

/-! ### The endpoint of a tuple of blocks, and its `Fin.cons` recursion -/

/-- The stopped-record state and record time after the tuple's blocks. -/
noncomputable def endptF {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    (w : Fin r → Word N) : RecState N m × ℕ :=
  (runOutF hm y r w, t + totLen r w)

@[simp] theorem totLen_cons (r : ℕ) (a : Word N) (w : Fin r → Word N) :
    totLen (r + 1) (Fin.cons a w) = a.1 + totLen r w := by
  rw [totLen_succ]; simp

@[simp] theorem runOutF_cons {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (a : Word N) (w : Fin r → Word N) :
    runOutF hm y (r + 1) (Fin.cons a w) = runOutF hm (out hm a.2 y) r w := by
  rw [runOutF_succ]
  have h0 : (Fin.cons a w : Fin (r + 1) → Word N) 0 = a := by simp
  have hs : (fun i : Fin r => (Fin.cons a w : Fin (r + 1) → Word N) i.succ) = w := by
    funext i
    simp
  rw [h0, hs]

@[simp] theorem blockProdF_cons {m : ℕ} (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) (r : ℕ)
    (a : Word N) (w : Fin r → Word N) :
    blockProdF p hm y (r + 1) (Fin.cons a w)
      = hitW p a.2 y * blockProdF p hm (out hm a.2 y) r w := by
  rw [blockProdF_succ]
  have h0 : (Fin.cons a w : Fin (r + 1) → Word N) 0 = a := by simp
  have hs : (fun i : Fin r => (Fin.cons a w : Fin (r + 1) → Word N) i.succ) = w := by
    funext i
    simp
  rw [h0, hs]

@[simp] theorem endptF_cons {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) (r : ℕ)
    (a : Word N) (w : Fin r → Word N) :
    endptF hm y t (r + 1) (Fin.cons a w)
      = (runOutF hm (out hm a.2 y) r w, (t + a.1) + totLen r w) := by
  simp only [endptF, totLen_cons, runOutF_cons]
  rw [Nat.add_assoc]

/-- Definition audit: the two-block weight is exactly the product of
`M5FirstBlock.mass_twoBlock_firstRecord`, i.e. `hitW p q₁ y₀ * hitW p q₂ (out hm q₁ y₀)`. -/
theorem blockProdF_two {m : ℕ} (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) (a b : Word N) :
    blockProdF p hm y 2 (Fin.cons a (Fin.cons b (fun i : Fin 0 => i.elim0)))
      = hitW p a.2 y * hitW p b.2 (out hm a.2 y) := by
  show blockProdF p hm y (1 + 1) (Fin.cons a (Fin.cons b (fun i : Fin 0 => i.elim0)))
      = hitW p a.2 y * hitW p b.2 (out hm a.2 y)
  rw [blockProdF_cons, blockProdF_cons]
  show hitW p a.2 y * (hitW p b.2 (out hm a.2 y) * 1)
      = hitW p a.2 y * hitW p b.2 (out hm a.2 y)
  rw [mul_one]

/-! ### Kernel-algebra lemmas for the lifted stopped record chain -/

open SwarmKB in
/-- One step of a kernel through a countable sum of measures. -/
theorem step_sum {X : Type*} [MeasurableSpace X] (κ : Kernel X X) {ι : Type*}
    (g : ι → Measure X) :
    step κ (Measure.sum g) = Measure.sum (fun i => step κ (g i)) :=
  Measure.bind_sum g ⇑κ (Kernel.aemeasurable κ)

open SwarmKB in
/-- One step of a kernel applied to a Dirac mass. -/
theorem step_dirac {X : Type*} [MeasurableSpace X] (κ : Kernel X X) (a : X) :
    step κ (Measure.dirac a) = κ a :=
  Measure.dirac_bind (Kernel.measurable κ) a

open SwarmKB in
/-- **Linearity of the iterated kernel in a countable sum of weighted Dirac masses.** -/
theorem step_iterate_sum_dirac {X : Type*} [MeasurableSpace X] (κ : Kernel X X) (r : ℕ)
    {ι : Type*} (c : ι → ℝ≥0∞) (z : ι → X) :
    (step κ)^[r] (Measure.sum (fun i => c i • Measure.dirac (z i)))
      = Measure.sum (fun i => c i • (step κ)^[r] (Measure.dirac (z i))) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, step_sum]
      simp only [step_smul, Function.iterate_succ_apply']

/-! ### The `r`-block aggregation identity

The `r`-fold iterate of the lifted stopped record kernel from the Dirac law at `(y, t)` is the
sum, over *all* `r`-tuples of finite words, of the product of the stopped record weights — with
the word tuple carrying zero weight unless every block is a first-record path from the running
record state.  This is the countable-sum (kernel-iterate) side of the record-law identification;
it is **not** a statement about the actual array, and in particular it does not assert
`Bridge.JointLawIdentity`. -/
theorem step_iterate_dirac_apply (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (t : ℕ) {A : Set (RecState N m × ℕ)}, MeasurableSet A →
      ((SwarmKB.step (hitKKernelT p hm))^[r] (Measure.dirac (y, t))) A
        = ∑' w : Fin r → Word N,
            ENNReal.ofReal (blockProdF p hm y r w) *
              (if endptF hm y t r w ∈ A then 1 else 0) := by
  intro r
  induction r with
  | zero =>
      intro y t A hA
      have hterm : ∀ w : Fin 0 → Word N,
          ENNReal.ofReal (blockProdF p hm y 0 w) *
              (if endptF hm y t 0 w ∈ A then 1 else 0)
            = (if ((y, t) : RecState N m × ℕ) ∈ A then 1 else 0) := by
        intro w
        show ENNReal.ofReal (1 : ℝ) * (if ((y, t) : RecState N m × ℕ) ∈ A then 1 else 0)
          = (if ((y, t) : RecState N m × ℕ) ∈ A then 1 else 0)
        rw [ENNReal.ofReal_one, one_mul]
      rw [Function.iterate_zero_apply, Measure.dirac_apply' _ hA,
        tsum_eq_single (Classical.arbitrary (Fin 0 → Word N))
          (fun b hb => absurd (Subsingleton.elim b _) hb), hterm,
        Set.indicator_apply]
      simp
  | succ r ih =>
      intro y t A hA
      have hz : SwarmKB.step (hitKKernelT p hm) (Measure.dirac (y, t))
          = Measure.sum (fun a : Word N =>
              ENNReal.ofReal (hitW p a.2 y) • Measure.dirac (out hm a.2 y, t + a.1)) := by
        rw [step_dirac, hitKKernelT_apply]
        rfl
      rw [Function.iterate_succ_apply, hz, step_iterate_sum_dirac, Measure.sum_apply _ hA]
      simp only [Measure.smul_apply, smul_eq_mul]
      have hstep : ∀ a : Word N,
          ((SwarmKB.step (hitKKernelT p hm))^[r]
              (Measure.dirac (out hm a.2 y, t + a.1))) A
            = ∑' w : Fin r → Word N,
                ENNReal.ofReal (blockProdF p hm (out hm a.2 y) r w) *
                  (if endptF hm (out hm a.2 y) (t + a.1) r w ∈ A then 1 else 0) :=
        fun a => ih (out hm a.2 y) (t + a.1) hA
      simp only [hstep, ← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_prod]
      rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ => Word N))
        (fun w' => ENNReal.ofReal (blockProdF p hm y (r + 1) w') *
          (if endptF hm y t (r + 1) w' ∈ A then 1 else 0))]
      refine tsum_congr fun u => ?_
      obtain ⟨a, w⟩ := u
      show ENNReal.ofReal (hitW p a.2 y) *
            (ENNReal.ofReal (blockProdF p hm (out hm a.2 y) r w) *
              (if endptF hm (out hm a.2 y) (t + a.1) r w ∈ A then 1 else 0))
          = ENNReal.ofReal (blockProdF p hm y (r + 1) (Fin.cons a w)) *
              (if endptF hm y t (r + 1) (Fin.cons a w) ∈ A then 1 else 0)
      simp only [endptF, blockProdF_cons, runOutF_cons, totLen_cons, Nat.add_assoc]
      rw [ENNReal.ofReal_mul (hitW_nonneg p hp0.le hp1.le a.2 y), mul_assoc]

/-! ### The actual array's block boxes: aggregation against the kernel iterate

The countable-sum step that turns the per-block factorisation `mass_jbox_concatF` into the
`r`-fold iterate of the lifted stopped record kernel.  Nothing here identifies the array's own
record statistics with the block endpoints: `joint_law_of_block_decomposition` takes the two
geometric inputs (pairwise disjointness of the block boxes, and their almost sure covering) as
explicit hypotheses, and `joint_law_of_block_stat` additionally takes the identification of the
array statistic with the block endpoints.  The first of the three is proved outright at `r = 1`
by `M5FirstBlock.jbox_disjoint`; for `r ≥ 2` they are the residual geometric inputs. -/

/-- Off a first-record chain the block weight vanishes. -/
theorem blockProdF_eq_zero_of_not_frChain (p : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ (r : ℕ) (y : RecState N m) (w : Fin r → Word N), ¬ FRChainF hm y r w →
      blockProdF p hm y r w = 0 := by
  intro r
  induction r with
  | zero => intro y w h; exact absurd trivial h
  | succ r ih =>
      intro y w h
      rw [blockProdF_succ]
      have h' : ¬ (Record.FirstRecord (Record.extendPath (w 0).2) (w 0).1
          (Record.ofRecState y) ∧ FRChainF hm (out hm (w 0).2 y) r (fun i => w i.succ)) :=
        fun hc => h ((frChainF_succ hm y r w).mpr hc)
      rcases not_and_or.mp h' with h | h
      · rw [hitW_of_not_firstRecord p (w 0).2 y h, zero_mul]
      · rw [ih (out hm (w 0).2 y) (fun i => w i.succ) h, mul_zero]

/-- A `tsum` over a subtype whose integrand vanishes outside equals the unrestricted `tsum`. -/
theorem tsum_subtype_eq_of_eq_zero {α : Type*} (s : Set α) (f : α → ℝ≥0∞)
    (h : ∀ x, x ∉ s → f x = 0) : ∑' x : s, f x = ∑' x, f x := by
  rw [tsum_subtype]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [h x hx, Set.indicator_of_notMem hx]

/-- **The block masses aggregate to the kernel iterate.**  Summing the exact actual-array mass of
every first-record `r`-block box against a measurable test set `A` of the stopped record state
space gives the `r`-fold iterate of `hitKKernelT` from `(zeroState, 0)`.

This is unconditional: it is a statement about the *masses* of the block boxes, not about the
array's own record statistics. -/
theorem tsum_block_mass_eq_iterate {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (r : ℕ) {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    ∑' w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        arrayMeasure N (jbox p m (totLen r w.1) (concatF r w.1)) *
            (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0)
      = ((SwarmKB.step (hitKKernelT p hm))^[r]
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState hm, 0))) A := by
  classical
  -- replace each block mass by the `hitW` product
  have hterm : ∀ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      arrayMeasure N (jbox p m (totLen r w.1) (concatF r w.1)) *
          (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0)
        = ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w.1) *
          (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A then 1 else 0) :=
    fun w => by rw [mass_jbox_concatF hp0 hp1 hm r w.1 w.2]
  refine Eq.trans (tsum_congr hterm) ?_
  -- extend the sum to all word tuples, where the weight vanishes
  refine Eq.trans (tsum_subtype_eq_of_eq_zero
    {w : Fin r → Word N | FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}
    (fun w => ENNReal.ofReal (blockProdF p hm (SwarmRecordMeas.StartLaw.zeroState hm) r w) *
      (if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w ∈ A then 1 else 0))
    (fun w hw => ?_)) ?_
  · rw [blockProdF_eq_zero_of_not_frChain p hm r
      (SwarmRecordMeas.StartLaw.zeroState hm) w hw, ENNReal.ofReal_zero, zero_mul]
  · exact (step_iterate_dirac_apply (N := N) p hp0 hp1 hm r
      (SwarmRecordMeas.StartLaw.zeroState hm) 0 hA).symm

/-- The piece of the array space on which the `r`-block box of `w` is followed and the record
endpoint of `w` falls in `A`. -/
noncomputable def blockPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (t : ℕ)
    (A : Set (RecState N m × ℕ)) (w : Fin r → Word N) : Set (Array N) :=
  if endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) t r w ∈ A
    then jbox p m (totLen r w) (concatF r w) else ∅

theorem measurableSet_blockPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (t : ℕ)
    {A : Set (RecState N m × ℕ)} (w : Fin r → Word N) :
    MeasurableSet (blockPiece (N := N) p hm r t A w) := by
  classical
  unfold blockPiece
  split
  · exact measurableSet_jbox p m (totLen r w) (concatF r w)
  · exact MeasurableSet.empty

/-- **The `r`-block box aggregation at the actual array.**  If the first-record `r`-block boxes
are pairwise disjoint — a deterministic geometric statement, proved by
`M5FirstBlock.jbox_disjoint` at `r = 1` — then the actual array probability that the block
decomposition exists with endpoint in `A` is exactly the iterate value. -/
theorem joint_law_of_block_decomposition {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (r : ℕ)
    (hdisj : Pairwise (fun w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (jbox p m (totLen r w.1) (concatF r w.1))
        (jbox p m (totLen r w'.1) (concatF r w'.1))))
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        U ∈ jbox p m (totLen r w.1) (concatF r w.1) ∧
          endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A}
      = ((SwarmKB.step (hitKKernelT p hm))^[r]
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState hm, 0))) A := by
  classical
  have hset : {U : Array N | ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        U ∈ jbox p m (totLen r w.1) (concatF r w.1) ∧
          endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A}
      = ⋃ w : {w : Fin r → Word N //
          FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
          blockPiece (N := N) p hm r 0 A w.1 := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, blockPiece]
    constructor
    · rintro ⟨w, hU, hmem⟩
      exact ⟨w, by rw [if_pos hmem]; exact hU⟩
    · rintro ⟨w, hw⟩
      by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
      · rw [if_pos hmem] at hw
        exact ⟨w, hw, hmem⟩
      · rw [if_neg hmem] at hw
        exact absurd hw (Set.notMem_empty U)
  have hdisj' : ∀ w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}, w ≠ w' →
      Disjoint (jbox p m (totLen r w.1) (concatF r w.1))
        (jbox p m (totLen r w'.1) (concatF r w'.1)) := hdisj
  have hdisjg : Pairwise (fun w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (blockPiece (N := N) p hm r 0 A w.1) (blockPiece (N := N) p hm r 0 A w'.1)) := by
    intro w w' hne
    simp only [blockPiece]
    by_cases hw : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
    · by_cases hw' : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_pos hw, if_pos hw']
        exact hdisj' w w' hne
      · rw [if_pos hw, if_neg hw']
        exact disjoint_bot_right
    · by_cases hw' : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w'.1 ∈ A
      · rw [if_neg hw, if_pos hw']
        exact disjoint_bot_left
      · rw [if_neg hw, if_neg hw']
        exact disjoint_bot_right
  rw [hset, measure_iUnion hdisjg
    (fun w => measurableSet_blockPiece (N := N) (A := A) p hm r 0 w.1)]
  refine Eq.trans (tsum_congr (fun w => ?_)) (tsum_block_mass_eq_iterate hp0 hp1 hm r hA)
  simp only [blockPiece]
  by_cases hmem : endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
  · rw [if_pos hmem, if_pos hmem, mul_one]
  · rw [if_neg hmem, if_neg hmem, measure_empty, mul_zero]

/-- **The joint law of the `r`-block record statistic, given the geometric block decomposition.**
If a statistic `S` of the actual array is the block endpoint on every first-record `r`-block box,
and those boxes cover almost every array, then the law of `S` is the `r`-fold iterate of the
lifted stopped record kernel from `(zeroState, 0)`.

The two geometric inputs (`hdisj`, `hcover`) and the identification `hS` are the residual
geometry; the countable aggregation is `joint_law_of_block_decomposition`. -/
theorem joint_law_of_block_stat {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) (r : ℕ)
    (hdisj : Pairwise (fun w w' : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w} =>
      Disjoint (jbox p m (totLen r w.1) (concatF r w.1))
        (jbox p m (totLen r w'.1) (concatF r w'.1))))
    (hcover : ∀ᵐ U ∂(arrayMeasure N), ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
      U ∈ jbox p m (totLen r w.1) (concatF r w.1))
    (S : Array N → RecState N m × ℕ)
    (hS : ∀ (w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w}) (U : Array N),
      U ∈ jbox p m (totLen r w.1) (concatF r w.1) →
        S U = endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1)
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | S U ∈ A}
      = ((SwarmKB.step (hitKKernelT p hm))^[r]
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState hm, 0))) A := by
  classical
  have hcongr : {U : Array N | S U ∈ A} =ᵐ[arrayMeasure N]
      {U : Array N | ∃ w : {w : Fin r → Word N //
        FRChainF hm (SwarmRecordMeas.StartLaw.zeroState hm) r w},
        U ∈ jbox p m (totLen r w.1) (concatF r w.1) ∧
          endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A} := by
    filter_upwards [hcover] with U hU
    apply propext
    constructor
    · intro hSA
      obtain ⟨w, hw⟩ := hU
      refine ⟨w, hw, ?_⟩
      show endptF hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 r w.1 ∈ A
      rw [← hS w U hw]
      show S U ∈ A
      exact hSA
    · rintro ⟨w, hw, hmem⟩
      show S U ∈ A
      rw [hS w U hw]
      exact hmem
  rw [measure_congr hcongr]
  exact joint_law_of_block_decomposition hp0 hp1 hm r hdisj hA

end M6Aggr
