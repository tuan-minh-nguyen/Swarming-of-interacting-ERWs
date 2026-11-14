/-
# The stopped next-record probability kernel of the record chain

This file constructs the *stopped record law* `P(y,·)` of §3.1 of
`main_1d_revised.tex` ("we stop when the maximum position first reaches `1`") for the
capped-step chain of `SimJumpCore`/`SimJumpPath`, in the compact record-state coordinates of
`Swarm/RecordState.lean`, using the normalized first-record state
`SimJump.Record.toRecState` of `Swarm/Bridge.lean`.

Objects:

* `hitW p q y` : the mass of the finite path `q` in the stopped record law started at `y`,
  zero when `q` is not a first-record path (junk-free: non-record paths carry no mass);
* `hitK p hm L y` : the stopped record measure at horizon `L`, a genuine **Borel finite kernel**
  `RecState N m → Measure (RecState N m)` (see `hitKernel`), whose total mass is the
  probability that a record occurs by time `L` (`hitK_univ`), with the paper's transition
  weights and the compact record state at the stopping time as atom (`hitK_apply`);
* `hitMass`, `srMass` : the real-valued path sums;
* `hitFMass_le_srMass`, `hitK_srSet_ge` : **eq. (force) on the kernel**, i.e.
  `(1-p)^(N(2K+1)) ≤ P(y, F)` for every `y` with `max_i d_i ≤ K`, where `F = srSet` is the set
  of simultaneous-record states.  This is exactly the `hforce` input of
  `SwarmRec.exists_invariant_measure_pos_srSet` in the paper's Prop. "front".

Explicitly *not* claimed here: the total mass of `hitK p hm L y` is `1`.  Its value is
`ENNReal.ofReal (hitMass p L y)`, the probability that the record time is `≤ L`; the remaining
input of the paper's proof of Prop. "front" is the almost-sure finiteness of the record time
(`∀ y, hitMass p L y → 1`), which the paper obtains from recurrence of the simple symmetric walk
via common jump uniforms.  See `README.md` for the exact statement and integration notes.
-/
import Swarm.RecordKernel.Measurable

open MeasureTheory ProbabilityTheory
open Classical
open scoped ENNReal

namespace SimJump.RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### Finite sums of measures -/

theorem finset_sum_measure_apply {ι α : Type*} [MeasurableSpace α] (t : Finset ι)
    (f : ι → Measure α) (s : Set α) : (∑ i ∈ t, f i) s = ∑ i ∈ t, f i s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, Measure.add_apply, ih]

/-! ### The stopped path weights -/

/-- Weight of the finite path `q` in the stopped record law started at the record state `y`.
Non-first-record paths carry weight `0`, so the junk value of `out` never contributes mass. -/
noncomputable def hitW (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m) : ℝ := by
  classical
  exact if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y) then
    pathW p k q (Record.ofRecState y) else 0

lemma hitW_of_firstRecord (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m)
    (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    hitW p q y = pathW p k q (Record.ofRecState y) := by
  classical
  rw [hitW]
  exact dif_pos h

lemma hitW_of_not_firstRecord (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m)
    (h : ¬ Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    hitW p q y = 0 := by
  classical
  rw [hitW]
  exact dif_neg h

theorem hitW_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m) : 0 ≤ hitW p q y := by
  classical
  rw [hitW]
  split
  · exact pathW_nonneg p hp hp1 k q _
  · exact le_rfl

theorem measurable_hitW (p : ℝ) (k : ℕ) (q : Fin k → JumpVec N) :
    Measurable (hitW (m := m) p q) := by
  classical
  have hEq : (hitW (m := m) p q : RecState N m → ℝ) =
      (fun y => if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
        then pathW p k q (Record.ofRecState y) else 0) := rfl
  rw [hEq]
  exact Measurable.ite (measurableSet_firstRecord k q) (measurable_pathW p k q) measurable_const

/-! ### The stopped next-record measure -/

/-- The stopped record measure at horizon `L`: the law of the compact record state at the first
record time, with the junk-free convention that paths without a record before time `L` carry
zero mass.  Its total mass (`hitK_univ`) is the probability that the record occurs by time `L`. -/
noncomputable def hitK (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m) :
    Measure (RecState N m) :=
  ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
    ENNReal.ofReal (hitW p q y) • Measure.dirac (out hm q y)

lemma hitK_apply (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m) {A : Set (RecState N m)}
    (hA : MeasurableSet A) :
    hitK p hm L y A = ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
      ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ A then 1 else 0) := by
  classical
  rw [hitK, finset_sum_measure_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [finset_sum_measure_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  simp only [Set.indicator_apply, Pi.one_apply]

lemma hitK_mono_horizon (p : ℝ) (hm : 1 ≤ m) {L L' : ℕ} (hLL : L ≤ L') (y : RecState N m)
    {A : Set (RecState N m)} (hA : MeasurableSet A) : hitK p hm L y A ≤ hitK p hm L' y A := by
  rw [hitK_apply p hm L y hA, hitK_apply p hm L' y hA]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) ?_
  intro k _ _
  exact Finset.sum_nonneg fun q _ => bot_le

/-- The real-valued total mass of the horizon-`L` stopped record law. -/
noncomputable def hitMass (p : ℝ) (L : ℕ) (y : RecState N m) : ℝ :=
  ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N, hitW p q y

/-- **Total mass of the stopped record law at horizon `L`.**  It is the probability that the
record time is at most `L`; the paper's "`P` is well defined" is exactly the statement that this
tends to `1`. -/
theorem hitK_univ (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (y : RecState N m) :
    hitK p hm L y Set.univ = ENNReal.ofReal (hitMass p L y) := by
  classical
  rw [hitK_apply p hm L y MeasurableSet.univ, hitMass,
    ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hitW_nonneg p hp hp1 q y)]
    exact Finset.sum_congr rfl fun q _ => by simp
  · exact fun k _ => Finset.sum_nonneg fun q _ => hitW_nonneg p hp hp1 q y

theorem hitK_univ_lt_top (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (y : RecState N m) : hitK p hm L y Set.univ < ⊤ := by
  rw [hitK_univ p hp hp1 hm L y]
  exact ENNReal.ofReal_lt_top

/-- **The stopped record measure is a Borel measurable function of the starting state.** -/
theorem measurable_hitK (p : ℝ) (hm : 1 ≤ m) (L : ℕ) :
    Measurable (hitK (N := N) (m := m) p hm L) := by
  classical
  refine Measure.measurable_of_measurable_coe (fun y : RecState N m => hitK p hm L y)
    fun A hA => ?_
  have hEq : (fun y : RecState N m => hitK p hm L y A) =
      (fun y => ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
        ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ A then 1 else 0)) := by
    funext y
    exact hitK_apply p hm L y hA
  rw [hEq]
  refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun q _ => ?_
  exact (ENNReal.measurable_ofReal.comp (measurable_hitW p k q)).mul
    (Measurable.ite ((measurable_out hm k q) hA) measurable_const measurable_const)

/-- **The stopped record kernel** (finite-horizon form) as a genuine Borel measurable kernel on
the compact record-state space. -/
noncomputable def hitKernel (p : ℝ) (hm : 1 ≤ m) (L : ℕ) :
    Kernel (RecState N m) (RecState N m) :=
  Kernel.mk (hitK p hm L) (measurable_hitK p hm L)

lemma hitKernel_apply (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m) :
    hitKernel p hm L y = hitK p hm L y := rfl

/-- A single finite path weight is at most one. -/
theorem pathW_le_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (q : Fin k → JumpVec N)
    (s : State N m) : pathW p k q s ≤ 1 := by
  have hsum := sum_pathW_one (m := m) p k s
  have hle : pathW p k q s ≤ ∑ q' : Fin k → JumpVec N, pathW p k q' s :=
    Finset.single_le_sum (fun q' _ => pathW_nonneg p hp hp1 k q' s) (Finset.mem_univ q)
  simpa [hsum] using hle

theorem hitW_le_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m) : hitW p q y ≤ 1 := by
  classical
  rw [hitW]
  split
  · exact pathW_le_one p hp hp1 k q _
  · norm_num

/-- A crude uniform bound on the horizon-`L` stopped-record mass: at most `1` per path of
length `k ≤ L`, and there are `(2^N)^k` such paths. -/
noncomputable def hitMassBound (N L : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (L + 1), (2 : ℝ) ^ (N * k)

theorem hitMass_le_bound (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (L : ℕ) (y : RecState N m) :
    hitMass p L y ≤ hitMassBound N L := by
  rw [hitMass, hitMassBound]
  refine Finset.sum_le_sum fun k _ => ?_
  have hcard : (Fintype.card (Fin k → JumpVec N) : ℝ) = (2 : ℝ) ^ (N * k) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have hJ : Fintype.card (JumpVec N) = 2 ^ N := by simp [JumpVec]
    rw [hJ, ← pow_mul]
    push_cast
    ring
  calc ∑ q : Fin k → JumpVec N, hitW p q y ≤ ∑ _q : Fin k → JumpVec N, (1 : ℝ) :=
        Finset.sum_le_sum fun q _ => hitW_le_one p hp hp1 q y
    _ = (2 : ℝ) ^ (N * k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact hcard

/-- **The stopped record kernel is a finite kernel**: a uniform bound on its total mass on the
compact exhaustion is given by `hitMassBound`. -/
theorem isFiniteKernel_hitKernel (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (L : ℕ) : IsFiniteKernel (hitKernel (N := N) (m := m) p hm L) :=
  ⟨ENNReal.ofReal (hitMassBound N L), ENNReal.ofReal_lt_top, fun y => by
    rw [hitKernel_apply, hitK_univ p hp hp1 hm L y]
    exact ENNReal.ofReal_mono (hitMass_le_bound p hp hp1 L y)⟩

/-! ### Eq. (force) on the stopped record kernel -/

/-- The mass the `k`-step term of `hitK` puts on the simultaneous-record set `F = srSet`. -/
noncomputable def srMass (p : ℝ) (hm : 1 ≤ m) (k : ℕ) (y : RecState N m) : ℝ :=
  ∑ q : Fin k → JumpVec N, hitW p q y * (if out hm q y ∈ srSet N m then (1 : ℝ) else 0)

/-- **Every simultaneous-record path contributes its full `pathW` weight to `srMass`.**  Hence the
prescribed-path mass `hitFMass` of `Swarm/Force.lean` is dominated by the `srSet`
mass of the stopped record law. -/
theorem hitFMass_le_srMass (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (hN : 0 < N) (k : ℕ) (y : RecState N m) :
    hitFMass p k (Record.ofRecState y) ≤ srMass p hm k y := by
  classical
  rw [hitFMass, srMass]
  refine Finset.sum_le_sum fun q _ => ?_
  by_cases hq : HitsFAt q (Record.ofRecState y)
  · rw [if_pos hq, hitW_of_firstRecord p q y
      (Record.firstRecord_extendPath hN q (Record.ofRecState y) hq),
      if_pos (out_mem_srSet hm hN q y hq), mul_one, one_mul]
  · rw [if_neg hq, zero_mul]
    exact mul_nonneg (hitW_nonneg p hp hp1 q y) (by
      by_cases hmem : out hm q y ∈ srSet N m <;> simp [hmem])

/-- **Prop. "front", eq. (force), on the stopped record kernel.**  From every record state with
`max_i d_i ≤ K`, the probability that the next record state is a simultaneous record
(`F = srSet`) is at least `(1-p)^(N(2K+1))`, uniformly in the horizon `L ≥ 2K+1`. -/
theorem hitK_srSet_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (K L : ℕ) (hL : 2 * K + 1 ≤ L) (y : RecState N m) (hy : y ∈ exh N m K) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) ≤ hitK p hm L y (srSet N m) := by
  classical
  rw [hitK_apply p hm L y (measurableSet_srSet N m)]
  have hstep : (∑ q : Fin (2 * K + 1) → JumpVec N,
      ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ srSet N m then 1 else 0)) =
      ENNReal.ofReal (srMass p hm (2 * K + 1) y) := by
    rw [srMass, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [ENNReal.ofReal_mul (hitW_nonneg p hp hp1 q y)]
      congr 1
      by_cases hmem : out hm q y ∈ srSet N m <;> simp [hmem]
    · exact fun q _ => mul_nonneg (hitW_nonneg p hp hp1 q y) (by
        by_cases hmem : out hm q y ∈ srSet N m <;> simp [hmem])
  calc ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))
      ≤ ENNReal.ofReal (hitFMass p (2 * K + 1) (Record.ofRecState y)) :=
        ENNReal.ofReal_mono (Record.hitFMass_ge_recState hp hp1 K y hy)
    _ ≤ ENNReal.ofReal (srMass p hm (2 * K + 1) y) :=
        ENNReal.ofReal_mono (hitFMass_le_srMass p hp hp1 hm hN (2 * K + 1) y)
    _ = ∑ q : Fin (2 * K + 1) → JumpVec N,
          ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ srSet N m then 1 else 0) := hstep.symm
    _ ≤ ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
          ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ srSet N m then 1 else 0) := by
        refine Finset.single_le_sum (f := fun k => ∑ q : Fin k → JumpVec N,
          ENNReal.ofReal (hitW p q y) * (if out hm q y ∈ srSet N m then 1 else 0))
          (fun k _ => Finset.sum_nonneg fun q _ => bot_le) (Finset.mem_range.mpr (by omega))

/-! ### Consequences for the paper's inputs -/

theorem srMass_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (k : ℕ)
    (y : RecState N m) : 0 ≤ srMass p hm k y :=
  Finset.sum_nonneg fun q _ => mul_nonneg (hitW_nonneg p hp hp1 q y) (by
    by_cases hmem : out hm q y ∈ srSet N m <;> simp [hmem])

theorem srMass_le_hitMass (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (y : RecState N m) :
    (∑ k ∈ Finset.range (L + 1), srMass p hm k y) ≤ hitMass p L y := by
  rw [hitMass]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [srMass]
  refine Finset.sum_le_sum fun q _ => ?_
  by_cases hmem : out hm q y ∈ srSet N m
  · rw [if_pos hmem, mul_one]
  · rw [if_neg hmem, mul_zero]
    exact hitW_nonneg p hp hp1 q y

/-- The force bound, in real-valued path-sum form: the total `srSet` mass of the terms with
horizon `k ≤ L` is at least `(1-p)^(N(2K+1))` from every state of `exh N m K`. -/
theorem force_le_srMassSum (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (K L : ℕ) (hL : 2 * K + 1 ≤ L) (y : RecState N m) (hy : y ∈ exh N m K) :
    (1 - p) ^ (N * (2 * K + 1)) ≤ ∑ k ∈ Finset.range (L + 1), srMass p hm k y := by
  have h1 : (1 - p) ^ (N * (2 * K + 1)) ≤ srMass p hm (2 * K + 1) y :=
    le_trans (Record.hitFMass_ge_recState hp hp1 K y hy)
      (hitFMass_le_srMass p hp hp1 hm hN (2 * K + 1) y)
  have h2 := Finset.single_le_sum (f := fun k => srMass p hm k y)
    (fun k _ => srMass_nonneg p hp hp1 hm k y) (Finset.mem_range.mpr (by omega : 2 * K + 1 < L + 1))
  linarith

/-- The total mass of the horizon-`L` stopped record law dominates the force bound, hence the
stopped record law puts at least `(1-p)^(N(2K+1))` mass on the *whole* space from every state of
`exh N m K`. -/
theorem hitMass_ge_force (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (K L : ℕ) (hL : 2 * K + 1 ≤ L) (y : RecState N m) (hy : y ∈ exh N m K) :
    (1 - p) ^ (N * (2 * K + 1)) ≤ hitMass p L y :=
  le_trans (force_le_srMassSum p hp hp1 hm hN K L hL y hy)
    (srMass_le_hitMass p hp hp1 hm L y)

/-- **Integration interface.**  If the record time is at most `L` almost surely from `y`
(equivalently: the stopped record mass at horizon `L` is one), then the horizon-`L` stopped
record measure is a probability measure, hence `hitKernel p hm L` is a Markov kernel and the
force bound `hitK_srSet_ge` turns into the paper's hypothesis `hforce` of
`SwarmRec.exists_invariant_measure_pos_srSet`.

The premise is *not* proved in this file.  It is the paper's "`P` is well-defined" step: the
record time is almost surely finite, proved there from recurrence of the simple symmetric walk
through the common-jump-uniform comparison. -/
theorem isProbabilityMeasure_hitK_of_mass_one (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m)
    (h : hitK p hm L y Set.univ = 1) : IsProbabilityMeasure (hitK p hm L y) :=
  ⟨h⟩

/-- **Integration interface.**  If additionally the mass is one for every record state, the
stopped record kernel of horizon `L` is a Markov kernel. -/
theorem isMarkovKernel_hitKernel_of_mass_one (p : ℝ) (hm : 1 ≤ m) (L : ℕ)
    (h : ∀ y : RecState N m, hitK p hm L y Set.univ = 1) :
    IsMarkovKernel (hitKernel (N := N) (m := m) p hm L) :=
  ⟨fun y => ⟨h y⟩⟩

/-- **Junk-freeness of the stopped record law**: only genuine first-record paths carry mass, so the
junk value of `out` never receives any weight. -/
theorem hitW_pos_imp_firstRecord (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (y : RecState N m)
    (h : hitW p q y ≠ 0) : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y) := by
  classical
  by_contra hc
  exact h (hitW_of_not_firstRecord p q y hc)

/-- The total mass of the stopped record law is monotone in the horizon. -/
theorem hitMass_mono_horizon (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {L L' : ℕ} (hLL : L ≤ L')
    (y : RecState N m) : hitMass p L y ≤ hitMass p L' y := by
  rw [hitMass, hitMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    fun k _ _ => Finset.sum_nonneg fun q _ => hitW_nonneg p hp hp1 q y

/-- **The paper's `hforce` hypothesis in the exact form used by
`SwarmRec.exists_invariant_measure_pos_srSet`**, for the finite-horizon stopped record kernel.
The only differences from the paper's statement are the explicit horizon restriction `2K+1 ≤ L`,
which disappears once the a.s. finiteness of the record time gives a horizon-free kernel, and the
strict inequality `p < 1` (the paper's range is `1/2 < p < 1`), which is needed for the constant
to be non-zero. -/
theorem hitKernel_force_bound (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (L : ℕ) :
    ∀ K : ℕ, 2 * K + 1 ≤ L → ∃ c : ℝ≥0∞, c ≠ 0 ∧
      ∀ y : RecState N m, y ∈ exh N m K → c ≤ hitKernel p hm L y (srSet N m) := by
  intro K hK
  refine ⟨ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))), ?_, fun y hy => ?_⟩
  · have hpos : (0 : ℝ) < (1 - p) ^ (N * (2 * K + 1)) :=
      pow_pos (by linarith : (0 : ℝ) < 1 - p) _
    intro hzero
    have h2 := congrArg ENNReal.toReal hzero
    simp only [ENNReal.toReal_ofReal (le_of_lt hpos), ENNReal.toReal_zero] at h2
    exact (ne_of_gt hpos) h2
  · rw [hitKernel_apply]
    exact hitK_srSet_ge p hp (le_of_lt hp1) hm hN K L hK y hy

end SimJump.RecKernel


