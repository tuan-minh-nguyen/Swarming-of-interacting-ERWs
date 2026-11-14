/-`BlockAggregate.step_iterate_dirac_apply` gives the law of the *terminal* block endpoint at every
`r`.  The record-law identity `Bridge.JointLawIdentity` needs the **joint** law of all the block
endpoints, i.e. a finite-dimensional *path* marginal.  This file does the first non-trivial case,
`r = 2`:

* `jointInfT2` — the joint law of the first and second block endpoints from `(y, t)`, built from
  two consecutive `hitKInfT` steps;
* `jointInfT2_apply` — its exact test-set formula: a double sum over pairs of finite words of the
  product of the two `hitW` weights, supported on the nested pair of endpoints `twoEndpt`;
* `joint_two_law` — the actual-array version: if the two-block first-record boxes are pairwise
  disjoint, cover almost every array, and a statistic `S` of the array is the nested pair of
  endpoints on each box, then the law of `S` is `jointInfT2`.

The box masses here come from the *already integrated* `M5FirstBlock.mass_twoBlock_firstRecord`,
not from `mass_jbox_concatF`; that is deliberate, so that the two-block aggregation is pinned to
the independently verified two-block factorisation rather than to this swarm's own generalisation.

The three geometric inputs (`hdisj`, `hcover`, `hS`) are the residual; at `r = 1` the analogous
three are theorems (see `R1Consistency.lean`).  Nothing here is `Bridge.JointLawIdentity`, and
nothing here asserts `Swarm.Ballistic`, `RegenAvailable`, `MainClaim` or a common speed.
-/
import Swarm.BlockAggregate

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

/-! ### The joint law of two consecutive block endpoints -/

/-- The joint law of the endpoints of two consecutive record blocks, started at `(y, t)`: draw
the first block from the stopped record law, then the second from the same law started at the
first block's endpoint, and keep both endpoints. -/
noncomputable def jointInfT2 (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ) :
    Measure ((RecState N m × ℕ) × (RecState N m × ℕ)) :=
  Measure.sum (fun a : Word N =>
    ENNReal.ofReal (hitW p a.2 y) •
      (hitKInfT p hm (out hm a.2 y, t + a.1)).map
        (fun z => ((out hm a.2 y, t + a.1), z)))

/-- The nested pair of endpoints of a pair of words. -/
noncomputable def twoEndpt {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ)
    (q : Word N × Word N) : (RecState N m × ℕ) × (RecState N m × ℕ) :=
  ((out hm q.1.2 y, t + q.1.1), (out hm q.2.2 (out hm q.1.2 y), (t + q.1.1) + q.2.1))

/-- **The exact joint law of the first two block endpoints**, as a double sum over finite words. -/
theorem jointInfT2_apply (p : ℝ) {m : ℕ} (hm : 1 ≤ m) (y : RecState N m) (t : ℕ)
    {A : Set ((RecState N m × ℕ) × (RecState N m × ℕ))} (hA : MeasurableSet A) :
    jointInfT2 p hm y t A
      = ∑' q : Word N × Word N,
          (ENNReal.ofReal (hitW p q.1.2 y) *
              ENNReal.ofReal (hitW p q.2.2 (out hm q.1.2 y))) *
            (if twoEndpt hm y t q ∈ A then 1 else 0) := by
  classical
  have hF : ∀ a : Word N, Measurable (fun z : RecState N m × ℕ =>
      ((out hm a.2 y, t + a.1), z)) := fun a =>
    Measurable.prodMk measurable_const measurable_id
  have hstep : ∀ a : Word N,
      (ENNReal.ofReal (hitW p a.2 y) •
          (hitKInfT p hm (out hm a.2 y, t + a.1)).map
            (fun z => ((out hm a.2 y, t + a.1), z))) A
        = ENNReal.ofReal (hitW p a.2 y) *
            ∑' b : Word N, ENNReal.ofReal (hitW p b.2 (out hm a.2 y)) *
              (if ((out hm a.2 y, t + a.1),
                  (out hm b.2 (out hm a.2 y), (t + a.1) + b.1)) ∈ A then 1 else 0) := by
    intro a
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hF a) hA,
      hitKInfT_apply p hm (out hm a.2 y, t + a.1) (hA.preimage (hF a))]
    simp only [Set.mem_preimage]
  rw [jointInfT2, Measure.sum_apply _ hA]
  simp only [hstep, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  refine tsum_congr fun q => ?_
  obtain ⟨a, b⟩ := q
  simp only [twoEndpt, mul_assoc]
  rfl

/-! ### The two-block first-record boxes of the actual array -/

/-- Both blocks are first-record paths from the running record state. -/
def FRTwo {m : ℕ} (hm : 1 ≤ m) (q : Word N × Word N) : Prop :=
  Record.FirstRecord (Record.extendPath q.1.2) q.1.1
      (Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm)) ∧
    Record.FirstRecord (Record.extendPath q.2.2) q.2.1
      (Record.ofRecState (out hm q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm)))

/-- The piece of the array space on which the two-block box of `q` is followed and the nested
endpoint of `q` falls in `A`. -/
noncomputable def twoPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (A : Set ((RecState N m × ℕ) × (RecState N m × ℕ))) (q : Word N × Word N) : Set (Array N) :=
  if twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q ∈ A
    then jbox p m (q.1.1 + q.2.1) (catWord q.1.2 q.2.2) else ∅

theorem measurableSet_twoPiece (p : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (A : Set ((RecState N m × ℕ) × (RecState N m × ℕ))) (q : Word N × Word N) :
    MeasurableSet (twoPiece (N := N) p hm A q) := by
  classical
  unfold twoPiece
  split
  · exact measurableSet_jbox p m (q.1.1 + q.2.1) (catWord q.1.2 q.2.2)
  · exact MeasurableSet.empty

/-- Off the two-block first-record pairs the product of the two `hitW` weights vanishes. -/
theorem twoEndpt_weight_eq_zero_of_not_frTwo {m : ℕ} (hm : 1 ≤ m) (p : ℝ)
    {q : Word N × Word N} (h : ¬ FRTwo hm q) :
    ENNReal.ofReal (hitW p q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm)) *
      ENNReal.ofReal (hitW p q.2.2 (out hm q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm))) = 0 := by
  rcases not_and_or.mp h with h | h
  · rw [hitW_of_not_firstRecord p q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm) h]
    simp
  · rw [hitW_of_not_firstRecord p q.2.2 (out hm q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm)) h]
    simp

/-- **The joint law of the first two block endpoints at the actual array**, given the geometric
two-block decomposition.  The box masses are those of `M5FirstBlock.mass_twoBlock_firstRecord`. -/
theorem joint_two_law {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (hdisj : Pairwise (fun q q' : {q : Word N × Word N // FRTwo hm q} =>
      Disjoint (jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2))
        (jbox p m (q'.1.1.1 + q'.1.2.1) (catWord q'.1.1.2 q'.1.2.2))))
    (hcover : ∀ᵐ U ∂(arrayMeasure N), ∃ q : {q : Word N × Word N // FRTwo hm q},
      U ∈ jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2))
    (S : Array N → (RecState N m × ℕ) × (RecState N m × ℕ))
    (hS : ∀ (q : {q : Word N × Word N // FRTwo hm q}) (U : Array N),
      U ∈ jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2) →
        S U = twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1)
    {A : Set ((RecState N m × ℕ) × (RecState N m × ℕ))} (hA : MeasurableSet A) :
    (arrayMeasure N) {U : Array N | S U ∈ A}
      = jointInfT2 p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 A := by
  classical
  have hset : {U : Array N | S U ∈ A} =ᵐ[arrayMeasure N]
      {U : Array N | ∃ q : {q : Word N × Word N // FRTwo hm q},
        U ∈ jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2) ∧
          twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1 ∈ A} := by
    filter_upwards [hcover] with U hU
    apply propext
    constructor
    · intro hSA
      obtain ⟨q, hq⟩ := hU
      exact ⟨q, hq, by rw [← hS q U hq]; exact hSA⟩
    · rintro ⟨q, hq, hmem⟩
      show S U ∈ A
      rw [hS q U hq]
      exact hmem
  rw [measure_congr hset]
  -- the union of the pieces
  have hunion : {U : Array N | ∃ q : {q : Word N × Word N // FRTwo hm q},
        U ∈ jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2) ∧
          twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1 ∈ A}
      = ⋃ q : {q : Word N × Word N // FRTwo hm q},
          twoPiece (N := N) p hm A q.1 := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, twoPiece]
    constructor
    · rintro ⟨q, hq, hmem⟩
      exact ⟨q, by rw [if_pos hmem]; exact hq⟩
    · rintro ⟨q, hq⟩
      by_cases hmem : twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1 ∈ A
      · rw [if_pos hmem] at hq
        exact ⟨q, hq, hmem⟩
      · rw [if_neg hmem] at hq
        exact absurd hq (Set.notMem_empty U)
  rw [hunion]
  have hdisj' : ∀ q q' : {q : Word N × Word N // FRTwo hm q}, q ≠ q' →
      Disjoint (jbox p m (q.1.1.1 + q.1.2.1) (catWord q.1.1.2 q.1.2.2))
        (jbox p m (q'.1.1.1 + q'.1.2.1) (catWord q'.1.1.2 q'.1.2.2)) := hdisj
  have hdisjg : ∀ q q' : {q : Word N × Word N // FRTwo hm q}, q ≠ q' →
      Disjoint (twoPiece (N := N) p hm A q.1) (twoPiece (N := N) p hm A q'.1) := by
    intro q q' hne
    simp only [twoPiece]
    by_cases hq : twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1 ∈ A
    · by_cases hq' : twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q'.1 ∈ A
      · rw [if_pos hq, if_pos hq']
        exact hdisj' q q' hne
      · rw [if_pos hq, if_neg hq']
        exact disjoint_bot_right
    · by_cases hq' : twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q'.1 ∈ A
      · rw [if_neg hq, if_pos hq']
        exact disjoint_bot_left
      · rw [if_neg hq, if_neg hq']
        exact disjoint_bot_right
  rw [measure_iUnion hdisjg (fun q => measurableSet_twoPiece p hm A q.1)]
  have hsub := tsum_subtype_eq_of_eq_zero
    {q : Word N × Word N | FRTwo hm q}
    (fun q => ENNReal.ofReal (hitW p q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm)) *
      ENNReal.ofReal (hitW p q.2.2 (out hm q.1.2 (SwarmRecordMeas.StartLaw.zeroState hm))) *
        (if twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q ∈ A then 1 else 0))
    (fun q hq => by
      rw [twoEndpt_weight_eq_zero_of_not_frTwo hm p hq, zero_mul])
  refine Eq.trans (tsum_congr (fun q => ?_))
    (hsub.trans (jointInfT2_apply p hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 hA).symm)
  -- each piece carries exactly the two-block mass
  simp only [twoPiece]
  by_cases hmem : twoEndpt hm (SwarmRecordMeas.StartLaw.zeroState hm) 0 q.1 ∈ A
  · rw [if_pos hmem, if_pos hmem,
      mass_twoBlock_firstRecord hp0 hp1 hm
        (by rw [extJump_eq_extendPath]; exact q.2.1)
        (by rw [extJump_eq_extendPath]; exact q.2.2)]
    exact (mul_one _).symm
  · rw [if_neg hmem, if_neg hmem, measure_empty, mul_zero]

end M6Aggr
