/-
Exact finite enriched-chain/raw-array joins for arbitrary record prefixes.

The enriched side is the actual finite Markov-chain law `chainVec` starting at
`asegK p hm y`.  Unlike the old fresh-prefix theorem, exact atom masses are
proved at arbitrary record states: the segment decoder, not an `srSet`
hypothesis, gives uniqueness of the represented first-record word.  The raw
side keeps the complete arbitrary measurable suffix pattern and its weight.
-/
import Swarm.FreshPrefix
import Swarm.RawPrefixReconstruction
import Swarm.MeasuredRawRecordPrefix

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmMeasuredJoin

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Transition Swarming.CurrentState
open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords SwarmRawRecord SwarmMeasuredRawRecord
open SwarmFreshPrefix SwarmFinHorizon SwarmFreshPos SwarmFreshCyl

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Exact one-atom mass at an arbitrary compact state.  On first-record
support, `segBlock` is a left inverse, so no second raw word can contribute to
the same enriched atom.  In particular no simultaneous-record or positivity
hypothesis is needed. -/
theorem asegK_atom_of_firstRecord (p : ℝ) (hm : 1 ≤ m) (y : RecState N m)
    {k : ℕ} (hk : 0 < k) (q : Fin k → JumpVec N)
    (hq : FirstRecord (extendPath q) k (ofRecState y)) :
    (SwarmSegKernel.asegK (N := N) p hm y)
        {(SwarmSegKernel.segOf y k q, RecKernel.out hm q y)} =
      ENNReal.ofReal (RecKernel.hitW p q y) := by
  classical
  have hmeas : MeasurableSet
      ({(SwarmSegKernel.segOf y k q, RecKernel.out hm q y)} :
        Set (SwarmInfSeg.Pair N m)) := by
    have h := (SwarmFreshTwoSeg.measurableSet_seg_singleton
      (SwarmSegKernel.segOf y k q)).prod
        (measurableSet_singleton (RecKernel.out hm q y))
    rwa [Set.singleton_prod_singleton] at h
  rw [SwarmSegKernel.asegK_apply p hm y hmeas]
  refine (tsum_eq_single (⟨k, q⟩ : (k : ℕ) × (Fin k → JumpVec N)) ?_).trans ?_
  · rintro ⟨k', q'⟩ hne
    by_cases hq' : FirstRecord (extendPath q') k' (ofRecState y)
    · rw [if_neg, mul_zero]
      intro hmem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      have hseg := congrArg (SwarmRawRecord.segBlock (N := N)) hmem.1
      rw [SwarmRawRecord.segBlock_segOf y (SwarmDHStruct.firstRecord_ne_zero hq') q' hq',
        SwarmRawRecord.segBlock_segOf y hk q hq] at hseg
      exact hne (by exact hseg)
    · rw [RecKernel.hitW_of_not_firstRecord p q' y hq', ENNReal.ofReal_zero, zero_mul]
  · simp

/-- Total extension of a finite raw-block list; the default is never used below
`bs.length`. -/
def defaultBlock : RawBlock N := ⟨0, fun i => Fin.elim0 i⟩

noncomputable def blockSeq (bs : List (RawBlock N)) (j : ℕ) : RawBlock N :=
  bs.getD j (defaultBlock (N := N))

@[simp] theorem blockSeq_cons_zero (b : RawBlock N) (bs : List (RawBlock N)) :
    blockSeq (b :: bs) 0 = b := by simp [blockSeq]

@[simp] theorem blockSeq_cons_succ (b : RawBlock N) (bs : List (RawBlock N)) (j : ℕ) :
    blockSeq (b :: bs) (j + 1) = blockSeq bs j := by simp [blockSeq]

/-- The endpoint sequence after a cons is the tail sequence at the first
block's actual output state. -/
theorem ep_blockSeq_cons_succ (hm : 1 ≤ m) (y : RecState N m)
    (b : RawBlock N) (bs : List (RawBlock N)) (j : ℕ) :
    ep hm y (blockSeq (b :: bs)) (j + 1) =
      ep hm (RecKernel.out hm b.2 y) (blockSeq bs) j := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      change RecKernel.out hm (blockSeq (b :: bs) (j + 1)).2
          (ep hm y (blockSeq (b :: bs)) (j + 1)) =
        RecKernel.out hm (blockSeq bs j).2
          (ep hm (RecKernel.out hm b.2 y) (blockSeq bs) j)
      rw [blockSeq_cons_succ, ih]

theorem atom_blockSeq_cons_succ (hm : 1 ≤ m) (y : RecState N m)
    (b : RawBlock N) (bs : List (RawBlock N)) (j : ℕ) :
    atom hm y (blockSeq (b :: bs)) (j + 1) =
      atom hm (RecKernel.out hm b.2 y) (blockSeq bs) j := by
  simp only [atom]
  rw [blockSeq_cons_succ, ep_blockSeq_cons_succ, ep_blockSeq_cons_succ]

/-- The `Fin`-indexed atom vector is literally the reconstructed `rawPairs`
list, including every actual successive output state. -/
theorem rawPairs_eq_ofFn_atom_blockSeq (hm : 1 ≤ m) (y : RecState N m) :
    ∀ bs : List (RawBlock N), rawPairs hm y bs =
      List.ofFn (fun j : Fin bs.length => atom hm y (blockSeq bs) j) := by
  intro bs
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
      rw [rawPairs_cons, List.ofFn_succ, ih]
      congr 1
      apply congrArg (fun f : Fin bs.length → SwarmInfSeg.Pair N m => List.ofFn f)
      funext j
      exact (atom_blockSeq_cons_succ hm y b bs (j : ℕ)).symm

/-- At every in-range index the totalised block sequence has the source list's
actual first-record property at its actual predecessor. -/
theorem firstRecord_blockSeq (hm : 1 ≤ m) (y : RecState N m)
    {bs : List (RawBlock N)} (hbs : AllFirst hm y bs) {j : ℕ}
    (hj : j < bs.length) :
    FirstRecord (extendPath (blockSeq bs j).2) (blockSeq bs j).1
      (ofRecState (ep hm y (blockSeq bs) j)) := by
  induction j generalizing bs y with
  | zero =>
      cases bs with
      | nil => simp at hj
      | cons b bs =>
          change FirstRecord (extendPath b.2) b.1 (ofRecState y)
          exact hbs.1
  | succ j ih =>
      cases bs with
      | nil => simp at hj
      | cons b bs =>
          rw [blockSeq_cons_succ, ep_blockSeq_cons_succ]
          exact ih _ hbs.2 (by simpa using hj)

/-- `ofReal prefixW` is the finite product of the actual successor-state
`hitW` factors along the totalised block sequence. -/
theorem ofReal_prefixW_eq_prod (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    (bs : List (RawBlock N)) :
    ENNReal.ofReal (prefixW p hm y bs) =
      ∏ j ∈ Finset.range bs.length,
        ENNReal.ofReal (RecKernel.hitW p (blockSeq bs j).2
          (ep hm y (blockSeq bs) j)) := by
  induction bs generalizing y with
  | nil => simp [prefixW]
  | cons b bs ih =>
      simp only [prefixW]
      rw [ENNReal.ofReal_mul (RecKernel.hitW_nonneg p hp hp1 b.2 y), ih]
      simp only [List.length_cons, Finset.prod_range_succ']
      have hshift : (∏ j ∈ Finset.range bs.length,
          ENNReal.ofReal (RecKernel.hitW p (blockSeq (b :: bs) (j + 1)).2
            (ep hm y (blockSeq (b :: bs)) (j + 1)))) =
          ∏ j ∈ Finset.range bs.length,
            ENNReal.ofReal (RecKernel.hitW p (blockSeq bs j).2
              (ep hm (RecKernel.out hm b.2 y) (blockSeq bs) j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [blockSeq_cons_succ, ep_blockSeq_cons_succ]
      rw [hshift, blockSeq_cons_zero, ep_zero]
      exact mul_comm _ _

/-- The finite enriched Markov chain charges the reconstructed raw-prefix atom
cylinder exactly `prefixW`.  All blocks and endpoint states are retained; no
positivity or `srSet` hypothesis is used. -/
theorem chainVec_rawPrefix_pin_mass (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (y : RecState N m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) :
    (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
        (SwarmSegKernel.pairK (N := N) p hm) bs.length)
        (pin (atom hm y (blockSeq bs)) bs.length) =
      ENNReal.ofReal (prefixW p hm y bs) := by
  haveI hmark : IsMarkovKernel (SwarmSegKernel.pairK (N := N) (m := m) p hm) :=
    SwarmSegKernel.isMarkovKernel_pairK (N := N) (m := m) p hm hp hp1
  haveI hprob : IsProbabilityMeasure (SwarmSegKernel.asegK (N := N) p hm y) :=
    SwarmSegKernel.isProbabilityMeasure_asegK p hm hp hp1 y
  cases bs with
  | nil => simp [pin_zero, SwarmChain.chainVec_zero, prefixW]
  | cons b bs =>
      have hfr0 : FirstRecord (extendPath b.2) b.1 (ofRecState y) := hbs.1
      have hstart :
          (SwarmSegKernel.asegK (N := N) p hm y) {atom hm y (blockSeq (b :: bs)) 0} =
            ENNReal.ofReal (RecKernel.hitW p b.2 y) := by
        simp only [atom, blockSeq_cons_zero, ep_zero]
        exact asegK_atom_of_firstRecord p hm y
          (SwarmDHStruct.firstRecord_ne_zero hfr0) b.2 hfr0
      have hstep : ∀ j : ℕ, j < bs.length →
          (SwarmSegKernel.pairK (N := N) p hm (atom hm y (blockSeq (b :: bs)) j))
              {atom hm y (blockSeq (b :: bs)) (j + 1)} =
            ENNReal.ofReal (RecKernel.hitW p (blockSeq (b :: bs) (j + 1)).2
              (ep hm y (blockSeq (b :: bs)) (j + 1))) := by
        intro j hj
        rw [SwarmSegKernel.pairK_apply]
        change (SwarmSegKernel.asegK (N := N) p hm
            (ep hm y (blockSeq (b :: bs)) (j + 1)))
            {(SwarmSegKernel.segOf (ep hm y (blockSeq (b :: bs)) (j + 1))
                (blockSeq (b :: bs) (j + 1)).1 (blockSeq (b :: bs) (j + 1)).2,
              RecKernel.out hm (blockSeq (b :: bs) (j + 1)).2
                (ep hm y (blockSeq (b :: bs)) (j + 1)))} = _
        exact asegK_atom_of_firstRecord p hm _
          (SwarmDHStruct.firstRecord_ne_zero
            (firstRecord_blockSeq hm y hbs (by simpa using hj)))
          _ (firstRecord_blockSeq hm y hbs (by simpa using hj))
      simp only [List.length_cons]
      rw [chainVec_pin_mass_succ _ _ _ (measurableSet_atom_singleton hm y (blockSeq (b :: bs))) bs.length,
        hstart]
      have hprod : (∏ j ∈ Finset.range bs.length,
          (SwarmSegKernel.pairK (N := N) p hm (atom hm y (blockSeq (b :: bs)) j))
            {atom hm y (blockSeq (b :: bs)) (j + 1)}) =
          ∏ j ∈ Finset.range bs.length,
            ENNReal.ofReal (RecKernel.hitW p (blockSeq bs j).2
              (ep hm (RecKernel.out hm b.2 y) (blockSeq bs) j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hstep j (Finset.mem_range.mp hj), blockSeq_cons_succ, ep_blockSeq_cons_succ]
      rw [hprod]
      simp only [prefixW]
      rw [ENNReal.ofReal_mul (RecKernel.hitW_nonneg p hp hp1 b.2 y),
        ofReal_prefixW_eq_prod p hm hp hp1 (RecKernel.out hm b.2 y) bs]

/-- Nonnegativity of the complete actual-state record-prefix weight. -/
theorem prefixW_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (y : RecState N m) (bs : List (RawBlock N)) :
    0 ≤ prefixW p hm y bs := by
  induction bs generalizing y with
  | nil => exact zero_le_one
  | cons b bs ih =>
      exact mul_nonneg (RecKernel.hitW_nonneg p hp hp1 b.2 y) (ih _)

/-- **Measured enriched/raw finite-window joined identity.**  The first factor
is the exact pinned-cylinder mass of the actual enriched finite chain.  The
finite sum retains the whole-prefix positivity guard, arbitrary raw pattern
`C`, every suffix word and its terminal-state weight.  This is an exact scalar
comparison, not an assertion of independence or of an unfinished-tail future
marginal identity. -/
theorem arrayMeasure_rawPrefixWindow_eq_enriched_pin_mul_suffix
    (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (y : RecState N m) (hy : ofRecState y = SwarmFreshArray.startState (N := N) m)
    (bs : List (RawBlock N)) (hbs : AllFirst hm y bs) (s : ℕ)
    (C : Set (Fin (rawLen bs + s + 1) → Fin N → ℤ)) :
    (arrayMeasure N) (rawPrefixWindow p m (rawWord bs) s C) =
      (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) p hm y)
          (SwarmSegKernel.pairK (N := N) p hm) bs.length)
          (pin (atom hm y (blockSeq bs)) bs.length) *
        ∑ qs : Fin s → JumpVec N,
          if PosSeqFin (N := N) (rawWord bs) ∧
              patOf (N := N) (catWord (rawWord bs) qs) ∈ C then
            ENNReal.ofReal (pathW p s qs (ofRecState (terminal hm y bs)))
          else 0 := by
  rw [SwarmMeasuredRawRecord.arrayMeasure_rawPrefixWindow_terminal p hp0 hp1 hm y hy bs hbs,
    chainVec_rawPrefix_pin_mass p hm hp0.le hp1.le y bs hbs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro qs hqs
  by_cases hcond : PosSeqFin (N := N) (rawWord bs) ∧
      patOf (N := N) (catWord (rawWord bs) qs) ∈ C
  · rw [if_pos hcond, if_pos hcond,
      ← ENNReal.ofReal_mul (prefixW_nonneg p hp0.le hp1.le hm y bs)]
  · rw [if_neg hcond, if_neg hcond, mul_zero]

end SwarmMeasuredJoin
