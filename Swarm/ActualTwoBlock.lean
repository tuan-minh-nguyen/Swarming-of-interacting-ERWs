/-
# Direction E, stage 3: the block factorisation of the array's jump masses

`M5FirstIterate.mass_jbox_firstRecord` gives the mass of a *first* record block in the stopped
record notation `hitW`.  The point of this file is that the same product formula governs every
later block, so the identification is not special to the first iterate:

* `pathWFun_add` / `evolveFun_shift`: the chain algebra's path weight and state recursion split
  over concatenation of jump words;
* `mass_jbox_cat`: **the mass of a concatenated word factors**, the second factor being the path
  weight `pathW p k₂ q₂ (evolveFun q₁ k₁ (startState m))` from the state reached after the first
  block.

Consequently the exact array probability of any finite word is a product of one-block weights,
and a whole run of record blocks is `∏ hitW`, i.e. the weight of the corresponding iterate of
`hitKKernel`.  The remaining glue for the *full* `Bridge.JointLawIdentity` is the state-identity
`ofRecState (out hm q y) = normalize (evolveFun q k (ofRecState y))`, which identifies the state
reached after a block with the compact record state that `hitW` is applied to in the next factor;
that identity is recorded here as an explicit residual, not assumed.

No claim about `Swarm.Ballistic`, `RegenAvailable` or the main theorem is made here.
-/
import Swarm.ActualFirstIterate

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M5FirstBlock

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump SimJump.RecKernel RecordoSupply Swarming.CurrentState
open SwarmRec

variable {N : ℕ} [Nonempty (Fin N)]

/-! ### Splitting the path weight and the state recursion over a concatenation -/

theorem evolveFun_shift {m : ℕ} (u : ℕ → JumpVec N) (k₁ : ℕ) :
    ∀ (k₂ : ℕ) (s : SimJump.State N m),
      SimJump.evolveFun (fun t => u (t + k₁)) k₂ (SimJump.evolveFun u k₁ s)
        = SimJump.evolveFun u (k₁ + k₂) s := by
  intro k₂
  induction k₂ with
  | zero => intro s; simp [SimJump.evolveFun, SimJump.evolve]
  | succ k₂ ih =>
      intro s
      rw [SimJump.evolveFun_succ, ih,
        show k₁ + (k₂ + 1) = k₁ + k₂ + 1 from by omega, SimJump.evolveFun_succ,
        show k₂ + k₁ = k₁ + k₂ from Nat.add_comm k₂ k₁]

theorem pathWFun_add {m : ℕ} (p : ℝ) (u : ℕ → JumpVec N) (k₁ : ℕ) :
    ∀ (k₂ : ℕ) (s : SimJump.State N m),
      SimJump.pathWFun p u (k₁ + k₂) s
        = SimJump.pathWFun p u k₁ s *
          SimJump.pathWFun p (fun t => u (t + k₁)) k₂ (SimJump.evolveFun u k₁ s) := by
  intro k₂
  induction k₂ with
  | zero => intro s; simp [SimJump.pathWFun, SimJump.pathW]
  | succ k₂ ih =>
      intro s
      rw [Nat.add_succ, SimJump.pathWFun_succ, ih, SimJump.pathWFun_succ, evolveFun_shift,
        show k₂ + k₁ = k₁ + k₂ from Nat.add_comm k₂ k₁, mul_assoc]

/-! ### Concatenation of finite words -/

/-- The concatenation of two finite jump words. -/
noncomputable def catWord {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N) :
    Fin (k₁ + k₂) → JumpVec N :=
  fun i => if h : (i : ℕ) < k₁ then q₁ ⟨i, h⟩
    else q₂ ⟨(i : ℕ) - k₁, by have := i.2; omega⟩

theorem extJump_cat_left {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N)
    {t : ℕ} (ht : t < k₁) : extJump (k₁ + k₂) (catWord q₁ q₂) t = q₁ ⟨t, ht⟩ := by
  rw [extJump_apply _ (by omega)]
  simp only [catWord, ht, dif_pos]

theorem extJump_cat_right {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N)
    {t : ℕ} (ht : t < k₂) : extJump (k₁ + k₂) (catWord q₁ q₂) (t + k₁) = q₂ ⟨t, ht⟩ := by
  rw [extJump_apply _ (by omega)]
  have hnk : ¬ (t + k₁) < k₁ := by omega
  simp only [catWord, hnk, dif_neg, not_false_eq_true, Nat.add_sub_cancel]

theorem extJump_apply_not {r : ℕ} (q : Fin r → JumpVec N) {n : ℕ} (hn : ¬ n < r) :
    extJump r q n = (fun _ => true : JumpVec N) := dif_neg hn

/-- The tail of a concatenated word is the second word. -/
theorem extJump_cat_shift {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N) :
    (fun t => extJump (k₁ + k₂) (catWord q₁ q₂) (t + k₁)) = extJump k₂ q₂ := by
  funext t
  by_cases ht : t < k₂
  · rw [extJump_cat_right q₁ q₂ ht, extJump_apply q₂ ht]
  · rw [extJump_apply_not q₂ (by omega),
      extJump_apply_not (catWord q₁ q₂) (show ¬ (t + k₁ < k₁ + k₂) by omega)]

/-- The head of a concatenated word is the first word. -/
theorem extJump_cat_head {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N)
    {t : ℕ} (ht : t < k₁) : extJump (k₁ + k₂) (catWord q₁ q₂) t = extJump k₁ q₁ t := by
  rw [extJump_cat_left q₁ q₂ ht, extJump_apply q₁ ht]

/-- The state recursion after the first block is the recursion of the first word. -/
theorem evolveFun_cat_head {m : ℕ} {k₁ k₂ : ℕ} (q₁ : Fin k₁ → JumpVec N)
    (q₂ : Fin k₂ → JumpVec N) (s : SimJump.State N m) :
    SimJump.evolveFun (extJump (k₁ + k₂) (catWord q₁ q₂)) k₁ s
      = SimJump.evolveFun (extJump k₁ q₁) k₁ s :=
  evolveFun_congr (fun t ht => extJump_cat_head q₁ q₂ ht) s

/-- `pathW` is the finite-word weight of the continuation, at any state. -/
theorem pathW_eq_pathWFun_ext' (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (s : SimJump.State N m) :
    pathW p r q s = SimJump.pathWFun p (extJump r q) r s := by
  rw [← SimJump.pathW_eq_pathWFun p (extJump r q) r s]
  congr 2
  funext i
  exact (extJump_apply q i.2).symm

theorem pathWFun_congr {m : ℕ} (p : ℝ) {u u' : ℕ → JumpVec N} {k : ℕ}
    (h : ∀ t, t < k → u t = u' t) (s : SimJump.State N m) :
    SimJump.pathWFun p u k s = SimJump.pathWFun p u' k s := by
  have hw : (fun i : Fin k => u i) = fun i : Fin k => u' i := by
    funext i
    exact h i i.2
  simp only [SimJump.pathWFun, hw]

/-! ### The factorisation of the array's block masses -/

/-- **The mass of a concatenated word factors over the two blocks.**  The second factor is the
chain algebra's path weight started from the state reached after the first block — exactly the
weight that `hitW` assigns to the next record block. -/
theorem mass_jbox_cat {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {k₁ k₂ : ℕ}
    (q₁ : Fin k₁ → JumpVec N) (q₂ : Fin k₂ → JumpVec N) :
    arrayMeasure N (jbox p m (k₁ + k₂) (catWord q₁ q₂))
      = ENNReal.ofReal (pathW p k₁ q₁ (startState (N := N) m)) *
        ENNReal.ofReal (pathW p k₂ q₂
          (SimJump.evolveFun (extJump k₁ q₁) k₁ (startState (N := N) m))) := by
  rw [mass_jbox_pathW hp0 hp1 m (k₁ + k₂) (catWord q₁ q₂),
    pathW_eq_pathWFun_ext' p m (k₁ + k₂) (catWord q₁ q₂) (startState (N := N) m), pathWFun_add,
    extJump_cat_shift, evolveFun_cat_head,
    pathWFun_congr (m := m) p (u := extJump (k₁ + k₂) (catWord q₁ q₂))
      (u' := extJump k₁ q₁) (k := k₁) (fun t ht => extJump_cat_head q₁ q₂ ht)
      (startState (N := N) m),
    ← pathW_eq_pathWFun_ext' p m k₁ q₁ (startState (N := N) m),
    ← pathW_eq_pathWFun_ext' p m k₂ q₂
      (SimJump.evolveFun (extJump k₁ q₁) k₁ (startState (N := N) m)),
    ENNReal.ofReal_mul (pathW_nonneg p hp0.le hp1.le k₁ q₁ _)]


 /-! ### Invariance of the chain weights under the record normalisation -/

theorem otherVisits_normalize (m : ℕ) (s : SimJump.State N m) (i : Fin N) :
    SimJump.otherVisits (Record.normalize s) i = SimJump.otherVisits s i := by
  unfold SimJump.otherVisits
  refine Finset.sum_congr rfl fun j _ => ?_
  show s.eta j ((s.pos i - 1) + 1) = s.eta j (s.pos i)
  rw [show (s.pos i - 1) + 1 = s.pos i by ring]

theorem qRight_normalize (p : ℝ) (m : ℕ) (s : SimJump.State N m) (i : Fin N) :
    SimJump.qRight p m (Record.normalize s) i = SimJump.qRight p m s i := by
  unfold SimJump.qRight
  rw [otherVisits_normalize]

theorem stepW_normalize (p : ℝ) (m : ℕ) (s : SimJump.State N m) (v : JumpVec N) :
    SimJump.stepW p m (Record.normalize s) v = SimJump.stepW p m s v := by
  unfold SimJump.stepW
  exact Finset.prod_congr rfl fun i _ => by rw [qRight_normalize]

theorem step_normalize (m : ℕ) (s : SimJump.State N m) (v : JumpVec N) :
    SimJump.step m (Record.normalize s) v = Record.normalize (SimJump.step m s v) := by
  have hpos : SimJump.stepPos (Record.normalize s) v
      = fun i => SimJump.stepPos s v i - 1 := by
    funext i
    simp only [SimJump.stepPos, Record.normalize]
    ring
  have heta : ∀ (i : Fin N) (x : ℤ),
      (SimJump.step m (Record.normalize s) v).eta i x
        = (SimJump.step m s v).eta i (x + 1) := by
    intro i x
    show (if x = SimJump.stepPos (Record.normalize s) v i then
        SimJump.cap m ((Record.normalize s).eta i x + 1) else (Record.normalize s).eta i x) = _
    show _ = (if x + 1 = SimJump.stepPos s v i then
        SimJump.cap m (s.eta i (x + 1) + 1) else s.eta i (x + 1))
    by_cases hx : x + 1 = SimJump.stepPos s v i
    · have h2 : SimJump.stepPos (Record.normalize s) v i = SimJump.stepPos s v i - 1 := by
        rw [hpos]
      have hx' : x = SimJump.stepPos (Record.normalize s) v i := by omega
      rw [if_pos hx', if_pos hx]
      rfl
    · have h2 : SimJump.stepPos (Record.normalize s) v i = SimJump.stepPos s v i - 1 := by
        rw [hpos]
      have hx' : ¬ x = SimJump.stepPos (Record.normalize s) v i := by omega
      rw [if_neg hx', if_neg hx]
      rfl
  refine CurrentState.recordState_ext ?_ ?_
  · exact hpos
  · funext i x
    exact heta i x

theorem evolveFun_normalize (m : ℕ) (u : ℕ → JumpVec N) :
    ∀ (k : ℕ) (s : SimJump.State N m),
      SimJump.evolveFun u k (Record.normalize s) = Record.normalize (SimJump.evolveFun u k s) := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih => intro s; rw [SimJump.evolveFun_succ, SimJump.evolveFun_succ, ih, step_normalize]

theorem pathWFun_normalize (p : ℝ) (m : ℕ) (u : ℕ → JumpVec N) :
    ∀ (k : ℕ) (s : SimJump.State N m),
      SimJump.pathWFun p u k (Record.normalize s) = SimJump.pathWFun p u k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [SimJump.pathWFun_succ, SimJump.pathWFun_succ, ih, evolveFun_normalize, stepW_normalize]

theorem pathW_normalize (p : ℝ) (m : ℕ) (k : ℕ) (q : Fin k → JumpVec N)
    (s : SimJump.State N m) :
    pathW p k q (Record.normalize s) = pathW p k q s := by
  rw [pathW_eq_pathWFun_ext' p m k q (Record.normalize s), pathW_eq_pathWFun_ext' p m k q s,
    pathWFun_normalize]

/-! ### The compact record state after a block -/

/-- Expanding the compact record state of a normalised state returns the normalised state. -/
theorem ofRecState_toRecordAmb (m : ℕ) (s : SimJump.State N m)
    (hs : Record.RecordStart (Record.normalize s)) :
    Record.ofRecState (⟨Record.toRecordAmb s, Record.toRecordAmb_mem s hs⟩ : RecState N m)
      = Record.normalize s := by
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    show -((2 * (⟨Record.toRecordAmb s, Record.toRecordAmb_mem s hs⟩ : RecState N m).val.1 i : ℕ) : ℤ)
      = (Record.normalize s).pos i
    exact (Record.normalized_pos_halfDist_of_valid s hs i).symm
  · funext i x
    show ((⟨Record.toRecordAmb s, Record.toRecordAmb_mem s hs⟩ : RecState N m).val.2 i x).val
      = (Record.normalize s).eta i x
    rfl

/-- **The compact record state reached after a first-record block** is the normalised capped
state at the block's end: exactly the state that the stopped record kernel continues from. -/
theorem ofRecState_out {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m)
    (hFR : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    Record.ofRecState (out hm q y)
      = Record.normalize (SimJump.evolveFun (Record.extendPath q) k (Record.ofRecState y)) := by
  rw [out_of_firstRecord hm q y hFR]
  exact ofRecState_toRecordAmb m _
    (Record.normalized_recordStart (Record.extendPath q) k (Record.ofRecState y)
      (Record.ofRecState_recordStart y hm) hm hFR)

/-- **The two-block mass law.**  The probability that the actual array follows the first block
`q₁` and then the block `q₂` is the first block's stopped-record weight `hitW p q₁ y₀` times the
path weight `pathW p k₂ q₂ (ofRecState y₁)` started from the compact record state `y₁ = out q₁ y₀`
reached after the first block.  This is the block-level Markov factorisation of the stopped record
chain, at the actual array. -/
theorem mass_jbox_cat_hitW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) {k₁ k₂ : ℕ} {q₁ : Fin k₁ → JumpVec N}
    (hFR₁ : Record.FirstRecord (extJump k₁ q₁) k₁
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)))
    (q₂ : Fin k₂ → JumpVec N) :
    arrayMeasure N (jbox p m (k₁ + k₂) (catWord q₁ q₂))
      = ENNReal.ofReal (hitW p q₁ (SwarmRecordMeas.StartLaw.zeroState hm1)) *
        ENNReal.ofReal (pathW p k₂ q₂
          (SimJump.Record.ofRecState (out hm1 q₁
            (SwarmRecordMeas.StartLaw.zeroState hm1)))) := by
  have hFR₁' : Record.FirstRecord (Record.extendPath q₁) k₁
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)) := by
    rw [← extJump_eq_extendPath]
    exact hFR₁
  rw [mass_jbox_cat hp0 hp1 m q₁ q₂, ← ofRecState_zeroState m hm1,
    hitW_of_firstRecord p q₁ (SwarmRecordMeas.StartLaw.zeroState hm1) hFR₁']
  congr 1
  rw [ofRecState_out hm1 q₁ (SwarmRecordMeas.StartLaw.zeroState hm1) hFR₁',
    pathW_normalize, extJump_eq_extendPath]

/-- **The two-block mass law in stopped-record notation**: the array probability of following the
first-record block `q₁` and then the first-record block `q₂` is the product of the two stopped
record weights, the second taken at the compact record state `out hm q₁ y₀` reached after the
first block.  This is the `r = 2` block content of `Bridge.JointLawIdentity`. -/
theorem mass_twoBlock_firstRecord {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm1 : 1 ≤ m) {k₁ k₂ : ℕ} {q₁ : Fin k₁ → JumpVec N} {q₂ : Fin k₂ → JumpVec N}
    (hFR₁ : Record.FirstRecord (extJump k₁ q₁) k₁
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState hm1)))
    (hFR₂ : Record.FirstRecord (extJump k₂ q₂) k₂
      (SimJump.Record.ofRecState (out hm1 q₁ (SwarmRecordMeas.StartLaw.zeroState hm1)))) :
    arrayMeasure N (jbox p m (k₁ + k₂) (catWord q₁ q₂))
      = ENNReal.ofReal (hitW p q₁ (SwarmRecordMeas.StartLaw.zeroState hm1)) *
        ENNReal.ofReal (hitW p q₂ (out hm1 q₁ (SwarmRecordMeas.StartLaw.zeroState hm1))) := by
  rw [mass_jbox_cat_hitW hp0 hp1 hm1 hFR₁ q₂,
    hitW_of_firstRecord p q₂ (out hm1 q₁ (SwarmRecordMeas.StartLaw.zeroState hm1))
      (by rw [← extJump_eq_extendPath]; exact hFR₂)]

end M5FirstBlock
