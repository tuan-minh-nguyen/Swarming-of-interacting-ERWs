/-
Raw capped successors versus compact record states, in general dimensions.

The key point is normalization-invariance of the capped-step weights.  It does
not require a positive excursion or a fresh past.  Together with the concrete
formula for `recState`, this identifies `ofRecState` of the stopped record state
with the normalized actual successor, and transports every finite suffix weight.
-/
import Swarm.FreshArrayBridge

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmRawRecord

open SimJump.Record SwarmRec

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- Extensionality for capped states; the cap proof is irrelevant. -/
theorem state_ext {s t : State N m} (hpos : s.pos = t.pos) (heta : s.eta = t.eta) :
    s = t := by
  cases s
  cases t
  simp_all

/-- Expansion of the stopped compact state is exactly normalization of the actual successor. -/
theorem ofRecState_recState (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hm : 1 ≤ m) (h : FirstRecord u k s) (hs : RecordStart s) :
    ofRecState (RecKernel.recState u k s hm h hs) = normalize (evolveFun u k s) := by
  apply state_ext
  · funext i
    change -(2 * ((RecKernel.recState u k s hm h hs).val.1 i : ℤ)) =
      (normalize (evolveFun u k s)).pos i
    rw [RecKernel.recState_val]
    exact (normalized_pos_halfDist u k s hs.even_pos h i).symm
  · funext i x
    change ((RecKernel.recState u k s hm h hs).val.2 i x).val =
      (normalize (evolveFun u k s)).eta i x
    rw [RecKernel.recState_val]
    rfl

/-- The same converse for the public stopped-map `out`. -/
theorem ofRecState_out (hm : 1 ≤ m) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m) (h : FirstRecord (extendPath q) k (ofRecState y)) :
    ofRecState (RecKernel.out hm q y) =
      normalize (evolveFun (extendPath q) k (ofRecState y)) := by
  rw [RecKernel.out_of_firstRecord hm q y h]
  exact ofRecState_recState _ _ _ _ _ _

/-- Moving the record origin commutes with one capped step. -/
theorem normalize_step (s : State N m) (v : JumpVec N) :
    normalize (step m s v) = step m (normalize s) v := by
  have hp (i : Fin N) : stepPos (normalize s) v i = stepPos s v i - 1 := by
    change (s.pos i - 1) + (if v i = true then 1 else -1) =
      s.pos i + (if v i = true then 1 else -1) - 1
    split_ifs <;> ring
  apply state_ext
  · funext i
    change stepPos s v i - 1 = stepPos (normalize s) v i
    exact (hp i).symm
  · funext i x
    change (step m s v).eta i (x + 1) = (step m (normalize s) v).eta i x
    by_cases hx : x + 1 = stepPos s v i
    · have hx' : x = stepPos (normalize s) v i := by rw [hp]; omega
      calc
        (step m s v).eta i (x + 1) = cap m (s.eta i (x + 1) + 1) := by
          simp only [step, hx, if_pos]
        _ = cap m ((normalize s).eta i x + 1) := rfl
        _ = (step m (normalize s) v).eta i x := by
          simp only [step, hx', if_pos]
    · have hx' : x ≠ stepPos (normalize s) v i := by rw [hp]; omega
      rw [step_eta_of_ne _ _ _ _ hx, step_eta_of_ne _ _ _ _ hx']
      rfl

/-- `otherVisits` is invariant under moving the record origin. -/
theorem otherVisits_normalize (s : State N m) (i : Fin N) :
    otherVisits (normalize s) i = otherVisits s i := by
  unfold otherVisits
  apply Finset.sum_congr rfl
  intro j hj
  change s.eta j (s.pos i - 1 + 1) = s.eta j (s.pos i)
  congr 2
  ring

/-- The one-walker right probability is normalization-invariant. -/
theorem qRight_normalize (p : ℝ) (s : State N m) (i : Fin N) :
    qRight p m (normalize s) i = qRight p m s i := by
  unfold qRight
  rw [otherVisits_normalize]

/-- The simultaneous one-step weight is normalization-invariant. -/
theorem stepW_normalize (p : ℝ) (s : State N m) (v : JumpVec N) :
    stepW p m (normalize s) v = stepW p m s v := by
  simp only [stepW, qRight_normalize]

/-- Normalization commutes with every finite evolution. -/
theorem evolveFun_normalize (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    normalize (evolveFun u k s) = evolveFun u k (normalize s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [evolveFun_succ, evolveFun_succ, normalize_step, ih]

/-- Every infinite-word finite-prefix weight is normalization-invariant. -/
theorem pathWFun_normalize (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    pathWFun p u k (normalize s) = pathWFun p u k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [pathWFun_succ, pathWFun_succ, ih, ← evolveFun_normalize, stepW_normalize]

/-- Every finite-word weight is normalization-invariant. -/
theorem pathW_normalize (p : ℝ) {k : ℕ} (q : Fin k → JumpVec N) (s : State N m) :
    pathW p k q (normalize s) = pathW p k q s := by
  rw [SwarmFreshCyl.pathW_eq_pathWFun_extendPath,
    SwarmFreshCyl.pathW_eq_pathWFun_extendPath]
  exact pathWFun_normalize p (extendPath q) k s

/-- Arbitrary finite suffix weights at the compact stopped state equal those at the actual raw
successor.  No fresh-start or positivity condition is imposed on the suffix. -/
theorem pathW_recState_eq_raw (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hm : 1 ≤ m) (h : FirstRecord u k s) (hs : RecordStart s)
    {r : ℕ} (q : Fin r → JumpVec N) :
    pathW p r q (ofRecState (RecKernel.recState u k s hm h hs)) =
      pathW p r q (evolveFun u k s) := by
  rw [ofRecState_recState, pathW_normalize]

/-- The stopped word weight is exactly the actual raw suffix weight on its first-record support. -/
theorem hitW_recState_eq_raw (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hm : 1 ≤ m) (h : FirstRecord u k s) (hs : RecordStart s)
    {r : ℕ} (q : Fin r → JumpVec N) :
    RecKernel.hitW p q (RecKernel.recState u k s hm h hs) =
      if FirstRecord (extendPath q) r
          (ofRecState (RecKernel.recState u k s hm h hs)) then
        pathW p r q (evolveFun u k s) else 0 := by
  by_cases hq : FirstRecord (extendPath q) r
      (ofRecState (RecKernel.recState u k s hm h hs))
  · rw [RecKernel.hitW_of_firstRecord p q _ hq, if_pos hq, pathW_recState_eq_raw]
  · rw [RecKernel.hitW_of_not_firstRecord p q _ hq, if_neg hq]

/-- Public `out` form of the raw suffix transport. -/
theorem hitW_out_eq_raw (p : ℝ) (hm : 1 ≤ m) {k : ℕ} (qf : Fin k → JumpVec N)
    (y : RecState N m) (hf : FirstRecord (extendPath qf) k (ofRecState y))
    {r : ℕ} (q : Fin r → JumpVec N) :
    RecKernel.hitW p q (RecKernel.out hm qf y) =
      if FirstRecord (extendPath q) r (ofRecState (RecKernel.out hm qf y)) then
        pathW p r q (evolveFun (extendPath qf) k (ofRecState y)) else 0 := by
  rw [RecKernel.out_of_firstRecord hm qf y hf]
  exact hitW_recState_eq_raw p (extendPath qf) k (ofRecState y) hm hf
    (ofRecState_recordStart y hm) q

end SwarmRawRecord

