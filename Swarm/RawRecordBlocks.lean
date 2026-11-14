/-
The general raw-word / enriched-record splice.

The middle block is an arbitrary first-record excursion from the actual `out`
of the preceding block.  The final raw future is unrestricted and retains its
true capped successor state.  This is a deterministic weighted dictionary, not
a fresh-future independence theorem.
-/
import Swarm.RawRecordTransport
import Swarm.WordSplitSum

open MeasureTheory Set
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawRecord

open SimJump.Record SwarmRec SwarmFreshArray SwarmArrayWords

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-- The compact simultaneous-record state whose expansion is exactly the canonical raw-array
start state, including all of its below-record capped local times. -/
noncomputable def freshRecState (hm : 1 ≤ m) (i₀ : Fin N) : RecState N m :=
  ⟨(fun _ => 0, fun i x => ⟨(SwarmFreshArray.startState (N := N) m).eta i x,
      Nat.lt_succ_of_le ((SwarmFreshArray.startState (N := N) m).hcap i x)⟩), by
    have hs := freshStart_startState (N := N) m hm
    have hone : (⟨1, Nat.lt_succ_of_le hm⟩ : Fin (m + 1)) = 1 := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
    refine ⟨⟨i₀, rfl⟩, ?_, ?_, ?_⟩
    · intro i x hx
      apply Fin.ext
      exact hs.2.1 i x hx
    · intro i
      simp [hone, hs.2.2 i]
    · intro i
      apply Fin.ext
      simp [hone, hs.2.2 i, Nat.mod_eq_of_lt (by omega : 1 < m + 1)]⟩

/-- Expansion of `freshRecState` is the actual capped raw-array start, not an artificial fresh
state with erased below-record information. -/
theorem ofRecState_freshRecState (hm : 1 ≤ m) (i₀ : Fin N) :
    ofRecState (freshRecState (N := N) hm i₀) = SwarmFreshArray.startState (N := N) m := by
  apply state_ext
  · funext i
    simpa [freshRecState, ofRecState] using (startState_pos (N := N) m i).symm
  · rfl

/-- The constructed initial state is in the simultaneous-record set. -/
theorem freshRecState_mem_srSet (hm : 1 ≤ m) (i₀ : Fin N) :
    freshRecState (N := N) hm i₀ ∈ srSet N m := by
  intro i
  rfl

/-- An exact two-block/raw-record splice from the canonical array start. -/
theorem start_pathW_record_middle (p : ℝ) (hm : 1 ≤ m) (i₀ : Fin N)
    {k r : ℕ} (qf : Fin k → JumpVec N)
    (hf : FirstRecord (extendPath qf) k (ofRecState (freshRecState (N := N) hm i₀)))
    (q : Fin r → JumpVec N)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀)))) :
    pathW p (k + r) (catWord qf q) (SwarmFreshArray.startState (N := N) m) =
      pathW p k qf (SwarmFreshArray.startState (N := N) m) *
        RecKernel.hitW p q (RecKernel.out hm qf (freshRecState (N := N) hm i₀)) := by
  have hraw := hitW_out_eq_raw p hm qf (freshRecState (N := N) hm i₀) hf q
  rw [RecKernel.hitW_of_firstRecord p q _ hq, if_pos hq,
    ofRecState_freshRecState] at hraw
  rw [show SwarmFreshArray.startState (N := N) m = capState m Swarming.Trajectory.initialWalkState from rfl,
    SwarmFreshArray.evolveFun_capState] at hraw
  rw [pathW_split p m k r (catWord qf q), prefWord_catWord, suffWord_catWord, ← hraw,
    RecKernel.hitW_of_firstRecord p q _ hq]

/-- **The three-block raw-array ↔ enriched-record dictionary, in general dimensions.**
The first two blocks are successive genuine record excursions, while the final raw future is
arbitrary and its weight is evaluated at the actual capped successor after both blocks. -/
theorem start_pathW_record_middle_future (p : ℝ) (hm : 1 ≤ m) (i₀ : Fin N)
    {k r s : ℕ} (qf : Fin k → JumpVec N)
    (hf : FirstRecord (extendPath qf) k (ofRecState (freshRecState (N := N) hm i₀)))
    (q : Fin r → JumpVec N)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀))))
    (qs : Fin s → JumpVec N) :
    pathW p (k + r + s) (catWord (catWord qf q) qs) (SwarmFreshArray.startState (N := N) m) =
      (pathW p k qf (SwarmFreshArray.startState (N := N) m) *
        RecKernel.hitW p q (RecKernel.out hm qf (freshRecState (N := N) hm i₀))) *
      pathW p s qs (capState m (runJ m (extendPath (catWord qf q)) (k + r))) := by
  rw [pathW_split p m (k + r) s (catWord (catWord qf q) qs),
    prefWord_catWord, suffWord_catWord, start_pathW_record_middle p hm i₀ qf hf q hq]

/-- **Raw positions inside the second record.**  At offset `0 ≤ t ≤ r`, including both onset and
endpoint, the concatenated raw path is the enriched `segOf` path translated by exactly one record
level.  No assumption that walkers are simultaneously at the record, and no duration-one hypothesis,
is made. -/
theorem patOf_record_suffix (hm : 1 ≤ m) (i₀ : Fin N) {k r : ℕ}
    (qf : Fin k → JumpVec N)
    (hf : FirstRecord (extendPath qf) k (ofRecState (freshRecState (N := N) hm i₀)))
    (q : Fin r → JumpVec N) (hr : 0 < r)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀))))
    {t : ℕ} (ht : t ≤ r) (i : Fin N) :
    SwarmFinHorizon.patOf (N := N) (catWord qf q) ⟨k + t, by omega⟩ i =
      1 + (SwarmSegKernel.segOf (RecKernel.out hm qf (freshRecState (N := N) hm i₀)) r q).p t i := by
  have hsplit := posAt_boundary (N := N) (catWord qf q) ht i
  have hpre := posAt_boundary_pref (N := N) (catWord qf q) i
  rw [suffWord_catWord] at hsplit
  rw [prefWord_catWord] at hpre
  rw [hpre] at hsplit
  have hend := congrFun (congrArg State.pos
    (ofRecState_out hm qf (freshRecState (N := N) hm i₀) hf)) i
  have hev := SwarmFreshPos.pos_evolveFun (extendPath qf) k
    (ofRecState (freshRecState (N := N) hm i₀)) i
  rw [ofRecState_freshRecState] at hev
  have hstart := startState_pos (N := N) m i
  have hrel := SwarmFreshPos.pos_evolveFun (extendPath q) t
    (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀))) i
  change SwarmFreshPos.posAt (SwarmFreshPos.seqOf (catWord qf q)) (k + t) i = _
  rw [SwarmFreshCyl.posAt_seqOf_eq_extendPath (catWord qf q) (k + t) i (by omega), hsplit]
  rw [SwarmFreshCyl.segOf_p_of_firstRecord hr q hq]
  rw [SwarmSegKernel.relP, hrel]
  change (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀))).pos i =
    (evolveFun (extendPath qf) k (ofRecState (freshRecState (N := N) hm i₀))).pos i - 1 at hend
  rw [ofRecState_freshRecState] at hend
  omega

/-- The enriched duration of the middle block is exactly its raw word length. -/
theorem dur_record_suffix (hm : 1 ≤ m) (i₀ : Fin N) {k r : ℕ}
    (qf : Fin k → JumpVec N) (hr : 0 < r) (q : Fin r → JumpVec N)
    (hq : FirstRecord (extendPath q) r
      (ofRecState (RecKernel.out hm qf (freshRecState (N := N) hm i₀)))) :
    (SwarmSegKernel.segOf (RecKernel.out hm qf (freshRecState (N := N) hm i₀)) r q).dur = r :=
  SwarmFreshCyl.segOf_dur_of_firstRecord hr q hq

end SwarmRawRecord

