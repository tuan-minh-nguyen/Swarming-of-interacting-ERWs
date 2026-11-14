/-
Global raw-horizon cover of coherent enriched trajectories.

A coherent trajectory is generated at every step from the previous atom's
actual endpoint record state.  This is the genuine support of `infLaw`, rather
than mere segment compatibility (which forgets record states).  The raw path
is decoded from its nearest-neighbour steps, decomposed by the accepted unique
maximal completed-record/unfinished-tail decomposition, and lifted back to the
canonical enriched cylinders.
-/
import Swarm.CanonicalInfiniteFibres
import Swarm.RawWindowIdentification
import Swarm.InfSegCompat

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmRawGlobalCover

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open SwarmCanonicalFixedHorizon SwarmCanonicalJoinedWindow
open SwarmRawWindowIdentification SwarmEnrichedRawTail
open SwarmChainAssemble SwarmFinFuture SwarmFinHorizon SwarmFreshPos
open SwarmInfSeg

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The nearest-neighbour word decoded from a path through time `K`. -/
def pathWord {N K : ℕ} (X : ℕ → Fin N → ℤ) : Fin K → JumpVec N :=
  fun t i => decide (X (t.1 + 1) i = X t.1 i + 1)

/-- Decoding a zero-based nearest-neighbour path recovers every position in
its horizon.  This is entirely pathwise and needs no record hypotheses. -/
theorem posAt_pathWord {N K : ℕ} (X : ℕ → Fin N → ℤ)
    (hzero : ∀ i, X 0 i = 0)
    (hstep : ∀ n i, X (n + 1) i = X n i + 1 ∨ X (n + 1) i = X n i - 1) :
    ∀ {n : ℕ}, n ≤ K → ∀ i,
      posAt (seqOf (pathWord X (K := K))) n i = X n i := by
  intro n
  induction n with
  | zero => intro _ i; rw [posAt_zero, hzero]
  | succ n ih =>
      intro hn i
      have hnK : n < K := by omega
      rw [posAt_succ, ih (by omega) i]
      have hval : seqOf (pathWord X (K := K)) n i = pathWord X (K := K) ⟨n, hnK⟩ i := by
        exact congrFun (seqOf_val (pathWord X (K := K)) ⟨n, hnK⟩) i
      rw [hval]
      rcases hstep n i with h | h
      · simp [pathWord, h]
      · have hne : ¬ X n i - 1 = X n i + 1 := by omega
        simp [pathWord, h, hne]
        ring

/-- The finite raw pattern of the decoded word is exactly the original path. -/
theorem patOf_pathWord {N K : ℕ} (X : ℕ → Fin N → ℤ)
    (hzero : ∀ i, X 0 i = 0)
    (hstep : ∀ n i, X (n + 1) i = X n i + 1 ∨ X (n + 1) i = X n i - 1) :
    pathPat (N := N) K X = patOf (N := N) (pathWord X (K := K)) := by
  funext n i
  exact (posAt_pathWord X hzero hstep (Nat.le_of_lt_succ n.2) i).symm

/-- The first component of a coherent enriched trajectory is a genuine
first-record atom at the indicated state. -/
def CanonicalAtom (hm : 1 ≤ m) (y : RecState N m) (a : SwarmInfSeg.Pair N m) : Prop :=
  ∃ b : RawBlock N, FirstRecord (extendPath b.2) b.1 (ofRecState y) ∧
    a = (SwarmSegKernel.segOf y b.1 b.2, RecKernel.out hm b.2 y)

/-- Record-state coherence: the initial atom starts at `y`, and every later
atom starts at the preceding atom's actual endpoint state. -/
def Coherent (hm : 1 ≤ m) (y : RecState N m) (A : ℕ → SwarmInfSeg.Pair N m) : Prop :=
  CanonicalAtom hm y (A 0) ∧ ∀ n, CanonicalAtom hm (A n).2 (A (n + 1))

/-- Coherence is inherited by the genuine record shift, with the first
atom's endpoint as the new initial state. -/
theorem coherent_shift {hm : 1 ≤ m} {y : RecState N m}
    {A : ℕ → SwarmInfSeg.Pair N m} (hA : Coherent hm y A) :
    Coherent hm (A 0).2 (trajShift A) := by
  refine ⟨hA.2 0, ?_⟩
  intro n
  exact hA.2 (n + 1)

end SwarmRawGlobalCover
