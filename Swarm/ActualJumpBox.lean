/-
# Direction E, stage 1: exact finite-window jump-box masses of the actual array

The stopped record kernel `SimJump.RecKernel.hitKKernel` of `areas/recordkernel` is a countable
sum over finite *first-record paths* `q : Fin k → JumpVec N` with weight `hitW p q y = pathW p k q
(ofRecState y)`.  Identifying its iterates with the actual array's record statistics needs, as a
first genuine stage, the exact probability that the actual interacting array produces a
prescribed finite jump word from its (deterministic) start state.

That is what this file computes.  For a word `q : Fin r → JumpVec N` the box

  `jbox p m r q = {ω | ∀ n < r, ∀ i, nextJumpVec p m ω n i = q n i}`

is proved to be the cylinder over the automaton's own read coordinates (`jbox_eq_cyl`), the read
coordinates are injective (`jcoord_injective`, from the letter-automaton injectivity of
`SymmLetters`), and hence

  `mass_jbox : arrayMeasure N (jbox p m r q) = ∏ (n,i), jumpWeight (q n i) (alpha n i)`,

where `alpha n i` is the *actual* threshold in force at step `n` along the word.  Composing with
the chain algebra of `SimJumpPath` gives

  `mass_jbox_pathW : arrayMeasure N (jbox p m r q) = ofReal (pathW p r q (ofRecState y₀))`

for the start state `y₀` of `RecordStartLaw.zeroState`, i.e. exactly the weight with which
`hitKInfT` counts the first block.  No probability is postulated: this is a product-measure
computation on the fresh read coordinates of the actual array.

Nothing here asserts the law of *later* blocks (which needs the strong Markov property at the
record times) and nothing here asserts `Swarm.Ballistic`, `RegenAvailable` or the main theorem.
-/
import Swarm.SymmLetters
import Swarm.SymmFairLaw
import Swarm.CurrentState
import Swarm.SimJumpPath
import Swarm.RecordStartLaw

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace M5FirstBlock

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model Swarming.FairWalk
open Swarming.Transition SimJump Swarming.CurrentState

variable {N : ℕ}

/-! ### The pure jump-word recursion

`runJ q` is the walk state obtained by following the prescribed jump word `q`.  It is the same
recursion as `SymmLetters.runL` driven by the letters `(b,b)`, which is what provides both the
identification with the actual trajectory and the injectivity of the read coordinates. -/

/-- One step of the interacting walk driven by a prescribed jump vector. -/
noncomputable def jnext (_m : ℕ) (v : JumpVec N) (s : WalkState N) : WalkState N where
  pos i := s.pos i + jumpShift (v i)
  ell i x := s.ell i x + if x = s.pos i + jumpShift (v i) then 1 else 0

/-- The walk state after following the jump word `q`. -/
noncomputable def runJ (m : ℕ) (q : ℕ → JumpVec N) : ℕ → WalkState N
  | 0 => initialWalkState
  | n + 1 => jnext m (q n) (runJ m q n)

@[simp] theorem runJ_zero (m : ℕ) (q : ℕ → JumpVec N) : runJ m q 0 = initialWalkState := rfl

@[simp] theorem runJ_succ (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) :
    runJ m q (n + 1) = jnext m (q n) (runJ m q n) := rfl

/-! ### Driving the letter automaton by a jump word -/

/-- The letter attached to a prescribed jump: both bits are the jump.  Then `lstep` is the jump
whatever the threshold is. -/
def qq (v : JumpVec N) : Fin N → Bool × Bool := fun i => (v i, v i)

theorem lstep_qq (v : JumpVec N) (i : Fin N) (α : ℝ) :
    FairWalk.lstep (qq v i) α = jumpShift (v i) := by
  unfold FairWalk.lstep jumpShift qq
  by_cases hα : α = 1 / 2
  · rw [if_pos hα]
  · rw [if_neg hα]

theorem lamNextState_qq (p : ℝ) (m : ℕ) (v : JumpVec N) (s : WalkState N) :
    FairWalk.lamNextState p m (qq v) s = jnext m v s := by
  have hpos : FairWalk.lamNextPos p m (qq v) s = fun i => s.pos i + jumpShift (v i) := by
    funext i
    simp only [FairWalk.lamNextPos, lstep_qq]
  cases s with
  | mk pos ell =>
    simp only [FairWalk.lamNextState, jnext, hpos]

theorem runL_qq (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) :
    ∀ n, FairWalk.runL p m (fun t => qq (q t)) n = runJ m q n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FairWalk.runL_succ, runJ_succ, ih, lamNextState_qq]

/-! ### Read coordinates of a jump word and their injectivity -/

/-- The coordinate read at step `n` by walker `i` along the jump word `q`. -/
noncomputable def jcoord (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    Fin N × ℤ × ℕ :=
  (i, (runJ m q n).pos i, (runJ m q n).ell i ((runJ m q n).pos i))

theorem jcoord_eq_readC (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    jcoord p m q n i = FairWalk.readC p m (fun t => qq (q t)) n i := by
  unfold jcoord FairWalk.readC
  rw [runL_qq]

/-- **Every coordinate is read at most once along a jump word.** -/
theorem jcoord_injective (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (r : ℕ) :
    Function.Injective (fun ni : Fin r × Fin N => jcoord p m q ni.1 ni.2) := by
  have heq : (fun ni : Fin r × Fin N => jcoord p m q ni.1 ni.2)
      = (fun ni : Fin r × Fin N =>
          FairWalk.readC p m (fun t => qq (q t)) ni.1 ni.2) := by
    funext ni
    exact jcoord_eq_readC p m q ni.1 ni.2
  rw [heq]
  exact FairWalk.readC_injective (p := p) (m := m) (fun t => qq (q t)) r

/-- The actual threshold in force at step `n` along the word `q`. -/
noncomputable def jalpha (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) (i : Fin N) : ℝ :=
  rightProbability p m (runJ m q n).ell i ((runJ m q n).pos i)

/-! ### The trajectory of an array follows the recursion of its own jump word -/

theorem nextWalkState_eq_jnext (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) :
    nextWalkState p m ω (trajectory p m ω n) =
      jnext m (nextJumpVec p m ω n) (trajectory p m ω n) := by
  have hpos : Trajectory.nextPos p m ω (trajectory p m ω n)
      = fun i => (trajectory p m ω n).pos i + jumpShift (nextJumpVec p m ω n i) := by
    funext i
    exact CurrentState.nextPos_eq_nextJumpVec p m ω n i
  simp only [nextWalkState, jnext, hpos]

/-- **The actual trajectory is the recursion of its own jump word.** -/
theorem trajectory_eq_runJ (p : ℝ) (m : ℕ) (ω : Array N) :
    ∀ n, trajectory p m ω n = runJ m (fun t => nextJumpVec p m ω t) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ, runJ_succ, ← ih]
      exact nextWalkState_eq_jnext p m ω n


/-! ### The capped state of a walk state and the chain recursion

`SimJump.State N m` stores the local times capped at `m`.  `capState m s` is the capped state of
the walk state `s`; the one-step recursion of the record chain is exactly the jump recursion of
`runJ` under this cap. -/

/-- The capped record-chain state of a walk state. -/
noncomputable def capState (m : ℕ) (s : WalkState N) : SimJump.State N m where
  pos := s.pos
  eta i x := SimJump.cap m (s.ell i x)
  hcap _ _ := SimJump.cap_le m _

theorem capState_pos (m : ℕ) (s : WalkState N) : (capState m s).pos = s.pos := rfl

theorem capState_eta (m : ℕ) (s : WalkState N) (i : Fin N) (x : ℤ) :
    (capState m s).eta i x = min (s.ell i x) m := rfl

/-- Capping commutes with the interaction step. -/
theorem step_capState (m : ℕ) (v : JumpVec N) (s : WalkState N) :
    SimJump.step m (capState m s) v = capState m (jnext m v s) := by
  have hpos : SimJump.stepPos (capState m s) v = fun i => s.pos i + jumpShift (v i) := by
    funext i
    simp only [SimJump.stepPos, capState_pos]
    cases h : v i <;> simp [jumpShift, h]
  have heta : ∀ (i : Fin N) (x : ℤ),
      (SimJump.step m (capState m s) v).eta i x = min ((jnext m v s).ell i x) m := by
    intro i x
    show (if x = SimJump.stepPos (capState m s) v i then
        SimJump.cap m ((capState m s).eta i x + 1) else (capState m s).eta i x) = _
    by_cases hx : x = s.pos i + jumpShift (v i)
    · have hx' : x = SimJump.stepPos (capState m s) v i := by rw [hpos]; exact hx
      rw [if_pos hx', capState_eta]
      simp only [jnext, hx, if_true, SimJump.cap]
      omega
    · have hx' : ¬ x = SimJump.stepPos (capState m s) v i := by rw [hpos]; exact hx
      rw [if_neg hx', capState_eta]
      simp only [jnext, hx, if_false, Nat.add_zero]
  refine CurrentState.recordState_ext ?_ ?_
  · exact hpos
  · funext i x
    exact heta i x

/-- The chain recursion of the capped state along a jump word. -/
theorem evolveFun_capState (m : ℕ) (q : ℕ → JumpVec N) :
    ∀ n, SimJump.evolveFun q n (capState m initialWalkState) = capState m (runJ m q n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SimJump.evolveFun_succ, runJ_succ, ih, step_capState]

/-- The right-jump probability only depends on the capped local times, so it agrees with the
uncapped `rightProbability` of the walk state. -/
theorem qRight_capState (p : ℝ) (m : ℕ) (s : WalkState N) (i : Fin N) :
    SimJump.qRight p m (capState m s) i = rightProbability p m s.ell i (s.pos i) := by
  have h1 : SimJump.qRight p m (capState m s) i
      = if m ≤ Model.otherVisits (fun j x => (capState m s).eta j x) i ((capState m s).pos i)
        then p else 1 / 2 := by
    rw [SimJump.qRight, CurrentState.otherVisits_erase_eq]
  have h2 : m ≤ Model.otherVisits s.ell i (s.pos i) ↔
      m ≤ Model.otherVisits (fun j y => min (s.ell j y) m) i (s.pos i) :=
    Model.excited_capped_iff m s.ell i (s.pos i)
  have h3 : (fun j x => (capState m s).eta j x) = fun j y => min (s.ell j y) m := rfl
  have h4 : (capState m s).pos = s.pos := rfl
  rw [h1, h3, h4]
  unfold rightProbability
  unfold Model.Excited
  by_cases hc : m ≤ Model.otherVisits s.ell i (s.pos i)
  · rw [if_pos hc, if_pos (h2.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (h2.mpr h))]

/-- The one-step joint weight of the capped state is the product of the walk state's own
one-walker weights. -/
theorem stepW_capState (p : ℝ) (m : ℕ) (s : WalkState N) (v : JumpVec N) :
    SimJump.stepW p m (capState m s) v
      = ∏ i : Fin N, jumpWeight (v i) (rightProbability p m s.ell i (s.pos i)) := by
  simp only [SimJump.stepW, SimJump.stepFactor, jumpWeight]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [qRight_capState]

/-! ### The initial state is the paper's start record state -/

/-- The capped initial state of the record chain. -/
noncomputable def startState (m : ℕ) : SimJump.State N m := capState m initialWalkState

theorem startState_pos (m : ℕ) (i : Fin N) : (startState (N := N) m).pos i = 0 := rfl

theorem startState_eta (m : ℕ) (hm : 1 ≤ m) (i : Fin N) (x : ℤ) :
    (startState (N := N) m).eta i x = if x = 0 then 1 else 0 := by
  simp only [startState, capState_eta]
  have h : initialWalkState.ell i x = if x = 0 then 1 else 0 := rfl
  rw [h]
  by_cases hx : x = 0
  · rw [if_pos hx]; exact min_eq_left hm
  · rw [if_neg hx]; exact min_eq_left (Nat.zero_le m)

/-- **The compact start record state expands to the chain's initial state.** -/
theorem ofRecState_zeroState (m : ℕ) (hm : 1 ≤ m) [Nonempty (Fin N)] :
    SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm)
      = startState (N := N) m := by
  have hpos : ∀ i : Fin N,
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm)).pos i
        = (startState (N := N) m).pos i := fun i => rfl
  have heta : ∀ (i : Fin N) (x : ℤ),
      (SimJump.Record.ofRecState (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m) hm)).eta i x
        = (startState (N := N) m).eta i x := by
    intro i x
    show ((SwarmRecordMeas.StartLaw.zeta (N := N) m hm i x).val) = (startState (N := N) m).eta i x
    rw [startState_eta m hm i x]
    by_cases hx : x = 0
    · subst hx
      rw [show (SwarmRecordMeas.StartLaw.zeta (N := N) m hm i 0)
          = ⟨1, Nat.lt_succ_of_le hm⟩ from SwarmRecordMeas.StartLaw.zeta_at_zero (N := N) hm i]
      rfl
    · rw [if_neg hx]
      show ((SwarmRecordMeas.StartLaw.zeta (N := N) m hm i x)).val = 0
      rw [show (SwarmRecordMeas.StartLaw.zeta (N := N) m hm i x) = 0 from by
        simp only [SwarmRecordMeas.StartLaw.zeta, hx, if_false]]
      simp
  refine CurrentState.recordState_ext ?_ ?_
  · funext i
    exact hpos i
  · funext i x
    exact heta i x

/-! ### The actual jump box of a finite word -/

/-- Extend a finite word to a jump sequence (the tail is irrelevant). -/
noncomputable def extJump (r : ℕ) (q : Fin r → JumpVec N) : ℕ → JumpVec N :=
  fun n => if h : n < r then q ⟨n, h⟩ else fun _ => true

theorem extJump_apply {r : ℕ} (q : Fin r → JumpVec N) {n : ℕ} (hn : n < r) :
    extJump r q n = q ⟨n, hn⟩ := dif_pos hn

/-- The event that the actual array follows the jump word `q` for its first `r` steps. -/
noncomputable def jbox (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) : Set (Array N) :=
  {ω | ∀ (n : Fin r) (i : Fin N), nextJumpVec p m ω (n : ℕ) i = q n i}

theorem runJ_congr (m : ℕ) {q q' : ℕ → JumpVec N} (n : ℕ) (h : ∀ s, s < n → q s = q' s) :
    runJ m q n = runJ m q' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runJ_succ, runJ_succ, ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self n))),
        h n (Nat.lt_succ_self n)]

/-- Along a prescribed prefix of jumps, the actual trajectory is the pure jump recursion. -/
theorem trajectory_eq_runJ_of_prefix (p : ℝ) (m : ℕ) (ω : Array N) {q : ℕ → JumpVec N} {n : ℕ}
    (h : ∀ t : ℕ, t < n → ∀ i : Fin N, nextJumpVec p m ω t i = q t i) :
    trajectory p m ω n = runJ m q n := by
  rw [trajectory_eq_runJ]
  refine runJ_congr m n (fun s hs => ?_)
  funext i
  exact h s hs i


/-! ### The box as a cylinder over the word's own read coordinates -/

theorem mem_jumpSet_iff {b : Bool} {α u : ℝ} :
    u ∈ jumpSet b α ↔ (if u ≤ α then true else false) = b := by
  by_cases h : u ≤ α <;> cases b <;> simp [jumpSet, h]
  exact not_le.mp h

theorem measurableSet_jumpSet (b : Bool) (α : ℝ) : MeasurableSet (jumpSet b α) := by
  cases b
  · simpa only [jumpSet, Bool.false_eq_true, if_false] using measurableSet_Ioi (a := α)
  · simpa only [jumpSet, if_true] using measurableSet_Iic (a := α)

/-- Along a word, the actual trajectory is the word's own recursion. -/
theorem trajectory_eq_runJ_ext (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) (ω : Array N)
    (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) :
    trajectory p m ω n = runJ m (extJump r q) n := by
  refine trajectory_eq_runJ_of_prefix p m ω (fun t ht i => ?_)
  rw [extJump_apply q (lt_of_lt_of_le ht hn)]
  exact hbox ⟨t, lt_of_lt_of_le ht hn⟩ i

theorem departureCoord_eq_jcoord (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (ω : Array N) (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) (i : Fin N) :
    departureCoord p m ω n i = jcoord p m (extJump r q) n i := by
  unfold departureCoord jcoord
  rw [trajectory_eq_runJ_ext p m r q ω hbox hn]

theorem currentAlpha_eq_jalpha (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (ω : Array N) (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) (i : Fin N) :
    currentAlpha p m ω n i = jalpha p m (extJump r q) n i := by
  unfold currentAlpha jalpha
  rw [trajectory_eq_runJ_ext p m r q ω hbox hn]

/-- **The jump box is the cylinder over the word's read coordinates.** -/
theorem jbox_eq_cyl (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    jbox p m r q = ⋂ (n : Fin r) (i : Fin N),
      (fun ω : Array N => ω (jcoord p m (extJump r q) (n : ℕ) i)) ⁻¹'
        jumpSet (q n i) (jalpha p m (extJump r q) (n : ℕ) i) := by
  ext ω
  constructor
  · intro hbox
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro n i
    have hn : (n : ℕ) ≤ r := le_of_lt n.2
    rw [← departureCoord_eq_jcoord p m r q ω hbox hn i,
      ← currentAlpha_eq_jalpha p m r q ω hbox hn i]
    exact mem_jumpSet_iff.mpr (hbox n i)
  · intro hcyl
    have hcyl' : ∀ (k : ℕ) (hk : k < r) (i : Fin N),
        ω (jcoord p m (extJump r q) k i) ∈
          jumpSet (q ⟨k, hk⟩ i) (jalpha p m (extJump r q) k i) :=
      fun k hk i => Set.mem_iInter.mp (Set.mem_iInter.mp hcyl ⟨k, hk⟩) i
    have key : ∀ k : ℕ, ∀ hk : k < r, ∀ i : Fin N,
        nextJumpVec p m ω k i = q ⟨k, hk⟩ i := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk i
        have hpre : ∀ t : ℕ, t < k → ∀ j : Fin N, nextJumpVec p m ω t j = extJump r q t j := by
          intro t ht j
          rw [extJump_apply q (lt_trans ht hk)]
          exact ih t ht (lt_trans ht hk) j
        have htr : trajectory p m ω k = runJ m (extJump r q) k :=
          trajectory_eq_runJ_of_prefix p m ω hpre
        have hcoord : departureCoord p m ω k i = jcoord p m (extJump r q) k i := by
          unfold departureCoord jcoord
          rw [htr]
        have halpha : currentAlpha p m ω k i = jalpha p m (extJump r q) k i := by
          unfold currentAlpha jalpha
          rw [htr]
        rw [nextJumpVec, hcoord, halpha]
        exact mem_jumpSet_iff.mp (hcyl' k hk i)
    intro n i
    exact key (n : ℕ) n.2 i

/-! ### The exact mass of a jump box -/

theorem jalpha_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ)
    (i : Fin N) : 0 < jalpha p m q n i := by
  unfold jalpha rightProbability
  split
  · linarith
  · norm_num

theorem jalpha_lt_one {p : ℝ} (hp1 : p < 1) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ)
    (i : Fin N) : jalpha p m q n i < 1 := by
  unfold jalpha rightProbability
  split
  · linarith
  · norm_num

theorem jumpWeight_nonneg {b : Bool} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    0 ≤ jumpWeight b α := by
  cases b
  · simp only [jumpWeight, Bool.false_eq_true, if_false]; linarith
  · simp only [jumpWeight, if_true]; linarith

theorem uniform01_jumpSet {b : Bool} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    uniform01 (jumpSet b α) = ENNReal.ofReal (jumpWeight b α) := by
  cases b
  · simp only [jumpSet, Bool.false_eq_true, if_false, jumpWeight]
    exact uniform01_Ioi h0 h1
  · simp only [jumpSet, if_true, jumpWeight]
    exact uniform01_Iic h0 h1

/-- **Finite-cylinder product law** for distinct coordinates of the uniform array. -/
theorem measure_cyl_prod {ι : Type*} [Fintype ι] (c : ι → Fin N × ℤ × ℕ)
    (hc : Function.Injective c) (I : ι → Set ℝ) (hI : ∀ q, MeasurableSet (I q)) :
    arrayMeasure N (⋂ q, (fun ω : Array N => ω (c q)) ⁻¹' I q) = ∏ q, uniform01 (I q) := by
  have h := SwarmIID.indep_iInter_comp (μ := arrayMeasure N) (array_independent N) hc I hI
  rw [h]
  exact Finset.prod_congr rfl fun q _ => arrayMeasure_preimage_set N (c q) (I q) (hI q)

/-- The jump box as a cylinder over the finite index type `Fin r × Fin N`. -/
theorem jbox_eq_cyl_prod (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    jbox p m r q = ⋂ ni : Fin r × Fin N,
      (fun ω : Array N => ω (jcoord p m (extJump r q) (ni.1 : ℕ) ni.2)) ⁻¹'
        jumpSet (q ni.1 ni.2) (jalpha p m (extJump r q) (ni.1 : ℕ) ni.2) := by
  rw [jbox_eq_cyl]
  ext ω
  simp only [Set.mem_iInter, Set.mem_preimage, Prod.forall]

/-- **The exact mass of a finite jump box**: the product of the actual one-walker thresholds. -/
theorem mass_jbox (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (r : ℕ)
    (q : Fin r → JumpVec N) :
    arrayMeasure N (jbox p m r q) =
      ENNReal.ofReal (∏ ni : Fin r × Fin N,
        jumpWeight (q ni.1 ni.2) (jalpha p m (extJump r q) (ni.1 : ℕ) ni.2)) := by
  rw [jbox_eq_cyl_prod,
    measure_cyl_prod (fun ni : Fin r × Fin N => jcoord p m (extJump r q) (ni.1 : ℕ) ni.2)
      (jcoord_injective p m (extJump r q) r) _
      (fun ni => measurableSet_jumpSet _ _)]
  rw [show (∏ ni : Fin r × Fin N,
        uniform01 (jumpSet (q ni.1 ni.2) (jalpha p m (extJump r q) (ni.1 : ℕ) ni.2)))
      = ∏ ni : Fin r × Fin N,
        ENNReal.ofReal (jumpWeight (q ni.1 ni.2)
          (jalpha p m (extJump r q) (ni.1 : ℕ) ni.2)) from
    Finset.prod_congr rfl fun ni _ =>
      uniform01_jumpSet (jalpha_pos hp0 m (extJump r q) _ _)
        (jalpha_lt_one hp1 m (extJump r q) _ _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (fun ni _ =>
    jumpWeight_nonneg (jalpha_pos hp0 m (extJump r q) _ _)
      (jalpha_lt_one hp1 m (extJump r q) _ _) (b := q ni.1 ni.2))]

/-! ### Comparison with the chain algebra's path weight -/

/-- The chain algebra's path weight is the product of its one-step weights. -/
theorem pathWFun_eq_prod_fin (p : ℝ) (u : ℕ → JumpVec N) :
    ∀ (k : ℕ) (s : SimJump.State N m),
      SimJump.pathWFun p u k s
        = ∏ n : Fin k, SimJump.stepW p m (SimJump.evolveFun u n s) (u n) := by
  intro k
  induction k with
  | zero => intro s; simp [SimJump.pathWFun, SimJump.pathW]
  | succ k ih =>
      intro s
      rw [SimJump.pathWFun_succ, ih, Fin.prod_univ_castSucc]
      simp

theorem pathW_eq_pathWFun_ext (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    pathW p r q (startState (N := N) m)
      = SimJump.pathWFun p (extJump r q) r (startState (N := N) m) := by
  rw [← SimJump.pathW_eq_pathWFun p (extJump r q) r (startState (N := N) m)]
  congr 2
  funext i
  exact (extJump_apply q i.2).symm

theorem stepW_evolveFun_startState (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    {n : ℕ} (hn : n < r) :
    SimJump.stepW p m (SimJump.evolveFun (extJump r q) n (startState (N := N) m))
        (extJump r q n)
      = ∏ i : Fin N, jumpWeight (q ⟨n, hn⟩ i) (jalpha p m (extJump r q) n i) := by
  have hev : SimJump.evolveFun (extJump r q) n (startState (N := N) m)
      = capState m (runJ m (extJump r q) n) := by
    rw [startState, evolveFun_capState]
  rw [hev, stepW_capState]
  exact Finset.prod_congr rfl fun i _ => by simp only [jalpha, extJump_apply q hn]

/-- **The exact mass of a finite jump box, in the frozen-record notation of `hitKInfT`.** -/
theorem mass_jbox_pathW (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (r : ℕ)
    (q : Fin r → JumpVec N) :
    arrayMeasure N (jbox p m r q)
      = ENNReal.ofReal (pathW p r q (startState (N := N) m)) := by
  rw [mass_jbox hp0 hp1 m r q, pathW_eq_pathWFun_ext p m r q, pathWFun_eq_prod_fin]
  congr 1
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun n _ => ?_
  exact (stepW_evolveFun_startState p m r q n.2).symm

end M5FirstBlock
