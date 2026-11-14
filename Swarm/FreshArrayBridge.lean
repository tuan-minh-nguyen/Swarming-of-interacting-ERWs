/-
# the finite fresh-segment measure on the actual array path interface

`SwarmFreshCyl.segKpos_wordCyl` (`Swarm/FreshCyl.lean`, integrated) says: for a simultaneous-record
start state `y ∈ srSet`, a first-record word `q : Fin k → JumpVec N` that keeps every walker
strictly above the record level (`PosSeqFin q`), the strict-positivity part of the first-segment
law gives the segment cylinder `wordCyl q` exactly the mass

  `segKpos p hm y (wordCyl q) = ENNReal.ofReal (hitW p q y)`,

and `hitW p q y = pathW p k q (ofRecState y)` is the same from every fresh start.

On the actual-array side the corresponding theorem is `M5FirstBlock.mass_jbox_pathW`
(`Swarm/ActualJumpBox.lean`, integrated):

  `arrayMeasure N (M5FirstBlock.jbox p m r q) = ENNReal.ofReal (pathW p r q (startState))`.

That module cannot be imported in a 15 GiB session: measured peak RSS of `import ActualJumpBox`
alone is 13.7 GB (it pulls in `RecordStartLaw`), and the combined import with `FreshCyl` is
OOM-killed at 13.9 GB.  This file therefore re-derives the *array word-mass computation* from the
light model modules (`CurrentState`, `Trajectory`, `UniformArray`, `TransitionLaw`,
`FreshIndependence`, all at the `import Mathlib` memory baseline), with one simplification: the
injectivity of the read coordinates is proved directly from the deterministic jump recursion and
the local-time counting identity, instead of through the letter automaton's `readC_injective`.

Contents.

* §1 `jnext`/`runJ`: the pure jump recursion; `runJ_pos` and `runJ_ell_eq_localTime` identify its
  positions and local times with `SwarmFreshPos.posAt` and `SwarmTrajectory.localTime`.
* §2 `jcoord` (walker, position, local time at the current position) and `jcoord_injective`:
  along a jump word every read coordinate is used at most once.  This is the only input the
  product-measure computation needs.
* §3 `jbox` is the cylinder over the word's own read coordinates (`jbox_eq_cyl`), the array
  trajectory follows its word on the box (`trajectory_eq_runJ_extendPath`), and
  `mass_jbox_pathW` is the exact array mass of the box — the same statement as
  `M5FirstBlock.mass_jbox_pathW`, from the same model definitions.
* §4 `freshStart_startState`: the canonical start state of the array recursion is a
  `SwarmFreshPos.FreshStart`; hence, for `y ∈ srSet`, the array box of a fresh first-record word
  carries exactly `pathW p k q (ofRecState y) = hitW p q y`.
* §5 the bridge: `array_jbox_mass_eq_segKpos` —

  `arrayMeasure N (jbox p m k q) = segKpos p hm y (wordCyl q)`

  for every `y ∈ srSet`, `k ≥ 1`, first-record word `q` with `PosSeqFin q`, at every
  `1/2 < p < 1`, `m ≥ 1`.  Plus the exact boundary-point correspondence
  (`array_trajectory_pos_eq_wordCyl`, `wordCyl_boundary_eq_array`): on the box, the array's
  position path *is* the `p` component of every segment in `wordCyl q`.

Scope.  Finite horizon `k` only.  Nothing here asserts the law of later blocks, stationarity,
`hstruct`, regeneration, `(ED)` or a speed.  The `hfr`/`hy`/`hq` premises are kept intact: the
mass identity is the finite first-segment one; `hfr` is what turns `pathW` into the record chain's
`hitW`.
-/
import Swarm.FreshCyl
import Swarm.CurrentState
import Swarm.Trajectory
import Swarm.UniformArray
import Swarm.TransitionLaw
import Swarm.FreshIndependence

open MeasureTheory ProbabilityTheory Set
open Classical
open scoped ENNReal BigOperators

namespace SwarmFreshArray

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model
open Swarming.Transition SimJump Swarming.CurrentState
open SimJump.Record SwarmRec

set_option autoImplicit false

variable {N : ℕ}

/-! ## 1. The pure jump-word recursion -/

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

/-- The position path of `runJ` is the net displacement of the jump word. -/
theorem runJ_pos (m : ℕ) (q : ℕ → JumpVec N) :
    ∀ (n : ℕ) (i : Fin N), (runJ m q n).pos i = SwarmFreshPos.posAt q n i := by
  intro n
  induction n with
  | zero => intro i; simp [SwarmFreshPos.posAt]
  | succ n ih =>
      intro i
      rw [SwarmFreshPos.posAt_succ, runJ_succ]
      change (runJ m q n).pos i + jumpShift (q n i)
        = SwarmFreshPos.posAt q n i + (if q n i = true then (1 : ℤ) else -1)
      rw [ih i]
      simp only [Swarming.Transition.jumpShift]

/-- The local time stored by `runJ` at a site is the path local time of its position path. -/
theorem runJ_ell_eq_localTime (m : ℕ) (q : ℕ → JumpVec N) :
    ∀ (n : ℕ) (i : Fin N) (x : ℤ),
      (runJ m q n).ell i x = localTime (fun t => (runJ m q t).pos i) n x := by
  intro n
  induction n with
  | zero => intro i x; simp [initialWalkState, localTime_zero, eq_comm]
  | succ n ih =>
      intro i x
      rw [localTime_succ, runJ_succ]
      change (runJ m q n).ell i x
          + (if x = (runJ m q n).pos i + jumpShift (q n i) then 1 else 0)
        = localTime (fun t => (runJ m q t).pos i) n x
          + if (runJ m q n).pos i + jumpShift (q n i) = x then 1 else 0
      rw [ih i x]
      simp only [eq_comm]

/-! ## 2. Read coordinates of a jump word and their injectivity -/

/-- The coordinate read at step `n` by walker `i` along the jump word `q`. -/
noncomputable def jcoord (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) (i : Fin N) :
    Fin N × ℤ × ℕ :=
  (i, (runJ m q n).pos i, (runJ m q n).ell i ((runJ m q n).pos i))

/-- **Every read coordinate is used at most once along a jump word.**  If walker `i` reads the
same site with the same local time at two times, those times coincide: at the later time the
local time at that site is strictly larger (`localTime_lt_of_visit`), since the walker is there. -/
theorem jcoord_injective (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (r : ℕ) :
    Function.Injective (fun ni : Fin r × Fin N => jcoord p m q ni.1 ni.2) := by
  rintro ⟨n, i⟩ ⟨n', i'⟩ h
  simp only [jcoord, Prod.mk.injEq] at h
  obtain ⟨hii, hpos, hell⟩ := h
  subst hii
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exfalso
    have hvisit := Swarming.Trajectory.localTime_lt_of_visit
      (X := fun t => (runJ m q t).pos i) (x := (runJ m q n').pos i) hlt rfl
    have heqlt : localTime (fun t => (runJ m q t).pos i) n ((runJ m q n').pos i)
        = localTime (fun t => (runJ m q t).pos i) n' ((runJ m q n').pos i) := by
      rw [← runJ_ell_eq_localTime m q n i, ← runJ_ell_eq_localTime m q n' i]
      simpa only [hpos] using hell
    exact (ne_of_lt hvisit) heqlt
  · exact Prod.ext heq rfl
  · exfalso
    have hvisit := Swarming.Trajectory.localTime_lt_of_visit
      (X := fun t => (runJ m q t).pos i) (x := (runJ m q n).pos i) hgt rfl
    have heqlt : localTime (fun t => (runJ m q t).pos i) n ((runJ m q n).pos i)
        = localTime (fun t => (runJ m q t).pos i) n' ((runJ m q n).pos i) := by
      rw [← runJ_ell_eq_localTime m q n i, ← runJ_ell_eq_localTime m q n' i]
      simpa only [← hpos] using hell
    exact (ne_of_gt hvisit) heqlt

/-- The actual threshold in force at step `n` along the word `q`. -/
noncomputable def jalpha (p : ℝ) (m : ℕ) (q : ℕ → JumpVec N) (n : ℕ) (i : Fin N) : ℝ :=
  rightProbability p m (runJ m q n).ell i ((runJ m q n).pos i)

/-! ## 3. The actual trajectory follows its own jump word -/

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

/-! ### The capped state of a walk state and the chain recursion -/

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

/-! ### The canonical start state of the array recursion -/

/-- The capped initial state of the record chain: all walkers at the record level with local
time one there and zero above.  This is the state at which the array's word mass is evaluated. -/
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

/-! ### The actual jump box of a finite word -/

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

theorem extendPath_apply {r : ℕ} (q : Fin r → JumpVec N) {n : ℕ} (hn : n < r) :
    Record.extendPath q n = q ⟨n, hn⟩ := dif_pos hn

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
theorem trajectory_eq_runJ_extendPath (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (ω : Array N) (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) :
    trajectory p m ω n = runJ m (Record.extendPath q) n := by
  refine trajectory_eq_runJ_of_prefix p m ω (fun t ht i => ?_)
  rw [extendPath_apply q (lt_of_lt_of_le ht hn)]
  exact hbox ⟨t, lt_of_lt_of_le ht hn⟩ i

theorem departureCoord_eq_jcoord (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (ω : Array N) (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) (i : Fin N) :
    departureCoord p m ω n i = jcoord p m (Record.extendPath q) n i := by
  unfold departureCoord jcoord
  rw [trajectory_eq_runJ_extendPath p m r q ω hbox hn]

theorem currentAlpha_eq_jalpha (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    (ω : Array N) (hbox : ω ∈ jbox p m r q) {n : ℕ} (hn : n ≤ r) (i : Fin N) :
    currentAlpha p m ω n i = jalpha p m (Record.extendPath q) n i := by
  unfold currentAlpha jalpha
  rw [trajectory_eq_runJ_extendPath p m r q ω hbox hn]

/-- **The jump box is the cylinder over the word's read coordinates.** -/
theorem jbox_eq_cyl (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    jbox p m r q = ⋂ (n : Fin r) (i : Fin N),
      (fun ω : Array N => ω (jcoord p m (Record.extendPath q) (n : ℕ) i)) ⁻¹'
        jumpSet (q n i) (jalpha p m (Record.extendPath q) (n : ℕ) i) := by
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
        ω (jcoord p m (Record.extendPath q) k i) ∈
          jumpSet (q ⟨k, hk⟩ i) (jalpha p m (Record.extendPath q) k i) :=
      fun k hk i => Set.mem_iInter.mp (Set.mem_iInter.mp hcyl ⟨k, hk⟩) i
    have key : ∀ k : ℕ, ∀ hk : k < r, ∀ i : Fin N,
        nextJumpVec p m ω k i = q ⟨k, hk⟩ i := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk i
        have hpre : ∀ t : ℕ, t < k → ∀ j : Fin N,
            nextJumpVec p m ω t j = Record.extendPath q t j := by
          intro t ht j
          rw [extendPath_apply q (lt_trans ht hk)]
          exact ih t ht (lt_trans ht hk) j
        have htr : trajectory p m ω k = runJ m (Record.extendPath q) k :=
          trajectory_eq_runJ_of_prefix p m ω hpre
        have hcoord : departureCoord p m ω k i = jcoord p m (Record.extendPath q) k i := by
          unfold departureCoord jcoord
          rw [htr]
        have halpha : currentAlpha p m ω k i = jalpha p m (Record.extendPath q) k i := by
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
theorem measure_cyl_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Fin N × ℤ × ℕ)
    (hc : Function.Injective c) (I : ι → Set ℝ) (hI : ∀ q, MeasurableSet (I q)) :
    arrayMeasure N (⋂ q, (fun ω : Array N => ω (c q)) ⁻¹' I q) = ∏ q, uniform01 (I q) := by
  have h := SwarmIID.indep_iInter_comp (μ := arrayMeasure N) (array_independent N) hc I hI
  rw [h]
  exact Finset.prod_congr rfl fun q _ => arrayMeasure_preimage_set N (c q) (I q) (hI q)

/-- The jump box as a cylinder over the finite index type `Fin r × Fin N`. -/
theorem jbox_eq_cyl_prod (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N) :
    jbox p m r q = ⋂ ni : Fin r × Fin N,
      (fun ω : Array N => ω (jcoord p m (Record.extendPath q) (ni.1 : ℕ) ni.2)) ⁻¹'
        jumpSet (q ni.1 ni.2) (jalpha p m (Record.extendPath q) (ni.1 : ℕ) ni.2) := by
  rw [jbox_eq_cyl]
  ext ω
  simp only [Set.mem_iInter, Set.mem_preimage, Prod.forall]

/-- **The exact mass of a finite jump box**: the product of the actual one-walker thresholds. -/
theorem mass_jbox {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (r : ℕ)
    (q : Fin r → JumpVec N) :
    arrayMeasure N (jbox p m r q) =
      ENNReal.ofReal (∏ ni : Fin r × Fin N,
        jumpWeight (q ni.1 ni.2) (jalpha p m (Record.extendPath q) (ni.1 : ℕ) ni.2)) := by
  rw [jbox_eq_cyl_prod,
    measure_cyl_prod (fun ni : Fin r × Fin N => jcoord p m (Record.extendPath q) (ni.1 : ℕ) ni.2)
      (jcoord_injective p m (Record.extendPath q) r) _
      (fun ni => measurableSet_jumpSet _ _)]
  rw [show (∏ ni : Fin r × Fin N,
        uniform01 (jumpSet (q ni.1 ni.2) (jalpha p m (Record.extendPath q) (ni.1 : ℕ) ni.2)))
      = ∏ ni : Fin r × Fin N,
        ENNReal.ofReal (jumpWeight (q ni.1 ni.2)
          (jalpha p m (Record.extendPath q) (ni.1 : ℕ) ni.2)) from
    Finset.prod_congr rfl fun ni _ =>
      uniform01_jumpSet (jalpha_pos hp0 m (Record.extendPath q) _ _)
        (jalpha_lt_one hp1 m (Record.extendPath q) _ _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (fun ni _ =>
    jumpWeight_nonneg (jalpha_pos hp0 m (Record.extendPath q) _ _)
      (jalpha_lt_one hp1 m (Record.extendPath q) _ _) (b := q ni.1 ni.2))]

/-! ### Comparison with the chain algebra's path weight -/

/-- The chain algebra's path weight is the product of its one-step weights. -/
theorem pathWFun_eq_prod_fin (p : ℝ) (m : ℕ) (u : ℕ → JumpVec N) :
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
      = SimJump.pathWFun p (Record.extendPath q) r (startState (N := N) m) := by
  rw [← SimJump.pathW_eq_pathWFun p (Record.extendPath q) r (startState (N := N) m)]
  congr 2
  funext i
  exact (extendPath_apply q i.2).symm

theorem stepW_evolveFun_startState (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → JumpVec N)
    {n : ℕ} (hn : n < r) :
    SimJump.stepW p m (SimJump.evolveFun (Record.extendPath q) n (startState (N := N) m))
        (Record.extendPath q n)
      = ∏ i : Fin N, jumpWeight (q ⟨n, hn⟩ i) (jalpha p m (Record.extendPath q) n i) := by
  have hev : SimJump.evolveFun (Record.extendPath q) n (startState (N := N) m)
      = capState m (runJ m (Record.extendPath q) n) := by
    rw [startState, evolveFun_capState]
  rw [hev, stepW_capState]
  exact Finset.prod_congr rfl fun i _ => by
    simp only [jalpha, extendPath_apply q hn]

/-- **The exact mass of a finite jump box, in the frozen-record notation of `hitW`.**
Identical statement to `M5FirstBlock.mass_jbox_pathW` of `Swarm/ActualJumpBox.lean`, proved
here from the light model modules so that it can be combined with `FreshCyl`. -/
theorem mass_jbox_pathW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (r : ℕ)
    (q : Fin r → JumpVec N) :
    arrayMeasure N (jbox p m r q)
      = ENNReal.ofReal (pathW p r q (startState (N := N) m)) := by
  rw [mass_jbox hp0 hp1 m r q, pathW_eq_pathWFun_ext p m r q, pathWFun_eq_prod_fin]
  congr 1
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun n _ => ?_
  exact (stepW_evolveFun_startState p m r q n.2).symm

/-! ## 4. The canonical start state is a fresh start; the mass at `srSet` -/

/-- The array recursion's start state is the paper's fresh start: all walkers at the record
level, local time one there, and zero strictly above. -/
theorem freshStart_startState (m : ℕ) (hm : 1 ≤ m) :
    SwarmFreshPos.FreshStart (startState (N := N) m) := by
  refine ⟨fun i => startState_pos m i, fun i x hx => ?_, fun i => ?_⟩
  · rw [startState_eta m hm i x, if_neg (ne_of_gt hx)]
  · rw [startState_eta m hm i 0, if_pos rfl]

/-- **The array start state carries the same word mass as every simultaneous-record state.**
For `y ∈ srSet` the two `pathW` values are the two fresh starts of `SwarmFreshPos.pathW_eq_fresh`
(the array's canonical one and `ofRecState y`). -/
theorem pathW_startState_eq {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {y : RecState N m}
    (hy : y ∈ srSet N m) {k : ℕ} (q : Fin k → JumpVec N)
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    pathW p k q (startState (N := N) m) = pathW p k q (Record.ofRecState y) :=
  SwarmFreshCyl.pathW_eq_fresh p (freshStart_startState m hm)
    (SwarmFreshPos.freshStart_ofRecState hy hm) q hq

/-- The array mass of a jump box, read at any simultaneous-record state `y ∈ srSet`. -/
theorem mass_jbox_pathW_srSet {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m) {k : ℕ} (q : Fin k → JumpVec N)
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    arrayMeasure N (jbox p m k q)
      = ENNReal.ofReal (pathW p k q (Record.ofRecState y)) := by
  rw [mass_jbox_pathW hp0 hp1 m k q, pathW_startState_eq hm hy q hq]

/-! ## 5. The bridge: fresh-segment cylinder mass = actual-array box mass -/

/-- **The finite fresh-segment measure on the actual array's path interface.**

For every `1/2 < p < 1`, `m ≥ 1`, every simultaneous-record start state `y ∈ srSet`, every
`k ≥ 1` and every first-record word `q` that keeps every walker strictly above the record level,
the strict-positivity part of the enriched first-segment law on the segment cylinder `wordCyl q`
is *exactly* the actual array's probability of following the jump word `q` for its first `k`
steps:

  `arrayMeasure N (jbox p m k q) = segKpos p hm y (wordCyl q)`.

Both sides are the same `pathW p k q` at a fresh start (`startState` on the array side,
`ofRecState y` on the chain side), which is `hitW p q y` because `q` is a first-record word. -/
theorem array_jbox_mass_eq_segKpos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m) {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    arrayMeasure N (jbox p m k q)
      = SwarmFreshCyl.segKpos p hm y (SwarmFreshCyl.wordCyl q) := by
  rw [mass_jbox_pathW_srSet (k := k) (q := q) hp0 hp1 hm hy hq,
    SwarmFreshCyl.segKpos_wordCyl p hm hy hk q hfr hq,
    RecKernel.hitW_of_firstRecord p q y hfr]

/-! ### Exact boundary points: the array's position path is the segment's `p` -/

/-- On the jump box, the actual array's position path is the segment's `p` component: the
`wordCyl` cylinder is defined by `SwarmFreshPos.posAt (extendPath q)`, and that is exactly the
array trajectory's position path. -/
theorem array_trajectory_pos_eq_wordCyl (p : ℝ) (m : ℕ) {k : ℕ} (q : Fin k → JumpVec N)
    {ω : Array N} (hbox : ω ∈ jbox p m k q) {n : ℕ} (hn : n ≤ k) (i : Fin N) :
    (trajectory p m ω n).pos i = SwarmFreshPos.posAt (Record.extendPath q) n i := by
  rw [trajectory_eq_runJ_extendPath p m k q ω hbox hn, runJ_pos]

/-- **Exact boundary correspondence of the two cylinders.**  Every segment in `wordCyl q` has,
at every time `n ≤ k`, its relative position path `p` equal to the actual array's position path
on the box.  This is the *same* boundary point on both sides, not merely the same mass. -/
theorem wordCyl_boundary_eq_array (p : ℝ) (m : ℕ) {k : ℕ} (q : Fin k → JumpVec N)
    {ω : Array N} (hbox : ω ∈ jbox p m k q) {s : SwarmConcat.Seg N}
    (hs : s ∈ SwarmFreshCyl.wordCyl q) {n : ℕ} (hn : n ≤ k) (i : Fin N) :
    s.p n i = (trajectory p m ω n).pos i := by
  obtain ⟨-, hp⟩ := hs
  rw [hp, array_trajectory_pos_eq_wordCyl p m q hbox hn i]

/-- The segment of a first-record word has the first-record boundary at time `k`: one walker
at the record level one and nobody above it before. -/
theorem wordCyl_firstRecord_boundary {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    {s : SwarmConcat.Seg N} (hs : s ∈ SwarmFreshCyl.wordCyl q) :
    (∃ i : Fin N, s.p k i = 1) ∧ ∀ t < k, ∀ i : Fin N, s.p t i ≤ 0 := by
  obtain ⟨hex, hle⟩ := (SwarmFreshCyl.firstRecord_iff_posAt hy (Record.extendPath q) k).mp hfr
  obtain ⟨-, hp⟩ := hs
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [hp]; exact hi⟩
  · intro t ht i
    rw [hp]
    exact hle t ht i

/-- **The array boundary point of the first record.**  On the jump box of a first-record word,
the actual array has a walker at level `1` at time `k` and no walker above the level before
`k` — the array-side image of `FirstRecord`, matched to `wordCyl`'s boundary by
`array_trajectory_pos_eq_wordCyl`. -/
theorem array_firstRecord_boundary {p : ℝ} {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    {ω : Array N} (hbox : ω ∈ jbox p m k q) :
    (∃ i : Fin N, (trajectory p m ω k).pos i = 1) ∧
      ∀ t < k, ∀ i : Fin N, (trajectory p m ω t).pos i ≤ 0 := by
  obtain ⟨hex, hle⟩ := (SwarmFreshCyl.firstRecord_iff_posAt hy (Record.extendPath q) k).mp hfr
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, by rw [array_trajectory_pos_eq_wordCyl p m q hbox le_rfl i, hi]⟩
  · intro t ht i
    rw [array_trajectory_pos_eq_wordCyl p m q hbox (le_of_lt ht) i]
    exact hle t ht i

/-- The array mass of a jump box equals the stopped record atom weight `hitW` at any
simultaneous-record state, for a first-record word. -/
theorem array_jbox_mass_eq_hitW {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m) {k : ℕ}
    (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    arrayMeasure N (jbox p m k q) = ENNReal.ofReal (RecKernel.hitW p q y) := by
  rw [mass_jbox_pathW_srSet (k := k) (q := q) hp0 hp1 hm hy hq,
    RecKernel.hitW_of_firstRecord p q y hfr]

/-- The *array first-record cylinder*: the jump box of `q` cut down to the actual array event
"someone is at level `1` at time `k` and nobody is above the level before `k`".  This is the
array-side image of the word condition `FirstRecord (extendPath q) k (ofRecState y)`. -/
noncomputable def arrayFirstRecordCyl (p : ℝ) (m : ℕ) (k : ℕ) : Set (Array N) :=
  {ω | (∃ i : Fin N, (trajectory p m ω k).pos i = 1) ∧
    ∀ t < k, ∀ i : Fin N, (trajectory p m ω t).pos i ≤ 0}

/-- **The fresh-segment mass of the actual array's first-record cylinder.**

Under the same hypotheses as the bridge, the box of `q` is *contained* in the actual array's
first-record event (that is the content of `array_firstRecord_boundary`), so cutting the box
down to that event does not change its mass:

  `arrayMeasure N (jbox p m k q ∩ arrayFirstRecordCyl p m k) = segKpos p hm y (wordCyl q)`.

This is the version in which the word-level `hfr` has become a literal array event: the cylinder
on the right is a finite-`q`, finite-`k` first-record cylinder of the fresh array model, and on
it the array's position path equals the segment's `p` (`wordCyl_boundary_eq_array`). -/
theorem arrayFirstRecordCyl_mass_eq_segKpos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 1 ≤ m) {y : RecState N m} (hy : y ∈ srSet N m) {k : ℕ} (hk : 0 < k)
    (q : Fin k → JumpVec N)
    (hfr : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y))
    (hq : SwarmFreshPos.PosSeqFin (N := N) q) :
    arrayMeasure N (jbox p m k q ∩ arrayFirstRecordCyl p m k)
      = SwarmFreshCyl.segKpos p hm y (SwarmFreshCyl.wordCyl q) := by
  have hsubset : jbox p m k q ⊆ arrayFirstRecordCyl p m k :=
    fun ω hbox => array_firstRecord_boundary (p := p) (k := k) (q := q) hy hfr hbox
  rw [Set.inter_eq_left.mpr hsubset]
  exact array_jbox_mass_eq_segKpos hp0 hp1 hm hy hk q hfr hq

/-- **Set-level correspondence on the box.**  Restricted to the jump box of `q`, the actual
array's first-record event is *exactly* the word condition
`FirstRecord (extendPath q) k (ofRecState y)`: the two cylinders are the same set on the box. -/
theorem jbox_firstRecord_iff (p : ℝ) {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    {k : ℕ} (q : Fin k → JumpVec N) {ω : Array N} (hbox : ω ∈ jbox p m k q) :
    ω ∈ arrayFirstRecordCyl p m k ↔
      Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y) := by
  constructor
  · rintro ⟨hex, hle⟩
    rw [SwarmFreshCyl.firstRecord_iff_posAt hy (Record.extendPath q) k]
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, by
        rw [← array_trajectory_pos_eq_wordCyl p m q hbox le_rfl i]
        exact hi⟩
    · intro t ht i
      rw [← array_trajectory_pos_eq_wordCyl p m q hbox (le_of_lt ht) i]
      exact hle t ht i
  · intro hfr
    exact array_firstRecord_boundary (p := p) (k := k) (q := q) hy hfr hbox

/-! ## 6. Non-vacuity: the bridge has an instance -/

/-- The all-zero record state: every walker at the record level, local time one there and zero
elsewhere.  Built directly from `recSet`, with no invariant law and no start law imported. -/
noncomputable def zeroRecState (N m : ℕ) (hm : 1 ≤ m) (i₀ : Fin N) : RecState N m :=
  ⟨(fun _ => 0, fun _ x => if x = 0 then ⟨1, Nat.lt_succ_of_le hm⟩ else 0), by
    have hone : (⟨1, Nat.lt_succ_of_le hm⟩ : Fin (m + 1)) = 1 := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : 1 < m + 1)]
    refine ⟨⟨i₀, rfl⟩, ?_, ?_, ?_⟩
    · intro i x hx
      simp [ne_of_gt hx]
    · intro i
      simp [hone]
    · intro i
      simp [hone]⟩

theorem zeroRecState_mem_srSet (N m : ℕ) (hm : 1 ≤ m) (i₀ : Fin N) :
    zeroRecState N m hm i₀ ∈ srSet N m := by
  intro i
  show dist2 (zeroRecState N m hm i₀) i ≤ 0
  rfl

/-- The all-right word of length one is a strict-positivity word. -/
theorem posSeqFin_one_allRight :
    SwarmFreshPos.PosSeqFin (N := N) (fun _ : Fin 1 => (fun _ => true : JumpVec N)) := by
  intro n hn i
  have hn1 : (n : ℕ) = 1 := by have := n.2; omega
  rw [SwarmFreshPos.posAt]
  simp [SwarmFreshPos.seqOf, hn1]

/-- From any `y ∈ srSet`, the all-right word of length one is a first-record word. -/
theorem firstRecord_one_allRight {m : ℕ} {y : RecState N m} (hy : y ∈ srSet N m)
    (i₀ : Fin N) :
    Record.FirstRecord (Record.extendPath (fun _ : Fin 1 => (fun _ => true : JumpVec N))) 1
      (Record.ofRecState y) := by
  rw [SwarmFreshCyl.firstRecord_iff_posAt hy]
  refine ⟨⟨i₀, ?_⟩, ?_⟩
  · rw [SwarmFreshPos.posAt]
    simp [Record.extendPath]
  · intro t ht i
    have ht0 : t = 0 := by omega
    subst ht0
    rw [SwarmFreshPos.posAt]
    simp

/-- **Non-vacuity of the bridge.**  For `N ≥ 1`, `m ≥ 1`, `1/2 < p < 1`, the hypothesis package
of `array_jbox_mass_eq_segKpos` is simultaneously satisfiable: `y` is the all-zero record state
(which lies in `srSet`), `k = 1` and `q` is the all-right word.  The bridge identity is therefore
not a vacuous implication. -/
theorem array_jbox_mass_eq_segKpos_nonvacuous (hN : 0 < N) {m : ℕ} (hm : 1 ≤ m) {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) :
    ∃ y : RecState N m, y ∈ srSet N m ∧
      ∃ q : Fin 1 → JumpVec N,
        SwarmFreshPos.PosSeqFin (N := N) q ∧
        Record.FirstRecord (Record.extendPath q) 1 (Record.ofRecState y) ∧
        arrayMeasure N (jbox p m 1 q)
          = SwarmFreshCyl.segKpos p hm y (SwarmFreshCyl.wordCyl q) := by
  refine ⟨zeroRecState N m hm ⟨0, hN⟩, zeroRecState_mem_srSet N m hm ⟨0, hN⟩,
    fun _ => (fun _ => true : JumpVec N), posSeqFin_one_allRight, ?_, ?_⟩
  · exact firstRecord_one_allRight (zeroRecState_mem_srSet N m hm ⟨0, hN⟩) ⟨0, hN⟩
  · exact array_jbox_mass_eq_segKpos hp0 hp1 hm
      (zeroRecState_mem_srSet N m hm ⟨0, hN⟩) (by norm_num) _
      (firstRecord_one_allRight (zeroRecState_mem_srSet N m hm ⟨0, hN⟩) ⟨0, hN⟩)
      posSeqFin_one_allRight

end SwarmFreshArray


