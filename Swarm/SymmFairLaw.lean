/-
Auxiliary definitions and the deterministic (previsibility) layer.

The departure coordinate consulted at step `n` depends on the array through the values it
has already consumed, so it is *adapted*.  We condition on the Boolean word of the
*interacting* jumps actually taken (a finite set of alternatives).  `trajectory_eq_wState`
is the precise statement that the state at time `n` is a function of that word alone.
-/
import Swarm.Trajectory
import Swarm.TransitionLaw
import Swarm.FreshIndependence

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.History Swarming.Trajectory
  Swarming.Transition

namespace Swarming.SymmFair

variable {N : ℕ}

/-! ### Boolean signs -/

/-- The set of uniforms producing the Boolean auxiliary sign `b`. -/
noncomputable def symmSet (b : Bool) : Set ℝ := if b = true then Set.Iic (1 / 2) else Set.Ioi (1 / 2)

lemma two_mul_le_one_iff (u : ℝ) : 2 * u ≤ 1 ↔ u ≤ 1 / 2 := by
  constructor <;> intro h <;> linarith

lemma mem_symmSet_iff {u : ℝ} {b : Bool} : u ∈ symmSet b ↔ symmetricStep u = jumpShift b := by
  cases b
  · simp only [symmSet, Bool.false_eq_true, if_false, jumpShift, mem_Ioi]
    constructor
    · intro h
      rw [symmetricStep, if_neg (by linarith : ¬ 2 * u ≤ 1)]
    · intro h
      by_contra hle
      rw [symmetricStep, if_pos (by linarith : 2 * u ≤ 1)] at h
      exact absurd h (by norm_num)
  · simp only [symmSet, if_true, jumpShift, mem_Iic]
    constructor
    · intro h
      rw [symmetricStep, if_pos (by linarith : 2 * u ≤ 1)]
    · intro h
      by_contra hle
      rw [symmetricStep, if_neg (by linarith : ¬ 2 * u ≤ 1)] at h
      exact absurd h (by norm_num)

lemma symmSet_measurable (b : Bool) : MeasurableSet (symmSet b) := by
  cases b <;> simp [symmSet, measurableSet_Iic, measurableSet_Ioi]

/-- The auxiliary sign of walker `i` at step `n`, as a Boolean. -/
noncomputable def symmB (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) : Bool :=
  decide (ω (departureCoord p m ω n i) ≤ 1 / 2)

/-- The joint interacting jump vector of step `n`. -/
noncomputable def driveB (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) : Fin N → Bool :=
  fun i => decide (ω (departureCoord p m ω n i) ≤ currentAlpha p m ω n i)

lemma symmB_iff_mem (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) (b : Bool) :
    symmB p m ω n i = b ↔ ω (departureCoord p m ω n i) ∈ symmSet b := by
  cases b
  · simp only [symmB, symmSet, Bool.false_eq_true, if_false, mem_Ioi, decide_eq_false_iff_not,
      not_le]
  · simp only [symmB, symmSet, if_true, mem_Iic, decide_eq_true_eq]

lemma driveB_iff_mem (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) (b : Bool) :
    driveB p m ω n i = b ↔ ω (departureCoord p m ω n i) ∈ jumpSet b (currentAlpha p m ω n i) := by
  cases b
  · simp only [driveB, jumpSet, Bool.false_eq_true, if_false, mem_Ioi, decide_eq_false_iff_not,
      not_le]
  · simp only [driveB, jumpSet, if_true, mem_Iic, decide_eq_true_eq]

/-- The auxiliary sign really is `symmetricStep` of the consulted uniform. -/
lemma symmetricStep_eq_jumpShift_symmB (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) :
    symmetricStep (ω (departureCoord p m ω n i)) = jumpShift (symmB p m ω n i) := by
  rw [← mem_symmSet_iff]
  exact (symmB_iff_mem p m ω n i _).mp rfl

/-- The auxiliary sign lemma in the shape in which the recursion presents it. -/
lemma symmetricStep_eq_jumpShift_symmB' (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) :
    symmetricStep (ω (i, (trajectory p m ω n).pos i,
        (trajectory p m ω n).ell i ((trajectory p m ω n).pos i))) =
      jumpShift (symmB p m ω n i) :=
  symmetricStep_eq_jumpShift_symmB p m ω n i

/-- The walk of `Trajectory.symmetricWalk` as the partial sums of its Boolean signs. -/
theorem symmetricWalk_eq_sum (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) :
    ∀ n : ℕ, symmetricWalk p m ω i n =
      ∑ k ∈ Finset.range n, jumpShift (symmB p m ω k i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [symmetricWalk, ih, Finset.sum_range_succ, symmetricStep_eq_jumpShift_symmB']

/-! ### The state is a function of the jump word -/

lemma WalkState.ext' {a b : WalkState N} (hp : a.pos = b.pos) (he : a.ell = b.ell) : a = b := by
  cases a
  cases b
  simp_all

/-- The position update, with the consulted uniform written out. -/
lemma nextPos_eq_state (p : ℝ) (m : ℕ) (ω : Array N) (s : WalkState N) (i : Fin N) :
    nextPos p m ω s i = s.pos i + jumpShift
      (decide (ω (i, s.pos i, s.ell i (s.pos i)) ≤ rightProbability p m s.ell i (s.pos i))) := by
  unfold nextPos drivenStep jumpShift
  by_cases h : ω (i, s.pos i, s.ell i (s.pos i)) ≤ rightProbability p m s.ell i (s.pos i)
  · simp [h]
  · simp [h]

/-- The jump of step `n`, written with the state at time `n`. -/
lemma driveB_eq_state (p : ℝ) (m : ℕ) (ω : Array N) {k : ℕ} {s : WalkState N}
    (hs : trajectory p m ω k = s) (i : Fin N) :
    driveB p m ω k i = decide (ω (i, s.pos i, s.ell i (s.pos i)) ≤
      rightProbability p m s.ell i (s.pos i)) := by
  unfold driveB currentAlpha departureCoord
  rw [hs]

lemma nextWalkState_eq_of_traj_eq (p : ℝ) (m : ℕ) {ω ω' : Array N} {k : ℕ}
    (hstate : trajectory p m ω k = trajectory p m ω' k) (hb : driveB p m ω k = driveB p m ω' k) :
    trajectory p m ω (k + 1) = trajectory p m ω' (k + 1) := by
  rw [trajectory_succ, trajectory_succ, ← hstate]
  set s := trajectory p m ω k
  have h1 : trajectory p m ω k = s := rfl
  have h2 : trajectory p m ω' k = s := hstate.symm
  have hpos : nextPos p m ω s = nextPos p m ω' s := by
    funext i
    rw [nextPos_eq_state, nextPos_eq_state, (driveB_eq_state p m ω h1 i).symm,
      (driveB_eq_state p m ω' h2 i).symm, congrFun hb i]
  apply WalkState.ext'
  · exact hpos
  · funext i x
    rw [nextWalkState_ell, nextWalkState_ell, congrFun hpos i]

/-- **Previsibility.** The whole trajectory at time `k` is a function of the word of
interacting jumps taken before `k`. -/
theorem trajectory_eq_of_driveB_eq (p : ℝ) (m : ℕ) :
    ∀ (k : ℕ) (ω ω' : Array N), (∀ t < k, driveB p m ω t = driveB p m ω' t) →
      trajectory p m ω k = trajectory p m ω' k := by
  intro k
  induction k with
  | zero => intro ω ω' _; rw [trajectory_zero, trajectory_zero]
  | succ k ih =>
      intro ω ω' h
      exact nextWalkState_eq_of_traj_eq p m
        (ih ω ω' fun t ht => h t (Nat.lt_succ_of_lt ht)) (h k (Nat.lt_succ_self k))

/-- The departure coordinate read at step `k` is a function of the earlier word. -/
theorem departureCoord_eq_of_driveB_eq (p : ℝ) (m : ℕ) (i : Fin N) {k : ℕ} {ω ω' : Array N}
    (h : ∀ t < k, driveB p m ω t = driveB p m ω' t) :
    departureCoord p m ω k i = departureCoord p m ω' k i := by
  unfold departureCoord
  rw [trajectory_eq_of_driveB_eq p m k ω ω' h]

/-- The current right probability at step `k` is a function of the earlier word. -/
theorem currentAlpha_eq_of_driveB_eq (p : ℝ) (m : ℕ) (i : Fin N) {k : ℕ} {ω ω' : Array N}
    (h : ∀ t < k, driveB p m ω t = driveB p m ω' t) :
    currentAlpha p m ω k i = currentAlpha p m ω' k i := by
  unfold currentAlpha
  rw [trajectory_eq_of_driveB_eq p m k ω ω' h]

/-! ### Canonical data attached to a word -/

/-- The state after the prescribed jump word `u`, taken from an array realising it
(the initial state when no array realises it). -/
noncomputable def wState (p : ℝ) (m : ℕ) (r : ℕ) (u : Fin r → Fin N → Bool) : WalkState N := by
  classical
  exact if h : ∃ ω : Array N, ∀ t : Fin r, driveB p m ω t = u t then
    trajectory p m (Classical.choose h) r else initialWalkState

/-- An array whose jump word is `u` drives the trajectory to the state `wState u` at time `r`. -/
theorem trajectory_eq_wState (p : ℝ) (m : ℕ) {r : ℕ} {u : Fin r → Fin N → Bool} {ω : Array N}
    (h : ∀ t : Fin r, driveB p m ω t = u t) :
    trajectory p m ω r = wState p m r u := by
  classical
  have hex : ∃ ω' : Array N, ∀ t : Fin r, driveB p m ω' t = u t := ⟨ω, h⟩
  simp only [wState, dif_pos hex]
  exact trajectory_eq_of_driveB_eq p m r ω (Classical.choose hex)
    (fun t ht => by rw [h ⟨t, ht⟩, Classical.choose_spec hex ⟨t, ht⟩])

/-- The first `k` entries of a word. -/
noncomputable def wPre {r : ℕ} (w : Fin r → Fin N → Bool) (k : ℕ) (hk : k ≤ r) :
    Fin k → Fin N → Bool :=
  fun t => w (Fin.castLE hk t)

/-- The state at step `k` prescribed by the first `k` entries of the word `w`. -/
noncomputable def wStateAt (p : ℝ) (m : ℕ) {r : ℕ} (w : Fin r → Fin N → Bool) (k : Fin r) :
    WalkState N :=
  wState p m k (wPre w k (le_of_lt k.2))

/-- The coordinate consulted at step `k` along the word `w`. -/
noncomputable def wCoordAt (p : ℝ) (m : ℕ) {r : ℕ} (w : Fin r → Fin N → Bool) (k : Fin r)
    (i : Fin N) : Fin N × ℤ × ℕ :=
  (i, (wStateAt p m w k).pos i, (wStateAt p m w k).ell i ((wStateAt p m w k).pos i))

/-- The right probability in force at step `k` along the word `w`. -/
noncomputable def wAlphaAt (p : ℝ) (m : ℕ) {r : ℕ} (w : Fin r → Fin N → Bool) (k : Fin r)
    (i : Fin N) : ℝ :=
  rightProbability p m (wStateAt p m w k).ell i ((wStateAt p m w k).pos i)

lemma trajectory_eq_wStateAt (p : ℝ) (m : ℕ) {r : ℕ} {w : Fin r → Fin N → Bool} {ω : Array N}
    {k : Fin r} (h : ∀ t : Fin k, driveB p m ω t = w (Fin.castLE (le_of_lt k.2) t)) :
    trajectory p m ω k = wStateAt p m w k :=
  trajectory_eq_wState p m h

lemma departureCoord_eq_wCoordAt (p : ℝ) (m : ℕ) {r : ℕ} {w : Fin r → Fin N → Bool}
    {ω : Array N} {k : Fin r} (h : ∀ t : Fin k, driveB p m ω t = w (Fin.castLE (le_of_lt k.2) t))
    (i : Fin N) : departureCoord p m ω k i = wCoordAt p m w k i := by
  unfold departureCoord wCoordAt
  rw [trajectory_eq_wStateAt p m h]

lemma currentAlpha_eq_wAlphaAt (p : ℝ) (m : ℕ) {r : ℕ} {w : Fin r → Fin N → Bool}
    {ω : Array N} {k : Fin r} (h : ∀ t : Fin k, driveB p m ω t = w (Fin.castLE (le_of_lt k.2) t))
    (i : Fin N) : currentAlpha p m ω k i = wAlphaAt p m w k i := by
  unfold currentAlpha wAlphaAt
  rw [trajectory_eq_wStateAt p m h]

/-- The event that walker's interacting jumps follow the word `w`. -/
noncomputable def wordSet (p : ℝ) (m : ℕ) (r : ℕ) (w : Fin r → Fin N → Bool) : Set (Array N) :=
  {ω | ∀ k : Fin r, driveB p m ω k = w k}

/-- The word event is the cylinder over the word's own fresh coordinates. -/
theorem wordSet_eq_cyl (p : ℝ) (m : ℕ) (r : ℕ) (w : Fin r → Fin N → Bool) :
    wordSet p m r w =
      ⋂ (k : Fin r) (i : Fin N),
        (fun ω : Array N => ω (wCoordAt p m w k i)) ⁻¹' jumpSet (w k i) (wAlphaAt p m w k i) := by
  ext ω
  constructor
  · intro hω
    simp only [mem_iInter, mem_preimage]
    intro k i
    have hpre : ∀ t : Fin k, driveB p m ω ↑t = w (Fin.castLE (le_of_lt k.2) t) := by
      intro t
      rw [hω ⟨t.1, lt_of_lt_of_le t.2 (le_of_lt k.2)⟩]
      exact congrArg w (Fin.ext rfl)
    have hc := departureCoord_eq_wCoordAt (p := p) (m := m) (r := r) (w := w) (ω := ω)
      (k := k) hpre i
    have ha := currentAlpha_eq_wAlphaAt (p := p) (m := m) (r := r) (w := w) (ω := ω)
      (k := k) hpre i
    have hmem := (driveB_iff_mem p m ω k i (w k i)).mp (congrFun (hω k) i)
    rwa [hc, ha] at hmem
  · intro hω
    have hcyl : ∀ (k : Fin r) (i : Fin N),
        ω (wCoordAt p m w k i) ∈ jumpSet (w k i) (wAlphaAt p m w k i) := by
      intro k i
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hω k) i
    intro k
    have key : ∀ (n : ℕ) (hn : n < r), driveB p m ω (Fin.mk n hn) = w (Fin.mk n hn) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        funext i
        have hpre : ∀ t : Fin n, driveB p m ω ↑t = w (Fin.castLE (le_of_lt hn) t) := by
          intro t
          have ht : t.1 < r := Nat.lt_trans t.2 hn
          have hcast : (Fin.castLE (le_of_lt hn) t : Fin r) = Fin.mk t.1 ht := Fin.ext rfl
          rw [hcast]
          exact ih t.1 t.2 ht
        have hc := departureCoord_eq_wCoordAt (p := p) (m := m) (r := r) (w := w) (ω := ω)
          (k := Fin.mk n hn) hpre i
        have ha := currentAlpha_eq_wAlphaAt (p := p) (m := m) (r := r) (w := w) (ω := ω)
          (k := Fin.mk n hn) hpre i
        have hmem := hcyl (Fin.mk n hn) i
        rw [← hc, ← ha] at hmem
        exact (driveB_iff_mem p m ω (Fin.mk n hn) i (w (Fin.mk n hn) i)).mpr hmem
    exact key k.1 k.2

/-- A finite cylinder over a family of array coordinates. -/
def cyl {ι : Type*} (c : ι → Fin N × ℤ × ℕ) (I : ι → Set ℝ) : Set (Array N) :=
  ⋂ q, (fun ω : Array N => ω (c q)) ⁻¹' I q

/-- **Finite-cylinder product law** for distinct coordinates of the uniform array. -/
theorem measure_cyl {ι : Type*} [Fintype ι] (c : ι → Fin N × ℤ × ℕ)
    (hc : Function.Injective c) (I : ι → Set ℝ) (hI : ∀ q, MeasurableSet (I q)) :
    arrayMeasure N (cyl c I) = ∏ q, uniform01 (I q) := by
  have h := SwarmIID.indep_iInter_comp (μ := arrayMeasure N) (array_independent N) hc I hI
  rw [cyl, h]
  exact Finset.prod_congr rfl fun q _ => arrayMeasure_preimage_set N (c q) (I q) (hI q)

/-! ### The first increment is exactly fair -/

/-- The coordinate consulted at step `0` is deterministic. -/
lemma departureCoord_zero (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) :
    departureCoord p m ω 0 i = (i, 0, 1) := by
  unfold departureCoord
  rw [trajectory_zero]
  rfl

/-- The auxiliary sign of step `0` is the threshold of a single uniform coordinate. -/
theorem symmB_zero_iff (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) (b : Bool) :
    symmB p m ω 0 i = b ↔ ω (i, 0, 1) ∈ symmSet b := by
  rw [symmB_iff_mem, departureCoord_zero]

/-- `uniform01` gives the exact fair coin mass at the threshold `1/2`. -/
lemma uniform01_symmSet (b : Bool) : uniform01 (symmSet b) = 1 / 2 := by
  cases b
  · show uniform01 (Set.Ioi (1 / 2)) = 1 / 2
    rw [uniform01_Ioi (by norm_num) (by norm_num), show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  · show uniform01 (Set.Iic (1 / 2)) = 1 / 2
    rw [uniform01_Iic (by norm_num) (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num

/-- **The exact fair law of the first auxiliary increment of the actual process.** -/
theorem measure_symmB_zero (p : ℝ) (m : ℕ) (i : Fin N) (b : Bool) :
    arrayMeasure N {ω : Array N | symmB p m ω 0 i = b} = 1 / 2 := by
  have hset : {ω : Array N | symmB p m ω 0 i = b} =
      (fun ω : Array N => ω (i, 0, 1)) ⁻¹' symmSet b := by
    ext ω
    exact symmB_zero_iff p m ω i b
  rw [hset, arrayMeasure_preimage_set N (i, 0, 1) (symmSet b) (symmSet_measurable b),
    uniform01_symmSet]

/-- The same statement for the first increment of `Trajectory.symmetricWalk` itself:
`symmetricStep` of the consulted uniform is a fair `±1` sign. -/
theorem measure_symmetricStep_zero (p : ℝ) (m : ℕ) (i : Fin N) (b : Bool) :
    arrayMeasure N {ω : Array N |
        symmetricStep (ω (departureCoord p m ω 0 i)) = jumpShift b} = 1 / 2 := by
  have hset : {ω : Array N | symmetricStep (ω (departureCoord p m ω 0 i)) = jumpShift b} =
      (fun ω : Array N => ω (i, 0, 1)) ⁻¹' symmSet b := by
    ext ω
    have h1 : symmetricStep (ω (departureCoord p m ω 0 i)) = jumpShift b ↔
        ω (departureCoord p m ω 0 i) ∈ symmSet b := mem_symmSet_iff.symm
    have h2 : ω (departureCoord p m ω 0 i) ∈ symmSet b ↔ ω (i, 0, 1) ∈ symmSet b := by
      rw [departureCoord_zero]
    exact h1.trans h2
  rw [hset, arrayMeasure_preimage_set N (i, 0, 1) (symmSet b) (symmSet_measurable b),
    uniform01_symmSet]


/-- The step-`0` coordinates of the walkers are distinct. -/
lemma zeroCoord_injective (p : ℝ) (m : ℕ) :
    Function.Injective (fun i : Fin N => departureCoord p m (fun _ => 0) 0 i) := by
  intro i j h
  have h' : (i, (0 : ℤ), (1 : ℕ)) = (j, (0 : ℤ), (1 : ℕ)) := by
    rw [← departureCoord_zero p m (fun _ => (0 : ℝ)) i,
      ← departureCoord_zero p m (fun _ => (0 : ℝ)) j]
    exact h
  exact congrArg Prod.fst h'

/-- **Joint fairness at time `0`**: the auxiliary signs of all walkers at the first step
are `2^{-N}`-uniform, i.e. independent fair coins. -/
theorem measure_symmB_zero_vec (p : ℝ) (m : ℕ) (b : Fin N → Bool) :
    arrayMeasure N {ω : Array N | ∀ i : Fin N, symmB p m ω 0 i = b i} = (1 / 2) ^ N := by
  have hset : {ω : Array N | ∀ i : Fin N, symmB p m ω 0 i = b i} =
      cyl (fun i : Fin N => departureCoord p m (fun _ => 0) 0 i) (fun i => symmSet (b i)) := by
    ext ω
    simp only [cyl, mem_iInter, mem_preimage, mem_setOf_eq]
    constructor
    · intro h i
      rw [departureCoord_zero, ← symmB_zero_iff]
      exact h i
    · intro h i
      rw [symmB_zero_iff]
      have := h i
      rwa [departureCoord_zero] at this
  rw [hset, measure_cyl _ (zeroCoord_injective p m) _ (fun i => symmSet_measurable (b i))]
  simp [uniform01_symmSet]

end Swarming.SymmFair


