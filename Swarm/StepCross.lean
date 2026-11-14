/-
  **Exact one-step laws of the actual interacting walker in its actual random environment.**

  Paper reference: `main_1d_revised.tex`, proof of Lemma `transience`, the chain

      (reveal)   {M_n^j >= x+1, B_j(x) = 1} ⊆ {L_n^j(x) >= m}
      (dominate) alpha_n^i >= omega_j(X_n^i)   on {0 <= X_n^i < M_n^j}
      (cross)    P(T_{b0} < T_{b1+1} | F_s) <= prod_{x=b0+1}^{b1} r(x)

  This file proves the *one-step* content of (dominate)/(cross) at the level of the
  actual probability space `Swarming.Uniform.Array N` with the paper's uniform-array
  measure, i.e. without a nested filtration:

  * `measure_history_inter_stepUp` / `..._stepDown`: **the exact one-step law of walker `i`
    given the complete actual history**.  Conditionally on the used-coordinate history
    `actualHistory p m U n`, the next step of `i` is right with mass exactly
    `currentAlpha p m U n i` and left with mass exactly `1 - currentAlpha p m U n i`.
    This is the marginal of `Swarming.Transition.conditional_jumpLaw` restricted to one
    walker; it is *not* a `condExp` statement about a nested filtration.
  * `measure_crossAt`: the **exact one-step crossing probability** at the paper's top
    site: from `X_n^i = b1` the walker is at `b1 + 1` at time `n+1` with mass exactly
    `alpha_n^i` times the mass of the history-and-state event.
  * `cross_from_below_eq_empty`: from any site `x` with `x + 1 <= b1` the walker cannot be
    at `b1 + 1` at time `n + 1`.  Hence the one-step crossing probability, as a function
    of the current site `x`, is `alpha * 1{x = b1}` — the "exact closed form".
  * `stepUp_measure_ge_omegaAt`: the paper's interior StepHyp / (dominate) as an
    inequality between *actual* transition masses:
    `omega_j(X_n^i) * P(history) <= P(history AND i steps right)` on
    `{0 <= X_n^i < M_n^j}`.  Only (reveal)/(dominate) plus the exact one-step law.
  * `cross_measure_ge_omegaAt`: the same at the crossing site `b1`, i.e. on the paper's
    event `{X_n^i = b1, M_n^j >= b1 + 1}` the one-step crossing probability dominates
    `omega_j(b1)`.

  Boundary honesty.  The paper's (dominate) is stated on `{0 <= X_n^i < M_n^j}` only.
  `boundary_drift_negative` below exhibits an explicit array of the actual model on which
  the interior hypothesis fails (`X_n^i > M_n^j`) and the one-step scale-function drift of
  the crossing argument is **strictly negative**: the restriction to the interior is
  necessary, not cosmetic.  This is a concrete witness at the model, complementing the
  measure-theoretic statement `SwarmSpeed.measure_eq_zero_of_unconditional_hdom`.

  Reading of the drift statements.  `oneStep_drift`, `oneStep_drift_nonneg` and
  `oneStep_drift_usedSigma` are weighted-mass identities for the site `x`; they are the
  drift of `f (X_n^i)` only together with the site identification
  `hpos : X_n^i = x`, which they therefore carry as an explicit hypothesis (and which the
  algebra itself does not consume).  The site-conditioned versions `oneStep_drift_at`,
  `oneStep_drift_usedSigma_at`, `interior_drift_at` need no `hpos`: the site condition is
  part of the event `histAt p m U n i x`.

  What is deliberately NOT claimed here: no nested filtration, no `condExp`, no
  optional stopping, no multi-step / geometric tail bound, no `P(T_{b0} < T_{b1+1} | F_s)`
  bound.  Those need the filtration of `areas/filtration` and the conditional law of the
  next jump in *that* filtration, which `areas/transience/GAP.md` lists as open.
-/
import Swarm.Imports
import Swarm.TransitionLaw
import Swarm.Reveal
import Swarm.MeasurableInc
import Swarm.Transience.Scale
import Swarm.IncrementExpectation

namespace Swarming.StepCross

open MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.History
open Swarming.HistoryDeterminism Swarming.Transition Swarming.Increment
open scoped ENNReal BigOperators

variable {N : ℕ}

/-! ### The two one-step events of walker `i` -/

/-- Walker `i` steps one unit to the right at time `n`. -/
noncomputable def stepUp (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : Set (Array N) :=
  {ω | (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i + 1}

/-- Walker `i` steps one unit to the left at time `n`. -/
noncomputable def stepDown (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : Set (Array N) :=
  {ω | (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i - 1}

@[simp] lemma mem_stepUp {p : ℝ} {m n : ℕ} {i : Fin N} {ω : Array N} :
    ω ∈ stepUp (N := N) p m n i ↔
      (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i + 1 := Iff.rfl

@[simp] lemma mem_stepDown {p : ℝ} {m n : ℕ} {i : Fin N} {ω : Array N} :
    ω ∈ stepDown (N := N) p m n i ↔
      (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i - 1 := Iff.rfl

/-- Every step of every walker has length one. -/
lemma pos_succ_eq_or (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + 1 ∨
      (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  unfold drivenStep
  split <;> omega

/-- A step moves the walker at most one unit up (`Reveal.pos_succ_le`, restated here for
convenience of local use) and at most one unit down. -/
lemma pos_succ_ge (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U n).pos i - 1 ≤ (trajectory p m U (n + 1)).pos i := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  unfold drivenStep
  split <;> omega

lemma measurable_stepUp (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : MeasurableSet (stepUp p m n i) := by
  have h1 := (Swarming.Fair.measurable_trajectory (N := N) p m (n + 1)).1 i
  have h0 := (Swarming.Fair.measurable_trajectory (N := N) p m n).1 i
  have : stepUp (N := N) p m n i =
      {ω | (trajectory p m ω (n + 1)).pos i - (trajectory p m ω n).pos i = 1} := by
    ext ω; simp only [mem_stepUp, mem_ofPred_eq]; constructor <;> intro h <;> omega
  rw [this]
  exact measurableSet_eq_fun (h1.sub h0) measurable_const

lemma measurable_stepDown (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) : MeasurableSet (stepDown p m n i) := by
  have h1 := (Swarming.Fair.measurable_trajectory (N := N) p m (n + 1)).1 i
  have h0 := (Swarming.Fair.measurable_trajectory (N := N) p m n).1 i
  have : stepDown (N := N) p m n i =
      {ω | (trajectory p m ω (n + 1)).pos i - (trajectory p m ω n).pos i = -1} := by
    ext ω; simp only [mem_stepDown, mem_ofPred_eq]; constructor <;> intro h <;> omega
  rw [this]
  exact measurableSet_eq_fun (h1.sub h0) measurable_const

/-! ### Reading a step off the freshly used coordinate

On the complete actual history at time `n` the state is frozen
(`HistoryDeterminism.trajectory_eq_of_history`), so the step of walker `i` is decided by the
single fresh coordinate `U (departureCoord p m U n i)` against the frozen threshold
`currentAlpha p m U n i`.  This is the deterministic content behind
`Transition.conditional_jumpLaw`. -/

lemma stepUp_iff_of_history {p : ℝ} {m n : ℕ} {i : Fin N} {U ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) :
    ω ∈ stepUp (N := N) p m n i ↔
      ω (departureCoord p m U n i) ∈ jumpSet true (currentAlpha p m U n i) := by
  have htr := trajectory_eq_of_history p m U n hω
  have hα : currentAlpha p m ω n i = currentAlpha p m U n i := by
    simpa only [currentAlpha] using currentAlpha_eq_of_history p m U n hω i
  have hc : departureCoord p m ω n i = departureCoord p m U n i := by
    simp only [departureCoord, htr]
  have key := nextPos_eq_iff p m ω n (fun _ => true) i
  have hshift : jumpShift (true : Bool) = 1 := rfl
  rw [hshift] at key
  rw [hc, hα] at key
  rw [mem_stepUp]
  rw [show (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i + 1 ↔
      Trajectory.nextPos p m ω (trajectory p m ω n) i =
        (trajectory p m ω n).pos i + 1 from by
    rw [trajectory_succ, nextWalkState_pos]]
  exact key

lemma stepDown_iff_of_history {p : ℝ} {m n : ℕ} {i : Fin N} {U ω : Array N}
    (hω : ω ∈ historyEvent (actualHistory p m U n)) :
    ω ∈ stepDown (N := N) p m n i ↔
      ω (departureCoord p m U n i) ∈ jumpSet false (currentAlpha p m U n i) := by
  have htr := trajectory_eq_of_history p m U n hω
  have hα : currentAlpha p m ω n i = currentAlpha p m U n i := by
    simpa only [currentAlpha] using currentAlpha_eq_of_history p m U n hω i
  have hc : departureCoord p m ω n i = departureCoord p m U n i := by
    simp only [departureCoord, htr]
  have key := nextPos_eq_iff p m ω n (fun _ => false) i
  have hshift : jumpShift (false : Bool) = -1 := rfl
  rw [hshift] at key
  rw [hc, hα] at key
  rw [mem_stepDown]
  rw [show (trajectory p m ω (n + 1)).pos i = (trajectory p m ω n).pos i - 1 ↔
      Trajectory.nextPos p m ω (trajectory p m ω n) i =
        (trajectory p m ω n).pos i + -1 from by
    rw [trajectory_succ, nextWalkState_pos]; constructor <;> intro h <;> omega]
  exact key

/-! ### The exact one-step law given the complete history -/

/-- The product law of `HistoryCylinder` for the family that constrains only walker `i`. -/
theorem measure_history_inter_coord {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (b : Bool) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet b (currentAlpha p m U n i))) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (jumpWeight b (currentAlpha p m U n i)) := by
  classical
  set α := currentAlpha p m U n i with hα
  have hI : ∀ l : Fin N, MeasurableSet (if l = i then jumpSet b α else univ) := by
    intro l
    by_cases hli : l = i
    · simp only [if_pos hli]; exact jumpSet_measurable b α
    · simp only [if_neg hli]; exact MeasurableSet.univ
  have hmain := measure_actualHistory_and_next_sets p m U n
    (fun l : Fin N => if l = i then jumpSet b α else univ) hI
  have hInter : (⋂ l, (fun ω : Array N => ω (departureCoord p m U n l)) ⁻¹'
      (if l = i then jumpSet b α else univ)) =
      ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' jumpSet b α) := by
    ext ω
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro h
      have hh := h i
      simpa using hh
    · intro h l
      by_cases hli : l = i
      · subst hli; simpa using h
      · simp only [if_neg hli, mem_univ]
  rw [hInter] at hmain
  rw [hmain]
  have hterm : ∀ l : Fin N, arrayMeasure N ((fun ω : Array N => ω (departureCoord p m U n l)) ⁻¹'
      (if l = i then jumpSet b α else univ)) =
      if l = i then ENNReal.ofReal (jumpWeight b α) else 1 := by
    intro l
    by_cases hli : l = i
    · rw [if_pos hli, if_pos hli, arrayMeasure_preimage_set N _ _ (jumpSet_measurable b α)]
      exact uniform01_jumpSet (currentAlpha_pos hp0 hp1 m U n i)
        (currentAlpha_lt_one hp0 hp1 m U n i) b
    · rw [if_neg hli, if_neg hli]
      simp only [preimage_univ]
      exact measure_univ
  have hprod : ∏ l : Fin N, (if l = i then ENNReal.ofReal (jumpWeight b α) else 1) =
      ENNReal.ofReal (jumpWeight b α) := by
    rw [Finset.prod_eq_single i (fun l _ hli => by simp only [if_neg hli])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  rw [Finset.prod_congr rfl (fun l _ => hterm l), hprod]

/-- **Exact one-step right-jump law of the actual walker.**  Conditionally on the complete
actual used-coordinate history at time `n`, walker `i` steps right with mass exactly its
actual right probability `currentAlpha p m U n i`. -/
theorem measure_history_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  have hset : historyEvent (actualHistory p m U n) ∩ stepUp (N := N) p m n i =
      historyEvent (actualHistory p m U n) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet true (currentAlpha p m U n i)) := by
    ext ω
    by_cases hω : ω ∈ historyEvent (actualHistory p m U n)
    · simp only [mem_inter_iff, hω, true_and, mem_preimage]
      exact stepUp_iff_of_history hω
    · simp only [mem_inter_iff, hω, false_and]
  rw [hset, measure_history_inter_coord hp0 hp1 m U n i true]
  simp [jumpWeight]

/-- **Exact one-step left-jump law of the actual walker.** -/
theorem measure_history_inter_stepDown {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepDown p m n i) =
      arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (1 - currentAlpha p m U n i) := by
  have hset : historyEvent (actualHistory p m U n) ∩ stepDown (N := N) p m n i =
      historyEvent (actualHistory p m U n) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet false (currentAlpha p m U n i)) := by
    ext ω
    by_cases hω : ω ∈ historyEvent (actualHistory p m U n)
    · simp only [mem_inter_iff, hω, true_and, mem_preimage]
      exact stepDown_iff_of_history hω
    · simp only [mem_inter_iff, hω, false_and]
  rw [hset, measure_history_inter_coord hp0 hp1 m U n i false]
  simp [jumpWeight]

/-- The two one-step events exhaust the history event. -/
theorem history_inter_stepUp_union_stepDown {p : ℝ} (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    historyEvent (actualHistory p m U n) ∩ stepUp p m n i ∪
        historyEvent (actualHistory p m U n) ∩ stepDown p m n i =
      historyEvent (actualHistory p m U n) := by
  ext ω
  simp only [mem_union, mem_inter_iff, mem_stepUp, mem_stepDown]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases pos_succ_eq_or p m ω n i with hs | hs
    · exact Or.inl ⟨h, hs⟩
    · exact Or.inr ⟨h, hs⟩

/-! ### The exact one-step crossing probability at the paper's top site -/

/-- `crossAt b1` : walker `i` sits at `b1` at time `n` and at `b1 + 1` at time `n + 1`. -/
noncomputable def crossAt (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (b1 : ℤ) : Set (Array N) :=
  {ω | (trajectory p m ω n).pos i = b1 ∧ (trajectory p m ω (n + 1)).pos i = b1 + 1}

@[simp] lemma mem_crossAt {p : ℝ} {m n : ℕ} {i : Fin N} {b1 : ℤ} {ω : Array N} :
    ω ∈ crossAt (N := N) p m n i b1 ↔
      (trajectory p m ω n).pos i = b1 ∧ (trajectory p m ω (n + 1)).pos i = b1 + 1 :=
  Iff.rfl

/-- The history event together with a prescribed current site of walker `i`. -/
noncomputable def histAt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    Set (Array N) :=
  historyEvent (actualHistory p m U n) ∩ {ω | (trajectory p m ω n).pos i = x}

lemma histAt_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    histAt p m U n i x =
      if (trajectory p m U n).pos i = x then historyEvent (actualHistory p m U n) else ∅ := by
  by_cases h : (trajectory p m U n).pos i = x
  · rw [if_pos h]
    ext ω
    simp only [histAt, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1
      refine ⟨h1, ?_⟩
      rw [trajectory_eq_of_history p m U n h1]
      exact h
  · rw [if_neg h]
    ext ω
    simp only [histAt, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro h1 h2
    rw [trajectory_eq_of_history p m U n h1] at h2
    exact h h2

lemma measure_histAt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    arrayMeasure N (histAt p m U n i x) =
      if (trajectory p m U n).pos i = x then
        arrayMeasure N (historyEvent (actualHistory p m U n)) else 0 := by
  rw [histAt_eq]
  split <;> simp

/-- **The exact one-step law at a prescribed site.**  Given the actual history and the
actual site `x` of walker `i`, the mass of "and `i` steps right" is the mass of
"history and `i` at `x`" times the actual right probability.  When `x` is not the actual
site both sides vanish. -/
theorem measure_histAt_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    arrayMeasure N (histAt p m U n i x ∩ stepUp p m n i) =
      arrayMeasure N (histAt p m U n i x) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  rw [histAt_eq]
  split
  · rw [measure_history_inter_stepUp hp0 hp1 m U n i]
  · rw [Set.empty_inter, measure_empty, zero_mul]

theorem measure_histAt_inter_stepDown {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    arrayMeasure N (histAt p m U n i x ∩ stepDown p m n i) =
      arrayMeasure N (histAt p m U n i x) *
        ENNReal.ofReal (1 - currentAlpha p m U n i) := by
  rw [histAt_eq]
  split
  · rw [measure_history_inter_stepDown hp0 hp1 m U n i]
  · rw [Set.empty_inter, measure_empty, zero_mul]

/-- **The exact one-step crossing probability.**  From the paper's top site `b1`, walker
`i` is at `b1 + 1` one step later with mass exactly `alpha_n^i` times the mass of the
history-and-state event; for every other site the crossing mass is `0`
(`cross_from_below_eq_empty`). -/
theorem measure_crossAt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (b1 : ℤ) :
    arrayMeasure N (histAt p m U n i b1 ∩ crossAt p m n i b1) =
      arrayMeasure N (histAt p m U n i b1) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  have hset : histAt p m U n i b1 ∩ crossAt (N := N) p m n i b1 =
      histAt p m U n i b1 ∩ stepUp p m n i := by
    ext ω
    simp only [histAt, crossAt, mem_inter_iff, mem_ofPred_eq, mem_stepUp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h4, h3⟩
      exact ⟨⟨h1, h2⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, h2, by omega⟩
  rw [hset, measure_histAt_inter_stepUp hp0 hp1 m U n i b1]

/-- From any site at least two below the top site the walker cannot be at `b1 + 1` one
step later: the crossing mass is exactly zero. -/
theorem cross_from_below_eq_empty (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    (x b1 : ℤ) (hx : x + 1 ≤ b1) :
    histAt p m U n i x ∩ {ω | b1 + 1 ≤ (trajectory p m ω (n + 1)).pos i} = ∅ := by
  ext ω
  constructor
  · intro hω
    simp only [mem_inter_iff, histAt, mem_ofPred_eq] at hω
    obtain ⟨⟨h1, h2⟩, h3⟩ := hω
    have hle := pos_succ_le p m ω n i
    have h2' : (trajectory p m ω n).pos i = (trajectory p m U n).pos i := by
      rw [trajectory_eq_of_history p m U n h1]
    simp only [mem_empty_iff_false]
    omega
  · intro hω
    simp only [mem_empty_iff_false] at hω

/-- At the top site, "at least `b1 + 1`" and "exactly `b1 + 1`" coincide. -/
theorem ge_top_iff {p : ℝ} {m n : ℕ} {i : Fin N} {ω : Array N} {b1 : ℤ}
    (h : (trajectory p m ω n).pos i = b1) :
    b1 + 1 ≤ (trajectory p m ω (n + 1)).pos i ↔
      (trajectory p m ω (n + 1)).pos i = b1 + 1 := by
  have hle := pos_succ_le p m ω n i
  constructor
  · intro hge
    have hb : (trajectory p m ω (n + 1)).pos i ≤ b1 + 1 := by
      calc (trajectory p m ω (n + 1)).pos i ≤ (trajectory p m ω n).pos i + 1 := hle
        _ = b1 + 1 := by rw [h]
    omega
  · intro heq; omega

/-! ### The paper's interior StepHyp / (dominate) as a one-step mass inequality -/

/-- **Interior one-step domination (the paper's (dominate), StepHyp form).**

On the paper's interior event `{0 <= X_n^i < M_n^j}` (with `i != j`) the actual right-step
mass of walker `i` given the complete actual history dominates the revealed weight
`omega_j(X_n^i)`: -/
theorem stepUp_measure_ge_omegaAt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j)
    (h0 : 0 ≤ (trajectory p m U n).pos i)
    (hlt : (trajectory p m U n).pos i < runMax p m U j n) :
    ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) *
        arrayMeasure N (historyEvent (actualHistory p m U n)) ≤
      arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i) := by
  rw [measure_history_inter_stepUp hp0 hp1 m U n i]
  have hdom := dominate (le_of_lt hp0) m U hij n h0 hlt
  have hmono : ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) ≤
      ENNReal.ofReal (currentAlpha p m U n i) :=
    ENNReal.ofReal_le_ofReal (by simpa only [currentAlpha] using hdom)
  calc ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) *
        arrayMeasure N (historyEvent (actualHistory p m U n))
      = arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) := mul_comm _ _
    _ ≤ arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) := mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The one-step crossing estimate on the paper's event `{X_n^i = b1, M_n^j >= b1+1}`.**

This is exactly the event on which the paper's (cross) is applied, at one step: the actual
mass of crossing to `b1 + 1` from `b1` dominates `omega_j(b1)` times the mass of the
history-and-state event.  (The paper then iterates this and applies optional stopping;
neither is claimed here.) -/
theorem cross_measure_ge_omegaAt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) (b1 : ℤ)
    (hstate : (trajectory p m U n).pos i = b1) (h0 : 0 ≤ b1)
    (hlt : b1 < runMax p m U j n) :
    ENNReal.ofReal (omegaAt p m U j b1) * arrayMeasure N (historyEvent (actualHistory p m U n)) ≤
      arrayMeasure N (histAt p m U n i b1 ∩ crossAt p m n i b1) := by
  rw [measure_crossAt hp0 hp1 m U n i b1, measure_histAt, if_pos hstate]
  have hdom := dominate (le_of_lt hp0) m U hij n (by rw [hstate]; exact h0)
    (by rw [hstate]; exact hlt)
  have hmono : ENNReal.ofReal (omegaAt p m U j b1) ≤ ENNReal.ofReal (currentAlpha p m U n i) :=
    ENNReal.ofReal_le_ofReal (by simpa only [currentAlpha, hstate] using hdom)
  calc ENNReal.ofReal (omegaAt p m U j b1) *
        arrayMeasure N (historyEvent (actualHistory p m U n))
      = arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (omegaAt p m U j b1) := mul_comm _ _
    _ ≤ arrayMeasure N (historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) := mul_le_mul_of_nonneg_left hmono (by positivity)


/-! ### The exact one-step drift of the crossing scale function -/

open SwarmSpeed

set_option linter.unusedVariables false in
/-- **The paper's one-step drift identity at the actual model.**

Reading, and where the hypothesis is needed.  The displayed identity is an *algebraic*
statement about the two exact one-step masses of `H_n = historyEvent (actualHistory p m U n)`
weighted by `f(x+1) - f x` and `f(x-1) - f x`.  It is the conditional drift of
`f = sc w b0 b1` **at the site `x`**, i.e. of `f (X_{n+1}^i) - f (X_n^i)` on the event that
the walker currently sits at `x`; that reading needs the identification
`hpos : X_n^i = x` (and then `X_{n+1}^i = x + 1` on `stepUp`, `x - 1` on `stepDown`).  Without
`hpos` the identity remains true but is only the weighted-mass identity, *not* a statement
about `f (X_n^i)`; the site-conditioned formulation is `oneStep_drift_at` below.

The masses are `measure_history_inter_stepUp` / `measure_history_inter_stepDown`; no `condExp`
occurs.  The hypothesis `hpos` is deliberately kept although the displayed algebra does not
consume it: an implication with it is the form that can be read as a statement about
`f (X_n^i)`. -/
theorem oneStep_drift {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {w : ℕ → ℝ}
    (hlo : ∀ y, 1 / 2 ≤ w y) (hhi : ∀ y, w y < 1) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1)
    (hpos : (trajectory p m U n).pos i = (x : ℤ)) :
    ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i)) *
        (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      + ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepDown p m n i)) *
        (sc w b0 b1 (x - 1) - sc w b0 b1 x)
      = ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n))) *
        ((currentAlpha p m U n i - w x) *
          (sc w b0 b1 (x + 1) - sc w b0 b1 (x - 1))) := by
  -- `hpos` plays no role in the displayed algebra; it is the identification of the
  -- parameter `x` with the walker's site which turns this into the drift of `sc (X_n)`.
  have htop : arrayMeasure N (historyEvent (actualHistory p m U n)) ≠ ⊤ := measure_ne_top _ _
  have hα0 := currentAlpha_pos hp0 hp1 m U n i
  have hα1 := currentAlpha_lt_one hp0 hp1 m U n i
  have e1 : ENNReal.toReal
      (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i)) =
      ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n))) *
        currentAlpha p m U n i := by
    rw [measure_history_inter_stepUp hp0 hp1 m U n i, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hα0.le]
  have e2 : ENNReal.toReal
      (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepDown p m n i)) =
      ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n))) *
        (1 - currentAlpha p m U n i) := by
    rw [measure_history_inter_stepDown hp0 hp1 m U n i, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - currentAlpha p m U n i)]
  have hdr := sc_drift (w := w) hlo hhi hb hx0 hx1 (currentAlpha p m U n i)
  rw [e1, e2]
  linear_combination ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n))) * hdr

/-- The drift at the site `x` (see `hpos`) is nonnegative as soon as the ambient weight at
`x` is dominated by the walker's actual right probability — the paper's (dominate) at one
step.  As in `oneStep_drift`, `hpos` is what makes this the drift of `f (X_n^i)` rather than
a weighted-mass inequality. -/
theorem oneStep_drift_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {w : ℕ → ℝ}
    (hlo : ∀ y, 1 / 2 ≤ w y) (hhi : ∀ y, w y < 1) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) (hpos : (trajectory p m U n).pos i = (x : ℤ))
    (hdom : w x ≤ currentAlpha p m U n i) :
    0 ≤ ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i)) *
        (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      + ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepDown p m n i)) *
        (sc w b0 b1 (x - 1) - sc w b0 b1 x) := by
  rw [oneStep_drift hp0 hp1 m U n i hlo hhi hb hx0 hx1 hpos]
  refine mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (by linarith) ?_)
  exact sub_nonneg.mpr (sc_monotone hlo hhi hb (by omega : x - 1 ≤ x + 1))

/-- **Paper-interior one-step drift at the actual model.**  On `{0 <= x < M_n^j}` with
`X_n^i = x`, the actual random environment `y => omegaAt p m U j y` dominates the walker's
right probability, so the one-step drift of the crossing scale function is nonnegative.
This is the exact one-step inequality that the paper's submartingale/optional-stopping
argument starts from; the iteration over time and the stopping argument are *not* claimed.-/
theorem interior_oneStep_drift_nonneg {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1)
    (hpos : (trajectory p m U n).pos i = (x : ℤ))
    (h0 : 0 ≤ (x : ℤ)) (hlt : (x : ℤ) < runMax p m U j n) :
    0 ≤ ENNReal.toReal (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepUp p m n i)) *
        (sc (fun y => omegaAt p m U j (y : ℤ)) b0 b1 (x + 1) -
          sc (fun y => omegaAt p m U j (y : ℤ)) b0 b1 x)
      + ENNReal.toReal
          (arrayMeasure N (historyEvent (actualHistory p m U n) ∩ stepDown p m n i)) *
        (sc (fun y => omegaAt p m U j (y : ℤ)) b0 b1 (x - 1) -
          sc (fun y => omegaAt p m U j (y : ℤ)) b0 b1 x) := by
  have hlo : ∀ y : ℕ, 1 / 2 ≤ omegaAt p m U j (y : ℤ) := by
    intro y; unfold omegaAt; split <;> linarith
  have hhi : ∀ y : ℕ, omegaAt p m U j (y : ℤ) < 1 := by
    intro y; unfold omegaAt; split <;> linarith
  refine oneStep_drift_nonneg hp0 hp1 m U n i hlo hhi hb hx0 hx1 hpos ?_
  have hdom := dominate (le_of_lt hp0) m U hij n (by rw [hpos]; exact h0)
    (by rw [hpos]; exact hlt)
  simpa only [currentAlpha, hpos] using hdom


/-! ### The boundary: the interior hypothesis is not cosmetic

The paper states (dominate) on `{0 <= X_n^i < M_n^j}` only, and `CrossStepInt`/`HdomBoundary`
show that the unrestricted version forces the boundary to be null.  Here is the concrete
witness at the actual model: an explicit array of `Array 2` on which walker `0` runs to
`+n`, walker `1` runs to `-n`, the site `1` is marked for walker `1` (so `omega_1(1) = p`)
while walker `0` is unexcited there (so `alpha_n^0 = 1/2`).  Then
`0 <= X_n^0` but `X_n^0 < M_n^1` fails, domination reverses, and the one-step drift of the
crossing scale function `f = sc w 0 1` at `x = 1` is **strictly negative**. -/

/-- Walker `0` reads `0` (always jumps right), walker `1` reads `(p+1)/2 > p` (always jumps
left). -/
noncomputable def witArray (p : ℝ) : Array 2 := fun c => if c.1 = 0 then 0 else (p + 1) / 2

lemma witArray_zero {p : ℝ} (x : ℤ) (k : ℕ) : witArray p ((0 : Fin 2), x, k) = 0 := by
  simp [witArray]

lemma witArray_one {p : ℝ} (x : ℤ) (k : ℕ) :
    witArray p ((1 : Fin 2), x, k) = (p + 1) / 2 := by
  have h : ¬ ((1 : Fin 2) = 0) := by norm_num
  simp [witArray, h]

lemma wit_pos_zero {p : ℝ} (hp0 : 1 / 2 < p) (m : ℕ) (n : ℕ) :
    (trajectory p m (witArray p) n).pos (0 : Fin 2) = (n : ℤ) := by
  induction n with
  | zero => simp [trajectory_zero, initialWalkState]
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_pos, nextPos, ih]
      have hcoord : ∀ (x : ℤ) (k : ℕ), witArray p ((0 : Fin 2), x, k) = 0 := witArray_zero (p := p)
      rw [hcoord]
      have hα : (0 : ℝ) ≤ rightProbability p m (trajectory p m (witArray p) n).ell (0 : Fin 2) (n : ℤ) := by
        have h := one_half_le_rightProbability (le_of_lt hp0) m
          (trajectory p m (witArray p) n).ell (0 : Fin 2) (n : ℤ)
        linarith
      rw [drivenStep_eq_one_of_le hα]
      push_cast
      ring

lemma wit_pos_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ) :
    (trajectory p m (witArray p) n).pos (1 : Fin 2) = -(n : ℤ) := by
  induction n with
  | zero => simp [trajectory_zero, initialWalkState]
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_pos, nextPos, ih]
      have hcoord : ∀ (x : ℤ) (k : ℕ), witArray p ((1 : Fin 2), x, k) = (p + 1) / 2 :=
        witArray_one (p := p)
      rw [hcoord]
      have hαle : rightProbability p m (trajectory p m (witArray p) n).ell (1 : Fin 2) (-(n : ℤ)) ≤ p :=
        rightProbability_le_p (le_of_lt hp0) m _ (1 : Fin 2) _
      have hnot : ¬ ((p + 1) / 2 ≤
          rightProbability p m (trajectory p m (witArray p) n).ell (1 : Fin 2) (-(n : ℤ))) := by
        linarith
      rw [drivenStep_eq_neg_one_of_not_le hnot]
      push_cast
      ring

lemma wit_ell_one_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ) :
    (trajectory p m (witArray p) n).ell (1 : Fin 2) ((1 : ℕ) : ℤ) = 0 := by
  induction n with
  | zero => simp [trajectory_zero, initialWalkState]
  | succ n ih =>
      rw [trajectory_succ, nextWalkState_ell, ih]
      have hne : ¬ ((1 : ℤ) = nextPos p m (witArray p) (trajectory p m (witArray p) n) (1 : Fin 2)) := by
        intro h
        have h2 : (trajectory p m (witArray p) (n + 1)).pos (1 : Fin 2) = 1 := by
          rw [trajectory_succ, nextWalkState_pos]; exact h.symm
        rw [wit_pos_one hp0 hp1 m (n + 1)] at h2
        omega
      simp [hne]

lemma wit_runMax_one {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (n : ℕ) :
    runMax p m (witArray p) (1 : Fin 2) n = 0 := by
  unfold runMax
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun t ht => ?_)
    rw [wit_pos_one hp0 hp1 m t]
    omega
  · have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos n)
    have h := Finset.le_sup' (f := fun t => (trajectory p m (witArray p) t).pos (1 : Fin 2)) hmem
    rw [wit_pos_one hp0 hp1 m 0] at h
    simpa using h

lemma wit_otherVisits {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) :
    otherVisits (trajectory p m (witArray p) 1).ell (0 : Fin 2) ((1 : ℕ) : ℤ) = 0 := by
  unfold otherVisits
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hj : j = 0
  · rw [if_pos hj]
  · rw [if_neg hj]
    have hj1 : j = 1 := by
      revert hj
      fin_cases j <;> simp
    rw [hj1, wit_ell_one_one hp0 hp1 m 1]

lemma wit_currentAlpha {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (hm : 1 ≤ m) :
    currentAlpha p m (witArray p) 1 (0 : Fin 2) = 1 / 2 := by
  have hov := wit_otherVisits hp0 hp1 m
  have hnex : ¬ Excited m (trajectory p m (witArray p) 1).ell (0 : Fin 2) ((1 : ℕ) : ℤ) := by
    unfold Excited
    rw [hov]
    omega
  unfold currentAlpha rightProbability
  rw [wit_pos_zero hp0 m 1]
  exact if_neg hnex

lemma wit_omegaAt {p : ℝ} (hp1 : p < 1) (m : ℕ) :
    omegaAt p m (witArray p) (1 : Fin 2) ((1 : ℕ) : ℤ) = p := by
  have hmark : SiteMark p m (witArray p) (1 : Fin 2) ((1 : ℕ) : ℤ) := by
    unfold SiteMark
    intro k hk
    rw [witArray_one]
    linarith
  unfold omegaAt
  rw [if_pos hmark]

/-- **The interior hypothesis is necessary.**  An explicit array of the actual model on
which the paper's interior condition `0 <= X_n^i < M_n^j` fails and the domination of the
walker's right probability by the revealed weight **reverses** at the paper's top site. -/
theorem interior_hypothesis_necessary {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ U : Array 2,
      0 ≤ (trajectory p m U 1).pos (0 : Fin 2) ∧
      ¬ ((trajectory p m U 1).pos (0 : Fin 2) < runMax p m U (1 : Fin 2) 1) ∧
      currentAlpha p m U 1 (0 : Fin 2) <
        omegaAt p m U (1 : Fin 2) ((trajectory p m U 1).pos (0 : Fin 2)) := by
  refine ⟨witArray p, ?_, ?_, ?_⟩
  · rw [wit_pos_zero hp0 m 1]; norm_num
  · rw [wit_pos_zero hp0 m 1, wit_runMax_one hp0 hp1 m 1]; norm_num
  · rw [wit_pos_zero hp0 m 1, wit_currentAlpha hp0 hp1 m hm, wit_omegaAt hp1 m]
    linarith

/-- **The drift really changes sign at the boundary.**  With the witness environment
`w y = omega_2(y)` and `b0 = 0`, `b1 = 1`, the paper's one-step drift at the top site `x = 1`
is `(alpha - w 1) (f 2 - f 0) < 0`: the submartingale step of the crossing argument fails
once the walker is no longer strictly below the other walker's running maximum. -/
theorem drift_negative_at_boundary {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    (currentAlpha p 2 (witArray p) 1 (0 : Fin 2) -
        omegaAt p 2 (witArray p) (1 : Fin 2) ((1 : ℕ) : ℤ)) *
      (sc (fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) 0 1 2 -
        sc (fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) 0 1 0) < 0 := by
  have hlo : ∀ y : ℕ, 1 / 2 ≤ omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ) := by
    intro y; unfold omegaAt; split <;> linarith
  have hhi : ∀ y : ℕ, omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ) < 1 := by
    intro y; unfold omegaAt; split <;> linarith
  have htop : sc (fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) 0 1 2 = 1 := by
    have h := sc_top (w := fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) hlo hhi
      (b0 := 0) (b1 := 1) (by norm_num)
    simpa using h
  have hbot : sc (fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) 0 1 0 = 0 :=
    sc_b0 (w := fun y : ℕ => omegaAt p 2 (witArray p) (1 : Fin 2) (y : ℤ)) (b0 := 0) (b1 := 1)
  rw [wit_currentAlpha hp0 hp1 2 (by norm_num), wit_omegaAt hp1 2, htop, hbot]
  linarith


/-! ### StepHyp conditional on the used-coordinate σ-algebra of the actual history

`Swarm/IncrementExpectation.lean` introduces `usedSigma p m U n`, the σ-algebra generated by the
array coordinates that the actual history at time `n` has consumed, and proves the exact
conditional jump law and the vanishing conditional mean of the centred increment on it.
Here we prove the *conditional* form of the paper's interior StepHyp on that σ-algebra: for
every used-coordinate event `G` the right-step mass of walker `i` inside `G AND history`
dominates `omega_j(X_n^i)` times the mass of `G AND history`.

Honest limitations, stated as such: `usedSigma p m U n` is **not** shown to be nested in `n`
(the repo has no `usedSigma p m U n ≤ usedSigma p m U (n+1)`), so this is *not* yet a
filtration and the inequality is not yet an iterable conditional expectation.  That nesting
is the open item `areas/transience/GAP.md` (i) 3; nothing here assumes it. -/

/-- The exact one-step law of walker `i` relative to an arbitrary used-coordinate event. -/
theorem measure_pastProj_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    {A : Set (used (actualHistory p m U n) → ℝ)} (hA : MeasurableSet A) (b : Bool) :
    arrayMeasure N ((pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet b (currentAlpha p m U n i))) =
      arrayMeasure N (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (jumpWeight b (currentAlpha p m U n i)) := by
  classical
  set α := currentAlpha p m U n i with hα
  have hI : ∀ l : Fin N, MeasurableSet (if l = i then jumpSet b α else univ) := by
    intro l
    by_cases hli : l = i
    · simp only [if_pos hli]; exact jumpSet_measurable b α
    · simp only [if_neg hli]; exact MeasurableSet.univ
  have hm := SwarmIID.indep_fresh_finset (array_independent N) (fun c => measurable_pi_apply c)
    (nextCoords_injective p m U n) (fun l => next_not_mem_used_actualHistory p m U n l)
    (A ∩ compatible (actualHistory p m U n)) (hA.inter (compatible_measurable _))
    (fun l : Fin N => if l = i then jumpSet b α else univ) hI
  have hInter : (⋂ l, (fun ω : Array N => ω (departureCoord p m U n l)) ⁻¹'
      (if l = i then jumpSet b α else univ)) =
      ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' jumpSet b α) := by
    ext ω
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro h
      have hh := h i
      simpa using hh
    · intro h l
      by_cases hli : l = i
      · subst hli; simpa using h
      · simp only [if_neg hli, mem_univ]
  rw [hInter] at hm
  have hset : pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) =
      pastProj p m U n ⁻¹' (A ∩ compatible (actualHistory p m U n)) :=
    pastProj_inter_history p m U n A
  have hproj : pastProj p m U n = fun ω (j : used (actualHistory p m U n)) => ω j := rfl
  rw [hset]
  change (arrayMeasure N) ((fun ω (j : used (actualHistory p m U n)) => ω j) ⁻¹'
      (A ∩ compatible (actualHistory p m U n)) ∩
      (fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹' jumpSet b α) =
    (arrayMeasure N) ((fun ω (j : used (actualHistory p m U n)) => ω j) ⁻¹'
      (A ∩ compatible (actualHistory p m U n))) * ENNReal.ofReal (jumpWeight b α)
  rw [hm]
  congr 1
  have hterm : ∀ l : Fin N, arrayMeasure N ((fun ω : Array N => ω (departureCoord p m U n l)) ⁻¹'
      (if l = i then jumpSet b α else univ)) =
      if l = i then ENNReal.ofReal (jumpWeight b α) else 1 := by
    intro l
    by_cases hli : l = i
    · rw [if_pos hli, if_pos hli, arrayMeasure_preimage_set N _ _ (jumpSet_measurable b α)]
      exact uniform01_jumpSet (currentAlpha_pos hp0 hp1 m U n i)
        (currentAlpha_lt_one hp0 hp1 m U n i) b
    · rw [if_neg hli, if_neg hli]
      simp only [preimage_univ]
      exact measure_univ
  rw [Finset.prod_congr rfl (fun l _ => hterm l)]
  rw [Finset.prod_eq_single i (fun l _ hli => by simp only [if_neg hli])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- **The conditional one-step right-jump law on the used-coordinate σ-algebra.** -/
theorem measure_usedSigma_inter_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) :
    arrayMeasure N (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) =
      arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  have hset : pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) ∩ stepUp (N := N) p m n i =
      (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet true (currentAlpha p m U n i)) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨hG, hH⟩, hU⟩
      exact ⟨⟨hG, hH⟩, (stepUp_iff_of_history hH).mp hU⟩
    · rintro ⟨⟨hG, hH⟩, hQ⟩
      exact ⟨⟨hG, hH⟩, (stepUp_iff_of_history hH).mpr hQ⟩
  rw [hset, measure_pastProj_inter_stepUp hp0 hp1 m U n i hA true]
  simp [jumpWeight]

/-- **The conditional one-step left-jump law on the used-coordinate σ-algebra.** -/
theorem measure_usedSigma_inter_stepDown {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) :
    arrayMeasure N (G ∩ historyEvent (actualHistory p m U n) ∩ stepDown p m n i) =
      arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (1 - currentAlpha p m U n i) := by
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hG
  have hset : pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n) ∩ stepDown (N := N) p m n i =
      (pastProj p m U n ⁻¹' A ∩ historyEvent (actualHistory p m U n)) ∩
        ((fun ω : Array N => ω (departureCoord p m U n i)) ⁻¹'
          jumpSet false (currentAlpha p m U n i)) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨hG, hH⟩, hU⟩
      exact ⟨⟨hG, hH⟩, (stepDown_iff_of_history hH).mp hU⟩
    · rintro ⟨⟨hG, hH⟩, hQ⟩
      exact ⟨⟨hG, hH⟩, (stepDown_iff_of_history hH).mpr hQ⟩
  rw [hset, measure_pastProj_inter_stepUp hp0 hp1 m U n i hA false]
  simp [jumpWeight]

/-- **Interior StepHyp conditional on the used coordinates.**  For every used-coordinate
event `G` and every `n` at which the actual walker `i` sits in `{0 <= x < M_n^j}`, the mass
of "walker `i` steps right" inside `G AND history` dominates `omega_j(x)` times the mass of
`G AND history`.  This is the paper's (dominate) in conditional (set-integral) form; it is
*not* a `condExp` w.r.t. a filtration, because `usedSigma` is not shown to be nested. -/
theorem stepUp_measure_ge_omegaAt_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G)
    (h0 : 0 ≤ (trajectory p m U n).pos i)
    (hlt : (trajectory p m U n).pos i < runMax p m U j n) :
    ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) *
        arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) ≤
      arrayMeasure N (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) := by
  rw [measure_usedSigma_inter_stepUp hp0 hp1 m U n i hG]
  have hdom := dominate (le_of_lt hp0) m U hij n h0 hlt
  have hmono : ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) ≤
      ENNReal.ofReal (currentAlpha p m U n i) :=
    ENNReal.ofReal_le_ofReal (by simpa only [currentAlpha] using hdom)
  calc ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) *
        arrayMeasure N (G ∩ historyEvent (actualHistory p m U n))
      = arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (omegaAt p m U j ((trajectory p m U n).pos i)) := mul_comm _ _
    _ ≤ arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)

/-- The revealed weight is nonnegative. -/
lemma omegaAt_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) :
    0 ≤ omegaAt p m U j x := by
  unfold omegaAt
  split <;> linarith

/-- The same inequality in real-valued (measure `.real`) form, i.e. the conditional
probability of a right step is at least `omega_j(x)` on every used-coordinate event. -/
theorem real_stepUp_ge_omegaAt_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G)
    (h0 : 0 ≤ (trajectory p m U n).pos i)
    (hlt : (trajectory p m U n).pos i < runMax p m U j n) :
    omegaAt p m U j ((trajectory p m U n).pos i) *
        (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) ≤
      (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) := by
  have h := stepUp_measure_ge_omegaAt_usedSigma hp0 hp1 m U n hij hG h0 hlt
  have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (omegaAt_nonneg hp0.le m U j _)] at h'

/-- **Conditional one-step crossing law at the paper's top site**, on the used-coordinate
σ-algebra: whenever the actual position of walker `i` at time `n` is `b1`, the conditional
mass of crossing to `b1 + 1` inside any used-coordinate event is exactly `alpha_n^i` times
its mass. -/
theorem measure_usedSigma_inter_crossAt {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (b1 : ℤ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G)
    (hstate : (trajectory p m U n).pos i = b1) :
    arrayMeasure N (G ∩ historyEvent (actualHistory p m U n) ∩ crossAt p m n i b1) =
      arrayMeasure N (G ∩ historyEvent (actualHistory p m U n)) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  have hset : G ∩ historyEvent (actualHistory p m U n) ∩ crossAt (N := N) p m n i b1 =
      G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i := by
    ext ω
    simp only [mem_inter_iff, mem_crossAt, mem_stepUp]
    constructor
    · rintro ⟨⟨hG, hH⟩, h2, h3⟩
      exact ⟨⟨hG, hH⟩, by omega⟩
    · rintro ⟨⟨hG, hH⟩, h3⟩
      have h2 : (trajectory p m ω n).pos i = b1 := by
        rw [trajectory_eq_of_history p m U n hH]; exact hstate
      exact ⟨⟨hG, hH⟩, h2, by omega⟩
  rw [hset, measure_usedSigma_inter_stepUp hp0 hp1 m U n i hG]

/-! ### Step counting: the crossing cannot happen too early

The paper's geometric tail bound uses that `b1+1-b0` consecutive right jumps are needed to
leave the window.  The deterministic half of that statement, at the actual model: to be at
`b1+1` at time `n+k` the walker must have started at least `b1+1-k` at time `n`. -/

lemma pos_le_of_histAt {p : ℝ} (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {x : ℤ}
    {ω : Array N} (hω : ω ∈ histAt p m U n i x) (k : ℕ) :
    (trajectory p m ω (n + k)).pos i ≤ x + (k : ℤ) := by
  induction k with
  | zero => simpa using le_of_eq hω.2
  | succ k ih =>
      have hle := pos_succ_le p m ω (n + k) i
      have e : n + (k + 1) = (n + k) + 1 := by omega
      rw [e]
      push_cast
      omega

/-- **Crossing needs steps.**  From site `x` at time `n`, walker `i` cannot be at `b1 + 1`
before time `n + (b1 + 1 - x)`; equivalently, if `x + k ≤ b1` then the crossing event at time
`n + k` is empty. -/
theorem cross_needs_steps (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (k : ℕ)
    (x b1 : ℤ) (hx : x + (k : ℤ) ≤ b1) :
    histAt p m U n i x ∩ {ω | b1 + 1 ≤ (trajectory p m ω (n + k)).pos i} = ∅ := by
  ext ω
  constructor
  · intro hω
    simp only [mem_inter_iff, mem_ofPred_eq] at hω
    obtain ⟨h1, h2⟩ := hω
    have hle := pos_le_of_histAt m U n i h1 k
    simp only [mem_empty_iff_false]
    omega
  · intro hω
    simp only [mem_empty_iff_false] at hω

/-! ### `usedSigma` is nested, hence the conditional StepHyp holds on every larger
used-coordinate σ-algebra

`areas/transience/GAP.md` records that the *state* σ-algebra `recordMeas` is not proved
nested.  The *used-coordinate* σ-algebra is a different object and **is** nested: the list
`actualHistory p m U n` grows with `n` (`HistoryDeterminism.actualHistory_succ`), so the set
of consumed coordinates grows and the projection to the smaller coordinate set is a
measurable function of the projection to the larger one.  Consequently the exact one-step
law proved above holds conditionally on `usedSigma p m U k` for **every** `k >= n`, not just
`k = n`.  Consequently `n => usedSigma p m U n` is a monotone family of σ-algebras, unlike the
state σ-algebra `recordMeas`.

Caution, recorded deliberately: the one-step law is available for `usedSigma p m U n`-events
**only**, not for events of a later `usedSigma p m U k` (`k > n`).  That direction is false in
general: a `usedSigma p m U (n+1)`-event may itself constrain the very coordinate that decides
the step at time `n` (e.g. `{omega (depCoord_n i) <= alpha_n^i}`), and then the conditional
mass of a right step is `1`, not `alpha_n^i`.  So nesting of `usedSigma` does **not** promote
the one-step law to a larger σ-algebra, and it still is not a `Filtration` carrying the
walker: `X_n` is only a function of the used coordinates on the history event `H_n`. -/

lemma used_append_left {N : ℕ} (a b : List (Record N)) : used a ⊆ used (a ++ b) := by
  intro c hc
  unfold used at hc ⊢
  rw [List.map_append, List.toFinset_append]
  exact Finset.mem_union_left _ hc

lemma used_mono (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    used (actualHistory p m U n) ⊆ used (actualHistory p m U (n + 1)) := by
  rw [HistoryDeterminism.actualHistory_succ]
  exact used_append_left _ _

/-- The used-coordinate σ-algebra is nested in time. -/
lemma usedSigma_mono (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    usedSigma p m U n ≤ usedSigma p m U (n + 1) := by
  intro s hs
  obtain ⟨A, hA, rfl⟩ := (measurableSet_usedSigma_iff p m U n).mp hs
  refine (measurableSet_usedSigma_iff p m U (n + 1)).mpr
    ⟨(fun g : used (actualHistory p m U (n + 1)) → ℝ =>
        fun j : used (actualHistory p m U n) => g ⟨j.1, used_mono p m U n j.2⟩) ⁻¹' A,
      hA.preimage (measurable_pi_lambda _ fun j => measurable_pi_apply _), ?_⟩
  ext ω
  rfl

/-- Monotonicity of the used-coordinate σ-algebra in the time index. -/
lemma usedSigma_mono' (p : ℝ) (m : ℕ) (U : Array N) {n k : ℕ} (h : n ≤ k) :
    usedSigma p m U n ≤ usedSigma p m U k := by
  induction k with
  | zero =>
      have hn : n = 0 := Nat.le_zero.mp h
      subst hn; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (usedSigma_mono p m U k)
      · have : n = k + 1 := le_antisymm h hge
        subst this; exact le_rfl

/-- The used-coordinate σ-algebras of the actual trajectory form a monotone family. -/
lemma monotone_usedSigma (p : ℝ) (m : ℕ) (U : Array N) :
    Monotone (fun n => usedSigma p m U n) := fun _ _ h => usedSigma_mono' p m U h

set_option linter.unusedVariables false in
/-- **The conditional one-step drift of the crossing scale function.**  For every event `G`
of the used-coordinate σ-algebra and every interior site, the two-point conditional
expectation of `f(X_{n+1}^i) - f(X_n^i)` given the used coordinates is `(alpha - w x)` times
`f(x+1) - f(x-1)` — and hence nonnegative on the paper's interior event `{0 <= x < M_n^j}`.

This is the paper's drift computation of the proof of Lemma `transience` in conditional
(set-integral) form at the actual model: no `condExp` object is built, but the identity holds
tested against *every* event of the used-coordinate σ-algebra `usedSigma p m U n`, which is
the exact content of "`E[f(X_{n+1}) - f(X_n) | F_n] = ...`" for `F_n = usedSigma p m U n`.

Same caveat as `oneStep_drift`: the displayed identity is the drift at the site `x` and needs
the identification `hpos : X_n^i = x`.  The site-conditioned form (no `hpos` required) is
`oneStep_drift_usedSigma_at`.  As in `oneStep_drift`, `hpos` is kept although the displayed
algebra does not consume it. -/
theorem oneStep_drift_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {w : ℕ → ℝ}
    (hlo : ∀ y, 1 / 2 ≤ w y) (hhi : ∀ y, w y < 1) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) (hpos : (trajectory p m U n).pos i = (x : ℤ))
    {G : Set (Array N)} (hG : MeasurableSet[usedSigma p m U n] G) :
    (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) *
        (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      + (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n) ∩ stepDown p m n i) *
        (sc w b0 b1 (x - 1) - sc w b0 b1 x)
      = (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) *
        ((currentAlpha p m U n i - w x) *
          (sc w b0 b1 (x + 1) - sc w b0 b1 (x - 1))) := by
  -- as in `oneStep_drift`: `hpos` is the site identification, not part of the algebra.
  have hα0 := currentAlpha_pos hp0 hp1 m U n i
  have hα1 := currentAlpha_lt_one hp0 hp1 m U n i
  have hU := measure_usedSigma_inter_stepUp hp0 hp1 m U n i hG
  have hD := measure_usedSigma_inter_stepDown hp0 hp1 m U n i hG
  have e1 : (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) =
      (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) * currentAlpha p m U n i := by
    simp only [Measure.real, hU, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0.le]
  have e2 : (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n) ∩ stepDown p m n i) =
      (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) *
        (1 - currentAlpha p m U n i) := by
    simp only [Measure.real, hD, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - currentAlpha p m U n i)]
  have hdr := sc_drift (w := w) hlo hhi hb hx0 hx1 (currentAlpha p m U n i)
  rw [e1, e2]
  linear_combination (arrayMeasure N).real (G ∩ historyEvent (actualHistory p m U n)) * hdr

/-- **The conditional drift is nonnegative on the paper's interior event.** -/
theorem interior_condExp_drift_usedSigma {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G)
    (hpos : (trajectory p m U n).pos i = (x : ℤ))
    (h0 : 0 ≤ (x : ℤ)) (hlt : (x : ℤ) < runMax p m U j n) :
    0 ≤ (arrayMeasure N).real
          (G ∩ historyEvent (actualHistory p m U n) ∩ stepUp p m n i) *
        (sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 (x + 1) -
          sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 x)
      + (arrayMeasure N).real
          (G ∩ historyEvent (actualHistory p m U n) ∩ stepDown p m n i) *
        (sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 (x - 1) -
          sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 x) := by
  have hlo : ∀ y : ℕ, 1 / 2 ≤ omegaAt p m U j (y : ℤ) := by
    intro y; unfold omegaAt; split <;> linarith
  have hhi : ∀ y : ℕ, omegaAt p m U j (y : ℤ) < 1 := by
    intro y; unfold omegaAt; split <;> linarith
  rw [oneStep_drift_usedSigma hp0 hp1 m U n i hlo hhi hb hx0 hx1 hpos hG]
  refine mul_nonneg ENNReal.toReal_nonneg (mul_nonneg ?_ ?_)
  · have hdom := dominate (le_of_lt hp0) m U hij n (by rw [hpos]; exact h0)
      (by rw [hpos]; exact hlt)
    have hdom' : omegaAt p m U j (x : ℤ) ≤ currentAlpha p m U n i := by
      simpa only [currentAlpha, hpos] using hdom
    linarith
  · exact sub_nonneg.mpr (sc_monotone hlo hhi hb (by omega : x - 1 ≤ x + 1))

/-! ### Site-conditioned form: the drift is genuinely the drift of `sc (X_n)` at the walker's
site

In `oneStep_drift`/`oneStep_drift_nonneg`/`oneStep_drift_usedSigma` the site `x` must be
identified with the walker's current site (`hpos`).  Here the site condition is built into the
*event* instead: everything is tested against `histAt p m U n i x = H_n AND {X_n^i = x}`, on
which `X_n^i = x` holds by construction.  These versions therefore need no `hpos`, and the
weighted masses are literally the masses of the two branches of `f (X_{n+1}^i) - f (x)`. -/

/-- **The drift at the walker's site.**  On `histAt x` the walker is at `x`, so the two terms
are the masses of the two one-step branches of `f (X_{n+1}^i) - f (X_n^i)`, and their weighted
sum is `(alpha - w x) (f(x+1) - f(x-1))` times the mass of `histAt x`. -/
theorem oneStep_drift_at {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {w : ℕ → ℝ}
    (hlo : ∀ y, 1 / 2 ≤ w y) (hhi : ∀ y, w y < 1) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) :
    (arrayMeasure N).real (histAt p m U n i (x : ℤ) ∩ stepUp p m n i) *
        (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      + (arrayMeasure N).real (histAt p m U n i (x : ℤ) ∩ stepDown p m n i) *
        (sc w b0 b1 (x - 1) - sc w b0 b1 x)
      = (arrayMeasure N).real (histAt p m U n i (x : ℤ)) *
        ((currentAlpha p m U n i - w x) *
          (sc w b0 b1 (x + 1) - sc w b0 b1 (x - 1))) := by
  have hα0 := currentAlpha_pos hp0 hp1 m U n i
  have hα1 := currentAlpha_lt_one hp0 hp1 m U n i
  have e1 : (arrayMeasure N).real (histAt p m U n i (x : ℤ) ∩ stepUp p m n i) =
      (arrayMeasure N).real (histAt p m U n i (x : ℤ)) * currentAlpha p m U n i := by
    simp only [Measure.real, measure_histAt_inter_stepUp hp0 hp1 m U n i (x : ℤ),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0.le]
  have e2 : (arrayMeasure N).real (histAt p m U n i (x : ℤ) ∩ stepDown p m n i) =
      (arrayMeasure N).real (histAt p m U n i (x : ℤ)) * (1 - currentAlpha p m U n i) := by
    simp only [Measure.real, measure_histAt_inter_stepDown hp0 hp1 m U n i (x : ℤ),
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - currentAlpha p m U n i)]
  have hdr := sc_drift (w := w) hlo hhi hb hx0 hx1 (currentAlpha p m U n i)
  rw [e1, e2]
  linear_combination (arrayMeasure N).real (histAt p m U n i (x : ℤ)) * hdr

/-- The site-restricted exact one-step mass inside an arbitrary used-coordinate event. -/
theorem measure_usedSigma_inter_histAt_stepUp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) :
    arrayMeasure N (G ∩ histAt p m U n i x ∩ stepUp p m n i) =
      arrayMeasure N (G ∩ histAt p m U n i x) *
        ENNReal.ofReal (currentAlpha p m U n i) := by
  by_cases hx : (trajectory p m U n).pos i = x
  · rw [histAt_eq, if_pos hx]
    exact measure_usedSigma_inter_stepUp hp0 hp1 m U n i hG
  · rw [histAt_eq, if_neg hx]
    simp

/-- The site-restricted exact one-step mass, left branch. -/
theorem measure_usedSigma_inter_histAt_stepDown {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) :
    arrayMeasure N (G ∩ histAt p m U n i x ∩ stepDown p m n i) =
      arrayMeasure N (G ∩ histAt p m U n i x) *
        ENNReal.ofReal (1 - currentAlpha p m U n i) := by
  by_cases hx : (trajectory p m U n).pos i = x
  · rw [histAt_eq, if_pos hx]
    exact measure_usedSigma_inter_stepDown hp0 hp1 m U n i hG
  · rw [histAt_eq, if_neg hx]
    simp

/-- **The site-conditioned drift, tested against every used-coordinate event.**  No `hpos`:
the site condition is part of the event. -/
theorem oneStep_drift_usedSigma_at {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) {w : ℕ → ℝ}
    (hlo : ∀ y, 1 / 2 ≤ w y) (hhi : ∀ y, w y < 1) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G) :
    (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepUp p m n i) *
        (sc w b0 b1 (x + 1) - sc w b0 b1 x)
      + (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepDown p m n i) *
        (sc w b0 b1 (x - 1) - sc w b0 b1 x)
      = (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ)) *
        ((currentAlpha p m U n i - w x) *
          (sc w b0 b1 (x + 1) - sc w b0 b1 (x - 1))) := by
  have hα0 := currentAlpha_pos hp0 hp1 m U n i
  have hα1 := currentAlpha_lt_one hp0 hp1 m U n i
  have e1 : (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepUp p m n i) =
      (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ)) * currentAlpha p m U n i := by
    simp only [Measure.real, measure_usedSigma_inter_histAt_stepUp hp0 hp1 m U n i (x : ℤ) hG,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0.le]
  have e2 : (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepDown p m n i) =
      (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ)) * (1 - currentAlpha p m U n i) := by
    simp only [Measure.real, measure_usedSigma_inter_histAt_stepDown hp0 hp1 m U n i (x : ℤ) hG,
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - currentAlpha p m U n i)]
  have hdr := sc_drift (w := w) hlo hhi hb hx0 hx1 (currentAlpha p m U n i)
  rw [e1, e2]
  linear_combination (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ)) * hdr

/-- **Paper-interior drift at the walker's site, conditionally on the used coordinates.**
No `hpos`: the site is part of the event `histAt x`, and the interior hypothesis
`0 <= x < M_n^j` makes `omega_j(x) <= alpha_n^i` by (dominate). -/
theorem interior_drift_at {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (U : Array N) (n : ℕ) {i j : Fin N} (hij : i ≠ j) {b0 b1 x : ℕ} (hb : b0 ≤ b1)
    (hx0 : b0 < x) (hx1 : x ≤ b1) {G : Set (Array N)}
    (hG : MeasurableSet[usedSigma p m U n] G)
    (hpos : (trajectory p m U n).pos i = (x : ℤ))
    (h0 : 0 ≤ (x : ℤ)) (hlt : (x : ℤ) < runMax p m U j n) :
    0 ≤ (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepUp p m n i) *
        (sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 (x + 1) -
          sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 x)
      + (arrayMeasure N).real (G ∩ histAt p m U n i (x : ℤ) ∩ stepDown p m n i) *
        (sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 (x - 1) -
          sc (fun y : ℕ => omegaAt p m U j (y : ℤ)) b0 b1 x) := by
  have hlo : ∀ y : ℕ, 1 / 2 ≤ omegaAt p m U j (y : ℤ) := by
    intro y; unfold omegaAt; split <;> linarith
  have hhi : ∀ y : ℕ, omegaAt p m U j (y : ℤ) < 1 := by
    intro y; unfold omegaAt; split <;> linarith
  rw [oneStep_drift_usedSigma_at hp0 hp1 m U n i hlo hhi hb hx0 hx1 hG]
  refine mul_nonneg ENNReal.toReal_nonneg (mul_nonneg ?_ ?_)
  · have hdom := dominate (le_of_lt hp0) m U hij n (by rw [hpos]; exact h0)
      (by rw [hpos]; exact hlt)
    have hdom' : omegaAt p m U j (x : ℤ) ≤ currentAlpha p m U n i := by
      simpa only [currentAlpha, hpos] using hdom
    linarith
  · exact sub_nonneg.mpr (sc_monotone hlo hhi hb (by omega : x - 1 ≤ x + 1))

end Swarming.StepCross

/-! ### Axiom audit -/


