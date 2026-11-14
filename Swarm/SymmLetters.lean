import Swarm.Trajectory
import Swarm.FreshIndependence

open scoped ENNReal

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

namespace Swarming.FairWalk

/-! ### Letters -/

/-- The letter of a driving uniform: first bit `2u ≤ 1` (drives `symmetricStep`),
second bit `u ≤ p` (decides the step when the walker is excited). -/
noncomputable def letter (p : ℝ) (u : ℝ) : Bool × Bool :=
  (if 2 * u ≤ 1 then true else false, if u ≤ p then true else false)

/-- The set of uniforms carrying a given letter. -/
noncomputable abbrev letterSet (p : ℝ) (l : Bool × Bool) : Set ℝ :=
  {u | letter p u = l}

lemma measurableSet_letterSet (p : ℝ) (l : Bool × Bool) : MeasurableSet (letterSet p l) := by
  obtain ⟨b1, b2⟩ := l
  have hfac : letterSet p (b1, b2) =
      ({u : ℝ | (if 2 * u ≤ 1 then true else false) = b1} ∩
        {u : ℝ | (if u ≤ p then true else false) = b2}) := by
    ext u
    simp only [letterSet, letter, Set.mem_ofPred_eq, Set.mem_inter_iff, Prod.mk.injEq]
  rw [hfac]
  refine MeasurableSet.inter ?_ ?_
  · cases b1
    · have h : {u : ℝ | (if 2 * u ≤ 1 then true else false) = false} = {u | 1 / 2 < u} := by
        ext u
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
        by_cases hu : 2 * u ≤ 1
        · rw [if_pos hu]; simp; linarith
        · rw [if_neg hu]; simp; linarith
      rw [h]; exact measurableSet_Ioi
    · have h : {u : ℝ | (if 2 * u ≤ 1 then true else false) = true} = {u | u ≤ 1 / 2} := by
        ext u
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
        by_cases hu : 2 * u ≤ 1
        · rw [if_pos hu]; simp; linarith
        · rw [if_neg hu]; simp; linarith
      rw [h]; exact measurableSet_Iic
  · cases b2
    · have h : {u : ℝ | (if u ≤ p then true else false) = false} = {u | p < u} := by
        ext u; by_cases hu : u ≤ p <;> simp [hu]
      rw [h]; exact measurableSet_Ioi
    · have h : {u : ℝ | (if u ≤ p then true else false) = true} = {u | u ≤ p} := by
        ext u; by_cases hu : u ≤ p <;> simp [hu]
      rw [h]; exact measurableSet_Iic

/-- `symmetricStep` is the sign of the first letter bit. -/
lemma symmetricStep_eq_letter (p : ℝ) (u : ℝ) :
    symmetricStep u = if (letter p u).1 then (1 : ℤ) else -1 := by
  unfold letter symmetricStep
  by_cases h : 2 * u ≤ 1
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp

/-- The step driven with right probability `α ∈ {1/2, p}` is a function of the letter. -/
noncomputable def lstep (l : Bool × Bool) (α : ℝ) : ℤ :=
  if α = 1 / 2 then (if l.1 then 1 else -1) else (if l.2 then 1 else -1)

lemma drivenStep_eq_lstep (p : ℝ) {α u : ℝ} (hα : α = 1 / 2 ∨ α = p) :
    drivenStep u α = lstep (letter p u) α := by
  have key1 : ∀ u : ℝ, drivenStep u (1 / 2) = (if 2 * u ≤ 1 then (1 : ℤ) else -1) := by
    intro u
    unfold drivenStep
    by_cases h : 2 * u ≤ 1
    · rw [if_pos h, if_pos (show u ≤ 1 / 2 by linarith)]
    · rw [if_neg h, if_neg (show ¬ (u ≤ 1 / 2) by linarith)]
  rcases hα with h | h
  · rw [h]
    unfold lstep
    rw [if_pos rfl]
    rw [key1 u]
    have hb : (letter p u).1 = decide (2 * u ≤ 1) := rfl
    rw [hb]
    by_cases h1 : 2 * u ≤ 1 <;> simp [h1]
  · rw [h]
    by_cases hp : p = 1 / 2
    · rw [hp]
      unfold lstep
      rw [if_pos rfl, key1 u]
      have hb : (letter (1 / 2) u).1 = decide (2 * u ≤ 1) := rfl
      rw [hb]
      by_cases h1 : 2 * u ≤ 1 <;> simp [h1]
    · unfold lstep
      rw [if_neg hp]
      unfold drivenStep letter
      by_cases h1 : u ≤ p
      · rw [if_pos h1, if_pos h1]; simp
      · rw [if_neg h1, if_neg h1]; simp

lemma rightProbability_eq_half_or_p {N : ℕ} (p : ℝ) (m : ℕ) (ell : LocalTimes N)
    (i : Fin N) (x : ℤ) :
    rightProbability p m ell i x = 1 / 2 ∨ rightProbability p m ell i x = p := by
  unfold rightProbability
  split <;> simp

/-! ### The letter automaton -/

lemma walkState_ext {N : ℕ} {a b : WalkState N} (hp : a.pos = b.pos) (he : a.ell = b.ell) :
    a = b := by
  cases a; cases b; simp_all

/-- Next positions, driven by the letters read at the departure sites. -/
noncomputable def lamNextPos {N : ℕ} (p : ℝ) (m : ℕ) (l : Fin N → Bool × Bool)
    (s : WalkState N) : Fin N → ℤ :=
  fun i => s.pos i + lstep (l i) (rightProbability p m s.ell i (s.pos i))

/-- Next walk state, driven by letters. -/
noncomputable def lamNextState {N : ℕ} (p : ℝ) (m : ℕ) (l : Fin N → Bool × Bool)
    (s : WalkState N) : WalkState N where
  pos := lamNextPos p m l s
  ell i x := s.ell i x + if x = lamNextPos p m l s i then 1 else 0

/-- The trajectory recursion driven by an arbitrary letter sequence. -/
noncomputable def runL {N : ℕ} (p : ℝ) (m : ℕ) (ls : ℕ → Fin N → Bool × Bool) :
    ℕ → WalkState N
  | 0 => initialWalkState
  | n + 1 => lamNextState p m (ls n) (runL p m ls n)

@[simp] lemma runL_zero {N : ℕ} (p : ℝ) (m : ℕ) (ls : ℕ → Fin N → Bool × Bool) :
    runL p m ls 0 = initialWalkState := rfl

@[simp] lemma runL_succ {N : ℕ} (p : ℝ) (m : ℕ) (ls : ℕ → Fin N → Bool × Bool) (n : ℕ) :
    runL p m ls (n + 1) = lamNextState p m (ls n) (runL p m ls n) := rfl

/-- The letter sequence read by the actual array. -/
noncomputable def readLetter {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) :
    Bool × Bool :=
  letter p (ω (departureCoord p m ω n i))

lemma lamNextPos_eq_nextPos {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N) (s : WalkState N) :
    lamNextPos p m (fun i => letter p (ω (i, s.pos i, s.ell i (s.pos i)))) s = nextPos p m ω s := by
  funext i
  simp only [lamNextPos, nextPos]
  rw [drivenStep_eq_lstep p (rightProbability_eq_half_or_p p m s.ell i (s.pos i))]

lemma lamNextState_eq_nextWalkState {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N)
    (s : WalkState N) :
    lamNextState p m (fun i => letter p (ω (i, s.pos i, s.ell i (s.pos i)))) s =
      nextWalkState p m ω s := by
  apply walkState_ext
  · exact lamNextPos_eq_nextPos p m ω s
  · funext i x
    simp only [lamNextState, nextWalkState]
    rw [lamNextPos_eq_nextPos p m ω s]

/-- The letter automaton reproduces the actual trajectory. -/
theorem runL_readLetter {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N) :
    ∀ n, runL p m (readLetter p m ω) n = trajectory p m ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runL_succ, trajectory_succ, ih]
      have h : readLetter p m ω n =
          (fun i => letter p (ω (i, (trajectory p m ω n).pos i,
            (trajectory p m ω n).ell i ((trajectory p m ω n).pos i)))) := rfl
      rw [h]
      exact lamNextState_eq_nextWalkState p m ω (trajectory p m ω n)

/-- The departure coordinate is read off the letter automaton. -/
lemma departureCoord_eq_readC {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ) (i : Fin N) :
    departureCoord p m ω n i =
      (i, (runL p m (readLetter p m ω) n).pos i,
        (runL p m (readLetter p m ω) n).ell i ((runL p m (readLetter p m ω) n).pos i)) := by
  rw [runL_readLetter]
  rfl

/-- The symmetric step at departure `n` is a function of the read letter. -/
theorem symmetricStep_eq_readLetter {N : ℕ} (p : ℝ) (m : ℕ) (ω : Array N) (n : ℕ)
    (i : Fin N) :
    symmetricStep (ω (departureCoord p m ω n i)) =
      (if (readLetter p m ω n i).1 then (1 : ℤ) else -1) := by
  have h : (readLetter p m ω n i).1 =
      (letter p (ω (departureCoord p m ω n i))).1 := rfl
  rw [h, ← symmetricStep_eq_letter]

end Swarming.FairWalk

namespace Swarming.FairWalk

/-! ### Determinism of the letter automaton and freshness of its reads -/

variable {N : ℕ}

/-- The read coordinate of the letter automaton at time `n` for walker `i`. -/
noncomputable def readC (p : ℝ) (m : ℕ) (ls : ℕ → Fin N → Bool × Bool) (n : ℕ)
    (i : Fin N) : Fin N × ℤ × ℕ :=
  (i, (runL p m ls n).pos i, (runL p m ls n).ell i ((runL p m ls n).pos i))

/-- Letter sequences agreeing up to `n` drive the same state at `n`. -/
lemma runL_congr {p : ℝ} {m : ℕ} {ls ls' : ℕ → Fin N → Bool × Bool} (n : ℕ)
    (h : ∀ s, s < n → ls s = ls' s) : runL p m ls n = runL p m ls' n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [runL_succ, runL_succ, h k (Nat.lt_succ_self k),
        ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self k)))]

/-- Matching read letters up to `r` forces the read coordinates to agree. -/
lemma departureCoord_eq_of_readLetters {p : ℝ} {m : ℕ} {ω : Array N}
    {ls : ℕ → Fin N → Bool × Bool}
    (h : ∀ n < r, ∀ i, readLetter p m ω n i = ls n i) :
    ∀ n ≤ r, ∀ i, departureCoord p m ω n i = readC p m ls n i := by
  intro n hn i
  have hc := departureCoord_eq_readC (p := p) (m := m) (ω := ω) n i
  have hrun : runL p m (readLetter p m ω) n = runL p m ls n :=
    runL_congr n (fun s hs => funext (fun j => h s (Nat.lt_of_lt_of_le hs hn) j))
  rw [hc, hrun]
  rfl

/-- A cylinder condition on the automaton reads forces the read letters. -/
lemma readLetter_eq_of_cylinder {p : ℝ} {m : ℕ} {ls : ℕ → Fin N → Bool × Bool}
    {ω : Array N} {r : ℕ}
    (hcyl : ∀ n < r, ∀ i, letter p (ω (readC p m ls n i)) = ls n i) :
    ∀ n < r, ∀ i, readLetter p m ω n i = ls n i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn i
      have hagree : ∀ s < n, ∀ j, readLetter p m ω s j = ls s j :=
        fun s hs j => ih s hs (Nat.lt_trans hs hn) j
      have hcoord := departureCoord_eq_of_readLetters (r := n) hagree n (le_refl n) i
      calc readLetter p m ω n i = letter p (ω (readC p m ls n i)) := by
            unfold readLetter
            rw [hcoord]
        _ = ls n i := hcyl n hn i

/-- Matching read letters put the letters at the automaton reads in place. -/
lemma cylinder_of_readLetters {p : ℝ} {m : ℕ} {ls : ℕ → Fin N → Bool × Bool}
    {ω : Array N} {r : ℕ}
    (h : ∀ n < r, ∀ i, readLetter p m ω n i = ls n i) :
    ∀ n < r, ∀ i, letter p (ω (readC p m ls n i)) = ls n i := by
  intro n hn i
  rw [← h n hn i]
  unfold readLetter
  rw [departureCoord_eq_of_readLetters h n (le_of_lt hn) i]

/-- Local times stored by the letter automaton are monotone in time. -/
lemma runL_ell_mono_step {p : ℝ} {m : ℕ} (ls : ℕ → Fin N → Bool × Bool) (k : ℕ)
    (i : Fin N) (x : ℤ) :
    (runL p m ls k).ell i x ≤ (runL p m ls (k + 1)).ell i x := by
  rw [runL_succ]
  simp only [lamNextState]
  split <;> omega

lemma runL_ell_mono {p : ℝ} {m : ℕ} (ls : ℕ → Fin N → Bool × Bool) {n k : ℕ}
    (hnk : n ≤ k) (i : Fin N) (x : ℤ) :
    (runL p m ls n).ell i x ≤ (runL p m ls k).ell i x := by
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (runL_ell_mono_step ls k i x)

/-- At a strictly later time, the local time of the current position is strictly larger. -/
lemma runL_ell_lt_current {p : ℝ} {m : ℕ} (ls : ℕ → Fin N → Bool × Bool) {n k : ℕ}
    (hnk : n < k) (i : Fin N) :
    (runL p m ls n).ell i ((runL p m ls k).pos i) <
      (runL p m ls k).ell i ((runL p m ls k).pos i) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : (runL p m ls n).ell i ((runL p m ls (j + 1)).pos i) ≤
      (runL p m ls j).ell i ((runL p m ls (j + 1)).pos i) :=
    runL_ell_mono ls (by omega) i _
  have h2 : (runL p m ls j).ell i ((runL p m ls (j + 1)).pos i) + 1 ≤
      (runL p m ls (j + 1)).ell i ((runL p m ls (j + 1)).pos i) := by
    have hposj : (runL p m ls (j + 1)).pos i = lamNextPos p m (ls j) (runL p m ls j) i := rfl
    rw [hposj]
    simp only [runL_succ, lamNextState]
    simp
  omega

/-- Every coordinate is read at most once by the letter automaton. -/
lemma readC_injective {p : ℝ} {m : ℕ} (ls : ℕ → Fin N → Bool × Bool) (r : ℕ) :
    Function.Injective (fun ni : Fin r × Fin N => readC p m ls ni.1 ni.2) := by
  rintro ⟨n, i⟩ ⟨n', i'⟩ heq
  simp only [readC, Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨hi, hpos, hell⟩ := heq
  subst hi
  rcases lt_trichotomy n n' with h | h | h
  · exfalso
    have hlt := runL_ell_lt_current (p := p) (m := m) ls h i
    rw [hpos] at hell
    exact absurd hell (ne_of_lt hlt)
  · subst h; rfl
  · exfalso
    have hlt := runL_ell_lt_current (p := p) (m := m) ls h i
    rw [← hpos] at hell
    exact absurd hell.symm (ne_of_lt hlt)

end Swarming.FairWalk

namespace Swarming.FairWalk

/-! ### Boxes and their exact masses -/

variable {N : ℕ}

/-- Default letter used outside the prescribed prefix. -/
noncomputable def defaultLetter : Bool × Bool := (true, true)

/-- Extend a finite letter pattern by default letters. -/
noncomputable def extLetter (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    ℕ → Fin N → Bool × Bool :=
  fun n i => if h : n < r then q ⟨n, h⟩ i else defaultLetter

/-- The read coordinate of the automaton driven by `q`. -/
noncomputable abbrev ccOf (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool)
    (n : Fin r) (i : Fin N) : Fin N × ℤ × ℕ :=
  readC p m (extLetter r q) n i

/-- The uniform probability of a letter. -/
noncomputable abbrev letterLaw (p : ℝ) (l : Bool × Bool) : ℝ≥0∞ := uniform01 (letterSet p l)

/-- The set of arrays whose read letters up to `r` follow the pattern `q`. -/
noncomputable def boxSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    Set (Array N) :=
  {ω | ∀ (n : Fin r) (i : Fin N), readLetter p m ω n i = q n i}

/-- The cylinder set prescribing the letters at the automaton's read coordinates. -/
noncomputable def cylSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    Set (Array N) :=
  {ω | ∀ (n : Fin r) (i : Fin N), letter p (ω (ccOf p m r q n i)) = q n i}

theorem boxSet_eq_cylSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    boxSet p m r q = cylSet p m r q := by
  ext ω
  constructor
  · intro h n i
    have h2 := (cylinder_of_readLetters (ls := extLetter r q)
      (fun k hk j => by
        have hh := h ⟨k, hk⟩ j
        simpa [extLetter, hk] using hh)) (↑n) n.isLt i
    simpa [extLetter, n.isLt] using h2
  · intro h n i
    have h' : ∀ k < r, ∀ j, letter p (ω (readC p m (extLetter r q) k j)) = extLetter r q k j := by
      intro k hk j
      have hh := h ⟨k, hk⟩ j
      simpa [ccOf, extLetter, hk] using hh
    have h2 := (readLetter_eq_of_cylinder (ls := extLetter r q) h') (↑n) n.isLt i
    simpa [extLetter, n.isLt] using h2

theorem measurableSet_cylSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    MeasurableSet (cylSet p m r q) := by
  have h : cylSet p m r q =
      ⋂ (n : Fin r) (i : Fin N), (fun ω : Array N => ω (ccOf p m r q n i)) ⁻¹'
        (letterSet p (q n i)) := by
    ext ω
    simp only [cylSet, Set.mem_iInter, Set.mem_preimage, letterSet, Set.mem_ofPred_eq]
  rw [h]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun i =>
    (measurableSet_letterSet p (q n i)).preimage (measurable_pi_apply _)

theorem measurableSet_boxSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    MeasurableSet (boxSet p m r q) := by
  rw [boxSet_eq_cylSet]
  exact measurableSet_cylSet p m r q

/-- The exact mass of a box: the product of the letter probabilities. -/
theorem mass_boxSet (p : ℝ) (m : ℕ) (r : ℕ) (q : Fin r → Fin N → Bool × Bool) :
    arrayMeasure N (boxSet p m r q) =
      ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) := by
  rw [boxSet_eq_cylSet]
  have hcyl : cylSet p m r q =
      ⋂ ni : Fin r × Fin N, (fun ω : Array N => ω (readC p m (extLetter r q) ni.1 ni.2)) ⁻¹'
        (letterSet p (q ni.1 ni.2)) := by
    ext ω
    simp [cylSet, ccOf]
  rw [hcyl, SwarmIID.indep_iInter_comp (array_independent N)
    (readC_injective (p := p) (m := m) (extLetter r q) r)
    (fun ni => letterSet p (q ni.1 ni.2)) (fun ni => measurableSet_letterSet p _)]
  refine Finset.prod_congr rfl fun ni _ => ?_
  exact arrayMeasure_preimage_set N _ _ (measurableSet_letterSet p _)

end Swarming.FairWalk

namespace Swarming.FairWalk

variable {N : ℕ}

/-- The sign carried by a letter. -/
def lsgn (l : Bool × Bool) : ℤ := if l.1 then 1 else -1

/-- The set of arrays on which the auxiliary walk's increments follow the pattern `ε`. -/
noncomputable def patSet (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) : Set (Array N) :=
  {ω | ∀ n : Fin r, symmetricStep (ω (departureCoord p m ω n i)) = ε n}

/-- The letter patterns producing the sign pattern `ε`. -/
abbrev goodPattern (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) (q : Fin r → Fin N → Bool × Bool) : Prop :=
  ∀ n : Fin r, lsgn (q n i) = ε n

theorem patSet_eq_iUnion (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    patSet p m r i ε = ⋃ q : Fin r → Fin N → Bool × Bool,
      (if goodPattern r i ε q then boxSet p m r q else ∅) := by
  classical
  ext ω
  constructor
  · intro h
    have hgood : goodPattern r i ε (fun n j => readLetter p m ω n j) := by
      intro n
      show (if (readLetter p m ω n i).1 then (1 : ℤ) else -1) = ε n
      rw [← symmetricStep_eq_readLetter]
      exact h n
    refine Set.mem_iUnion.2 ⟨fun n j => readLetter p m ω n j, ?_⟩
    rw [if_pos hgood]
    exact fun n j => rfl
  · intro h
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 h
    by_cases hg : goodPattern r i ε q
    · rw [if_pos hg] at hq
      intro n
      rw [symmetricStep_eq_readLetter, hq n i]
      exact hg n
    · rw [if_neg hg] at hq
      exact absurd hq (Set.notMem_empty ω)

/-- The second direction of the union needs only that boxes for different patterns are disjoint. -/
theorem disjoint_boxSet {q q' : Fin r → Fin N → Bool × Bool} (h : q ≠ q') :
    Disjoint (boxSet p m r q) (boxSet p m r q') := by
  refine Set.disjoint_left.2 fun ω h1 h2 => h ?_
  funext n j
  rw [← h1 n j, ← h2 n j]

/-- The exact mass of the increment pattern set, as a finite sum of box masses. -/
theorem mass_patSet (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    arrayMeasure N (patSet p m r i ε) =
      ∑ q : Fin r → Fin N → Bool × Bool,
        if goodPattern r i ε q then ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0 := by
  classical
  rw [patSet_eq_iUnion, measure_iUnion]
  · rw [tsum_fintype]
    exact Finset.sum_congr rfl fun q _ => by
      by_cases hg : goodPattern r i ε q
      · rw [if_pos hg, if_pos hg, mass_boxSet]
      · rw [if_neg hg, if_neg hg, measure_empty]
  · intro q q' hne
    show Disjoint (if goodPattern r i ε q then boxSet p m r q else ∅)
      (if goodPattern r i ε q' then boxSet p m r q' else ∅)
    by_cases hg : goodPattern r i ε q
    · by_cases hg' : goodPattern r i ε q'
      · rw [if_pos hg, if_pos hg']
        exact disjoint_boxSet (p := p) (m := m) (r := r) hne
      · rw [if_pos hg, if_neg hg']
        exact Set.disjoint_empty _
    · rw [if_neg hg]
      exact Set.empty_disjoint _
  · intro q
    by_cases hg : goodPattern r i ε q
    · rw [if_pos hg]; exact measurableSet_boxSet p m r q
    · rw [if_neg hg]; exact MeasurableSet.empty

end Swarming.FairWalk

namespace Swarming.FairWalk

variable {N : ℕ}

/-! ### The auxiliary walk and its finite-path law -/

/-- The increment of the auxiliary walk at departure `n`. -/
noncomputable def symmInc (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) (n : ℕ) : ℤ :=
  symmetricStep (ω (departureCoord p m ω n i))

/-- The auxiliary walk is the sum of its increments. -/
theorem symmetricWalk_eq_sum (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) (n : ℕ) :
    symmetricWalk p m ω i n = ∑ k ∈ Finset.range n, symmInc p m ω i k := by
  induction n with
  | zero => simp [symmetricWalk]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl

lemma symmInc_eq_lsgn (p : ℝ) (m : ℕ) (ω : Array N) (i : Fin N) (n : ℕ) :
    symmInc p m ω i n = lsgn (readLetter p m ω n i) := by
  unfold symmInc lsgn
  exact symmetricStep_eq_readLetter p m ω n i

/-- The pattern set of the auxiliary walk is the set where the increments follow `ε`. -/
theorem patSet_eq_increment_set (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    patSet p m r i ε = {ω : Array N | ∀ n : Fin r, symmInc p m ω i n = ε n} := rfl

/-- **The exact finite-path law of the actual auxiliary walk**, in cylinder form: the mass of any
increment pattern is the explicit finite sum of the letter-box masses. -/
theorem symmetricWalk_pattern_mass (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    arrayMeasure N {ω : Array N | ∀ n : Fin r, symmInc p m ω i n = ε n} =
      ∑ q : Fin r → Fin N → Bool × Bool,
        if goodPattern r i ε q then ∏ ni : Fin r × Fin N, letterLaw p (q ni.1 ni.2) else 0 := by
  rw [← patSet_eq_increment_set]
  exact mass_patSet p m r i ε

/-- The increments are measurable: the mass of any increment pattern is a finite sum. -/
theorem measurableSet_increment_pattern (p : ℝ) (m : ℕ) (r : ℕ) (i : Fin N) (ε : Fin r → ℤ) :
    MeasurableSet {ω : Array N | ∀ n : Fin r, symmInc p m ω i n = ε n} := by
  rw [← patSet_eq_increment_set, patSet_eq_iUnion]
  refine MeasurableSet.iUnion fun q => ?_
  by_cases hg : goodPattern r i ε q
  · rw [if_pos hg]; exact measurableSet_boxSet p m r q
  · rw [if_neg hg]; exact MeasurableSet.empty

end Swarming.FairWalk


