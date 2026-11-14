/-
# Marked hits are excited steps: the occupation input of Proposition `ball`

Continuation of `Marks.lean`.  Paper `main_1d_revised.tex`, strategy paragraph of §1:

  "We therefore know that every nonnegative marked site strictly below its running maximum is
   excited for every other walker.  Combining the one-dimensional Poisson equation for the
   transition probabilities determined by these marks with a correction near the running
   maximum, we bound the time that one walker spends at or below another walker's running
   maximum.  From this occupation estimate, we prove the positive lower speed in
   Proposition `ball`."

`excited_of_mark` (`Marks.lean`) is the first sentence.  This file turns it into the counting
statement that the occupation estimate consumes:

* `MarkHit p m U i j t` — walker `j` sits at time `t` on a site that is marked for walker `i`
  and strictly below `i`'s running maximum;
* `rightProbability_eq_p_of_markHit` — at such a site the right-jump probability of `j` is
  exactly `p` (paper display `(dominate)` at its extreme value: the environment `omega` is `p`
  at marked sites and `1/2` elsewhere);
* `markHitCount_le_excitedSteps` — **the counting step**: on a path where walker `j` is never
  negative, the number of marked hits of `j` up to time `n` is at most the number of excited
  steps of `j`;
* `pos_eq_mart_add_drift` and `markHit_excited_drift_le` — the same statement as accumulated
  rightward drift: the displacement of `j` minus its drift martingale is at least
  `(2p-1) * #(marked hits)`.

Everything is proved; see `ConcreteMarkAudit.lean` for the axiom audit.
-/
import Swarm.Marks

namespace Swarming.Marks

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped BigOperators

variable {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N}

/-- Walker `j` at time `t` sits on a site that is marked for walker `i` and strictly below `i`'s
running maximum. -/
def MarkHit (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) (t : ℕ) : Prop :=
  SiteMark p m U i ((trajectory p m U t).pos j) ∧
    ∃ s ≤ t, (trajectory p m U t).pos j < (trajectory p m U s).pos i

/-- The number of marked hits of walker `j` (with respect to walker `i`'s marks and running
maximum) up to and including time `n`. -/
noncomputable def markHitCount (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) (n : ℕ) : ℕ := by
  classical
  exact ∑ t ∈ Finset.range (n + 1), if MarkHit p m U i j t then 1 else 0

/-- **A marked hit is an excited step.** -/
theorem excited_of_markHit (hp : 1 / 2 ≤ p) {i j : Fin N} (hij : j ≠ i) {t : ℕ}
    (hx0 : 0 ≤ (trajectory p m U t).pos j) (h : MarkHit p m U i j t) :
    Excited m (trajectory p m U t).ell j ((trajectory p m U t).pos j) :=
  excited_of_mark hp hij hx0 h.1 h.2

/-- **Display `(dominate)`, sharp form**: at a marked hit the right-jump probability of walker
`j` is exactly `p`, so the jump dominates the jump with right probability `p`. -/
theorem rightProbability_eq_p_of_markHit (hp : 1 / 2 ≤ p) {i j : Fin N} (hij : j ≠ i) {t : ℕ}
    (hx0 : 0 ≤ (trajectory p m U t).pos j) (h : MarkHit p m U i j t) :
    rightProbability p m (trajectory p m U t).ell j ((trajectory p m U t).pos j) = p := by
  have hex := excited_of_markHit hp hij hx0 h
  simp only [rightProbability, hex, if_true]

/-- The excitation indicator `currentExcited` is `1` exactly at excited steps. -/
lemma currentExcited_eq_one_iff {t : ℕ} {j : Fin N} :
    currentExcited m (U := U) (p := p) t j = 1 ↔
      Excited m (trajectory p m U t).ell j ((trajectory p m U t).pos j) := by
  unfold currentExcited
  by_cases h : Excited m (trajectory p m U t).ell j ((trajectory p m U t).pos j)
  · simp [h]
  · simp [h]

/-- **The counting step of Proposition `ball`.**  If walker `j` never visits a negative site up
to time `n` (the paper's "nonnegative marked site" restriction), then its marked hits are
excited steps, so the number of marked hits is at most the number of excited steps. -/
theorem markHitCount_le_excitedSteps (hp : 1 / 2 ≤ p) {i j : Fin N} (hij : j ≠ i) {n : ℕ}
    (hpos : ∀ t, t ≤ n → 0 ≤ (trajectory p m U t).pos j) :
    markHitCount p m U i j n ≤ excitedSteps p m U (n + 1) j := by
  classical
  unfold markHitCount excitedSteps
  refine Finset.sum_le_sum fun t ht => ?_
  have htn : t ≤ n := by simpa using Finset.mem_range.mp ht
  by_cases h : MarkHit p m U i j t
  · have hex := excited_of_markHit hp hij (hpos t htn) h
    rw [if_pos h, (currentExcited_eq_one_iff (U := U) (p := p) (t := t) (j := j)).mpr hex]
  · rw [if_neg h]
    exact Nat.zero_le _

/-- The drift-martingale decomposition, in the form used by the occupation estimate. -/
theorem pos_eq_mart_add_drift (n : ℕ) (j : Fin N) :
    ((trajectory p m U n).pos j : ℝ)
      = driftMartingale p m U n j + (2 * p - 1) * (excitedSteps p m U n j : ℝ) := by
  unfold driftMartingale
  ring

/-- **Accumulated excited drift dominates the marked hits**: the displacement of walker `j` up to
time `n` exceeds its drift martingale by at least `(2p-1)` times the number of marked hits. -/
theorem markHit_excited_drift_le (hp : 1 / 2 ≤ p) {i j : Fin N} (hij : j ≠ i) {n : ℕ}
    (hpos : ∀ t, t ≤ n → 0 ≤ (trajectory p m U t).pos j) :
    (2 * p - 1) * (markHitCount p m U i j n : ℝ)
      ≤ ((trajectory p m U (n + 1)).pos j : ℝ) - driftMartingale p m U (n + 1) j := by
  have hcoef : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hcnt : (markHitCount p m U i j n : ℝ)
      ≤ (excitedSteps p m U (n + 1) j : ℝ) := by
    exact_mod_cast markHitCount_le_excitedSteps hp hij hpos (n := n) (U := U) (m := m)
  rw [pos_eq_mart_add_drift (n := n + 1) (j := j)]
  nlinarith

end Swarming.Marks


