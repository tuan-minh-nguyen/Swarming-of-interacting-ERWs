/-
  **Multi-step conditional force from an arbitrary enlarged-filtration past event.**

  `Swarm/GammaBase.lean` supplies two separate facts on the actual i.i.d.-uniform array:

  * `patternA_set_ge` : one step, against an arbitrary `enlMeas p m n` past set `G`,
      `ofReal (1-p)^{|A|} * mu G <= mu (G inter patSetA p m n A eps)`;
  * `evPrefix_mass_ge` : `k` steps, but the past piece is required to lie in
      `cylAt (prefRead n gamma)`, i.e. it must already be pinned to a single prefix `gamma`.

  Neither covers the case that arises when one prescribes a *word* of `k` unit jumps and
  wants the bound against an *arbitrary* enlarged-filtration past event.

  This file supplies that bridge.  For every `G` with `MeasurableSet[enlMeas p m n] G`,
  every `k` and every prescribed `+-1` word for the group `A`,

      ofReal (1-p)^{k*|A|} * arrayMeasure N G
        <= arrayMeasure N (G inter evWord p m n A eps k),

  where `evWord` is the plain event "the walkers of `A` follow the word for `k` steps",
  with no reference to the prefix at time `n`.  The prescribed word event is *memoryless*:
  `evWord (k+1) = evWord k inter patSetA (n+k) (eps k)`, which is what makes the induction
  clear of all prefix bookkeeping.

  Scope: this is a generic enlarged-filtration statement about the actual array measure.
  It contains no raw attempt tower, no `RegenAtStrict`, no `recTimeA`, no nullity, no
  invariant law, and no regeneration claim.
-/
import Swarm.GammaBase

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- The event that, starting from time `n`, the walkers of `A` follow the prescribed unit
word `ε` for `k` steps, with no condition on the prefix at time `n`. -/
noncomputable def evWord (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ)
    (k : ℕ) : Set (Array N) :=
  ⋃ γ : Pref N n, evPrefix m n γ A ε p k

/-- The prescribed word event is memoryless: the `(k+1)`-st step is appended to the
`k`-step event and does not depend on the prefix. -/
theorem evWord_succ (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) (k : ℕ) :
    evWord p m n A ε (k + 1) = evWord p m n A ε k ∩ patSetA p m (n + k) A (ε k) := by
  rw [evWord, evWord]
  rw [show (⋃ γ : Pref N n, evPrefix m n γ A ε p (k + 1))
      = ⋃ γ : Pref N n,
          (evPrefix m n γ A ε p k ∩ patSetA p m (n + k) A (ε k)) from rfl]
  rw [Set.iUnion_inter]

/-- At `k = 0` the word event is everything. -/
theorem evWord_zero (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) :
    evWord p m n A ε 0 = Set.univ := by
  refine Set.eq_univ_iff_forall.2 fun U => ?_
  exact Set.mem_iUnion.2 ⟨prefOf p m n U, prefAgree_prefOf U⟩

/-- The word event is measurable for the enlarged filtration at the end of the word. -/
theorem measurableSet_evWord_enl (p : ℝ) (m n : ℕ) (A : Finset (Fin N))
    (ε : ℕ → Fin N → ℤ) (k : ℕ) :
    MeasurableSet[enlMeas p m (n + k)] (evWord p m n A ε k) := by
  rw [evWord]
  refine MeasurableSet.iUnion fun γ : Pref N n => ?_
  have h := measurableSet_enlMeas_of_pathDet_cyl (N := N) p m
    (n₀ := n) (n₁ := n + k) (le_add_right le_rfl) (γ := γ)
    (B := Set.univ) (by exact MeasurableSet.univ)
    (evPrefix_pathDet p m n γ A ε k) (evPrefix_subset_prefAgree p m n γ A ε k)
  simpa using h

/-- Monotonicity of the enlarged filtration in the step count. -/
theorem enlMeas_le_add (N : ℕ) (p : ℝ) (m n : ℕ) :
    ∀ k : ℕ, enlMeas (N := N) p m n ≤ enlMeas p m (n + k)
  | 0 => by simp
  | (k + 1) => by
      have h1 : enlMeas (N := N) p m n ≤ enlMeas p m (n + k) := enlMeas_le_add N p m n k
      have h2 : enlMeas (N := N) p m (n + k) ≤ enlMeas p m (n + k + 1) :=
        enlMeas_mono (N := N) p m
      have h3 : n + k + 1 = n + (k + 1) := by ring
      rw [h3] at h2
      exact h1.trans h2

/-- **Multi-step conditional force from an arbitrary enlarged-filtration past event.** -/
theorem evWord_mass_ge (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m n : ℕ)
    (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) (k : ℕ) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ evWord p m n A ε k) := by
  induction k with
  | zero =>
      rw [evWord_zero, Set.inter_univ]
      simpa using le_rfl (a := arrayMeasure N G)
  | succ k ih =>
      have hmono := enlMeas_le_add N p m n k
      have hG' : MeasurableSet[enlMeas p m (n + k)] G := hmono G hG
      have hGk : MeasurableSet[enlMeas p m (n + k)] (G ∩ evWord p m n A ε k) :=
        hG'.inter (measurableSet_evWord_enl p m n A ε k)
      have hstep := patternA_set_ge (N := N) p hp0 hp1 (m := m) (n := n + k) A (ε k)
        (fun i _ => hε k i) (G := G ∩ evWord p m n A ε k) hGk
      have hEq : (G ∩ evWord p m n A ε k) ∩ patSetA p m (n + k) A (ε k)
          = G ∩ evWord p m n A ε (k + 1) := by
        rw [evWord_succ]
        exact Set.inter_assoc G _ _
      rw [hEq] at hstep
      calc ENNReal.ofReal (1 - p) ^ ((k + 1) * A.card) * arrayMeasure N G
          = ENNReal.ofReal (1 - p) ^ A.card *
              (ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N G) := by
            rw [← mul_assoc, ← pow_add]
            congr 1
            ring
        _ ≤ ENNReal.ofReal (1 - p) ^ A.card *
              arrayMeasure N (G ∩ evWord p m n A ε k) := mul_le_mul' le_rfl ih
        _ ≤ arrayMeasure N (G ∩ evWord p m n A ε (k + 1)) := hstep

/-- Consistency with the one-step object: the one-step word event is exactly `patSetA`. -/
theorem evWord_one (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) :
    evWord p m n A ε 1 = patSetA p m n A (ε 0) := by
  have h := evWord_succ p m n A ε 0
  rw [h, evWord_zero, Set.univ_inter]
  norm_num

/-- The whole-swarm instance: with `A = univ` the exponent is `k * N`. -/
theorem evWord_mass_ge_univ (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m n : ℕ)
    (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) (k : ℕ) :
    ENNReal.ofReal (1 - p) ^ (k * N) * arrayMeasure N G ≤
      arrayMeasure N (G ∩ evWord p m n (Finset.univ : Finset (Fin N)) ε k) := by
  have h := evWord_mass_ge (N := N) p hp0 hp1 m n (Finset.univ : Finset (Fin N)) ε hε hG k
  simpa using h

/-- The same bound with the intersection written the other way round. -/
theorem evWord_mass_ge_comp (p : ℝ) (hp0 : (1 : ℝ) / 2 ≤ p) (hp1 : p < 1) (m n k : ℕ)
    (A : Finset (Fin N)) (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) :
    ENNReal.ofReal (1 - p) ^ (k * A.card) * arrayMeasure N G ≤
      arrayMeasure N (evWord p m n A ε k ∩ G) := by
  rw [Set.inter_comm]
  exact evWord_mass_ge p hp0 hp1 m n A ε hε hG k

end Swarming.Enl


