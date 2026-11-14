/-
# `Swarm.Sandwich` is the source's regeneration structure, not an extra hypothesis

The assembly (`Swarm/Assembly.lean`) takes the paper's sandwich inequality
`z_k <= X_n^i < z_{k+1}` for `sigma_k <= n < sigma_{k+1}` as a hypothesis `Swarm.Sandwich`.
Reading the whole tree, `Sandwich` is *never produced*: every file uses it as an input
(`ae_tendsto_of_regen`, `DelayedRegen`, `NonnegDuration`, `Fidelity.paper_sandwich`, ...).

This file produces it.  The source defines, in §3.2,

* `tau_r` a simultaneous record time if `X_{tau_r}^i = r` for every `i`,
* a regeneration time if in addition `X_n^i > r` for every `i` and every `n > tau_r`,
* the regeneration level `r`, and then `D`/`T` are the successive differences of the
  regeneration levels and times.

The two clauses that make the sandwich inequality true are therefore pure path statements:

* `hlevel`     : at a regeneration time every walker is exactly on the level;
* `hnoReturn`  : after a regeneration time (`k >= 1`) no walker returns to or below the level;
* `hfirst`     : `sigma (k+1)` is the first time any walker reaches `z (k+1)`.

`M6Star.sandwich_of_regenSequence` derives the abstract `Swarm.Sandwich` interface from them
(for the increments `D k = z (k+1) - z k`, `T k = sigma (k+1) - sigma k`), and
`M6Star.Sandwich_of_regenSequence` packages it as a `Swarm.Sandwich` statement.  So the
regeneration input of the assembly reduces to the source's own definitions plus three path
clauses — no additional stochastic content is hidden in `Sandwich`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/
import Swarm.Assembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace M6Star

/-- Block sums of successive differences telescope for a monotone integer sequence. -/
lemma blockSum_diff {u : ℕ → ℕ} (hu : Monotone u) (k : ℕ) :
    Swarm.blockSum (fun j => u (j + 1) - u j) k = u k - u 0 := by
  induction k with
  | zero => simp [Swarm.blockSum]
  | succ k ih =>
    have h1 : u 0 ≤ u k := hu (Nat.zero_le k)
    have h2 : u k ≤ u (k + 1) := hu (Nat.le_succ k)
    have hstep : Swarm.blockSum (fun j => u (j + 1) - u j) (k + 1)
        = Swarm.blockSum (fun j => u (j + 1) - u j) k + (u (k + 1) - u k) := by
      simp [Swarm.blockSum, Finset.sum_range_succ]
    rw [hstep, ih]
    omega

/-- **The assembly's `Sandwich` interface from the source's regeneration times and levels.**

`sigma k` are the regeneration times, `z k` the regeneration levels of the path `x`, and the
three clauses are exactly the content of the source's definitions: the level is attained at
the regeneration time, is never reached again from above after it, and is first reached at
`sigma (k+1)`.  The conclusion is the assembly's pointwise sandwich structure for the
increments `D k = z (k+1) - z k` and `T k = sigma (k+1) - sigma k`. -/
theorem sandwich_of_regenSequence {N : ℕ} {x : ℕ → Fin N → ℤ} {σ z : ℕ → ℕ}
    (hσ0 : σ 0 = 0) (hz0 : z 0 = 0) (hσmono : Monotone σ) (hzmono : Monotone z)
    (hlevel : ∀ k i, x (σ k) i = (z k : ℤ))
    (hnoReturn : ∀ k, 1 ≤ k → ∀ n, σ k < n → ∀ i, (z k : ℤ) < x n i)
    (hfirst : ∀ k n i, n < σ (k + 1) → x n i < (z (k + 1) : ℤ)) :
    ∀ (i : Fin N) (k n : ℕ),
      ((1 ≤ k → Swarm.blockSum (fun j => σ (j + 1) - σ j) k ≤ n →
          (Swarm.blockSum (fun j => z (j + 1) - z j) k : ℤ) ≤ x n i) ∧
       ((Swarm.blockSum (fun j => z (j + 1) - z j) (k + 1) : ℤ) ≤ x n i →
          Swarm.blockSum (fun j => σ (j + 1) - σ j) (k + 1) ≤ n)) := by
  have hσ : ∀ k, Swarm.blockSum (fun j => σ (j + 1) - σ j) k = σ k := by
    intro k
    rw [blockSum_diff hσmono k, hσ0, Nat.sub_zero]
  have hz : ∀ k, Swarm.blockSum (fun j => z (j + 1) - z j) k = z k := by
    intro k
    rw [blockSum_diff hzmono k, hz0, Nat.sub_zero]
  intro i k n
  constructor
  · intro hk hn
    rw [hσ] at hn
    rw [hz]
    rcases lt_or_eq_of_le hn with hlt | heq
    · exact le_of_lt (hnoReturn k hk n hlt i)
    · rw [← heq, hlevel k i]
  · intro hge
    rw [hz] at hge
    rw [hσ]
    exact Nat.le_of_not_lt fun hcon => absurd hge (not_le.mpr (hfirst k n i hcon))

/-- **`Swarm.Sandwich` is a theorem, not an assumption**, once the increments are the
successive differences of the source's regeneration times and levels. -/
theorem Sandwich_of_regenSequence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (x : ℕ → Fin N → ℤ) {σ z : ℕ → ℕ}
    (hσ0 : σ 0 = 0) (hz0 : z 0 = 0) (hσmono : Monotone σ) (hzmono : Monotone z)
    (hlevel : ∀ k i, x (σ k) i = (z k : ℤ))
    (hnoReturn : ∀ k, 1 ≤ k → ∀ n, σ k < n → ∀ i, (z k : ℤ) < x n i)
    (hfirst : ∀ k n i, n < σ (k + 1) → x n i < (z (k + 1) : ℤ)) :
    Swarm.Sandwich μ (fun n (_ : Ω) => x n)
      (fun k (_ : Ω) => z (k + 1) - z k) (fun k (_ : Ω) => σ (k + 1) - σ k) :=
  Filter.Eventually.of_forall fun _ =>
    sandwich_of_regenSequence hσ0 hz0 hσmono hzmono hlevel hnoReturn hfirst

end M6Star


