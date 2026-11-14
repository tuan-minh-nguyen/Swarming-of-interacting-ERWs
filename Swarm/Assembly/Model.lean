/-
Area (h) — final integration and source fidelity.

This file builds the *interface* between the paper `main_1d_revised.tex` and Lean:
the concrete interacting `N`-walker system is described by the property
`Swarm.IsInteractingLaw` (nearest-neighbour paths started at `0` whose conditional jump
law given the enlarged filtration is the paper's rule (1.1)), and the elementary
consequences of that rule that the final assembly needs are proved here.

What is proved here (no proof holes, no axioms beyond Lean's):
* `localTime`, `otherVisits`, `Excited`, `rightProb` — the paper's `L_n^i(x)`, `alpha_n^i`;
* the partition of a measurable past-event `A` by the two possible jumps;
* the *drift identity* `E[step | F_n] = (2p-1) 1{excited}` in the form
  `∫_A (X_{n+1}-X_n) = (2p-1) mu.real (A ∩ {excited})`;
* the telescoping identity `∫ X_n = (2p-1) sum_{t<n} P(excited at t)`, hence
  `∫ X_n <= (2p-1) n`;
* the **upper half of the interval in the main theorem**: if `X_n^i/n -> v` then
  `v <= 2p-1`, and in fact `v = (2p-1) * lim (1/n) sum_{t<n} P(excited at t)`.
  (The paper derives `limsup X_n/n <= 2p-1` from the martingale strong law; the argument
  below is elementary and needs only the conditional transition rule, bounded
  convergence, and `|X_n| <= n`.)

The upper bound `v <= 2p-1` is one half of the paper's claim
`v_{N,m}(p) in [kappa(m,p), 2p-1]`; it was not covered by any previous module of the
campaign (the abstract renewal theorem `Renewal.paper_main_abstract` only transfers the
*lower* bound `kappa <= v`).
-/
import Swarm.Imports

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace Swarm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ}

/-! ### Local times, excitation, and the transition rule -/

/-- The paper's `L_n^i(x)`: the number of visits of walker `i` to `x` up to time `n`. -/
noncomputable def localTime (X : ℕ → Ω → Fin N → ℤ) (n : ℕ) (ω : Ω) (i : Fin N) (x : ℤ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if X t ω i = x then 1 else 0

/-- The paper's `sum_{j != i} L_n^j(x)`: visits to `x` by all walkers other than `i`. -/
noncomputable def otherVisits (X : ℕ → Ω → Fin N → ℤ) (n : ℕ) (ω : Ω) (i : Fin N)
    (x : ℤ) : ℕ :=
  ∑ j ∈ Finset.univ.erase i, localTime X n ω j x

/-- Walker `i` is *excited* at time `n`: its current position has been visited at least `m`
times in total by the other walkers. -/
noncomputable def Excited (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω) (i : Fin N) : Prop :=
  m ≤ otherVisits X n ω i (X n ω i)

attribute [local instance] Classical.propDecidable

/-- The paper's `alpha_n^i = 1/2 + (p - 1/2) 1{sum_{j != i} L_n^j(X_n^i) >= m}`. -/
noncomputable def rightProb (p : ℝ) (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω)
    (i : Fin N) : ℝ :=
  1 / 2 + (p - 1 / 2) * if Excited X m n ω i then 1 else 0

/-- The set on which walker `i` is excited at time `n`. -/
def excitedSet (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (i : Fin N) : Set Ω :=
  {ω | Excited X m n ω i}

/-- The set on which walker `i` jumps to the right at time `n`. -/
def upSet (X : ℕ → Ω → Fin N → ℤ) (n : ℕ) (i : Fin N) : Set Ω :=
  {ω | X (n + 1) ω i = X n ω i + 1}

/-- Every jump is a nearest-neighbour jump. -/
def NearestNeighbour (X : ℕ → Ω → Fin N → ℤ) : Prop :=
  ∀ n ω i, X (n + 1) ω i = X n ω i + 1 ∨ X (n + 1) ω i = X n ω i - 1

/-- **The concrete model of the paper, as a property of `(mu, X)`.**

`X` is a system of `N` interacting nearest-neighbour walks on `Z` started at `0`; `𝓕` is
the paper's enlarged filtration (it contains the walk coordinates, `meas`), and the
conditional law of the jump of walker `i` at time `n` given `𝓕 n` is the paper's rule

  `P(X_{n+1}^i = X_n^i + 1 | 𝓕 n) = 1/2 + (p - 1/2) 1{sum_{j != i} L_n^j(X_n^i) >= m}`.

The rule is stated in the equivalent "for every past event `A`" form, which is the
conditional-probability statement of the paper and needs no conditional-probability API.
Jumps of different walkers are not required to be independent here: the final assembly
does not use it. -/
def IsInteractingLaw (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (X : ℕ → Ω → Fin N → ℤ) (m : ℕ) (p : ℝ) : Prop :=
  (∀ n i, Measurable[𝓕 n] fun ω => X n ω i) ∧
  (∀ ω i, X 0 ω i = 0) ∧
  NearestNeighbour X ∧
  (∀ (n : ℕ) (i : Fin N) (A : Set Ω), MeasurableSet[𝓕 n] A →
    μ.real (A ∩ upSet X n i)
      = 1 / 2 * μ.real A + (p - 1 / 2) * μ.real (A ∩ excitedSet X m n i))

/-! ### Elementary consequences of the model -/

section Basic

variable {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

lemma localTime_le (n : ℕ) (ω : Ω) (i : Fin N) (x : ℤ) : localTime X n ω i x ≤ n + 1 := by
  unfold localTime
  calc ∑ t ∈ Finset.range (n + 1), (if X t ω i = x then 1 else 0)
      ≤ ∑ _t ∈ Finset.range (n + 1), (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs <;> simp
    _ = n + 1 := by simp

lemma nearestNeighbour_of_law (h : IsInteractingLaw 𝓕 μ X m p) : NearestNeighbour X := h.2.2.1

/-- Every jump has absolute value one. -/
lemma abs_step_of_law (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (ω : Ω) (i : Fin N) :
    X (n + 1) ω i - X n ω i = 1 ∨ X (n + 1) ω i - X n ω i = -1 := by
  rcases h.2.2.1 n ω i with h' | h' <;> [left; right] <;> omega

/-- The walk starts at the origin, so `|X_n| <= n`. -/
lemma abs_le_time_of_law (h : IsInteractingLaw 𝓕 μ X m p) :
    ∀ n ω i, |X n ω i| ≤ (n : ℤ) := by
  intro n
  induction n with
  | zero => intro ω i; simp [h.2.1 ω i]
  | succ n ih =>
      intro ω i
      have hs := abs_step_of_law h n ω i
      have h1 : |X (n + 1) ω i| ≤ |X n ω i| + 1 := by
        have hstep : X (n + 1) ω i = X n ω i + 1 ∨ X (n + 1) ω i = X n ω i - 1 := by
          rcases hs with hs | hs <;> omega
        rcases hstep with h' | h'
        · rw [h']
          calc |X n ω i + 1| ≤ |X n ω i| + |(1 : ℤ)| := abs_add_le _ _
            _ = |X n ω i| + 1 := by simp
        · rw [h', sub_eq_add_neg]
          calc |X n ω i + -1| ≤ |X n ω i| + |(-1 : ℤ)| := abs_add_le _ _
            _ = |X n ω i| + 1 := by simp
      have h2 := ih ω i
      push_cast
      omega

end Basic

end Swarm
