/-
  **Direction B (m2): the actual one-step Poisson drift, part 1.**

  The paper's `(Zdrift)`/`(Zloss)` of *Swarming of interacting excited random walks* computes

      E[H_{j,n+1}(X_{n+1}^i) - H_{j,n}(X_n^i) | F_n],
      H_{j,n}(x) = E[H_j(x) | F_n],   H_j = Hpot h_j.

  This file supplies the *deterministic* core and its `condExp` transport, with the actual
  trajectory `Swarming.Trajectory.trajectory`, the actual `arrayMeasure N`, the actual site marks
  `SwarmLogRatio.siteMarks` and the actual enlarged filtration `enlFilt p m n`:

  * `Hpot_succ_sub'`, `Hpot_pred_sub` — the exact increment of `SwarmOcc.Hpot` in terms of the
    integer-indexed step function `hZpot` (`hZpot h x = 1` for `x <= -1`, `= h x.toNat` otherwise):
        H(x+1) - H(x) = hZpot h x,      H(x-1) - H(x) = - hZpot h (x-1).
  * `Hpot_traj_sub` — along the actual trajectory,
        H(X_{n+1}^i) - H(X_n^i) = 1{up} hZpot(X_n^i) - 1{down} hZpot(X_n^i - 1),
    the deterministic one-step Poisson increment split by jump direction.
  * `condExp_Hpot_traj_sub` — the same identity under `condExp (enlFilt p m n)`, obtained by
    `condExp_congr_ae` (so no integrability is needed for this form).
  * `condExp_Hpot_traj_split` — the additive form
        E[H(X_{n+1}^i) | F_n] = E[H(X_n^i) | F_n] + E[1{up} hZpot(X_n^i) | F_n]
                                              - E[1{down} hZpot(X_n^i - 1) | F_n],
    with the integrability of every term supplied (`integrable_hZpot_traj`), i.e. the paper's
    "evaluating the jump of walk i" step, before any adaptation is used.

  Nothing here assumes measurability of the environment `h_j`: the two jump-set conditional means
  are the *actual* objects, and the substitution of the revealed value below the record is a
  separate (later) statement.
-/
import Swarm.EnlDrift
import Swarm.Zdrift

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross
open SwarmCross

variable {N : ℕ}

/-! ### The integer-indexed step function of the potential -/

/-- The step function of `SwarmOcc.Hpot`: `h` on `x >= 0`, extended by the boundary value
`h(-1) = 1` below.  `Hpot h (x+1) - Hpot h x = hZpot h x` for *every* integer `x`. -/
noncomputable def hZpot (h : ℕ → ℝ) : ℤ → ℝ :=
  fun x => if x ≤ -1 then 1 else h x.toNat

lemma hZpot_of_nonpos {h : ℕ → ℝ} {x : ℤ} (hx : x ≤ -1) : hZpot h x = 1 := if_pos hx

lemma hZpot_of_nonneg {h : ℕ → ℝ} {x : ℤ} (hx : 0 ≤ x) : hZpot h x = h x.toNat :=
  if_neg (by omega)

/-- **The exact increment of `Hpot`**: `H(x+1) - H(x) = hZpot h x` on all of `ℤ`.  This is
`SwarmOcc.Hpot_succ_sub` with the two cases `x >= 0`, `x <= -1` merged. -/
theorem Hpot_succ_sub' {h : ℕ → ℝ} (x : ℤ) :
    SwarmOcc.Hpot h (x + 1) - SwarmOcc.Hpot h x = hZpot h x := by
  rw [SwarmOcc.Hpot_succ_sub]
  unfold hZpot
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_neg (by omega : ¬ x ≤ -1)]
  · rw [if_neg hx, if_pos (by omega : x ≤ -1)]

/-- The backward increment: `H(x-1) - H(x) = - hZpot h (x-1)`. -/
theorem Hpot_pred_sub {h : ℕ → ℝ} (x : ℤ) :
    SwarmOcc.Hpot h (x - 1) - SwarmOcc.Hpot h x = -hZpot h (x - 1) := by
  have h := Hpot_succ_sub' (h := h) (x - 1)
  rw [show x - 1 + 1 = x from by ring] at h
  linarith

/-! ### The increment along the actual trajectory -/

/-- **The one-step Poisson increment along the actual trajectory**, split by the direction of the
jump of walker `i`:
`H(X_{n+1}^i) - H(X_n^i) = 1{up} hZpot(X_n^i) - 1{down} hZpot(X_n^i - 1)`. -/
theorem Hpot_traj_sub {p : ℝ} {m n : ℕ} (h : ℕ → ℝ) (U : Array N) (i : Fin N) :
    SwarmOcc.Hpot h ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot h ((trajectory p m U n).pos i)
      = stepUpInd p m n i U * hZpot h ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot h ((trajectory p m U n).pos i - 1) := by
  by_cases hup : U ∈ stepUp p m n i
  · have hpos : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + 1 := hup
    have hdn : U ∉ stepDown p m n i := fun hd => not_stepUp_and_stepDown p m U n i ⟨hup, hd⟩
    rw [hpos, Hpot_succ_sub', stepUpInd, Set.indicator_of_mem hup,
      stepDownInd, Set.indicator_of_notMem hdn]
    ring
  · have hdn : U ∈ stepDown p m n i := (stepUp_or_stepDown p m U n i).resolve_left hup
    have hpos : (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1 := hdn
    rw [hpos, Hpot_pred_sub, stepUpInd, Set.indicator_of_notMem hup,
      stepDownInd, Set.indicator_of_mem hdn]
    ring

/-- Pointwise form of `Hpot_traj_sub` as an equality of functions. -/
theorem Hpot_traj_sub_fun {p : ℝ} {m n : ℕ} (h : ℕ → ℝ) (i : Fin N) :
    (fun U : Array N => SwarmOcc.Hpot h ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot h ((trajectory p m U n).pos i))
      = fun U => stepUpInd p m n i U * hZpot h ((trajectory p m U n).pos i)
        - stepDownInd p m n i U * hZpot h ((trajectory p m U n).pos i - 1) :=
  funext fun U => Hpot_traj_sub h U i

/-- **The conditional one-step increment.**  Under the actual enlarged filtration the same
identity holds, so the `condExp` of the potential increment is a `condExp` of the two jump-set
terms.  No integrability hypothesis is needed in this form. -/
theorem condExp_Hpot_traj_sub {p : ℝ} {m n : ℕ} (h : ℕ → ℝ) (i : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmOcc.Hpot h ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot h ((trajectory p m U n).pos i))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => stepUpInd p m n i U * hZpot h ((trajectory p m U n).pos i)
          - stepDownInd p m n i U * hZpot h ((trajectory p m U n).pos i - 1)) :=
  condExp_congr_ae (Filter.Eventually.of_forall fun U => Hpot_traj_sub h U i)

end Swarming.Enl


