/-
  **One-step conditional drift with a revealed random environment.**

  The paper's eq. (dominate) is stated for the *revealed* weights `ω_j(x)`, which are
  `ℱ_s`-measurable on `{b0 < X_s <= b1}` by (reveal).  The mechanism that lets the drift
  computation survive an `ω`-dependent weight is that a `ℱ_s`-measurable weight vector is in
  particular `ℱ_n`-measurable for every `n ≥ s`, hence can be pulled out of `μ[· | ℱ_n]`
  site by site.  This is what `condExp_scD_step` below does: it is the random-environment
  replacement of `SwarmSpeed.condExp_sc_step_int` (which is restricted to a fixed
  deterministic weight sequence).
-/
import Swarm.Imports
import Swarm.StoppedCross
import Swarm.Diag

open MeasureTheory Filter
open scoped Topology BigOperators

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}

/-! ### Clamped drift increments -/

/-- The clamped increment `f(z+1) - f(z-1)` at the (random) level `g ω`, with the level
operated on inside the clamp so that measurability is global. -/
noncomputable def deltaD (wf : Ω → ℕ → ℝ) (b0 b1 : ℕ) (g : Ω → ℕ) : Ω → ℝ :=
  fun ω => if g ω ≤ b1 then scDiag wf b0 b1 (fun ω' => g ω' + 1) ω
    - scDiag wf b0 b1 (fun ω' => g ω' - 1) ω else 0

/-- The clamped correction `f(z-1) - f(z)` at the (random) level `g ω`. -/
noncomputable def backD (wf : Ω → ℕ → ℝ) (b0 b1 : ℕ) (g : Ω → ℕ) : Ω → ℝ :=
  fun ω => if 1 ≤ g ω then scDiag wf b0 b1 (fun ω' => g ω' - 1) ω
    - scDiag wf b0 b1 g ω else 0

variable {m : MeasurableSpace Ω}

lemma measurable_deltaD (hw : ∀ x, Measurable[m] (fun ω => wf ω x))
    (hg : Measurable[m] g) :
    Measurable[m] (deltaD wf b0 b1 g) := by
  unfold deltaD
  refine Measurable.ite (measurableSet_le hg measurable_const) ?_ measurable_const
  exact (measurable_scDiag hw (hg.add measurable_const)).sub
    (measurable_scDiag hw (hg.sub measurable_const))

lemma measurable_backD (hw : ∀ x, Measurable[m] (fun ω => wf ω x))
    (hg : Measurable[m] g) :
    Measurable[m] (backD wf b0 b1 g) := by
  unfold backD
  refine Measurable.ite (measurableSet_le measurable_const hg) ?_ measurable_const
  exact (measurable_scDiag hw (hg.sub measurable_const)).sub (measurable_scDiag hw hg)

/-- `deltaD` is *exactly* the paper's increment at the current state. -/
lemma deltaD_eq_scaleDelta (wf : Ω → ℕ → ℝ) (n : ℕ) :
    deltaD wf b0 b1 (fun ω => X n ω) = fun ω => scaleDelta (wf ω) b0 b1 X n ω := by
  funext ω
  unfold deltaD scaleDelta
  by_cases h : X n ω ≤ b1
  · rw [if_pos h, if_pos h,
      scDiag_apply (wf := wf) (g := fun ω' => X n ω' + 1) (ω := ω) (by show X n ω + 1 ≤ b1 + 1; omega),
      scDiag_apply (wf := wf) (g := fun ω' => X n ω' - 1) (ω := ω) (by show X n ω - 1 ≤ b1 + 1; omega)]
  · rw [if_neg h, if_neg h]

/-- `backD` is the paper's correction at the current state, on the window. -/
lemma backD_apply {n : ℕ} {ω : Ω} (hω : X n ω ≤ b1 + 1) :
    backD wf b0 b1 (fun ω => X n ω) ω = scaleBack (wf ω) b0 b1 X n ω := by
  unfold backD scaleBack
  by_cases h : 1 ≤ X n ω
  · rw [if_pos h, if_pos h,
      scDiag_apply (wf := wf) (g := fun ω' => X n ω' - 1) (ω := ω) (by show X n ω - 1 ≤ b1 + 1; omega),
      scDiag_apply (wf := wf) (g := fun ω => X n ω) (ω := ω) hω]
  · rw [if_neg h, if_neg h]

end SwarmSpeed
