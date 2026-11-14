/-
  **Random (revealed) environment crossing estimate, conditional on the past.**

  Infrastructure: measurable presentation of the paper's scale function `f = sc`
  for an `Ω`-dependent weight family `wf : Ω → ℕ → ℝ` (the revealed environment
  `ω_j`), so that `ω ↦ sc (wf ω) b0 b1 (X n ω)` is `ℱ n`-measurable and can be
  *pulled out* of the conditional expectation `μ[· | ℱ n]`.

  Nothing here assumes the weights are deterministic; only that each coordinate
  map `ω ↦ wf ω x` is measurable with respect to the σ-algebra of the reveal time.
-/
import Swarm.Imports
import Swarm.StoppedCross

open MeasureTheory Filter
open scoped Topology BigOperators

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ### Measurability of the scale function in a random weight family -/

section Diag

variable {m : MeasurableSpace Ω} {wf : Ω → ℕ → ℝ}

/-- Each ratio `r(x) = (1-w(x))/w(x)` is measurable in the weight family. -/
lemma measurable_rat_diag (hw : ∀ x, Measurable[m] (fun ω => wf ω x)) (x : ℕ) :
    Measurable[m] (fun ω => rat (wf ω) x) := by
  unfold rat
  exact (measurable_const.sub (hw x)).div (hw x)

/-- The potential `R(y) = ∏_{x=b0+1}^{y} r(x)` is measurable in the weight family. -/
lemma measurable_R_diag (hw : ∀ x, Measurable[m] (fun ω => wf ω x)) (b0 y : ℕ) :
    Measurable[m] (fun ω => R (wf ω) b0 y) := by
  unfold R
  exact Finset.measurable_prod _ (fun x _ => measurable_rat_diag hw x)

/-- The normaliser `Z = ∑_{y=b0}^{b1} R(y)` is measurable in the weight family. -/
lemma measurable_Z_diag (hw : ∀ x, Measurable[m] (fun ω => wf ω x)) (b0 b1 : ℕ) :
    Measurable[m] (fun ω => Z (wf ω) b0 b1) := by
  unfold Z
  exact Finset.measurable_sum _ (fun y _ => measurable_R_diag hw b0 y)

end Diag

/-- The numerator `sum_{y=b0}^{z-1} R(y)` of the scale function, written as a sum over the
*fixed* window `Ico b0 (b1+1)` with a comparison against the (variable) level `g ω`.  This
clamped form is measurable as a function of `ω` and agrees with `num (wf ω) b0 (g ω)` as soon
as `g ω ≤ b1 + 1`. -/
noncomputable def scNumDiag (wf : Ω → ℕ → ℝ) (b0 b1 : ℕ) (g : Ω → ℕ) : Ω → ℝ :=
  fun ω => ∑ y ∈ Finset.Ico b0 (b1 + 1), if y < g ω then R (wf ω) b0 y else 0

/-- The clamped scale function `f(g ω)`, as a measurable function of `ω`. -/
noncomputable def scDiag (wf : Ω → ℕ → ℝ) (b0 b1 : ℕ) (g : Ω → ℕ) : Ω → ℝ :=
  fun ω => scNumDiag wf b0 b1 g ω / Z (wf ω) b0 b1

variable {wf : Ω → ℕ → ℝ} {m : MeasurableSpace Ω} {b0 b1 : ℕ} {g : Ω → ℕ}

lemma measurable_scNumDiag (hw : ∀ x, Measurable[m] (fun ω => wf ω x))
    (hg : Measurable[m] g) :
    Measurable[m] (scNumDiag wf b0 b1 g) := by
  unfold scNumDiag
  refine Finset.measurable_sum _ (fun y _ => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const hg) (measurable_R_diag hw b0 y)
    measurable_const

lemma measurable_scDiag (hw : ∀ x, Measurable[m] (fun ω => wf ω x))
    (hg : Measurable[m] g) :
    Measurable[m] (scDiag wf b0 b1 g) := by
  unfold scDiag
  exact (measurable_scNumDiag hw hg).div (measurable_Z_diag hw b0 b1)

/-- The clamped representation of the numerator. -/
lemma num_eq_sum_window {v : ℕ → ℝ} {z : ℕ} (hz : z ≤ b1 + 1) :
    num v b0 z = ∑ y ∈ Finset.Ico b0 (b1 + 1), if y < z then R v b0 y else 0 := by
  rw [← Finset.sum_filter]
  have h : (Finset.Ico b0 (b1 + 1)).filter (fun y => y < z) = Finset.Ico b0 z := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [h]
  rfl

/-- `sc` agrees with its clamped measurable presentation on the window. -/
lemma scDiag_apply {ω : Ω} (h : g ω ≤ b1 + 1) :
    scDiag wf b0 b1 g ω = sc (wf ω) b0 b1 (g ω) := by
  have h1 : scNumDiag wf b0 b1 g ω = num (wf ω) b0 (g ω) :=
    (num_eq_sum_window (b0 := b0) (b1 := b1) (v := wf ω) (z := g ω) h).symm
  unfold scDiag sc
  rw [h1]

end SwarmSpeed
