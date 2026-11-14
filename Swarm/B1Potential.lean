/-
  **`locsum`, layer B1: the full stationary potential as the monotone limit of the truncations.**

  `LocSum.Q_telescope` gives `Q (ℓ+m) x - Q ℓ x = Pz x ℓ * (1 + Q m (x-ℓ))`; with `Pz ≥ 0` this
  makes the truncations `k ↦ Q p k x` monotone in `k`, so the paper's potential
  `h^*(x) = 1 + 2 Σ_{q≥1} ∏_{u<q} ρ(x-u)` is the supremum of its truncations.  This file
  records the monotonicity and the sup (`hstarN`), and the cofinality of the subsequence
  `k = ℓ + m`, which is what the truncation comparison `h^* - h^*_ℓ = Pz(x,ℓ)(h^*(x-ℓ)-1)`
  is the limit of.  The comparison itself still needs the (a.e.) finiteness of `hstarN`, i.e.
  the pass to the limit in `Q_telescope`; that is *not* claimed here.
-/
import Swarm.A4Assembly

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

/-- The truncations of the stationary potential are monotone in the truncation depth. -/
lemma Q_monotone {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x : ℕ) (ω : ℕ → Bool) :
    Monotone (fun k => LocSum.Q p k x ω) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [LocSum.Q_succ']
  have := LocSum.Pz_nonneg hp1 hp2 x k ω
  linarith

/-- **The full stationary potential** at site `x` of a mark row, as the `ℝ≥0∞`-valued supremum
of its truncations. -/
def hstarN (p : ℝ) (x : ℕ) : (ℕ → Bool) → ℝ≥0∞ :=
  fun ω => ⨆ k, ENNReal.ofReal (LocSum.Q p k x ω)

lemma ofReal_Q_le_hstarN (p : ℝ) (x k : ℕ) (ω : ℕ → Bool) :
    ENNReal.ofReal (LocSum.Q p k x ω) ≤ hstarN p x ω :=
  le_iSup (fun k => ENNReal.ofReal (LocSum.Q p k x ω)) k

/-- `hstarN` is monotone in the truncation depth: the sup may be taken along `k = ℓ + m`. -/
lemma hstarN_shift {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x ℓ : ℕ) (ω : ℕ → Bool) :
    hstarN p x ω = ⨆ m, ENNReal.ofReal (LocSum.Q p (ℓ + m) x ω) := by
  have hmono := Q_monotone hp1 hp2 x ω
  apply le_antisymm
  · refine iSup_le fun k => ?_
    have h1 : LocSum.Q p k x ω ≤ LocSum.Q p (ℓ + k) x ω := hmono (Nat.le_add_left k ℓ)
    calc ENNReal.ofReal (LocSum.Q p k x ω) ≤ ENNReal.ofReal (LocSum.Q p (ℓ + k) x ω) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ ⨆ m, ENNReal.ofReal (LocSum.Q p (ℓ + m) x ω) :=
          le_iSup (fun m => ENNReal.ofReal (LocSum.Q p (ℓ + m) x ω)) k
  · refine iSup_le fun m => ?_
    exact le_iSup (fun k => ENNReal.ofReal (LocSum.Q p k x ω)) (ℓ + m)

end

end LocSumAct
