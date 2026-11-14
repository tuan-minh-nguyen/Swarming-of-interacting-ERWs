/-
# Payoff: the `(diam)` statement with `HdefA` *and* transience discharged

`DiamAssemblyMain.ae_spread_div_tendsto_zero_of_transience` needs four inputs: the log-fourth `Q`
variance estimate `LogVarBound`, the positional comparison `HcompA`, the deficit estimate
`HdefA`, and a.e. transience of each walker.  `HdefA.lean` proves `HdefA`; this module adds the
verified actual transience `SwarmBad.ae_transience_actual` and concludes `(diam)`
(`spread_n / n → 0` a.s.) from exactly `LogVarBound` and `HcompA` alone, for `2 ≤ m`, `2 ≤ N`.

Nothing here is used by `HdefA.lean`: the deficit estimate does *not* consume transience or any
positive-lower-speed input.  This file is a convenience interface for the assembly.
-/
import Swarm.HdefA
import Swarm.FrozenBadTime

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssemblyHdefA

variable {N : ℕ}

/-- **`(diam)` from `LogVarBound` and `HcompA` alone** (for `2 ≤ m`, `2 ≤ N`).

`DiamAssembly.ae_spread_div_tendsto_zero_of_transience` needs `LogVarBound`, `HcompA`, `HdefA`
and the a.e. transience of every walker.  `HdefA` is `hdefA` above, and transience is
`SwarmBad.ae_transience_actual` (for each `i` pick any `j ≠ i`, which exists since `2 ≤ N`). -/
theorem ae_spread_div_tendsto_zero_of_logvar_hcomp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    {m N : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) [NeZero N] {C K : ℝ} (hK : 0 ≤ K)
    (hC : @DiamAssembly.LogVarBound N p m C) (hcomp : @DiamAssembly.HcompA N p m _ K) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (DiamAssembly.XA p m U) n : ℤ) : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
  have htr : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop := by
    intro i
    have h2 : 2 ≤ N := hN
    obtain ⟨j, hji⟩ : ∃ j : Fin N, i ≠ j := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin N)) ⊆ {i} := by
        intro k _
        simp only [Finset.mem_singleton]
        exact (hcon k).symm
      have hcard := Finset.card_le_card hsub
      have hN' : N ≤ 1 := by simpa using hcard
      omega
    exact SwarmBad.ae_transience_actual hp0 hp1 hm i j hji
  exact ae_spread_div_tendsto_zero_of_transience' hp0 hp1 m hK hC hcomp htr

end DiamAssemblyHdefA
