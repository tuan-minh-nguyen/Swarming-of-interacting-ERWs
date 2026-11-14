/-
# Downstream diameter assembly (direction 4): discharging `hpos` unconditionally

`DiamAssemblyMain.ae_spread_div_tendsto_zero_of_transience` reduces the eventual-nonnegativity
hypothesis of `(diam)` to the a.e. transience of the individual walkers.  That transience is an
accepted result of the campaign (`Swarm/FrozenBadTime.lean`,
`SwarmBad.ae_transience_actual`, for `2 <= m` and for a pair of *distinct* walkers).  Here the
"distinct walker" parameter is chosen for every index, which turns the per-pair statement into the
`∀ i`-uniform `∀ᶠ n, ∀ i, 0 ≤ X^i_n` that the leader-descent reduction needs.

Consequently the eventual-nonnegativity residual of `(diam)` is *not* a residual any more.
-/
import Swarm.DiamAssemblyReduction
import Swarm.FrozenBadTime

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssembly

variable {N : ℕ}

/-- For `N >= 2` every index has a distinct partner (used to instantiate the two-walker form of
`SwarmBad.ae_transience_actual`). -/
theorem exists_ne_fin (hN : 2 ≤ N) (i : Fin N) : ∃ j : Fin N, j ≠ i := by
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  by_cases h : i.val = 0
  · refine ⟨⟨1, h1⟩, ?_⟩
    intro hc
    have hv : (1 : ℕ) = i.val := congrArg Fin.val hc
    omega
  · refine ⟨⟨0, h0⟩, ?_⟩
    intro hc
    exact h (by rw [← hc])

/-- **Eventual nonnegativity of every walker, unconditionally** (for `2 <= m`, `2 <= N`). -/
theorem ae_hpos_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, 0 ≤ XA p m U i n := by
  refine hpos_of_ae_transience (fun i => ?_)
  obtain ⟨j, hji⟩ := exists_ne_fin hN i
  exact SwarmBad.ae_transience_actual (N := N) hp0 hp1 hm i j (fun h => hji h.symm)

/-- **`(diam)` with `hpos` discharged unconditionally.** -/
theorem ae_spread_div_tendsto_zero_actual {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) [Nonempty (Fin N)] {C K : ℝ} (hK : 0 ≤ K)
    (hC : LogVarBound (N := N) p m C) (hcomp : HcompA (N := N) p m K) (hdef : HdefA (N := N) p m) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) := by
  exact ae_spread_div_tendsto_zero_of_transience hp0 hp1 m hK hC hcomp hdef
    (fun i => by
      obtain ⟨j, hji⟩ := exists_ne_fin hN i
      exact SwarmBad.ae_transience_actual (N := N) hp0 hp1 hm i j (fun h => hji h.symm))

/-- **The headline reduction.**  For `2 <= m` and `2 <= N`, almost surely the spread of the `N`
actual walkers is `o(n)` as soon as the two explicit moment bounds `(Mpot)`, `(Mdiff)` and the two
explicit residuals `HcompA` (the `hcomp` positional comparison at the reset time) and `HdefA`
(the paper's `(prelim)`) hold.  Every other ingredient — `hgap`, the block-uniform telescoped
`(Wdrift)`, `(Qslln)`, the reset-time bookkeeping, `UnitStep`, the initial condition and `hpos` —
is proved. -/
theorem ae_diam_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) [Nonempty (Fin N)] {C₁ C₂ K : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hK : 0 ≤ K)
    (hPot : PotMomentBound (N := N) p m C₁) (hDiff : DiffMomentBound (N := N) p m C₂)
    (hcomp : HcompA (N := N) p m K) (hdef : HdefA (N := N) p m) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) :=
  ae_spread_div_tendsto_zero_of_potMoment hp0 hp1 m hC₁ hC₂ hK hPot hDiff hcomp hdef
    (ae_hpos_actual hp0 hp1 hm hN)

end DiamAssembly
