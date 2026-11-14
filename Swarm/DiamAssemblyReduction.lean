/-
# Downstream diameter assembly (direction 4): discharging the log-fourth variance input

`DiamAssemblyMain.ae_spread_div_tendsto_zero` consumes the paper's log-fourth variance estimate for
the separated-group martingale `Q^{A,A^c}` as the explicitly typed hypothesis `LogVarBound`.  This
module shows that `LogVarBound` follows from the two moment bounds on the *actual* array that the
campaign already reduced `(hcomp)`/`(maxmom)` to:

* `(Mpot)` — the second moment of the static window potential `PotMax^{A}`,
* `(Mdiff)` — the second moment of the group-weight update cost `siteDiff^{A,A^c}`,

via the integrated theorem `SwarmQVariance.Q_log_variance_of_potMoment`.  Both are stated here
uniformly over the leading block, with a single `N`-independent constant, which is exactly what
`LogVarBound` needs.

It also derives the *whole* nested-leader drift residual `NestedLeader.DriftInput` for the actual
array from the single remaining positional-comparison hypothesis `HcompA`.
-/
import Swarm.DiamAssemblyMain
import Swarm.QVarBound

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssembly

variable {N : ℕ}

/-! ## 8. `(Mpot)` + `(Mdiff)` imply `LogVarBound` -/

/-- `(Mpot)`, uniformly over the leading block.  For `p > 1/2` this is *proved* unconditionally
(the accepted `MpotMain.hPot_actual'`); it is kept as a hypothesis here only because that module is
not part of the integrated build this file is verified against. -/
def PotMomentBound (p : ℝ) (m : ℕ) (C₁ : ℝ) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (k : ℕ),
    ∫ U, (SwarmQVariance.PotMax p m k A hA U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4

/-- `(Mdiff)`, uniformly over the leading block: the second moment of the one-step cost of the
group-weight update. -/
def DiffMomentBound (p : ℝ) (m : ℕ) (C₂ : ℝ) : Prop :=
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (k : ℕ),
    ∫ U, (SwarmQVariance.siteDiff p m k A Aᶜ hA U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4

/-- **The log-fourth variance estimate from the two moment bounds.** -/
theorem logVarBound_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : PotMomentBound (N := N) p m C₁) (hDiff : DiffMomentBound (N := N) p m C₂) :
    LogVarBound (N := N) p m (8 * C₁ + 2 * C₂) := by
  constructor
  · intro A hA hAc k
    exact (SwarmQVariance.Q_log_variance_of_potMoment hp0 hp1 m A Aᶜ hA hAc
      disjoint_compl_right hC₁ hC₂ (hPot A hA) (hDiff A hA)).1 k
  · intro A hA hAc k
    exact (SwarmQVariance.Q_log_variance_of_potMoment hp0 hp1 m A Aᶜ hA hAc
      disjoint_compl_right hC₁ hC₂ (hPot A hA) (hDiff A hA)).2 k

/-! ## 9. The whole nested-leader drift residual, from `HcompA` alone -/

/-- **`DriftInput` for the actual array.**  Almost surely the nested-leader drift residual
`NestedLeader.DriftInput (XA p m U) K` holds, with

* `hgap` proved (`gapAt_le_Wtot`),
* `htel` proved from `LogVarBound` (`ae_htel_reset`),
* `hpos` — required by `DriftInput_of_W` only through `NestedLeader.DriftInput_of_W`?  it is not
  needed here, and is not assumed,

and `HcompA` the only stochastic input. -/
theorem ae_driftInput {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    [Nonempty (Fin N)] {C K : ℝ} (hC : LogVarBound (N := N) p m C)
    (hcomp : HcompA (N := N) p m K) :
    ∀ᵐ U ∂(arrayMeasure N), NestedLeader.DriftInput (XA p m U) K := by
  filter_upwards [ae_htel_reset hp0 hp1 m hC, hcomp] with U htel hcompU
  refine NestedLeader.DriftInput_of_W (X := XA p m U) (K := K)
    (fun A n => Wtot p m U n A) ?_ ?_ hcompU
  · intro ε hε
    filter_upwards with n A hA hAc hlead hsep
    have h := gapAt_le_Wtot (le_of_lt hp0) (le_of_lt hp1) m U n hsep
    have hεn : 0 ≤ ε * (n : ℝ) := mul_nonneg (le_of_lt hε) (Nat.cast_nonneg n)
    linarith
  · intro ε hε
    filter_upwards [htel ε hε] with n hn A hA hAc hlead hsep
    exact hn A hA hAc hlead hsep

/-- **`(diam)` from `(Mpot)`, `(Mdiff)`, `hcomp` and `(prelim)`.** -/
theorem ae_spread_div_tendsto_zero_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) [Nonempty (Fin N)] {C₁ C₂ K : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hK : 0 ≤ K)
    (hPot : PotMomentBound (N := N) p m C₁) (hDiff : DiffMomentBound (N := N) p m C₂)
    (hcomp : HcompA (N := N) p m K) (hdef : HdefA (N := N) p m)
    (hpos : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, 0 ≤ XA p m U i n) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) :=
  ae_spread_div_tendsto_zero hp0 hp1 m hK
    (logVarBound_of_potMoment hp0 hp1 m hC₁ hC₂ hPot hDiff) hcomp hdef hpos

/-- **`DriftInput` from `(Mpot)` and `(Mdiff)`.** -/
theorem ae_driftInput_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    [Nonempty (Fin N)] {C₁ C₂ K : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : PotMomentBound (N := N) p m C₁) (hDiff : DiffMomentBound (N := N) p m C₂)
    (hcomp : HcompA (N := N) p m K) :
    ∀ᵐ U ∂(arrayMeasure N), NestedLeader.DriftInput (XA p m U) K :=
  ae_driftInput hp0 hp1 m (logVarBound_of_potMoment hp0 hp1 m hC₁ hC₂ hPot hDiff) hcomp

end DiamAssembly
