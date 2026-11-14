/-
# Downstream diameter assembly (direction 4): `(diam)` from the localised residuals

This is the assembly step: the deterministic nested-leader reduction
(`NestedLeader.spread_div_tendsto_zero_of_W`), instantiated at the *actual* array
`U ↦ (XA p m U : Fin N → ℕ → ℤ)` of the interacting excited random walk, with

* `hgap` **proved** (`gapAt_le_Wtot`, from `SepGroup.gap_le_WA`);
* `htel` **proved** from the paper's log-fourth variance estimate
  (`ae_htel_reset`, module `DiamAssemblyTelescope`);
* `UnitStep` and the zero initial condition **proved** (`unitStep_XA`, `zero_XA`);

and with the three residuals that are genuinely not supplied by the accepted material left as
explicitly typed hypotheses:

1. `LogVarBound` — the paper's log-fourth variance estimate for `Q^{A,A^c}` (uniform in the
   block, one `N`-independent constant).  Its two routes are `(Mpot) + (Mdiff)`
   (`QVarBound.Q_log_variance_of_potMoment`) and `(Mpot) + (Smom₄)`
   (`SwarmSiteDiff.Q_log_variance_of_static`).
2. `HcompA` — the positional comparison `hcomp` at the reset time.
3. `HdefA` — the paper's `(prelim)`, `deficit_t = o(t)`.

`HposA` (eventual nonnegativity) is *removed* by `hpos_of_ae_transience`, which needs only the
a.e. transience of each walker (available as `SwarmBad.ae_transience_actual` for `m >= 2`).
-/
import Swarm.DiamAssemblyTelescope

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssembly

variable {N : ℕ}

/-! ## 5. Eventual nonnegativity: `hpos`

The nested-leader reduction asks for `∀ᶠ n, ∀ i, 0 ≤ X^i_n`.  The transience results give, for
each *fixed* walker, convergence to `+∞`; the uniform-in-`i` statement is a finite intersection. -/

/-- **`hpos` from the a.e. transience of every walker.** -/
theorem hpos_of_ae_transience {p : ℝ} {m : ℕ}
    (htr : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, 0 ≤ XA p m U i n := by
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop :=
    MeasureTheory.ae_all_iff.mpr htr
  filter_upwards [hall] with U hU
  have h1 : ∀ i : Fin N, ∀ᶠ n : ℕ in atTop, 0 ≤ (trajectory p m U n).pos i := fun i => by
    filter_upwards [(tendsto_atTop.mp (hU i)) (0 : ℤ)] with n hn
    exact hn
  exact Filter.eventually_all.mpr h1

/-! ## 6. The two explicit stochastic residuals, at the actual array -/

/-- The paper's `hcomp` positional comparison at the reset time of a separated leading block. -/
def HcompA (p : ℝ) (m : ℕ) [Nonempty (Fin N)] (K : ℝ) : Prop :=
  ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
      NestedLeader.Leading (fun i => XA p m U i n) A →
      LeaderDescent.SepMax (XA p m U) A n →
      Wtot p m U (LeaderDescent.resetTime (XA p m U) A n) A ≤
        K * (((NestedLeader.blockSpread
                (fun i => XA p m U i (LeaderDescent.resetTime (XA p m U) A n)) A : ℤ) : ℝ)
            + ((NestedLeader.deficit (XA p m U) (LeaderDescent.resetTime (XA p m U) A n) : ℤ) : ℝ)
            + 2) + ε * (n : ℝ)

/-- The paper's `(prelim)`: the deficit `max_j (M_t^j - X_t^j)` is `o(t)`. -/
def HdefA (p : ℝ) (m : ℕ) [Nonempty (Fin N)] : Prop :=
  ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
    ((NestedLeader.deficit (XA p m U) t : ℤ) : ℝ) ≤ ε * (t : ℝ)

/-! ## 7. `(diam)` at the actual array -/

/-- **`(diam)` for the actual interacting walk, from the three localised residuals.**

Almost surely the spread of the `N` positions is `o(n)`:
`(max_i X_n^i - min_i X_n^i) / n → 0`.

Every ingredient other than `LogVarBound`, `HcompA` and `HdefA` is proved in this file or in the
accepted modules it imports. -/
theorem ae_spread_div_tendsto_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    [Nonempty (Fin N)] {C K : ℝ} (hK : 0 ≤ K) (hC : LogVarBound (N := N) p m C)
    (hcomp : HcompA (N := N) p m K) (hdef : HdefA (N := N) p m)
    (hpos : ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, 0 ≤ XA p m U i n) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) := by
  filter_upwards [ae_htel_reset hp0 hp1 m hC, hcomp, hdef, hpos] with U htel hcompU hdefU hposU
  refine NestedLeader.spread_div_tendsto_zero_of_W (X := XA p m U) hK
    (fun A n => Wtot p m U n A) ?_ ?_ hcompU (unitStep_XA p m U) (zero_XA p m U) hdefU hposU
  · intro ε hε
    filter_upwards with n A hA hAc hlead hsep
    have h := gapAt_le_Wtot (le_of_lt hp0) (le_of_lt hp1) m U n hsep
    have hεn : 0 ≤ ε * (n : ℝ) := mul_nonneg (le_of_lt hε) (Nat.cast_nonneg n)
    linarith
  · intro ε hε
    filter_upwards [htel ε hε] with n hn A hA hAc hlead hsep
    exact hn A hA hAc hlead hsep

/-- **`(diam)` with `hpos` discharged by transience.**  Same statement, with the eventual
nonnegativity hypothesis replaced by the a.e. transience of the individual walkers. -/
theorem ae_spread_div_tendsto_zero_of_transience {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) [Nonempty (Fin N)] {C K : ℝ} (hK : 0 ≤ K) (hC : LogVarBound (N := N) p m C)
    (hcomp : HcompA (N := N) p m K) (hdef : HdefA (N := N) p m)
    (htr : ∀ i : Fin N, ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => (trajectory p m U n).pos i) atTop atTop) :
    ∀ᵐ U ∂(arrayMeasure N),
      Tendsto (fun n => ((LeaderDescent.spreadZ (XA p m U) n : ℤ) : ℝ) / (n : ℝ)) atTop
        (𝓝 0) :=
  ae_spread_div_tendsto_zero hp0 hp1 m hK hC hcomp hdef (hpos_of_ae_transience htr)

end DiamAssembly
