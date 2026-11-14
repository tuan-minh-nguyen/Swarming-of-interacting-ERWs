/-
# `(locmart)` at the paper's local scale: the maximal two-sided deviation bound

The paper's Proposition `local`, display `(locmart)`, needs `|M^i_t - M^i_s| ≤ C_T L^{3/4}` on a
good event, for a drift martingale with bounded increments.  `areas/martingale/LOCMOVE.md`
records the two missing ingredients: a *conditional* Hoeffding lemma (Mathlib has only the
unconditional one) and the tower iteration giving a fixed-horizon mgf bound.

`CondHoeffding.lean` (the conditional Hoeffding lemma) and `Azuma.lean` (tower + maximal
Chernoff) supply those.  This file repairs their indexing and states the result in the paper's
own constants.

## Source correction (important)

`Azuma.lean` assumed, for the same `k`, `StronglyMeasurable[ℱ k] (ξ k)` together with
`μ[ξ k | ℱ k] =ᵐ 0`.  A `ℱ k`-strongly-measurable function is its own conditional expectation,
so those hypotheses force `ξ k =ᵐ 0`: the theorem was *vacuously* strong and inapplicable to a
martingale difference, which is `ℱ (k+1)`-measurable and centred only given `ℱ k`.  We replaced
the hypothesis by `∀ k, StronglyMeasurable[ℱ (k+1)] (ξ k)` and repaired the three uses, so the
statement below is non-vacuous at that (correct) indexing.

## Instantiation

`LocMartConcrete.lean` supplies the interacting-law and actual-array instances.  It uses the
verified `SwarmHosc.mart_martingale` directly, so no projection-event-to-`centredInc` conversion
or exact-real-history conditioning is needed.  The residual here is only the local profile:
the estimate starts at deterministic time zero, not at a random record time.

Also, `(L^{3/4})²/(16 T L) = L^{1/2}/(16 T)`, so the exponent below is `-L^{1/2}/(16T)`,
which is `≤ -c_T L^{1/16}` once `L^{7/16} ≥ 16 T c_T`.  That comparison and absorption of
the polynomial prefactor are prose here, not proved by this module.
-/
import Swarm.Azuma

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace LocMart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0} {ξ : ℕ → Ω → ℝ}

/-- **`(locmart)` probabilistic half at the paper's local scale.**

`ξ k` is `ℱ (k+1)`-measurable, centred given `ℱ k`, and `|ξ k| ≤ 2`.  Over a window of `T L`
steps at deviation `L^{3/4}`,

  `μ{∃ k ≤ T L, L^{3/4} ≤ |ξ_0 + ⋯ + ξ_{k-1}|}
      ≤ 2 (T L + 1) exp(-(L^{3/4})²/(16 T L))`.

Uniform in the starting time; empty sums contribute `0`; no second-moment or maximal inequality
is used, only the conditional Hoeffding lemma and the tower. -/
theorem measure_max_abs_psum_locmart
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hbdd : ∀ k ω, |ξ k ω| ≤ 2)
    (hmean : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {T L : ℕ} (hT : 1 ≤ T) (hL : 1 ≤ L) :
    μ.real {ω | ∃ k ≤ T * L, (L : ℝ) ^ (3 / 4 : ℝ) ≤ |psum ξ k ω|}
      ≤ 2 * (((T * L : ℕ) : ℝ) + 1) *
          Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) := by
  have hTL : 1 ≤ T * L := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hε : 0 < (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  have hεC : (L : ℝ) ^ (3 / 4 : ℝ) ≤ 2 * ((T * L : ℕ) : ℝ) * 2 := by
    have h1 : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast hL) (by norm_num)
    have h2 : (L : ℝ) ≤ ((T * L : ℕ) : ℝ) := by
      have h3 : L ≤ T * L := Nat.le_mul_of_pos_left L (by omega)
      exact_mod_cast h3
    nlinarith
  have hmain := measure_max_abs_psum_ge_le (μ := μ) (ℱ := ℱ) (ξ := ξ) (C := 2)
    (ε := (L : ℝ) ^ (3 / 4 : ℝ)) hmeas (by norm_num) hbdd hmean hTL hε
  refine le_trans hmain (le_of_eq ?_)
  have hden : (4 : ℝ) * ((T * L : ℕ) : ℝ) * 2 ^ 2 = 16 * ((T * L : ℕ) : ℝ) := by ring
  rw [hden]

end LocMart
