/-
# The meeting rule with `(coincide)` *proved*: `JoinRuleFrom` from the measured clauses

`M2Meet.joinRuleFrom_of_clauses` (`Swarm/MeetCompose.lean`) produces the source's meeting
rule `FluidMerge.JoinRuleFrom` at the sharp constant `2 C²` on the sharp window
`[64⌈C⌉, T]` from the finite-scale clauses, **given** the fluid `(coincide)`
`StickyOn (fun i r => lift x i r) (64⌈C⌉) T` as an input.

`M4Sharp.stickyOn_of_clauses` (`SharpCoincide.lean`) proves exactly that `StickyOn` from the
same clause data plus `(locgroup)` and the vanishing normalized allowance.  This file joins
the two, so the meeting rule no longer carries `(coincide)` — nor a `LocalField`, nor a lag
bound — as a premise:

* `stickyOn_lift_of_clauses` — the lifted `(coincide)` on `[64⌈C⌉, T]` from the uniform
  convergence of the raw record interpolants (the compactness output), via
  `M2B.scaledPosition_tendsto_of_ratio` at the moving knots `⌊L_n t⌋` and
  `M2Meet.lift_apply`;
* `joinRuleFrom_of_clauses_sharp` — the same hypotheses as
  `M2Meet.joinRuleFrom_of_clauses` with `hsticky` **removed** and `(locgroup)` added.

Scope.  Deterministic.  The remaining inputs are the literal record and step-one paths, the
Proposition-`local` clauses without the lag, `(locmart)`, `(locgroup)`, the carrier
`{d_r ≤ L}`, the window `r ≥ (T+3)L`, the numerical thresholds (`1 ≤ C`, `1 ≤ L_n`,
`Numerics`, `64⌈C⌉ ≤ T`, two distinct walkers), the vanishing allowance `η_n/L_n → 0` with
`C_T L_n^{3/4} ≤ η_n`, the uniform convergence of the actual raw record interpolants to a
`1`-Lipschitz fluid limit.  No probability, no `arrayMeasure`, no stationarity, no velocity,
no `NoCoalescence`; the failure probability of these clauses is *not* estimated here.
-/
import Swarm.SharpCoincide
import Swarm.MeetCompose

open Finset Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Sharp

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid M4Coincide

/-- **The lifted fluid `(coincide)` on `[64⌈C⌉, T]` from the measured clauses.**

This is `M4Sharp.stickyOn_of_clauses` with its knotwise convergence hypothesis discharged
from the uniform convergence of the raw record interpolants: at the grid knot
`k n = ⌊L_n t⌋` the ratio `k n / L_n → t` and `k n ≤ T L_n`, so
`M2B.scaledPosition_tendsto_of_ratio` gives the required convergence, and `M2Meet.lift_apply`
identifies the subtype limit with the zero-extension `M2Meet.lift x`.

The conclusion is verbatim the `hsticky` premise of `M2Meet.joinRuleFrom_of_clauses`. -/
theorem stickyOn_lift_of_clauses
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {A : ℕ → ι → ℕ → ℕ} {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, JoinStep.LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, JoinStep.MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) CT T (scale n) (level n))
    (hC1 : 1 ≤ C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, JoinStep.Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        FluidLimit.scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    FluidMerge.StickyOn (fun i r => M2Meet.lift x i r) (64 * Nat.ceil C : ℝ) (T : ℝ) := by
  have hs0 : (0 : ℝ) ≤ (64 * Nat.ceil C : ℝ) := by positivity
  refine M4Sharp.stickyOn_of_clauses hscale hscaleTop hτ hne hcl hM hgrow hC1 hHT hdr hr hL1
    hij hnum hT64 hηdef heta hs0 le_rfl ?_
  intro i t h1 h2
  have ht0 : (0 : ℝ) ≤ t := le_trans hs0 h1
  have htT : t ≤ (T : ℝ) := h2
  have hkT : ∀ᶠ n in atTop, ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
    refine Filter.Eventually.of_forall (fun n => ?_)
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hfl : ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * t :=
      Nat.floor_le (mul_nonneg hL.le ht0)
    have hmono : (scale n : ℝ) * t ≤ (scale n : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left htT hL.le
    calc ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * t := hfl
      _ ≤ (scale n : ℝ) * (T : ℝ) := hmono
      _ = (T : ℝ) * (scale n : ℝ) := by ring
  have hratio : Tendsto (fun n => ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ))
      atTop (𝓝 t) := M2Meet.tendsto_floor_mul_div hscale hscaleTop ht0
  have hk := M2B.scaledPosition_tendsto_of_ratio (T := (T : ℝ)) hscale hconv hlip
    (v := t) ⟨ht0, htT⟩ (k := fun n => ⌊(scale n : ℝ) * t⌋₊) hkT hratio i
  rw [M2Meet.lift_apply (x := x) (i := i) (r := t) ⟨ht0, htT⟩]
  exact hk

/-- **The source's meeting rule from the measured clauses, with `(coincide)` proved.**

Same hypotheses as `M2Meet.joinRuleFrom_of_clauses`, except that the fluid `(coincide)`
`StickyOn` is not assumed: it is derived from `LocalClauses + MartClause + (locgroup)` by
`stickyOn_lift_of_clauses`.  The conclusion is the actual `FluidMerge.JoinRuleFrom` at the
sharp constant `2 C²` on the source's window `[64⌈C⌉, T]`. -/
theorem joinRuleFrom_of_clauses_sharp
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {A : ℕ → ι → ℕ → ℕ} {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, JoinStep.LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, JoinStep.MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) CT T (scale n) (level n))
    (hC1 : 1 ≤ C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, JoinStep.Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        FluidLimit.scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    FluidMerge.JoinRuleFrom (fun i r => M2Meet.lift x i r) (64 * Nat.ceil C : ℝ) (2 * C ^ 2)
      (T : ℝ) :=
  M2Meet.joinRuleFrom_of_clauses hscale hscaleTop hτ hne hcl hM
    (lt_of_lt_of_le zero_lt_one hC1) hHT hdr hr hL1 hij hnum hT64 hηdef heta hconv hlip
    (stickyOn_lift_of_clauses hscale hscaleTop hτ hne hcl hM hgrow hC1 hHT hdr hr hL1 hij
      hnum hT64 hηdef heta hconv hlip)

end M4Sharp
