/-
# The fluid `StickyOn` (`(coincide)`) from the finite-scale class spread

`FluidMerge.StickyOn x s₀ T` is the accepted interface for the paper's `(coincide)`:
fluid paths that agree at one time `s` agree at every later time of the window.  It is
consumed by `FluidMergeLight.exists_persistent_coalescence` and by
`FluidGeometryLight.stickyOn_of_localGood` is the zero-error *sufficient* route to it.

This file derives `StickyOn` **directly** from the finite-scale data of `CoincideClass` and
pointwise grid convergence, without passing through `FluidLocalGood` and without any
rescaled-potential limit:

* at each fluid time `s`, the coincidence class `D = {k | x k s = x i s}` is finite, and grid
  convergence at `s` makes its grid spread `o(L)` (`CoincideStart.classStart_tendsto`);
* `CoincideStart.pairwise_of_grid` then gives `|y_i(t) − y_j(t)| ≤ ε n` at every grid time
  `⌊L_n t⌋`, `s ≤ t ≤ T`, with `ε n → 0`;
* grid convergence at `t` upgrades this to `x i t = x j t`.

So the only inputs are the per-scale local-good field, `(locgroup)`, and the compactness
conclusion at the grid knots.  No `StickyOn`, `JoinRuleFrom`, `hpair`, stationarity or
`noCoalescence` is assumed.
-/
import Swarm.CoincideStart
import Swarm.FluidMergeLight
import Swarm.FluidCore

open Finset Filter Topology
open scoped BigOperators

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Coincide

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid

/-- **The fluid `(coincide)`/`StickyOn` from the finite-scale class spread.**  Per scale: the
local-good field with `(locgroup)`, the record window conditions, and the two error profiles
`η = O(ε₁L)`, `C_T L^{3/4} = O(ε₂L)` with `ε₁, ε₂ → 0`.  Plus: the scaled positions at every
grid knot `⌊L_n t⌋`, `t ∈ [0,T]`, converge to the fluid paths `x`.  Then any two fluid paths
that meet at a time `s ≥ 0` coincide for all later times of `[0,T]`. -/
theorem stickyOn_of_grid
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (η n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n))
    {x : ι → ℝ → ℝ} {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (hconv : ∀ (i : ι) (t : ℝ), s₀ ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (x i t))) :
    FluidMerge.StickyOn x s₀ (T : ℝ) := by
  classical
  intro i j s t hs0s hst htT heq
  -- the coincidence class of `i` at the fluid time `s`
  set D : Finset ι := Finset.univ.filter (fun k => x k s = x i s) with hDdef
  have hiD : i ∈ D := by
    rw [hDdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
  have hjD : j ∈ D := by
    rw [hDdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.symm⟩
  have hDne : D.Nonempty := ⟨i, hiD⟩
  have hs0le : (0 : ℝ) ≤ s := le_trans hs0 hs0s
  have hsT : s ≤ (T : ℝ) := le_trans hst htT
  -- grid convergence at the meeting time gives the `ε₀` of the class spread
  have hconv_s : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 (x i s)) := by
    intro k hk
    have hks : x k s = x i s := (Finset.mem_filter.mp hk).2
    rw [← hks]
    exact hconv k s hs0s hsT
  -- the pairwise `(4.8)`: one vanishing `ε` bounds every grid difference on `[s,T]`
  obtain ⟨ε, hεt, hpair⟩ := pairwise_of_grid hscale hscaleTop hLF hgrow hC1 hCT hτ hne
    hdr hrT hDne hε1t hε2t hs0le hsT le_rfl hconv_s hη hct
  -- pass to the limit at the target time `t`
  have hlim : Tendsto (fun n =>
      |FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
        - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j
            ⌊(scale n : ℝ) * t⌋₊|) atTop (𝓝 |x i t - x j t|) :=
    (((hconv i t (le_trans hs0s hst) htT).sub (hconv j t (le_trans hs0s hst) htT)).abs)
  have hbound : ∀ n,
      |FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
        - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j
            ⌊(scale n : ℝ) * t⌋₊| ≤ ε n :=
    fun n => hpair n i j t hiD hjD hst htT
  have hzero : |x i t - x j t| ≤ 0 :=
    le_of_tendsto_of_tendsto hlim hεt (Eventually.of_forall hbound)
  have hsub : x i t - x j t = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  exact sub_eq_zero.mp hsub

/-- The same conclusion in the swarm's canonical `(coincide)` object
`WCJFFluidCore.CoincideOn`: for a fixed fluid time `s` at which two paths agree, they agree on
all of `[s,T]`.  This is `stickyOn_of_grid` specialised to `s₀ = s`. -/
theorem coincideOn_of_grid
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (η n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n))
    {x : ι → ℝ → ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ (T : ℝ))
    (hconv : ∀ (i : ι) (t : ℝ), 0 ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (x i t))) :
    WCJFFluidCore.CoincideOn x s (T : ℝ) := by
  intro i j heq u hsu huT
  exact stickyOn_of_grid hscale hscaleTop hLF hgrow hC1 hCT hτ hne hdr hrT hε1t hε2t hη hct hs0
    (fun k t h1 h2 => hconv k t (le_trans hs0 h1) h2) i j s u le_rfl hsu huT heq
