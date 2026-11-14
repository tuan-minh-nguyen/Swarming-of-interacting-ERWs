/-
# The fluid `(coincide)` on the sharp window `[64⌈C⌉, T]`, from the measured clauses

`M4Sharp.SharpClass` removes the whole-window lag from the finite-scale class-spread
induction.  This file lifts the result to the fluid level and then feeds it the *measured*
clauses, so that no `LocalField` and no lag hypothesis is left as a premise:

* `classSpread_of_grid_lag` — the class spread `o(L)` at every grid time of `[s,T]`, from
  grid convergence at the single time `s ≥ 64⌈C⌉`;
* `pairwise_of_grid_lag` — the same in the pairwise `(4.8)` form;
* `stickyOn_of_grid_sharp` — the fluid `(coincide)` `FluidMerge.StickyOn x s₀ T` for every
  `s₀ ≥ 64⌈C⌉`, with no coincidence asserted below `64⌈C⌉`;
* `coincideOn_of_grid_sharp` — the same in `WCJFFluidCore.CoincideOn` form;
* `stickyOn_of_clauses` — the same conclusion from `JoinStep.LocalClauses`,
  `JoinStep.MartClause`, `(locgroup)` and the lattice/numerical data: the field comes from
  `LocalClauses.toField` (allowance `L_n + η_n`) and the sharp post-`64⌈C⌉` lag from
  `LagFromMart.lag_le_sub`, so the lag clause is *derived*, not assumed.

Scope.  Deterministic.  Nothing here mentions probabilities, `arrayMeasure`, invariance,
stationarity or a velocity; the named remaining inputs are the literal record and step-one
paths, `LocalClauses` (Proposition `local` minus the lag), `(locmart)`, `(locgroup)`, the
carrier `{d_r ≤ L}`, the numerical thresholds, the vanishing normalized allowance
`η_n/L_n → 0`, `1 ≤ C`, and knotwise convergence of the scaled positions.
-/
import Swarm.SharpClass

open Finset Filter Topology
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Sharp

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid M4Coincide

/-! ## 3. The class spread along a scale sequence, started at `64⌈C⌉L` -/

/-- **The source's `(4.8)` for the coincidence class, started at the sharp origin.**  Per
scale: a local field at *any* allowance `ηF n` (in practice the coarse `L_n + η_n`), `(locgroup)`,
the record and step-one paths, the carrier `d_r ≤ L`, the window `r ≥ (T+3)L`, the sharp lag
`η n` on `[τ_r + 64⌈C⌉L, τ_r + TL]`, and vanishing errors `ε₁, ε₂`; plus convergence of the
scaled positions of `D` to a common value `c` at the grid time of the fluid time `s`, with
`64⌈C⌉ ≤ s`.  Then one vanishing `ε` bounds the spread of `D` at every grid time of `[s,Tn]`. -/
theorem classSpread_of_grid_lag
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r ηF η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (ηF n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ), τ n (r n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (r n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (η n : ℤ))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s) (hsT : s ≤ Tn)
    (hTn : Tn ≤ (T : ℝ)) {c : ℝ}
    (hconv : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 c))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (t : ℝ), s ≤ t → t ≤ Tn →
        ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) ≤ ε n * (scale n) := by
  obtain ⟨ε0, hε0t, hstart⟩ :=
    classStart_tendsto (X := X) (τ := τ) (level := r) (scale := scale) hscale hD hs0 hconv
  exact classSpread_tendsto_lag hscale hscaleTop hLF hgrow hlagw hC1 hCT hτ hne hdr hrT hD
    hε0t hε1t hε2t hs0 hs64 hsT hTn hstart hη hct

/-- **The paper's `(4.8)` in pairwise form, started at `64⌈C⌉L`.**  Two walkers of the
coincidence class `D` have scaled positions within one vanishing `ε n` at every grid time
`⌊L_n t⌋`, `s ≤ t ≤ T`, as soon as `64⌈C⌉ ≤ s`. -/
theorem pairwise_of_grid_lag
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r ηF η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (ηF n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ), τ n (r n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (r n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (η n : ℤ))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s) (hsT : s ≤ Tn)
    (hTn : Tn ≤ (T : ℝ)) {c : ℝ}
    (hconv : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 c))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (i j : ι) (t : ℝ), i ∈ D → j ∈ D → s ≤ t → t ≤ Tn →
        |FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
          - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j
              ⌊(scale n : ℝ) * t⌋₊| ≤ ε n := by
  obtain ⟨ε, hεt, hspread⟩ := classSpread_of_grid_lag hscale hscaleTop hLF hgrow hlagw hC1 hCT
    hτ hne hdr hrT hD hε1t hε2t hs0 hs64 hsT hTn hconv hη hct
  refine ⟨ε, hεt, ?_⟩
  intro n i j t hi hj hst htT
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hDne : D.Nonempty := ⟨i, hi⟩
  have hsp := hspread n t hst htT
  have hcast : FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊
      - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j ⌊(scale n : ℝ) * t⌋₊
      = ((X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℝ)
          - (X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℝ)) / (scale n : ℝ) := by
    unfold FluidLimit.scaledPosition
    ring
  have hsub1 : X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
      - X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
      ≤ spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) := sub_spreadS hDne hi hj
  have hsub2 : X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
      - X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
      ≤ spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) := sub_spreadS hDne hj hi
  rw [hcast, abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
  constructor
  · have h2 : ((X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
          - X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ)
        ≤ ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) := by
      exact_mod_cast hsub2
    push_cast at h2 ⊢
    linarith
  · have h1 : ((X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊)
          - X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ)
        ≤ ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) := by
      exact_mod_cast hsub1
    push_cast at h1 ⊢
    linarith

/-! ## 4. The fluid `(coincide)` on `[s₀, T]` for `s₀ ≥ 64⌈C⌉` -/

/-- **The fluid `(coincide)` from the finite-scale class spread, with the honest origin.**

Per scale: the local field at any allowance `ηF n`, `(locgroup)`, the record and step-one
paths, the carrier, the window, the sharp lag on `[τ_r + 64⌈C⌉L, τ_r + TL]` and the two
vanishing error profiles; plus convergence of the scaled positions at every grid knot of
`[s₀, T]`.  Then any two fluid paths that meet at a time `s ≥ s₀ ≥ 64⌈C⌉` coincide for all
later times of `[s₀, T]`.

This is `M4Coincide.stickyOn_of_grid` with `LocalField.lag` replaced by the sharp
post-`64⌈C⌉L` lag, and with the conclusion restricted to the source's own window
`[64⌈C⌉, T]`.  No coincidence is claimed before `64⌈C⌉`. -/
theorem stickyOn_of_grid_sharp
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r ηF η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (ηF n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ), τ n (r n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (r n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (η n : ℤ))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n))
    {x : ι → ℝ → ℝ} {s₀ : ℝ} (hs0 : 0 ≤ s₀) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s₀)
    (hconv : ∀ (i : ι) (t : ℝ), s₀ ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (x i t))) :
    FluidMerge.StickyOn x s₀ (T : ℝ) := by
  classical
  intro i j s t hs0s hst htT heq
  set D : Finset ι := Finset.univ.filter (fun k => x k s = x i s) with hDdef
  have hiD : i ∈ D := by
    rw [hDdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩
  have hjD : j ∈ D := by
    rw [hDdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.symm⟩
  have hDne : D.Nonempty := ⟨i, hiD⟩
  have hs0le : (0 : ℝ) ≤ s := le_trans hs0 hs0s
  have hsT : s ≤ (T : ℝ) := le_trans hst htT
  have hs64' : (64 * Nat.ceil C : ℝ) ≤ s := le_trans hs64 hs0s
  have hconv_s : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 (x i s)) := by
    intro k hk
    have hks : x k s = x i s := (Finset.mem_filter.mp hk).2
    rw [← hks]
    exact hconv k s hs0s hsT
  obtain ⟨ε, hεt, hpair⟩ := pairwise_of_grid_lag hscale hscaleTop hLF hgrow hlagw hC1 hCT
    hτ hne hdr hrT hDne hε1t hε2t hs0le hs64' hsT le_rfl hconv_s hη hct
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
`WCJFFluidCore.CoincideOn`. -/
theorem coincideOn_of_grid_sharp
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r ηF η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (ηF n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ), τ n (r n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (r n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (η n : ℤ))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n))
    {x : ι → ℝ → ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s)
    (hsT : s ≤ (T : ℝ))
    (hconv : ∀ (i : ι) (t : ℝ), s ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (x i t))) :
    WCJFFluidCore.CoincideOn x s (T : ℝ) := by
  intro i j heq u hsu huT
  exact stickyOn_of_grid_sharp hscale hscaleTop hLF hgrow hlagw hC1 hCT hτ hne hdr hrT hε1t
    hε2t hη hct hs0 hs64 hconv i j s u le_rfl hsu huT heq

/-! ## 5. The same from the measured clauses, with the lag *derived* -/

/-- **The fluid `(coincide)` on `[64⌈C⌉, T]` from `LocalClauses + MartClause`.**

Inputs: at every scale `L_n → ∞` the literal record, unit-step paths, the Proposition-`local`
clauses `JoinStep.LocalClauses` (potential monotonicity/unit increment, `(loccoord)`,
`(locmove)`, `(lococc)` — *no* lag clause), `(locmart)` as `JoinStep.MartClause`, the source's
`(locgroup)` for all disjoint groups, the carrier `{d_r ≤ L}`, the window `r ≥ (T+3)L`, the
numerical thresholds (`1 ≤ L_n`, `Numerics`, `64⌈C⌉ ≤ T`, `1 ≤ C`), two distinct walkers and
the vanishing normalized allowance `η_n/L_n → 0` with `C_T L_n^{3/4} ≤ η_n`; and knotwise
convergence of the actual scaled positions on `[s₀, T]` with `s₀ ≥ 64⌈C⌉`.

Conclusion: `FluidMerge.StickyOn x s₀ T`, i.e. the source's `(coincide)` on its own window
`[64C, T]`.  This is verbatim the `hsticky` premise of `M2Meet.joinRuleFrom_of_clauses`.

The local field is built at the coarse allowance `scale n + eta n` by
`LocalClauses.toField`, and the lag clause used by the induction is the sharp one on
`[τ_r + 64⌈C⌉L, τ_r + TL]` supplied by `LagFromMart.lag_le_sub`.  So neither
`LocalField` nor any lag bound survives as a premise. -/
theorem stickyOn_of_clauses
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {A : ℕ → ι → ℕ → ℕ} {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hcl : ∀ n, JoinStep.LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, JoinStep.MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) CT T (scale n) (level n))
    (hC1 : 1 ≤ C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, JoinStep.Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {x : ι → ℝ → ℝ} {s₀ : ℝ} (hs0 : 0 ≤ s₀) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s₀)
    (hconv : ∀ (i : ι) (t : ℝ), s₀ ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => FluidLimit.scaledPosition (X n) (level n) (τ n (level n))
        (scale n) i ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (x i t))) :
    FluidMerge.StickyOn x s₀ (T : ℝ) := by
  classical
  -- the local field at the coarse allowance `L + η`, with the lag clause derived
  have hLF : ∀ n, LocalField (X n) (τ n) (H n) C CT T (scale n) (level n)
      (scale n + eta n) := fun n =>
    JoinStep.LocalClauses.toField (hcl n) (hτ n) (hM n) (hdr n) (hηdef n)
  -- the sharp lag on the subwindow `[τ_r + 64⌈C⌉L, τ_r + TL]`
  have hlagw : ∀ (n : ℕ) (i : ι) (m : ℕ),
      τ n (level n) + 64 * Nat.ceil C * scale n ≤ m →
      m ≤ τ n (level n) + T * scale n → runMaxI (X n) i m - X n i m ≤ (eta n : ℤ) := by
    intro n i m h1 h2
    exact JoinStep.lag_le_sub (X n) (hτ n) (hM n) (lt_of_lt_of_le zero_lt_one hC1)
      (hcl n).occ (hdr n) (hL1 n) hij (hnum n) hT64 (hηdef n) h1 h2 i
  refine stickyOn_of_grid_sharp (CT := fun _ => CT) hscale hscaleTop hLF hgrow hlagw hC1
    (fun _ => hHT) hτ hne hdr hrT
    (ε1 := fun n => (eta n : ℝ) / (scale n : ℝ))
    (ε2 := fun n => (eta n : ℝ) / (scale n : ℝ)) heta heta ?_ ?_ hs0 hs64 hconv
  · intro n
    have hLpos : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    exact le_of_eq (div_mul_cancel₀ _ hLpos.ne').symm
  · intro n
    have hLpos : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    rw [div_mul_cancel₀ _ hLpos.ne']
    exact hηdef n

end M4Sharp
