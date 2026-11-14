/-
# The same coalescence with `(coincide)` taken as an input, and the finite-scale spread

This file therefore exposes the same coalescence theorem with `StickyOn` as a *hypothesis*
rather than a conclusion, so that such a sharper coincidence statement plugs in verbatim:

* `coalescence_of_sticky` : the meeting rule is produced by
  `M2Meet.joinRuleFrom_of_clauses` from the finite-scale clauses `LocalClauses` + `MartClause`,
  the drift and the initial gap are produced from `MartClause` and `{d_r ≤ L}`, and only
  `StickyOn (lift x) 64⌈C⌉₊ T` is consumed.  Nothing else about coincidence is assumed, and the
  scalar side is only `0 < C` (the `1 ≤ C` of the local-field route is no longer needed).
* `coalesced_at_theta_of_sticky` : the same at every fluid time `θ ≥ B`.
* `knotSpread_tendsto_zero` : the **pointwise finite-scale spread** at such a `θ`: the actual
  scaled positions of any two walkers at the grid knot `⌊L θ⌋` differ by `o(1)`.  This is
  `(4.8)` read at one fluid time, on the actual trajectory, with no measure involved.

## Scope

Deterministic, exactly as `M1Coalesce`.  `StickyOn` is the *only* fluid-level premise; the
probability that the clause layer and the coincidence statement hold is not addressed here, and
`StickyOn` is not derived in this file.
-/
import Swarm.M1Coalesce

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace M1C

open FluidMerge FluidInterpolation FluidLimit RecordDefect JoinStep FluidJoin

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Fluid coalescence below `B - 2` with `(coincide)` as an input.**  Identical to
`coalescence_of_clauses` except that `StickyOn (lift x) 64⌈C⌉₊ T` replaces the local-good field
`Glue.LocalField` + `M4Coincide.GroupGrow`, and `0 < C` replaces `1 ≤ C`. -/
theorem coalescence_of_sticky {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hCT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hsticky : StickyOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ))
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ)) :
    ∃ u, 64 * (Nat.ceil C : ℝ) ≤ u ∧
      u ≤ (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1 ∧
      u < (T : ℝ) ∧
      ∀ t, u ≤ t → t ≤ (T : ℝ) → ∀ i j, M2Meet.lift x i t = M2Meet.lift x j t := by
  have hlip : ∀ i, LipschitzWith 1 (x i) :=
    fun i => lipschitz_of_uniform_recordFamily hscale hne (T := (T : ℝ)) (x := x) (φ := id) hconvR i
  have hconvU : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ)))
      (fun t => x i t) atTop :=
    fun i => tendstoUniformly_rawSample hscale hscaleTop hne i (hconvR i)
  have hconvK : ∀ (i : ι) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ (T : ℝ)),
      Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (M2Meet.lift x i t)) :=
    fun i t ht0 htT => knot_tendsto hscale hscaleTop hne hconvR i t ht0 htT
  have hTn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hs₀0 : (0 : ℝ) ≤ 64 * (Nat.ceil C : ℝ) := by positivity
  have hjoin : JoinRuleFrom (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (2 * C ^ 2)
      (T : ℝ) :=
    M2Meet.joinRuleFrom_of_clauses (scale := scale) (level := level) (eta := eta) hscale
      hscaleTop hτ hne hcl hM hC hCT hdr hr hL1 hij hnum hT64 hηdef heta hconvU hlip hsticky
  have hmove0 : FluidMotionOn (fun i r => M2Meet.lift x i r) 0 (T : ℝ) :=
    fluidMotionOn_of_martClause (C := C) hscale hscaleTop hM hconvK hlip
  have hmove : FluidMotionOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ) :=
    fun i s t hs hst htT => hmove0 i s t (le_trans hs₀0 hs) hst htT
  have hconv0 : ∀ i, Tendsto (fun n =>
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0) atTop
      (𝓝 (M2Meet.lift x i 0)) := by
    intro i
    have h := hconvK i 0 le_rfl hTn
    simpa using h
  have hgap0 : fluidGap (fun i => M2Meet.lift x i 0) ≤ 1 :=
    fluidGap_lift_zero_le_one hτ hscale hdr hconv0
  have hT64' : 64 * (Nat.ceil C : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT64
  have hgap₀ : fluidGap (fun i => M2Meet.lift x i (64 * (Nat.ceil C : ℝ))) ≤
      1 + 64 * (Nat.ceil C : ℝ) :=
    fluidGap_le_one_add hmove0 hs₀0 hT64' hgap0
  obtain ⟨u, hsu, hu, huT, hpers⟩ :=
    exists_persistent_coalescence (fun i r => M2Meet.lift x i r)
      (64 * (Nat.ceil C : ℝ)) (2 * C ^ 2) (1 + 64 * (Nat.ceil C : ℝ)) (T : ℝ)
      hmove hjoin hsticky (by positivity) (by positivity) (hbb.trans hBT) (by linarith) hgap₀
  exact ⟨u, hsu, hu, huT, hpers⟩

/-- The `hcoal` shape of `coalescence_of_sticky`. -/
theorem coalesced_at_theta_of_sticky {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hCT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hsticky : StickyOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ))
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ))
    {θ : Set.Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) :
    x i θ = x j θ := by
  obtain ⟨u, hsu, hu, huT, hpers⟩ := coalescence_of_sticky hscale hscaleTop hτ hne hcl hM hC hCT
    hdr hr hL1 hij hnum hT64 hηdef heta hconvR hsticky hbb hBT
  have huB : u < (θ : ℝ) := by linarith
  have heq := hpers (θ : ℝ) huB.le θ.2.2 i j
  rwa [M2Meet.lift_apply θ.2, M2Meet.lift_apply θ.2] at heq

/-- **Pointwise finite-scale spread at a coalesced fluid time.**  At any fluid time
`θ ∈ [B, T]`, the actual scaled positions of any two walkers at the grid knot `⌊L_n θ⌋` differ
by `o(1)`: this is the source's `(4.8)` read at the single fluid time `θ`, with no measure and
no rate.  It is the finite-scale shadow of `coalesced_at_theta_of_sticky`. -/
theorem knotSpread_tendsto_zero {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hCT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hsticky : StickyOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ))
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ))
    {θ : Set.Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * (θ : ℝ)⌋₊
      - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j
        ⌊(scale n : ℝ) * (θ : ℝ)⌋₊) atTop (𝓝 0) := by
  have heq : x i θ = x j θ :=
    coalesced_at_theta_of_sticky hscale hscaleTop hτ hne hcl hM hC hCT hdr hr hL1 hij hnum
      hT64 hηdef heta hconvR hsticky hbb hBT hBθ i j
  have hi := knot_tendsto hscale hscaleTop hne hconvR i (θ : ℝ) θ.2.1 θ.2.2
  have hj := knot_tendsto hscale hscaleTop hne hconvR j (θ : ℝ) θ.2.1 θ.2.2
  have hsub := hi.sub hj
  have hlift : M2Meet.lift x i (θ : ℝ) - M2Meet.lift x j (θ : ℝ) = 0 := by
    rw [M2Meet.lift_apply θ.2, M2Meet.lift_apply θ.2, heq, sub_self]
  rw [hlift] at hsub
  simpa using hsub

end M1C


