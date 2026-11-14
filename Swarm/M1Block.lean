/-
# `M4Coincide.GroupGrow` *is* `BlkCoin.BlockClauses.group`, and the coalescence on that interface

`BlkCoin.BlockClauses` (`CoinGen`) is what the measured window package
`WindowMain.exists_badEvent_blockClauses` produces: `(loccoord)`, `(locmove)`, `(lococc)`,
`hmono`, `hunit` in its field `base` (i.e. `JoinStep.LocalClauses`) and the source's
`(locgroup)` for **all** disjoint nonempty groups in its field `group`.

`M4Coincide.GroupGrow` — the group-growth clause consumed by `M4Coincide.stickyOn_of_grid` — is
that same `(locgroup)` with the binder order permuted and with the potential written as
`M4Coincide.Wpot` instead of `BlkCoin.Wpot`.  The two `Wpot`s are the same formula
(`W_n^{I,J} = |I|⁻¹ Σ_{i∈I} H_n^{Jᶜ}(X_n^i) - max_{j∈J} H_n^{Jᶜ}(X_n^j)`), so the transport is
`rfl`/`linarith` only: `groupGrow_of_blockClauses` below.

Consequence (`coalescence_of_blockClauses`): the deterministic endpoint of step 6 —
`M1C.coalescence_of_clauses` — can be fed **exactly** the measured object: one `BlockClauses`
per scale (which carries `LocalClauses` as `.base`) plus the local-good field with sharp lag.
`GroupGrow` and `LocalClauses` are no longer separate hypotheses.

## Scope

Same deterministic scope as `M1Coalesce`.  This file does not produce a `BlockClauses`; it only
transports one.  The sharp-lag `Glue.LocalField` remains a hypothesis.
-/
import Swarm.CoinGen
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

/-- The source's `(locgroup)` in the form the finite-scale coincidence induction consumes.  This
is a type bridge: the two potentials are the same definition. -/
theorem groupGrow_of_blockClauses {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r : ℕ}
    (h : BlkCoin.BlockClauses X τ H C CT T L r) :
    M4Coincide.GroupGrow H X τ CT T L r := by
  intro I J s t hI hJ hd h1 h2 h3 hsep
  have hg := h.group I J hd hI hJ s t h1 h2 h3 hsep
  show BlkCoin.Wpot H X (Finset.univ \ J) I J t
    ≤ BlkCoin.Wpot H X (Finset.univ \ J) I J s + CT * (L : ℝ) ^ (3 / 4 : ℝ)
  linarith

/-- **Fluid coalescence below `B - 2` from the measured block clauses and the local-good
field.**  `hBC n` is the per-scale `BlkCoin.BlockClauses` (hence `LocalClauses`), `hLF n` the
per-scale `Glue.LocalField` with sharp lag `η^L_n = o(L_n)`; everything else is as in
`M1C.coalescence_of_clauses`. -/
theorem coalescence_of_blockClauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta etaL : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hLF : ∀ n, Glue.LocalField (X n) (τ n) (H n) C CT T (scale n) (level n) (etaL n))
    (hC₁ : 1 ≤ C) (hCT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    (hηL : ∀ n, ((etaL n : ℕ) : ℝ) ≤ ε1 n * (scale n : ℝ))
    (hct : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n : ℝ))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ)) :
    ∃ u, 64 * (Nat.ceil C : ℝ) ≤ u ∧
      u ≤ (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1 ∧
      u < (T : ℝ) ∧
      ∀ t, u ≤ t → t ≤ (T : ℝ) → ∀ i j, M2Meet.lift x i t = M2Meet.lift x j t :=
  coalescence_of_clauses hscale hscaleTop hτ hne (fun n => (hBC n).base) hM hLF
    (fun n => groupGrow_of_blockClauses (hBC n)) hC₁ hCT hdr hr hL1 hij hnum hT64 hηdef heta
    hε1t hε2t hηL hct hconvR hbb hBT

end M1C


