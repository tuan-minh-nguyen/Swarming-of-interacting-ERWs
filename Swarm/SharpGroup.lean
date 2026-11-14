/-
# `(locgroup)`: the measured block clauses and `GroupGrow` are the same clause

`BlkCoin.BlockClauses.group` (`Swarm/CoinGen.lean`) and `M4Coincide.GroupGrow`
(`Swarm/CoincideClass.lean`) state the source's `(locgroup)` — "across a separated stretch
the potential `W^{I,J}` grows by at most `C_T L^{3/4}`" — for arbitrary disjoint nonempty
groups `I, J` and the **same** potential `Wpot H X (univ \ J) I J`, i.e. with the true
complement index `A = Jᶜ`.  They differ only in shape (`W t − W s ≤ C_T L^{3/4}` versus
`W t ≤ W s + C_T L^{3/4}`) and in the order of the hypotheses.

So the measured package of `WindowMain.exists_badEvent_blockClauses` /
`WindowMain.exists_blockClauses_allN` feeds `GroupGrow` directly: no new analytic input is
needed to close the `(locgroup)` premise of the sharp class-spread chain.

* `groupGrow_of_blockClauses`, `blockClauses_of_groupGrow`, `blockClauses_iff_groupGrow` —
  the typebridge, nothing else;
* `stickyOn_lift_of_blockClauses`, `joinRuleFrom_of_blockClauses` — the sharp coincidence and
  the meeting rule with the *whole* measured block-clause package as the only clause input.

Scope.  Deterministic; no probability, no estimate of the measure of the bad event, and no
removal of the restrictions under which the window modules prove `BlockClauses`.
-/
import Swarm.SharpJoin
import Swarm.CoinGen

open Finset Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Sharp

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Glue RecordDefect LocalFluid M4Coincide

/-- The measured clauses and the coincidence induction use differently named copies of the
same potential: `BlkCoin.Wpot` and `M4Coincide.Wpot` have the same definition, so the
`(locgroup)` transfer is definitional. -/
theorem blkCoin_Wpot_eq {H : Finset ι → ℕ → ℤ → ℤ} {X : ι → ℕ → ℤ} {A I J : Finset ι}
    {n : ℕ} : BlkCoin.Wpot H X A I J n = M4Coincide.Wpot H X A I J n := rfl

/-- **`(locgroup)` in the measured shape gives `GroupGrow`.**  The two statements are the
same inequality about the same potential `Wpot H X (univ \ J) I J`; only the side of the
`C_T L^{3/4}` differs. -/
theorem groupGrow_of_blockClauses {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r : ℕ}
    (hBC : BlkCoin.BlockClauses X τ H C CT T L r) : GroupGrow H X τ CT T L r := by
  intro I J s t hI hJ hdisj h1 h2 h3 hsep
  have h := hBC.group I J hdisj hI hJ s t h1 h2 h3 hsep
  rw [blkCoin_Wpot_eq, blkCoin_Wpot_eq] at h
  linarith

/-- The converse bridge: `GroupGrow` together with the lag-free local clauses is the measured
`BlockClauses` package. -/
theorem blockClauses_of_groupGrow {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r : ℕ}
    (hbase : JoinStep.LocalClauses X τ H C CT T L r) (hgrow : GroupGrow H X τ CT T L r) :
    BlkCoin.BlockClauses X τ H C CT T L r := by
  refine ⟨hbase, ?_⟩
  intro I J hdisj hI hJ s t h1 h2 h3 hsep
  have h := hgrow I J s t hI hJ hdisj h1 h2 h3 hsep
  rw [show M4Coincide.Wpot H X (Finset.univ \ J) I J t = BlkCoin.Wpot H X (Finset.univ \ J) I J t
    from blkCoin_Wpot_eq.symm,
    show M4Coincide.Wpot H X (Finset.univ \ J) I J s = BlkCoin.Wpot H X (Finset.univ \ J) I J s
    from blkCoin_Wpot_eq.symm] at h
  linarith

/-- The two forms of `(locgroup)` are equivalent. -/
theorem blockClauses_iff_groupGrow {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    {H : Finset ι → ℕ → ℤ → ℤ} {C CT : ℝ} {T L r : ℕ} :
    (∃ _ : JoinStep.LocalClauses X τ H C CT T L r, GroupGrow H X τ CT T L r) ↔
      BlkCoin.BlockClauses X τ H C CT T L r := by
  constructor
  · rintro ⟨hbase, hgrow⟩
    exact blockClauses_of_groupGrow hbase hgrow
  · intro hBC
    exact ⟨hBC.base, groupGrow_of_blockClauses hBC⟩

/-- **The lifted fluid `(coincide)` on `[64⌈C⌉, T]` from the measured block clauses alone.**

Identical to `M4Sharp.stickyOn_lift_of_clauses`, but the two clause hypotheses
`LocalClauses` and `(locgroup)` are replaced by the single measured package
`BlkCoin.BlockClauses` (its `base` field is the Proposition-`local` clauses without the lag,
its `group` field is `(locgroup)`).  This is the shape in which
`WindowMain.exists_badEvent_blockClauses` produces the clauses off its bad event. -/
theorem stickyOn_lift_of_blockClauses
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {A : ℕ → ι → ℕ → ℕ} {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, JoinStep.MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
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
    FluidMerge.StickyOn (fun i r => M2Meet.lift x i r) (64 * Nat.ceil C : ℝ) (T : ℝ) :=
  stickyOn_lift_of_clauses hscale hscaleTop hτ hne (fun n => (hBC n).base) hM
    (fun n => groupGrow_of_blockClauses (hBC n)) hC1 hHT hdr hr hL1 hij hnum hT64 hηdef heta
    hconv hlip

/-- **The source's meeting rule at `2 C²` on `[64⌈C⌉, T]` from the measured block clauses.**

This is `M2Meet.joinRuleFrom_of_clauses` with `(coincide)` proved and the two clause premises
merged into the measured `BlkCoin.BlockClauses` package.  The only clause-level input left is
`BlockClauses` at every scale (plus `(locmart)`), together with the numerical data, the
vanishing allowance and the compactness output. -/
theorem joinRuleFrom_of_blockClauses
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {A : ℕ → ι → ℕ → ℕ} {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, JoinStep.MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
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
  M2Meet.joinRuleFrom_of_clauses hscale hscaleTop hτ hne (fun n => (hBC n).base) hM
    (lt_of_lt_of_le zero_lt_one hC1) hHT hdr hr hL1 hij hnum hT64 hηdef heta hconv hlip
    (stickyOn_lift_of_blockClauses hscale hscaleTop hτ hne hBC hM hC1 hHT hdr hr hL1 hij hnum
      hT64 hηdef heta hconv hlip)

end M4Sharp
