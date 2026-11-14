/-
# The sharp chain: no local-good field anywhere

`M4Sharp` proves

`M4Sharp.stickyOn_lift_of_blockClauses` :
  `BlkCoin.BlockClauses` + `(locmart)` + carrier `{d_r ≤ L}` + window `(T+3)L ≤ r` + numerics
  + `η_n/L_n → 0` with `C_T L_n^{3/4} ≤ η_n` + raw-sample uniform convergence + `LipschitzWith 1`
  ⇒ `StickyOn (fun i r => M2Meet.lift x i r) (64⌈C⌉₊) T`,

with **no** `Glue.LocalField` and **no** lag premise (the field is `LocalClauses.toField` at the
coarse allowance `L + η`, the sharp lag is `LagFromMart.lag_le_sub` on
`[τ_r + 64⌈C⌉₊L, τ_r + TL]`, and the class induction starts at `64⌈C⌉₊`).

This file feeds that coincidence into the composition of `M1Coalesce`/`M1Sticky`/`M1Half`, so the
whole chain — coalescence below `B - 2`, the `hcoal` shape, and the paper's `(half)` clause
uniform in the scale — runs on the **measured clause layer alone**:

    BlkCoin.BlockClauses + JoinStep.MartClause + carrier + window + numerics + η + one
    convergence hypothesis

with `Glue.LocalField`, `M4Coincide.GroupGrow`, `(coincide)`, `(fluid)`, `(meet)`, the `(5.1)`
gap bound and `LipschitzWith 1` all either derived here or in `M1Coalesce`, or supplied by
`M4Sharp`.

## Scope

Deterministic, exactly as `M1Coalesce`/`M1Half`.  The only remaining input is the *probability*
that the measured window package produces `BlockClauses` + `MartClause` at every scale with the
vanishing allowance — that is the local-good event, and it is not estimated here.  No `κ`, no
`arrayMeasure`, no `N`/`m`/`p` regime, no velocity, no `NoCoalescence`.
-/
import Swarm.M1Half
import Swarm.M1Sticky
import Swarm.SharpGroup

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace M1C

open FluidMerge FluidInterpolation FluidLimit RecordDefect JoinStep FluidJoin

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Fluid coalescence below `B - 2` from the measured clauses alone.**  No local-good field,
no group-growth clause, no lag: `(coincide)` is `M4Sharp.stickyOn_lift_of_blockClauses`. -/
theorem coalescence_of_blockClauses_sharp {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC₁ : 1 ≤ C) (hCT : 0 ≤ CT)
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
  have hsticky : StickyOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ) :=
    M4Sharp.stickyOn_lift_of_blockClauses hscale hscaleTop hτ hne hBC hM hC₁ hCT hdr hr hL1 hij
      hnum hT64 hηdef heta hconvU hlip
  exact coalescence_of_sticky hscale hscaleTop hτ hne (fun n => (hBC n).base) hM
    (lt_of_lt_of_le (by norm_num) hC₁) hCT hdr hr hL1 hij hnum hT64 hηdef heta hconvR hsticky
    hbb hBT

/-- The `hcoal` shape of `coalescence_of_blockClauses_sharp`. -/
theorem coalesced_at_theta_of_blockClauses_sharp {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC₁ : 1 ≤ C) (hCT : 0 ≤ CT)
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
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ))
    {θ : Set.Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) :
    x i θ = x j θ := by
  obtain ⟨u, _hsu, hu, huT, hpers⟩ := coalescence_of_blockClauses_sharp hscale hscaleTop hτ hne
    hBC hM hC₁ hCT hdr hr hL1 hij hnum hT64 hηdef heta hconvR hbb hBT
  have huB : u < (θ : ℝ) := by linarith
  have heq := hpers (θ : ℝ) huB.le θ.2.2 i j
  rwa [M2Meet.lift_apply θ.2, M2Meet.lift_apply θ.2] at heq

/-- **The paper's `(half)` clause, uniformly in the scale, from the measured clauses alone.**
Same as `half_from_clauses` but with **no** `Glue.LocalField` and **no** lag profile: the
per-scale data are `BlkCoin.BlockClauses` and `JoinStep.MartClause` (both produced by the
measured window package off its bad event), the carrier, the record window, the numerical
thresholds and the single vanishing allowance `η ≤ ε_L L` (with `C_T L^{3/4} ≤ η`). -/
theorem half_from_clauses_sharp (C₀ B Tn : ℕ) (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hB0 : (0 : ℝ) ≤ (B : ℝ))
    {C CT : ℝ} (hC : 1 ≤ C) (hCT : 0 ≤ CT) (hT64 : 64 * Nat.ceil C ≤ Tn)
    (hC₀ : Tn + 3 ≤ C₀)
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ)) (hcard : 2 ≤ Fintype.card ι) (μ : ℝ)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (η : ℕ),
      IsRecord X τ → (∀ i m, |X i (m + 1) - X i m| = 1) → defect X τ r ≤ (L : ℤ) →
      τ (r + B * L) - τ r ≤ Tn * L →
      BlkCoin.BlockClauses X τ H C CT Tn L r →
      MartClause X τ A μ CT Tn L r →
      1 ≤ L → Numerics C CT L →
      CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) →
      (η : ℝ) ≤ ε L * (L : ℝ) →
      2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ L : ℕ, n + 1 ≤ L ∧ ∃ r : ℕ, C₀ * L ≤ r ∧
      ∃ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (η : ℕ),
        IsRecord X τ ∧ (∀ i m, |X i (m + 1) - X i m| = 1) ∧
        defect X τ r ≤ (L : ℤ) ∧ τ (r + B * L) - τ r ≤ Tn * L ∧
        BlkCoin.BlockClauses X τ H C CT Tn L r ∧
        MartClause X τ A μ CT Tn L r ∧
        1 ≤ L ∧ Numerics C CT L ∧
        CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) ∧
        (η : ℝ) ≤ ε L * (L : ℝ) ∧
        (L : ℤ) < 2 * defect X τ (r + B * L) :=
    fun n => hcon (n + 1)
  choose L hLn r hrL X τ H A η hrec hNN hd htime hBC hM hL1 hnum hηdef hηN hbad using hseq
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := L) (fun n => by have := hLn n; omega)
      tendsto_id
  have hLpos : ∀ n, 0 < L n := fun n => by have := hLn n; omega
  have hr : ∀ n, (Tn + 3) * L n ≤ r n :=
    fun n => le_trans (Nat.mul_le_mul_right (L n) hC₀) (hrL n)
  have hlow : ∀ n, (B : ℝ) ≤ DefectKnot.thetaL (τ n) B (r n) (L n) :=
    fun n => DefectKnot.theta_mem_lower (hrec n) (hNN n) (hLpos n)
  have hup : ∀ n, DefectKnot.thetaL (τ n) B (r n) (L n) ≤ (Tn : ℝ) :=
    fun n => DefectKnot.theta_mem_upper (htime n) (hLpos n)
  obtain ⟨θ, hθmem, ψ, hψ, hθtend⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => DefectKnot.thetaL (τ n) B (r n) (L n)) (fun n => ⟨hlow n, hup n⟩)
  obtain ⟨x, φ, hφ, _hxlip, _hxbound, hxconv, _hxstart, _hlarge', _hscale', _hd', _hsample⟩ :=
    FluidInterpolation.exists_record_interpolated_limit_subseq C₀ (Tn : ℝ) hTn
      (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n)) (fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hrL (ψ n)) (hLtop.comp hψ.tendsto_atTop)
      (fun n => hLpos (ψ n)) (fun n => hd (ψ n)) ⟨0, ⟨le_rfl, hTn⟩⟩ rfl
      (fun n i k => hNN (ψ n) i k)
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : ι, i₀ ≠ j₀ := by
    have h1 : 1 < Fintype.card ι := by omega
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h1 a
    exact ⟨b, a, hb⟩
  -- the coalescence at `θ` from the sharp chain
  have hcoal : ∀ i j : ι,
      x i ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩ = x j ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩ := by
    intro i j
    have hcomp : Tendsto (fun n => ε (L (ψ (φ n)))) atTop (𝓝 0) :=
      hε.comp ((hLtop.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop)
    have hratio : Tendsto (fun n => (η (ψ (φ n)) : ℝ) / (L (ψ (φ n)) : ℝ)) atTop (𝓝 0) := by
      have hb : ∀ n, (η (ψ (φ n)) : ℝ) / (L (ψ (φ n)) : ℝ) ≤ ε (L (ψ (φ n))) := by
        intro n
        have hLr : (0 : ℝ) < (L (ψ (φ n)) : ℝ) := by exact_mod_cast hLpos (ψ (φ n))
        rw [div_le_iff₀ hLr]
        simpa only [mul_comm] using hηN (ψ (φ n))
      have hnn : ∀ n, 0 ≤ (η (ψ (φ n)) : ℝ) / (L (ψ (φ n)) : ℝ) :=
        fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact squeeze_zero hnn hb hcomp
    refine coalesced_at_theta_of_blockClauses_sharp
      (scale := fun n => L (ψ (φ n))) (level := fun n => r (ψ (φ n)))
      (eta := fun n => η (ψ (φ n))) (H := fun n => H (ψ (φ n)))
      (A := fun n => A (ψ (φ n))) (μ := μ) (C := C) (CT := CT) (T := Tn) (B := B)
      (fun n => hLpos (ψ (φ n))) ((hLtop.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop)
      (fun n => hrec (ψ (φ n))) (fun n i m => hNN (ψ (φ n)) i m)
      (fun n => hBC (ψ (φ n))) (fun n => hM (ψ (φ n))) hC hCT
      (fun n => hd (ψ (φ n))) (fun n => hr (ψ (φ n))) (fun n => hL1 (ψ (φ n)))
      hij (fun n => hnum (ψ (φ n))) hT64 (fun n => hηdef (ψ (φ n))) hratio
      (x := x) (fun i => hxconv i) hbb hBT ?_ i j
    exact hθmem.1
  have hθtendφ : Tendsto
      (fun n => DefectKnot.thetaL (τ (ψ (φ n))) B (r (ψ (φ n))) (L (ψ (φ n))))
      atTop (𝓝 (θ : ℝ)) := hθtend.comp hφ.tendsto_atTop
  have hlim : ∀ i, Tendsto (fun n => DefectKnot.knotConf (fun n => X (ψ (φ n)))
      (fun n => τ (ψ (φ n))) B (fun n => r (ψ (φ n))) (fun n => L (ψ (φ n))) n i)
      atTop (𝓝 (x i ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩)) :=
    fun i => DefectKnot.knotConf_tendsto_of_uniform (X := fun n => X (ψ n))
      (τ := fun n => τ (ψ n)) (B := B) (Tn := Tn) hB0
      (level := fun n => r (ψ n)) (scale := fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hLpos (ψ n)) (fun n i k => hNN (ψ n) i k)
      (fun n => htime (ψ n)) hφ hxconv hθmem.1 hθtendφ i
  have hev := DefectKnot.half_eventually_of_coalesced (X := fun n => X (ψ (φ n)))
    (τ := fun n => τ (ψ (φ n))) (B := B) (level := fun n => r (ψ (φ n)))
    (scale := fun n => L (ψ (φ n))) (fun n => hrec (ψ (φ n)))
    (fun n => hLpos (ψ (φ n)))
    (y := fun i => x i ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩) hlim hcoal
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hev] with n hn
    exact (not_le.2 (hbad (ψ (φ n)))) hn
  exact hfalse.exists.elim (fun n hn => hn)

end M1C


