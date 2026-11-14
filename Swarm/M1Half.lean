/-
# The deterministic `(half)` clause from the measured clause layer

`M4D.UniformHalfClause` (`Swarm/BlockAssembly.lean`) quantifies over **arbitrary**
nearest-neighbour record paths and is therefore false (`assembly/HalfRefute.lean`,
`assembly/CoalesceRefute.lean`): the lockstep family `X i k = k - [i = i₁](n+1)` has
`d_r = L` and never coalesces, and it carries no local-good data at all.  The paper's `(half)`
is instead the deterministic content of the local-good event `𝒢_{r,L,T}`.

This file states and proves that repaired clause **uniform in the scale**, on exactly the
clause layer that `M1C.coalescence_of_blockClauses` consumes:

    exists L₀, ∀ L ≥ L₀, ∀ r ≥ C₀ L, ∀ (actual nearest-neighbour record family at scale L
      with its block clauses, its (locmart), its local-good field and the per-scale
      vanishing allowances),

      the carrier {d_r ≤ L} and (time) force   2 d_{r+BL} ≤ L.

The per-scale vanishing allowances are measured against one fixed profile `ε → 0`:
`η ≤ ε_L L`, `η^L ≤ ε_L L` and `C_T L^{3/4} ≤ ε_L L`.  These are exactly the rates that
`M1C.coalescence_of_blockClauses` needs; the uniform statement keeps them per-scale because
the underlying estimates are per-scale (`M2Meet` needs `η_n/L_n → 0`, `M4Coincide` needs
`η^L_n ≤ ε₁ n L_n`).

## Proof

The proof is the published contradiction argument of
`DefectKnotUniform.exists_uniform_half_of_knot_coalescence` (failure of uniformity gives a
sequence of `L → ∞` counterexamples; `FluidInterpolation.exists_record_interpolated_limit_subseq`
selects a compactness limit; `thetaL` selects one fluid time `θ_n → θ ≥ B`; the limit is
coalesced at `θ` by `M1C.coalesced_at_theta_of_clauses`; then
`DefectKnot.half_eventually_of_coalesced` contradicts the counterexamples), with the clause
data carried along the sequence.  No new probabilistic input appears: the probability that a
trajectory carries the clause layer is exactly what the measured window package has to
supply, and is not claimed here.

## Scope

Deterministic.  The conclusion is **not** `M4D.UniformHalfClause` (which is refuted) and is
**not** claimed for arbitrary record families: the clause layer is a hypothesis.  No `κ`,
no `arrayMeasure`, no `N`/`m`/`p` regime, no velocity.
-/
import Swarm.M1Block
import Swarm.DefectKnotUniform

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace M1C

open FluidMerge FluidInterpolation FluidLimit RecordDefect JoinStep FluidJoin

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The paper's `(BTchoice)` display supplies the scalar margin `hbb`.**  With the window
constant `⌈C⌉₊`, `b = 2C²` and `N = card ι`, the displayed inequality
`(1 + 64⌈C⌉₊)(1 + b)^N + 2 < B` implies `(1 + 64⌈C⌉₊)(1 + b)^{N-1} - 1 < B - 2`.  (This is the
published `FluidMerge.paper_margin_of_BTchoice`, recorded here at the actual constants so that
the margin of `half_from_clauses`/`coalescence_of_clauses` is verifiably the paper's.) -/
theorem hbb_of_BTchoice {C : ℝ} {B : ℕ}
    (hchoice : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι) + 2
      < (B : ℝ)) :
    (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2 :=
  FluidMerge.paper_margin_of_BTchoice (N := Fintype.card ι) (C := (Nat.ceil C : ℝ))
    (b := 2 * C ^ 2) (B := B) (by positivity) (by positivity) hchoice

/-- **The paper's `(half)` on the clause layer, uniformly in the scale.**

`C₀`, `B`, `T` and `C, C_T` are the paper's schedule constants; `ε → 0` is the single
vanishing profile against which the three finite-scale allowances are measured at each scale.
Every other hypothesis is a per-scale deterministic statement about the actual
nearest-neighbour record family.

**On `ε` (non-vacuity).**  The premises ask `CT L^{3/4} ≤ ε L · L`, i.e.
`ε L ≥ CT L^{-1/4}`; so `ε` must be a profile that decays *slower* than `L^{-1/4}`
(e.g. `ε L = L^{-1/8}`) for the class to be non-empty at large `L`.  That is exactly the shape
of a family carrying the clause layer: `CT L^{3/4} ≤ η` and `η ≤ ε L · L` force
`η/L → 0` while `CT L^{-1/4} ≤ η/L`, and any such family is dominated by some `ε → 0`
(namely `ε L = max (η_L/L, η^L_L/L, CT L^{-1/4})`, which tends to `0`).  So the quantified
class is precisely “the clause layer with vanishing allowances”, not an empty one. -/
theorem half_from_clauses (C₀ B Tn : ℕ) (hTn : (0 : ℝ) ≤ (Tn : ℝ)) (hB0 : (0 : ℝ) ≤ (B : ℝ))
    {C CT : ℝ} (hC : 1 ≤ C) (hCT : 0 ≤ CT) (hT64 : 64 * Nat.ceil C ≤ Tn)
    (hC₀ : Tn + 3 ≤ C₀)
    (hbb : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ)) (hcard : 2 ≤ Fintype.card ι) (μ : ℝ)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ)
        (η ηL : ℕ),
      IsRecord X τ → (∀ i m, |X i (m + 1) - X i m| = 1) → defect X τ r ≤ (L : ℤ) →
      τ (r + B * L) - τ r ≤ Tn * L →
      BlkCoin.BlockClauses X τ H C CT Tn L r →
      MartClause X τ A μ CT Tn L r →
      Glue.LocalField X τ H C CT Tn L r ηL →
      1 ≤ L → Numerics C CT L →
      CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) →
      (η : ℝ) ≤ ε L * (L : ℝ) →
      ((ηL : ℕ) : ℝ) ≤ ε L * (L : ℝ) →
      CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε L * (L : ℝ) →
      2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ L : ℕ, n + 1 ≤ L ∧ ∃ r : ℕ, C₀ * L ≤ r ∧
      ∃ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ)
        (η ηL : ℕ),
        IsRecord X τ ∧ (∀ i m, |X i (m + 1) - X i m| = 1) ∧
        defect X τ r ≤ (L : ℤ) ∧ τ (r + B * L) - τ r ≤ Tn * L ∧
        BlkCoin.BlockClauses X τ H C CT Tn L r ∧
        MartClause X τ A μ CT Tn L r ∧
        Glue.LocalField X τ H C CT Tn L r ηL ∧
        1 ≤ L ∧ Numerics C CT L ∧
        CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ) ∧
        (η : ℝ) ≤ ε L * (L : ℝ) ∧
        ((ηL : ℕ) : ℝ) ≤ ε L * (L : ℝ) ∧
        CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε L * (L : ℝ) ∧
        (L : ℤ) < 2 * defect X τ (r + B * L) :=
    fun n => hcon (n + 1)
  choose L hLn r hrL X τ H A η ηL hrec hNN hd htime hBC hM hLF hL1 hnum hηdef hηN hηLN
    hctN hbad using hseq
  -- the scale grows
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := L) (fun n => by have := hLn n; omega)
      tendsto_id
  have hLpos : ∀ n, 0 < L n := fun n => by have := hLn n; omega
  -- the record window starts at `(T+3)L ≤ r`
  have hr : ∀ n, (Tn + 3) * L n ≤ r n :=
    fun n => le_trans (Nat.mul_le_mul_right (L n) hC₀) (hrL n)
  -- one fluid time inside `[B, T]`
  have hlow : ∀ n, (B : ℝ) ≤ DefectKnot.thetaL (τ n) B (r n) (L n) :=
    fun n => DefectKnot.theta_mem_lower (hrec n) (hNN n) (hLpos n)
  have hup : ∀ n, DefectKnot.thetaL (τ n) B (r n) (L n) ≤ (Tn : ℝ) :=
    fun n => DefectKnot.theta_mem_upper (htime n) (hLpos n)
  obtain ⟨θ, hθmem, ψ, hψ, hθtend⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => DefectKnot.thetaL (τ n) B (r n) (L n)) (fun n => ⟨hlow n, hup n⟩)
  -- a compactness limit along a further subsequence
  obtain ⟨x, φ, hφ, _hxlip, _hxbound, hxconv, _hxstart, _hlarge', _hscale', _hd', _hsample⟩ :=
    FluidInterpolation.exists_record_interpolated_limit_subseq C₀ (Tn : ℝ) hTn
      (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n)) (fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hrL (ψ n)) (hLtop.comp hψ.tendsto_atTop)
      (fun n => hLpos (ψ n)) (fun n => hd (ψ n)) ⟨0, ⟨le_rfl, hTn⟩⟩ rfl
      (fun n i k => hNN (ψ n) i k)
  -- the two distinct indices the meeting rule needs
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : ι, i₀ ≠ j₀ := by
    have h1 : 1 < Fintype.card ι := by omega
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h1 a
    exact ⟨b, a, hb⟩
  -- the coalescence of the limit at `θ`, from the clause layer
  have hcoal : ∀ i j : ι,
      x i ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩ = x j ⟨(θ : ℝ), hB0.trans hθmem.1, hθmem.2⟩ := by
    intro i j
    have hθtendφ : Tendsto
        (fun n => DefectKnot.thetaL (τ (ψ (φ n))) B (r (ψ (φ n))) (L (ψ (φ n))))
        atTop (𝓝 (θ : ℝ)) := hθtend.comp hφ.tendsto_atTop
    -- the vanishing profiles at the reindexed scale
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
    refine coalesced_at_theta_of_clauses
      (scale := fun n => L (ψ (φ n))) (level := fun n => r (ψ (φ n)))
      (eta := fun n => η (ψ (φ n))) (etaL := fun n => ηL (ψ (φ n)))
      (H := fun n => H (ψ (φ n))) (A := fun n => A (ψ (φ n))) (μ := μ)
      (C := C) (CT := CT) (T := Tn) (B := B)
      (fun n => hLpos (ψ (φ n))) ((hLtop.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop)
      (fun n => hrec (ψ (φ n))) (fun n i m => hNN (ψ (φ n)) i m)
      (fun n => (hBC (ψ (φ n))).base) (fun n => hM (ψ (φ n)))
      (fun n => hLF (ψ (φ n))) (fun n => groupGrow_of_blockClauses (hBC (ψ (φ n))))
      hC hCT (fun n => hd (ψ (φ n))) (fun n => hr (ψ (φ n))) (fun n => hL1 (ψ (φ n)))
      hij (fun n => hnum (ψ (φ n))) hT64 (fun n => hηdef (ψ (φ n))) hratio
      hcomp hcomp (fun n => hηLN (ψ (φ n))) (fun n => hctN (ψ (φ n)))
      (x := x) (fun i => hxconv i) hbb hBT ?_ i j
    exact hθmem.1
  -- the eventual `(half)` clause, and the contradiction with the counterexamples
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


