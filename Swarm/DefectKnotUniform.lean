/-
# Uniform scale threshold for the halving clause from knot coalescence

`DefectKnot` proves the exact knot identity and that `(half)` holds eventually along a
subsequence whose knot configurations coalesce in the limit.  This file removes the
subsequence and states the **uniform threshold** form of the source's conclusion: if the
fluid limit of every admissible record sequence is coalesced at the knot time, then there is
an integer `L₀` such that, for *every* integer `L ≥ L₀`, *every* `r ≥ C₀ L` and *every*
actual nearest-neighbour walker family with first-passage record times, the halving clause
`2 * d_{r+BL} <= L` holds on `{d_r <= L} ∩ {(time)}`.

The hypothesis `hcoal` is the source's `(5.6)`/`(5.12)` (`x_1(u) = ... = x_N(u)` for
`u >= s_*`, together with `R(theta) = B`) restricted to `theta ∈ [B, T]` and read at the
exact knot.  Nothing stronger is used: by `DefectKnot.spread_ge_half_of_half_fails`, a
persistent failure of `(half)` already forces a non-coalesced limit knot configuration, so
coalescence is not an artefact of the formulation.
-/
import Swarm.DefectKnot

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

set_option linter.unusedSectionVars false

namespace DefectKnot

open FluidInterpolation FluidLimit RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Composing the index of a uniformly convergent family with a strictly increasing map
preserves uniform convergence. -/
theorem tendstoUniformly_comp_strictMono {F : ℕ → ι → ℝ} {f : ι → ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (h : TendstoUniformly F f atTop) :
    TendstoUniformly (fun n => F (φ n)) f atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  exact hφ.tendsto_atTop.eventually (h ε hε)

/-- **The knot configurations converge to the fluid value at the knot.**

Uniform convergence of the literal record interpolants and `theta_L -> theta` give
convergence of the scaled positions at the exact knot `tau_{r+BL}`, with a varying knot
index, to the fluid limit at the fluid time `theta`.  `theta ∈ [B, Tn]` supplies the
horizon bound `knotIdx <= rawHorizon`. -/
theorem knotConf_tendsto_of_uniform {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {B Tn : ℕ}
    (hB0 : (0 : ℝ) ≤ (B : ℝ))
    {level scale : ℕ → ℕ} (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (htime : ∀ n, τ n (level n + B * scale n) - τ n (level n) ≤ Tn * scale n)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t)
      atTop)
    {θ : Set.Icc (0 : ℝ) (Tn : ℝ)} (hθB : (B : ℝ) ≤ (θ : ℝ))
    (hθtend : Tendsto (fun n => thetaL (τ (φ n)) B (level (φ n)) (scale (φ n))) atTop
      (𝓝 (θ : ℝ)))
    (i : ι) :
    Tendsto (fun n => knotConf X τ B level scale (φ n) i) atTop (𝓝 (x i θ)) := by
  have hlow : ∀ n, (B : ℝ) ≤ thetaL (τ (φ n)) B (level (φ n)) (scale (φ n)) :=
    fun n => theta_mem_lower (hτ (φ n)) (hNN (φ n)) (hscale (φ n))
  have hup : ∀ n, thetaL (τ (φ n)) B (level (φ n)) (scale (φ n)) ≤ (Tn : ℝ) :=
    fun n => theta_mem_upper (htime (φ n)) (hscale (φ n))
  have h0 : ∀ n, (0 : ℝ) ≤ thetaL (τ (φ n)) B (level (φ n)) (scale (φ n)) :=
    fun n => hB0.trans (hlow n)
  have hk : ∀ n, knotIdx (τ (φ n)) B (level (φ n)) (scale (φ n)) ≤
      rawHorizon (Tn : ℝ) (scale (φ n)) := by
    intro n
    have h1 : (knotIdx (τ (φ n)) B (level (φ n)) (scale (φ n)) : ℝ) / (scale (φ n) : ℝ)
        ≤ (Tn : ℝ) := hup n
    rw [div_le_iff₀ (by exact_mod_cast hscale (φ n))] at h1
    exact Nat.le_floor (by linarith)
  have htend : Tendsto
      (fun n => (⟨thetaL (τ (φ n)) B (level (φ n)) (scale (φ n)), ⟨h0 n, hup n⟩⟩ :
        Set.Icc (0 : ℝ) (Tn : ℝ))) atTop (𝓝 θ) :=
    tendsto_subtype_rng.2 hθtend
  exact knot_tendsto_of_uniform (X := fun n => X (φ n)) (τ := fun n => τ (φ n))
    (level := fun n => level (φ n)) (scale := fun n => scale (φ n))
    (fun n => hscale (φ n)) (T := (Tn : ℝ)) hconv
    (k := fun n => knotIdx (τ (φ n)) B (level (φ n)) (scale (φ n)))
    (t := fun n => ⟨thetaL (τ (φ n)) B (level (φ n)) (scale (φ n)), ⟨h0 n, hup n⟩⟩)
    (tlim := θ) (fun n => rfl) hk htend i

/-- **Uniform threshold for the halving clause.**  If every admissible record sequence has a
coalesced fluid limit at the knot time in `[B, T]`, then `(half)` holds for all sufficiently
large scales `L`, uniformly over the starting level `r ≥ C₀ L` and over *all* actual
nearest-neighbour walker families with first-passage record times, on the event
`{d_r ≤ L} ∩ {(time)}`. -/
theorem exists_uniform_half_of_knot_coalescence (C₀ B Tn : ℕ) (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hB0 : (0 : ℝ) ≤ (B : ℝ))
    (hcoal : ∀ (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
      (hτ : ∀ n, IsRecord (X n) (τ n))
      (hlarge : ∀ n, C₀ * scale n ≤ level n)
      (hscaleTop : Tendsto scale atTop atTop)
      (hscale : ∀ n, 0 < scale n)
      (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
      (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
      (htime : ∀ n, τ n (level n + B * scale n) - τ n (level n) ≤ Tn * scale n)
      (x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ →
      (∀ i, TendstoUniformly
        (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t)
        atTop) →
      ∀ θ : Set.Icc (0 : ℝ) (Tn : ℝ), (B : ℝ) ≤ (θ : ℝ) → ∀ i j, x i θ = x j θ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ), IsRecord X τ →
        (∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) →
        defect X τ r ≤ (L : ℤ) → τ (r + B * L) - τ r ≤ Tn * L →
        2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ L : ℕ, n + 1 ≤ L ∧ ∃ r : ℕ, C₀ * L ≤ r ∧
      ∃ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ), IsRecord X τ ∧
        (∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) ∧
        defect X τ r ≤ (L : ℤ) ∧ τ (r + B * L) - τ r ≤ Tn * L ∧
        (L : ℤ) < 2 * defect X τ (r + B * L) :=
    fun n => hcon (n + 1)
  choose L hLn r hrL X τ hrec hNN hd htime hbad using hseq
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := L) (fun n => by have := hLn n; omega)
      tendsto_id
  have hLpos : ∀ n, 0 < L n := fun n => by have := hLn n; omega
  have hlow : ∀ n, (B : ℝ) ≤ thetaL (τ n) B (r n) (L n) :=
    fun n => theta_mem_lower (hrec n) (hNN n) (hLpos n)
  have hup : ∀ n, thetaL (τ n) B (r n) (L n) ≤ (Tn : ℝ) :=
    fun n => theta_mem_upper (htime n) (hLpos n)
  obtain ⟨θ, hθmem, ψ, hψ, hθtend⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => thetaL (τ n) B (r n) (L n)) (fun n => ⟨hlow n, hup n⟩)
  obtain ⟨x, φ, hφ, hxlip, hxbound, hxconv, hxstart, hlarge', hscale', hd', hsample⟩ :=
    exists_record_interpolated_limit_subseq C₀ (Tn : ℝ) hTn
      (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n)) (fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hrL (ψ n)) (hLtop.comp hψ.tendsto_atTop)
      (fun n => hLpos (ψ n)) (fun n => hd (ψ n)) ⟨0, ⟨le_rfl, hTn⟩⟩ rfl
      (fun n i k => hNN (ψ n) i k)
  have hcoaleq := hcoal (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n))
    (fun n => L (ψ n)) (fun n => hrec (ψ n)) (fun n => hrL (ψ n))
    (hLtop.comp hψ.tendsto_atTop) (fun n => hLpos (ψ n)) (fun n => hd (ψ n))
    (fun n i k => hNN (ψ n) i k) (fun n => htime (ψ n)) x φ hφ hxconv
    ⟨θ, hB0.trans hθmem.1, hθmem.2⟩ hθmem.1
  have hθtend' : Tendsto (fun n => thetaL (τ (ψ n)) B (r (ψ n)) (L (ψ n))) atTop (𝓝 θ) :=
    hθtend
  have hθtendφ : Tendsto (fun n => thetaL (τ (ψ (φ n))) B (r (ψ (φ n))) (L (ψ (φ n))))
      atTop (𝓝 θ) := hθtend'.comp hφ.tendsto_atTop
  have hlim : ∀ i, Tendsto (fun n => knotConf (fun n => X (ψ (φ n)))
      (fun n => τ (ψ (φ n))) B (fun n => r (ψ (φ n))) (fun n => L (ψ (φ n))) n i)
      atTop (𝓝 (x i ⟨θ, hB0.trans hθmem.1, hθmem.2⟩)) :=
    fun i => knotConf_tendsto_of_uniform (X := fun n => X (ψ n)) (τ := fun n => τ (ψ n))
      (B := B) (Tn := Tn) hB0 (level := fun n => r (ψ n)) (scale := fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hLpos (ψ n)) (fun n i k => hNN (ψ n) i k)
      (fun n => htime (ψ n)) hφ hxconv hθmem.1 hθtendφ i
  have hev := half_eventually_of_coalesced (X := fun n => X (ψ (φ n)))
    (τ := fun n => τ (ψ (φ n))) (B := B) (level := fun n => r (ψ (φ n)))
    (scale := fun n => L (ψ (φ n))) (fun n => hrec (ψ (φ n)))
    (fun n => hLpos (ψ (φ n)))
    (y := fun i => x i ⟨θ, hB0.trans hθmem.1, hθmem.2⟩) hlim hcoaleq
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hev] with n hn
    exact (not_le.2 (hbad (ψ (φ n)))) hn
  exact hfalse.exists.elim (fun n hn => hn)
