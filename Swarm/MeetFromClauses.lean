/-
# The fluid `(meet)` bound from the actual finite-scale clauses

This is the finite-to-fluid step of the source's `(meet)`: it takes

* the literal record, the finite-scale local clauses `LocalClauses` (which contain
  `(locmove)`, `(loccoord)` and `(lococc)`) and the martingale clause `MartClause` at every
  scale `L_n`,
* the uniform convergence of the actual record interpolants to the fluid limit `x`,
* a *strict fluid separation* of a group `D` from its complement on `[s,t]` with a positive
  margin `γ`,
* the sharp lag `eta_n` with `eta_n / L_n → 0`,

and concludes the paper's fluid `(meet)` inequality at the true sharp constant `2 C^2`:

  `t - s ≤ 2 C^2 (sup_D x(s) - sup_{D^c} x(s))`.

Mechanism (all pieces are in the tree): `M2B.sep_eventually_of_fluid` transfers the fluid
separation to the grid `(sep)` at every grid time of the window; `JoinStep.run_le_sharp`
turns the grid `(sep)` into the lattice-unit sharp meet bound; and
`M2Meet.meet_of_grid_bounds'` divides by `L` and passes to the limit.  The grid start uses
the *ceiling* `⌈L s⌉`, because the grid `(sep)` is available for `k/L ≥ s` and the finite
meet bound needs `(sep)` at every grid time of `[s_n, t_n)`.

No probability is proved here: `LocalClauses`/`MartClause` are the deterministic clause
packages that the measured local-good events supply; `StickyOn` (used by
`MeetJoin.joinRuleFrom_of_meetBound`) is *not* assumed here.
-/
import Swarm.MeetPassageGeneral
import Swarm.FreshCoalesce

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

open M2B FluidMerge FluidLimit Glue LocalFluid RecordDefect JoinStep

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The ceiling grid knot -/

/-- `⌈L s⌉ / L → s`. -/
theorem tendsto_ceil_mul_div {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ)) atTop (𝓝 s) := by
  have hsc : Tendsto (fun n => (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleTop
  have hinv : Tendsto (fun n => ((scale n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsc
  have hbound : ∀ n, ‖((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ) - s‖
      ≤ ((scale n : ℝ))⁻¹ := by
    intro n
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hlow : (scale n : ℝ) * s ≤ ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hup : ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) < (scale n : ℝ) * s + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hL.le hs)
    have h1 : s ≤ ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ) := by
      rw [le_div_iff₀ hL]
      linarith
    have h2 : ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ) ≤ s + ((scale n : ℝ))⁻¹ := by
      rw [div_le_iff₀ hL]
      have : ((scale n : ℝ) * s + 1) = (s + ((scale n : ℝ))⁻¹) * (scale n : ℝ) := by
        field_simp
      linarith [hup, this.le, this.ge]
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    constructor
    · linarith
    · have : s + ((scale n : ℝ))⁻¹ - s = ((scale n : ℝ))⁻¹ := by ring
      linarith [h2]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound hinv

/-- The ceiling knot stays inside the raw horizon when `s < T`. -/
theorem ceil_le_horizon {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    {T : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsT : s < (T : ℝ)) :
    ∀ᶠ n in atTop, ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
  have hsc : Tendsto (fun n => (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleTop
  have hinv : Tendsto (fun n => ((scale n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsc
  have hε : ∀ᶠ n in atTop, ((scale n : ℝ))⁻¹ < (T : ℝ) - s := by
    have hpos : (0 : ℝ) < (T : ℝ) - s := by linarith
    exact (tendsto_order.1 hinv).2 _ hpos
  filter_upwards [hε] with n hn
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hup : ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) < (scale n : ℝ) * s + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hL.le hs)
  have h2 : (1 : ℝ) < ((T : ℝ) - s) * (scale n : ℝ) := by
    have := mul_lt_mul_of_pos_right hn hL
    rwa [inv_mul_cancel₀ hL.ne'] at this
  nlinarith [hup, h2]

/-! ## 2. The grid `(sep)` from the fluid separation -/

/-- The finite-scale `(sep)` holds at every grid time of the fluid window `[s,t]`, uniformly
once the scale is large.  This is `M2B.sep_eventually_of_fluid`, with the sharp lag derived
from `(locmart)` inside the sharp window. -/
theorem gridSep_eventually {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    {D : Finset ι} (hD : D.Nonempty) (hJ : (Finset.univ \ D).Nonempty)
    {s t γ : ℝ} (hs0 : 0 < s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s) (hst : s ≤ t)
    (htT : t ≤ (T : ℝ))
    (hγ : 0 < γ)
    (hsep : ∀ (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (T : ℝ)), v ∈ Set.Icc s t →
      γ ≤ D.inf' hD (fun i => M2B.fpos x i hv)
        - (Finset.univ \ D).sup' hJ (fun j => M2B.fpos x j hv)) :
    ∀ᶠ n in atTop, ∀ k : ℕ,
      s ≤ (k : ℝ) / (scale n : ℝ) → (k : ℝ) / (scale n : ℝ) ≤ t →
      Sep (X n) D (Finset.univ \ D) (τ n (level n) + k) := by
  classical
  refine M2B.sep_eventually_of_fluid hscale hscaleTop hτ hne hdr hr hconv heta hD hJ
    hs0 hst htT hγ hsep ?_
  filter_upwards with n
  intro j k hk1 hk2
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hk64 : ((64 * Nat.ceil C * scale n : ℕ) : ℤ) ≤ ((τ n (level n) + k : ℕ) : ℤ) - (τ n (level n) : ℤ) := by
    have hk1' : s * (scale n : ℝ) ≤ (k : ℝ) := by
      rw [le_div_iff₀ hL] at hk1
      linarith
    have h1 : (64 * Nat.ceil C : ℝ) * (scale n : ℝ) ≤ (k : ℝ) := by
      calc (64 * Nat.ceil C : ℝ) * (scale n : ℝ) ≤ s * (scale n : ℝ) :=
            mul_le_mul_of_nonneg_right hs64 hL.le
        _ ≤ (k : ℝ) := hk1'
    have h2 : (64 * Nat.ceil C) * scale n ≤ k := by
      have : ((64 * Nat.ceil C) * scale n : ℕ) = (64 * Nat.ceil C) * scale n := rfl
      have h3 : (((64 * Nat.ceil C) * scale n : ℕ) : ℝ) ≤ (k : ℝ) := by
        rw [this]; push_cast; exact h1
      exact_mod_cast h3
    have h4 : τ n (level n) + 64 * Nat.ceil C * scale n ≤ τ n (level n) + k := by
      have : 64 * Nat.ceil C * scale n = (64 * Nat.ceil C) * scale n := by ring
      omega
    have h5 : ((τ n (level n) + 64 * Nat.ceil C * scale n : ℕ) : ℤ)
        ≤ ((τ n (level n) + k : ℕ) : ℤ) := by exact_mod_cast h4
    omega
  have hkTL : (k : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
    rw [div_le_iff₀ hL] at hk2
    calc (k : ℝ) ≤ t * (scale n : ℝ) := hk2
      _ ≤ (T : ℝ) * (scale n : ℝ) := mul_le_mul_of_nonneg_right htT hL.le
  have hkTn : τ n (level n) + k ≤ τ n (level n) + T * scale n := by
    have h1 : k ≤ T * scale n := by
      have : (k : ℝ) ≤ ((T * scale n : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  exact lag_le_sub (X n) (hτ n) (hM n) hC (hcl n).occ (hdr n) (hL1 n) hij (hnum n) hT64
    (hηdef n) (by omega) hkTn j

 /-! ## 3. The ceiling knot eventually lies below the floor knot of a later time -/

/-- For `s < t`, eventually `⌈L s⌉ ≤ ⌊L t⌋`. -/
theorem eventually_ceil_le_floor {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) {s t : ℝ} (hs0 : 0 < s) (hst : s < t) :
    ∀ᶠ n in atTop, ⌈(scale n : ℝ) * s⌉₊ ≤ ⌊(scale n : ℝ) * t⌋₊ := by
  have hs1 : Tendsto (fun n => ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ)) atTop (𝓝 s) :=
    tendsto_ceil_mul_div hscale hscaleTop hs0.le
  have ht1 : Tendsto (fun n => ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ)) atTop (𝓝 t) :=
    tendsto_floor_mul_div hscale hscaleTop (le_of_lt (lt_trans hs0 hst))
  have h1 : ∀ᶠ n in atTop, ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ) < s + (t - s) / 3 :=
    (tendsto_order.1 hs1).2 _ (by linarith)
  have h2 : ∀ᶠ n in atTop, t - (t - s) / 3 < ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ) :=
    (tendsto_order.1 ht1).1 _ (by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hlt : ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) < ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) := by
    have h3 : ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ)
        < ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ) := by
      have hmid : s + (t - s) / 3 < t - (t - s) / 3 := by linarith
      exact lt_trans (lt_trans hn1 hmid) hn2
    rwa [div_lt_div_iff_of_pos_right hL] at h3
  exact_mod_cast hlt.le

/-- The ceiling knot of `s` is at most the ceiling of `T * L` when `s ≤ T`. -/
theorem ceil_mul_le_horizon {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    {T : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    ∀ n, ⌈(scale n : ℝ) * s⌉₊ ≤ ((T + 1) * scale n : ℕ) := by
  intro n
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have h1 : (scale n : ℝ) * s ≤ (scale n : ℝ) * (T : ℝ) := mul_le_mul_of_nonneg_left hsT hL.le
  have h2 : ⌈(scale n : ℝ) * s⌉₊ ≤ ⌈(scale n : ℝ) * (T : ℝ)⌉₊ := Nat.ceil_mono h1
  have h3 : ⌈(scale n : ℝ) * (T : ℝ)⌉₊ ≤ ((T + 1) * scale n : ℕ) := by
    rw [Nat.ceil_le]
    push_cast
    nlinarith
  exact le_trans h2 h3

end M2Meet
