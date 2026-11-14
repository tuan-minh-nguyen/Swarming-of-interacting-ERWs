/-
# The sharp coalescence time from fluid coalescence

`FluidCoincide.spreadS_eventually_le_of_coincidence` is the source's `(4.1)`+`(4.8)`: fluid
coincidence of a group on `[s,T]` makes the finite-scale spread of that group `o(L)` at *every*
grid time of `[sL, TL]`.  This file reads that statement in the shape the sharp `(half)` clause
consumes, and in the constants it consumes.

* `coincideOn_of_rule` -- the paper's `(4.9)` persistence read as a rule: if whole-pack
  coincidence, once true at a time `u >= s`, holds at every later time of `[s,T]`, then
  coincidence at the single coalescence time propagates to the whole interval.
* `spreadS_univ_of_coalescence_time` -- whole-pack spread `o(L)` at every grid time after the
  coalescence time, from coincidence at that single time plus the rule.
* `exists_small_spread_knot` -- the existence form: eventually there is a grid time strictly
  after the fluid coalescence time, inside the fluid window, at which the whole-pack spread is
  at most `b L`.
* `exists_coalescence_time_sharp` -- **the sharp `(half)` premise triple**, in the exact
  constants of `JoinStep.halving_of_coalesce_sharp`: for all sufficiently large scales there is
  `t` with `tau_r + 64 ceil(C) L <= t`, `t <= tau_{r+BL}` and `spreadS univ t <= HalfEps C N L`.
  The caller places the grid knot `m` (explicit comparisons); no probability, no
  `NoCoalescence`, no stationary law.

Every statement is deterministic and eventual in the scale; the only inputs are the accepted
uniform convergence of the raw samples and the fluid coalescence of the limit.
-/
import Swarm.CoincideLimit
import Swarm.HalvingResidual

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidCoincide

open FluidInterpolation FluidLimit Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The persistence rule `(4.9)` and the single-time hypothesis -/

/-- **The paper's `(4.9)` used as a rule.**  If whole-pack coincidence, once true at a time
`u >= s`, is true at every later time of `[s,T]`, then coincidence at the single time `s`
propagates to the whole interval. -/
theorem coincideOn_of_rule {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)} {s : ℝ}
    (hs0 : 0 ≤ s) (hsT : s ≤ T)
    (hrule : ∀ (u v : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → (u : ℝ) ≤ (v : ℝ) → (v : ℝ) ≤ T →
      (∀ i j : ι, x i u = x j u) → ∀ i j : ι, x i v = x j v)
    (h0 : ∀ i j : ι, x i ⟨s, hs0, hsT⟩ = x j ⟨s, hs0, hsT⟩) :
    ∀ (v : Set.Icc (0 : ℝ) T), s ≤ (v : ℝ) → ∀ i j : ι, x i v = x j v := by
  intro v hv i j
  exact hrule ⟨s, hs0, hsT⟩ v le_rfl hv v.2.2 h0 i j

/-- **Whole-pack spread `o(L)` at every grid time after the coalescence time**, from
coincidence at that single fluid time plus the persistence rule. -/
theorem spreadS_univ_of_coalescence_time
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T)
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hrule : ∀ (u v : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → (u : ℝ) ≤ (v : ℝ) → (v : ℝ) ≤ T →
      (∀ i j : ι, x i u = x j u) → ∀ i j : ι, x i v = x j v)
    (h0 : ∀ i j : ι, x i ⟨s, hs0, hsT⟩ = x j ⟨s, hs0, hsT⟩)
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop, ∀ m : ℕ, s * (scale n : ℝ) ≤ (m : ℝ) → (m : ℝ) ≤ T * (scale n : ℝ) →
      ((spreadS (X n) (Finset.univ : Finset ι) (τ n (level n) + m) : ℤ) : ℝ)
        ≤ b * (scale n : ℝ) :=
  spreadS_univ_eventually_le_of_coalescence hscale (T := T) (s := s) hconv
    (fun v hv i j => coincideOn_of_rule hs0 hsT hrule h0 v hv i j) b hb

/-! ## 2. The existence form: one small-spread grid time after the coalescence time -/

/-- **Eventually there is a grid time, strictly after the fluid coalescence time and inside the
fluid window, at which the whole-pack spread is at most `b L`.**  This is the finite-scale
content of the source's `(4.8)` in existential form. -/
theorem exists_small_spread_knot
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {T : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hcoal : ∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i j : ι, x i u = x j u)
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop, ∃ m : ℕ, s * (scale n : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ T * (scale n : ℝ) ∧
      ((spreadS (X n) (Finset.univ : Finset ι) (τ n (level n) + m) : ℤ) : ℝ)
        ≤ b * (scale n : ℝ) := by
  -- the knot `ceil (s L)` and the room `1 <= (T - s) L` once `L` is large
  have hroom : ∀ᶠ n in atTop, (1 : ℝ) ≤ (T - s) * (scale n : ℝ) := by
    have hpos : (0 : ℝ) < T - s := by linarith
    have hcast : Tendsto (fun n : ℕ => (scale n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hscaleTop
    exact (Tendsto.const_mul_atTop hpos hcast).eventually_ge_atTop 1
  filter_upwards [spreadS_univ_eventually_le_of_coalescence (X := X) (τ := τ)
      (level := level) (scale := scale) hscale (T := T) (s := s) (x := x) hconv hcoal b hb,
    hroom] with n hn hroomn
  refine ⟨Nat.ceil (s * (scale n : ℝ)), Nat.le_ceil _, ?_, ?_⟩
  · have hscR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hceil : ((Nat.ceil (s * (scale n : ℝ)) : ℕ) : ℝ) < s * (scale n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hs0 hscR.le)
    nlinarith
  · exact hn _ (Nat.le_ceil _) (le_of_lt (by
      have hscR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
      have hceil : ((Nat.ceil (s * (scale n : ℝ)) : ℕ) : ℝ) < s * (scale n : ℝ) + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg hs0 hscR.le)
      nlinarith))

/-! ## 3. The sharp `(half)` premise triple -/

/-- **The sharp coalescence time in the exact constants of the `(half)` clause.**

For the actual per-scale family, once the fluid limit has all coordinates equal from the fluid
time `s` on, and the caller places the grid knot `m n` above `s L` and above the sharp start
`64 ceil(C) L`, below the fluid horizon `T L` and below the sharp window length
`tau_{r+BL} - tau_r`, there is for all sufficiently large scales a grid time `t` with

* `tau_r + 64 ceil(C) L <= t`  (the sharp lower endpoint of `(half)`),
* `t <= tau_{r+BL}`            (the sharp upper endpoint of `(half)`),
* `spreadS univ t <= HalfEps C N * L`  (the one coalescence-time hypothesis of
  `JoinStep.halving_of_coalesce_sharp`, with `N = |iota|`).

All four comparisons are hypotheses on the caller's schedule; no new analytic input appears. -/
theorem exists_coalescence_time_sharp
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {s : ℝ}
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hcoal : ∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i j : ι, x i u = x j u)
    {C : ℝ} (hC : 0 < C) {B : ℕ} (m : ℕ → ℕ)
    (hmS : ∀ᶠ n in atTop, s * (scale n : ℝ) ≤ (m n : ℝ))
    (hmSh : ∀ᶠ n in atTop,
      64 * (Nat.ceil C : ℝ) * (scale n : ℝ) ≤ (m n : ℝ))
    (hmT : ∀ᶠ n in atTop, (m n : ℝ) ≤ T * (scale n : ℝ))
    (hmB : ∀ᶠ n in atTop, τ n (level n) + m n ≤ τ n (level n + B * scale n)) :
    ∀ᶠ n in atTop, ∃ t : ℕ,
      τ n (level n) + 64 * Nat.ceil C * scale n ≤ t ∧
      t ≤ τ n (level n + B * scale n) ∧
      ((spreadS (X n) (Finset.univ : Finset ι) t : ℤ) : ℝ)
        ≤ JoinStep.HalfEps C (Fintype.card ι) * (scale n : ℝ) := by
  filter_upwards [spreadS_univ_eventually_le_of_coalescence (X := X) (τ := τ)
      (level := level) (scale := scale) hscale (T := T) (s := s) (x := x) hconv hcoal
      (JoinStep.HalfEps C (Fintype.card ι)) (JoinStep.HalfEps_pos hC _),
    hmS, hmSh, hmT, hmB] with n hsp hS hSh hT hB
  refine ⟨τ n (level n) + m n, ?_, hB, hsp _ hS hT⟩
  have hcast : (64 : ℕ) * Nat.ceil C * scale n
      = 64 * (Nat.ceil C : ℝ) * (scale n : ℝ) := by push_cast; ring
  have hSh' : ((64 : ℕ) * Nat.ceil C * scale n : ℝ) ≤ (m n : ℝ) := by
    rw [hcast]; exact hSh
  have : (64 : ℕ) * Nat.ceil C * scale n ≤ m n := by exact_mod_cast hSh'
  omega

/-- The rule-based form of `exists_coalescence_time_sharp`: coincidence at the single fluid time
`s` plus the persistence rule `(4.9)` replace coincidence on the whole interval. -/
theorem exists_coalescence_time_sharp_of_rule
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T)
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hrule : ∀ (u v : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → (u : ℝ) ≤ (v : ℝ) → (v : ℝ) ≤ T →
      (∀ i j : ι, x i u = x j u) → ∀ i j : ι, x i v = x j v)
    (h0 : ∀ i j : ι, x i ⟨s, hs0, hsT⟩ = x j ⟨s, hs0, hsT⟩)
    {C : ℝ} (hC : 0 < C) {B : ℕ} (m : ℕ → ℕ)
    (hmS : ∀ᶠ n in atTop, s * (scale n : ℝ) ≤ (m n : ℝ))
    (hmSh : ∀ᶠ n in atTop,
      64 * (Nat.ceil C : ℝ) * (scale n : ℝ) ≤ (m n : ℝ))
    (hmT : ∀ᶠ n in atTop, (m n : ℝ) ≤ T * (scale n : ℝ))
    (hmB : ∀ᶠ n in atTop, τ n (level n) + m n ≤ τ n (level n + B * scale n)) :
    ∀ᶠ n in atTop, ∃ t : ℕ,
      τ n (level n) + 64 * Nat.ceil C * scale n ≤ t ∧
      t ≤ τ n (level n + B * scale n) ∧
      ((spreadS (X n) (Finset.univ : Finset ι) t : ℤ) : ℝ)
        ≤ JoinStep.HalfEps C (Fintype.card ι) * (scale n : ℝ) :=
  exists_coalescence_time_sharp hscale hconv
    (fun u hu i j => coincideOn_of_rule hs0 hsT hrule h0 u hu i j) hC m hmS hmSh hmT hmB

end FluidCoincide
