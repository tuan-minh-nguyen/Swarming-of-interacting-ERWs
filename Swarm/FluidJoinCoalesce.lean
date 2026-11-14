/-
# From the paper's fluid inputs to the halving-clause coalescence premise

`FluidMerge.paper_fluid_coalesce_before_B_sub_two` proves the deterministic part of the
paper's step 6: a monotone one-speed fluid motion `FluidMotionOn`, the meeting rule
`JoinRuleFrom` (the source's `(meet)`, (4.14)-(4.15)) and coincidence on contact
`StickyOn` (the source's `(coincide)`, (4.9)) force full coalescence at a fluid time
below `B - 2`, persistently on the bounded window.  `DefectKnot` shows that the
halving clause `(half)` holds eventually exactly when the fluid knot configuration
coalesces, and `DefectKnotUniform.exists_uniform_half_of_knot_coalescence` states the
uniform scale threshold with that coalescence as the hypothesis `hcoal`, read at a
fluid time `θ ∈ [B, T]`.

This file connects the two statements and shrinks the hypothesis.  It proves

* `fluidMotionOn_of_tendsto_lower` -- the source's `(fluid)` (3.2).  The unit upper
  speed bound on the limit is separate (`hupper`, available from the compactness
  package's `LipschitzWith 1`), and the *monotonicity* is exactly the local-good
  one-sided estimate `X_t - X_s ≥ -E_L` of (3.1) divided by `L`; only `E_L / L → 0`
  is used.
* `coalesced_at_of_fluid` -- the source's (5.6) read at an arbitrary fluid time
  `θ ≥ B`, i.e. precisely the `hcoal` premise of `DefectKnot` in the shape in which
  `exists_uniform_half_of_knot_coalescence` consumes it.
* `fluidGap_zero_le_one`, `fluidGap_le_one_add` -- the source's (5.1) initial gap
  bound: on the literal event `{d_r ≤ L}` the fluid gap at the window origin is at
  most one, and hence at most `1 + 64C` at `s₀ = 64C`.  This discharges `hgap₀`.
* `LeaderPersist`, `joinRuleFrom_of_reaches` -- the paper's own reduction of `(meet)`
  to the stopping alternative (4.15) ("some outsider reaches the record before
  `s + b Δ(s)`") plus leader persistence, so that `JoinRuleFrom` is not a black box.

No probability, no stationary law and no `NoCoalescence` hypothesis is introduced.
Nothing here constructs the fluid limit or estimates the probability of a local good
event; `JoinRuleFrom` and `StickyOn` remain explicit premises below.
-/
import Swarm.FluidMergeLight
import Swarm.DefectKnotUniform

set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidJoin

open FluidMerge FluidInterpolation FluidLimit RecordDefect

/-! ## 1. The source's `(fluid)`: monotone one-speed fluid motion -/

/-- **The paper's (3.2) from the finite-scale data.**

Let `y n i t` be the finite-scale position of walker `i` at fluid time `t`, `x i t` its
pointwise limit, and suppose

* `x` already obeys the unit upper speed bound `x i t - x i s ≤ t - s` (the compactness
  package supplies `LipschitzWith 1` for the limit);
* `y` converges to `x` pointwise at every fluid time of the window;
* the finite-scale increment obeys the one-sided bound `y n i t - y n i s ≥ -ε n`
  (this is the local-good window estimate `X_t - X_s ≥ -E_L` of (3.1), normalised);
* `ε n → 0`.

Then `x` is the paper's monotone one-speed fluid path `(fluid)`.  Divisibility by the
scale is not used: only `ε n → 0`. -/
theorem fluidMotionOn_of_tendsto_lower
    {ι : Type*} {y : ℕ → ι → ℝ → ℝ} {x : ι → ℝ → ℝ} {s₀ T : ℝ} {ε : ℕ → ℝ}
    (hupper : ∀ i s t, s₀ ≤ s → s ≤ t → t ≤ T → x i t - x i s ≤ t - s)
    (hconv : ∀ i t, s₀ ≤ t → t ≤ T → Tendsto (fun n => y n i t) atTop (𝓝 (x i t)))
    (hε : Tendsto ε atTop (𝓝 0))
    (hlow : ∀ n i s t, s₀ ≤ s → s ≤ t → t ≤ T → -(ε n) ≤ y n i t - y n i s) :
    FluidMotionOn x s₀ T := by
  intro i s t hs hst htT
  refine ⟨?_, hupper i s t hs hst htT⟩
  have hs' : Tendsto (fun n => y n i s) atTop (𝓝 (x i s)) := hconv i s hs (hst.trans htT)
  have ht' : Tendsto (fun n => y n i t) atTop (𝓝 (x i t)) := hconv i t (hs.trans hst) htT
  have hlim : Tendsto (fun n => y n i t - y n i s) atTop (𝓝 (x i t - x i s)) := ht'.sub hs'
  have hneg : Tendsto (fun n => -(ε n)) atTop (𝓝 0) := by
    simpa using hε.neg
  have hge := le_of_tendsto_of_tendsto' hneg hlim (fun n => hlow n i s t hs hst htT)
  linarith

/-- A one-Lipschitz function on the compact fluid interval has the paper's unit upper
speed bound on `[0,T]`.  This is how `hupper` is discharged from the compactness
package's `∀ i, LipschitzWith 1 (x i)`. -/
theorem upper_speed_of_lipschitz_on_Icc {T : ℝ} {z : Set.Icc (0 : ℝ) T →ᵇ ℝ}
    (hz : LipschitzWith 1 z) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hst : s ≤ t) :
    z ⟨t, ht⟩ - z ⟨s, hs⟩ ≤ t - s := by
  have hdist : |z ⟨t, ht⟩ - z ⟨s, hs⟩| ≤ dist (⟨t, ht⟩ : Set.Icc (0 : ℝ) T) ⟨s, hs⟩ := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      hz.dist_le_mul ⟨t, ht⟩ ⟨s, hs⟩
  have hdt : dist (⟨t, ht⟩ : Set.Icc (0 : ℝ) T) ⟨s, hs⟩ = t - s := by
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s)]
  rw [hdt] at hdist
  exact (abs_le.mp hdist).2

/-! ## 2. The source's (5.6) at an arbitrary fluid time `θ ≥ B` -/

/-- **The paper's (5.6), read at `θ`.**  On the four fluid inputs of step 6 -- monotone
one-speed motion, the meeting rule, coincidence on contact, and the initial gap bound --
all fluid positions coincide at every fluid time `θ ∈ [B, T]`.  In particular this is
exactly the `hcoal` clause consumed by
`DefectKnot.exists_uniform_half_of_knot_coalescence`, whose `θ` is constrained to
`B ≤ θ ≤ Tn`.

The only content beyond `FluidMerge.paper_fluid_coalesce_before_B_sub_two` is the
elementary observation that the coalescence time `u` is below `B - 2 < B ≤ θ`. -/
theorem coalesced_at_of_fluid {N : ℕ} [Nonempty (Fin N)]
    {x : Fin N → ℝ → ℝ} {C b T : ℝ} {B : ℕ}
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hmove : FluidMotionOn x (64 * C) T)
    (hjoin : JoinRuleFrom x (64 * C) b T)
    (hsticky : StickyOn x (64 * C) T)
    (hBB : (1 + 64 * C) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < T)
    (hgap₀ : fluidGap (fun i => x i (64 * C)) ≤ 1 + 64 * C)
    {θ : ℝ} (hBθ : (B : ℝ) ≤ θ) (hθT : θ ≤ T) :
    ∀ i j, x i θ = x j θ := by
  obtain ⟨u, -, huB, hpers⟩ :=
    paper_fluid_coalesce_before_B_sub_two x hC hb hmove hjoin hsticky hBB hBT hgap₀
  exact hpers θ (by linarith) hθT

/-- **The paper's (5.6) at `θ`, in the generality of `DefectKnot`'s index type.**

`DefectKnot.exists_uniform_half_of_knot_coalescence` is stated for an arbitrary finite
nonempty index type, while the paper form `Fin N` is the application.  This is the same
bridge as `coalesced_at_of_fluid`, proved directly from
`FluidMerge.exists_persistent_coalescence`, so that the halving-clause package can be
re-parameterised without a `Fin N` translation. -/
theorem coalesced_at_of_fluid_card {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ι → ℝ → ℝ} {C b T : ℝ} {B : ℕ}
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hmove : FluidMotionOn x (64 * C) T)
    (hjoin : JoinRuleFrom x (64 * C) b T)
    (hsticky : StickyOn x (64 * C) T)
    (hBB : (1 + 64 * C) * (1 + b) ^ (Fintype.card ι - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < T)
    (hgap₀ : fluidGap (fun i => x i (64 * C)) ≤ 1 + 64 * C)
    {θ : ℝ} (hBθ : (B : ℝ) ≤ θ) (hθT : θ ≤ T) :
    ∀ i j, x i θ = x j θ := by
  have hD : 0 ≤ 1 + 64 * C := by linarith
  have hstart : 64 * C ≤ (1 + 64 * C) - 1 := le_of_eq (by ring)
  obtain ⟨u, -, hu, -, hpersist⟩ :=
    exists_persistent_coalescence x (64 * C) b (1 + 64 * C) T
      hmove hjoin hsticky hD hb (hBB.trans hBT) hstart hgap₀
  exact hpersist θ (by linarith) hθT

/-! ## 3. The source's (5.1): the initial gap bound from the literal event `{d_r ≤ L}` -/

/-- **The paper's (5.1) at the window origin.**  On `{d_r ≤ L}`, every scaled position at
the record origin lies in `[-1, 0]`, hence the fluid gap there is at most one.  This is
`FluidLimit.scaledPosition_at_record_mem` read through the limit: pointwise convergence
preserves both one-sided bounds, and no continuity of the supremum is needed. -/
theorem fluidGap_zero_le_one {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    {x : ι → ℝ}
    (hconv : ∀ i, Tendsto (fun n =>
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0) atTop (𝓝 (x i))) :
    fluidGap x ≤ 1 := by
  have hmem : ∀ n i,
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0 ∈ Set.Icc (-1 : ℝ) 0 :=
    fun n i => scaledPosition_at_record_mem (X n) (τ n) (hτ n) (level n) (scale n)
      (hscale n) (hd n) i
  have hmax : ∀ i, x i ≤ 0 := fun i =>
    le_of_tendsto_of_tendsto' (hconv i) tendsto_const_nhds (fun n => (hmem n i).2)
  have hmin : ∀ i, -1 ≤ x i := fun i =>
    le_of_tendsto_of_tendsto' tendsto_const_nhds (hconv i) (fun n => (hmem n i).1)
  have hsup : fluidMax x ≤ 0 := by
    unfold fluidMax
    exact Finset.sup'_le Finset.univ_nonempty x (fun i _ => hmax i)
  have hinf : -1 ≤ fluidMin x := by
    unfold fluidMin
    exact Finset.le_inf' Finset.univ_nonempty x (fun i _ => hmin i)
  unfold fluidGap
  linarith

/-- **The paper's (5.1) at `s₀ = 64C`.**  The gap bound at the origin plus the diameter
growth inequality `(diamgrow)` gives `Δ(64C) ≤ 1 + 64C`, i.e. the `hgap₀` premise of
`coalesced_at_of_fluid` and of `paper_fluid_coalesce_before_B_sub_two`. -/
theorem fluidGap_le_one_add {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ι → ℝ → ℝ} {T s₀ : ℝ} (hmove : FluidMotionOn x 0 T)
    (hs₀ : 0 ≤ s₀) (hT : s₀ ≤ T) (hgap₀ : fluidGap (fun i => x i 0) ≤ 1) :
    fluidGap (fun i => x i s₀) ≤ 1 + s₀ := by
  have h := fluidGap_growth hmove (le_refl (0 : ℝ)) hs₀ hT (x := x)
  linarith

/-! ## 4. The source's `(meet)` as the stopping alternative (4.15) plus persistence -/

/-- Leader persistence: a coordinate that leads at fluid time `s` still leads at every
later fluid time of the window.  This is the consequence of `(4.9)` the paper uses
tacitly in step 6 ("leader persistence ensures `A(s_k)` is increasing"). -/
def LeaderPersist {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ → ℝ) (s₀ T : ℝ) : Prop :=
  ∀ s t, s₀ ≤ s → s ≤ t → t ≤ T →
    leaders (fun i => x i s) ⊆ leaders (fun i => x i t)

/-- **The source's `(meet)` from its stopping formulation (4.15).**

If leaders persist and, whenever the leading set is proper and the candidate deadline
`s + b Δ(s)` is below `T`, some *outsider* reaches the current fluid maximum by a time
`u ≤ s + b Δ(s)`, then the meeting rule `JoinRuleFrom` holds.  This is the paper's own
argument: the outsider joins `A(u)`, and persistence keeps the old leaders there, so the
leading set grows strictly. -/
theorem joinRuleFrom_of_reaches {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ → ℝ) {s₀ b T : ℝ}
    (hpersist : LeaderPersist x s₀ T)
    (hreach : ∀ s, s₀ ≤ s → leaders (fun i => x i s) ≠ Finset.univ →
      s + b * fluidGap (fun i => x i s) < T →
      ∃ u, s ≤ u ∧ u ≤ s + b * fluidGap (fun i => x i s) ∧
        ∃ k, k ∉ leaders (fun i => x i s) ∧ x k u = fluidMax (fun i => x i u)) :
    JoinRuleFrom x s₀ b T := by
  intro s hs hne hcand
  obtain ⟨u, hsu, hu, k, hknot, hkmax⟩ := hreach s hs hne hcand
  have huT : u ≤ T := le_of_lt (lt_of_le_of_lt hu hcand)
  have hsub : leaders (fun i => x i s) ⊆ leaders (fun i => x i u) :=
    hpersist s u hs hsu huT
  have hk : k ∈ leaders (fun i => x i u) := mem_leaders.mpr hkmax
  have hne' : leaders (fun i => x i s) ≠ leaders (fun i => x i u) := by
    intro heq
    exact hknot (heq ▸ hk)
  exact ⟨u, hsu, hu, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩⟩

end FluidJoin


