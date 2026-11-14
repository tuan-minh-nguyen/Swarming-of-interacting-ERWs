/-
# Pointwise grid-sample convergence for the actual record interpolants

The compactness entry point `FluidInterpolation.exists_record_interpolated_limit_subseq`
delivers two convergence statements: uniform convergence of the literal clamped
interpolants `recordFamily`, and uniform convergence of the raw grid samples
`scaledPosition ... (rawSample ...)` at the last component of its output tuple.  The
halving-clause package `DefectKnot.exists_uniform_half_of_knot_coalescence`, on the other
hand, receives only the first of the two.  The source's step 4 needs the *grid* values:
`(fluid)` (3.2) is an inequality between scaled positions at integer times `⌊L s⌋`,
`⌊L t⌋`, and the initial gap bound `(5.1)` is read at `⌊L·0⌋ = 0`.

This file therefore recovers the grid-sample convergence from `recordFamily` uniform
convergence alone.  Two elementary facts are used:

* the clamped interpolant at the grid knot `k` is the literal scaled position
  (`FluidInterpolation.recordFamily_apply_knot`, already public);
* `⌊L t⌋ / L → t` with error at most `L⁻¹` (`floor_div_sub_le` below).

No probabilistic input, no extra compactness extraction and no subsequence change is
involved: the same `φ` and the same limit `x` are used.
-/
import Swarm.DefectKnotUniform
import Swarm.FluidJoinCoalesce

set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidJoin

open FluidMerge FluidInterpolation FluidLimit RecordDefect

/-! ## 1. The grid knot converges to the fluid time -/

/-- `⌊L t⌋ / L` differs from `t` by at most `L⁻¹` for `t ≥ 0` and `L > 0`. -/
theorem floor_div_sub_le {L : ℕ} (hL : 0 < L) {t : ℝ} (ht : 0 ≤ t) :
    |((⌊(L : ℝ) * t⌋₊ : ℝ)) / (L : ℝ) - t| ≤ (L : ℝ)⁻¹ := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hf0 : (0 : ℝ) ≤ (L : ℝ) * t := mul_nonneg (Nat.cast_nonneg L) ht
  have hlow : (⌊(L : ℝ) * t⌋₊ : ℝ) ≤ (L : ℝ) * t := Nat.floor_le hf0
  have hup : (L : ℝ) * t < (⌊(L : ℝ) * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hle : ((⌊(L : ℝ) * t⌋₊ : ℝ)) / (L : ℝ) ≤ t := by
    rw [div_le_iff₀ hLr]; linarith
  have hlt : t < ((⌊(L : ℝ) * t⌋₊ : ℝ)) / (L : ℝ) + (L : ℝ)⁻¹ := by
    have h := div_lt_div_of_pos_right hup hLr
    rw [mul_div_cancel_left₀ t hLr.ne'] at h
    have heq : ((⌊(L : ℝ) * t⌋₊ : ℝ) + 1) / (L : ℝ)
        = ((⌊(L : ℝ) * t⌋₊ : ℝ)) / (L : ℝ) + (L : ℝ)⁻¹ := by
      rw [add_div, one_div]
    linarith [h, heq ▸ h]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **Pointwise grid-sample convergence.**  Uniform convergence of the literal clamped
interpolants along `φ`, plus `scale → ∞`, give convergence of the literal scaled
positions at the grid knot `⌊scale·t⌋` to the fluid limit at `t`.  This is the form in
which the source's `(fluid)` and `(5.1)` need the compactness output. -/
theorem gridSample_tendsto
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto (fun n => scale (φ n)) atTop atTop)
    {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T (φ n) i)) (fun t => x i t) atTop)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (i : ι) :
    Tendsto (fun n => scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊) atTop (𝓝 (x i ⟨t, ht0, htT⟩)) := by
  set k : ℕ → ℕ := fun n => ⌊(scale (φ n) : ℝ) * t⌋₊ with hk
  -- the grid knots are inside the raw horizon
  have hk_le : ∀ n, k n ≤ rawHorizon T (scale (φ n)) := by
    intro n
    refine Nat.le_floor ?_
    have h1 : ((k n : ℝ)) ≤ (scale (φ n) : ℝ) * t :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) ht0)
    have h2 : (scale (φ n) : ℝ) * t ≤ (scale (φ n) : ℝ) * T :=
      mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg _)
    linarith
  -- the corresponding fluid times
  have hk_nonneg : ∀ n, (0 : ℝ) ≤ (k n : ℝ) / (scale (φ n) : ℝ) := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hk_le_time : ∀ n, (k n : ℝ) / (scale (φ n) : ℝ) ≤ T := by
    intro n
    have hLr : (0 : ℝ) < (scale (φ n) : ℝ) := by exact_mod_cast hscale (φ n)
    rw [div_le_iff₀ hLr]
    have h1 : ((k n : ℝ)) ≤ (scale (φ n) : ℝ) * t :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) ht0)
    have h2 : (scale (φ n) : ℝ) * t ≤ (scale (φ n) : ℝ) * T :=
      mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg _)
    linarith
  set tn : ℕ → Set.Icc (0 : ℝ) T :=
    fun n => ⟨(k n : ℝ) / (scale (φ n) : ℝ), hk_nonneg n, hk_le_time n⟩ with htn_def
  -- the grid values are the interpolant at those times
  have hstep : ∀ n, recordFamily X τ level scale hscale T (φ n) i (tn n)
      = scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n))) (scale (φ n)) i (k n) := by
    intro n
    exact DefectKnot.recordFamily_apply_knot hscale (φ n) i rfl (hk_le n)
  -- the knot times converge to `t`
  have htn : Tendsto tn atTop (𝓝 ⟨t, ht0, htT⟩) := by
    rw [tendsto_subtype_rng]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖(k n : ℝ) / (scale (φ n) : ℝ) - t‖ ≤ (scale (φ n) : ℝ)⁻¹ := by
      intro n
      simpa only [Real.norm_eq_abs, hk] using floor_div_sub_le (hscale (φ n)) ht0
    have hzero : Tendsto (fun n => (scale (φ n) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hscaleTop)
    exact squeeze_zero (fun n => norm_nonneg _) hbound hzero
  -- uniform convergence evaluated at the moving knot
  have hdiff : Tendsto
      (fun n => ⇑(recordFamily X τ level scale hscale T (φ n) i) (tn n) - x i (tn n))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.mp (hconv i) ε hε)
    exact ⟨N, fun n hn => by
      have h := hN n hn (tn n)
      rw [Real.dist_eq] at h ⊢
      rw [sub_zero, abs_sub_comm]
      exact h⟩
  have hcont : Tendsto (fun n => x i (tn n)) atTop (𝓝 (x i ⟨t, ht0, htT⟩)) :=
    ((x i).continuous.tendsto _).comp htn
  have hsum := hdiff.add hcont
  have hlim : Tendsto (fun n => ⇑(recordFamily X τ level scale hscale T (φ n) i) (tn n))
      atTop (𝓝 (x i ⟨t, ht0, htT⟩)) := by
    simpa using hsum
  have := hstep
  simpa only [hstep, hk] using hlim

/-! ## 2. The limit is one-Lipschitz -/

/-- **The compactness limit is `1`-Lipschitz.**  `TendstoUniformly` of the actual clamped
interpolants, each `1`-Lipschitz, to `x i` forces `x i` to be `1`-Lipschitz.  This is how
the unit upper speed bound `hupper` of `fluidMotionOn_of_tendsto_lower` is discharged,
since the halving-clause tuple does not carry the compactness package's explicit
`LipschitzWith 1` output. -/
theorem lipschitz_of_uniform_recordFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n)
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)} {φ : ℕ → ℕ}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T (φ n) i)) (fun t => x i t) atTop)
    (i : ι) : LipschitzWith 1 (x i) := by
  refine LipschitzWith.mk_one (fun a b => ?_)
  have hfloor : dist (x i a) (x i b) ≤ dist a b := by
    have hev : ∀ᶠ n in atTop,
        dist (⇑(recordFamily X τ level scale hscale T (φ n) i) a)
          (⇑(recordFamily X τ level scale hscale T (φ n) i) b) ≤ dist a b := by
      refine Filter.Eventually.of_forall (fun n => ?_)
      have hlip : LipschitzWith 1 (recordFamily X τ level scale hscale T (φ n) i) :=
        lipschitz_recordFamily X τ level scale hscale T hNN (φ n) i
      simpa only [NNReal.coe_one, one_mul] using hlip.dist_le_mul a b
    have hta := (hconv i).tendsto_at a
    have htb := (hconv i).tendsto_at b
    have hprod : Tendsto
        (fun n => dist (⇑(recordFamily X τ level scale hscale T (φ n) i) a)
          (⇑(recordFamily X τ level scale hscale T (φ n) i) b))
        atTop (𝓝 (dist (x i a) (x i b))) := hta.dist htb
    exact le_of_tendsto_of_tendsto hprod tendsto_const_nhds hev
  exact hfloor

/-! ## 3. The halving-clause coalescence premise from the fluid geometry -/

/-- Unbundling of a compact-interval fluid limit to a function of real time.  Outside
`[0,T]` it is clamped; inside, `restrictToIcc_apply` identifies it with the literal
value. -/
noncomputable def restrictToIcc {ι : Type*} {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) : ι → ℝ → ℝ :=
  fun i t => x i ⟨min (max t 0) T, ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩⟩

theorem restrictToIcc_apply {ι : Type*} {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (i : ι) :
    restrictToIcc hT x i t = x i ⟨t, ht⟩ := by
  refine congrArg (x i) (Subtype.ext ?_)
  simp only [max_eq_left ht.1, min_eq_left ht.2]

/-- **The `hcoal` premise of `exists_uniform_half_of_knot_coalescence`, discharged down to
the paper's step-4/5/6 fluid inputs.**

For one admissible record family and one subsequential compactness limit `x`, the
coalescence of the fluid knot configuration at every fluid time `θ ≥ B` follows from:

* the literal event `{d_r ≤ L}` (`hd`), which is what makes `(5.1)` true;
* uniform convergence of the literal interpolants (`hconv`) -- from this file the grid
  samples converge pointwise and the limit is `1`-Lipschitz;
* the finite-scale one-sided estimate `-(ε (φ n)) ≤ x_i(t) - x_i(s)` with `ε → 0`, i.e.
  the local-good window estimate `(3.1)` divided by `L`; this is the *only* place a
  local-good condition enters, and it enters only through its normalised limit;
* the meeting rule `JoinRuleFrom` (the source's `(meet)`, reduced in
  `FluidJoin.joinRuleFrom_of_reaches` to (4.15) plus leader persistence);
* coincidence on contact `StickyOn` (the source's `(coincide)`).

Nothing probabilistic is assumed. -/
theorem hcoal_at_theta_of_fluid_geometry
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ} {B Tn : ℕ}
    (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) (hφ : StrictMono φ)
    (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t) atTop)
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hs₀T : 64 * C ≤ (Tn : ℝ))
    (hBB : (1 + 64 * C) * (1 + b) ^ (Fintype.card ι - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hlow : ∀ n i (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ (Tn : ℝ) →
      -(ε (φ n)) ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
        - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * s⌋₊)
    (hjoin : JoinRuleFrom (restrictToIcc hTn x) (64 * C) b (Tn : ℝ))
    (hsticky : StickyOn (restrictToIcc hTn x) (64 * C) (Tn : ℝ))
    {θ : Set.Icc (0 : ℝ) (Tn : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) :
    ∀ i j, x i θ = x j θ := by
  have hscaleTop' : Tendsto (fun n => scale (φ n)) atTop atTop :=
    hscaleTop.comp hφ.tendsto_atTop
  -- the compactness limit is one-Lipschitz, hence has unit upper speed
  have hxlip : ∀ i, LipschitzWith 1 (x i) :=
    fun i => lipschitz_of_uniform_recordFamily hscale hNN hconv i
  -- the source's (fluid) (3.2)
  have hmove0 : FluidMotionOn (restrictToIcc hTn x) 0 (Tn : ℝ) := by
    refine fluidMotionOn_of_tendsto_lower (s₀ := 0) (T := (Tn : ℝ))
      (ε := fun n => ε (φ n))
      (y := fun n i t => scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊) ?_ ?_ (hε.comp hφ.tendsto_atTop) ?_
    · intro i s t hs hst htT
      have hu := upper_speed_of_lipschitz_on_Icc (hxlip i) (s := s) (t := t)
        ⟨hs, hst.trans htT⟩ ⟨hs.trans hst, htT⟩ hst
      rw [restrictToIcc_apply hTn x ⟨hs, hst.trans htT⟩ i,
        restrictToIcc_apply hTn x ⟨hs.trans hst, htT⟩ i]
      exact hu
    · intro i t ht0 htT
      have hgrid := gridSample_tendsto hscale hscaleTop' hconv ht0 htT i
      rw [restrictToIcc_apply hTn x ⟨ht0, htT⟩ i]
      exact hgrid
    · exact hlow
  have hmove : FluidMotionOn (restrictToIcc hTn x) (64 * C) (Tn : ℝ) :=
    fun i s t hs hst htT => hmove0 i s t (le_trans (by linarith : (0 : ℝ) ≤ 64 * C) hs) hst htT
  -- the source's (5.1) at the window origin
  have hgap0 : fluidGap (fun i => restrictToIcc hTn x i 0) ≤ 1 := by
    have hconv0 : ∀ i, Tendsto (fun n =>
        scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n))) (scale (φ n)) i 0)
        atTop (𝓝 (restrictToIcc hTn x i 0)) := by
      intro i
      have hgrid := gridSample_tendsto hscale hscaleTop' hconv (le_refl (0 : ℝ)) hTn i
      rw [restrictToIcc_apply hTn x ⟨le_refl (0 : ℝ), hTn⟩ i]
      simpa only [mul_zero, Nat.floor_zero] using hgrid
    exact fluidGap_zero_le_one (X := fun n => X (φ n)) (τ := fun n => τ (φ n))
      (level := fun n => level (φ n)) (scale := fun n => scale (φ n))
      (fun n => hτ (φ n)) (fun n => hscale (φ n)) (fun n => hd (φ n)) hconv0
  -- the source's (5.1) at `s₀ = 64C`
  have hgap₀ : fluidGap (fun i => restrictToIcc hTn x i (64 * C)) ≤ 1 + 64 * C :=
    fluidGap_le_one_add hmove0 (by linarith : (0 : ℝ) ≤ 64 * C) hs₀T hgap0
  -- the source's (5.6) at `θ`
  have hcoal := coalesced_at_of_fluid_card (x := restrictToIcc hTn x) (C := C) (b := b)
    (T := (Tn : ℝ)) (B := B) hC hb hmove hjoin hsticky hBB hBT hgap₀
    (θ := (θ : ℝ)) hBθ θ.2.2
  intro i j
  rw [← restrictToIcc_apply hTn x θ.2 i, ← restrictToIcc_apply hTn x θ.2 j]
  exact hcoal i j

/-- **The halving-clause scale threshold with `hcoal` replaced by the paper's fluid
geometry.**

This is `DefectKnot.exists_uniform_half_of_knot_coalescence` with its `hcoal` hypothesis
-- "every fluid knot configuration coalesces at every `θ ∈ [B,T]`" -- replaced by the
strictly more primitive fluid data of the paper's steps 4-6: a vanishing one-sided
finite-scale drift `ε`, the meeting rule `(meet)`, and coincidence on contact
`(coincide)`.  By `hcoal_at_theta_of_fluid_geometry` the two forms are equivalent, so the
uniform halving threshold `2 d_{r+BL} ≤ L` follows unchanged, uniformly over all actual
nearest-neighbour families with first-passage records and over `r ≥ C₀ L`, on
`{d_r ≤ L} ∩ {(time)}`.

The conclusion is *not* a new probability statement: no local-good probability, no
stationary law and no `NoCoalescence` hypothesis appears, and `hgeo` is a deterministic
condition on each compactness limit. -/
theorem exists_uniform_half_of_fluid_join {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ B Tn : ℕ) (hTn : (0 : ℝ) ≤ (Tn : ℝ)) (hB0 : (0 : ℝ) ≤ (B : ℝ))
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hs₀T : 64 * C ≤ (Tn : ℝ))
    (hBB : (1 + 64 * C) * (1 + b) ^ (Fintype.card ι - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ))
    (hgeo : ∀ (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
      (hτ : ∀ n, IsRecord (X n) (τ n))
      (_hlarge : ∀ n, C₀ * scale n ≤ level n)
      (hscaleTop : Tendsto scale atTop atTop)
      (hscale : ∀ n, 0 < scale n)
      (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
      (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
      (_htime : ∀ n, τ n (level n + B * scale n) - τ n (level n) ≤ Tn * scale n)
      (x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ →
      (∀ i, TendstoUniformly
        (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t)
        atTop) →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        (∀ n i (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ (Tn : ℝ) →
          -(ε (φ n)) ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
              (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
            - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
              (scale (φ n)) i ⌊(scale (φ n) : ℝ) * s⌋₊) ∧
        JoinRuleFrom (restrictToIcc hTn x) (64 * C) b (Tn : ℝ) ∧
        StickyOn (restrictToIcc hTn x) (64 * C) (Tn : ℝ)) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ), IsRecord X τ →
        (∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) →
        defect X τ r ≤ (L : ℤ) → τ (r + B * L) - τ r ≤ Tn * L →
        2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  refine DefectKnot.exists_uniform_half_of_knot_coalescence C₀ B Tn hTn hB0 ?_
  intro X τ level scale hτ hlarge hscaleTop hscale hd hNN htime x φ hφ hconv θ hBθ
  obtain ⟨ε, hε, hlow, hjoin, hsticky⟩ :=
    hgeo X τ level scale hτ hlarge hscaleTop hscale hd hNN htime x φ hφ hconv
  exact hcoal_at_theta_of_fluid_geometry hTn hτ hscale hscaleTop hφ hd hNN hconv
    hC hb hs₀T hBB hBT ε hε hlow hjoin hsticky hBθ

/-- **The source's `(coincide)` from its finite-scale spread statement (4.8).**

`StickyOn` is the paper's (4.9): a set of coordinates that agree at one fluid time agree
at every later fluid time of the window.  The finite-scale content of the source's
order-statistic induction is (4.8), i.e. that the spread of the corresponding scaled
positions over the lattice window is `o(1)`; for the pairwise form used by `StickyOn`
this is the requirement that whenever two fluid coordinates agree at fluid time `s`,
their finite-scale grid values at any later grid time differ by `η n → 0`.

Taking the limit of the difference with this `o(1)` bound gives the equality, so the
hypothesis `hpair` is exactly the finite-scale data that the local-good machinery
`(loccoord)`, `(locgroup)` and `(sep)` must supply, expressed in the fluid-time grid used
by the compactness package. -/
theorem stickyOn_of_finiteL_pairwise
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ}
    {Tn : ℕ} (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop) (hφ : StrictMono φ)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t) atTop)
    {s₀ : ℝ} (hs₀0 : 0 ≤ s₀)
    (hpair : ∀ (i j : ι) (s : ℝ), s₀ ≤ s → s ≤ (Tn : ℝ) →
      restrictToIcc hTn x i s = restrictToIcc hTn x j s →
      ∀ t : ℝ, s ≤ t → t ≤ (Tn : ℝ) →
        ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
          ∀ n, |scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
              - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊| ≤ η n) :
    StickyOn (restrictToIcc hTn x) s₀ (Tn : ℝ) := by
  have hscaleTop' : Tendsto (fun n => scale (φ n)) atTop atTop :=
    hscaleTop.comp hφ.tendsto_atTop
  intro i j s t hs hst htT heq
  obtain ⟨η, hη, hb⟩ := hpair i j s hs (hst.trans htT) heq t hst htT
  have ht0 : 0 ≤ t := le_trans (le_trans hs₀0 hs) hst
  have hi := gridSample_tendsto hscale hscaleTop' hconv ht0 htT i
  have hj := gridSample_tendsto hscale hscaleTop' hconv ht0 htT j
  have hdt : Tendsto (fun n => scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
      - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊)
      atTop (𝓝 (restrictToIcc hTn x i t - restrictToIcc hTn x j t)) := by
    rw [restrictToIcc_apply hTn x ⟨ht0, htT⟩ i, restrictToIcc_apply hTn x ⟨ht0, htT⟩ j]
    exact hi.sub hj
  have hzero : Tendsto (fun n => scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
      - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
        - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊‖ ≤ η n := by
      intro n
      rw [Real.norm_eq_abs]
      exact hb n
    simpa only [sub_zero] using squeeze_zero (fun n => norm_nonneg _) hbound hη
  have huniq := tendsto_nhds_unique hdt hzero
  linarith

/-- **The halving-clause coalescence premise from purely finite-scale data.**

Same as `hcoal_at_theta_of_fluid_geometry`, but with the fluid-level coincidence premise
`StickyOn` replaced by the finite-scale spread condition `hpair` of the source's (4.8).
Together with `fluidMotionOn_of_tendsto_lower` (which turns the finite-scale one-sided
drift `ε` and the automatic unit speed into the source's `(fluid)`) and the initial-gap
bounds `(5.1)`, the only remaining fluid-level input is the meeting rule
`JoinRuleFrom`.

In particular *no* coalescence or equality statement about the limit appears among the
hypotheses: every premise is a statement about the actual nearest-neighbour family at
finite scale `L` together with the single meeting-rule alternative. -/
theorem hcoal_at_theta_of_finiteL_coincide
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ} {B Tn : ℕ}
    (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) (hφ : StrictMono φ)
    (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t) atTop)
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hs₀T : 64 * C ≤ (Tn : ℝ))
    (hBB : (1 + 64 * C) * (1 + b) ^ (Fintype.card ι - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hlow : ∀ n i (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ (Tn : ℝ) →
      -(ε (φ n)) ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
        - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * s⌋₊)
    (hjoin : JoinRuleFrom (restrictToIcc hTn x) (64 * C) b (Tn : ℝ))
    (hpair : ∀ (i j : ι) (s : ℝ), 64 * C ≤ s → s ≤ (Tn : ℝ) →
      restrictToIcc hTn x i s = restrictToIcc hTn x j s →
      ∀ t : ℝ, s ≤ t → t ≤ (Tn : ℝ) →
        ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
          ∀ n, |scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
              - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊| ≤ η n)
    {θ : Set.Icc (0 : ℝ) (Tn : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) :
    ∀ i j, x i θ = x j θ :=
  hcoal_at_theta_of_fluid_geometry hTn hτ hscale hscaleTop hφ hd hNN hconv hC hb hs₀T hBB hBT
    ε hε hlow hjoin
    (stickyOn_of_finiteL_pairwise hTn hscale hscaleTop hφ hconv
      (by linarith : (0 : ℝ) ≤ 64 * C) hpair) hBθ

/-- **Passage of a finite-scale "outsider reaches the record" witness to the fluid level.**

If, at one fixed fluid time `u`, some coordinate `k` is within `ε n → 0` of the finite-scale
supremum of the scaled positions for every `n`, then at the limit `x k ≥ fluidMax x`.  The
witness index `k` may be chosen freely here because the index set is finite: in a general
argument the index could vary with `n`, but this statement takes the fixed index directly,
which is what the pigeonhole reduction produces. -/
theorem fluidMax_le_of_sup_sub_le {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {y : ℕ → ι → ℝ} {x : ι → ℝ} {ε : ℕ → ℝ} {k : ι}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (x i)))
    (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ n, (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => y n i) - ε n
      ≤ y n k) :
    fluidMax x ≤ x k := by
  have hsup : Tendsto (fun n => (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => y n i)) atTop
      (𝓝 ((Finset.univ : Finset ι).sup' Finset.univ_nonempty x)) := DefectKnot.tendsto_sup'_finset hy
  have hlim : Tendsto (fun n => (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => y n i) - ε n) atTop
      (𝓝 ((Finset.univ : Finset ι).sup' Finset.univ_nonempty x)) := by
    simpa using hsup.sub hε
  have hk : Tendsto (fun n => y n k) atTop (𝓝 (x k)) := hy k
  have hle := le_of_tendsto_of_tendsto hlim hk (Filter.Eventually.of_forall h)
  simpa only [fluidMax] using hle

/-- **The source's (4.14)-(4.15) reduced to its finite-scale witness.**

`JoinRuleFrom` follows from leader persistence plus the finite-scale statement that,
whenever the fluid leading set is proper and the candidate deadline `s + b Δ(s)` is below
`T`, some *fluid* outsider `k` has its scaled position within `ε (φ n) → 0` of the
finite-scale supremum of the scaled positions at some grid time `u ≤ s + b Δ(s)`.

No equality between fluid coordinates is assumed: the finite-scale witness passes to
`x k u = fluidMax (·,u)` by `fluidMax_le_of_sup_sub_le` and the automatic reverse
inequality.  The outsider condition `k ∉ A(s)` is a fixed set condition, so it survives
the limit unchanged; only the witness *index* would need the finite pigeonhole, and it is
already fixed here. -/
theorem joinRuleFrom_of_finiteL_witness
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ}
    {Tn : ℕ} (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop) (hφ : StrictMono φ)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t) atTop)
    {s₀ b : ℝ} (hs₀0 : 0 ≤ s₀)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpersist : LeaderPersist (restrictToIcc hTn x) s₀ (Tn : ℝ))
    (hwit : ∀ s, s₀ ≤ s → leaders (fun i => restrictToIcc hTn x i s) ≠ Finset.univ →
      s + b * fluidGap (fun i => restrictToIcc hTn x i s) < (Tn : ℝ) →
      ∃ u, s ≤ u ∧ u ≤ s + b * fluidGap (fun i => restrictToIcc hTn x i s) ∧
        ∃ k, k ∉ leaders (fun i => restrictToIcc hTn x i s) ∧
          ∀ n, (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i =>
              scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) i ⌊(scale (φ n) : ℝ) * u⌋₊) - ε (φ n)
            ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) k ⌊(scale (φ n) : ℝ) * u⌋₊) :
    JoinRuleFrom (restrictToIcc hTn x) s₀ b (Tn : ℝ) := by
  have hscaleTop' : Tendsto (fun n => scale (φ n)) atTop atTop :=
    hscaleTop.comp hφ.tendsto_atTop
  refine joinRuleFrom_of_reaches _ hpersist ?_
  intro s hs hne hcand
  obtain ⟨u, hsu, hu, k, hknot, hk⟩ := hwit s hs hne hcand
  refine ⟨u, hsu, hu, k, hknot, ?_⟩
  have hu0 : 0 ≤ u := le_trans (le_trans hs₀0 hs) hsu
  have huT : u ≤ (Tn : ℝ) := le_of_lt (lt_of_le_of_lt hu hcand)
  have hcons : ∀ i, Tendsto (fun n =>
      scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * u⌋₊) atTop (𝓝 (restrictToIcc hTn x i u)) :=
    fun i => by
      rw [restrictToIcc_apply hTn x ⟨hu0, huT⟩ i]
      exact gridSample_tendsto hscale hscaleTop' hconv hu0 huT i
  have hle := fluidMax_le_of_sup_sub_le (y := fun n i =>
      scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
        (scale (φ n)) i ⌊(scale (φ n) : ℝ) * u⌋₊)
    (x := fun i => restrictToIcc hTn x i u) (ε := fun n => ε (φ n)) hcons
    (hε.comp hφ.tendsto_atTop) hk
  exact le_antisymm (Finset.le_sup' (fun i => restrictToIcc hTn x i u) (Finset.mem_univ k)) hle

/-- **The halving-clause coalescence premise from four finite-scale conditions.**

The endpoint of this file: `hcoal` at `θ ≥ B` (hence the uniform halving threshold via
`exists_uniform_half_of_fluid_join`) follows from

* `{d_r ≤ L}` (`hd`) and the scalar inequalities,
* the finite-scale one-sided drift `-(ε (φ n)) ≤ x_i(t) − x_i(s)` with `ε → 0` — the
  normalised local-good estimate (3.1);
* the finite-scale pairwise spread `o(1)` of the source's (4.8);
* leader persistence and the finite-scale outsider witness of (4.14)-(4.15).

Every premise is a statement about the actual nearest-neighbour family at scale `L_n`,
except leader persistence, which is a statement about the limit.  No fluid equality, no
`FluidMotionOn`, no `StickyOn`, no `JoinRuleFrom`, and no probability appears among the
hypotheses; those four are derived here from the finite-scale data. -/
theorem hcoal_at_theta_of_finiteL
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {φ : ℕ → ℕ} {B Tn : ℕ}
    (hTn : (0 : ℝ) ≤ (Tn : ℝ))
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) (hφ : StrictMono φ)
    (hd : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) (Tn : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i)) (fun t => x i t) atTop)
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hs₀T : 64 * C ≤ (Tn : ℝ))
    (hBB : (1 + 64 * C) * (1 + b) ^ (Fintype.card ι - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (Tn : ℝ))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hlow : ∀ n i (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ (Tn : ℝ) →
      -(ε (φ n)) ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
        - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
          (scale (φ n)) i ⌊(scale (φ n) : ℝ) * s⌋₊)
    (hpersist : LeaderPersist (restrictToIcc hTn x) (64 * C) (Tn : ℝ))
    (hwit : ∀ s, 64 * C ≤ s → leaders (fun i => restrictToIcc hTn x i s) ≠ Finset.univ →
      s + b * fluidGap (fun i => restrictToIcc hTn x i s) < (Tn : ℝ) →
      ∃ u, s ≤ u ∧ u ≤ s + b * fluidGap (fun i => restrictToIcc hTn x i s) ∧
        ∃ k, k ∉ leaders (fun i => restrictToIcc hTn x i s) ∧
          ∀ n, (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i =>
              scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) i ⌊(scale (φ n) : ℝ) * u⌋₊) - ε (φ n)
            ≤ scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) k ⌊(scale (φ n) : ℝ) * u⌋₊)
    (hpair : ∀ (i j : ι) (s : ℝ), 64 * C ≤ s → s ≤ (Tn : ℝ) →
      restrictToIcc hTn x i s = restrictToIcc hTn x j s →
      ∀ t : ℝ, s ≤ t → t ≤ (Tn : ℝ) →
        ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
          ∀ n, |scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
              - scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                (scale (φ n)) j ⌊(scale (φ n) : ℝ) * t⌋₊| ≤ η n)
    {θ : Set.Icc (0 : ℝ) (Tn : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) :
    ∀ i j, x i θ = x j θ :=
  hcoal_at_theta_of_fluid_geometry hTn hτ hscale hscaleTop hφ hd hNN hconv hC hb hs₀T hBB hBT
    ε hε hlow
    (joinRuleFrom_of_finiteL_witness hTn hscale hscaleTop hφ hconv
      (by linarith : (0 : ℝ) ≤ 64 * C) ε hε hpersist hwit)
    (stickyOn_of_finiteL_pairwise hTn hscale hscaleTop hφ hconv
      (by linarith : (0 : ℝ) ≤ 64 * C) hpair) hBθ

end FluidJoin


