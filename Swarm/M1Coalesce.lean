/-The deterministic part of the paper's step 6 has two published entry points:

* `MeetCompose`/`M2Meet.joinRuleFrom_of_clauses` : the finite-scale clauses
  `JoinStep.LocalClauses` + `JoinStep.MartClause` at every scale, the meet allowance `η`,
  uniform convergence of the actual record samples and `LipschitzWith 1` on the limit, together
  with the fluid `(coincide)` `StickyOn`, yield the paper's meeting rule
  `JoinRuleFrom` at the sharp constant `2 C^2` and the sharp window origin `64⌈C⌉₊`.
* `CoincideFluid`/`M4Coincide.stickyOn_of_grid` : the local-good field `Glue.LocalField`, the
  group-growth clause `M4Coincide.GroupGrow` and two vanishing error profiles yield `StickyOn`
  from knotwise convergence of the grid samples.

This file joins them, and adds three reductions at these interfaces:

1. `tendstoUniformly_rawSample` / `knot_tendsto` : uniform convergence of the *literal clamped
   record interpolants* (`FluidInterpolation.recordFamily`, the compactness output) implies
   uniform convergence of the *raw samples* `scaledPosition … (rawSample …)`, which is the form
   `M2Meet` consumes, and pointwise convergence at every grid knot `⌊L t⌋`, which is the form
   `M4Coincide` consumes.  The gap is `≤ L⁻¹` (`FluidInterpolation.dist_scaledInterp_floor_le`).
   So **one** convergence hypothesis drives both entry points.
2. `fluidMotionOn_of_martClause` : the source's `(fluid)` (3.2) — monotone one-speed fluid motion
   — is *derived* from `(locmart)` alone.  `JoinStep.MartClause.down` is the source's own
   finite-`L` statement that inside the record window a walker cannot fall back by more than
   `C_T L^{3/4}`; divided by `L` and passed to the limit this is exactly the one-sided drift of
   `(3.1)`, with the explicit allowance `C_T L^{-1/4} → 0`.  Hence no separate local-good drift
   premise is needed: `MartClause` already carries it.
3. `fluidGap_lift_zero_le_one` : the source's `(5.1)` initial gap bound, from the record carrier
   `{d_r ≤ L}` and convergence at the origin.

The main theorem `coalescence_of_clauses` then produces a genuine fluid coalescence time below
`B - 2` and persistent equality on `[64⌈C⌉₊, T]` for the lifted limit, from the clause layer
`LocalClauses + MartClause + LocalField + GroupGrow` and the schedule `64⌈C⌉₊ ≤ T`,
`(1 + 64⌈C⌉₊)(1 + 2C²)^{card-1} - 1 < B - 2 < T`.  `coalesced_at_theta_of_clauses` reads it at
any `θ ≥ B`, which is exactly the `hcoal` shape of
`DefectKnotUniform.exists_uniform_half_of_knot_coalescence`.

## Scope (read before quoting)

* Deterministic.  No measure, no `arrayMeasure`, no `N`/`m`/`p` regime, no `κ`, no velocity, no
  `NoCoalescence`, no stationarity, no all-`N` or `2m < N` claim.  The probability that the
  clause layer holds is *not* supplied here: `LocalClauses`/`MartClause` are what the measured
  bad event `WindowMain.exists_badEvent_*` provides, while `Glue.LocalField` (with the sharp lag
  `η_n = o(L_n)`) and `M4Coincide.GroupGrow` are **not** yet supplied by any measured package —
  those remain the named finite-scale inputs.
* The window origin is the sharp `64⌈C⌉₊` of `M2Meet`, not `64C`; the scalar margin is stated
  with `D = 1 + 64⌈C⌉₊` accordingly.  The paper's `(1+64C)` form is recovered a fortiori when
  `C` is an integer.
-/
import Swarm.MeetCompose
import Swarm.CoincideFluid
import Swarm.FluidJoinCoalesce
import Swarm.LagFromMart
import Swarm.FluidJoinHcoal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace M1C

open FluidMerge FluidInterpolation FluidLimit RecordDefect JoinStep FluidJoin

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 0. Two elementary scale facts -/

/-- The shift by the record level cancels in a difference of scaled positions. -/
theorem scaledPosition_sub {X : ι → ℕ → ℤ} {level start scale : ℕ} (hscale : (scale : ℝ) ≠ 0)
    (i : ι) (k l : ℕ) :
    (scale : ℝ) * (scaledPosition X level start scale i k - scaledPosition X level start scale i l)
      = ((X i (start + k) : ℤ) : ℝ) - ((X i (start + l) : ℤ) : ℝ) := by
  simp only [scaledPosition]
  field_simp
  ring

/-! ## 1. One convergence hypothesis for both entry points -/

/-- The literal clamped record interpolant at `t` is the scaled interpolation. -/
theorem recordFamily_apply_eq {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    {T : ℝ} (hscale : ∀ n, 0 < scale n) (n : ℕ) (i : ι)
    (t : Set.Icc (0 : ℝ) T) :
    recordFamily X τ level scale hscale T n i t =
      scaledInterp (X n) (level n) (τ n (level n)) (scale n) i (rawHorizon T (scale n)) (t : ℝ) := by
  simp only [recordFamily, scaledBundle_apply]

/-- **Raw-sample uniform convergence from the compactness limit.**  Uniform convergence of the
literal clamped interpolants `recordFamily` implies uniform convergence of the raw grid samples
`scaledPosition … (rawSample …)`, which is the exact family `M2Meet.joinRuleFrom_of_clauses`
consumes.  The only estimate is `FluidInterpolation.dist_scaledInterp_floor_le`
(`≤ L⁻¹`), made uniform in `t` by `rawSample_eq_floor`. -/
theorem tendstoUniformly_rawSample {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    {T : ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ} (i : ι)
    (hconvR : TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop) :
    TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ)))
      (fun t => x i t) atTop := by
  rw [Metric.tendstoUniformly_iff] at hconvR ⊢
  intro ε hε
  have hquart : 0 < ε / 4 := by linarith
  have hinv : ∀ᶠ n in atTop, (scale n : ℝ)⁻¹ ≤ ε / 4 := by
    have h1 : Tendsto (fun n : ℕ => (scale n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hscaleTop)
    exact h1.eventually (eventually_le_nhds (show (0 : ℝ) < ε / 4 by linarith))
  filter_upwards [hconvR (ε / 4) hquart, hinv] with n h1 h2
  intro t
  rw [dist_comm]
  have hfloor : rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ)
      = ⌊(scale n : ℝ) * (t : ℝ)⌋₊ := rawSample_eq_floor (t := (t : ℝ)) t.2.2
  have hnn : ∀ k, |X n i ((τ n (level n) + k) + 1) - X n i (τ n (level n) + k)| ≤ 1 :=
    fun k => le_of_eq (hne n i _)
  have hd := dist_scaledInterp_floor_le (X := X n) (level := level n) (start := τ n (level n))
    (scale := scale n) i (hscale n) hnn (T := (T : ℝ)) (t := (t : ℝ)) t.2.1 t.2.2
  have hfam : recordFamily X τ level scale hscale (T : ℝ) n i t
      = scaledInterp (X n) (level n) (τ n (level n)) (scale n) i
          (rawHorizon (T : ℝ) (scale n)) (t : ℝ) := recordFamily_apply_eq hscale n i t
  have hstep1 : dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ)))
      (recordFamily X τ level scale hscale (T : ℝ) n i t) ≤ (scale n : ℝ)⁻¹ := by
    rw [hfloor, hfam, dist_comm]
    exact hd
  have hstep2 : dist (recordFamily X τ level scale hscale (T : ℝ) n i t) (x i t) < ε / 4 := by
    simpa only [dist_comm] using h1 t
  calc dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ))) (x i t)
      ≤ dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
            (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) (t : ℝ)))
          (recordFamily X τ level scale hscale (T : ℝ) n i t)
        + dist (recordFamily X τ level scale hscale (T : ℝ) n i t) (x i t) :=
        dist_triangle _ _ _
    _ ≤ ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith

/-- **Knotwise convergence of the grid samples**, the form `M4Coincide.stickyOn_of_grid`
consumes, with the target written through `M2Meet.lift` so that the two entry points share one
limit. -/
theorem knot_tendsto {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {T : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (i : ι) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ (T : ℝ)) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
      ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (M2Meet.lift x i t)) := by
  have hpt := (tendstoUniformly_rawSample hscale hscaleTop hne i (hconvR i)).tendsto_at
    (⟨t, ht0, htT⟩ : Set.Icc (0 : ℝ) (T : ℝ))
  have hrw : ∀ n, scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon (T : ℝ) (scale n))
          (⟨t, ht0, htT⟩ : Set.Icc (0 : ℝ) (T : ℝ)))
      = scaledPosition (X n) (level n) (τ n (level n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊ :=
    fun n => by rw [rawSample_eq_floor htT]
  simp only [hrw] at hpt
  have hl : M2Meet.lift x i t = x i ⟨t, ht0, htT⟩ :=
    M2Meet.lift_apply (Set.mem_Icc.mpr ⟨ht0, htT⟩)
  rw [hl]
  exact hpt

/-! ## 2. The source's `(fluid)` (3.2) from `(locmart)` -/

/-- `L^{3/4} / L = L^{-1/4}` for a positive natural scale. -/
theorem rpow_three_quarters_div (L : ℕ) (hL : 0 < L) :
    (L : ℝ) ^ (3 / 4 : ℝ) / (L : ℝ) = (L : ℝ) ^ (-(1 / 4) : ℝ) := by
  have hx : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsplit : (L : ℝ) ^ (-(1 / 4) : ℝ) * (L : ℝ) = (L : ℝ) ^ (3 / 4 : ℝ) := by
    have h1 : (L : ℝ) ^ (-(1 / 4) + 1 : ℝ) = (L : ℝ) ^ (-(1 / 4) : ℝ) * (L : ℝ) ^ (1 : ℝ) :=
      Real.rpow_add hx _ _
    rw [Real.rpow_one] at h1
    have h2 : (-(1 / 4) + 1 : ℝ) = 3 / 4 := by norm_num
    rw [h2] at h1
    exact h1.symm
  rw [← hsplit]
  exact mul_div_cancel_right₀ _ hx.ne'

/-- `C_T L^{-1/4} → 0` along any unbounded scale sequence. -/
theorem tendsto_rpow_neg_quarter {scale : ℕ → ℕ} (hscaleTop : Tendsto scale atTop atTop)
    (CT : ℝ) :
    Tendsto (fun n => CT * (scale n : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hcast : Tendsto (fun n : ℕ => (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleTop
  simpa using (hpow.comp hcast).const_mul CT

/-- **The paper's `(fluid)` (3.2) from the finite-scale `(locmart)`.**  Inside the record window
`JoinStep.MartClause.down` bounds the backward displacement of every walker by `C_T L^{3/4}`;
divided by the scale this is the one-sided drift of `(3.1)` with allowance `C_T L^{-1/4} → 0`.
The unit upper speed is the limit's `LipschitzWith 1`. -/
theorem fluidMotionOn_of_martClause {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {A : ℕ → ι → ℕ → ℕ} {level scale : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconvK : ∀ (i : ι) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ (T : ℝ)),
      Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (M2Meet.lift x i t)))
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    FluidMotionOn (fun i r => M2Meet.lift x i r) 0 (T : ℝ) := by
  refine fluidMotionOn_of_tendsto_lower (x := fun i r => M2Meet.lift x i r)
    (y := fun n i t => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
      ⌊(scale n : ℝ) * t⌋₊)
    (ε := fun n => CT * (scale n : ℝ) ^ (-(1 / 4) : ℝ)) ?_ ?_
    (tendsto_rpow_neg_quarter hscaleTop CT) ?_
  · intro i s t hs hst htT
    have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs, le_trans hst htT⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨le_trans hs hst, htT⟩
    have hu := upper_speed_of_lipschitz_on_Icc (hlip i) hsI htI hst
    rwa [M2Meet.lift_apply hsI, M2Meet.lift_apply htI]
  · intro i t hs htT
    exact hconvK i t hs htT
  · intro n i s t hs hst htT
    have hLpos : 0 < scale n := hscale n
    have hLR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hLpos
    have hneR : (scale n : ℝ) ≠ 0 := hLR.ne'
    set st : ℕ := τ n (level n) with hst_def
    set ms : ℕ := ⌊(scale n : ℝ) * s⌋₊ with hms_def
    set mt : ℕ := ⌊(scale n : ℝ) * t⌋₊ with hmt_def
    have hmsmt : ms ≤ mt := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))
    have hfloorT : ⌊(scale n : ℝ) * (T : ℝ)⌋₊ ≤ T * scale n := by
      have hcast : ((⌊(scale n : ℝ) * (T : ℝ)⌋₊ : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
        simpa only [mul_comm] using
          Nat.floor_le (show (0 : ℝ) ≤ (scale n : ℝ) * (T : ℝ) by positivity)
      exact_mod_cast hcast
    have hmtT : mt ≤ T * scale n :=
      le_trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left htT (Nat.cast_nonneg _))) hfloorT
    have hdown := (hM n).down (i := i) (s := st + ms) (t := st + mt)
      (Nat.le_add_right _ _) (Nat.add_le_add_left hmsmt _) (by omega)
    have hdiff : ((X n i (st + ms) : ℤ) : ℝ) - ((X n i (st + mt) : ℤ) : ℝ)
        = (scale n : ℝ) * (scaledPosition (X n) (level n) st (scale n) i ms
            - scaledPosition (X n) (level n) st (scale n) i mt) :=
      (scaledPosition_sub hneR i ms mt).symm
    have h1 : (scale n : ℝ) * (scaledPosition (X n) (level n) st (scale n) i ms
        - scaledPosition (X n) (level n) st (scale n) i mt) ≤ CT * (scale n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [← hdiff]
      exact hdown
    have h2 : scaledPosition (X n) (level n) st (scale n) i ms
        - scaledPosition (X n) (level n) st (scale n) i mt
        ≤ CT * (scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ) := by
      rw [le_div_iff₀ hLR]
      linarith
    have h3 : CT * (scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ)
        = CT * (scale n : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [mul_div_assoc, rpow_three_quarters_div (scale n) hLpos]
    have hbound : scaledPosition (X n) (level n) (τ n (level n)) (scale n) i ⌊(scale n : ℝ) * s⌋₊
        - scaledPosition (X n) (level n) (τ n (level n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
        ≤ CT * (scale n : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [h3] at h2
      simpa only [hst_def, hms_def, hmt_def] using h2
    linarith

/-! ## 3. The source's `(5.1)` initial gap bound -/

/-- **The paper's `(5.1)`**, read on the record carrier `{d_r ≤ L}`: the fluid gap at the window
origin is at most one. -/
theorem fluidGap_lift_zero_le_one {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    {T : ℕ} (hτ : ∀ n, IsRecord (X n) (τ n)) (hscale : ∀ n, 0 < scale n)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ)) →ᵇ ℝ}
    (hconv0 : ∀ i, Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0)
      atTop (𝓝 (M2Meet.lift x i 0))) :
    fluidGap (fun i => M2Meet.lift x i 0) ≤ 1 :=
  fluidGap_zero_le_one hτ hscale hdr hconv0

/-! ## 4. The composition -/

/-- **Fluid coalescence from the measured clause layer.**

Every premise is a per-scale deterministic statement about the *actual* nearest-neighbour record
family, plus the schedule scalar inequalities:

* `LocalClauses` (`(loccoord)`, `(locmove)`, `(lococc)`, `hmono`, `hunit`) and `MartClause`
  (`(locmart)` at `μ`) at every scale, with the meet allowance `η_n` (`C_T L^{3/4} ≤ η_n`,
  `η_n / L_n → 0`) — the data of the measured bad event;
* the local-good field `LocalField` with sharp lag `η^L_n ≤ ε₁ n · L_n`, `ε₁ → 0`, and the group
  growth clause `GroupGrow`, with `C_T L^{3/4} ≤ ε₂ n · L_n`, `ε₂ → 0`;
* the record carrier `{d_r ≤ L}`, the record window `(T+3)L ≤ r`, unit steps;
* one uniform convergence hypothesis, the compactness limit `x`, and `LipschitzWith 1` on it;
* `64⌈C⌉₊ ≤ T`, `(1 + 64⌈C⌉₊)(1 + 2C²)^{card ι - 1} - 1 < B - 2 < T`.

Conclusion: a fluid time `u ∈ [64⌈C⌉₊, (1 + 64⌈C⌉₊)(1+2C²)^{card ι - 1} - 1]` with `u < T`
below which all lifted coordinates coincide for all later times of the window. -/
theorem coalescence_of_clauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta etaL : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hLF : ∀ n, Glue.LocalField (X n) (τ n) (H n) C CT T (scale n) (level n) (etaL n))
    (hgrow : ∀ n, M4Coincide.GroupGrow (H n) (X n) (τ n) CT T (scale n) (level n))
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
      ∀ t, u ≤ t → t ≤ (T : ℝ) → ∀ i j, M2Meet.lift x i t = M2Meet.lift x j t := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC₁
  -- the limit is `1`-Lipschitz because the actual nearest-neighbour paths are
  have hlip : ∀ i, LipschitzWith 1 (x i) :=
    fun i => lipschitz_of_uniform_recordFamily hscale hne (T := (T : ℝ)) (x := x) (φ := id) hconvR i
  -- one convergence hypothesis, two consumers
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
  -- (coincide) from the local-good field and the group-growth clause
  have hsticky : StickyOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ) := by
    refine M4Coincide.stickyOn_of_grid (scale := scale) hscale hscaleTop
      (X := X) (τ := τ) (H := H) (C := C) (CT := fun _ => CT) (T := T)
      (r := level) (η := etaL) hLF hgrow hC₁ (fun _ => hCT) hτ hne hdr hr hε1t hε2t hηL
      hct (x := fun i r => M2Meet.lift x i r) (s₀ := 64 * (Nat.ceil C : ℝ)) hs₀0 ?_
    intro i t hst htT
    exact hconvK i t (le_trans hs₀0 hst) htT
  -- (meet) from the finite-scale clauses
  have hjoin : JoinRuleFrom (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (2 * C ^ 2)
      (T : ℝ) :=
    M2Meet.joinRuleFrom_of_clauses (scale := scale) (level := level) (eta := eta) hscale
      hscaleTop hτ hne hcl hM hCpos hCT hdr hr hL1 hij hnum hT64 hηdef heta hconvU hlip hsticky
  -- (fluid) from (locmart)
  have hmove0 : FluidMotionOn (fun i r => M2Meet.lift x i r) 0 (T : ℝ) :=
    fluidMotionOn_of_martClause (C := C) hscale hscaleTop hM hconvK hlip
  have hmove : FluidMotionOn (fun i r => M2Meet.lift x i r) (64 * (Nat.ceil C : ℝ)) (T : ℝ) :=
    fun i s t hs hst htT => hmove0 i s t (le_trans hs₀0 hs) hst htT
  -- (5.1) at the origin and at the window start
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
  -- the merge induction
  obtain ⟨u, hsu, hu, huT, hpers⟩ :=
    exists_persistent_coalescence (fun i r => M2Meet.lift x i r)
      (64 * (Nat.ceil C : ℝ)) (2 * C ^ 2) (1 + 64 * (Nat.ceil C : ℝ)) (T : ℝ)
      hmove hjoin hsticky (by positivity) (by positivity) (hbb.trans hBT) (by linarith) hgap₀
  exact ⟨u, hsu, hu, huT, hpers⟩

/-- **The `hcoal` shape**: at every fluid time `θ ≥ B` the compact-interval limit is fully
coalesced.  This is exactly the hypothesis
`DefectKnotUniform.exists_uniform_half_of_knot_coalescence` consumes. -/
theorem coalesced_at_theta_of_clauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta etaL : ℕ → ℕ} {C CT μ : ℝ} {T B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hLF : ∀ n, Glue.LocalField (X n) (τ n) (H n) C CT T (scale n) (level n) (etaL n))
    (hgrow : ∀ n, M4Coincide.GroupGrow (H n) (X n) (τ n) CT T (scale n) (level n))
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
    (hBT : (B : ℝ) - 2 < (T : ℝ))
    {θ : Set.Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) :
    x i θ = x j θ := by
  obtain ⟨u, hsu, hu, huT, hpers⟩ := coalescence_of_clauses hscale hscaleTop hτ hne hcl hM hLF
    hgrow hC₁ hCT hdr hr hL1 hij hnum hT64 hηdef heta hε1t hε2t hηL hct hconvR hbb hBT
  have huB : u < (θ : ℝ) := by linarith
  have heq := hpers (θ : ℝ) huB.le θ.2.2 i j
  rwa [M2Meet.lift_apply θ.2, M2Meet.lift_apply θ.2] at heq

end M1C


