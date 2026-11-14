/-
# Fluid coincidence implies a finite-scale small-spread grid time -- the source's (4.1)+(4.8)

## The gap this file closes

`JoinStep.halving_of_coalesce_sharp` (and every consumer of the sharp `(half)` clause) needs
**one** grid time `s` in the sharp subwindow `[tau_r + 64 ceil(C) L, tau_{r+BL}]` at which the
whole-pack spread is at most `HalfEps C N * L`.  In the public base that time is carried as a
residual (`M1D.MeasuredHalf`, `HalvingResidual.GoodHalf`, `EndpointHalving.NoCoalescence`).

The source obtains it from the **fluid** coalescence of the limit, not from a finite-scale
inequality: displays `(4.1)` and `(4.8)` of `results/proposition-tight-expanded.md` say that for
a group `D` whose fluid positions coincide at fluid time `s`, the finite-scale spread of `D`
at *every* grid time of `[tau_r + floor(L s), tau_r + T L]` is `o(L)`, uniformly in the grid
index.  The public base proves the *reverse* arrow (`Coalesce.hcoal_at_theta_of_finiteL_spread`,
and `Coalesce.hpair_of_class_spread` takes `(4.8)` itself as the hypothesis `hclass`), and it
proves `(4.1)` only for the *leader block at a single fixed knot*
(`BlkSeed.leadersAt_spread_eventually`, where the fluid time must be an integer).

This file proves the missing arrow in the form the source uses it:

* `rawSample_at_knot` -- the clipped raw sample at the knot `m/L` is `m`;
* `spreadS_eventually_le_of_coincidence` -- **the source's `(4.8)`**: if the fluid positions of
  `D` coincide on the whole fluid interval `[s,T]`, then for every `b > 0` and all sufficiently
  large scales, at **every** grid index `m` with `s L <= m <= T L` the spread of `D` at
  `tau_r + m` is at most `b L`.  Both the class `D` and the grid index `m` are universally
  quantified *inside* the eventual statement, so the uniformity over grid times that `(4.8)`
  needs is present;
* `spreadS_univ_eventually_le_of_coalescence` -- the whole-pack case `D = univ`, i.e. the
  finite-scale face of full fluid coalescence;
* `exists_small_spread_knot` -- the same read as an existence statement: eventually there is a
  grid time strictly after the fluid time `s` (and inside the window) with small spread.

Nothing here is probabilistic and nothing is a new finite-scale premise: the only inputs are the
accepted compactness export's uniform convergence of the *raw samples*
(`FluidInterpolation.exists_record_interpolated_limit_subseq`, last component) and the fluid
coincidence of the limit.  In particular no `NoCoalescence` event, no stationary law and no
`StickyOn`/`JoinRuleFrom` appear.
-/
import Swarm.FluidInterpolationLimit
import Swarm.GlueCore

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidCoincide

open FluidInterpolation FluidLimit Glue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The grid knot of a raw index -/

/-- **The clipped raw sample at the knot `m/scale` is `m`.**  This is what lets the uniform
convergence of the raw samples speak about the literal discrete time `tau + m`. -/
theorem rawSample_at_knot {T : ℝ} {scale : ℕ} (hscale : 0 < scale) {m : ℕ}
    (hm : (m : ℝ) ≤ T * (scale : ℝ)) :
    rawSample scale (rawHorizon T scale) ((m : ℝ) / (scale : ℝ)) = m := by
  have hsc : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  have htT : (m : ℝ) / (scale : ℝ) ≤ T := by
    rw [div_le_iff₀ hsc]
    linarith
  rw [rawSample_eq_floor htT]
  have hcancel : (scale : ℝ) * ((m : ℝ) / (scale : ℝ)) = (m : ℝ) := by
    field_simp
  rw [hcancel]
  simp

/-! ## 2. Uniform closeness at every knot -/

/-- Uniform convergence of the raw samples gives one cofinite scale set on which *all* the
grid knots of the window are simultaneously within `c` of the fluid positions. -/
theorem eventually_uniform_close
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {T : ℝ}
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, ∀ i : ι, ∀ t : Set.Icc (0 : ℝ) T,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t| ≤ c := by
  have hclose : ∀ i : ι, ∀ᶠ n in atTop, ∀ t : Set.Icc (0 : ℝ) T,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t| ≤ c := by
    intro i
    have h1 := Metric.tendstoUniformly_iff.mp (hconv i) c hc
    filter_upwards [h1] with n hn t
    have hdist : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t|
        = dist (x i t) (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t)) := by
      rw [Real.dist_eq, abs_sub_comm]
    rw [hdist]
    exact le_of_lt (hn t)
  have hall : ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset ι), ∀ t : Set.Icc (0 : ℝ) T,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t| ≤ c :=
    (Finset.eventually_all (I := (Finset.univ : Finset ι))).mpr (fun i _ => hclose i)
  simpa using hall

/-! ## 3. The source's `(4.8)`: coincident class, small spread, all grid times -/

/-- **The source's `(4.1)` + `(4.8)`.**  If the fluid positions of a nonempty group `D` agree at
every fluid time of `[s,T]`, then for every `b > 0` and all sufficiently large scales the
finite-scale spread of `D` is at most `b L` at **every** grid index `m` with `s L <= m <= T L`.

Both `D` (subject to its coincidence property) and `m` are quantified inside the eventual
statement: this is exactly the uniformity in time that the Section-5.1 merger consumes. -/
theorem spreadS_eventually_le_of_coincidence
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {s : ℝ}
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop,
      ∀ (D : Finset ι), D.Nonempty →
      (∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i ∈ D, ∀ j ∈ D, x i u = x j u) →
      ∀ m : ℕ, s * (scale n : ℝ) ≤ (m : ℝ) → (m : ℝ) ≤ T * (scale n : ℝ) →
        ((spreadS (X n) D (τ n (level n) + m) : ℤ) : ℝ) ≤ b * (scale n : ℝ) := by
  have hc : (0 : ℝ) < b / 8 := by positivity
  filter_upwards [eventually_uniform_close (X := X) (τ := τ) (level := level)
    (scale := scale) (T := T) (x := x) hconv hc] with n hn D hD hcoin m hm0 hmT
  have hscR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  -- the fluid time of the knot `m`
  have ht0 : (0 : ℝ) ≤ (m : ℝ) / (scale n : ℝ) :=
    div_nonneg (Nat.cast_nonneg m) hscR.le
  have htT : (m : ℝ) / (scale n : ℝ) ≤ T := by
    rw [div_le_iff₀ hscR]
    linarith
  set t : Set.Icc (0 : ℝ) T := ⟨(m : ℝ) / (scale n : ℝ), ht0, htT⟩ with ht
  have htval : (t : ℝ) = (m : ℝ) / (scale n : ℝ) := rfl
  have hraw : rawSample (scale n) (rawHorizon T (scale n)) t = m := by
    rw [htval]
    exact rawSample_at_knot (hscale n) hmT
  have hsle : s ≤ (t : ℝ) := by
    rw [htval, le_div_iff₀ hscR]
    linarith
  -- the extremal members of `D`
  obtain ⟨i₁, hi₁, hmax⟩ :=
    exists_sMax (X := X n) (S := D) (n := τ n (level n) + m) hD
  obtain ⟨j₁, hj₁, hmin⟩ :=
    exists_sMin (X := X n) (S := D) (n := τ n (level n) + m) hD
  -- closeness at the knot
  have h1 : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ m
      - x i₁ t| ≤ b / 8 := by
    have := hn i₁ t
    rwa [hraw] at this
  have h2 : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ m
      - x j₁ t| ≤ b / 8 := by
    have := hn j₁ t
    rwa [hraw] at this
  have heq : x i₁ t = x j₁ t := hcoin t hsle i₁ hi₁ j₁ hj₁
  -- the spread is realised by `(i₁, j₁)`
  have hspread : ((spreadS (X n) D (τ n (level n) + m) : ℤ) : ℝ)
      = (X n i₁ (τ n (level n) + m) : ℝ) - (X n j₁ (τ n (level n) + m) : ℝ) := by
    unfold spreadS
    rw [hmax, hmin]
    push_cast
    ring
  have hdiff : (X n i₁ (τ n (level n) + m) : ℝ) - (X n j₁ (τ n (level n) + m) : ℝ)
      = (scale n : ℝ) * (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ m
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ m) := by
    unfold scaledPosition
    field_simp
    ring
  have hbound : scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ m
      - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ m ≤ b / 4 := by
    have hA := abs_le.mp h1
    have hB := abs_le.mp h2
    linarith
  rw [hspread, hdiff]
  have hstep : (scale n : ℝ) * (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ m
      - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ m)
      ≤ (scale n : ℝ) * (b / 4) := mul_le_mul_of_nonneg_left hbound hscR.le
  nlinarith [hstep, hscR]

/-! ## 4. The whole pack -/

/-- **Full fluid coalescence gives small whole-pack spread at every grid time of the window.**
The `D = univ` case: if all fluid positions agree on `[s,T]`, then eventually the whole-pack
spread is at most `b L` at every grid index in `[s L, T L]`. -/
theorem spreadS_univ_eventually_le_of_coalescence
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {s : ℝ}
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hcoal : ∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i j : ι, x i u = x j u)
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop, ∀ m : ℕ, s * (scale n : ℝ) ≤ (m : ℝ) → (m : ℝ) ≤ T * (scale n : ℝ) →
      ((spreadS (X n) (Finset.univ : Finset ι) (τ n (level n) + m) : ℤ) : ℝ)
        ≤ b * (scale n : ℝ) := by
  filter_upwards [spreadS_eventually_le_of_coincidence (X := X) (τ := τ) (level := level)
    (scale := scale) hscale (T := T) (s := s) (x := x) hconv b hb]
    with n hn m hm0 hmT
  exact hn Finset.univ Finset.univ_nonempty
    (fun u hu i _ j _ => hcoal u hu i j) m hm0 hmT

/-! ## 4b. From the public `recordFamily` convergence to the raw-sample convergence

The accepted compactness export carries two convergence statements: convergence of the
*piecewise-affine* family `recordFamily` (the component the public `BlkSeed`/`FluidJoin` files
consume) and convergence of the *raw samples* used above.  The former implies the latter,
because the interpolation error at a raw sample is at most `1/scale`.  This bridge means the
whole package above can be fed from either component of the export. -/

/-- **`recordFamily` convergence implies raw-sample convergence.** -/
theorem rawSample_tendsto_of_recordFamily_tendsto
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ} {T : ℝ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hNN : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (h : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop) :
    ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop := by
  intro i
  rw [Metric.tendstoUniformly_iff]
  intro c hc
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have h1 : ∀ᶠ n in atTop, ∀ t : Set.Icc (0 : ℝ) T,
      dist ((recordFamily X τ level scale hscale T n i) t) (x i t) < c / 2 := by
    filter_upwards [Metric.tendstoUniformly_iff.mp (h i) (c / 2) hc2] with n hn t
    rw [dist_comm]
    exact hn t
  have hcast : Tendsto (fun n : ℕ => (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleTop
  have hinv : Tendsto (fun n : ℕ => ((scale n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have h2 : ∀ᶠ n in atTop, ((scale n : ℝ))⁻¹ < c / 2 :=
    (tendsto_order.1 hinv).2 (c / 2) hc2
  filter_upwards [h1, h2] with n hn1 hn2 t
  have hle := recordFamily_rawSample_le X τ level scale hscale hNN n i t
  have hle' : dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon T (scale n)) t))
      ((recordFamily X τ level scale hscale T n i) t) ≤ ((scale n : ℝ))⁻¹ := by
    rw [dist_comm]
    exact hle
  have htri : dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon T (scale n)) t)) (x i t)
      ≤ dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
          ((recordFamily X τ level scale hscale T n i) t)
        + dist ((recordFamily X τ level scale hscale T n i) t) (x i t) :=
    dist_triangle _ _ _
  have h4 : dist ((recordFamily X τ level scale hscale T n i) t) (x i t) < c / 2 := hn1 t
  have h5 : dist (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
        ((recordFamily X τ level scale hscale T n i) t)
      + dist ((recordFamily X τ level scale hscale T n i) t) (x i t) < c := by
    linarith [hle', h4, hn2]
  rw [dist_comm]
  exact lt_of_le_of_lt htri h5

/-- **`(4.8)` from the `recordFamily` convergence.**  The same statement, fed from the
convergence component that the public `BlkSeed`/`FluidJoin` files consume. -/
theorem spreadS_eventually_le_of_coincidence_recordFamily
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hNN : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    {T : ℝ} {s : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop,
      ∀ (D : Finset ι), D.Nonempty →
      (∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i ∈ D, ∀ j ∈ D, x i u = x j u) →
      ∀ m : ℕ, s * (scale n : ℝ) ≤ (m : ℝ) → (m : ℝ) ≤ T * (scale n : ℝ) →
        ((spreadS (X n) D (τ n (level n) + m) : ℤ) : ℝ) ≤ b * (scale n : ℝ) :=
  spreadS_eventually_le_of_coincidence hscale (T := T) (s := s)
    (rawSample_tendsto_of_recordFamily_tendsto hscale hscaleTop hNN hconv) b hb

/-! ## 5. Wiring: the hypothesis is the accepted compactness export

The uniform convergence used above is not an assumption: it is the last component of
`FluidInterpolation.exists_record_interpolated_limit_subseq`, proved from the actual record
geometry (`IsRecord`, `d_r <= L`, unit steps) and the scale tending to infinity.  This section
records the composition, so that the whole chain from the accepted export to `(4.8)` is a single
theorem. -/

/-- **`(4.8)` along an accepted compactness subsequence.**  From the record geometry of the
actual family there are a limit `x` and a subsequence `phi` on which: for every fluid time `s`
and every `b > 0`, *if* the fluid positions of `D` coincide on `[s,T]`, then the finite-scale
spread of `D` is at most `b L` at every grid index of `[sL, TL]`, for all sufficiently large
scales of the subsequence. -/
theorem exists_subseq_spread_le_of_fluid_coalescence
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hτ : ∀ n, RecordDefect.IsRecord (X n) (τ n))
    (hlarge : ∀ n, C₀ * scale n ≤ level n)
    (hscaleTop : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hd : ∀ n, RecordDefect.defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (z : Set.Icc (0 : ℝ) T) (hz : z = ⟨0, ⟨le_rfl, hT⟩⟩)
    (hNN : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1) :
    ∃ (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (s : ℝ), 0 ≤ s → s ≤ T →
      (∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i j : ι, x i u = x j u) →
      ∀ (b : ℝ), 0 < b → ∀ᶠ n in atTop,
        ∀ (D : Finset ι), D.Nonempty →
        (∀ (u : Set.Icc (0 : ℝ) T), s ≤ (u : ℝ) → ∀ i ∈ D, ∀ j ∈ D, x i u = x j u) →
        ∀ m : ℕ, s * (scale (φ n) : ℝ) ≤ (m : ℝ) →
          (m : ℝ) ≤ T * (scale (φ n) : ℝ) →
          ((spreadS (X (φ n)) D (τ (φ n) (level (φ n)) + m) : ℤ) : ℝ)
            ≤ b * (scale (φ n) : ℝ) := by
  obtain ⟨x, φ, hφ, -, -, -, -, -, hscaleφ, -, hraw⟩ :=
    exists_record_interpolated_limit_subseq (ι := ι) C₀ T hT X τ level scale hτ hlarge
      hscaleTop hscale hd z hz hNN
  refine ⟨x, φ, hφ, fun s hs0 hsT hcoal b hb => ?_⟩
  exact spreadS_eventually_le_of_coincidence
    (X := fun n => X (φ n)) (τ := fun n => τ (φ n)) (level := fun n => level (φ n))
    (scale := fun n => scale (φ n)) (fun n => hscale (φ n)) (T := T) (s := s)
    (x := x) hraw b hb

end FluidCoincide
