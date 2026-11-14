/-
# The fluid `(meet)` deadline from the finite-scale sharp meet bounds

The paper's step 6 (`main_1d_revised.tex`, proof of Proposition `tight`,
the paragraph after `(coincide)`) asserts

  `(meet)  t - s <= b (max_i x_i(s) - min_i x_i(s))`

for a separated leading group, after dividing the finite-`L` potential estimate
by `L` and letting `L → ∞`.  The finite-`L` half is the accepted sharp bound
`JoinStep.run_le_sharp`:

  `t_L - s_L <= 2 C^2 (spread_D(s_L) + (min_D X - max_{D^c} M)(s_L) + eta)
                  + 2 C C_T L^{3/4}`,

and the fluid input `(sep)` is transferred to the grid by
`M2B.sep_eventually_of_fluid`.  What is *not* in the tree is the passage from
that lattice-unit inequality at every scale to the fluid inequality, uniformly
over the group and without any probability input.  This file supplies exactly
that passage.

Main declarations.

* `tendsto_floor_mul_div` — `⌊L s⌋ / L → s`;
* `tendsto_sup'_scaled` — the running maximum of the scaled positions at the
  grid knot `⌊L s⌋` converges to the fluid coordinate;
* `gapStar` — the lattice quantity `max_D X - max_J X` whose normalisation is
  exactly `sup'_D (scaled) - sup'_J (scaled)`; note that
  `spread_D + (min_D X - max_J M)` is at most `gapStar`, so `run_le_sharp`'s
  right-hand side is dominated by `2 C^2 (gapStar + eta) + 2 C C_T L^{3/4}`;
* `meet_of_grid_bounds` — **the fluid `(meet)`**: if every scale satisfies the
  lattice-unit sharp meet bound at the *same* fluid times `s ≤ t`, and
  `eta / L → 0`, then `t - s ≤ 2 C^2 (sup_D x(s) - sup_J x(s))`.

The factor is the true `2 C^2` of the sharp finite round, not the source's
`C^2`.  Nothing probabilistic, no stationarity, no fluid potential object `W`,
and no Sticky/JoinRule input appears: this is the deterministic limit passage.
The strict fluid separation of the group from its complement on `[s,t]` is the
*consumer's* premise (it is what `M2B.sep_eventually_of_fluid` needs to produce
the grid `(sep)`); see `MeetFromClauses.lean`.  Unknown at this file: whether
the sharp window hypotheses of `run_le_sharp` hold, which is measured input.
-/
import Swarm.FluidMeet

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

open M2B FluidMerge FluidLimit Glue LocalFluid

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The grid knot tends to the fluid time -/

/-- `⌊L s⌋ / L → s` along any sequence of scales tending to infinity. -/
theorem tendsto_floor_mul_div {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) / (scale n : ℝ)) atTop (𝓝 s) := by
  have hsc : Tendsto (fun n => (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleTop
  have hinv : Tendsto (fun n => ((scale n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsc
  have hbound : ∀ n, ‖((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) / (scale n : ℝ) - s‖
      ≤ ((scale n : ℝ))⁻¹ := by
    intro n
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hf0 : (0 : ℝ) ≤ (scale n : ℝ) * s := mul_nonneg hL.le hs
    have hlow : ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * s := Nat.floor_le hf0
    have hup : (scale n : ℝ) * s < ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hle : ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) / (scale n : ℝ) ≤ s := by
      rw [div_le_iff₀ hL]
      linarith
    have hlt : s ≤ ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) / (scale n : ℝ) + ((scale n : ℝ))⁻¹ := by
      have h1 : ((scale n : ℝ) * s) / (scale n : ℝ)
          < (((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) + 1) / (scale n : ℝ) := by
        exact div_lt_div_of_pos_right hup hL
      rw [mul_div_cancel_left₀ s hL.ne', add_div, one_div] at h1
      linarith
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound hinv

/-- Monotonicity of the floor of the scaled time. -/
theorem floor_le_floor_mul {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ⌊(scale n : ℝ) * s⌋₊ ≤ ⌊(scale n : ℝ) * t⌋₊ := by
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  refine Nat.le_floor ?_
  have h1 : ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * s :=
    Nat.floor_le (mul_nonneg hL.le hs)
  have h2 : (scale n : ℝ) * s ≤ (scale n : ℝ) * t := mul_le_mul_of_nonneg_left hst hL.le
  push_cast
  linarith

/-- The grid knots stay within the raw horizon. -/
theorem floor_le_horizon {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) {T : ℕ}
    {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    ∀ n, ⌊(scale n : ℝ) * s⌋₊ ≤ FluidInterpolation.rawHorizon (T : ℝ) (scale n) := by
  intro n
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  rw [FluidInterpolation.rawHorizon]
  refine Nat.floor_mono ?_
  calc (scale n : ℝ) * s ≤ (scale n : ℝ) * (T : ℝ) := mul_le_mul_of_nonneg_left hsT hL.le
    _ = (T : ℝ) * (scale n : ℝ) := by ring

/-! ## 2. Scaled positions at the floor knot -/

/-- The actual scaled position at the grid knot `⌊L s⌋` converges to the fluid
coordinate at `s`.  This is `M2B.scaledPosition_tendsto_of_ratio` with the
explicit ratio `⌊L s⌋ / L → s`. -/
theorem tendsto_scaled_floor {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (T : ℝ)) (i : ι) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 (M2B.fpos x i hs)) := by
  have hkT : ∀ᶠ n in atTop, ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall (floor_le_horizon hscale hs.1 hs.2)] with n hn
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have h1 : ((⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ (scale n : ℝ) * s :=
      Nat.floor_le (mul_nonneg hL.le hs.1)
    have h2 : (scale n : ℝ) * s ≤ (scale n : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hs.2 hL.le
    linarith
  exact M2B.scaledPosition_tendsto_of_ratio hscale hconv hlip hs
    (k := fun n => ⌊(scale n : ℝ) * s⌋₊) hkT (tendsto_floor_mul_div hscale hscaleTop hs.1) i

/-! ## 3. The lattice gap `max_D X - max_J X` and its normalisation -/

/-- The lattice-unit gap between the maxima of two groups. -/
noncomputable def gapStar (X : ι → ℕ → ℤ) (D J : Finset ι) (n : ℕ) : ℝ :=
  ((sMax X D n : ℤ) : ℝ) - ((sMax X J n : ℤ) : ℝ)

/-- `run_le_sharp`'s right-hand side is dominated by `2 C^2 (gapStar + eta)`. -/
theorem spread_add_gap_le_gapStar {X : ι → ℕ → ℤ} {D J : Finset ι} {n : ℕ}
    (hD : D.Nonempty) (hJ : J.Nonempty) (hDJ : J = Finset.univ \ D) :
    ((spreadS X D n : ℤ) : ℝ) + ((sMin X D n - sMaxM X J n : ℤ) : ℝ)
      ≤ gapStar X D J n := by
  have h1 : ((sMaxM X J n : ℤ) : ℝ) ≥ ((sMax X J n : ℤ) : ℝ) := by
    have hle : sMax X J n ≤ sMaxM X J n :=
      sMax_le hJ (fun j hj => le_trans (le_runMaxI X j n) (le_sMaxM hJ hj))
    exact_mod_cast hle
  have h2 : ((spreadS X D n : ℤ) : ℝ)
      = ((sMax X D n : ℤ) : ℝ) - ((sMin X D n : ℤ) : ℝ) := by
    unfold spreadS
    push_cast
    ring
  have h3 : ((sMin X D n - sMaxM X J n : ℤ) : ℝ)
      = ((sMin X D n : ℤ) : ℝ) - ((sMaxM X J n : ℤ) : ℝ) := by push_cast; ring
  rw [h2, h3]
  unfold gapStar
  linarith

/-- The normalised lattice gap is the difference of the scaled group maxima. -/
theorem sup'_scaledPosition_eq {X : ι → ℕ → ℤ} {D : Finset ι} {start level L k : ℕ}
    (hL : 0 < L) (hD : D.Nonempty) :
    D.sup' hD (fun i => scaledPosition X level start L i k)
      = (((sMax X D (start + k) : ℤ) : ℝ) - (level : ℝ)) / (L : ℝ) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hD _ (fun i hi => ?_)
    have h1 : X i (start + k) ≤ sMax X D (start + k) := le_sMax hD hi
    have h2 : ((X i (start + k) : ℤ) : ℝ) ≤ ((sMax X D (start + k) : ℤ) : ℝ) := by
      exact_mod_cast h1
    unfold scaledPosition
    rw [div_le_div_iff_of_pos_right hLr]
    linarith
  · obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_sup' hD (fun i => X i (start + k))
    rw [sMax_of_nonempty hD, hval]
    exact Finset.le_sup' (fun i => ((X i (start + k) : ℝ) - (level : ℝ)) / (L : ℝ)) hi

/-- The group maximum of the scaled positions converges to the fluid supremum. -/
theorem tendsto_sup'_scaled {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (T : ℝ)) {D : Finset ι} (hD : D.Nonempty) :
    Tendsto (fun n => D.sup' hD (fun i => scaledPosition (X n) (level n) (τ n (level n))
        (scale n) i ⌊(scale n : ℝ) * s⌋₊)) atTop
      (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs))) :=
  M2B.tendsto_sup'_finset_of hD (fun i _ => tendsto_scaled_floor hscale hscaleTop hconv hlip hs i)

/-! ## 4. The fluid `(meet)` -/

/-- **The fluid `(meet)` deadline.**  If at every scale the sharp finite-`L`
meet estimate holds at the *same* fluid times `s ≤ t` in the lattice form

  `t_L - s_L ≤ 2 C^2 (gapStar + eta) + 2 C C_T L^{3/4}`,

with `t_L = ⌊L t⌋`, `s_L = ⌊L s⌋`, then the fluid inequality
`t - s ≤ 2 C^2 (sup_D x(s) - sup_J x(s))` holds.  No probability, no
potential, no Sticky/JoinRule input. -/
theorem meet_of_grid_bounds {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale eta : ℕ → ℕ}
    {C CT : ℝ} {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (T : ℝ)) (hst : s ≤ t) (htT : t ≤ (T : ℝ))
    {D J : Finset ι} (hD : D.Nonempty) (hJ : J.Nonempty)
    (hbd : ∀ n, ((⌊(scale n : ℝ) * t⌋₊ - ⌊(scale n : ℝ) * s⌋₊ : ℕ) : ℝ)
      ≤ 2 * C ^ 2 * (gapStar (X n) D J (τ n (level n) + ⌊(scale n : ℝ) * s⌋₊) + (eta n : ℝ))
        + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0)) :
    t - s ≤ 2 * C ^ 2 * (D.sup' hD (fun i => M2B.fpos x i hs)
      - J.sup' hJ (fun j => M2B.fpos x j hs)) := by
  set sL : ℕ → ℕ := fun n => ⌊(scale n : ℝ) * s⌋₊ with hsL
  set tL : ℕ → ℕ := fun n => ⌊(scale n : ℝ) * t⌋₊ with htL
  have hstL : ∀ n, sL n ≤ tL n := fun n => floor_le_floor_mul hscale hs.1 hst
  -- the scaled lattice inequality
  have hscaled : ∀ n, (tL n : ℝ) / (scale n : ℝ) - (sL n : ℝ) / (scale n : ℝ)
      ≤ 2 * C ^ 2 * ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
          - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
            + (eta n : ℝ) / (scale n : ℝ))
        + 2 * C * CT * ((scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ)) := by
    intro n
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have h := hbd n
    have hcast : ((tL n - sL n : ℕ) : ℝ) = (tL n : ℝ) - (sL n : ℝ) := by
      rw [Nat.cast_sub (hstL n)]
    rw [hcast] at h
    have hdiv : ((tL n : ℝ) - (sL n : ℝ)) / (scale n : ℝ)
        ≤ (2 * C ^ 2 * (gapStar (X n) D J (τ n (level n) + sL n) + (eta n : ℝ))
            + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ)) / (scale n : ℝ) :=
      (div_le_div_iff_of_pos_right hL).mpr h
    have hsplit : (2 * C ^ 2 * (gapStar (X n) D J (τ n (level n) + sL n) + (eta n : ℝ))
            + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ)) / (scale n : ℝ)
        = 2 * C ^ 2 * ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
            - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
              + (eta n : ℝ) / (scale n : ℝ))
          + 2 * C * CT * ((scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ)) := by
      unfold gapStar
      ring
    rw [hsplit] at hdiv
    calc (tL n : ℝ) / (scale n : ℝ) - (sL n : ℝ) / (scale n : ℝ)
        = ((tL n : ℝ) - (sL n : ℝ)) / (scale n : ℝ) := by rw [sub_div]
      _ ≤ _ := hdiv
  -- limits of both sides
  have hsupD : Tendsto (fun n => D.sup' hD (fun i => scaledPosition (X n) (level n)
      (τ n (level n)) (scale n) i (sL n))) atTop (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs))) :=
    tendsto_sup'_scaled hscale hscaleTop hconv hlip hs hD
  have hsupJ : Tendsto (fun n => J.sup' hJ (fun j => scaledPosition (X n) (level n)
      (τ n (level n)) (scale n) j (sL n))) atTop (𝓝 (J.sup' hJ (fun j => M2B.fpos x j hs))) :=
    tendsto_sup'_scaled hscale hscaleTop hconv hlip hs hJ
  have hpolar : Tendsto (fun n => ((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
      / (scale n : ℝ) - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ) / (scale n : ℝ))
      atTop (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs) - J.sup' hJ (fun j => M2B.fpos x j hs))) := by
    have hfun : (fun n => ((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ) / (scale n : ℝ)
        - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ) / (scale n : ℝ))
        = (fun n => D.sup' hD (fun i => scaledPosition (X n) (level n) (τ n (level n))
              (scale n) i (sL n))
            - J.sup' hJ (fun j => scaledPosition (X n) (level n) (τ n (level n))
              (scale n) j (sL n))) := by
      funext n
      rw [sup'_scaledPosition_eq (hscale n) hD, sup'_scaledPosition_eq (hscale n) hJ]
      ring
    rw [hfun]
    exact hsupD.sub hsupJ
  have hleft : Tendsto (fun n => (tL n : ℝ) / (scale n : ℝ) - (sL n : ℝ) / (scale n : ℝ))
      atTop (𝓝 (t - s)) :=
    (tendsto_floor_mul_div hscale hscaleTop (hs.1.trans hst)).sub
      (tendsto_floor_mul_div hscale hscaleTop hs.1)
  have heta' : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0) := heta
  have hpolar' : Tendsto (fun n =>
      2 * C ^ 2 * ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
          - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
            + (eta n : ℝ) / (scale n : ℝ))
        + 2 * C * CT * ((scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ))) atTop
      (𝓝 (2 * C ^ 2 * (D.sup' hD (fun i => M2B.fpos x i hs)
        - J.sup' hJ (fun j => M2B.fpos x j hs)))) := by
    have h1 : Tendsto (fun n => ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
          - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
            + (eta n : ℝ) / (scale n : ℝ))) atTop
        (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs) - J.sup' hJ (fun j => M2B.fpos x j hs))) := by
      simpa only [sub_div, add_zero] using hpolar.add heta'
    have h2 : Tendsto (fun n => (scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ)) atTop (𝓝 0) := by
      have hpow : Tendsto (fun n => (scale n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
          (tendsto_natCast_atTop_atTop.comp hscaleTop)
      have hinv : Tendsto (fun n => ((scale n : ℝ) ^ (1 / 4 : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hpow
      refine Tendsto.congr' ?_ hinv
      filter_upwards [Filter.Eventually.of_forall hscale] with n hn
      have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hn
      have h1' : (scale n : ℝ) ^ ((3 : ℝ) / 4) / (scale n : ℝ)
          = (scale n : ℝ) ^ ((3 : ℝ) / 4 - 1) := by
        rw [Real.rpow_sub hL, Real.rpow_one]
      rw [h1', show (3 : ℝ) / 4 - 1 = -(1 / 4) by norm_num, Real.rpow_neg hL.le]
    have hfin := (h1.const_mul (2 * C ^ 2)).add (h2.const_mul (2 * C * CT))
    simpa only [sub_div, mul_zero, add_zero] using hfin
  exact le_of_tendsto_of_tendsto hleft hpolar' (Filter.Eventually.of_forall hscaled)

end M2Meet
