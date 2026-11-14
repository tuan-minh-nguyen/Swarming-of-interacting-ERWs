/-
# The fluid `(meet)` passage with an arbitrary grid start

`MeetPassage.meet_of_grid_bounds` reads the finite-scale sharp meet bound at the *floor* grid
knot `⌊L s⌋`.  The finite-to-fluid step actually needs a knot at or *above* the fluid time `s`:
the grid `(sep)` is transferred from a fluid strict separation on `(s,t]`
(`M2B.sep_eventually_of_fluid`), so the leftmost grid time of the finite window must satisfy
`k/L ≥ s`.  This file repeats the limit passage with an arbitrary grid start `sL n` whose
normalised value tends to `s`, so that the caller can take `sL n = ⌈L s⌉` (see
`MeetFromClauses.lean`).

Nothing else changes: the lattice inequality is assumed only eventually (finitely many scales
are irrelevant for the limit), and the conclusion is the same fluid `(meet)` bound.
-/
import Swarm.MeetPassage

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

open M2B FluidMerge FluidLimit Glue LocalFluid

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The grid knot ratio of the right end of the window. -/
theorem tendsto_floor_mul_div' {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ)) atTop (𝓝 t) :=
  tendsto_floor_mul_div hscale hscaleTop ht

/-- **The fluid `(meet)` deadline from lattice-unit bounds at an arbitrary grid start.**

If the grid start `sL n` has `sL n / L → s` and stays inside the raw horizon, and at every
sufficiently large scale the sharp finite meet bound holds at the fluid times `s < t` in the
lattice form `(⌊L t⌋ - sL n) ≤ 2C² (gapStar + eta) + 2 C C_T L^{3/4}`, then
`t - s ≤ 2C² (sup_D x(s) - sup_J x(s))`. -/
theorem meet_of_grid_bounds' {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale eta : ℕ → ℕ}
    {sL : ℕ → ℕ} {C CT : ℝ} {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (T : ℝ)) (hst : s < t) (htT : t ≤ (T : ℝ))
    {D J : Finset ι} (hD : D.Nonempty) (hJ : J.Nonempty)
    (hsLratio : Tendsto (fun n => (sL n : ℝ) / (scale n : ℝ)) atTop (𝓝 s))
    (hsLh : ∀ᶠ n in atTop, (sL n : ℝ) ≤ (T : ℝ) * (scale n : ℝ))
    (hbd : ∀ᶠ n in atTop, ((⌊(scale n : ℝ) * t⌋₊ - sL n : ℕ) : ℝ)
      ≤ 2 * C ^ 2 * (gapStar (X n) D J (τ n (level n) + sL n) + (eta n : ℝ))
        + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0)) :
    t - s ≤ 2 * C ^ 2 * (D.sup' hD (fun i => M2B.fpos x i hs)
      - J.sup' hJ (fun j => M2B.fpos x j hs)) := by
  set tL : ℕ → ℕ := fun n => ⌊(scale n : ℝ) * t⌋₊ with htL
  have htLratio : Tendsto (fun n => (tL n : ℝ) / (scale n : ℝ)) atTop (𝓝 t) :=
    tendsto_floor_mul_div hscale hscaleTop (hs.1.trans hst.le)
  -- eventually the grid window is nonempty
  have hstL : ∀ᶠ n in atTop, sL n ≤ tL n := by
    have hδ : (0 : ℝ) < (t - s) / 3 := by linarith
    have h1 : ∀ᶠ n in atTop, (sL n : ℝ) / (scale n : ℝ) < s + (t - s) / 3 :=
      (tendsto_order.1 hsLratio).2 _ (by linarith)
    have h2 : ∀ᶠ n in atTop, t - (t - s) / 3 < (tL n : ℝ) / (scale n : ℝ) :=
      (tendsto_order.1 htLratio).1 _ (by linarith)
    filter_upwards [h1, h2] with n hn1 hn2
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hmid : s + (t - s) / 3 < t - (t - s) / 3 := by linarith
    have hlt : (sL n : ℝ) < (tL n : ℝ) := by
      have h3 : (sL n : ℝ) / (scale n : ℝ) < (tL n : ℝ) / (scale n : ℝ) :=
        lt_trans (lt_trans hn1 hmid) hn2
      rwa [div_lt_div_iff_of_pos_right hL] at h3
    exact_mod_cast hlt.le
  -- the scaled lattice inequality
  have hscaled : ∀ᶠ n in atTop,
      (tL n : ℝ) / (scale n : ℝ) - (sL n : ℝ) / (scale n : ℝ)
      ≤ 2 * C ^ 2 * ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
          - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
            + (eta n : ℝ) / (scale n : ℝ))
        + 2 * C * CT * ((scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ)) := by
    filter_upwards [hbd, hstL] with n hb hle
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hcast : ((tL n - sL n : ℕ) : ℝ) = (tL n : ℝ) - (sL n : ℝ) := by
      rw [Nat.cast_sub hle]
    rw [hcast] at hb
    have hdiv : ((tL n : ℝ) - (sL n : ℝ)) / (scale n : ℝ)
        ≤ (2 * C ^ 2 * (gapStar (X n) D J (τ n (level n) + sL n) + (eta n : ℝ))
            + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ)) / (scale n : ℝ) :=
      (div_le_div_iff_of_pos_right hL).mpr hb
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
  -- limits
  have hsupD : Tendsto (fun n => D.sup' hD (fun i => scaledPosition (X n) (level n)
      (τ n (level n)) (scale n) i (sL n))) atTop (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs))) := by
    refine M2B.tendsto_sup'_finset_of hD (fun i _ => ?_)
    exact M2B.scaledPosition_tendsto_of_ratio hscale hconv hlip hs (k := sL) hsLh hsLratio i
  have hsupJ : Tendsto (fun n => J.sup' hJ (fun j => scaledPosition (X n) (level n)
      (τ n (level n)) (scale n) j (sL n))) atTop (𝓝 (J.sup' hJ (fun j => M2B.fpos x j hs))) := by
    refine M2B.tendsto_sup'_finset_of hJ (fun j _ => ?_)
    exact M2B.scaledPosition_tendsto_of_ratio hscale hconv hlip hs (k := sL) hsLh hsLratio j
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
  have h1 : Tendsto (fun n => ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
        - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
          + (eta n : ℝ) / (scale n : ℝ))) atTop
      (𝓝 (D.sup' hD (fun i => M2B.fpos x i hs) - J.sup' hJ (fun j => M2B.fpos x j hs))) := by
    simpa only [sub_div, add_zero] using hpolar.add heta
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
  have hleft : Tendsto (fun n => (tL n : ℝ) / (scale n : ℝ) - (sL n : ℝ) / (scale n : ℝ))
      atTop (𝓝 (t - s)) := htLratio.sub hsLratio
  have hpolar' : Tendsto (fun n =>
      2 * C ^ 2 * ((((sMax (X n) D (τ n (level n) + sL n) : ℤ) : ℝ)
          - ((sMax (X n) J (τ n (level n) + sL n) : ℤ) : ℝ)) / (scale n : ℝ)
            + (eta n : ℝ) / (scale n : ℝ))
        + 2 * C * CT * ((scale n : ℝ) ^ (3 / 4 : ℝ) / (scale n : ℝ))) atTop
      (𝓝 (2 * C ^ 2 * (D.sup' hD (fun i => M2B.fpos x i hs)
        - J.sup' hJ (fun j => M2B.fpos x j hs)))) := by
    have hfin := (h1.const_mul (2 * C ^ 2)).add (h2.const_mul (2 * C * CT))
    simpa only [sub_div, mul_zero, add_zero] using hfin
  exact le_of_tendsto_of_tendsto hleft hpolar' hscaled

end M2Meet
