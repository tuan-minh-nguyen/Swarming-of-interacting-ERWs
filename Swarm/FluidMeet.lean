/-
# The fluid `(meet)` deadline from the sharp finite-scale meet bound

The paper's step 6 obtains fluid coalescence from two finite-scale inequalities:

* `(coincide)` — equality of two fluid coordinates propagates forward in time;
* `(meet)` — a separated run of a top group cannot last longer than
  `b (min_{i in I} x_i(s) - max_{j in I^c} x_j(s))`.

`(meet)` is asserted in the source after dividing the finite-`L` potential bound
`(locmove)` by `L` and letting `L -> infinity`.  The finite-`L` statement is *proved*
(`JoinStep.run_le_sharp`, `JoinStep.exists_failure_of_gap`).  The passage to the fluid
level is what this file supplies.

The only inputs are (i) the sharp lag `M^i_n - X^i_n <= eta_n` on the sharp subwindow
(`JoinStep.lag_le_sub`, a consequence of `(locmart)`, carried here as the explicit
vanishing hypothesis `eta_n / L_n -> 0`), (ii) the accepted uniform convergence of the
actual record interpolants to the fluid limit, and (iii) the scalar clause package
consumed by `exists_failure_of_gap`.  Nothing probabilistic, no stationarity, no
`StickyOn`.

Residual after this file: the *separation hypothesis* itself.  That is the paper's
`(4.9)` acting on the leading set; it is not produced here.
-/
import Swarm.FreshCoalesce
import Swarm.PointwiseCoalescence
import Swarm.BlkSeed

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2B

open FluidInterpolation FluidLimit Glue JoinStep RecordDefect FluidMerge FluidCoincide LocalFluid

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. Finite extrema of convergent families -/

/-- Supremum over an arbitrary nonempty `Finset` of convergent reals converges to the
supremum of the limits.  (The `Finset.univ` version is `DefectKnot.tendsto_sup'_finset`.) -/
theorem tendsto_sup'_finset_of {S : Finset ι} (hS : S.Nonempty) {z : ℕ → ι → ℝ} {y : ι → ℝ}
    (h : ∀ i ∈ S, Tendsto (fun n => z n i) atTop (𝓝 (y i))) :
    Tendsto (fun n => S.sup' hS (fun i => z n i)) atTop (𝓝 (S.sup' hS y)) := by
  obtain ⟨i₀, hi₀, hval⟩ := Finset.exists_mem_eq_sup' hS y
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hall : ∀ᶠ n in atTop, ∀ i : ι, i ∈ S → z n i < y i + ε / 2 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ S
    · exact Eventually.mono
        ((tendsto_order.1 (h i hi)).2 (y i + ε / 2) (lt_add_of_pos_right _ hε2))
        (fun n hn _ => hn)
    · exact Eventually.of_forall (fun n hmem => absurd hmem hi)
  have hlow : ∀ᶠ n in atTop, y i₀ - ε / 2 < z n i₀ :=
    (tendsto_order.1 (h i₀ hi₀)).1 (y i₀ - ε / 2) (sub_lt_self _ hε2)
  filter_upwards [hall, hlow] with n hn hlown
  rw [Real.dist_eq, hval, abs_lt]
  constructor
  · have hle : z n i₀ ≤ S.sup' hS (fun i => z n i) := Finset.le_sup' (fun i => z n i) hi₀
    linarith
  · have hhigh : S.sup' hS (fun i => z n i) ≤ y i₀ + ε / 2 := by
      refine Finset.sup'_le hS (fun i => z n i) ?_
      intro i hi
      have h1 : y i ≤ y i₀ := by
        rw [← hval]
        exact Finset.le_sup' (fun j => y j) hi
      linarith [hn i hi]
    linarith

/-- Infimum over an arbitrary nonempty `Finset` of convergent reals. -/
theorem tendsto_inf'_finset_of {S : Finset ι} (hS : S.Nonempty) {z : ℕ → ι → ℝ} {y : ι → ℝ}
    (h : ∀ i ∈ S, Tendsto (fun n => z n i) atTop (𝓝 (y i))) :
    Tendsto (fun n => S.inf' hS (fun i => z n i)) atTop (𝓝 (S.inf' hS y)) := by
  obtain ⟨i₀, hi₀, hval⟩ := Finset.exists_mem_eq_inf' hS y
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hall : ∀ᶠ n in atTop, ∀ i : ι, i ∈ S → y i - ε / 2 < z n i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ S
    · exact Eventually.mono
        ((tendsto_order.1 (h i hi)).1 (y i - ε / 2) (sub_lt_self _ hε2))
        (fun n hn _ => hn)
    · exact Eventually.of_forall (fun n hmem => absurd hmem hi)
  have hup : ∀ᶠ n in atTop, z n i₀ < y i₀ + ε / 2 :=
    (tendsto_order.1 (h i₀ hi₀)).2 (y i₀ + ε / 2) (lt_add_of_pos_right _ hε2)
  filter_upwards [hall, hup] with n hn hupn
  rw [Real.dist_eq, hval, abs_lt]
  constructor
  · have hlow : y i₀ - ε / 2 ≤ S.inf' hS (fun i => z n i) := by
      refine Finset.le_inf' hS (fun i => z n i) ?_
      intro i hi
      have h1 : y i₀ ≤ y i := by
        rw [← hval]
        exact Finset.inf'_le (fun j => y j) hi
      linarith [hn i hi]
    linarith
  · have hle : S.inf' hS (fun i => z n i) ≤ z n i₀ := Finset.inf'_le (fun i => z n i) hi₀
    linarith

/-! ## 2. Convergence of the actual record interpolant at a moving grid knot -/

/-- **Literal grid values at a moving fluid time.**  If the grid knots `k n` satisfy
`k n / scale n -> v` and stay inside the raw horizon, then the literal scaled position of
every walker at `tau_r + k n` converges to the fluid value at `v`.  This is the bridge
from the accepted uniform convergence of `recordFamily` to the grid values that the
finite-`L` meet bound speaks about, at a *real* fluid time. -/
theorem scaledPosition_tendsto_of_ratio
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ}
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) T)
    {k : ℕ → ℕ} (hkT : ∀ᶠ n in atTop, (k n : ℝ) ≤ T * (scale n : ℝ))
    (hratio : Tendsto (fun n => (k n : ℝ) / (scale n : ℝ)) atTop (𝓝 v))
    (i : ι) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n))
      atTop (𝓝 (x i ⟨v, hv⟩)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hclose : ∀ᶠ n in atTop, ∀ t : Set.Icc (0 : ℝ) T,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t| < ε / 2 := by
    have h := (Metric.tendstoUniformly_iff.mp (hconv i)) (ε / 2) hε2
    filter_upwards [h] with n hn
    intro t
    have h2 := hn t
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs] at h2
    exact h2
  have hnear : ∀ᶠ n in atTop, |(k n : ℝ) / (scale n : ℝ) - v| < ε / 2 := by
    have h : ∀ᶠ n in atTop, dist ((k n : ℝ) / (scale n : ℝ)) v < ε / 2 :=
      (Metric.tendsto_nhds.mp hratio) (ε / 2) hε2
    filter_upwards [h] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hclose, hnear, hkT] with n hn hrn hkn
  have hscn : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hknn : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg _
  have ht0 : 0 ≤ (k n : ℝ) / (scale n : ℝ) := div_nonneg hknn hscn.le
  have htT : (k n : ℝ) / (scale n : ℝ) ≤ T := by
    rw [div_le_iff₀ hscn]
    linarith [hkn]
  set t : Set.Icc (0 : ℝ) T := ⟨(k n : ℝ) / (scale n : ℝ), ht0, htT⟩ with htdef
  have htval : (t : ℝ) = (k n : ℝ) / (scale n : ℝ) := by rw [htdef]
  have hkraw : rawSample (scale n) (rawHorizon T (scale n)) (t : ℝ) = k n := by
    rw [htval]
    exact rawSample_at_knot (hscale n) hkn
  have h1 := hn t
  rw [hkraw] at h1
  have h1' : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i t|
      < ε / 2 := by simpa only [abs_sub_comm] using h1
  have h2 : |x i t - x i ⟨v, hv⟩| < ε / 2 := by
    have h3 : dist (x i t) (x i ⟨v, hv⟩) ≤ |(k n : ℝ) / (scale n : ℝ) - v| := by
      have h := (hlip i).dist_le_mul t ⟨v, hv⟩
      have h4 : dist t ⟨v, hv⟩ = |(k n : ℝ) / (scale n : ℝ) - v| := by
        rw [Subtype.dist_eq, Real.dist_eq, htval]
      rw [h4] at h
      simpa using h
    rw [Real.dist_eq] at h3
    linarith
  have hsplit :
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i ⟨v, hv⟩|
        ≤ |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i t|
          + |x i t - x i ⟨v, hv⟩| := by
    have := abs_add_le (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i t)
      (x i t - x i ⟨v, hv⟩)
    have heq : (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i t)
        + (x i t - x i ⟨v, hv⟩)
        = scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n) - x i ⟨v, hv⟩ := by
      ring
    rwa [heq] at this
  have hfin := lt_of_le_of_lt hsplit (add_lt_add h1' h2)
  rw [Real.dist_eq]
  linarith [hfin]

/-! ## 3. `(sep)` transfers from the fluid scale to the grid -/

variable {T : ℕ}

/-- Fluid position of walker `i` at the fluid time `v`. -/
noncomputable def fpos (x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)) (i : ι) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (T : ℝ)) : ℝ := x i ⟨v, hv⟩

/-- **The paper's `(sep)` at the grid, from strict fluid separation.**

If the fluid positions of a proper nonempty group `D` stay at distance at least `γ` above
the fluid positions of its complement on the fluid interval `[s,t]`, and the sharp lag
`M - X <= eta` of `(locmart)` holds there with `eta / L -> 0`, then eventually `(sep)` holds
at *every* grid index whose fluid time lies in `[s,t]`.

This is the finite-scale prerequisite of the paper's `(meet)` passage.  It uses the uniform
convergence of the actual record interpolants, hence is uniform over the grid indices of the
window and needs no subsequence. -/
theorem sep_eventually_of_fluid
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale η : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hηv : Tendsto (fun n => (η n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    {D : Finset ι} (hD : D.Nonempty) (hJ : (Finset.univ \ D).Nonempty)
    {s t γ : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htT : t ≤ (T : ℝ)) (hγ : 0 < γ)
    (hsep : ∀ (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (T : ℝ)), v ∈ Set.Icc s t →
      γ ≤ D.inf' hD (fun i => fpos x i hv) - (Finset.univ \ D).sup' hJ (fun j => fpos x j hv))
    (hlag : ∀ᶠ n in atTop, ∀ (j : ι) (k : ℕ),
      s ≤ (k : ℝ) / (scale n : ℝ) → (k : ℝ) / (scale n : ℝ) ≤ t →
      runMaxI (X n) j (τ n (level n) + k) - X n j (τ n (level n) + k) ≤ (η n : ℤ)) :
    ∀ᶠ n in atTop, ∀ k : ℕ,
      s ≤ (k : ℝ) / (scale n : ℝ) → (k : ℝ) / (scale n : ℝ) ≤ t →
      Sep (X n) D (Finset.univ \ D) (τ n (level n) + k) := by
  classical
  have hδ : ∀ᶠ n in atTop, ∀ i : ι, ∀ tt : Set.Icc (0 : ℝ) (T : ℝ),
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) tt) - x i tt| < γ / 8 := by
    rw [Filter.eventually_all]
    intro i
    have h := (Metric.tendstoUniformly_iff.mp (hconv i)) (γ / 8) (by linarith)
    filter_upwards [h] with n hn tt
    have h2 := hn tt
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs] at h2
    exact h2
  have hηsmall : ∀ᶠ n in atTop, |(η n : ℝ) / (scale n : ℝ)| < γ / 8 := by
    have h := (Metric.tendsto_nhds.mp hηv) (γ / 8) (by linarith)
    filter_upwards [h] with n hn
    rwa [Real.dist_eq, sub_zero] at hn
  have hbig : ∀ᶠ n in atTop, (8 : ℝ) / γ ≤ (scale n : ℝ) := by
    have hsc : Tendsto (fun n => (scale n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hscaleTop
    exact hsc.eventually_ge_atTop (8 / γ)
  filter_upwards [hlag, hδ, hηsmall, hbig] with n hln hcl hηn hbn
  intro k hk1 hk2
  have hscn : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hv0 : 0 ≤ (k : ℝ) / (scale n : ℝ) := div_nonneg hkR hscn.le
  have hkL : (k : ℝ) ≤ t * (scale n : ℝ) := by
    rw [div_le_iff₀ hscn] at hk2
    linarith
  have hvT : (k : ℝ) / (scale n : ℝ) ≤ (T : ℝ) := by
    rw [div_le_iff₀ hscn]
    nlinarith [hkL, htT, hscn]
  have hv : (k : ℝ) / (scale n : ℝ) ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hv0, hvT⟩
  have hk_le : (k : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
    rw [div_le_iff₀ hscn] at hvT; linarith
  -- fluid order of any in-group and out-group walker at the knot's fluid time
  have horder : ∀ i ∈ D, ∀ j ∈ Finset.univ \ D, fpos x i hv - fpos x j hv ≥ γ := by
    intro i hi j hj
    have h1 : D.inf' hD (fun i => fpos x i hv) ≤ fpos x i hv :=
      Finset.inf'_le (fun i => fpos x i hv) hi
    have h2 : fpos x j hv ≤ (Finset.univ \ D).sup' hJ (fun j => fpos x j hv) :=
      Finset.le_sup' (fun j => fpos x j hv) hj
    have h3 := hsep ((k : ℝ) / (scale n : ℝ)) hv ⟨hk1, hk2⟩
    linarith
  have hraw : rawSample (scale n) (rawHorizon (T : ℝ) (scale n))
      ((k : ℝ) / (scale n : ℝ)) = k := rawSample_at_knot (hscale n) hk_le
  -- scaled positions and the lattice inequality
  have hspread : ∀ i ∈ D, ∀ j ∈ Finset.univ \ D,
      γ * 3 / 4 ≤ scaledPosition (X n) (level n) (τ n (level n)) (scale n) i k
        - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j k := by
    intro i hi j hj
    have hai : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i k
        - fpos x i hv| < γ / 8 := by
      have hh := hcl i ⟨_, hv⟩
      simpa only [hraw, fpos] using hh
    have haj : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) j k
        - fpos x j hv| < γ / 8 := by
      have hh := hcl j ⟨_, hv⟩
      simpa only [hraw, fpos] using hh
    have h1 := abs_lt.mp hai
    have h2 := abs_lt.mp haj
    have h3 := horder i hi j hj
    linarith [h1.1, h1.2, h2.1, h2.2, h3]
  have hηB : (η n : ℝ) ≤ (scale n : ℝ) * γ / 8 := by
    have h1 : (η n : ℝ) / (scale n : ℝ) ≤ |(η n : ℝ) / (scale n : ℝ)| := le_abs_self _
    have h2 : (η n : ℝ) / (scale n : ℝ) * (scale n : ℝ) = (η n : ℝ) := by field_simp
    nlinarith [hηn, h1, hscn]
  have hLB : (2 : ℝ) ≤ (scale n : ℝ) * γ / 4 := by
    have h1 : 8 / γ * γ = 8 := by field_simp
    nlinarith [hbn, hγ]
  have hpos : ∀ i : ι, 0 ≤ X n i (τ n (level n) + k) := by
    intro i
    have h1 := pos_ge_range (X := X n) (τ := τ n) (hτ n) (hne n) (r := level n)
      (T := T) (L := scale n) (n := τ n (level n) + k) (i := i) (hdr n)
      (Nat.le_add_right _ _) (Nat.add_le_add_left (by exact_mod_cast hk_le) _)
    have h3 : (((T + 3) * scale n : ℕ) : ℤ) ≤ ((level n : ℤ)) := by exact_mod_cast hr n
    have h4 : (((T + 2) * scale n : ℕ) : ℤ) ≤ ((level n : ℤ)) := by
      have h5 : (T + 2) * scale n ≤ (T + 3) * scale n :=
        Nat.mul_le_mul_right _ (by omega)
      have h6 : ((T + 2) * scale n : ℕ) ≤ level n := le_trans h5 (hr n)
      exact_mod_cast h6
    have h7 : (0 : ℤ) ≤ X n i (τ n (level n) + k) := by linarith
    exact_mod_cast h7
  refine ⟨fun i _ => hpos i, hD, hJ, ?_⟩
  intro i hi j hj
  have hj' : j ∈ Finset.univ \ D := hj
  have sp := hspread i hi j hj'
  have hLagJ : runMaxI (X n) j (τ n (level n) + k) - X n j (τ n (level n) + k) ≤ (η n : ℤ) :=
    hln j k hk1 hk2
  have hLagZ : runMaxI (X n) j (τ n (level n) + k)
      ≤ X n j (τ n (level n) + k) + (η n : ℤ) := by linarith [hLagJ]
  have hLagR : ((runMaxI (X n) j (τ n (level n) + k) : ℤ) : ℝ)
      ≤ ((X n j (τ n (level n) + k) : ℤ) : ℝ) + (η n : ℝ) := by
    exact_mod_cast hLagZ
  have hdiff : ((X n i (τ n (level n) + k) : ℝ) - (X n j (τ n (level n) + k) : ℝ))
      = (scale n : ℝ) * (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i k
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j k) := by
    unfold scaledPosition
    field_simp
    ring
  have hmain : ((runMaxI (X n) j (τ n (level n) + k) : ℤ) : ℝ) + 2
      ≤ ((X n i (τ n (level n) + k) : ℤ) : ℝ) := by
    have h9 : ((X n i (τ n (level n) + k) : ℤ) : ℝ)
        - ((X n j (τ n (level n) + k) : ℤ) : ℝ) ≥ (scale n : ℝ) * (γ * 3 / 4) := by
      rw [hdiff]
      nlinarith [sp, hscn]
    linarith
  have h' : ((runMaxI (X n) j (τ n (level n) + k) + 2 : ℤ) : ℝ)
      ≤ ((X n i (τ n (level n) + k) : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast h'

/-! ## 4. Pointwise coalescence does not need `(coincide)` persistence

The paper's `(5.6)` is stated as "all fluid positions coincide at one time below `B - 2`",
and the source then uses `(coincide)` only to keep them equal afterwards.  For the halving
clause (`FluidCoincide.halving_eventually_of_pointwise_coalescence_B`) only the *single*
coincident time is consumed.  This section records that the single-time statement follows
from `(meet)`/`JoinRuleFrom`, the one-sided motion `(fluid)` and the diameter seed, with
**no** `StickyOn` and no leader persistence. -/

/-- **Pointwise fluid coalescence from the meeting rule alone.**

`FluidMerge.exists_persistent_coalescence` uses `StickyOn` to keep the paths equal *after*
the first full-coincidence time.  The first full-coincidence time itself is the output of
`exists_coalescence_aux` and needs neither `StickyOn` nor leader persistence: a strictly
growing leading set that reaches the whole pack means every coordinate equals the maximum. -/
theorem coalesced_at_some_time_of_join {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ → ℝ) {s₀ b D T : ℝ}
    (hmove : FluidMerge.FluidMotionOn x s₀ T) (hjoin : FluidMerge.JoinRuleFrom x s₀ b T)
    (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hs₀ : s₀ ≤ D - 1) (hgap₀ : FluidMerge.fluidGap (fun i => x i s₀) ≤ D)
    (hlim : D * (1 + b) ^ (Fintype.card ι - 1) - 1 < T) :
    ∃ u, s₀ ≤ u ∧ u ≤ D * (1 + b) ^ (Fintype.card ι - 1) - 1 ∧ ∀ i j, x i u = x j u := by
  have hcard₀ : 0 + 1 ≤ (FluidMerge.leaders (fun i => x i s₀)).card := by
    simpa using (Finset.card_pos.mpr (FluidMerge.leaders_nonempty (fun i => x i s₀)))
  obtain ⟨u, hsu, hu, hlead⟩ := FluidMerge.exists_coalescence_aux x s₀ b D T hmove hjoin hD hb
    hlim (Fintype.card ι) 0 s₀ (Nat.sub_le _ _) hcard₀ le_rfl (by simpa using hs₀)
    (by simpa using hgap₀)
  refine ⟨u, hsu, hu, fun i j => ?_⟩
  have hi := (FluidMerge.leaders_eq_univ_iff (fun k => x k u)).mp hlead i
  have hj := (FluidMerge.leaders_eq_univ_iff (fun k => x k u)).mp hlead j
  exact hi.trans hj.symm

/-- **The paper's `(5.6)` shape**: one coincident fluid time in `[64⌈C⌉, B-1]`.

The start is the sharp window origin `64 * n` with `n = ⌈C⌉`, the diameter seed is
`1 + 64 n` (`FluidJoin.fluidGap_le_one_add` at the fluid level), and the geometric margin is
the `(BTchoice)` inequality at the ceiling.  The meeting rule is the only remaining input. -/
theorem coalesced_below_B_of_join {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ → ℝ) {C b : ℝ} {n B T : ℝ}
    (hn : C ≤ n) (hn0 : 0 ≤ n)
    (hmove : FluidMerge.FluidMotionOn x (64 * n) T) (hjoin : FluidMerge.JoinRuleFrom x (64 * n) b T)
    (hb : 0 ≤ b)
    (hB : (1 + 64 * n) * (1 + b) ^ (Fintype.card ι - 1) - 1 < B - 2)
    (hBT : B - 2 < T)
    (hgap₀ : FluidMerge.fluidGap (fun i => x i (64 * n)) ≤ 1 + 64 * n) :
    ∃ u, 64 * n ≤ u ∧ u < B - 2 ∧ ∀ i j, x i u = x j u := by
  obtain ⟨u, hsu, hu, hcoin⟩ := coalesced_at_some_time_of_join x (s₀ := 64 * n) (b := b)
    (D := 1 + 64 * n) (T := T) hmove hjoin (by nlinarith)
    hb (le_of_eq (by rw [add_sub_cancel_left])) hgap₀ (hB.trans hBT)
  exact ⟨u, hsu, lt_of_le_of_lt hu hB, hcoin⟩
