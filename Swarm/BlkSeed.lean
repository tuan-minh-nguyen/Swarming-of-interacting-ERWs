/-
# The fluid-limit leader seed for the finite top-block merge

`results/lean/areas/tightness/COINCIDENCE_GENERAL_BLOCK.md` lists as open "the
fluid-limit small-spread leader seed required to initialise the source's
Section-5.1 merger".  This file supplies exactly that finite-`L` seed, from the
accepted compactness exports and nothing else:

* `leadersAt x t` — the set of walkers attaining the fluid maximum at the fluid
  time `t`; the fluid face of the source's record set `A = A(s)`.
* `recordFamily_apply_of_eq` / `scaledPosition_at_knot_tendsto` — the actual
  interpolant at a grid knot is the scaled discrete position, so the accepted
  uniform convergence of the actual interpolants (`recordFamily`, the object
  produced by `FluidInterpolation.exists_record_interpolated_limit_subseq`)
  specialises to convergence of the literal discrete positions at the raw time
  `τ_r + m*L`, at fluid time `m`.
* `leadersAt_spread_eventually` — the source's `(4.1)`: the spread of the leader
  block at the discrete time `τ_r + m*L` is `o(L)`.
* `leadersAt_topBlock_eventually` — that block is a literal `JoinStep.TopBlock`
  of the discrete configuration at that time.
* `exists_seed_topBlock` — the two combined, with a single fixed set `D₀`
  (the fluid leader set) and the `o(L)` statement in the usable "for every
  `b > 0`, eventually spread `≤ b*L`" form.
* `seed_at_window` — the same at the source's sharp window start
  `m = 64*⌈C⌉`, with the window endpoint `τ_r + 64⌈C⌉L ≤ τ_r + TL` recorded,
  which is precisely the hypothesis shape of `BlkCoin.merge_round_persist'`.

No probability, no local-good event, no `NoCoalescence`, no tightness and no
`MainClaim` appears.  Every conclusion is about the actual integer positions
`X n i (τ_r + m*L)`, not about the limit object alone.
-/
import Swarm.FluidInterpolationLimit
import Swarm.JoinCore

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

set_option linter.unusedSectionVars false

namespace BlkSeed

open FluidInterpolation FluidLimit Glue JoinStep

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The leader set of a fluid configuration -/

/-- The walkers attaining the fluid maximum at the fluid time `t`. -/
noncomputable def leadersAt {T : ℝ} (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (t : Set.Icc (0 : ℝ) T) : Finset ι :=
  Finset.univ.filter (fun i => x i t = Finset.univ.sup' Finset.univ_nonempty (fun j => x j t))

theorem mem_leadersAt {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} {i : ι} :
    i ∈ leadersAt x t ↔ Finset.univ.sup' Finset.univ_nonempty (fun j => x j t) = x i t := by
  simp [leadersAt, eq_comm]

theorem leadersAt_nonempty {T : ℝ} (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (t : Set.Icc (0 : ℝ) T) : (leadersAt x t).Nonempty := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun j => x j t)
  exact ⟨i, mem_leadersAt.mpr hi⟩

theorem leadersAt_eq_sup {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} {i : ι} (hi : i ∈ leadersAt x t) :
    x i t = Finset.univ.sup' Finset.univ_nonempty (fun j => x j t) :=
  (mem_leadersAt.mp hi).symm

theorem leadersAt_le {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} {i : ι} (hi : i ∈ leadersAt x t) (j : ι) : x j t ≤ x i t := by
  rw [leadersAt_eq_sup hi]
  exact Finset.le_sup' (fun j => x j t) (Finset.mem_univ j)

theorem leadersAt_eq {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} {i j : ι} (hi : i ∈ leadersAt x t) (hj : j ∈ leadersAt x t) :
    x i t = x j t := by
  rw [leadersAt_eq_sup hi, leadersAt_eq_sup hj]

theorem lt_sup_of_notMem {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} {j : ι} (hj : j ∉ leadersAt x t) :
    x j t < Finset.univ.sup' Finset.univ_nonempty (fun i => x i t) := by
  refine lt_of_le_of_ne (Finset.le_sup' (fun i => x i t) (Finset.mem_univ j)) ?_
  intro h
  exact hj (mem_leadersAt.mpr h.symm)

/-- A proper leader set keeps a strictly positive fluid gap to the rest of the pack. -/
theorem exists_gap_of_proper {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    {t : Set.Icc (0 : ℝ) T} (h : leadersAt x t ≠ Finset.univ) :
    ∃ δ > 0, ∀ j, j ∉ leadersAt x t →
      x j t ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => x i t) - δ := by
  have hne : (Finset.univ \ leadersAt x t).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact h (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
  obtain ⟨jmax, hjmax, hmax⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ \ leadersAt x t) hne (fun j => x j t)
  have hlt : x jmax t < Finset.univ.sup' Finset.univ_nonempty (fun i => x i t) :=
    lt_sup_of_notMem (Finset.mem_sdiff.mp hjmax).2
  refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun i => x i t) - x jmax t, by linarith, ?_⟩
  intro j hj
  have h1 : x j t ≤ (Finset.univ \ leadersAt x t).sup' hne (fun j => x j t) :=
    Finset.le_sup' (fun j => x j t) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)
  rw [hmax] at h1
  linarith

/-! ## 2. The actual interpolant at a grid knot -/

/-- The actual interpolant of the record window, evaluated at a grid knot, is the scaled
discrete position.  This is what lets the accepted uniform convergence of `recordFamily`
speak about the literal integer positions. -/
theorem recordFamily_apply_of_eq (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n) {T : ℝ} (n : ℕ) (i : ι) {t : Set.Icc (0 : ℝ) T} {k : ℕ}
    (ht : (t : ℝ) = (k : ℝ) / (scale n)) (hk : k ≤ rawHorizon T (scale n)) :
    (recordFamily X τ level scale hscale T n i) t
      = scaledPosition (X n) (level n) (τ n (level n)) (scale n) i k := by
  have h1 : (recordFamily X τ level scale hscale T n i) t
      = scaledInterp (X n) (level n) (τ n (level n)) (scale n) i
          (rawHorizon T (scale n)) (t : ℝ) := rfl
  rw [h1, ht]
  exact scaledInterp_at_knot (X n) (level n) (τ n (level n)) (scale n) i (hscale n) hk

/-- Knot convergence: uniform convergence of the actual interpolants gives convergence of the
literal discrete positions at the fluid time `m`, i.e. at the raw time `τ_r + m*L`. -/
theorem scaledPosition_at_knot_tendsto (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {t : Set.Icc (0 : ℝ) T} {m : ℕ} (hm : (t : ℝ) = (m : ℝ)) (i : ι) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
      (m * scale n)) atTop (𝓝 (x i t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ n in atTop,
      dist (x i t) ((recordFamily X τ level scale hscale T n i) t) < ε :=
    (Metric.tendstoUniformly_iff.mp (hconv i) ε hε).mono (fun n hn => hn t)
  filter_upwards [hev] with n hn
  have hscaleR : (0 : ℝ) ≤ (scale n : ℝ) := by positivity
  have hk : m * scale n ≤ rawHorizon T (scale n) := by
    unfold rawHorizon
    refine Nat.le_floor ?_
    calc ((m * scale n : ℕ) : ℝ) = (m : ℝ) * (scale n : ℝ) := by push_cast; ring
      _ = (t : ℝ) * (scale n : ℝ) := by rw [hm]
      _ ≤ T * (scale n : ℝ) := mul_le_mul_of_nonneg_right t.2.2 hscaleR
  have hksR : ((m * scale n : ℕ) : ℝ) = (m : ℝ) * (scale n : ℝ) := by push_cast; ring
  have hscn : (scale n : ℝ) ≠ 0 := by
    exact_mod_cast (hscale n).ne'
  have ht : ((t : ℝ)) = ((m * scale n : ℕ) : ℝ) / (scale n : ℝ) := by
    rw [hksR, hm]
    exact (mul_div_cancel_right₀ (m : ℝ) hscn).symm
  rw [recordFamily_apply_of_eq X τ level scale hscale n i ht hk] at hn
  rw [dist_comm] at hn
  exact hn

/-! ## 3. The seed: `o(L)` spread of the leader block at the discrete time `τ_r + m*L` -/

/-- The scaled discrete positions of any two leaders converge to the same fluid value. -/
theorem leadersAt_scaled_tendsto (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {t : Set.Icc (0 : ℝ) T} {m : ℕ} (hm : (t : ℝ) = (m : ℝ))
    {i j : ι} (hi : i ∈ leadersAt x t) (hj : j ∈ leadersAt x t) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (m * scale n)
        - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j (m * scale n))
      atTop (𝓝 0) := by
  have hi' := scaledPosition_at_knot_tendsto X τ level scale hscale hT x hconv hm i
  have hj' := scaledPosition_at_knot_tendsto X τ level scale hscale hT x hconv hm j
  have heq : x i t = x j t := leadersAt_eq hi hj
  have hsub := hi'.sub hj'
  rw [← heq, sub_self] at hsub
  exact hsub

/-- **The source's `(4.1)`, finite-`L` form.**  The spread of the leader block at the discrete
time `τ_r + m*L` is `o(L)`: for every `b > 0` and all sufficiently large scales,
`spread(leadersAt) ≤ b * L`. -/
theorem leadersAt_spread_eventually (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {t : Set.Icc (0 : ℝ) T} {m : ℕ} (hm : (t : ℝ) = (m : ℝ)) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop,
      ((spreadS (X n) (leadersAt x t) (τ n (level n) + m * scale n) : ℤ) : ℝ)
        ≤ b * (scale n : ℝ) := by
  classical
  have hpair : ∀ i ∈ leadersAt x t, ∀ j ∈ leadersAt x t, ∀ᶠ n in atTop,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (m * scale n)
        - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j (m * scale n)|
        ≤ b / 4 := by
    intro i hi j hj
    have hz := leadersAt_scaled_tendsto X τ level scale hscale hT x hconv hm hi hj
    have hhalf : (0 : ℝ) < b / 4 := by positivity
    have hbnd := Metric.tendsto_nhds.mp hz (b / 4) hhalf
    filter_upwards [hbnd] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact le_of_lt hn
  have hall : ∀ᶠ n in atTop,
      ∀ i ∈ leadersAt x t, ∀ j ∈ leadersAt x t,
        |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (m * scale n)
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j (m * scale n)|
          ≤ b / 4 := by
    rw [Finset.eventually_all]
    intro i hi
    rw [Finset.eventually_all]
    intro j hj
    exact hpair i hi j hj
  filter_upwards [hall] with n hn
  obtain ⟨i₁, hi₁, hmax1⟩ := exists_sMax (X := X n) (S := leadersAt x t)
    (n := τ n (level n) + m * scale n) (leadersAt_nonempty x t)
  obtain ⟨j₁, hj₁, hmin1⟩ := exists_sMin (X := X n) (S := leadersAt x t)
    (n := τ n (level n) + m * scale n) (leadersAt_nonempty x t)
  have hbound := hn i₁ hi₁ j₁ hj₁
  have hscaleR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hscalediff :
      ((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ)) / (scale n : ℝ)
      = scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ (m * scale n)
        - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (m * scale n) := by
    unfold scaledPosition
    ring
  have hspread : ((spreadS (X n) (leadersAt x t) (τ n (level n) + m * scale n) : ℤ) : ℝ)
      = (X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ) := by
    unfold spreadS
    rw [hmax1, hmin1]
    push_cast
    ring
  rw [hspread]
  have hmul : ((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ))
      = (scale n : ℝ) * (((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ)) / (scale n : ℝ)) := by
    field_simp
  have habs : |((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ))|
      = (scale n : ℝ) * |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁
            (m * scale n)
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (m * scale n)| := by
    rw [hmul, abs_mul, abs_of_pos hscaleR, hscalediff]
  calc ((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ))
      ≤ |((X n i₁ (τ n (level n) + m * scale n) : ℝ)
        - (X n j₁ (τ n (level n) + m * scale n) : ℝ))| := le_abs_self _
    _ = (scale n : ℝ) * |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁
            (m * scale n)
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (m * scale n)| := habs
    _ ≤ (scale n : ℝ) * (b / 4) := mul_le_mul_of_nonneg_left hbound hscaleR.le
    _ ≤ b * (scale n : ℝ) := by nlinarith [hscaleR]


/-- **The top-block half of the seed.**  If the fluid leader set is proper, then for all
sufficiently large scales the leader set is a literal block of largest positions of the
discrete configuration at the time `τ_r + m*L`. -/
theorem leadersAt_topBlock_eventually (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {t : Set.Icc (0 : ℝ) T} {m : ℕ} (hm : (t : ℝ) = (m : ℝ))
    (hproper : leadersAt x t ≠ Finset.univ) :
    ∀ᶠ n in atTop, TopBlock (X n) (leadersAt x t) (τ n (level n) + m * scale n) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_of_proper hproper
  have hpair : ∀ i ∈ leadersAt x t, ∀ j ∈ Finset.univ \ leadersAt x t, ∀ᶠ n in atTop,
      X n j (τ n (level n) + m * scale n) ≤ X n i (τ n (level n) + m * scale n) := by
    intro i hi j hj
    have hj' : j ∉ leadersAt x t := (Finset.mem_sdiff.mp hj).2
    have hiT := scaledPosition_at_knot_tendsto X τ level scale hscale hT x hconv hm i
    have hjT := scaledPosition_at_knot_tendsto X τ level scale hscale hT x hconv hm j
    have hle : x j t ≤ x i t - δ := by
      rw [leadersAt_eq_sup hi]
      exact hgap j hj'
    have hε : (0 : ℝ) < δ / 4 := by positivity
    have h1 : ∀ᶠ n in atTop,
        |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (m * scale n)
          - x i t| < δ / 4 := by
      have hbnd := Metric.tendsto_nhds.mp hiT (δ / 4) hε
      filter_upwards [hbnd] with n hn
      rwa [Real.dist_eq] at hn
    have h2 : ∀ᶠ n in atTop,
        |scaledPosition (X n) (level n) (τ n (level n)) (scale n) j (m * scale n)
          - x j t| < δ / 4 := by
      have hbnd := Metric.tendsto_nhds.mp hjT (δ / 4) hε
      filter_upwards [hbnd] with n hn
      rwa [Real.dist_eq] at hn
    filter_upwards [h1, h2] with n hn1 hn2
    have hscaleR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hlt : scaledPosition (X n) (level n) (τ n (level n)) (scale n) j (m * scale n)
        < scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (m * scale n) := by
      have h3 := (abs_lt.mp hn1).1
      have h4 := (abs_lt.mp hn2).2
      linarith
    have hcast : (((X n j (τ n (level n) + m * scale n) : ℝ) - (level n : ℝ))
          / (scale n : ℝ))
        < (((X n i (τ n (level n) + m * scale n) : ℝ) - (level n : ℝ))
          / (scale n : ℝ)) := hlt
    have hreal : (X n j (τ n (level n) + m * scale n) : ℝ)
        < (X n i (τ n (level n) + m * scale n) : ℝ) := by
      have hstep := (div_lt_div_iff_of_pos_right hscaleR).mp hcast
      linarith
    exact_mod_cast le_of_lt hreal
  have hall : ∀ᶠ n in atTop, ∀ i ∈ leadersAt x t, ∀ j ∈ Finset.univ \ leadersAt x t,
      X n j (τ n (level n) + m * scale n) ≤ X n i (τ n (level n) + m * scale n) := by
    rw [Finset.eventually_all]
    intro i hi
    rw [Finset.eventually_all]
    intro j hj
    exact hpair i hi j hj
  refine hall.mono ?_
  intro n hn i hi j hj
  exact hn i hi j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)

/-- **The fluid-limit leader seed.**  From the accepted uniform convergence of the actual
interpolants there is a single fixed set `D₀` (the fluid leader set at time `m`) which is a
nonempty block of largest positions of the discrete configuration at `τ_r + m*L` with
`o(L)` spread, uniformly eventually.  Either `D₀` is the whole pack, or the top-block
statement holds eventually. -/
theorem exists_seed_topBlock (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {t : Set.Icc (0 : ℝ) T} {m : ℕ} (hm : (t : ℝ) = (m : ℝ))
    {b : ℝ} (hb : 0 < b) :
    ∃ D₀ : Finset ι, D₀.Nonempty ∧ D₀ = leadersAt x t ∧
      (∀ᶠ n in atTop,
        ((spreadS (X n) D₀ (τ n (level n) + m * scale n) : ℤ) : ℝ) ≤ b * (scale n : ℝ)) ∧
      (D₀ = Finset.univ ∨
        ∀ᶠ n in atTop, TopBlock (X n) D₀ (τ n (level n) + m * scale n)) := by
  refine ⟨leadersAt x t, leadersAt_nonempty x t, rfl,
    leadersAt_spread_eventually X τ level scale hscale hT x hconv hm b hb, ?_⟩
  by_cases hproper : leadersAt x t = Finset.univ
  · exact Or.inl hproper
  · exact Or.inr (leadersAt_topBlock_eventually X τ level scale hscale hT x hconv hm hproper)

/-! ## 4. The seed at the source's sharp window start `64*⌈C⌉` -/

/-- The seed at `m = 64*⌈C⌉`, together with the exact window endpoint used by
`BlkCoin.merge_round_persist'`: `τ_r + 64⌈C⌉L ≤ τ_r + TL` for natural `T ≥ 64⌈C⌉`. -/
theorem seed_at_window (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ)
    (level scale : ℕ → ℕ) (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {C : ℝ} {t : Set.Icc (0 : ℝ) T} (hm : (t : ℝ) = ((64 * ⌈C⌉₊ : ℕ) : ℝ))
    {b : ℝ} (hb : 0 < b) :
    ∃ D₀ : Finset ι, D₀.Nonempty ∧ D₀ = leadersAt x t ∧
      (∀ᶠ n in atTop,
        ((spreadS (X n) D₀ (τ n (level n) + 64 * ⌈C⌉₊ * scale n) : ℤ) : ℝ)
          ≤ b * (scale n : ℝ)) ∧
      (D₀ = Finset.univ ∨
        ∀ᶠ n in atTop,
          TopBlock (X n) D₀ (τ n (level n) + 64 * ⌈C⌉₊ * scale n)) := by
  obtain ⟨D₀, hne, hD, hspread, htop⟩ :=
    exists_seed_topBlock (m := 64 * ⌈C⌉₊) X τ level scale hscale hT x hconv hm hb
  exact ⟨D₀, hne, hD, hspread, htop⟩

/-- The sharp window: for a natural horizon `Tn ≥ 64⌈C⌉`, the seed time lies in
`[τ_r + 64⌈C⌉L, τ_r + Tn*L]`. -/
theorem seed_time_mem_window {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    {C : ℝ} {Tn : ℕ} (hT64 : 64 * ⌈C⌉₊ ≤ Tn) (n : ℕ) :
    τ n (level n) + 64 * ⌈C⌉₊ * scale n ≤ τ n (level n) + Tn * scale n :=
  Nat.add_le_add_left (Nat.mul_le_mul_right (scale n) hT64) _

end BlkSeed
