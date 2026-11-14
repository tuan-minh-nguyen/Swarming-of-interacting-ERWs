/-
# Dependency-light fluid-limit approximation for the local-good geometry

This module supplies two analytic links which are absent from
`FluidGeometryLight`: simultaneous Arzela--Ascoli extraction for bounded
uniformly Lipschitz path families, and passage of a uniform finite-window
record-lag estimate to `AtRecordsOn`.  Discrete positions and maxima below use
`LeaderDescent.runMax`, i.e. the maximum over the entire actual past.
No probability estimate, interpolation theorem, local-good estimate, or
positive record-advance lower bound is asserted here.
-/
import Swarm.FluidGeometryLight
import Swarm.LeaderDescent
import Swarm.RecordDefect
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open Filter Topology
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidLimit

open FluidGeometry

universe u v

/-- **Simultaneous bounded Arzela--Ascoli extraction.**  Uniform absolute
bounds replace any assumption that the paths start at zero.  The same
subsequence works for every coordinate, for the finite walker coordinate type.
The limit retains the common Lipschitz constant and range bounds, and each
coordinate converges in the uniform metric. -/
theorem exists_lipschitz_uniform_limit_subseq
    {τ : Type u} {ι : Type v} [PseudoMetricSpace τ] [CompactSpace τ] [Fintype ι]
    (F : ℕ → ι → (τ →ᵇ ℝ)) (K : ℝ≥0) (a b : ℝ)
    (hlip : ∀ n i, LipschitzWith K (F n i))
    (hbdd : ∀ n i t, F n i t ∈ Set.Icc a b) :
    ∃ (x : ι → (τ →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, LipschitzWith K (x i)) ∧
      (∀ i t, x i t ∈ Set.Icc a b) ∧
      (∀ i, TendstoUniformly (fun n => F (φ n) i) (x i) atTop) := by
  let A : ι → Set (τ →ᵇ ℝ) := fun i => closure (Set.range (fun n => F n i))
  have hcompact : ∀ i, IsCompact (A i) := by
    intro i
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc a b) isCompact_Icc
    · intro f t hf
      obtain ⟨n, rfl⟩ := hf
      exact hbdd n i t
    · apply Metric.equicontinuous_of_continuity_modulus (fun d : ℝ => (K : ℝ) * d)
      · simpa using (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun d : ℝ => (K : ℝ) * d) (𝓝 0) (𝓝 ((K : ℝ) * 0)))
      · rintro s t ⟨f, n, rfl⟩
        exact (hlip n i).dist_le_mul s t
  have hmem : ∀ n, F n ∈ Set.pi Set.univ A := by
    intro n i _
    exact subset_closure ⟨n, rfl⟩
  obtain ⟨x, hx, φ, hφ, hlim⟩ := (isCompact_univ_pi hcompact).tendsto_subseq hmem
  have hcoord (i : ι) : Tendsto (fun n => F (φ n) i) atTop (𝓝 (x i)) := by
    have h := (continuous_apply i).continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def] using h
  have hunif (i : ι) : TendstoUniformly (fun n => F (φ n) i) (x i) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hcoord i)
  have hpoint (i : ι) (t : τ) :
      Tendsto (fun n => F (φ n) i t) atTop (𝓝 (x i t)) := (hunif i).tendsto_at t
  refine ⟨x, φ, hφ, ?_, ?_, hunif⟩
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro s t
    apply le_of_tendsto ((hpoint i s).dist (hpoint i t))
    exact Eventually.of_forall fun n => (hlip (φ n) i).dist_le_mul s t
  · intro i t
    constructor
    · exact ge_of_tendsto (hpoint i t)
        (Eventually.of_forall fun n => (hbdd (φ n) i t).1)
    · exact le_of_tendsto (hpoint i t)
        (Eventually.of_forall fun n => (hbdd (φ n) i t).2)

/-- The paper's concrete compactness situation: one-Lipschitz rescaled paths
on `[0,T]` start in `[-1,0]`.  Uniform bounds `[-1-T,T]` are derived from
Lipschitzness; they are not added as hypotheses. -/
theorem exists_oneLipschitz_rescaled_limit_subseq {ι : Type v} [Fintype ι]
    (T : ℝ) (hT : 0 ≤ T) (F : ℕ → ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hlip : ∀ n i, LipschitzWith 1 (F n i))
    (z : Set.Icc (0 : ℝ) T) (hz : z = ⟨0, ⟨le_rfl, hT⟩⟩)
    (hstart : ∀ n i, F n i z ∈ Set.Icc (-1) 0) :
    ∃ (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, LipschitzWith 1 (x i)) ∧
      (∀ i t, x i t ∈ Set.Icc (-1 - T) T) ∧
      (∀ i, TendstoUniformly (fun n => F (φ n) i) (x i) atTop) ∧
      (∀ i, x i z ∈ Set.Icc (-1) 0) := by
  have hdist (t : Set.Icc (0 : ℝ) T) : dist t z ≤ T := by
    subst z
    change |(t : ℝ) - 0| ≤ T
    rw [sub_zero, abs_of_nonneg t.2.1]
    exact t.2.2
  have hbound : ∀ n i t, F n i t ∈ Set.Icc (-1 - T) T := by
    intro n i t
    have h1 : dist (F n i t) (F n i z) ≤ dist t z := by
      simpa using (hlip n i).dist_le_mul t z
    rw [Real.dist_eq] at h1
    have habs : |F n i t - F n i z| ≤ T := h1.trans (hdist t)
    have habs' := abs_le.mp habs
    have hz' := hstart n i
    constructor <;> linarith [habs'.1, habs'.2, hz'.1, hz'.2]
  obtain ⟨x, φ, hφ, hxlip, hxbound, hx⟩ :=
    exists_lipschitz_uniform_limit_subseq F 1 (-1 - T) T hlip hbound
  refine ⟨x, φ, hφ, hxlip, hxbound, hx, ?_⟩
  intro i
  constructor
  · exact ge_of_tendsto ((hx i).tendsto_at z)
      (Eventually.of_forall fun n => (hstart (φ n) i).1)
  · exact le_of_tendsto ((hx i).tendsto_at z)
      (Eventually.of_forall fun n => (hstart (φ n) i).2)

/-- Passage of the literal uniformly-small discrete increment errors to the
fluid drift inequalities `(fluid)`.  Both the lower and upper input errors are
quantified independently in `ε`; no exact-fluid increment predicate is assumed. -/
theorem fluid_increment_bounds_of_uniform_error {ι : Type v}
    (xL : ℕ → ι → ℝ → ℝ) (x : ι → ℝ → ℝ) (v s t : ℝ)
    (hx : ∀ i, TendstoUniformly (fun n => xL n i) (x i) atTop)
    (hlower : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i,
      -ε ≤ xL n i t - xL n i s)
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i,
      xL n i t - xL n i s ≤ v * (t - s) + ε) :
    ∀ i, 0 ≤ x i t - x i s ∧ x i t - x i s ≤ v * (t - s) := by
  intro i
  have hfwd : Tendsto (fun n => xL n i t - xL n i s) atTop
      (𝓝 (x i t - x i s)) := ((hx i).tendsto_at t).sub ((hx i).tendsto_at s)
  have hrev : Tendsto (fun n => xL n i s - xL n i t) atTop
      (𝓝 (x i s - x i t)) := ((hx i).tendsto_at s).sub ((hx i).tendsto_at t)
  constructor
  · have hnonpos : x i s - x i t ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      apply le_of_tendsto hrev
      exact (hlower ε hε).mono fun n hn => by linarith [hn i]
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto hfwd ((hupper ε hε).mono fun n hn => hn i)

/-- The threshold step in `(fluidmax)`.  If every coordinate has crossed
`q > m_i(0)` by `s₀` and is nondecreasing from `s₀` through `T`, then the
paper's limiting expression `max(m_i(0),x_i(t))` agrees with the coordinate.
The crossing premise remains an explicit local-occupation estimate; it is not
proved by compactness. -/
theorem atRecordsOn_max_initial_of_crossed
    {ι : Type v} (x : ι → ℝ → ℝ) (a : ι → ℝ) (q s₀ T : ℝ)
    (hinitial : ∀ i, a i ≤ q) (hcross : ∀ i, q < x i s₀)
    (hmono : ∀ i s t, s₀ ≤ s → s ≤ t → t ≤ T → x i s ≤ x i t) :
    AtRecordsOn x (fun i t => max (a i) (x i t)) s₀ T := by
  intro i t hst htT
  apply max_eq_right
  exact (hinitial i).trans_lt ((hcross i).trans_le (hmono i s₀ t le_rfl hst htT)) |>.le

/-- Position on a shifted raw-time grid, with the record level and spatial
scale made explicit.  No truncation of the discrete path is involved. -/
noncomputable def scaledPosition {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → ℕ → ℤ)
    (level start scale : ℕ) (i : ι) (k : ℕ) : ℝ :=
  ((X i (start + k) : ℝ) - (level : ℝ)) / (scale : ℝ)

/-- The actual running maximum on the same shifted raw-time grid. -/
noncomputable def scaledMaximum {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → ℕ → ℤ)
    (level start scale : ℕ) (i : ι) (k : ℕ) : ℝ :=
  ((LeaderDescent.runMax X i (start + k) : ℝ) - (level : ℝ)) / (scale : ℝ)

/-- The normalized record lag is exactly the scaled integer running-maximum
lag; in particular the maximum is over `0,...,start+k`, not just the window. -/
theorem scaledMaximum_sub_scaledPosition {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → ℕ → ℤ)
    (level start scale : ℕ) (i : ι) (k : ℕ) :
    scaledMaximum X level start scale i k - scaledPosition X level start scale i k =
      (((LeaderDescent.runMax X i (start + k) - X i (start + k) : ℤ) : ℝ)) /
        (scale : ℝ) := by
  rw [scaledMaximum, scaledPosition, Int.cast_sub]
  ring

/-- Running maxima dominate the current discrete positions. -/
theorem scaledPosition_le_scaledMaximum {ι : Type*} [Fintype ι] [DecidableEq ι] (X : ι → ℕ → ℤ)
    (level start scale : ℕ) (i : ι) (k : ℕ) :
    scaledPosition X level start scale i k ≤ scaledMaximum X level start scale i k := by
  have h := LeaderDescent.le_runMax X i (start + k)
  have hc : (X i (start + k) : ℝ) ≤ (LeaderDescent.runMax X i (start + k) : ℝ) := by
    exact_mod_cast h
  rw [scaledPosition, scaledMaximum]
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg scale)

/-- At the record time, `d_r ≤ L` gives exactly the initial bounds used by
Arzela--Ascoli after scaling by `L`. -/
theorem scaledPosition_at_record_mem {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (X : ι → ℕ → ℤ) (τ : ℕ → ℕ)
    (hτ : RecordDefect.IsRecord X τ) (r scale : ℕ) (hscale : 0 < scale)
    (hd : RecordDefect.defect X τ r ≤ (scale : ℤ)) (i : ι) :
    scaledPosition X r (τ r) scale i 0 ∈ Set.Icc (-1) 0 := by
  have hscaleR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  have hupperZ : X i (τ r) ≤ (r : ℤ) := by
    rw [← (hτ r).2]
    exact RecordDefect.le_runMax (τ r) i
  have hlowZ : (r : ℤ) - X i (τ r) ≤ (scale : ℤ) := by
    apply le_trans ?_ hd
    rw [RecordDefect.defect]
    have hmin := RecordDefect.runMin_le (X := X) (τ r) i
    omega
  have hupperR : (X i (τ r) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hupperZ
  have hlowR : ((r : ℤ) - X i (τ r) : ℤ) ≤ (scale : ℤ) := hlowZ
  have hlowR' : ((r : ℝ) - (X i (τ r) : ℝ)) ≤ (scale : ℝ) := by
    exact_mod_cast hlowR
  rw [scaledPosition, Nat.add_zero]
  constructor
  · apply (le_div_iff₀ hscaleR).2
    nlinarith
  · apply (div_le_iff₀ hscaleR).2
    nlinarith

/-- The leading rescaled initial position is zero at a genuine record time. -/
theorem sup_scaledPosition_at_record {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (X : ι → ℕ → ℤ) (τ : ℕ → ℕ)
    (hτ : RecordDefect.IsRecord X τ) (r scale : ℕ) (hscale : 0 < scale) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => scaledPosition X r (τ r) scale i 0) = 0 := by
  have hscaleR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    have hupperZ : X i (τ r) ≤ (r : ℤ) := by
      rw [← (hτ r).2]
      exact RecordDefect.le_runMax (τ r) i
    have hupperR : (X i (τ r) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hupperZ
    rw [scaledPosition, Nat.add_zero]
    apply (div_le_iff₀ hscaleR).2
    nlinarith
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      Finset.univ_nonempty (fun i => X i (τ r))
    have hval : X i (τ r) = (r : ℤ) := by
      rw [← (hτ r).2, RecordDefect.runMax]
      exact hi.symm
    calc
      0 = scaledPosition X r (τ r) scale i 0 := by
        rw [scaledPosition, Nat.add_zero, hval]
        simp
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun j => scaledPosition X r (τ r) scale j 0) :=
        Finset.le_sup' (fun j => scaledPosition X r (τ r) scale j 0) (Finset.mem_univ i)

/-- Full paper-window compactness interface.  The continuous bounded maps are
the supplied interpolated paths (the interpolation construction is outside
this module), but their initial values are identified with actual record
windows.  Compactness is nontrivially used, while the record-index constraint,
initial defect bound, and divergence of the scales are all preserved along the
single common subsequence. -/
theorem exists_record_rescaled_limit_subseq
    {ι : Type v} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (F : ℕ → ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ))
    (hτ : ∀ n, RecordDefect.IsRecord (X n) (τ n))
    (hlarge : ∀ n, C₀ * scale n ≤ level n)
    (hscaleTop : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hd : ∀ n, RecordDefect.defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (z : Set.Icc (0 : ℝ) T) (hz : z = ⟨0, ⟨le_rfl, hT⟩⟩)
    (hlip : ∀ n i, LipschitzWith 1 (F n i))
    (hFstart : ∀ n i, F n i z =
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0) :
    ∃ (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, LipschitzWith 1 (x i)) ∧
      (∀ i t, x i t ∈ Set.Icc (-1 - T) T) ∧
      (∀ i, TendstoUniformly (fun n => F (φ n) i) (x i) atTop) ∧
      (∀ i, x i z ∈ Set.Icc (-1) 0) ∧
      (∀ n, C₀ * scale (φ n) ≤ level (φ n)) ∧
      Tendsto (fun n => scale (φ n)) atTop atTop ∧
      (∀ n, RecordDefect.defect (X (φ n)) (τ (φ n)) (level (φ n)) ≤
        (scale (φ n) : ℤ)) := by
  have hstart : ∀ n i, F n i z ∈ Set.Icc (-1) 0 := by
    intro n i
    rw [hFstart]
    exact scaledPosition_at_record_mem (X n) (τ n) (hτ n) (level n) (scale n)
      (hscale n) (hd n) i
  obtain ⟨x, φ, hφ, hxlip, hxbound, hx, hxstart⟩ :=
    exists_oneLipschitz_rescaled_limit_subseq T hT F hlip z hz hstart
  refine ⟨x, φ, hφ, hxlip, hxbound, hx, hxstart,
    (fun n => hlarge (φ n)), ?_, (fun n => hd (φ n))⟩
  exact hscaleTop.comp hφ.tendsto_atTop

/-- **Uniform record-lag passage to the fluid limit.**  The finite paths and
finite running maxima have the same real time domain as the fluid paths.  The
lag estimate is uniform in every coordinate and every time in `[s₀,T]`; the
result is exactly `FluidGeometry.AtRecordsOn`. -/
theorem atRecordsOn_of_uniform_record_lag
    {ι : Type v}
    (xL mL : ℕ → ι → ℝ → ℝ) (x m : ι → ℝ → ℝ) (s₀ T : ℝ)
    (hx : ∀ i, TendstoUniformly (fun n => xL n i) (x i) atTop)
    (hm : ∀ i, TendstoUniformly (fun n => mL n i) (m i) atTop)
    (hlag : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i t, s₀ ≤ t → t ≤ T →
      dist (mL n i t) (xL n i t) < ε) :
    AtRecordsOn x m s₀ T := by
  intro i t hst htT
  apply dist_eq_zero.mp
  by_contra hne
  have hpos : 0 < dist (m i t) (x i t) := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  let ε := dist (m i t) (x i t) / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨n, hxn, hmn, hlagn⟩ :=
    ((Metric.tendstoUniformly_iff.mp (hx i) ε hε).and
      ((Metric.tendstoUniformly_iff.mp (hm i) ε hε).and (hlag ε hε))).exists
  have hlagn' := hlagn i t hst htT
  have hxn' := hxn t
  have hmn' := hmn t
  have htri := dist_triangle4 (m i t) (mL n i t) (xL n i t) (x i t)
  dsimp [ε] at hlagn' hxn' hmn'
  rw [dist_comm (x i t) (xL n i t)] at hxn'
  linarith

/-- Direct discrete-record version.  `sample n t` chooses an integer raw-time
offset, `horizon n` gives the explicit future bound, and the error profile is
for the genuine full-past `LeaderDescent.runMax`. -/
theorem atRecordsOn_of_scaled_discrete_lag
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ℕ → ι → ℕ → ℤ) (level start scale : ℕ → ℕ)
    (sample : ℕ → ℝ → ℕ) (horizon : ℕ → ℕ)
    (x m : ι → ℝ → ℝ) (s₀ T : ℝ)
    (hx : ∀ i, TendstoUniformly
      (fun n t => scaledPosition (X n) (level n) (start n) (scale n) i (sample n t))
      (x i) atTop)
    (hm : ∀ i, TendstoUniformly
      (fun n t => scaledMaximum (X n) (level n) (start n) (scale n) i (sample n t))
      (m i) atTop)
    (hfuture : ∀ n t, s₀ ≤ t → t ≤ T → sample n t ≤ horizon n)
    (hlag : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i k, k ≤ horizon n →
      (((LeaderDescent.runMax (X n) i (start n + k) - X n i (start n + k) : ℤ) : ℝ)) /
        (scale n : ℝ) < ε) :
    AtRecordsOn x m s₀ T := by
  apply atRecordsOn_of_uniform_record_lag
    (xL := fun n i t => scaledPosition (X n) (level n) (start n) (scale n) i (sample n t))
    (mL := fun n i t => scaledMaximum (X n) (level n) (start n) (scale n) i (sample n t))
    (x := x) (m := m) (s₀ := s₀) (T := T) hx hm
  intro ε hε
  filter_upwards [hlag ε hε] with n hn
  intro i t hst htT
  rw [Real.dist_eq, scaledMaximum_sub_scaledPosition]
  have hnonneg : 0 ≤ scaledMaximum (X n) (level n) (start n) (scale n) i (sample n t) -
      scaledPosition (X n) (level n) (start n) (scale n) i (sample n t) :=
    sub_nonneg.mpr (scaledPosition_le_scaledMaximum (X n) (level n) (start n) (scale n)
      i (sample n t))
  have hnonneg' : 0 ≤
      (((LeaderDescent.runMax (X n) i (start n + sample n t) -
        X n i (start n + sample n t) : ℤ) : ℝ)) / (scale n : ℝ) := by
    rw [← scaledMaximum_sub_scaledPosition]
    exact hnonneg
  rw [abs_of_nonneg hnonneg']
  exact hn i (sample n t) (hfuture n t hst htT)

end FluidLimit
