/-
# Record-clock local window for the actual drift martingales `M^i`

This file turns the accepted count-free stopped-window estimate
`StoppedWindow.measureReal_band_stoppedWindow_le`
(`Swarm/StoppedMartingaleWindow.lean`, hash-identical copy built here)
into the paper's display `(locmart)` **at the true record clock of the actual model**, with no
union over clock values, no truncation `tau_r /\\ A`, and no record-time tail.

Content, in order.

* `stronglyMeasurable_driftMartingale`, `abs_driftMartingale_le`,
  `integrable_driftMartingale`, `condExp_increments_driftMartingale` - the four standing
  hypotheses of the stopped-window theorem for the paper's own drift martingale
  `M^i = X^i - (2p-1)*excitedSteps^i` on the genuine enlarged filtration `Enl.enlFilt`: adapted
  strong measurability, integrability, zero conditional means (`(mart)`) and the pointwise
  increment bound `2`, which is unconditional - no carrier, no `(locmax)`, no `{d_r <= L}`.

* `stoppedWindowRec` - the two-endpoint record-clock window event
  `exists s <= n, exists k <= n-s, eps <= |M^i_{tau_r+s+k} - M^i_{tau_r+s}|`, written with the
  actual canonical record time `SwarmRecordMeas.Actual.recTimeA`, and
  `measureReal_stoppedWindowRec` - its measured bound
  `mu.real <= 2 (n+1)^2 exp (-(eps^2)/(16 n))`
  with `mu = Swarming.Uniform.arrayMeasure N`.  The random clock enters through the *bands*
  `ClockFibre.clockFibre p m r a` (the exact record fibres), which are `F_a`-measurable,
  pairwise disjoint and cover `ReachAll`, plus `ReachAll^c` being null
  (`ClockFibre.ae_mem_reachAll`).  This is the same null set as the `top`-fibre of
  `Swarming.Enl.maxClock` (`areas/filtration/StoppedClock.maxClock_top_subset_compl_reach`), so
  it is the genuine clock with its null top fibre; the `NatInf` object is not needed because the
  band form never reads the clock off `ReachAll^c`.

* `locMartBad`, `locMartGood` - the paper's `(locmart)` event family: on `locMartGood r T L`
  every walker `i` satisfies `|M^i_t - M^i_s| <= L^{3/4}` for all `tau_r <= s <= t <= tau_r+T*L`.
  `measureReal_locMartBad_le` is its unconditional union bound over the `N` walkers.

* `exists_locMartBad_le` - the same bound in the paper's profile
  `C_T exp (-c_T L^{1/16})`, so this component of the paper's good event is *discharged* (and
  with the stronger exponent `exp(-c L^{1/2})` before absorption).  Nothing is assumed about
  `d_r`: the display holds without the carrier `{d_r <= L}`.

What is **not** claimed here: any statement about `(lococc)`, `(loccoord)`, `(locgroup)`,
`(locmove)`, HalfClauseAt, `rho`, tightness, MainClaim or common speed.  The windowed group
martingale component is *not* touched: its increment envelope is only a.e. and not predictable at
the band index, so its record-clock transfer needs a separately named a.e.-carrier form
(`StoppedMartingaleWindow` only has the pointwise carrier form).
-/
import Swarm.StoppedMartingaleWindow
import Swarm.ClockFibreAzuma

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory
open SwarmRecordMeas SwarmRecordMeas.Actual

namespace RecordClock

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The drift martingale on the enlarged filtration -/

/-- The paper's drift martingale is adapted to the genuine enlarged filtration. -/
theorem stronglyMeasurable_driftMartingale (p : ℝ) (m t : ℕ) (i : Fin N) :
    StronglyMeasurable[Enl.enlFilt p m t] (fun U : Array N => driftMartingale p m U t i) := by
  induction t with
  | zero =>
      have hzero : (fun U : Array N => driftMartingale p m U 0 i) = fun _ => (0 : ℝ) := by
        funext U
        simp [Swarming.Trajectory.driftMartingale, Swarming.Trajectory.excitedSteps]
      rw [hzero]
      exact stronglyMeasurable_const
  | succ t ih =>
      have hfun : (fun U : Array N => driftMartingale p m U (t + 1) i)
          = fun U => driftMartingale p m U t i + ExcOcc.martIncr p m t i U := by
        funext U
        rw [ExcOcc.martIncr_eq_driftMartingale]
        ring
      rw [hfun]
      refine (ih.mono ((Enl.enlFilt p m).mono (Nat.le_succ t))).add ?_
      exact (ExcOcc.stronglyMeasurable_martIncr p m t i).mono le_rfl

/-- The drift martingale has increments bounded by `2` in absolute value, so it is bounded by
`2 t` at time `t`.  Both are unconditional. -/
theorem abs_driftMartingale_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i : Fin N) (U : Array N) :
    |driftMartingale p m U t i| ≤ 2 * (t : ℝ) := by
  induction t with
  | zero =>
      have h0 : driftMartingale p m U 0 i = 0 := by
        simp [Swarming.Trajectory.driftMartingale, Swarming.Trajectory.excitedSteps]
      rw [h0]
      simp
  | succ t ih =>
      have hsplit : driftMartingale p m U (t + 1) i
          = driftMartingale p m U t i + ExcOcc.martIncr p m t i U := by
        rw [ExcOcc.martIncr_eq_driftMartingale]
        ring
      rw [hsplit]
      have hstep := ExcOcc.martIncr_abs_le hp0 hp1 m t i U
      have hcast : (2 : ℝ) * ((t + 1 : ℕ) : ℝ) = 2 * (t : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      calc |driftMartingale p m U t i + ExcOcc.martIncr p m t i U|
          ≤ |driftMartingale p m U t i| + |ExcOcc.martIncr p m t i U| := abs_add_le _ _
        _ ≤ 2 * (t : ℝ) + 2 := by linarith

/-- Every time slice of the drift martingale is integrable under the array measure. -/
theorem integrable_driftMartingale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (i : Fin N) :
    Integrable (fun U : Array N => driftMartingale p m U t i) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound
    (((stronglyMeasurable_driftMartingale p m t i).mono ((Enl.enlFilt p m).le t)).measurable.aestronglyMeasurable)
    (2 * (t : ℝ)) ?_
  filter_upwards with U
  rw [Real.norm_eq_abs]
  exact abs_driftMartingale_le hp0 hp1 m t i U

/-- The unit-step increment of the drift martingale is exactly the conditional-difference
`martIncr`, hence conditionally centred on the enlarged filtration. -/
theorem condExp_increments_driftMartingale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i : Fin N) :
    (arrayMeasure N)[StoppedWindow.increments
        (fun (t : ℕ) (U : Array N) => driftMartingale p m U t i) t
        | Enl.enlFilt p m t] =ᵐ[arrayMeasure N] 0 := by
  have hfun : StoppedWindow.increments
      (fun (t : ℕ) (U : Array N) => driftMartingale p m U t i) t
      = ExcOcc.martIncr p m t i := by
    funext U
    rw [StoppedWindow.increments_apply, ExcOcc.martIncr_eq_driftMartingale]
  rw [hfun]
  exact ExcOcc.condExp_martIncr hp0 hp1 m t i

/-- The pointwise increment bound `|M_{t+1} - M_t| <= 2`. -/
theorem abs_increment_driftMartingale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i : Fin N) (U : Array N) :
    |driftMartingale p m U (t + 1) i - driftMartingale p m U t i| ≤ 2 := by
  have h := ExcOcc.martIncr_abs_le hp0 hp1 m t i U
  rwa [ExcOcc.martIncr_eq_driftMartingale] at h

/-! ## 2. The two-endpoint record-clock window -/

/-- The two-endpoint deviation event of the drift martingale of walker `i` over the random
window `[tau_r, tau_r + n]`, with `tau_r` the actual canonical record time. -/
def stoppedWindowRec (p : ℝ) (m r n : ℕ) (ε : ℝ) (i : Fin N) : Set (Array N) :=
  {U | ∃ s ≤ n, ∃ k ≤ n - s,
    ε ≤ |driftMartingale p m U (recTimeA p m U r + s + k) i
          - driftMartingale p m U (recTimeA p m U r + s) i|}

@[simp] theorem mem_stoppedWindowRec {p : ℝ} {m r n : ℕ} {ε : ℝ} {i : Fin N} {U : Array N} :
    U ∈ stoppedWindowRec p m r n ε i ↔
      ∃ s ≤ n, ∃ k ≤ n - s,
        ε ≤ |driftMartingale p m U (recTimeA p m U r + s + k) i
              - driftMartingale p m U (recTimeA p m U r + s) i| := Iff.rfl

/-- **Count-free two-endpoint bound at the actual record clock.** -/
theorem measureReal_stoppedWindowRec {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (r : ℕ) (i : Fin N) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    (arrayMeasure N).real (stoppedWindowRec p m r n ε i) ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (16 * (n : ℝ))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hband := StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := arrayMeasure N) (ℱ := Enl.enlFilt p m)
    (Q := fun (t : ℕ) (U : Array N) => driftMartingale p m U t i)
    (σ := fun U : Array N => recTimeA p m U r)
    (B := fun a : ℕ => ClockFibre.clockFibre p m r a)
    (G := ReachAll p m)
    (fun t => stronglyMeasurable_driftMartingale p m t i)
    (fun t => integrable_driftMartingale hp0 hp1 m t i)
    (fun t => condExp_increments_driftMartingale hp0 hp1 m t i)
    (by norm_num : (0 : ℝ) < 2)
    (fun t U => abs_increment_driftMartingale hp0 hp1 m t i U)
    (fun a => ClockFibre.measurableSet_clockFibre p m r a)
    (fun a b hab => ClockFibre.disjoint_clockFibre p m r a b hab)
    (ClockFibre.reachAll_subset_iUnion_clockFibre p m r)
    (fun a => by
      rintro U ⟨hR, hfib⟩
      exact ClockFibre.recTimeA_eq_of_mem_clockFibre hR hfib)
    hn hε
  have hexp : (4 : ℝ) * (n : ℝ) * 2 ^ 2 = 16 * (n : ℝ) := by ring
  rw [hexp] at hband
  have hnull : (arrayMeasure N) {U : Array N | U ∉ ReachAll p m} = 0 := by
    have h := ClockFibre.ae_mem_reachAll (N := N) hp0 hp1 hm hN
    rwa [ae_iff] at h
  have hreal0 : (arrayMeasure N).real {U : Array N | U ∉ ReachAll p m} = 0 := by
    rw [Measure.real_def, hnull, ENNReal.toReal_zero]
  have hsub : stoppedWindowRec p m r n ε i ⊆
      {U : Array N | U ∉ ReachAll p m} ∪
        (ReachAll p m ∩ stoppedWindowRec p m r n ε i) := by
    intro U hU
    by_cases h : U ∈ ReachAll p m
    · exact Or.inr ⟨h, hU⟩
    · exact Or.inl h
  calc (arrayMeasure N).real (stoppedWindowRec p m r n ε i)
      ≤ (arrayMeasure N).real ({U : Array N | U ∉ ReachAll p m} ∪
          (ReachAll p m ∩ stoppedWindowRec p m r n ε i)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real {U : Array N | U ∉ ReachAll p m}
          + (arrayMeasure N).real (ReachAll p m ∩ stoppedWindowRec p m r n ε i) :=
        measureReal_union_le _ _
    _ = (arrayMeasure N).real (ReachAll p m ∩ stoppedWindowRec p m r n ε i) := by
        rw [hreal0, zero_add]
    _ ≤ 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (16 * (n : ℝ))) := hband

/-! ## 3. The `(locmart)` event and its union bound -/

/-- The failure event of the paper's display `(locmart)` at the record window
`[tau_r, tau_r+T*L]`. -/
def locMartBad (p : ℝ) (m r T L : ℕ) : Set (Array N) :=
  {U | ∃ i : Fin N, ∃ s ≤ T * L, ∃ k ≤ T * L - s,
    (L : ℝ) ^ ((3 : ℝ) / 4) ≤
      |driftMartingale p m U (recTimeA p m U r + s + k) i
        - driftMartingale p m U (recTimeA p m U r + s) i|}

/-- The good event: the paper's display `(locmart)` holds for every walker at the record
window. -/
def locMartGood (p : ℝ) (m r T L : ℕ) : Set (Array N) := (locMartBad p m r T L)ᶜ

theorem locMartBad_eq_iUnion (p : ℝ) (m r T L : ℕ) :
    locMartBad p m r T L
      = ⋃ i : Fin N, stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i := by
  ext U
  simp only [locMartBad, stoppedWindowRec, Set.mem_ofPred_eq, Set.mem_iUnion]

/-- `(locmart)` holds at every walker on the good event, with `<=` rather than `<`. -/
theorem locMartGood_spec {p : ℝ} {m r T L : ℕ} {U : Array N}
    (hU : U ∈ locMartGood p m r T L) :
    ∀ (i : Fin N) (s k : ℕ), s ≤ T * L → k ≤ T * L - s →
      |driftMartingale p m U (recTimeA p m U r + s + k) i
        - driftMartingale p m U (recTimeA p m U r + s) i| ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := by
  intro i s k hs hk
  by_contra hcon
  push Not at hcon
  exact hU ⟨i, s, hs, k, hk, le_of_lt hcon⟩

/-- **Unconditional union bound for `(locmart)` over all walkers at the record clock.** -/
theorem measureReal_locMartBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (r T L : ℕ) (hTL : 1 ≤ T * L) :
    (arrayMeasure N).real (locMartBad p m r T L) ≤
      (N : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ)))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hεpos : 0 < (L : ℝ) ^ ((3 : ℝ) / 4) := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · rw [hL, Nat.mul_zero] at hTL
      omega
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hL) _
  rw [locMartBad_eq_iUnion]
  have hunion : (⋃ i : Fin N, stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i)
      = ⋃ i ∈ (Finset.univ : Finset (Fin N)),
          stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i := by
    ext U
    simp
  rw [hunion]
  refine le_trans (measureReal_biUnion_finset_le (Finset.univ)
    (fun i : Fin N => stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i)) ?_
  have hterm : ∀ i : Fin N,
      (arrayMeasure N).real (stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i)
        ≤ 2 * (((T * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) :=
    fun i => measureReal_stoppedWindowRec hp0 hp1 hm hN r i hTL hεpos
  calc ∑ i : Fin N,
        (arrayMeasure N).real (stoppedWindowRec p m r (T * L) ((L : ℝ) ^ ((3 : ℝ) / 4)) i)
      ≤ ∑ _i : Fin N, 2 * (((T * L : ℕ) : ℝ) + 1) ^ 2 *
            Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (N : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-! ## 4. The paper's `xOf` profile -/

/-- The paper's scale `xOf L = L^(1/16)`. -/
noncomputable def xOf (L : ℕ) : ℝ := (L : ℝ) ^ ((1 : ℝ) / 16)

theorem xOf_nonneg (L : ℕ) : 0 ≤ xOf L := Real.rpow_nonneg (Nat.cast_nonneg L) _

theorem one_le_xOf {L : ℕ} (hL : 1 ≤ L) : 1 ≤ xOf L :=
  Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)

/-- `b * u ^ d <= exp (kappa * u)` once `u` exceeds an explicit threshold. -/
theorem pow_mul_le_exp (b κ : ℝ) (hκ : 0 < κ) (d : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : b * (((d + 1).factorial : ℕ) : ℝ) / κ ^ (d + 1) ≤ u) :
    b * u ^ d ≤ Real.exp (κ * u) := by
  have hκpos : (0 : ℝ) < κ ^ (d + 1) := by positivity
  have hfact : (0 : ℝ) < (((d + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (d + 1)
  have hx : (0 : ℝ) ≤ κ * u := mul_nonneg hκ.le hu0
  have hsum := Real.sum_le_exp_of_nonneg hx (d + 2)
  have hmem : (d + 1) ∈ Finset.range (d + 2) := Finset.mem_range.mpr (by omega)
  have hnn : ∀ i ∈ Finset.range (d + 2), (0 : ℝ) ≤ (κ * u) ^ i / ((i.factorial : ℕ) : ℝ) := by
    intro i _
    positivity
  have hterm : (κ * u) ^ (d + 1) / (((d + 1).factorial : ℕ) : ℝ) ≤ Real.exp (κ * u) :=
    le_trans (Finset.single_le_sum hnn hmem) hsum
  have h1 : b * (((d + 1).factorial : ℕ) : ℝ) ≤ u * κ ^ (d + 1) := by
    rw [div_le_iff₀ hκpos] at hu
    linarith [hu]
  have h2 : b * u ^ d * (((d + 1).factorial : ℕ) : ℝ) ≤ (κ * u) ^ (d + 1) := by
    have h3 : b * u ^ d * (((d + 1).factorial : ℕ) : ℝ)
        ≤ (u * κ ^ (d + 1)) * u ^ d := by
      have hm := mul_le_mul_of_nonneg_right h1 (pow_nonneg hu0 d)
      linarith [hm]
    have h4 : (u * κ ^ (d + 1)) * u ^ d = (κ * u) ^ (d + 1) := by
      rw [pow_succ]
      ring
    linarith [h3, h4]
  calc b * u ^ d = b * u ^ d * (((d + 1).factorial : ℕ) : ℝ)
        / (((d + 1).factorial : ℕ) : ℝ) := by field_simp
    _ ≤ (κ * u) ^ (d + 1) / (((d + 1).factorial : ℕ) : ℝ) := by
        rw [div_le_div_iff_of_pos_right hfact]
        exact h2
    _ ≤ Real.exp (κ * u) := hterm

/-- **The `(locmart)` component of the paper's good event in the paper's profile.**
There are `c_T > 0` and `L_0` such that for every `L >= L_0` and every record level `r`,
the probability that some walker's drift martingale deviates by `L^{3/4}` inside the record
window `[tau_r, tau_r + T*L]` is at most `exp (-c_T L^{1/16})`.  No hypothesis on `d_r` is used,
so this needs no carrier at all. -/
theorem exists_locMartBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ,
      (arrayMeasure N).real (locMartBad p m r T L) ≤ Real.exp (-c * xOf L) := by
  classical
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  set κ : ℝ := 1 / (32 * (T : ℝ)) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  set u₀ : ℝ := (2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2) * ((((4 + 1).factorial : ℕ) : ℝ))
    / κ ^ (4 + 1) with hu₀def
  have hu₀0 : 0 ≤ u₀ := by rw [hu₀def]; positivity
  refine ⟨κ, hκpos, max 2 (Nat.ceil (u₀ ^ 2) + 1), ?_⟩
  intro L hL r
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := by omega
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLr1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  set v : ℝ := (L : ℝ) ^ ((1 : ℝ) / 2) with hvdef
  have hv0 : 0 ≤ v := Real.rpow_nonneg hLr.le _
  have hv1 : 1 ≤ v := Real.one_le_rpow hLr1 (by norm_num)
  have hvne : v ≠ 0 := by linarith
  have hv2 : v ^ 2 = (L : ℝ) := by
    rw [hvdef]
    rw [show (2 : ℕ) = 2 from rfl, ← Real.rpow_natCast ((L : ℝ) ^ ((1 : ℝ) / 2)) 2]
    rw [← Real.rpow_mul hLr.le]
    norm_num
  have hv2ge1 : (1 : ℝ) ≤ v ^ 2 := by rw [hv2]; exact hLr1
  -- the ceiling condition gives `u₀ <= v`
  have hceil : u₀ ^ 2 ≤ (L : ℝ) := by
    have h1 : u₀ ^ 2 ≤ (Nat.ceil (u₀ ^ 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (u₀ ^ 2) : ℝ) ≤ (L : ℝ) := by
      have h3 : Nat.ceil (u₀ ^ 2) + 1 ≤ L :=
        le_trans (le_max_right _ _) hL
      have h4 : Nat.ceil (u₀ ^ 2) ≤ L := by omega
      exact_mod_cast h4
    linarith
  have hu₀v : u₀ ≤ v := by nlinarith [hceil, hv2, hv0, hu₀0]
  -- elementary rpow identities
  have h34 : ((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((L : ℝ) ^ ((3 : ℝ) / 4)) 2]
    rw [← Real.rpow_mul hLr.le]
    norm_num
  have h32' : (L : ℝ) ^ ((3 : ℝ) / 2) = v ^ (3 : ℝ) := by
    rw [show ((3 : ℝ) / 2) = (1 / 2) * (3 : ℝ) from by norm_num]
    rw [Real.rpow_mul hLr.le]
  have h32 : (L : ℝ) ^ ((3 : ℝ) / 2) = v ^ 3 :=
    h32'.trans (Real.rpow_natCast v 3)
  have hTLcast : (((T * L : ℕ)) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  have hexpEq : -(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ))
      = -(v) / (16 * (T : ℝ)) := by
    rw [h34, h32, hTLcast, ← hv2]
    field_simp
  have hTL1 : 1 ≤ T * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the exact bound
  have hmain := measureReal_locMartBad_le (N := N) hp0 hp1 hm hN r T L hTL1
  have hTLle : (((T * L : ℕ)) : ℝ) + 1 ≤ ((T : ℝ) + 1) * v ^ 2 := by
    rw [hTLcast, hv2]
    nlinarith [hv2ge1, hTpos]
  have hTLle0 : (0 : ℝ) ≤ (((T * L : ℕ)) : ℝ) + 1 := by positivity
  have hTLle0' : (0 : ℝ) ≤ ((T : ℝ) + 1) * v ^ 2 := by
    have : (0 : ℝ) ≤ ((T : ℝ) + 1) := by linarith
    positivity
  -- absorb the polynomial factor
  have habs : 2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2 * v ^ 4 ≤ Real.exp (κ * v) := by
    have h := pow_mul_le_exp (2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2) κ hκpos 4 hv0
      (by rw [hu₀def] at hu₀v; exact hu₀v)
    have h4 : ((2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2) * v ^ 4) = _ := rfl
    calc 2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2 * v ^ 4
        = (2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2) * v ^ 4 := by ring
      _ ≤ Real.exp (κ * v) := h
  have hexpκ : Real.exp (κ * v) * Real.exp (-(v) / (16 * (T : ℝ))) = Real.exp (-(κ * v)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hκdef]
    field_simp
    ring
  have hvl : xOf L ≤ v := by
    rw [xOf, hvdef]
    exact Real.rpow_le_rpow_of_exponent_le hLr1 (by norm_num)
  have hfinal : Real.exp (-(κ * v)) ≤ Real.exp (-κ * xOf L) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hκpos, hvl]
  calc (arrayMeasure N).real (locMartBad p m r T L)
      ≤ (N : ℝ) * (2 * (((T * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(((L : ℝ) ^ ((3 : ℝ) / 4)) ^ 2) / (16 * ((T * L : ℕ) : ℝ)))) := hmain
    _ = 2 * (N : ℝ) * ((((T * L : ℕ) : ℝ) + 1) ^ 2 *
          Real.exp (-(v) / (16 * (T : ℝ)))) := by rw [hexpEq]; ring
    _ ≤ 2 * (N : ℝ) * ((((T : ℝ) + 1) * v ^ 2) ^ 2 *
          Real.exp (-(v) / (16 * (T : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsq : ((((T * L : ℕ) : ℝ) + 1)) ^ 2 ≤ (((T : ℝ) + 1) * v ^ 2) ^ 2 :=
          pow_le_pow_left₀ hTLle0 hTLle 2
        exact mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 2 * (N : ℝ) * ((T : ℝ) + 1) ^ 2 * v ^ 4 *
          Real.exp (-(v) / (16 * (T : ℝ))) := by ring
    _ ≤ Real.exp (κ * v) * Real.exp (-(v) / (16 * (T : ℝ))) := by
        refine mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = Real.exp (-(κ * v)) := hexpκ
    _ ≤ Real.exp (-κ * xOf L) := hfinal
    _ = Real.exp (-κ * xOf L) := rfl

end RecordClock
