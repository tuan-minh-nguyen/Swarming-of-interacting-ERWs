import Swarm.M1Coalesce
import Swarm.SharpGroup

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace Swarming.Diameter

open FluidInterpolation FluidLimit FluidMerge FluidJoin Glue JoinStep LocalFluid RecordDefect
open M2Meet

set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
variable {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
variable {level scale eta : ℕ → ℕ} {C μ : ℝ} {CT : ℕ → ℝ} {T : ℕ}
variable {x : ι → Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ}

private theorem fluidMotionOn_of_martingale_error
    (hscale : ∀ n, 0 < scale n)
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ (CT n) T (scale n) (level n))
    (hη : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (hratio : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ (i : ι) (t : ℝ), 0 ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (lift x i t)))
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    FluidMotionOn (lift x) 0 (T : ℝ) := by
  refine fluidMotionOn_of_tendsto_lower (x := lift x)
    (y := fun n i t => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
      ⌊(scale n : ℝ) * t⌋₊) ?_ hconv hratio ?_
  · intro i s t hs hst ht
    have hsI : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs, hst.trans ht⟩
    have htI : t ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.trans hst, ht⟩
    rw [lift_apply hsI, lift_apply htI]
    exact upper_speed_of_lipschitz_on_Icc (hlip i) hsI htI hst
  · intro n i s t hs hst ht
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    let a := ⌊(scale n : ℝ) * s⌋₊
    let b := ⌊(scale n : ℝ) * t⌋₊
    have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_left hst hL.le)
    have hb : b ≤ T * scale n := by
      change ⌊(scale n : ℝ) * t⌋₊ ≤ T * scale n
      rw [← Nat.floor_natCast (R := ℝ) (T * scale n)]
      apply Nat.floor_mono
      push_cast
      exact (mul_le_mul_of_nonneg_left ht hL.le).trans_eq (mul_comm _ _)
    have hd := (hM n).down (i := i) (s := τ n (level n) + a) (t := τ n (level n) + b)
      (Nat.le_add_right _ _) (Nat.add_le_add_left hab _) (Nat.add_le_add_left hb _)
    have hd' := (div_le_div_iff_of_pos_right hL).mpr (hd.trans (hη n))
    have he := M1C.scaledPosition_sub (X := X n) (level := level n) (start := τ n (level n)) hL.ne' i a b
    have hprod := congrArg (fun z : ℝ => z / (scale n : ℝ)) he
    change _ ≤ scaledPosition (X n) (level n) (τ n (level n)) (scale n) i b -
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i a
    rw [mul_div_cancel_left₀ _ hL.ne'] at hprod
    linarith only [hd', hprod]

private theorem meetBound_of_local_errors
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C (CT n) T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ (CT n) T (scale n) (level n))
    (hC : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C (CT n) (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hη : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (hratio : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hlag : ∀ n i k, 64 * Nat.ceil C * scale n ≤ k → k ≤ T * scale n →
      runMaxI (X n) i (τ n (level n) + k) - X n i (τ n (level n) + k) ≤ (eta n : ℤ))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    MeetBound (lift x) (64 * Nat.ceil C : ℝ) (2 * C ^ 2) (T : ℝ) := by
  classical
  intro D hD s t hs₀ hst htT _ hD' hsep
  rcases hst.eq_or_lt with rfl | hst
  · simp only [sub_self]
    exact mul_nonneg (by positivity) (fluidGap_nonneg _)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hs₀pos : (0 : ℝ) < 64 * (Nat.ceil C : ℝ) := by
    have : (0 : ℝ) < (Nat.ceil C : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hCpos
    positivity
  have hs : 0 < s := hs₀pos.trans_le hs₀
  have hsI : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.le, hst.le.trans htT⟩
  have hJ : (Finset.univ \ D).Nonempty := by
    refine Finset.sdiff_nonempty.mpr (fun h => hD' ?_)
    exact Finset.eq_univ_iff_forall.mpr (fun i => h (Finset.mem_univ i))
  have hcont : ∀ i, ContinuousOn (lift x i) (Icc (64 * Nat.ceil C : ℝ) (T : ℝ)) :=
    fun i => (continuousOn_lift x i).mono (fun _ hu => ⟨hs₀pos.le.trans hu.1, hu.2⟩)
  obtain ⟨γ, hγ, hmargin⟩ := exists_sep_margin hcont hD hJ hs₀ hst.le htT hsep
  have hgrid : ∀ᶠ n in atTop, ∀ k : ℕ, s ≤ (k : ℝ) / (scale n : ℝ) →
      (k : ℝ) / (scale n : ℝ) ≤ t → Sep (X n) D (Finset.univ \ D) (τ n (level n) + k) := by
    refine M2B.sep_eventually_of_fluid hscale hscaleTop hτ hne hdr hr hconv hratio hD hJ
      hs hst.le htT hγ (fun u hu huv => ?_) ?_
    · simpa only [fpos_eq_lift hu] using hmargin u huv
    · filter_upwards with n i k hk hkt
      have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
      apply hlag n i k
      · exact_mod_cast (show (64 * (Nat.ceil C : ℝ)) * (scale n : ℝ) ≤ (k : ℝ) from
          (mul_le_mul_of_nonneg_right hs₀ hL.le).trans ((le_div_iff₀ hL).mp hk))
      · exact_mod_cast ((div_le_iff₀ hL).mp (hkt.trans htT))
  let a (n : ℕ) := ⌈(scale n : ℝ) * s⌉₊
  let b (n : ℕ) := ⌊(scale n : ℝ) * t⌋₊
  have ha := tendsto_ceil_mul_div hscale hscaleTop hs.le
  have hb := tendsto_floor_mul_div hscale hscaleTop (hs.le.trans hst.le)
  have hapos := ceil_le_horizon hscale hscaleTop hs.le (hst.trans_le htT)
  have hab : ∀ᶠ n in atTop, a n < b n := by
    filter_upwards [(tendsto_order.mp ha).2 ((s + t) / 2) (by linarith),
      (tendsto_order.mp hb).1 ((s + t) / 2) (by linarith)] with n h1 h2
    have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have h : (a n : ℝ) / (scale n : ℝ) < (b n : ℝ) / (scale n : ℝ) := h1.trans h2
    exact_mod_cast (div_lt_div_iff_of_pos_right hL).mp h
  have hη₂ : Tendsto (fun n => (((2 * eta n : ℕ) : ℝ) / (scale n : ℝ))) atTop (𝓝 0) := by
    convert hratio.const_mul (2 : ℝ) using 1
    · ext n
      push_cast
      ring
    · simp
  have hmeet := meet_of_grid_bounds' (C := C) (CT := 0) (eta := fun n => 2 * eta n)
    hscale hscaleTop hconv hlip hsI hst htT hD hJ ha hapos (by
      filter_upwards [hgrid, hab] with n hSep hlt
      have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
      have hlo : s * (scale n : ℝ) ≤ (a n : ℝ) := mul_self_le_ceil
      have hhi : (b n : ℝ) ≤ t * (scale n : ℝ) := by
        rw [mul_comm]
        exact Nat.floor_le (mul_nonneg hL.le (hs.le.trans hst.le))
      have hs' : 64 * Nat.ceil C * scale n ≤ a n := by
        exact_mod_cast ((mul_le_mul_of_nonneg_right hs₀ hL.le).trans hlo)
      have ht' : b n ≤ T * scale n := by
        exact_mod_cast (hhi.trans (mul_le_mul_of_nonneg_right htT hL.le))
      have hSep' (k : ℕ) (hk : a n ≤ k) (hkb : k ≤ b n) :
          Sep (X n) D (Finset.univ \ D) (τ n (level n) + k) :=
        hSep k ((le_div_iff₀ hL).mpr (hlo.trans (by exact_mod_cast hk)))
          ((div_le_iff₀ hL).mpr ((by exact_mod_cast hkb : (k : ℝ) ≤ b n).trans hhi))
      have hSep'' (u : ℕ) (hu : τ n (level n) + a n ≤ u) (hv : u < τ n (level n) + b n) :
          Sep (X n) D (Finset.univ \ D) u := by
        have h := hSep' (u - τ n (level n)) (by omega) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at h
      have hRun := run_le_sharp (hτ n) (hne n) (hcl n) (hM n) hCpos (hCT n) (hdr n) (hr n)
        (hscale n) hij (hnum n) hT64 (hη n) hD hD' (Nat.add_le_add_left hs' _)
        (Nat.add_lt_add_left hlt _) (Nat.add_le_add_left ht' _) hSep'' (hSep' _ hlt.le le_rfl)
      have hGap := spread_add_gap_le_gapStar (X := X n) hD hJ rfl
        (n := τ n (level n) + a n)
      have hGap' := mul_le_mul_of_nonneg_left (add_le_add hGap (le_refl (eta n : ℝ)))
        (show 0 ≤ 2 * C ^ 2 by positivity)
      have hErr := mul_le_mul_of_nonneg_left (hη n) (show 0 ≤ 2 * C by positivity)
      have hErr' : 2 * C * (eta n : ℝ) ≤ 2 * C ^ 2 * (eta n : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hC hCpos.le])
          (Nat.cast_nonneg _)
      rw [Nat.add_sub_add_left] at hRun
      push_cast
      linarith only [hRun, hGap', hErr, hErr']) hη₂
  have hmain : t - s ≤ 2 * C ^ 2 * (D.sup' hD (fun i => lift x i s)
      - (Finset.univ \ D).sup' hJ (fun i => lift x i s)) := by
    simpa only [fpos_eq_lift hsI] using hmeet
  have hmax : D.sup' hD (fun i => lift x i s) ≤ fluidMax (fun i => lift x i s) :=
    Finset.sup'_le hD _ (fun i _ => Finset.le_sup' (fun j => lift x j s) (Finset.mem_univ i))
  obtain ⟨j, hj⟩ := hJ
  have hmin : fluidMin (fun i => lift x i s) ≤ (Finset.univ \ D).sup' ⟨j, hj⟩ (fun i => lift x i s) :=
    (Finset.inf'_le (fun i => lift x i s) (Finset.mem_univ j)).trans
      (Finset.le_sup' (fun i => lift x i s) hj)
  exact hmain.trans (mul_le_mul_of_nonneg_left (sub_le_sub hmax hmin) (by positivity))

/-- The fluid trajectories all agree at times at least \(B\) when the local error
divided by the spatial scale tends to zero. The coefficient of \(L^{3/4}\) may
vary with the scale. -/
theorem coalesced_at_of_local_errors {B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hBC : ∀ n, BlkCoin.BlockClauses (X n) (τ n) (H n) C (CT n) T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ (CT n) T (scale n) (level n))
    (hC : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C (CT n) (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hη : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (hratio : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hB : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2)
    {θ : Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) : x i θ = x j θ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlip : ∀ i, LipschitzWith 1 (x i) :=
    fun i => lipschitz_of_uniform_recordFamily hscale hne (T := (T : ℝ)) (x := x) (φ := id) hconvR i
  have hconvU : ∀ i, TendstoUniformly (fun n (t : Icc (0 : ℝ) (T : ℝ)) =>
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) t)) (fun t => x i t) atTop :=
    fun i => M1C.tendstoUniformly_rawSample hscale hscaleTop hne i (hconvR i)
  have hconvK := M1C.knot_tendsto hscale hscaleTop hne hconvR
  have hs₀ : (0 : ℝ) ≤ 64 * (Nat.ceil C : ℝ) := by positivity
  have hlag (n : ℕ) (i : ι) (s : ℕ) (hs : τ n (level n) + 64 * Nat.ceil C * scale n ≤ s)
      (ht : s ≤ τ n (level n) + T * scale n) :
      runMaxI (X n) i s - X n i s ≤ (eta n : ℤ) :=
    lag_le_sub (X n) (hτ n) (hM n) hCpos (hBC n).base.occ (hdr n) (hscale n) hij (hnum n) hT64
      (hη n) hs ht i
  have hη' (n : ℕ) : (eta n : ℝ) ≤ ((eta n : ℝ) / (scale n : ℝ)) * scale n := by
    rw [div_mul_cancel₀ _ (by exact_mod_cast (hscale n).ne')]
  have hsticky : StickyOn (lift x) (64 * Nat.ceil C : ℝ) (T : ℝ) :=
    M4Sharp.stickyOn_of_grid_sharp hscale hscaleTop
      (fun n => (hBC n).base.toField (hτ n) (hM n) (hdr n) (hη n))
      (fun n => M4Sharp.groupGrow_of_blockClauses (hBC n)) hlag hC hCT hτ hne hdr hr
      hratio hratio hη' (fun n => (hη n).trans (hη' n)) hs₀ le_rfl
      (fun i t hs ht => hconvK i t (hs₀.trans hs) ht)
  have hmeet := meetBound_of_local_errors hscale hscaleTop hτ hne (fun n => (hBC n).base)
    hM hC hCT hdr hr hij hnum hT64 hη hratio
    (fun n i k hk ht => hlag n i _ (Nat.add_le_add_left hk _) (Nat.add_le_add_left ht _)) hconvU hlip
  have hcont : ∀ i, ContinuousOn (lift x i) (Icc (64 * Nat.ceil C : ℝ) (T : ℝ)) :=
    fun i => (continuousOn_lift x i).mono (fun _ hu => ⟨hs₀.trans hu.1, hu.2⟩)
  have hjoin := joinRuleFrom_of_meetBound hsticky hcont hmeet (by positivity)
  have hmove := fluidMotionOn_of_martingale_error hscale hM hη hratio hconvK hlip
  have hconv0 : ∀ i, Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0)
      atTop (𝓝 (lift x i 0)) := fun i => by simpa using hconvK i 0 le_rfl (Nat.cast_nonneg T)
  have hgap := M1C.fluidGap_lift_zero_le_one hτ hscale hdr hconv0
  have hT64' : (64 * Nat.ceil C : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT64
  have hgap₀ := fluidGap_le_one_add hmove hs₀ hT64' hgap
  have hBT : (B : ℝ) - 2 < (T : ℝ) := by linarith only [hBθ, θ.2.2]
  obtain ⟨u, _, hu, _, hcoal⟩ := exists_persistent_coalescence (lift x)
    (64 * Nat.ceil C : ℝ) (2 * C ^ 2) (1 + 64 * Nat.ceil C : ℝ) (T : ℝ)
    (fun i s t hs hst ht => hmove i s t (hs₀.trans hs) hst ht)
    hjoin hsticky (by positivity) (by positivity) (hB.trans hBT) (by linarith only [hs₀]) hgap₀
  have he := hcoal (θ : ℝ) (by linarith only [hu, hB, hBθ]) θ.2.2 i j
  rwa [lift_apply θ.2, lift_apply θ.2] at he

end Swarming.Diameter
