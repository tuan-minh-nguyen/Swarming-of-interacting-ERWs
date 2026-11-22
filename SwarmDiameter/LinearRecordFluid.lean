import SwarmDiameter.LinearBlockGeometry
import SwarmDiameter.FluidLeaderPersistence
import Swarm.M1Coalesce

open Filter Set Finset
open FluidInterpolation FluidLimit FluidMerge FluidJoin Glue LocalFluid RecordDefect M2Meet
open scoped Topology BoundedContinuousFunction

namespace Swarming.Diameter

set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
variable {level scale : ℕ → ℕ} {ε : ℕ → ℝ} {C v : ℝ} {T : ℕ}
variable {x : ι → Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ}

private theorem motion_of_linear_errors (hscale : ∀ n, 0 < scale n)
    (hcl : ∀ n, LinearBlockClauses (X n) (τ n) (level n) T (scale n) C v (ε n * (scale n : ℝ)))
    (hε : Tendsto ε atTop (𝓝 0))
    (hconv : ∀ i (t : ℝ), 0 ≤ t → t ≤ (T : ℝ) →
      Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        ⌊(scale n : ℝ) * t⌋₊) atTop (𝓝 (lift x i t)))
    (hlip : ∀ i, LipschitzWith 1 (x i)) : FluidMotionOn (lift x) 0 (T : ℝ) := by
  refine fluidMotionOn_of_tendsto_lower (x := lift x)
    (y := fun n i t => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
      ⌊(scale n : ℝ) * t⌋₊) ?_ hconv hε ?_
  · intro i s t hs hst ht
    have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs, hst.trans ht⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs.trans hst, ht⟩
    rw [lift_apply hsI, lift_apply htI]
    exact upper_speed_of_lipschitz_on_Icc (hlip i) hsI htI hst
  · intro n i s t hs hst ht
    have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
    let a := ⌊(scale n : ℝ) * s⌋₊
    let b := ⌊(scale n : ℝ) * t⌋₊
    have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_left hst hL.le)
    have hb : b ≤ T * scale n := by
      have h := floor_le_horizon hscale (hs.trans hst) ht n
      simpa only [rawHorizon, ← Nat.cast_mul, Nat.floor_natCast] using h
    have hd := (hcl n).down i (τ n (level n) + a) (τ n (level n) + b)
      (Nat.le_add_right _ _) (Nat.add_le_add_left hab _) (Nat.add_le_add_left hb _)
    change -(ε n) ≤ scaledPosition (X n) (level n) (τ n (level n)) (scale n) i b -
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i a
    unfold scaledPosition
    rw [← sub_div, le_div_iff₀ hL]
    linarith only [hd]

private theorem lag_of_linear_errors
    (hscale : ∀ n, 0 < scale n) (hτ : ∀ n, IsRecord (X n) (τ n))
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hv : 0 < v) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hcl : ∀ n, LinearBlockClauses (X n) (τ n) (level n) T (scale n) C v (ε n * (scale n : ℝ)))
    (n : ℕ) (i : ι) (k : ℕ) (hk : 2 / v ≤ (k : ℝ) / (scale n : ℝ)) (hkt : k ≤ T * scale n) :
    (runMaxI (X n) i (τ n (level n) + k) : ℝ) - X n i (τ n (level n) + k) ≤ ε n * (scale n : ℝ) := by
  have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
  have hstart : (level n : ℝ) - (scale n : ℝ) ≤ (runMin (X n) (τ n (level n)) : ℝ) := by
    have hd := hdr n
    unfold defect at hd
    have hd' : (level n : ℝ) - (runMin (X n) (τ n (level n)) : ℝ) ≤ (scale n : ℝ) := by
      exact_mod_cast hd
    linarith only [hd']
  have h₁ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL).mp hk) hv.le
  rw [← mul_assoc, mul_div_cancel₀ _ hv.ne'] at h₁
  have h₂ := (hcl n).minimum (τ n (level n)) (τ n (level n) + k)
    le_rfl (Nat.le_add_right _ _) (Nat.add_le_add_left hkt _)
  push_cast at h₂
  apply (hcl n).lag (hτ n) (Nat.le_add_right _ _) (Nat.add_le_add_left hkt _) _ (mul_nonneg (hε₀ n) hL.le) i
  exact_mod_cast (show (level n : ℝ) ≤ (runMin (X n) (τ n (level n) + k) : ℝ) from by
    nlinarith only [hstart, h₁, h₂, mul_le_mul_of_nonneg_right (hε₁ n) hL.le])

omit [Nonempty ι] in
private theorem inf_scaled_eq {Y : ι → ℕ → ℤ} {r σ L k : ℕ} (hL : 0 < L)
    {J : Finset ι} (hJ : J.Nonempty) :
    J.inf' hJ (fun i => scaledPosition Y r σ L i k) =
      ((Glue.sMin Y J (σ + k) : ℝ) - r) / L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Glue.sMin, dif_pos hJ]
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hJ (fun i => Y i (σ + k))
  rw [he]
  refine le_antisymm (Finset.inf'_le _ hj) (Finset.le_inf' _ _ ?_)
  intro i hi
  unfold scaledPosition
  have h : Y j (σ + k) ≤ Y i (σ + k) := he ▸ Finset.inf'_le _ hi
  exact div_le_div_of_nonneg_right (sub_le_sub_right (by exact_mod_cast h) _) hL'.le

private theorem linear_bounds_of_grid
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hcl : ∀ n, LinearBlockClauses (X n) (τ n) (level n) T (scale n) C v (ε n * (scale n : ℝ)))
    (hC : 1 ≤ C) (hv : 0 < v) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) t)) (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {J : Finset ι} (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    {s t : ℝ} (hs : 2 / v ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hsep : ∀ u ∈ Set.Icc s t, ∀ i ∈ Jᶜ, ∀ j ∈ J, lift x j u < lift x i u) :
    (∀ i ∈ Jᶜ, lift x i t - J.inf' hJ (fun j => lift x j t) ≤
      C * (lift x i s - J.inf' hJ (fun j => lift x j s))) ∧
    t - s ≤ C * fluidGap (fun i => lift x i s) := by
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  rcases hst.eq_or_lt with rfl | hst
  · refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hJ (fun j => lift x j s)
      rw [he]
      have hp := hsep s ⟨le_rfl, le_rfl⟩ i hi j hj
      exact le_mul_of_one_le_left (sub_nonneg.mpr hp.le) hC
    · simpa only [sub_self] using mul_nonneg hC₀ (fluidGap_nonneg (fun i => lift x i s))
  have hs₀ : 0 < s := (div_pos (by norm_num) hv).trans_le hs
  have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs₀.le, hst.le.trans ht⟩
  have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs₀.le.trans hst.le, ht⟩
  let η (n : ℕ) := ⌈ε n * (scale n : ℝ)⌉₊
  have hη : Tendsto (fun n => (η n : ℝ) / (scale n : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (scale n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hscaleTop)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using hε.add hinv)
    have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
    rw [div_le_iff₀ hL, add_mul, inv_mul_cancel₀ hL.ne']
    exact (Nat.ceil_lt_add_one (mul_nonneg (hε₀ n) hL.le)).le
  have hJ' : (Finset.univ \ Jᶜ).Nonempty := by
    simpa only [← Finset.compl_eq_univ_sdiff, compl_compl] using hJ
  obtain ⟨γ, hγ, hmarg⟩ := exists_sep_margin (fun i => continuousOn_lift x i) hJc hJ hsI.1 hst.le ht hsep
  have hgrid : ∀ᶠ n in atTop, ∀ k : ℕ, s ≤ (k : ℝ) / (scale n : ℝ) →
      (k : ℝ) / (scale n : ℝ) ≤ t → Sep (X n) Jᶜ J (τ n (level n) + k) := by
    have h := M2B.sep_eventually_of_fluid hscale hscaleTop hτ hne hdr hr hconv hη hJc hJ'
      hs₀ hst.le ht hγ (fun u hu huv => by
        simpa only [← Finset.compl_eq_univ_sdiff, compl_compl, fpos_eq_lift hu] using hmarg u huv) (by
        filter_upwards with n i k hk hkt
        have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
        have hkt' : k ≤ T * scale n := by exact_mod_cast (div_le_iff₀ hL).mp (hkt.trans ht)
        have h := lag_of_linear_errors hscale hτ hdr hv hε₀ hε₁ hcl n i k (hs.trans hk) hkt'
        exact_mod_cast h.trans (Nat.le_ceil _))
    simpa only [← Finset.compl_eq_univ_sdiff, compl_compl] using h
  let a (n : ℕ) := ⌈(scale n : ℝ) * s⌉₊
  let b (n : ℕ) := ⌊(scale n : ℝ) * t⌋₊
  let σ (n : ℕ) := τ n (level n)
  let Y (n : ℕ) (i : ι) (k : ℕ) := scaledPosition (X n) (level n) (σ n) (scale n) i k
  have ha := tendsto_ceil_mul_div hscale hscaleTop hsI.1
  have hb := tendsto_floor_mul_div hscale hscaleTop htI.1
  have haT : ∀ᶠ n in atTop, a n ≤ T * scale n := by
    exact (ceil_le_horizon hscale hscaleTop hsI.1 (hst.trans_le ht)).mono (fun n hn => by
      exact_mod_cast hn)
  have hbT (n : ℕ) : b n ≤ T * scale n := by
    simpa only [rawHorizon, ← Nat.cast_mul, Nat.floor_natCast] using floor_le_horizon hscale htI.1 ht n
  have hab : ∀ᶠ n in atTop, a n ≤ b n := eventually_ceil_le_floor hscale hscaleTop hs₀ hst
  have hgrid' : ∀ᶠ n in atTop, a n ≤ b n ∧ ∀ u ∈ Finset.Icc (σ n + a n) (σ n + b n),
      Sep (X n) Jᶜ J u := by
    filter_upwards [hab, hgrid] with n habn hsep'n
    refine ⟨habn, fun u hu => ?_⟩
    obtain ⟨hu₁, hu₂⟩ := Finset.mem_Icc.mp hu
    have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
    let k := u - σ n
    have hk₁ : (a n : ℝ) ≤ k := by exact_mod_cast (show a n ≤ k by dsimp [k]; omega)
    have hk₂ : (k : ℝ) ≤ b n := by exact_mod_cast (show k ≤ b n by dsimp [k]; omega)
    have ha' : s ≤ (a n : ℝ) / (scale n : ℝ) := by
      apply (le_div_iff₀ hL).mpr
      rw [mul_comm]
      exact Nat.le_ceil _
    have hb' : (b n : ℝ) / (scale n : ℝ) ≤ t := by
      apply (div_le_iff₀ hL).mpr
      rw [mul_comm]
      exact Nat.floor_le (mul_nonneg hL.le htI.1)
    have h := hsep'n k (ha'.trans (div_le_div_of_nonneg_right hk₁ hL.le))
      ((div_le_div_of_nonneg_right hk₂ hL.le).trans hb')
    rwa [show σ n + k = u by dsimp [k]; omega] at h
  have hYa (i : ι) : Tendsto (fun n => Y n i (a n)) atTop (𝓝 (lift x i s)) := by
    rw [lift_apply hsI]
    exact M2B.scaledPosition_tendsto_of_ratio hscale hconv hlip hsI
      (haT.mono fun n h => by exact_mod_cast h) ha i
  have hYb (i : ι) : Tendsto (fun n => Y n i (b n)) atTop (𝓝 (lift x i t)) := by
    rw [lift_apply htI]
    exact M2B.scaledPosition_tendsto_of_ratio hscale hconv hlip htI
      (Eventually.of_forall (fun n => by exact_mod_cast hbT n)) hb i
  constructor
  · intro i hi
    have hlim₁ := (hYb i).sub (M2B.tendsto_inf'_finset_of hJ (fun j _ => hYb j))
    have hlim₂ := (hYa i).sub (M2B.tendsto_inf'_finset_of hJ (fun j _ => hYa j))
    have hlim₃ := (hlim₂.const_mul C).add hε
    rw [add_zero] at hlim₃
    apply le_of_tendsto_of_tendsto hlim₁ hlim₃
    filter_upwards [hgrid'] with n hn
    have h := (hcl n).compare J i hi (σ n + a n) (σ n + b n) (Nat.le_add_right _ _)
      (Nat.add_le_add_left hn.1 _) (Nat.add_le_add_left (hbT n) _) hn.2
    have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
    change Y n i (b n) - J.inf' hJ (fun j => Y n j (b n)) ≤
      C * (Y n i (a n) - J.inf' hJ (fun j => Y n j (a n))) + ε n
    unfold Y
    rw [inf_scaled_eq (hscale n) hJ, inf_scaled_eq (hscale n) hJ]
    simp only [scaledPosition, ← sub_div, sub_sub_sub_cancel_right, ← mul_div_assoc]
    have hh := (div_le_div_iff_of_pos_right hL).mpr h
    rwa [add_div, mul_div_cancel_right₀ _ hL.ne'] at hh
  · have hlim := (M2B.tendsto_sup'_finset_of Finset.univ_nonempty (fun i _ => hYa i)).sub
      (M2B.tendsto_inf'_finset_of Finset.univ_nonempty (fun i _ => hYa i))
    have hlim' := (hlim.const_mul C).add (hε.const_mul (C + 1))
    rw [mul_zero, add_zero] at hlim'
    apply le_of_tendsto_of_tendsto (hb.sub ha) hlim'
    filter_upwards [hgrid'] with n hn
    have h := (hcl n).meet J (σ n + a n) (σ n + b n) (Nat.le_add_right _ _)
      (Nat.add_le_add_left hn.1 _) (Nat.add_le_add_left (hbT n) _) hn.2
    have hL : (0 : ℝ) < scale n := by exact_mod_cast hscale n
    have hlag : (Glue.sMaxM (X n) Finset.univ (σ n + a n) : ℝ) ≤
        (runMax (X n) (σ n + a n) : ℝ) + ε n * (scale n : ℝ) := by
      obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
        (fun i => runMaxI (X n) i (σ n + a n))
      rw [Glue.sMaxM, dif_pos Finset.univ_nonempty, he]
      have ha' : s ≤ (a n : ℝ) / (scale n : ℝ) := by
        apply (le_div_iff₀ hL).mpr
        rw [mul_comm]
        exact Nat.le_ceil _
      have hd := lag_of_linear_errors hscale hτ hdr hv hε₀ hε₁ hcl n i (a n) (hs.trans ha')
        (hn.1.trans (hbT n))
      have hle : (X n i (σ n + a n) : ℝ) ≤ (runMax (X n) (σ n + a n) : ℝ) := by
        exact_mod_cast le_runMax (X := X n) (σ n + a n) i
      linarith only [hd, hle]
    unfold Y
    rw [DefectKnot.sup_scaledPosition_eq (hscale n), DefectKnot.inf_scaledPosition_eq (hscale n)]
    simp only [← sub_div, sub_sub_sub_cancel_right, ← mul_div_assoc]
    push_cast at h
    have hh : (b n : ℝ) - a n ≤
        C * ((runMax (X n) (σ n + a n) : ℝ) - runMin (X n) (σ n + a n)) +
          ((C + 1) * ε n) * (scale n : ℝ) := by
      nlinarith only [h, mul_le_mul_of_nonneg_left hlag hC₀]
    have hh' := (div_le_div_iff_of_pos_right hL).mpr hh
    rwa [add_div, mul_div_cancel_right₀ _ hL.ne'] at hh'

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
private theorem sup_sub_inf {J : Finset ι} (hJ : J.Nonempty) (z : ι → ℝ) (t : ℝ) :
    J.sup' hJ (fun i => t - z i) = t - J.inf' hJ z := by
  apply le_antisymm
  · exact Finset.sup'_le hJ _ (fun i hi => sub_le_sub_left (Finset.inf'_le z hi) _)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hJ z
    rw [he]
    exact Finset.le_sup' (fun i => t - z i) hi

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
private theorem inf_sub_sup {J : Finset ι} (hJ : J.Nonempty) (z : ι → ℝ) (t : ℝ) :
    J.inf' hJ (fun i => t - z i) = t - J.sup' hJ z := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hJ z
    rw [he]
    exact Finset.inf'_le (fun i => t - z i) hi
  · exact Finset.le_inf' hJ _ (fun i hi => sub_le_sub_left (Finset.le_sup' z hi) _)

/-- Any scaling limit of the record intervals with vanishing relative
errors has coalesced by the deterministic deadline. -/
theorem coalesced_at_of_linear_errors {B : ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hne : ∀ n i k, |X n i (k + 1) - X n i k| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hcl : ∀ n, LinearBlockClauses (X n) (τ n) (level n) T (scale n) C v (ε n * (scale n : ℝ)))
    (hC : 1 ≤ C) (hv : 0 < v) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0))
    (hconvR : ∀ i, TendstoUniformly (fun n => ⇑(recordFamily X τ level scale hscale (T : ℝ) n i))
      (fun t => x i t) atTop)
    (hs₀T : 2 / v ≤ (T : ℝ))
    (hB : (1 + 2 / v) * (1 + (C + 1)) ^ (Fintype.card ι - 1) - 1 < (B : ℝ))
    {θ : Set.Icc (0 : ℝ) (T : ℝ)} (hBθ : (B : ℝ) ≤ (θ : ℝ)) (i j : ι) : x i θ = x j θ := by
  have hlip : ∀ i, LipschitzWith 1 (x i) :=
    fun i => lipschitz_of_uniform_recordFamily hscale hne (T := (T : ℝ)) (x := x) (φ := id) hconvR i
  have hconv := fun i => M1C.tendstoUniformly_rawSample hscale hscaleTop hne i (hconvR i)
  have hconvK := M1C.knot_tendsto hscale hscaleTop hne hconvR
  have hmove := motion_of_linear_errors hscale hcl hε hconvK hlip
  have hconv0 : ∀ i, Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0)
      atTop (𝓝 (lift x i 0)) := fun i => by simpa using hconvK i 0 le_rfl (Nat.cast_nonneg T)
  have hgap := M1C.fluidGap_lift_zero_le_one hτ hscale hdr hconv0
  let y (i : ι) (t : ℝ) := t - x i (Set.projIcc 0 (T : ℝ) (Nat.cast_nonneg T) t)
  have hy (i : ι) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) : y i t = t - lift x i t := by
    simp only [y, Set.projIcc_of_mem _ ht, lift_apply ht]
  have hyc (i : ι) : Continuous (y i) := continuous_id.sub ((x i).continuous.comp continuous_projIcc)
  have hs₀ : 0 ≤ 2 / v := by positivity
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hymove : FluidMotionOn y 0 (T : ℝ) := by
    intro i s t hs hst ht
    rw [hy i ⟨hs, hst.trans ht⟩, hy i ⟨hs.trans hst, ht⟩]
    have h := hmove i s t hs hst ht
    exact ⟨by linarith only [h.2], by linarith only [h.1]⟩
  have hsup {J : Finset ι} (hJ : J.Nonempty) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
      J.sup' hJ (fun i => y i t) = t - J.inf' hJ (fun i => lift x i t) := by
    simpa only [hy _ ht] using sup_sub_inf hJ (fun i => lift x i t) t
  have hygap {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
      fluidGap (fun i => y i t) = fluidGap (fun i => lift x i t) := by
    unfold fluidGap fluidMax fluidMin
    rw [hsup Finset.univ_nonempty ht]
    simp only [hy _ ht, inf_sub_sup]
    ring
  have hbounds {J : Finset ι} (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty) {s t : ℝ}
      (hs : 2 / v ≤ s) (hst : s ≤ t) (ht : t ≤ T)
      (hsep : ∀ u ∈ Set.Icc s t, StrictTop y J u) :
      (∀ i ∈ Jᶜ, lift x i t - J.inf' hJ (fun j => lift x j t) ≤
        C * (lift x i s - J.inf' hJ (fun j => lift x j s))) ∧
      t - s ≤ C * fluidGap (fun i => lift x i s) :=
    linear_bounds_of_grid hscale hscaleTop hτ hne hdr hr hcl hC hv hε₀ hε₁ hε hconv hlip hJ hJc
      hs hst ht (fun u hu i hi j hj => by
        have hu' : u ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨(hs₀.trans hs).trans hu.1, hu.2.trans ht⟩
        have h := hsep u hu j hj i hi
        rw [hy i hu', hy j hu'] at h
        linarith only [h])
  have hcomp : TopGroupComparison y (2 / v) C (T : ℝ) := by
    intro J hJ s t hs hst ht hsep i hi
    have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs₀.trans hs, hst.trans ht⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hsI.1.trans hst, ht⟩
    rw [hsup hJ htI, hy i htI, hsup hJ hsI, hy i hsI,
      sub_sub_sub_cancel_left, sub_sub_sub_cancel_left]
    exact (hbounds hJ ⟨i, hi⟩ hs hst ht hsep).1 i hi
  have hmeet : MeetBound y (2 / v) C (T : ℝ) := by
    intro J hJ s t hs hst ht _ hproper hsep
    have hJc : Jᶜ.Nonempty := by
      rw [Finset.compl_eq_univ_sdiff]
      exact Finset.sdiff_nonempty.mpr (fun h => hproper (Finset.eq_univ_iff_forall.mpr (fun i => h (Finset.mem_univ i))))
    rw [hygap ⟨hs₀.trans hs, hst.trans ht⟩]
    exact (hbounds hJ hJc hs hst ht (by simpa only [StrictTop, Finset.compl_eq_univ_sdiff] using hsep)).2
  have hp := leaderPersist_of_topComparison hyc hC₀ hcomp
  have hj := joinRuleFrom_of_leaderPersist hp hC₀ hmeet
  have hg₀ : fluidGap (fun i => y i 0) ≤ 1 := by rwa [hygap ⟨le_rfl, Nat.cast_nonneg T⟩]
  have hg := fluidGap_le_one_add hymove hs₀ hs₀T hg₀
  have hBT := hB.trans_le (hBθ.trans θ.2.2)
  obtain ⟨u, _, hu, hco⟩ := exists_coalescence_of_leaderPersist hp
    (fun i s t hs hst ht => hymove i s t (hs₀.trans hs) hst ht) hj
    (by positivity : 0 ≤ 1 + 2 / v) (by positivity) hBT (by linarith only) hg
  have he := hco θ (hu.trans (hB.le.trans hBθ)) θ.2.2 i j
  rw [hy i θ.2, hy j θ.2, lift_apply θ.2, lift_apply θ.2] at he
  linarith only [he]

end Swarming.Diameter
