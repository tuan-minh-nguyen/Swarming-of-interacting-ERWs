import SwarmDiameter.TwoWalkerBlock
import SwarmDiameter.RecordTailFromBlock

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl SwarmRecordMeas.Actual SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem record_passage_duration_prob_le {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (r B u : ℕ) :
    (arrayMeasure N).real {U | ((B * u : ℕ) : ℕ∞) <
      recordTime (posPath p m U) (r + B) - recordTime (posPath p m U) r} ≤
      ∑ j ∈ Finset.range B, (arrayMeasure N).real {U |
        (u : ℕ∞) < recordDuration (posPath p m U) (r + j)} := by
  let μ := arrayMeasure N
  let E (j : ℕ) : Set (Array N) := {U | (u : ℕ∞) < recordDuration (posPath p m U) (r + j)}
  have hcover : ∀ᵐ U ∂μ, ((B * u : ℕ) : ℕ∞) <
      recordTime (posPath p m U) (r + B) - recordTime (posPath p m U) r →
        U ∈ ⋃ j ∈ Finset.range B, E j := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN] with U hU hTime
    by_contra hnot
    let τ := recTimeA p m U
    have hstep (j : ℕ) (hj : j < B) : τ (r + (j + 1)) - τ (r + j) ≤ u := by
      have h : recordDuration (posPath p m U) (r + j) ≤ (u : ℕ∞) :=
        le_of_not_gt (fun h : U ∈ E j => hnot (Set.mem_biUnion (Finset.mem_range.mpr hj) h))
      rw [recordDuration, recordTime_posPath_eq_of_mem_reachAll hU, recordTime_posPath_eq_of_mem_reachAll hU,
        ← ENat.natCast_sub, ENat.natCast_le_natCast, Nat.add_assoc] at h
      exact h
    have ht : ∀ b ≤ B, τ (r + b) ≤ τ r + b * u := by
      intro b
      induction b with
      | zero => simp
      | succ j ih =>
        intro hj
        have h₁ := hstep j (by omega)
        have h₂ := ih (by omega)
        rw [Nat.succ_mul]
        omega
    rw [recordTime_posPath_eq_of_mem_reachAll hU, recordTime_posPath_eq_of_mem_reachAll hU,
      ← ENat.natCast_sub, ENat.natCast_lt_natCast] at hTime
    have hh := ht B le_rfl
    change B * u < τ (r + B) - τ r at hTime
    omega
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)).trans
    (measureReal_biUnion_finset_le _ E)

private theorem tendsto_record_duration_limsup {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (u : ℕ) :
    let a (r : ℕ) := (arrayMeasure N).real {U | (u : ℕ∞) < recordDuration (posPath p m U) r}
    Tendsto a atTop (𝓝 (limsup a atTop)) := by
  have h := (tendsto_record_duration_tail_occupation (N := N) hp₀ hp₁ hm hN u).2.2
  dsimp only
  rw [h.limsup_eq]
  exact h

private theorem tendsto_record_diameter_limsup {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (x : ℝ) :
    let a (r : ℕ) := (arrayMeasure N).real {U | x < pathDiameter
      (recordTime (posPath p m U) r).toNat (posPath p m U)}
    Tendsto a atTop (𝓝 (limsup a atTop)) := by
  have h := (tendsto_record_diameter_tail_occupation (N := N) hp₀ hp₁ hm hN x).2.2
  dsimp only
  rw [h.limsup_eq]
  exact h

private theorem record_two_walker_diameter_limsup_le {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) {H d : ℝ} (hH : 0 ≤ H) (hd : 0 < d)
    (hW : ∀ᶠ u : ℕ in atTop, limsup (fun r => (arrayMeasure 2).real
      {U | (u : ℕ∞) < recordDuration (posPath p m U) r}) atTop ≤
        H * Real.exp (-d * (u : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ᶠ L : ℕ in atTop, limsup (fun r =>
      (arrayMeasure 2).real {U | (L : ℝ) < pathDiameter
        (recordTime (posPath p m U) r).toNat (posPath p m U)}) atTop ≤
        K * Real.exp (-c * Real.sqrt (L : ℝ)) := by
  obtain ⟨a, ha, hTwo⟩ := record_two_walker_halving_failure_le_sqrt hp₀ hp₁ hm
  let c := min a (d / 2)
  have hc : 0 < c := lt_min ha (half_pos hd)
  let μ := arrayMeasure 2
  let X := posPath (N := 2) p m
  let V (L : ℕ) := Real.sqrt (L : ℝ)
  have hV : Tendsto V atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hPow : Tendsto (fun L : ℕ => L ^ (2 : ℕ)) atTop atTop := tendsto_pow_atTop (by decide)
  have hRat := LocSumR1.eventually_poly_mul_exp_le (C := H + 1) (by positivity) hd 2
  have hcon : ∀ᶠ L : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
      μ.real {U | (L : ℝ) < pathDiameter (recordTime (X U) (r + L)).toNat (X U)} ≤
        μ.real {U | (2 * (L : ℝ)) < pathDiameter (recordTime (X U) r).toNat (X U)} +
          2 * Real.exp (-c * (L : ℝ) ^ (1 / 2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hTwo, hPow.eventually hW, hV.eventually hRat]
      with L hL hTwoL hDur hPoly
    let E (r : ℕ) := {U | ((L ^ 3 : ℕ) : ℕ∞) < recordTime (X U) (r + L) - recordTime (X U) r}
    let u := L ^ 2
    let F (r : ℕ) := {U | (u : ℕ∞) < recordDuration (X U) r}
    let e := Real.exp (-d * (u : ℝ) ^ (1 / 3 : ℝ))
    have he : 0 < e := Real.exp_pos _
    have hlim := tendsto_record_duration_limsup (N := 2) hp₀ hp₁ hm le_rfl u
    have hF : ∀ᶠ r : ℕ in atTop, μ.real (F r) ≤ (H + 1) * e := by
      have hlt := (show limsup (fun r => μ.real (F r)) atTop ≤ H * e from hDur).trans_lt
        (by linarith only [he] : H * e < (H + 1) * e)
      exact ((tendsto_order.mp hlim).2 _ hlt).mono (fun _ h => h.le)
    have hF' : ∀ᶠ r : ℕ in atTop, ∀ j ∈ Finset.range L, μ.real (F (r + j)) ≤ (H + 1) * e := by
      rw [Finset.eventually_all]
      intro j _
      exact (tendsto_add_atTop_nat j).eventually hF
    filter_upwards [eventually_ge_atTop (10 * L), hF'] with r hr hF'
    have hLE : μ.real (E r) ≤ (L : ℝ) * ((H + 1) * e) := by
      have h := record_passage_duration_prob_le (N := 2) hp₀ hp₁ hm le_rfl r L u
      rw [show L * u = L ^ 3 by dsimp only [u]; ring] at h
      exact h.trans (by simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
        (Finset.sum_le_sum (s := Finset.range L) hF'))
    have hV₀ : 0 ≤ V L := Real.sqrt_nonneg _
    have hV₂ : V L ^ 2 = (L : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hEst : V L ≤ (u : ℝ) ^ (1 / 3 : ℝ) := by
      have hL₀ : (1 : ℝ) ≤ L := by exact_mod_cast hL
      rw [show V L = (L : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _]
      dsimp only [u]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow_of_exponent_le hL₀ (by norm_num)
    have hEb : μ.real (E r) ≤ Real.exp (-c * V L) := by
      refine hLE.trans ?_
      have he' : e ≤ Real.exp (-d * V L) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hEst (neg_nonpos.mpr hd.le))
      rw [← hV₂]
      calc
        _ = ((H + 1) * V L ^ 2) * e := by ring
        _ ≤ (H + 1) * V L ^ 2 * Real.exp (-d * V L) :=
          mul_le_mul_of_nonneg_left he' (by positivity)
        _ ≤ Real.exp (-(d / 2) * V L) := hPoly
        _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hV₀)
    let A : Set (Array 2) := {U | (2 * (L : ℝ)) < pathDiameter (recordTime (X U) r).toNat (X U)}
    let G : Set (Array 2) := {U | pathDiameter (recordTime (X U) r).toNat (X U) ≤ 2 * (L : ℝ) ∧
      (L : ℝ) < pathDiameter (recordTime (X U) (r + L)).toNat (X U) ∧
      recordTime (X U) (r + L) - recordTime (X U) r ≤ ((L ^ 3 : ℕ) : ℕ∞)}
    have hg : μ.real G ≤ Real.exp (-c * V L) := (hTwoL r hr).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hV₀))
    have hsub : {U | (L : ℝ) < pathDiameter (recordTime (X U) (r + L)).toNat (X U)} ⊆
        A ∪ (G ∪ E r) := by
      intro U hU
      by_cases hA : U ∈ A
      · exact Or.inl hA
      · by_cases hE : U ∈ E r
        · exact Or.inr (Or.inr hE)
        · exact Or.inr (Or.inl ⟨le_of_not_gt hA, hU, le_of_not_gt hE⟩)
    rw [← Real.sqrt_eq_rpow]
    refine (measureReal_mono hsub (measure_ne_top μ _)).trans ((measureReal_union_le _ _).trans ?_)
    have hs := (measureReal_union_le G (E r)).trans (add_le_add hg hEb)
    exact add_le_add le_rfl (by linarith only [hs])
  obtain ⟨L₀, hcon⟩ := eventually_atTop.mp hcon
  let K := 2 / (1 - Real.exp (-c * ((2 : ℝ) ^ (1 / 2 : ℝ) - 1)))
  have hK : 0 ≤ K := by
    have h : (1 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith only [hc, h])))
  refine ⟨K, c, hK, hc, ?_⟩
  filter_upwards [eventually_ge_atTop L₀, eventually_ge_atTop (1 : ℕ)] with L hL₀ hL
  rw [Real.sqrt_eq_rpow]
  exact record_diameter_tail_le_of_contraction (N := 2) hp₀ hp₁ hm le_rfl (B := 1)
    (by norm_num) hc (by norm_num : (0 : ℝ) < 1 / 2)
    (fun l hl => by simpa only [one_mul] using hcon l hl) hL₀ hL

/-- The square-root exponential upper bound for diameter exceedances between
consecutive record times of two walkers. -/
theorem record_two_walker_exceedance_limsup_le {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) {H d : ℝ} (hH : 0 ≤ H) (hd : 0 < d)
    (hW : ∀ᶠ u : ℕ in atTop, limsup (fun r => (arrayMeasure 2).real
      {U | (u : ℕ∞) < recordDuration (posPath p m U) r}) atTop ≤
        H * Real.exp (-d * (u : ℝ) ^ (1 / 3 : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, limsup (fun r => (arrayMeasure 2).real
      {U | recordIntervalExceeds (posPath p m U) r x}) atTop ≤ Real.exp (-c * Real.sqrt x) := by
  obtain ⟨K, a, hK, ha, hD⟩ := record_two_walker_diameter_limsup_le hp₀ hp₁ hm hH hd hW
  let c := min (a / 2) (min d (1 / 128 : ℝ))
  have hc : 0 < c := lt_min (half_pos ha) (lt_min hd (by norm_num))
  have hca : c ≤ a / 2 := min_le_left _ _
  have hcd : c ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hc₁ : c ≤ 1 / 128 := (min_le_right _ _).trans (min_le_right _ _)
  let l (x : ℝ) := ⌊x / 2⌋₊
  let u (x : ℝ) := ⌈x ^ (3 / 2 : ℝ)⌉₊
  have hl : Tendsto l atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  have hu : Tendsto u atTop atTop := tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop (by norm_num))
  let P := K + H + 12
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpoly := LocSumR1.eventually_poly_mul_exp_le hP hc 3
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ), hl.eventually hD, hu.eventually hW,
    Real.tendsto_sqrt_atTop.eventually hpoly] with x hx hD hW hp
  let V := Real.sqrt x
  let e := Real.exp (-c * V)
  let μ := arrayMeasure 2
  let X := posPath (N := 2) p m
  let D (z : ℝ) (r : ℕ) := μ.real {U | z < pathDiameter (recordTime (X U) r).toNat (X U)}
  let W (r : ℕ) := μ.real {U | (u x : ℕ∞) < recordDuration (X U) r}
  let E (r : ℕ) := μ.real {U | recordIntervalExceeds (X U) r x}
  have hx₀ : 0 < x := (by norm_num : 0 < (4 : ℝ)).trans_le hx
  have hV : 1 ≤ V := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith only [hx] : 1 ≤ x)
  have hV₀ : (0 : ℝ) ≤ V := zero_le_one.trans hV
  have hV₂ : V ^ 2 = x := Real.sq_sqrt hx₀.le
  have hV₃ : V ^ (3 : ℕ) = x ^ (3 / 2 : ℝ) := by
    dsimp only [V]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
    norm_num
  have huLo : V ^ 3 ≤ (u x : ℝ) := hV₃.le.trans (Nat.le_ceil _)
  have hU₀ : 0 < u x := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx₀ _)
  have hU₁ : 1 ≤ u x := hU₀
  have huHi : (u x : ℝ) ≤ 2 * V ^ 3 := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hx₀.le (3 / 2 : ℝ))
    change (u x : ℝ) < x ^ (3 / 2 : ℝ) + 1 at h
    rw [← hV₃] at h
    linarith only [h, one_le_pow₀ hV (n := 3)]
  have hWpow : V ≤ (u x : ℝ) ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (pow_nonneg hV₀ 3) huLo (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV₀] at h
    norm_num at h
    exact h
  have hWlim : limsup W atTop ≤ H * e := by
    refine hW.trans (mul_le_mul_of_nonneg_left ?_ hH)
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_right hcd hV₀
    have h₂ := mul_le_mul_of_nonneg_left hWpow hd.le
    linarith only [h₁, h₂]
  have hlLo : x / 4 ≤ (l x : ℝ) := by
    have h := Nat.lt_floor_add_one (x / 2)
    change x / 2 < (l x : ℝ) + 1 at h
    linarith only [h, hx]
  have hlHi : (l x : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hlsqrt : V / 2 ≤ Real.sqrt (l x : ℝ) := by
    have h := Real.sqrt_le_sqrt hlLo
    rw [Real.sqrt_div hx₀.le, show Real.sqrt 4 = 2 by norm_num] at h
    exact h
  have hDlim : limsup (D (x / 2)) atTop ≤ K * e := by
    have hconv := tendsto_record_diameter_limsup (N := 2) hp₀ hp₁ hm le_rfl (x / 2)
    have hconv' := tendsto_record_diameter_limsup (N := 2) hp₀ hp₁ hm le_rfl (l x : ℝ)
    have h := le_of_tendsto_of_tendsto' hconv hconv' (fun r =>
      measureReal_mono (fun _ hz => hlHi.trans_lt hz) (measure_ne_top _ _))
    refine h.trans (hD.trans (mul_le_mul_of_nonneg_left ?_ hK))
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_right hca hV₀
    have h₂ := mul_le_mul_of_nonneg_left hlsqrt ha.le
    linarith only [h₁, h₂]
  let B := 4 * ((u x : ℝ) + 1) * Real.exp (-(x ^ 2) / (64 * (u x : ℝ)))
  have hB : B ≤ 12 * V ^ 3 * e := by
    have hUpos : (0 : ℝ) < (u x : ℝ) := by exact_mod_cast hU₀
    have hrate : V / 128 ≤ x ^ 2 / (64 * (u x : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (u x : ℝ))).mpr
      calc
        _ ≤ (V / 128) * (64 * (2 * V ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huHi (by norm_num)) (by positivity)
        _ = _ := by rw [← hV₂]; ring
    have he : Real.exp (-(x ^ 2) / (64 * (u x : ℝ))) ≤ e := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      have h := mul_le_mul_of_nonneg_right hc₁ hV₀
      linarith only [hrate, h]
    have hlen : (u x : ℝ) + 1 ≤ 3 * V ^ 3 := by linarith only [huHi, one_le_pow₀ hV (n := 3)]
    dsimp only [B]
    calc
      _ ≤ (4 * (3 * V ^ 3)) * e := mul_le_mul (mul_le_mul_of_nonneg_left hlen (by norm_num)) he
        (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hpoint (r : ℕ) : E r ≤ D (x / 2) r + W r + B := by
    simpa only [B, Nat.cast_ofNat, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
      (record_interval_exceedance_prob_le (N := 2) hp₀ hp₁ hm le_rfl r (u x) hU₁ hx₀)
  have hlim : limsup (fun r => D (x / 2) r + W r + B) atTop =
      limsup (D (x / 2)) atTop + limsup W atTop + B :=
    (((tendsto_record_diameter_limsup (N := 2) hp₀ hp₁ hm le_rfl (x / 2)).add
      (tendsto_record_duration_limsup (N := 2) hp₀ hp₁ hm le_rfl (u x))).add_const B).limsup_eq
  have hmono : limsup E atTop ≤ limsup (fun r => D (x / 2) r + W r + B) atTop :=
    limsup_le_limsup (Eventually.of_forall hpoint) (isCoboundedUnder_le_of_le atTop (fun _ => measureReal_nonneg))
      ⟨2 + B, eventually_map.mpr (Eventually.of_forall fun r => by
        have h₁ : D (x / 2) r ≤ 1 := measureReal_le_one
        have h₂ : W r ≤ 1 := measureReal_le_one
        linarith only [h₁, h₂])⟩
  calc
    _ ≤ limsup (D (x / 2)) atTop + limsup W atTop + B := hmono.trans_eq hlim
    _ ≤ K * e + H * e + 12 * V ^ 3 * e := add_le_add (add_le_add hDlim hWlim) hB
    _ ≤ P * V ^ 3 * e := by
      have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hV (n := 3)) (show 0 ≤ K + H by positivity)
      have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c * V)).le
      dsimp only [P]
      nlinarith only [h']
    _ ≤ _ := hp

end Swarming.Diameter
