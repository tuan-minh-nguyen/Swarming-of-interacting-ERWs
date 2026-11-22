import SwarmDiameter.TwoWalkerMeeting
import SwarmDiameter.TwoWalkerGap
import SwarmDiameter.MarkedSpatialTail
import SwarmDiameter.RecordCubicBlock

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmRecordMeas.Actual SwarmRestart
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem measureReal_iUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → Set Ω} {a : ℝ}
    (h : ∀ i, μ.real (E i) ≤ a) : μ.real (⋃ i, E i) ≤ (Fintype.card ι : ℝ) * a := by
  refine (measureReal_iUnion_fintype_le E).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i))

/-- Proposition 4.1 for the actual two-walker law. -/
theorem record_two_walker_halving_failure_le_sqrt {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r ≥ 10 * L,
      (arrayMeasure 2).real {U | pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) ≤ 2 * (L : ℝ) ∧
        (L : ℝ) < pathDiameter (recordTime (posPath p m U) (r + L)).toNat (posPath p m U) ∧
        recordTime (posPath p m U) (r + L) - recordTime (posPath p m U) r ≤ ((L ^ 3 : ℕ) : ℕ∞)}
        ≤ Real.exp (-c * Real.sqrt (L : ℝ)) := by
  classical
  obtain ⟨a, C, ha, hC, hSpatial⟩ := arrayMeasure_sum_hof_pow_tail hp₀ hp₁ hm 1
  obtain ⟨b, hb, hDown⟩ := record_downward_excursion_failure_le_sqrt (N := 2) hp₀ hp₁ hm
  let D := 5 * C + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let J := 2 * (2 * D + 1)
  have hJ : 0 < J := by dsimp only [J]; positivity
  let d := 1 / (16384 * J)
  have hd : 0 < d := by dsimp only [d]; positivity
  let c := min a (min b (min d (Real.log 2)))
  have hc : 0 < c := lt_min ha (lt_min hb (lt_min hd (Real.log_pos (by norm_num))))
  let A := 2 * (J + 1) ^ 2
  let P := 36 * C + 41 + 38 * A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  let V (L : ℕ) := Real.sqrt (L : ℝ)
  have hV : Tendsto V atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [eventually_ge_atTop (32 : ℕ), hV.eventually_ge_atTop 64, hDown,
    hV.eventually (LocSumR1.eventually_poly_mul_exp_le hP hc 18)] with L hL hV64 hDown hPoly
  intro r hr
  let x := L / 16
  let k := ⌈V L⌉₊
  let n := ⌈2 * D * (L : ℝ)⌉₊
  let K := k * n
  let H := 2 * L ^ 3
  let μ := arrayMeasure 2
  let σ (U : Array 2) := recTimeA p m U r
  let F := posPath (N := 2) p m
  let hpot (i : Fin 2) (U : Array 2) := SwarmOcc.Hpot (envH p m i U)
  let W := V L
  have hV₀ : (1 : ℝ) ≤ W := by linarith only [hV64]
  have hV₂ : W ^ 2 = (L : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hL₁ : 1 ≤ L := by omega
  have hL₀ : (0 : ℝ) < L := by exact_mod_cast hL₁
  have hxr : (L : ℝ) ≤ 32 * (x : ℝ) := by
    exact_mod_cast (show L ≤ 32 * x by dsimp only [x]; omega)
  have hx : 1 ≤ x := by dsimp only [x]; omega
  have hxL : 16 * x ≤ L := by dsimp only [x]; omega
  have hk : 0 < k := Nat.ceil_pos.mpr (zero_lt_one.trans_le hV₀)
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity)
  have hK : 1 ≤ K := Nat.mul_pos hk hn
  have hkx : k < x := by
    have hk' : (k : ℝ) < W + 1 := Nat.ceil_lt_add_one (zero_le_one.trans hV₀)
    have h := mul_nonneg (sub_nonneg.mpr hV64) (show 0 ≤ W + 32 by positivity)
    have : W + 1 ≤ (x : ℝ) := by nlinarith only [h, hV₂, hxr]
    exact_mod_cast hk'.trans_le this
  have hKmax : (K : ℝ) ≤ J * W ^ 3 := by
    have hk' : (k : ℝ) ≤ 2 * W := (Nat.ceil_lt_add_one (zero_le_one.trans hV₀)).le.trans (by linarith)
    have hn' : (n : ℝ) ≤ (2 * D + 1) * (L : ℝ) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * D * (L : ℝ) by positivity)
      have h₁ : (1 : ℝ) ≤ L := by exact_mod_cast hL₁
      change (n : ℝ) < 2 * D * (L : ℝ) + 1 at h
      linarith only [h, h₁]
    change (↑(k * n : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (2 * W) * ((2 * D + 1) * (L : ℝ)) :=
        mul_le_mul hk' hn' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← hV₂]; dsimp only [J]; ring
  have hExp : Real.exp (-(x : ℝ) ^ 2 / (16 * (K : ℝ))) ≤ Real.exp (-c * W) := by
    have hK₀ : (0 : ℝ) < K := by exact_mod_cast hK
    have hden := mul_le_mul_of_nonneg_left hKmax (by norm_num : (0 : ℝ) ≤ 16)
    have hx' : W ^ 2 / 32 ≤ (x : ℝ) := by rw [hV₂]; linarith only [hxr]
    have hpow := pow_le_pow_left₀ (by positivity) hx' 2
    have hcalc : d * W ≤ (x : ℝ) ^ 2 / (16 * (K : ℝ)) := by
      calc
        _ = (W ^ 2 / 32) ^ 2 / (16 * (J * W ^ 3)) := by
          dsimp only [d]
          field_simp [ne_of_gt hJ, ne_of_gt (zero_lt_one.trans_le hV₀)]
          ring
        _ ≤ (x : ℝ) ^ 2 / (16 * (J * W ^ 3)) :=
          div_le_div_of_nonneg_right hpow (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have hc' : c ≤ d := (min_le_right a _).trans ((min_le_right b _).trans (min_le_left d _))
    linarith only [hcalc, mul_le_mul_of_nonneg_right hc' (zero_le_one.trans hV₀)]
  have hGeom : (1 / 2 : ℝ) ^ k ≤ Real.exp (-c * W) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num,
      ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hc' : c ≤ Real.log 2 := (min_le_right a _).trans ((min_le_right b _).trans (min_le_right d _))
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hk' : W ≤ (k : ℝ) := Nat.le_ceil _
    have hprod := mul_le_mul_of_nonneg_right hc' (zero_le_one.trans hV₀)
    have hprod' := mul_le_mul_of_nonneg_left hk' hlog.le
    linarith only [hprod, hprod']
  have hMart : 2 * ((K : ℝ) + 1) ^ 2 * Real.exp (-(x : ℝ) ^ 2 / (16 * (K : ℝ))) ≤
      A * W ^ 6 * Real.exp (-c * W) := by
    have hW := one_le_pow₀ hV₀ (n := 3)
    have h1 : (K : ℝ) + 1 ≤ (J + 1) * W ^ 3 := by nlinarith only [hKmax, hW]
    have h2 := pow_le_pow_left₀ (show 0 ≤ (K : ℝ) + 1 by positivity) h1 2
    calc
      _ ≤ (2 * ((J + 1) * W ^ 3) ^ 2) * Real.exp (-c * W) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hExp (by positivity) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have hnD : 2 * (D * (L : ℝ)) ≤ (n : ℝ) := by
    rw [← mul_assoc]
    exact Nat.le_ceil _
  have hr₁ : 1 ≤ r := by omega
  have hr₅ : 5 * L ≤ r := by omega
  let I := {ij : Fin 2 × Fin 2 // ij.1 ≠ ij.2}
  let Z := Fin (H + 1)
  let S (i : Fin 2) (z : Z) : Set (Array 2) :=
    {U | D * L < hpot i U ((r + (z : ℕ) : ℕ) : ℤ) - hpot i U ((r + (z : ℕ) - 5 * L : ℕ) : ℤ)}
  let E (ij : I) : Set (Array 2) := {U | U ∈ ReachAll p m ∧
    (r : ℤ) ≤ runMax p m U ij.1.1 (σ U) ∧ hpot ij.1.1 U (r : ℤ) -
      hpot ij.1.1 U ((r - 4 * L : ℕ) : ℤ) ≤ D * L ∧
    U ∈ intervalSurvival p m ij.1.2 (r - 4 * L) (r - 1) (σ U) K}
  let M (i : Fin 2) : Set (Array 2) := ReachAll p m ∩ StoppedWindow.stoppedWindow
    (fun t U => driftMartingale p m U t i) σ K (x : ℝ)
  let Q (a : (I × Z) × Z) : Set (Array 2) :=
    let h := r + (a.1.2 : ℕ)
    frontReachesBeforeExit p m r a.2 (h - 5 * x) (h - 1) a.1.1.1.1 a.1.1.1.2 (x : ℝ) ∩ {U |
      hpot a.1.1.1.1 U (h : ℤ) - hpot a.1.1.1.1 U ((h - 5 * x : ℕ) : ℤ) ≤ D * L}
  let B := recordDownwardExcursion (N := 2) p m r (r - x) (r + H) H k
  have hcover : ∀ᵐ U ∂μ, (pathDiameter (recordTime (F U) r).toNat (F U) ≤ 2 * (L : ℝ) ∧
      (L : ℝ) < pathDiameter (recordTime (F U) (r + L)).toNat (F U) ∧
      recordTime (F U) (r + L) - recordTime (F U) r ≤ ((L ^ 3 : ℕ) : ℕ∞)) →
      U ∈ B ∪ ((⋃ iz : Fin 2 × Z, S iz.1 iz.2) ∪ ((⋃ a, E a) ∪ ((⋃ i, M i) ∪ (⋃ z, Q z)))) := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := 2) hp₀ hp₁ hm (by decide)] with U hU hbad
    by_contra hno
    have hnoB : U ∉ B := fun h => hno (Or.inl h)
    have hnoS (i : Fin 2) (z : Z) : U ∉ S i z :=
      fun h => hno (Or.inr (Or.inl (mem_iUnion.mpr ⟨(i, z), h⟩)))
    have hnoE (ij : I) : U ∉ E ij :=
      fun h => hno (Or.inr (Or.inr (Or.inl (mem_iUnion.mpr ⟨ij, h⟩))))
    have hnoM (i : Fin 2) : U ∉ M i :=
      fun h => hno (Or.inr (Or.inr (Or.inr (Or.inl (mem_iUnion.mpr ⟨i, h⟩)))))
    have hnoQ (z : (I × Z) × Z) : U ∉ Q z :=
      fun h => hno (Or.inr (Or.inr (Or.inr (Or.inr (mem_iUnion.mpr ⟨z, h⟩)))))
    have hspan (i : Fin 2) (h w : ℕ) (hhr : r ≤ h) (hhH : h ≤ r + H) (hw : w ≤ 5 * L) :
        hpot i U (h : ℤ) - hpot i U ((h - w : ℕ) : ℤ) ≤ D * L := by
      let z : Z := ⟨h - r, by omega⟩
      have hz : r + (z : ℕ) = h := by dsimp only [z]; omega
      have hS : hpot i U (h : ℤ) - hpot i U ((h - 5 * L : ℕ) : ℤ) ≤ D * L := by
        apply le_of_not_gt
        have h' := hnoS i z
        change ¬ (D * L < hpot i U _ - hpot i U _) at h'
        rwa [hz] at h'
      have hm : Monotone (hpot i U) := Hpot_envH_monotone (m := m) hp₀.le hp₁ i U
      exact (sub_le_sub_left (hm (by exact_mod_cast (show h - 5 * L ≤ h - w by omega))) _).trans hS
    have h₀ := recordTime_posPath_eq_of_mem_reachAll hU r
    have h₁ := recordTime_posPath_eq_of_mem_reachAll hU (r + L)
    obtain ⟨hInit, hDia, hTime⟩ := hbad
    rw [h₀, ENat.toNat_natCast] at hInit
    rw [h₁, ENat.toNat_natCast] at hDia
    rw [h₁, h₀, ← ENat.natCast_sub, ENat.natCast_le_natCast] at hTime
    obtain ⟨η, hη₀, hηK, hη⟩ := two_walker_meeting_of_no_deviations hp₀.le (by omega : 1 ≤ m)
      hU hx (by omega) (by omega) hInit
      (fun i j hij hi h => hnoE ⟨(i, j), hij⟩ ⟨hU, hi, hspan i r (4 * L) le_rfl (by omega) (by omega), h⟩)
      (fun i h => hnoM i ⟨hU, h⟩)
    let t := recTimeA p m U (r + L)
    have ht : η ≤ t := by
      by_contra! h
      obtain ⟨i, hi⟩ := M4RecordGeom.exists_traj_eq_level hU (r + L)
      have hle := (le_runMax p m U i t).trans (runMax_mono p m U i h.le)
      have h₁' := (hη i).2.2
      change (trajectory p m U t).pos i = ((r + L : ℕ) : ℤ) at hi
      push_cast at hi
      omega
    have htσ : t ≤ σ U + H := by dsimp only [σ, t, H]; omega
    have hMax (i : Fin 2) (u : ℕ) (hηu : η ≤ u) (hut : u ≤ t) :
        runMax p m U i u ≤ ((r + H : ℕ) : ℤ) := by
      have hs : σ U ≤ u := hη₀.trans hηu
      have hg (v : ℕ) : runMax p m U i (σ U + v) ≤ runMax p m U i (σ U) + (v : ℤ) := by
        induction v with
        | zero => simp
        | succ v ih =>
          have h1 := LocSepWindow.runMax_succ_le p m U i (σ U + v)
          rw [Nat.add_succ]
          push_cast
          change runMax p m U i (σ U + v + 1) ≤ runMax p m U i (σ U) + ((v : ℤ) + 1)
          omega
      have h1 := hg (u - σ U)
      rw [Nat.add_sub_cancel' hs] at h1
      have h2 := individual_runMax_le_record hU (r := r) i
      have hu := hut.trans htσ
      change runMax p m U i (σ U) ≤ _ at h2
      push_cast
      omega
    have hbig : 4 * (x : ℝ) + k < pathDiameter t (F U) :=
      (by exact_mod_cast (show 4 * x + k ≤ L by omega) : 4 * (x : ℝ) + k ≤ (L : ℝ)).trans_lt hDia
    obtain ⟨i, j, v, h, hij, hv, hrh, hh, hQ⟩ :=
      exists_passage_order_of_large_diameter hU hx hkx (by omega) hη₀ ht htσ hη hMax hnoB hbig
    let z : Z := ⟨h - r, by omega⟩
    let vv : Z := ⟨v, by omega⟩
    have hz : r + (z : ℕ) = h := by dsimp only [z]; omega
    apply hnoQ ((⟨(i, j), hij⟩, z), vv)
    change U ∈ frontReachesBeforeExit p m r v (r + (z : ℕ) - 5 * x) (r + (z : ℕ) - 1) i j _ ∧ _
    change _ ∧ hpot i U ((r + (z : ℕ) : ℕ) : ℤ) - hpot i U ((r + (z : ℕ) - 5 * x : ℕ) : ℤ) ≤ D * L
    rw [hz]
    exact ⟨hQ, hspan i h (5 * x) hrh hh (by omega)⟩
  let e := Real.exp (-c * W)
  have hS (iz : Fin 2 × Z) : μ.real (S iz.1 iz.2) ≤ 6 * C * W ^ 2 * e := by
    let h := r + (iz.2 : ℕ)
    have hh : 5 * L ≤ h := by dsimp only [h]; omega
    have hEq : h - 5 * L + 5 * L = h := Nat.sub_add_cancel hh
    have hs := hSpatial 2 iz.1 (h - 5 * L) (5 * L) (L : ℝ) hL₀
    simp only [pow_one, hEq, Nat.cast_mul, Nat.cast_ofNat] at hs
    have hmain : μ.real (S iz.1 iz.2) ≤ C * (5 * (L : ℝ) + 1) *
        Real.exp (-a * (L : ℝ) ^ (1 / 2 : ℝ)) := by
      convert hs using 2
      · ext U
        change D * L < hpot iz.1 U (h : ℤ) - hpot iz.1 U ((h - 5 * L : ℕ) : ℤ) ↔ _
        rw [Hpot_nat_sub_eq_sum_Ico _ (Nat.sub_le _ _)]
        dsimp only [hpot, envH, D]
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro h' <;> linarith only [h']
      · norm_num
    refine hmain.trans ?_
    have hpow : (L : ℝ) ^ (1 / 2 : ℝ) = W := (Real.sqrt_eq_rpow _).symm
    rw [hpow, ← hV₂]
    apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
    · have hW := one_le_pow₀ hV₀ (n := 2)
      nlinarith only [mul_le_mul_of_nonneg_left hW hC.le]
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (neg_le_neg (show c ≤ a from min_le_left _ _)) (zero_le_one.trans hV₀))
  have hE (ij : I) : μ.real (E ij) ≤ e := by
    have h := record_offset_interval_survival_prob_le (a := r - 4 * L) (b := r - 1)
      hp₀ hp₁ hm ij.2.symm (by omega) r 0 k hn hnD
    simp only [Nat.add_zero, Nat.sub_add_cancel hr₁] at h
    exact h.trans hGeom
  have hM (i : Fin 2) : μ.real (M i) ≤ A * W ^ 6 * e := by
    have h := record_offset_martingale_window_prob_le (m := m) hp₀ hp₁ i r 0 hK
      (ε := (x : ℝ)) (by exact_mod_cast (show 0 < x by omega))
    simp only [Nat.add_zero] at h
    exact h.trans hMart
  have hQ (a : (I × Z) × Z) : μ.real (Q a) ≤ (1 + A * W ^ 6) * e := by
    let h := r + (a.1.2 : ℕ)
    have hhp : 1 ≤ h := by dsimp only [h]; omega
    have hp := two_walker_passage_order_prob_le (a := h - 5 * x) (b := h - 1) hp₀ hp₁ hm
      a.1.1.2 (by omega) r a.2 k hn hk hnD (x := (x : ℝ)) (by exact_mod_cast (show 0 < x by omega))
    rw [Nat.sub_add_cancel hhp] at hp
    exact hp.trans (by rw [add_mul, one_mul]; exact add_le_add hGeom hMart)
  have hB : μ.real B ≤ e := by
    have hcb : c ≤ b := (min_le_right a _).trans (min_le_left b _)
    exact (hDown r hr x (by omega)).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg hcb) (zero_le_one.trans hV₀)))
  have hI : (Fintype.card I : ℝ) ≤ 4 := by
    have hc := Fintype.card_le_of_injective (fun a : I => a.1) Subtype.val_injective
    rw [Fintype.card_prod, Fintype.card_fin] at hc
    exact_mod_cast hc
  have hZ : (Fintype.card Z : ℝ) ≤ 3 * W ^ 6 := by
    have hH₁ : (H : ℝ) + 1 = 2 * W ^ 6 + 1 := by
      dsimp only [H]
      push_cast
      rw [← hV₂]
      ring
    rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one, hH₁]
    linarith only [one_le_pow₀ hV₀ (n := 6)]
  have hSsum : μ.real (⋃ iz : Fin 2 × Z, S iz.1 iz.2) ≤ (36 * C * W ^ 8) * e := by
    refine (measureReal_iUnion_le_card_mul hS).trans ?_
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.card_fin, Nat.cast_ofNat]
    calc
      _ ≤ (2 * (3 * W ^ 6)) * (6 * C * W ^ 2 * e) := by gcongr
      _ = _ := by ring
  have hEsum : μ.real (⋃ a, E a) ≤ 4 * e :=
    (measureReal_iUnion_le_card_mul hE).trans (mul_le_mul_of_nonneg_right hI (Real.exp_pos _).le)
  have hMsum : μ.real (⋃ i, M i) ≤ (2 * A * W ^ 6) * e := by
    refine (measureReal_iUnion_le_card_mul hM).trans ?_
    rw [Fintype.card_fin, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  have hQsum : μ.real (⋃ z, Q z) ≤ (36 * (1 + A) * W ^ 18) * e := by
    refine (measureReal_iUnion_le_card_mul hQ).trans ?_
    simp only [Fintype.card_prod, Nat.cast_mul]
    have hW₆ := one_le_pow₀ hV₀ (n := 6)
    have h₁ : 1 + A * W ^ 6 ≤ (1 + A) * W ^ 6 := by nlinarith only [hW₆]
    calc
      _ ≤ (4 * (3 * W ^ 6) * (3 * W ^ 6)) * (((1 + A) * W ^ 6) * e) := by gcongr
      _ = _ := by ring
  have hPower (a : ℕ) (ha : a ≤ 18) : W ^ a ≤ W ^ 18 := pow_le_pow_right₀ hV₀ ha
  have hC₈ := mul_le_mul_of_nonneg_left (hPower 8 (by decide)) (show 0 ≤ 36 * C by positivity)
  have hA₆ := mul_le_mul_of_nonneg_left (hPower 6 (by decide)) (show 0 ≤ 2 * A by positivity)
  have hA₀ := one_le_pow₀ hV₀ (n := 18)
  refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)).trans ?_
  calc
    _ ≤ e + ((36 * C * W ^ 8) * e + (4 * e + ((2 * A * W ^ 6) * e + (36 * (1 + A) * W ^ 18) * e))) :=
      (measureReal_union_le _ _).trans (add_le_add hB ((measureReal_union_le _ _).trans
        (add_le_add hSsum ((measureReal_union_le _ _).trans
          (add_le_add hEsum ((measureReal_union_le _ _).trans (add_le_add hMsum hQsum)))))))
    _ ≤ P * W ^ 18 * e := by
      dsimp only [P]
      have he := (Real.exp_pos (-c * W)).le
      change 0 ≤ e at he
      nlinarith only [mul_le_mul_of_nonneg_right hC₈ he, mul_le_mul_of_nonneg_right hA₆ he,
        mul_le_mul_of_nonneg_right hA₀ he]
    _ ≤ _ := hPoly

end Swarming.Diameter
