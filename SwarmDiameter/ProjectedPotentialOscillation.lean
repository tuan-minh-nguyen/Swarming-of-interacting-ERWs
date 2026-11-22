import SwarmDiameter.MarkedSpatialTail
import Swarm.LocOccCarrierAssembly
import Swarm.RecClockLocgroup

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl SwarmRecordMeas.Actual SwarmMarks
open ActualRecordFiltration LocOccCarrierAssembly
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem measureReal_iUnion_le_of_disjoint_weights {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : ℕ → Set Ω} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise fun i j => Disjoint (A i) (A j))
    (h : ∀ n, μ.real (B n) ≤ c * μ.real (A n)) :
    μ.real (⋃ n, B n) ≤ c := by
  have hh (n : ℕ) : μ (B n) ≤ ENNReal.ofReal c * μ (A n) := by
    have he := ENNReal.ofReal_le_ofReal (h n)
    simpa only [measureReal_def, ENNReal.ofReal_mul hc,
      ENNReal.ofReal_toReal (measure_ne_top μ _)] using he
  have hsum : (∑' n, μ (A n)) ≤ 1 := by
    rw [← measure_iUnion hd hA, ← measure_univ (μ := μ)]
    exact measure_mono (subset_univ _)
  have hbound : μ (⋃ n, B n) ≤ ENNReal.ofReal c := by
    calc
      _ ≤ ∑' n, μ (B n) := measure_iUnion_le _
      _ ≤ ∑' n, ENNReal.ofReal c * μ (A n) := ENNReal.tsum_le_tsum hh
      _ = ENNReal.ofReal c * ∑' n, μ (A n) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal c * 1 := mul_le_mul_right hsum _
      _ = _ := mul_one _
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hc)

/-- On the event that the diameter at the record is at most `L`, the
projected potential at fixed sites in the record interval has a small
oscillation throughout the next `T * L` steps. -/
theorem record_projH_oscillation_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ j : Fin N,
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L), ∃ u v : ℕ,
            recTimeA p m U r ≤ u ∧ u ≤ v ∧ v ≤ recTimeA p m U r + T * L ∧
            ε * (L : ℝ) ≤ |projH p m j v U (y : ℤ) - projH p m j u U (y : ℤ)|})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  obtain ⟨a, ha, hspatial⟩ := hlocal N (2 * T + 4) (show (0 : ℝ) < 1 by norm_num)
  let D := SiteHMax.Cproj p m
  have hD : 0 < D := by
    have h := SiteHMax.capB_pos hp₀ hp₁ m (V := 0) (by norm_num)
    change 0 < SiteHMax.Cproj p m * (2 * 0 + 7) at h
    dsimp only [D]
    linarith
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let b := ε ^ 2 / (1296 * (T : ℝ) * D ^ 2)
  have hb : 0 < b := by
    have hT₀ : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
    dsimp only [b]
    positivity
  let k := min a (b / 2)
  have hk : 0 < k := lt_min ha (half_pos hb)
  let c := k / 2
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  let M : ℝ := 2 * (2 * (T : ℝ) + 3) * ((T : ℝ) + 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoly := ((isLittleO_exp_mul_rpow_of_lt 6 (show -b < -(b / 2) by linarith)).const_mul_left M).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (Real.tendsto_exp_atTop.comp (htop.const_mul_atTop (half_pos hk))).eventually_ge_atTop 2
  refine ⟨c, half_pos hk, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspatial, htop.eventually hpoly, hlarge]
    with L hL hsp hpolyL hlargeL
  intro r hr j
  let μ := arrayMeasure N
  let V := R L
  let w := T * L
  let A (s : ℕ) := recordPrefixBand (N := N) p m r s L
  let I := Finset.Ico (A0 r T L) (A0 r T L + Lw T L)
  let F (s : ℕ) (y : ℕ) : Set (Array N) := {U |
    ∃ u v : ℕ, s ≤ u ∧ u ≤ v ∧ v ≤ s + w ∧
      ε * (L : ℝ) ≤ |projH p m j v U (y : ℤ) - projH p m j u U (y : ℤ)|}
  let G (s : ℕ) : Set (Array N) := {U | ∀ i < w, U ∈ SiteHMax.siteGood p m j V (s + i)}
  let H (s : ℕ) := ⋃ y ∈ I, (A s ∩ G s ∩ F s y)
  let B : Set (Array N) := {U | ∃ (i : Fin N) (y : ℕ),
    y ∈ Finset.Ico (A0 r T L - 1) (A0 r T L + Lw T L) ∧
    V < hof p (SwarmLogRatio.siteMarks p m U i) y}
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hV : 1 ≤ V := Real.one_le_rpow hLr (by norm_num)
  have hw : 1 ≤ w := Nat.mul_le_mul hT hL
  have hδ : 0 < ε * (L : ℝ) := mul_pos hε (zero_lt_one.trans_le hLr)
  have hB : μ.real B ≤ Real.exp (-a * V) := by
    refine (measureReal_mono ?_ (measure_ne_top μ _)).trans (hsp (A0 r T L - 1))
    rintro U ⟨i, y, hy, hf⟩
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Ico.mp hy
    refine Or.inl ⟨i, y - (A0 r T L - 1), ?_, ?_⟩
    · have he : (2 * T + 4) * L = (2 * T + 2) * L + 2 * L := by ring
      dsimp only [Lw] at hy₂
      omega
    · rw [Nat.add_sub_of_le hy₁]
      exact hf
  have hbound : μ.real (⋃ s, H s) ≤
      (I.card : ℝ) * (2 * ((w : ℝ) + 1) *
        Real.exp (-(ε * (L : ℝ)) ^ 2 / (16 * (w : ℝ) * (SiteHMax.capB p m V) ^ 2))) := by
    let K := 2 * ((w : ℝ) + 1) *
      Real.exp (-(ε * (L : ℝ)) ^ 2 / (16 * (w : ℝ) * (SiteHMax.capB p m V) ^ 2))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    change μ.real (⋃ s, H s) ≤ (I.card : ℝ) * K
    refine measureReal_iUnion_le_of_disjoint_weights (mul_nonneg (Nat.cast_nonneg _) hK)
      (fun s => (enlFilt p m).le s _ (measurableSet_recordPrefixBand p m r s L)) ?_ ?_
    · intro s t hst
      rw [← RecClockLG.recordBand_eq_recordPrefixBand p m r L s,
        ← RecClockLG.recordBand_eq_recordPrefixBand p m r L t]
      exact RecClockLG.disjoint_recordBand hst
    · intro s
      refine (measureReal_biUnion_finset_le I _).trans ?_
      have hh (y : ℕ) : μ.real (A s ∩ G s ∩ F s y) ≤ μ.real (A s) * K :=
        M3Hosc.measureReal_cell_siteOsc_pair_le_sharp hp₀ hp₁ m j (y : ℤ)
          (measurableSet_recordPrefixBand p m r s L) (zero_le_one.trans hV) hw hδ
      have he := sum_le_sum (s := I) (fun y _ => hh y)
      simpa only [sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using he
  have hcover : RecClockLG.recordCarrier p m r L ∩ {U |
      ∃ y ∈ I, ∃ u v : ℕ, recTimeA p m U r ≤ u ∧ u ≤ v ∧ v ≤ recTimeA p m U r + w ∧
          ε * (L : ℝ) ≤ |projH p m j v U (y : ℤ) - projH p m j u U (y : ℤ)|} ⊆
      B ∪ ⋃ s, H s := by
    rintro U ⟨hU, y, hy, hybad⟩
    by_cases hbad : U ∈ B
    · exact Or.inl hbad
    have hbnd := RecClockLG.subset_iUnion_recordBand (N := N) p m r L hU
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hbnd
    have hs' := RecClockLG.recTimeA_eq_of_mem_band hU.1 hs
    have hAs : U ∈ A s := by
      change U ∈ recordPrefixBand (N := N) p m r s L
      rwa [← RecClockLG.recordBand_eq_recordPrefixBand p m r L s]
    have hGs : U ∈ G s := by
      intro z hz
      exact M3Hosc.siteGood_of_shift_window hp₀ hp₁ m j (one_le_A0 hL hr)
        (fun k hk => recVal_window hAs hr j (by omega) (by omega))
        (fun y hy => le_of_not_gt (fun hf => hbad ⟨j, y, hy, hf⟩)) hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨s, Set.mem_biUnion hy
      ⟨⟨hAs, hGs⟩, by simpa only [F, hs', Set.mem_ofPred_eq] using hybad⟩⟩)
  have hcap : SiteHMax.capB p m V ≤ 9 * D * V := by
    change D * (2 * V + 7) ≤ 9 * D * V
    nlinarith [mul_le_mul_of_nonneg_left hV hD.le]
  have hcap0 := SiteHMax.capB_pos hp₀ hp₁ m (zero_le_one.trans hV)
  have hVcube : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V, R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hrate : Real.exp (-(ε * (L : ℝ)) ^ 2 / (16 * (w : ℝ) * (SiteHMax.capB p m V) ^ 2))
      ≤ Real.exp (-b * V) := by
    have hw0 : (0 : ℝ) < w := by exact_mod_cast (zero_lt_one.trans_le hw)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hw' : (w : ℝ) = (T : ℝ) * L := Nat.cast_mul _ _
    have hc := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0.le hcap 2)
      (show 0 ≤ (b * V) * (16 * (w : ℝ)) by positivity)
    calc
      _ = (b * V) * (16 * (w : ℝ)) * (SiteHMax.capB p m V) ^ 2 := by ring
      _ ≤ (b * V) * (16 * (w : ℝ)) * (9 * D * V) ^ 2 := hc
      _ = _ := by rw [hw', ← hVcube]; dsimp [b]; field_simp; ring
  have hCard : I.card = Lw T L := by simp [I, Nat.card_Ico]
  have hCard' : (I.card : ℝ) ≤ (2 * (T : ℝ) + 3) * L := by
    rw [hCard, Lw]
    push_cast
    nlinarith
  have hw' : (w : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
    dsimp only [w]
    push_cast
    nlinarith
  have hRpow : V ^ (6 : ℝ) = (L : ℝ) ^ (2 : ℕ) := by
    dsimp only [V, R]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hmart : μ.real (⋃ s, H s) ≤ Real.exp (-(b / 2) * V) := by
    refine hbound.trans ?_
    calc
      _ ≤ ((2 * (T : ℝ) + 3) * L) *
          (2 * (((T : ℝ) + 1) * L) * Real.exp (-b * V)) := by gcongr
      _ = M * (Real.exp (-b * V) * V ^ (6 : ℝ)) := by rw [hRpow]; dsimp only [M]; ring
      _ ≤ _ := by
        change ‖M * (Real.exp (-b * V) * V ^ (6 : ℝ))‖ ≤ 1 * ‖Real.exp (-(b / 2) * V)‖ at hpolyL
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_pos (Real.exp_pos _), one_mul] at hpolyL
        exact hpolyL
  refine (measureReal_mono hcover (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hB hmart).trans ?_))
  have h₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (neg_le_neg (min_le_left a (b / 2))) (zero_le_one.trans hV))
  have h₂ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (neg_le_neg (min_le_right a (b / 2))) (zero_le_one.trans hV))
  calc
    _ ≤ 2 * Real.exp (-k * V) := by linarith
    _ ≤ Real.exp (c * V) * Real.exp (-k * V) :=
      mul_le_mul_of_nonneg_right hlargeL (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [c, V]; ring

end Swarming.Diameter
