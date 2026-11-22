import SwarmDiameter.MarkedSpatialTail
import Swarm.LocOccCarrierAssembly
import Swarm.RecClockLocgroup

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl Swarming.Trajectory SwarmRecordMeas.Actual SwarmMarks
open ActualRecordFiltration LocOccCarrierAssembly ShiftedQplResidual ShiftedAdvance
open QplWindow QplPredEnv
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem measureReal_iUnion_le_of_weight_and_residual {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A E : ℕ → Set Ω} {B : Set Ω} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ s, MeasurableSet (A s)) (hB : MeasurableSet B)
    (hd : Pairwise fun s t => Disjoint (A s) (A t))
    (h : ∀ s, μ.real (E s) ≤ c * μ.real (A s) + μ.real (A s ∩ B)) :
    μ.real (⋃ s, E s) ≤ c + μ.real B := by
  have hh (s : ℕ) : μ (E s) ≤ ENNReal.ofReal c * μ (A s) + μ (A s ∩ B) := by
    have h₁ := ENNReal.ofReal_le_ofReal (h s)
    rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_add (mul_nonneg hc measureReal_nonneg) measureReal_nonneg,
      ENNReal.ofReal_mul hc, measureReal_def, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at h₁
  have hsum : (∑' s, μ (A s)) ≤ 1 := by
    rw [← measure_iUnion hd hA, ← measure_univ (μ := μ)]
    exact measure_mono (subset_univ _)
  have hds : Pairwise fun s t => Disjoint (A s ∩ B) (A t ∩ B) :=
    fun s t hst => (hd hst).mono inter_subset_left inter_subset_left
  have hsumb : (∑' s, μ (A s ∩ B)) ≤ μ B := by
    rw [← measure_iUnion hds (fun s => (hA s).inter hB)]
    exact measure_mono (iUnion_subset fun _ => inter_subset_right)
  have bound : μ (⋃ s, E s) ≤ ENNReal.ofReal c + μ B := by
    calc
      _ ≤ ∑' s, μ (E s) := measure_iUnion_le _
      _ ≤ (∑' s, (ENNReal.ofReal c * μ (A s) + μ (A s ∩ B))) := ENNReal.tsum_le_tsum hh
      _ = ENNReal.ofReal c * (∑' s, μ (A s)) + (∑' s, μ (A s ∩ B)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal c * 1 + μ B := add_le_add (mul_le_mul_right hsum _) hsumb
      _ = _ := by rw [mul_one]
  have hfin : ENNReal.ofReal c + μ B ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top μ B⟩
  simpa only [measureReal_def, ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top μ B),
    ENNReal.toReal_ofReal hc] using ENNReal.toReal_mono hfin bound

/-- At a simultaneous record of width at most `L`, the occupation martingale
has a maximal deviation of order `ε * L` with exceptional probability
at most `exp (-c * L ^ (1 / 3))` over the next `T * L` steps. -/
theorem record_Qpl_maximal_deviation_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ i j : Fin N,
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ k ≤ T * L, ε * (L : ℝ) ≤
            |ProjLedger.Qpl p m α i j (recTimeA p m U r + k) U -
              ProjLedger.Qpl p m α i j (recTimeA p m U r) U|})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  obtain ⟨a, ha, hspatial⟩ := hlocal N (2 * T + 4) (show (0 : ℝ) < 1 by norm_num)
  let D := KepW p m
  have hD : 0 < D := KepW_pos hp₀ hp₁ m
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let b := ε ^ 2 / (36 * (T : ℝ) * D ^ 2)
  have hT₀ : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
  have hb : 0 < b := by dsimp only [b]; positivity
  let c := min a (b / 2) / 2
  have hc : 0 < c := half_pos (lt_min ha (half_pos hb))
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  let M : ℝ := 2 * ((T : ℝ) + 1)
  have hpoly := ((isLittleO_exp_mul_rpow_of_lt 3 (show -b < -(b / 2) by linarith)).const_mul_left M).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (Real.tendsto_exp_atTop.comp (htop.const_mul_atTop hc)).eventually_ge_atTop 2
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspatial, htop.eventually hpoly, hlarge]
    with L hL hsp hpolyL hlargeL
  intro r hr i j
  let μ := arrayMeasure N
  let V := R L
  let w := A0 r T L
  let W := Lw T L + 1
  let n := T * L
  let A (s : ℕ) := recordPrefixBand (N := N) p m r s L
  let Q := ProjLedger.Qpl p m α i j
  let B := harmDefect p m j V w W
  let E (s : ℕ) := A s ∩ OscStartCell Q (fun _ => s) n (ε * (L : ℝ)) s
  let K := 2 * ((n : ℝ) + 1) *
    Real.exp (-(ε * (L : ℝ)) ^ 2 / (4 * (n : ℝ) * (envB p m V (envC p m V)) ^ 2))
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hV : 1 ≤ V := Real.one_le_rpow hLr (by norm_num)
  have hn : 1 ≤ n := Nat.mul_le_mul hT hL
  have hw := one_le_A0 hL hr
  have hδ : 0 < ε * (L : ℝ) := mul_pos hε (zero_lt_one.trans_le hLr)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : μ.real B ≤ Real.exp (-a * V) := by
    refine (measureReal_mono ?_ (measure_ne_top μ _)).trans (hsp (w - 1))
    intro U hU
    change ¬ ∀ y ∈ Finset.Ico (w - 1) (w + W),
      hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V at hU
    push Not at hU
    obtain ⟨y, hy, hf⟩ := hU
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Ico.mp hy
    refine Or.inl ⟨j, y - (w - 1), ?_, ?_⟩
    · have he : (2 * T + 4) * L = (2 * T + 2) * L + 2 * L := by ring
      dsimp only [W, Lw] at hy₂
      omega
    · rw [Nat.add_sub_of_le hy₁]
      exact hf
  have hBm : MeasurableSet B := by
    change MeasurableSet ({U : Array N | ∀ y ∈ Finset.Ico (w - 1) (w + W),
      hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V}ᶜ)
    refine MeasurableSet.compl ?_
    have he : {U : Array N | ∀ y ∈ Finset.Ico (w - 1) (w + W),
        hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V} =
        ⋂ y ∈ Finset.Ico (w - 1) (w + W),
          {U : Array N | hof p (SwarmLogRatio.siteMarks p m U j) y ≤ V} := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [he]
    refine Finset.measurableSet_biInter _ fun y _ => ?_
    exact ((measurable_hof (ne_of_gt (show 0 < p by linarith)) y).comp
      (SwarmLogRatio.measurePreserving_siteMarks (show 0 < p by linarith) hp₁ m j).measurable)
        measurableSet_Iic
  have hE (s : ℕ) : μ.real (E s) ≤ K * μ.real (A s) + μ.real (A s ∩ B) := by
    have h := measureReal_qpl_oscStartCell_le_shifted_window
      hp₀ hp₁ m α i j hα (τ := fun _ : Array N => s)
      (measurableSet_recordPrefixBand p m r s L) (by simp)
      hV (w := w) (M := W) hw hn hδ
    have hgeom : A s ∩ shiftedContDefect p m i j s w W n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro U ⟨hU, hbad⟩
      rcases hbad with ⟨k, hk, hbad⟩ | ⟨k, hk, hbad⟩
      · exact hbad (by
          obtain ⟨hlo, hhi⟩ := recVal_window hU hr j (show s ≤ s + k by omega)
            (show s + k ≤ s + T * L by omega)
          constructor <;> omega)
      · exact hbad (by
          obtain ⟨hlo, hhi, -⟩ := carrier_cell_window hU hr i j (show s ≤ s + k by omega)
            (show s + k ≤ s + T * L by omega)
          change (w : ℤ) ≤ (trajectory p m U (s + k)).pos i at hlo
          change (trajectory p m U (s + k)).pos i < (w : ℤ) + (Lw T L : ℤ) at hhi
          dsimp only [W]
          constructor <;> omega)
    simpa only [E, Q, A, K, B, Set.ofPred_true, Set.inter_univ, hgeom, measureReal_empty,
      zero_add, mul_comm] using h
  have hbound : μ.real (⋃ s, E s) ≤ K + μ.real B := by
    refine measureReal_iUnion_le_of_weight_and_residual hK
      (fun s => (enlFilt p m).le s _ (measurableSet_recordPrefixBand p m r s L)) hBm ?_ hE
    intro s t hst
    rw [← RecClockLG.recordBand_eq_recordPrefixBand p m r L s,
      ← RecClockLG.recordBand_eq_recordPrefixBand p m r L t]
    exact RecClockLG.disjoint_recordBand hst
  have hcover : RecClockLG.recordCarrier p m r L ∩ {U |
      ∃ k ≤ n, ε * (L : ℝ) ≤ |Q (recTimeA p m U r + k) U - Q (recTimeA p m U r) U|} ⊆
      ⋃ s, E s := by
    rintro U ⟨hU, k, hk, hdev⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (RecClockLG.subset_iUnion_recordBand p m r L hU)
    have hs' := RecClockLG.recTimeA_eq_of_mem_band hU.1 hs
    refine Set.mem_iUnion.mpr ⟨s, ?_, rfl, k, hk, ?_⟩
    · change U ∈ recordPrefixBand (N := N) p m r s L
      rwa [← RecClockLG.recordBand_eq_recordPrefixBand p m r L s]
    · rwa [hs'] at hdev
  have henv : envB p m V (envC p m V) ≤ 3 * D * V := by
    refine (envB_envC_le_kepW hp₀ hp₁ m hV).trans ?_
    calc
      D * (V + 2) ≤ D * (3 * V) := mul_le_mul_of_nonneg_left (by linarith) hD.le
      _ = _ := by ring
  have hV₀ : 0 ≤ V := zero_le_one.trans hV
  have henv₀ := envB_pos hp₀ hp₁ m hV₀ (envC_nonneg hp₀ hp₁ m hV₀)
  have hVcube : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V, R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hrate :
      Real.exp (-(ε * (L : ℝ)) ^ 2 / (4 * (n : ℝ) * (envB p m V (envC p m V)) ^ 2))
        ≤ Real.exp (-b * V) := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ henv₀.le henv 2)
      (show 0 ≤ (b * V) * (4 * (n : ℝ)) by positivity)
    calc
      _ = (b * V) * (4 * (n : ℝ)) * (envB p m V (envC p m V)) ^ 2 := by ring
      _ ≤ (b * V) * (4 * (n : ℝ)) * (3 * D * V) ^ 2 := he
      _ = _ := by rw [show (n : ℝ) = (T : ℝ) * L from Nat.cast_mul _ _, ← hVcube]
                  dsimp only [b]
                  field_simp
                  ring
  have hn' : (n : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
    dsimp only [n]
    push_cast
    linarith
  have hmart : K ≤ Real.exp (-(b / 2) * V) := by
    calc
      K ≤ M * (Real.exp (-b * V) * (L : ℝ)) := by
        calc
          _ ≤ (2 * (((T : ℝ) + 1) * L)) * Real.exp (-b * V) := by
            dsimp only [K]
            gcongr
          _ = _ := by dsimp only [M]; ring
      _ ≤ _ := by
        change ‖M * (Real.exp (-b * V) * V ^ (3 : ℝ))‖ ≤ 1 * ‖Real.exp (-(b / 2) * V)‖ at hpolyL
        rw [Real.rpow_ofNat, hVcube, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _), one_mul] at hpolyL
        exact hpolyL
  refine (measureReal_mono hcover (measure_ne_top μ _)).trans (hbound.trans
    ((add_le_add hmart hB).trans ?_))
  have h₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (neg_le_neg (min_le_left a (b / 2))) hV₀)
  have h₂ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (neg_le_neg (min_le_right a (b / 2))) hV₀)
  calc
    _ ≤ 2 * Real.exp (-(min a (b / 2)) * V) := by linarith
    _ ≤ Real.exp (c * V) * Real.exp (-(min a (b / 2)) * V) :=
      mul_le_mul_of_nonneg_right hlargeL (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [c, V]; ring

/-- The same probability bound for differences between any two times in the
record interval. -/
theorem record_Qpl_oscillation_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ i j : Fin N,
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
            ε * (L : ℝ) ≤ |ProjLedger.Qpl p m α i j t U - ProjLedger.Qpl p m α i j s U|})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨c, hc, h⟩ := record_Qpl_maximal_deviation_le_cube_root hp₀ hp₁ hm N T hT hα (half_pos hε)
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with L hL
  intro r hr i j
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hL r hr i j)
  rintro U ⟨hU, s, t, hs, hst, ht, hdev⟩
  refine ⟨hU, ?_⟩
  let σ := recTimeA p m U r
  let Q := ProjLedger.Qpl p m α i j
  change ∃ k ≤ T * L, ε / 2 * (L : ℝ) ≤ |Q (σ + k) U - Q σ U|
  change σ ≤ s at hs
  change t ≤ σ + T * L at ht
  by_contra! hsmall
  have h₁ := hsmall (s - σ) (by omega)
  have h₂ := hsmall (t - σ) (by omega)
  rw [Nat.add_sub_cancel' hs] at h₁
  rw [Nat.add_sub_cancel' (hs.trans hst)] at h₂
  apply (not_lt_of_ge hdev)
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp h₁).2, (abs_lt.mp h₂).1],
    by linarith [(abs_lt.mp h₁).1, (abs_lt.mp h₂).2]⟩

end Swarming.Diameter
