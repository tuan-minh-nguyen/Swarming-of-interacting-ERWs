import SwarmDiameter.FirstIntervalOccupation
import SwarmDiameter.RecordIntervals
import SwarmDiameter.RegenerationProbability

open Filter MeasureTheory Set
open Swarming.Uniform SwarmRestart SwarmFresh
open RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]

/-- The occupation identity at successive record levels. The event at each
level is measurable and is preserved by translating at a simultaneous record. -/
theorem tendsto_record_event_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (A : ℕ → Set (RegenPath.Path N)) (hA : ∀ r, MeasurableSet (A r))
    (hshift : ∀ {X : RegenPath.Path N} {t d : ℕ}, SwarmChain.pathRec t (d : ℤ) X →
      ∀ r, SwarmChain.pathRel t (d : ℤ) X ∈ A r ↔ X ∈ A (d + r)) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let b := ∫⁻ U, (D U : ℝ≥0∞) ∂μstar
    0 < b.toReal ∧ b ≠ ∞ ∧
      Tendsto (fun r => (arrayMeasure N).real {U | posPath p m U ∈ A r}) atTop
        (𝓝 ((∑' r : ℕ, μstar.real {U | r < D U ∧ posPath p m U ∈ A r}) / b.toReal)) := by
  classical
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let D := firstLevel (N := N) p m
  let T (U : Array N) := D U - 1
  let Z (r : ℕ) (U : Array N) : Bool := if posPath p m U ∈ A r then true else false
  let B : Set Bool := {true}
  have hZB (r : ℕ) (U : Array N) : Z r U ∈ B ↔ posPath p m U ∈ A r := by
    by_cases h : posPath p m U ∈ A r <;> simp [Z, B, h]
  have hZ (r : ℕ) : Measurable (Z r) :=
    Measurable.ite (hA r |>.preimage (measurable_posPath p m N)) measurable_const measurable_const
  have hB : MeasurableSet B := measurableSet_singleton true
  have hN₀ : 0 < N := by omega
  have hV := SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure hV
  have hfinite := ae_first_regeneration_finite hp₀ hp₁ hm hN
  have hac : μstar ≪ arrayMeasure N := ProbabilityTheory.cond_absolutelyContinuous
  have hfiniteStar := hac.ae_le hfinite
  have hD : Measurable D := measurable_firstLevel p m
  have hT : Measurable T := (measurable_of_countable (fun d : ℕ => d - 1)).comp hD
  have hTeq : (fun U => T U + 1) =ᵐ[μstar] D := by
    filter_upwards [hfiniteStar] with U hU
    obtain ⟨d, t, hd, hD', ht⟩ := (D_ne_top_iff_exists_firstBlock _).mp hU
    let q : LevelTime := ⟨(d, t), hd⟩
    have hcell := (rawFirstCell_univ_iff_D_tau p m q hN₀ U).mpr ⟨hD', ht⟩
    have he : D U = d := firstLevel_eq_of_rawFirstCell p m q hN₀ hcell
    change D U - 1 + 1 = D U
    omega
  have hone : 0 < μstar.real {U | T U = 0} := by
    apply (seedCond_first_regeneration_one_pos hN₀ hV).trans_le
    apply measureReal_mono (μ := μstar) ?_ (measure_ne_top μstar _)
    intro U hU
    have h : D U = 1 := hU.1
    change D U - 1 = 0
    rw [h]
  have htight := M4Blk.dT_tight p m hp₀ hp₁ hm N hN
  obtain ⟨π, hπ, hinv⟩ := SwarmDTR.exists_invariant_of_dT_tight hp₀ hp₁
    (by omega : 1 ≤ m) hN₀ htight
  let _ : IsProbabilityMeasure π := hπ
  obtain ⟨hfull, _, hreg, _⟩ :=
    ActualNeutralCapstone.actual_neutral_regenLaw_of_invariant_derived_level hp₀ hp₁ hm hN π hinv
  have hD_eq : D =ᵐ[μstar] NeutralRegen.selectedD p m N 0 := by
    filter_upwards [NeutralRegen.ae_all_chain hN₀ hfull hV] with U hU
    exact (firstRegeneration_eq_selected_zero hN₀ (hU 1)).1
  have hint : Integrable (fun U => ((T U + 1 : ℕ) : ℝ)) μstar := by
    apply (hreg.1 0).congr
    filter_upwards [hTeq, hD_eq] with U he he'
    exact congrArg (fun t : ℕ => (t : ℝ)) (he.trans he').symm
  have hfin : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) ≠ ∞ := by
    have h := (hasFiniteIntegral_def _ _).mp hint.hasFiniteIntegral
    simpa only [Real.enorm_natCast] using h.ne
  have hI : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) = ∫⁻ U, (D U : ℝ≥0∞) ∂μstar :=
    lintegral_congr_ae (hTeq.mono (fun _ he => congrArg (fun n : ℕ => (n : ℝ≥0∞)) he))
  have hpos : (1 : ℝ≥0∞) ≤ ∫⁻ U, (D U : ℝ≥0∞) ∂μstar := by
    rw [← hI]
    calc
      1 = ∫⁻ _ : Array N, (1 : ℝ≥0∞) ∂μstar := by simp
      _ ≤ _ := lintegral_mono (fun U => by simp)
  have hrel (q : LevelTime) (U : Array N) (hq : U ∈ rawFirstCell p m q Set.univ) (r : ℕ) :
      relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ A r ↔ posPath p m U ∈ A (q.1.1 + r) := by
    rw [SwarmChain.pathRel_relFuture]
    exact hshift ((mem_rawFirstCell p m q Set.univ U).mp hq).1.1 r
  have hnormalized (r : ℕ) :
      normalizedStrictLaw p m N (A r) = μstar {U | posPath p m U ∈ A r} := by
    rw [normalizedStrictLaw_eq_seedCond_map,
      Measure.map_apply (measurable_posPath p m N) (hA r)]
    rfl
  have hstar_factor (t r : ℕ) :
      μstar.real {U | D U = t ∧ posPath p m U ∈ A (t + r)} =
        μstar.real {U | D U = t} * μstar.real {U | posPath p m U ∈ A r} := by
    apply real_prob_first_regeneration_factor hN₀ hfiniteStar (fun q => q.1.1) D
      (fun q _ hq => firstLevel_eq_of_rawFirstCell p m q hN₀ hq) A hA hrel t r
      (μstar {U | posPath p m U ∈ A r})
    intro q
    change SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q (A r)) = _
    rw [seedCond_firstCell_factor hN₀ hV q (hA r), hnormalized]
  have hraw_factor (t r : ℕ) :
      (arrayMeasure N).real {U | D U = t ∧ posPath p m U ∈ A (t + r)} =
        (arrayMeasure N).real {U | D U = t} * μstar.real {U | posPath p m U ∈ A r} := by
    apply real_prob_first_regeneration_factor hN₀ hfinite (fun q => q.1.1) D
      (fun q _ hq => firstLevel_eq_of_rawFirstCell p m q hN₀ hq) A hA hrel t r
      (μstar {U | posPath p m U ∈ A r})
    intro q
    rw [rawFirstCell_normalized_mass p m N q hV (measure_ne_top _ _) (hA r), hnormalized]
  let ν := CycleOccupation.occupationLaw μstar hT hZ hfin
  have hstar : Tendsto (fun r => μstar.real {U | Z r U ∈ B}) atTop (𝓝 (ν.toMeasure.real B)) := by
    apply CycleOccupation.observation_prob_tendsto_of_first_interval hT hZ hfin hone hB
    intro t r
    have he : {U | T U = t} =ᵐ[μstar] {U | D U = t + 1} := by
      filter_upwards [hTeq] with U hU
      apply propext
      change T U + 1 = D U at hU
      change T U = t ↔ D U = t + 1
      omega
    have he' : {U | T U = t ∧ Z (t + 1 + r) U ∈ B} =ᵐ[μstar]
        {U | D U = t + 1 ∧ Z (t + 1 + r) U ∈ B} := by
      filter_upwards [he] with U hU
      exact congrArg (fun b : Prop => b ∧ Z (t + 1 + r) U ∈ B) hU
    rw [measureReal_congr he', measureReal_congr he]
    simpa only [hZB] using hstar_factor (t + 1) r
  have hraw : Tendsto (fun r => (arrayMeasure N).real {U | Z r U ∈ B}) atTop (𝓝 (ν.toMeasure.real B)) := by
    apply CycleOccupation.observation_prob_tendsto_of_delay hD hZ hB ?_ hstar
    intro t r
    simpa only [hZB] using hraw_factor t r
  have hformula : ν.toMeasure.real B =
      (∑' r : ℕ, μstar.real {U | r < D U ∧ posPath p m U ∈ A r}) /
        (∫⁻ U, (D U : ℝ≥0∞) ∂μstar).toReal := by
    change (CycleOccupation.occupationLaw μstar hT hZ hfin).toMeasure.real B = _
    rw [CycleOccupation.occupationLaw_real_apply μstar hT hZ hfin hB, hI]
    congr 1
    apply tsum_congr
    intro r
    apply measureReal_congr
    filter_upwards [hTeq] with U hU
    apply propext
    change T U + 1 = D U at hU
    change r ≤ T U ∧ Z r U ∈ B ↔ r < D U ∧ posPath p m U ∈ A r
    exact and_congr (by omega) (hZB r U)
  rw [hI] at hfin
  refine ⟨ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hpos)) hfin, hfin, ?_⟩
  rw [hformula] at hraw
  simpa only [hZB] using hraw

/-- Apply the record occupation identity to an exceedance of the diameter. -/
theorem tendsto_record_interval_exceedance_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (x : ℝ) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let b := ∫⁻ U, (D U : ℝ≥0∞) ∂μstar
    0 < b.toReal ∧ b ≠ ∞ ∧
      Tendsto (fun r => (arrayMeasure N).real {U | recordIntervalExceeds (posPath p m U) r x}) atTop
        (𝓝 ((∑' r : ℕ, μstar.real {U | r < D U ∧ recordIntervalExceeds (posPath p m U) r x}) / b.toReal)) :=
  tendsto_record_event_occupation hp₀ hp₁ hm hN
    (fun r => {X | recordIntervalExceeds X r x}) (fun r => measurableSet_recordIntervalExceeds r x)
    (fun hr r => recordIntervalExceeds_pathRel_iff hr r x)

/-- Apply the record occupation identity to a duration exceeding `u`. -/
theorem tendsto_record_duration_tail_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (u : ℕ) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let b := ∫⁻ U, (D U : ℝ≥0∞) ∂μstar
    0 < b.toReal ∧ b ≠ ∞ ∧
      Tendsto (fun r => (arrayMeasure N).real {U | (u : ℕ∞) < recordDuration (posPath p m U) r}) atTop
        (𝓝 ((∑' r : ℕ, μstar.real {U | r < D U ∧ (u : ℕ∞) < recordDuration (posPath p m U) r}) /
          b.toReal)) :=
  tendsto_record_event_occupation hp₀ hp₁ hm hN
    (fun r => {X | (u : ℕ∞) < recordDuration X r})
    (fun r => measurable_recordDuration r (MeasurableSet.of_discrete (s := Set.Ioi (u : ℕ∞))))
    (fun hr r => by simp only [Set.mem_ofPred_eq, recordDuration_pathRel hr r])

end Swarming.Diameter
