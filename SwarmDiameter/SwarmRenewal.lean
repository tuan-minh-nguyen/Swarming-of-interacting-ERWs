import Swarm.BlkMeasure
import Swarm.NeutralTwoInputCapstone
import SwarmDiameter.RegenerationProbability
import SwarmDiameter.PathDiameter
import SwarmDiameter.FirstIntervalOccupation

open Filter Finset MeasureTheory Set
open Swarming.Uniform SwarmRestart SwarmFresh
open RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped ENNReal Topology

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ} [Nonempty (Fin N)]

private theorem pathDiameter_relFuture (U : Array N) (t k : ℕ) (d : ℤ) :
    pathDiameter k (relFuture p m U t d) = pathDiameter (t + k) (posPath p m U) :=
  pathDiameter_shift (posPath p m U) t k d

private theorem real_prob_firstTime_factor {μ : Measure (Array N)} [IsProbabilityMeasure μ]
    (hN : 0 < N) (hD : ∀ᵐ U ∂μ, RegenPath.D (posPath p m U) ≠ ⊤)
    (t k : ℕ) {A : Set ℝ} (hA : MeasurableSet A) (c : ℝ≥0∞)
    (hcell : ∀ q : LevelTime,
      μ (rawFirstCell p m q {X | pathDiameter k X ∈ A}) =
        μ (rawFirstCell p m q Set.univ) * c) :
    μ.real {U | firstTime p m U = t ∧ pathDiameter (t + k) (posPath p m U) ∈ A} =
      μ.real {U | firstTime p m U = t} * c.toReal := by
  refine real_prob_first_regeneration_factor hN hD (fun q => q.1.2) (firstTime (N := N) p m)
    (fun q _ hq => firstTime_eq_of_rawFirstCell p m q hN hq)
    (fun u => pathDiameter u ⁻¹' A) (fun u => measurable_pathDiameter u hA)
    (fun q U _ u => ?_) t k c hcell
  change pathDiameter u (relFuture p m U q.1.2 (q.1.1 : ℤ)) ∈ A ↔
    pathDiameter (q.1.2 + u) (posPath p m U) ∈ A
  rw [pathDiameter_relFuture]

omit [Nonempty (Fin N)] in
private theorem firstTime_pos_of_regen {U : Array N} (hN : 0 < N)
    (hU : RegenPath.D (posPath p m U) ≠ ⊤) : 1 ≤ firstTime p m U := by
  obtain ⟨d, t, hd, hD, ht⟩ := (D_ne_top_iff_exists_firstBlock _).mp hU
  let q : LevelTime := ⟨(d, t), hd⟩
  have hq := (rawFirstCell_univ_iff_D_tau p m q hN U).mpr ⟨hD, ht⟩
  rw [firstTime_eq_of_rawFirstCell p m q hN hq]
  change 1 ≤ t
  by_contra! h
  have ht0 : t = 0 := by omega
  subst t
  obtain ⟨i, hi⟩ := (RegenPath.tau_eq_iff.mp ht).1
  rw [SwarmFresh.posPath_zero] at hi
  omega

/-- The limiting occupation law in equation (4.13). The diameter probabilities
converge under both laws, and the expected visit count in the first interval
bounds the probability of an observation by a fixed time under the conditional law. -/
theorem exists_diameter_occupationLaw (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution Δ atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ A : Set ℝ, MeasurableSet A →
        let visits := ∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A}
        ν.toMeasure.real A = visits / (∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar).toReal ∧
        Tendsto (fun n => μstar.real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) ∧
        Tendsto (fun n => (arrayMeasure N).real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) ∧
        ∀ n : ℕ, μstar.real {U | ∃ t ≤ n, Δ t U ∈ A} ≤ ((n : ℝ) + 1) * visits := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
  change ∃ ν : ProbabilityMeasure ℝ, _
  have hN₀ : 0 < N := by omega
  have hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure hV
  have htight := M4Blk.dT_tight p m hp₀ hp₁ hm N hN
  obtain ⟨π, hπ, hinv⟩ := SwarmDTR.exists_invariant_of_dT_tight hp₀ hp₁
    (by omega : 1 ≤ m) hN₀ htight
  let _ : IsProbabilityMeasure π := hπ
  obtain ⟨hfull, _, hreg, _⟩ :=
    ActualNeutralCapstone.actual_neutral_regenLaw_of_invariant_derived_level hp₀ hp₁ hm hN π hinv
  have hfinite := ae_first_regeneration_finite hp₀ hp₁ hm hN
  have hac : μstar ≪ arrayMeasure N := ProbabilityTheory.cond_absolutelyContinuous
  have hfiniteStar : ∀ᵐ U ∂μstar, RegenPath.D (posPath p m U) ≠ ⊤ := hac.ae_le hfinite
  have htime : Measurable (firstTime (N := N) p m) := measurable_firstTime p m
  have hΔ (n : ℕ) : Measurable (Δ n) := (measurable_pathDiameter n).comp (measurable_posPath p m N)
  let T (U : Array N) := firstTime p m U - 1
  have hT : Measurable T := (measurable_of_countable (fun t : ℕ => t - 1)).comp htime
  have hTeq : (fun U => T U + 1) =ᵐ[μstar] firstTime p m := by
    filter_upwards [hfiniteStar] with U hU
    have ht := firstTime_pos_of_regen hN₀ hU
    change firstTime p m U - 1 + 1 = firstTime p m U
    omega
  have htime_eq : firstTime p m =ᵐ[μstar] NeutralRegen.selectedT p m N 0 := by
    filter_upwards [NeutralRegen.ae_all_chain hN₀ hfull hV] with U hU
    exact (firstRegeneration_eq_selected_zero hN₀ (hU 1)).2
  have hint : Integrable (fun U => ((T U + 1 : ℕ) : ℝ)) μstar := by
    apply (hreg.2.1 0).congr
    filter_upwards [hTeq, htime_eq] with U he he'
    exact congrArg (fun t : ℕ => (t : ℝ)) (he.trans he').symm
  have hfin : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) ≠ ∞ := by
    have h := (hasFiniteIntegral_def _ _).mp hint.hasFiniteIntegral
    simpa only [Real.enorm_natCast] using h.ne
  have hone : 0 < μstar.real {U | T U = 0} := by
    apply (seedCond_first_regeneration_one_pos hN₀ hV).trans_le
    refine measureReal_mono (μ := μstar) ?_ (measure_ne_top μstar _)
    intro U hU
    change firstTime p m U - 1 = 0
    have h : firstTime p m U = 1 := hU.2
    rw [h]
  let ν := CycleOccupation.occupationLaw μstar hT hΔ hfin
  have hstar_factor (A : Set ℝ) (hA : MeasurableSet A) (t k : ℕ) :
      μstar.real {U | T U = t ∧ Δ (t + 1 + k) U ∈ A} =
        μstar.real {U | T U = t} * μstar.real {U | Δ k U ∈ A} := by
    have he (t : ℕ) : {U | T U = t} =ᵐ[μstar] {U | firstTime p m U = t + 1} := by
      filter_upwards [hTeq] with U hU
      apply propext
      change T U + 1 = firstTime p m U at hU
      change T U = t ↔ firstTime p m U = t + 1
      omega
    have heA : {U | T U = t ∧ Δ (t + 1 + k) U ∈ A} =ᵐ[μstar]
        {U | firstTime p m U = t + 1 ∧ Δ (t + 1 + k) U ∈ A} := by
      filter_upwards [he t] with U hh
      exact congrArg (fun b : Prop => b ∧ Δ (t + 1 + k) U ∈ A) hh
    rw [measureReal_congr heA, measureReal_congr (he t)]
    exact real_prob_firstTime_factor hN₀ hfiniteStar (t + 1) k hA (μstar {U | Δ k U ∈ A})
      (fun q => by
        change SwarmFB.seedCond (p := p) (m := m) (N := N)
          (rawFirstCell p m q (pathDiameter k ⁻¹' A)) = _
        rw [seedCond_firstCell_factor hN₀ hV q (measurable_pathDiameter k hA),
          normalizedStrictLaw_eq_seedCond_map,
          Measure.map_apply (measurable_posPath p m N) (measurable_pathDiameter k hA)]
        rfl)
  have hstar (A : Set ℝ) (hA : MeasurableSet A) :
      Tendsto (fun n => μstar.real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) :=
    CycleOccupation.observation_prob_tendsto_of_first_interval hT hΔ hfin hone hA (hstar_factor A hA)
  have hraw (A : Set ℝ) (hA : MeasurableSet A) :
      Tendsto (fun n => (arrayMeasure N).real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) := by
    apply CycleOccupation.observation_prob_tendsto_of_delay htime hΔ hA ?_ (hstar A hA)
    intro t k
    exact real_prob_firstTime_factor hN₀ hfinite t k hA (μstar {U | Δ k U ∈ A})
      (fun q => by
        change arrayMeasure N (rawFirstCell p m q (pathDiameter k ⁻¹' A)) = _
        rw [rawFirstCell_normalized_mass p m N q hV (measure_ne_top _ _) (measurable_pathDiameter k hA),
          normalizedStrictLaw_eq_seedCond_map,
          Measure.map_apply (measurable_posPath p m N) (measurable_pathDiameter k hA)]
        rfl)
  have hcount (A : Set ℝ) :
      (∑' t : ℕ, μstar.real {U | t ≤ T U ∧ Δ t U ∈ A}) =
        ∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A} := by
    apply tsum_congr
    intro t
    apply measureReal_congr
    filter_upwards [hTeq] with U he
    apply propext
    change T U + 1 = firstTime p m U at he
    change (t ≤ T U ∧ Δ t U ∈ A) ↔ (t < firstTime p m U ∧ Δ t U ∈ A)
    exact and_congr (by omega) Iff.rfl
  have hformula (A : Set ℝ) (hA : MeasurableSet A) :
      ν.toMeasure.real A =
        (∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A}) /
          (∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar).toReal := by
    change (CycleOccupation.occupationLaw μstar hT hΔ hfin).toMeasure.real A = _
    rw [CycleOccupation.occupationLaw_real_apply μstar hT hΔ hfin hA]
    have hI : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) =
        ∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar :=
      lintegral_congr_ae (hTeq.mono (fun _ he => congrArg (fun n : ℕ => (n : ℝ≥0∞)) he))
    rw [hI, hcount]
  have hmax (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
      μstar.real {U | ∃ t ≤ n, Δ t U ∈ A} ≤ ((n : ℝ) + 1) *
        ∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A} := by
    rw [← hcount]
    exact CycleOccupation.observation_exceeds_before_prob_le_occupation hT hΔ hfin hA (hstar_factor A hA) n
  have hnonneg : ∀ᵐ x ∂ν.toMeasure, 0 ≤ x := by
    rw [ae_iff]
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    have hneg : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by
      ext x
      exact not_le
    rw [hneg, hformula _ measurableSet_Iio]
    have hzero (t : ℕ) : {U : Array N | t < firstTime p m U ∧ Δ t U ∈ Set.Iio 0} = ∅ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => (not_lt_of_ge (pathDiameter_nonneg t (posPath p m U))) h.2
    simp only [hzero, measureReal_empty, tsum_zero, zero_div]
  exact ⟨ν, hnonneg, CycleOccupation.tendstoInDistribution_of_observation_prob_tendsto hΔ hraw,
    fun A hA => ⟨hformula A hA, hstar A hA, hraw A hA, hmax A hA⟩⟩

end Swarming.Diameter
