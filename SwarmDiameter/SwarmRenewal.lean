import Swarm.BlkMeasure
import Swarm.NeutralTwoInputCapstone
import Swarm.RawInitialPathLaw
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

private theorem rawFirstCell_with_diameter (q : LevelTime) (k : ℕ) (A : Set ℝ) :
    rawFirstCell (N := N) p m q {X | pathDiameter k X ∈ A} =
      rawFirstCell p m q Set.univ ∩ {U | pathDiameter (q.1.2 + k) (posPath p m U) ∈ A} := by
  ext U
  rw [Set.mem_inter_iff, mem_rawFirstCell p m q _ U, mem_rawFirstCell p m q _ U]
  simp only [Set.mem_univ, and_true, Set.mem_ofPred_eq, pathDiameter_relFuture, and_assoc]

private theorem rawFirstCell_inter_seed (q : LevelTime) (hN : 0 < N)
    (B : Set (ℕ → Fin N → ℤ)) :
    SwarmFB.seedSet (p := p) (m := m) (N := N) ∩ rawFirstCell p m q B =
      FirstBlockFuture p m q B := by
  ext U
  have h : U ∈ rawFirstCell (N := N) p m q B ↔
      U ∈ rawFirstCell p m q Set.univ ∧ relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ B := by
    rw [mem_rawFirstCell p m q B U, mem_rawFirstCell p m q Set.univ U]
    simp only [Set.mem_univ, and_true, and_assoc]
  rw [Set.mem_inter_iff, h, rawFirstCell_univ_iff_D_tau p m q hN U] <;> rfl

private theorem real_prob_firstTime_factor {μ : Measure (Array N)} [IsProbabilityMeasure μ]
    (hN : 0 < N) (hD : ∀ᵐ U ∂μ, RegenPath.D (posPath p m U) ≠ ⊤)
    (t k : ℕ) {A : Set ℝ} (hA : MeasurableSet A) (c : ℝ≥0∞)
    (hcell : ∀ q : LevelTime,
      μ (rawFirstCell p m q {X | pathDiameter k X ∈ A}) =
        μ (rawFirstCell p m q Set.univ) * c) :
    μ.real {U | firstTime p m U = t ∧ pathDiameter (t + k) (posPath p m U) ∈ A} =
      μ.real {U | firstTime p m U = t} * c.toReal := by
  let q (d : {d : ℕ // 1 ≤ d}) : LevelTime := ⟨(d.1, t), d.2⟩
  let S (d : {d : ℕ // 1 ≤ d}) : Set (Array N) := rawFirstCell p m (q d) Set.univ
  let B : Set (ℕ → Fin N → ℤ) := {X | pathDiameter k X ∈ A}
  let R (d : {d : ℕ // 1 ≤ d}) : Set (Array N) := rawFirstCell p m (q d) B
  have hS : {U : Array N | firstTime p m U = t} =ᵐ[μ] ⋃ d, S d := by
    filter_upwards [hD] with U hU
    apply propext
    change firstTime p m U = t ↔ U ∈ ⋃ d, S d
    constructor
    · intro ht
      obtain ⟨d, u, hd, he, hu⟩ := (D_ne_top_iff_exists_firstBlock _).mp hU
      let r : LevelTime := ⟨(d, u), hd⟩
      have hc : U ∈ rawFirstCell p m r Set.univ :=
        (rawFirstCell_univ_iff_D_tau p m r hN U).mpr ⟨he, hu⟩
      have htu := (firstTime_eq_of_rawFirstCell p m r hN hc).symm.trans ht
      change u = t at htu
      subst u
      exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, hc⟩
    · intro hh
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hh
      exact firstTime_eq_of_rawFirstCell p m (q d) hN hd
  have hR : {U : Array N | firstTime p m U = t ∧ pathDiameter (t + k) (posPath p m U) ∈ A}
      =ᵐ[μ] ⋃ d, R d := by
    filter_upwards [hS] with U hU
    apply propext
    change ((U ∈ {V : Array N | firstTime p m V = t}) ∧
      pathDiameter (t + k) (posPath p m U) ∈ A) ↔ U ∈ ⋃ d, R d
    rw [hU]
    simp only [Set.mem_iUnion, R, rawFirstCell_with_diameter, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    change ((∃ d, U ∈ S d) ∧ pathDiameter (t + k) (posPath p m U) ∈ A) ↔
      ∃ d, U ∈ S d ∧ pathDiameter (t + k) (posPath p m U) ∈ A
    constructor
    · rintro ⟨⟨d, hd⟩, hA⟩
      exact ⟨d, hd, hA⟩
    · rintro ⟨d, hd, hA⟩
      exact ⟨⟨d, hd⟩, hA⟩
  have hinj : Function.Injective q := by
    intro x y h
    exact Subtype.ext (congrArg (fun r : LevelTime => r.1.1) h)
  have hsdisj : Pairwise fun d e => Disjoint (S d) (S e) := fun _ _ hne =>
    pairwise_disjoint_rawFirstCell p m Set.univ hN (fun he => hne (hinj he))
  have hrdisj : Pairwise fun d e => Disjoint (R d) (R e) := fun _ _ hne =>
    pairwise_disjoint_rawFirstCell p m B hN (fun he => hne (hinj he))
  rw [measureReal_congr hS, measureReal_congr hR]
  rw [measureReal_def, measureReal_def,
    measure_iUnion hsdisj (fun d => measurableSet_rawFirstCell p m (q d) MeasurableSet.univ),
    measure_iUnion hrdisj (fun d => measurableSet_rawFirstCell p m (q d)
      (measurable_pathDiameter k hA))]
  have hf (d : {d : ℕ // 1 ≤ d}) : μ (R d) = μ (S d) * c := hcell (q d)
  simp only [hf, ENNReal.tsum_mul_right, ENNReal.toReal_mul]

private theorem seedCond_firstCell_factor (hN : 0 < N)
    (hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0)
    (q : LevelTime) {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q B) =
      SwarmFB.seedCond (p := p) (m := m) (N := N) (rawFirstCell p m q univ) *
        normalizedStrictLaw p m N B := by
  let ν := SwarmFB.seedCond (p := p) (m := m) (N := N)
  letI : IsProbabilityMeasure ν := SwarmFB.seedCond_isProbabilityMeasure hV
  have hf (A : Set (ℕ → Fin N → ℤ)) (hA : MeasurableSet A) :
      ν (rawFirstCell p m q A) =
        firstBlockLowMass (N := N) p m q * normalizedStrictLaw p m N A := by
    change SwarmFB.seedCond (rawFirstCell p m q A) = _
    rw [SwarmFB.seedCond_apply SwarmFB.measurableSet_seedSet, rawFirstCell_inter_seed q hN,
      FirstBlockFuture, SwarmRawTimeStrict.array_firstBlock_future_mass p m q.1.1 q.1.2 q.2 hA,
      normalizedStrictLaw_apply p m N hA]
    exact mul_left_comm _ _ _
  have hu := hf Set.univ MeasurableSet.univ
  rw [normalizedStrictLaw_eq_seedCond_map, Measure.map_apply (measurable_posPath p m N)
    MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one] at hu
  change ν (rawFirstCell p m q B) = ν (rawFirstCell p m q Set.univ) * _
  rw [hf B hB, hu]

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

private theorem firstTime_eq_selectedT_zero (hN : 0 < N) {U : Array N}
    (hU : U ∈ SwarmSelInd.Achain p m N 1 Set.univ) :
    firstTime p m U = NeutralRegen.selectedT p m N 0 U := by
  have hU' : U ∈ ⋃ L : Fin 1 → ℕ × ℕ, SwarmFB.Atom (p := p) (m := m) (N := N) L := by
    rwa [SwarmFB.iUnion_atom_eq]
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hU'
  have hZ : SwarmFB.Z (p := p) (m := m) (N := N) 0 U = L 0 := by
    simpa using SwarmFB.Z_eq_of_mem_atom (p := p) (m := m) (N := N) hN L hL 0
  rw [NeutralRegen.selectedT_eq_raw hN p m 0 hU, hZ]
  have hlist : SwarmFB.idxList L = [((L 0).1, SwarmFB.blkLevel (L 0))] := by
    simp [SwarmFB.idxList, List.ofFn_succ]
  rw [SwarmFB.Atom, hlist, SwarmSelInd.AchainIdx] at hL
  have hfr := (SwarmSelInd.mem_Hidx_cons.mp hL).2.1
  have hfr' : posPath p m U ∈ SwarmSel.firstRegen (L 0).1 (((L 0).2 + 1 : ℕ) : ℤ) := by
    simpa [SwarmFB.blkLevel, Nat.cast_add, Nat.cast_one] using hfr
  have hlevel := BlockLevelKac.firstRegenLevel_eq_of_firstRegen (posPath p m U)
    (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U)
    (t := (L 0).1) (d := (L 0).2 + 1) (by omega) hfr'
  have hrec := (SwarmSel.mem_firstRegen_iff.mp hfr').2.1
  have htau : RegenPath.tau (posPath p m U) (((L 0).2 + 1 : ℕ) : ℤ) =
      ((L 0).1 : ℕ∞) := RegenPath.tau_eq_iff.mpr
    ⟨⟨⟨0, hN⟩, hrec.2 _⟩, fun n hn i => ne_of_lt (hrec.1 n hn i)⟩
  unfold firstTime firstTau firstLevel
  rw [hlevel, htau]
  simp

private theorem seedCond_firstTime_eq_one_pos (hN : 0 < N)
    (hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0) :
    0 < (SwarmFB.seedCond (p := p) (m := m) (N := N)).real {U | firstTime p m U = 1} := by
  let ν := SwarmFB.seedCond (p := p) (m := m) (N := N)
  letI : IsProbabilityMeasure ν := SwarmFB.seedCond_isProbabilityMeasure hV
  let q : LevelTime := ⟨(1, 1), by omega⟩
  have hC : SwarmFB.seedSet (p := p) (m := m) (N := N) ⊆
      {U | RegenPath.Cdt (posPath p m U) 1 1} := by
    intro U hU
    have hpos : posPath p m U ∈ strictPos := hU
    have hone (i : Fin N) : posPath p m U 1 i = 1 := by
      have hs := SwarmFresh.posPath_step p m U 0 i
      rw [SwarmFresh.posPath_zero p m U i, sub_zero] at hs
      rwa [abs_of_pos (hpos.2 0 i)] at hs
    refine ⟨RegenPath.tau_eq_iff.mpr ⟨⟨⟨0, hN⟩, hone _⟩, ?_⟩, hone, ?_, ?_⟩
    · intro n hn i
      have hn' : n = 0 := by omega
      simp [hn', SwarmFresh.posPath_zero p m U i]
    · intro n hn ht i
      have hn' : n = 1 := by omega
      rw [hn', hone]
      decide
    · intro e he he'
      omega
  have hlow : 0 < firstBlockLowMass (N := N) p m q :=
    (pos_iff_ne_zero.mpr hV).trans_le (measure_mono hC)
  have hcell : ν (rawFirstCell p m q Set.univ) = firstBlockLowMass (N := N) p m q := by
    change SwarmFB.seedCond (rawFirstCell p m q Set.univ) = _
    rw [SwarmFB.seedCond_apply SwarmFB.measurableSet_seedSet, rawFirstCell_inter_seed q hN,
      FirstBlockFuture, SwarmRawTimeStrict.array_firstBlock_future_mass p m q.1.1 q.1.2 q.2
        MeasurableSet.univ]
    simp only [Set.inter_univ]
    change _⁻¹ * (firstBlockLowMass (N := N) p m q *
      arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N))) = _
    rw [mul_left_comm, ENNReal.inv_mul_cancel hV (measure_ne_top _ _), mul_one]
  have hsub : rawFirstCell (N := N) p m q Set.univ ⊆ {U | firstTime p m U = 1} :=
    fun _ hU => firstTime_eq_of_rawFirstCell p m q hN hU
  have hp : 0 < ν {U | firstTime p m U = 1} :=
    (hcell.symm ▸ hlow).trans_le (measure_mono hsub)
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

/-- The limiting occupation law in equation (4.13), with convergence
of the diameter probabilities under both the conditional and original laws. -/
theorem exists_diameter_occupationLaw (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution Δ atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ A : Set ℝ, MeasurableSet A →
        ν.toMeasure.real A =
          (∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A}) /
            (∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar).toReal ∧
        Tendsto (fun n => μstar.real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) ∧
        Tendsto (fun n => (arrayMeasure N).real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
  change ∃ ν : ProbabilityMeasure ℝ, _
  have hN₀ : 0 < N := by omega
  have hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  letI : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure hV
  have htight := M4Blk.dT_tight p m hp₀ hp₁ hm N hN
  obtain ⟨π, hπ, hinv⟩ := SwarmDTR.exists_invariant_of_dT_tight hp₀ hp₁
    (by omega : 1 ≤ m) hN₀ htight
  letI : IsProbabilityMeasure π := hπ
  obtain ⟨hfull, _, hreg, _⟩ :=
    ActualNeutralCapstone.actual_neutral_regenLaw_of_invariant_derived_level hp₀ hp₁ hm hN π hinv
  have hfinite : ∀ᵐ U ∂arrayMeasure N, RegenPath.D (posPath p m U) ≠ ⊤ := by
    filter_upwards [SwarmDTR.ae_exists_strictAttempt_of_dT_tight hp₀ hp₁ hm hN htight] with U hU
    obtain ⟨r, hr⟩ := hU
    have hrec : SwarmSel.isRegen (RawStrictAttemptTower.attemptTime p m U r)
        ((r + 1 : ℕ) : ℤ) (posPath p m U) := by
      obtain ⟨ha, hb⟩ := hr
      refine ⟨ha, ?_⟩
      intro n hn i
      have hh := hb (n - RawStrictAttemptTower.attemptTime p m U r) (by omega) i
      have htime : RawStrictAttemptTower.attemptTime p m U r +
          (n - RawStrictAttemptTower.attemptTime p m U r) = n := by omega
      rw [htime] at hh
      exact hh
    exact (SwarmActualHfull.raw_D_ne_top_iff_exists_isRegen (posPath p m U)
      (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U)).mpr
      ⟨_, _, by exact_mod_cast Nat.succ_pos r, hrec⟩
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
    exact firstTime_eq_selectedT_zero hN₀ (hU 1)
  have hint : Integrable (fun U => ((T U + 1 : ℕ) : ℝ)) μstar := by
    apply (hreg.2.1 0).congr
    filter_upwards [hTeq, htime_eq] with U he he'
    exact congrArg (fun t : ℕ => (t : ℝ)) (he.trans he').symm
  have hfin : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) ≠ ∞ := by
    have h := (hasFiniteIntegral_def _ _).mp hint.hasFiniteIntegral
    simpa only [Real.enorm_natCast] using h.ne
  have hone : 0 < μstar.real {U | T U = 0} := by
    apply (seedCond_firstTime_eq_one_pos hN₀ hV).trans_le
    apply measureReal_mono
    intro U hU
    change firstTime p m U - 1 = 0
    change firstTime p m U = 1 at hU
    rw [hU]
  let ν := CycleOccupation.occupationLaw μstar hT hΔ hfin
  have hstar (A : Set ℝ) (hA : MeasurableSet A) :
      Tendsto (fun n => μstar.real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) := by
    apply CycleOccupation.observation_prob_tendsto_of_first_interval hT hΔ hfin hone hA
    intro t k
    have he (t : ℕ) : {U | T U = t} =ᵐ[μstar] {U | firstTime p m U = t + 1} := by
      filter_upwards [hTeq] with U hU
      apply propext
      change T U = t ↔ firstTime p m U = t + 1
      omega
    have heA : {U | T U = t ∧ Δ (t + 1 + k) U ∈ A} =ᵐ[μstar]
        {U | firstTime p m U = t + 1 ∧ Δ (t + 1 + k) U ∈ A} := by
      filter_upwards [he t] with U hh
      exact congrArg (fun b : Prop => b ∧ Δ (t + 1 + k) U ∈ A) hh
    rw [measureReal_congr heA, measureReal_congr (he t)]
    exact real_prob_firstTime_factor hN₀ hfiniteStar (t + 1) k hA (μstar {U | Δ k U ∈ A})
      (fun q => by
        rw [seedCond_firstCell_factor hN₀ hV q (measurable_pathDiameter k hA),
          normalizedStrictLaw_eq_seedCond_map,
          Measure.map_apply (measurable_posPath p m N) (measurable_pathDiameter k hA)]
        rfl)
  have hraw (A : Set ℝ) (hA : MeasurableSet A) :
      Tendsto (fun n => (arrayMeasure N).real {U | Δ n U ∈ A}) atTop (𝓝 (ν.toMeasure.real A)) := by
    apply CycleOccupation.observation_prob_tendsto_of_delay htime hΔ hA ?_ (hstar A hA)
    intro t k
    exact real_prob_firstTime_factor hN₀ hfinite t k hA (μstar {U | Δ k U ∈ A})
      (fun q => by
        rw [rawFirstCell_normalized_mass p m N q hV (measure_ne_top _ _) (measurable_pathDiameter k hA),
          normalizedStrictLaw_eq_seedCond_map,
          Measure.map_apply (measurable_posPath p m N) (measurable_pathDiameter k hA)]
        rfl)
  have hformula (A : Set ℝ) (hA : MeasurableSet A) :
      ν.toMeasure.real A =
        (∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ Δ t U ∈ A}) /
          (∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar).toReal := by
    change (CycleOccupation.occupationLaw μstar hT hΔ hfin).toMeasure.real A = _
    rw [CycleOccupation.occupationLaw_real_apply μstar hT hΔ hfin hA]
    have hI : (∫⁻ U, (↑(T U + 1) : ℝ≥0∞) ∂μstar) =
        ∫⁻ U, (↑(firstTime p m U) : ℝ≥0∞) ∂μstar :=
      lintegral_congr_ae (hTeq.mono (fun _ he => congrArg (fun n : ℕ => (n : ℝ≥0∞)) he))
    rw [hI]
    congr 1
    apply tsum_congr
    intro t
    apply measureReal_congr
    filter_upwards [hTeq] with U he
    apply propext
    change (t ≤ T U ∧ Δ t U ∈ A) ↔ (t < firstTime p m U ∧ Δ t U ∈ A)
    exact and_congr (by omega) Iff.rfl
  have hnonneg : ∀ᵐ x ∂ν.toMeasure, 0 ≤ x := by
    rw [ae_iff]
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    change ν.toMeasure.real (Set.Iio 0) = 0
    rw [hformula _ measurableSet_Iio]
    have hzero (t : ℕ) : {U : Array N | t < firstTime p m U ∧ Δ t U ∈ Set.Iio 0} = ∅ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => (not_lt_of_ge (pathDiameter_nonneg t (posPath p m U))) h.2
    simp only [hzero, measureReal_empty, tsum_zero, zero_div]
  exact ⟨ν, hnonneg, CycleOccupation.tendstoInDistribution_of_observation_prob_tendsto hΔ hraw,
    fun A hA => ⟨hformula A hA, hstar A hA, hraw A hA⟩⟩

end Swarming.Diameter
