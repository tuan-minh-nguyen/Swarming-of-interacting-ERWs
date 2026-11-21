import Swarm.BlkMeasure
import Swarm.EnlFilt
import Swarm.NeutralTwoInputCapstone
import Swarm.RawInitialPathLaw

open Filter Finset MeasureTheory ProbabilityTheory Set
open Swarming.Enl Swarming.Uniform SwarmRestart
open RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped Topology

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ}

/-- Times through `n` at which all walkers first reach the same nonnegative level. -/
noncomputable def simultaneousRecordTimes (X : ℕ → Fin N → ℤ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun t => ∃ r : ℕ, SwarmChain.pathRec t (r : ℤ) X

theorem mem_simultaneousRecordTimes {X : ℕ → Fin N → ℤ} {t n : ℕ} :
    t ∈ simultaneousRecordTimes X n ↔ t ≤ n ∧ ∃ r : ℕ, SwarmChain.pathRec t (r : ℤ) X := by
  classical
  rw [simultaneousRecordTimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem measurableSet_simultaneousRecordAt_enl (p : ℝ) (m t : ℕ) :
    MeasurableSet[enlMeas p m t] {U : Array N | ∃ r : ℕ, RecordAt p m U t (r : ℤ)} := by
  let _ : MeasurableSpace (Array N) := enlMeas p m t
  apply (Measurable.exists (ι := ℕ) ?_).setOf
  intro r
  have hlt : Measurable[enlMeas p m t] (fun U : Array N =>
      ∀ s : Fin t, ∀ i : Fin N, (Swarming.Trajectory.trajectory p m U s).pos i < (r : ℤ)) :=
    Measurable.forall fun s => Measurable.forall fun i =>
      measurableSet_setOfPred.mp (enl_pos_measurable p m t s.isLt.le i measurableSet_Iio)
  have heq : Measurable[enlMeas p m t] (fun U : Array N =>
      ∀ i : Fin N, (Swarming.Trajectory.trajectory p m U t).pos i = (r : ℤ)) :=
    Measurable.forall fun i =>
      measurableSet_setOfPred.mp
        (measurableSet_eq_fun (enl_pos_measurable p m t le_rfl i) measurable_const)
  have hiff (U : Array N) :
      ((∀ s : Fin t, ∀ i : Fin N, (Swarming.Trajectory.trajectory p m U s).pos i < (r : ℤ)) ∧
        ∀ i : Fin N, (Swarming.Trajectory.trajectory p m U t).pos i = (r : ℤ)) ↔
      RecordAt p m U t (r : ℤ) :=
    ⟨fun h => ⟨fun s hs i => h.1 ⟨s, hs⟩ i, h.2⟩, fun h => ⟨fun s => h.1 s s.isLt, h.2⟩⟩
  simpa only [hiff] using hlt.and heq

private theorem measurable_simultaneousRecordTimes (n : ℕ) :
    Measurable (fun X : ℕ → Fin N → ℤ => simultaneousRecordTimes X n) := by
  rw [measurable_finset_iff]
  intro t
  simp only [mem_simultaneousRecordTimes]
  exact measurable_const.and (Measurable.exists fun r : ℕ =>
    measurableSet_setOfPred.mp (SwarmChain.measurable_pathRec t (r : ℤ)))

private theorem measurableSet_eventually_record_density (ρ : ℝ) :
    MeasurableSet {X : ℕ → Fin N → ℤ | ∀ᶠ n : ℕ in atTop,
      ρ * (n : ℝ) ≤ (simultaneousRecordTimes X n).card} := by
  have hmeas (n : ℕ) : Measurable (fun X : ℕ → Fin N → ℤ =>
      (simultaneousRecordTimes X n).card) :=
    (measurable_of_countable Finset.card).comp (measurable_simultaneousRecordTimes n)
  simp only [eventually_atTop]
  apply (Measurable.exists (ι := ℕ) ?_).setOf
  intro k
  apply Measurable.forall
  intro n
  exact measurable_const.imp
    (measurableSet_setOfPred.mp
      ((hmeas n) (MeasurableSet.of_discrete (s := {j : ℕ | ρ * (n : ℝ) ≤ (j : ℝ)}))))

private theorem eventually_record_density_of_regeneration
    {X : ℕ → Fin N → ℤ} {T z : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k)
    (hrec : ∀ k, SwarmChain.pathRec (Swarm.blockSum T k) (z k : ℤ) X)
    {a b : ℝ} (ha : 0 < a) (hb : b < a)
    (hlim : Tendsto (fun k => (Swarm.blockSum T k : ℝ) / k) atTop (𝓝 b)) :
    ∀ᶠ n : ℕ in atTop, a⁻¹ * (n : ℝ) ≤ (simultaneousRecordTimes X n).card := by
  have hK := Swarm.tendsto_renewCount hT
  have hS := (Swarm.tendsto_div_succ hlim).comp hK
  filter_upwards [hS.eventually (eventually_lt_nhds hb),
    hK.eventually (eventually_ge_atTop 1)] with n htime hpos
  let k := Swarm.renewCount T n
  have hk : k ≤ (simultaneousRecordTimes X n).card := by
    have hind := Swarm.strictMono_blockSum hT
    have hmap : Set.MapsTo (Swarm.blockSum T) (Finset.range k) (simultaneousRecordTimes X n) := by
      intro j hj
      have hjk : j ≤ k := (Finset.mem_range.mp hj).le
      exact mem_simultaneousRecordTimes.mpr
        ⟨(hind.monotone hjk).trans (Swarm.blockSum_renewCount_le T n), z j, hrec j⟩
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hind.injective.injOn
  have hpos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by exact hpos)
  have htime' : (Swarm.blockSum T (k + 1) : ℝ) < a * (k : ℝ) :=
    (div_lt_iff₀ hpos').mp htime
  have hn : (n : ℝ) < (Swarm.blockSum T (k + 1) : ℝ) := by
    exact_mod_cast Swarm.lt_blockSum_renewCount_succ hT n
  have hcard : (k : ℝ) ≤ (simultaneousRecordTimes X n).card := by exact_mod_cast hk
  calc
    a⁻¹ * (n : ℝ) = (n : ℝ) / a := by rw [div_eq_mul_inv, mul_comm]
    _ ≤ (k : ℝ) := (div_le_iff₀ ha).mpr (by linarith)
    _ ≤ (simultaneousRecordTimes X n).card := hcard

private theorem card_simultaneousRecordTimes_pathRel_le {X : ℕ → Fin N → ℤ} {t d : ℕ}
    (hrec : SwarmChain.pathRec t (d : ℤ) X) (n : ℕ) :
    (simultaneousRecordTimes (SwarmChain.pathRel t (d : ℤ) X) n).card ≤
      (simultaneousRecordTimes X (t + n)).card := by
  apply Finset.card_le_card_of_injOn (t + ·)
  · intro s hs
    obtain ⟨hs, r, hr⟩ := mem_simultaneousRecordTimes.mp hs
    have h := (SwarmChain.pathRec_pathRel t s (d : ℤ) (r : ℤ) X (by positivity) hrec).mp hr
    exact mem_simultaneousRecordTimes.mpr ⟨Nat.add_le_add_left hs t, d + r, by exact_mod_cast h⟩
  · intro s _ u _ h
    exact Nat.add_left_cancel h

/-- A common positive lower density of simultaneous record times under the
strictly positive and original laws. -/
theorem exists_positive_simultaneousRecordDensity [Nonempty (Fin N)]
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ᵐ U ∂SwarmFB.seedCond (p := p) (m := m) (N := N),
        ∀ᶠ n : ℕ in atTop, ρ * (n : ℝ) ≤ (simultaneousRecordTimes (posPath p m U) n).card) ∧
      (∀ᵐ U ∂arrayMeasure N,
        ∀ᶠ n : ℕ in atTop, ρ * (n : ℝ) ≤ (simultaneousRecordTimes (posPath p m U) n).card) := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
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
  let T := NeutralRegen.selectedT p m N
  let b := ∫ U, (T 0 U : ℝ) ∂μstar
  let a := b + 1
  have hb : 0 < b := hreg.mean_pos
  have ha : 0 < a := by dsimp only [a]; linarith
  have hba : b < a := by dsimp only [a]; linarith
  have hT := strong_law_ae_real (fun k U => (T k U : ℝ))
    (hreg.2.1 0) hreg.2.2.2.2.2.1 hreg.2.2.2.2.2.2
  have hstar : ∀ᵐ U ∂μstar, ∀ᶠ n : ℕ in atTop,
      a⁻¹ * (n : ℝ) ≤ (simultaneousRecordTimes (posPath p m U) n).card := by
    filter_upwards [hT, NeutralRegen.ae_all_chain hN₀ hfull hV] with U hlim hchain
    have hrec (k : ℕ) : SwarmChain.pathRec (NeutralRegen.selectedSigma p m N k U)
        (NeutralRegen.selectedLevel p m N k U : ℤ) (posPath p m U) := by
      rw [NeutralRegen.selectedSigma_eq_sum_Z hN₀ p m hchain, NeutralRegen.selectedLevel_cast]
      exact NeutralRegen.cumulative_record_Z hN₀ p m k (hchain k)
    exact eventually_record_density_of_regeneration (fun j => hreg.2.2.1 j U) hrec ha hba
      (by simpa only [Swarm.blockSum, Nat.cast_sum] using hlim)
  refine ⟨a⁻¹ / 2, by positivity, ?_, ?_⟩
  · filter_upwards [hstar] with U hU
    filter_upwards [hU] with n hn
    exact (mul_le_mul_of_nonneg_right (by linarith [inv_pos.mpr ha]) (by positivity)).trans hn
  · let C := ⋃ q : LevelTime, rawFirstCell (N := N) p m q Set.univ
    have hC : ∀ᵐ U ∂arrayMeasure N, U ∈ C := by
      filter_upwards [SwarmDTR.ae_exists_strictAttempt_of_dT_tight hp₀ hp₁ hm hN htight] with U hU
      obtain ⟨r, hr⟩ := hU
      change U ∈ ⋃ q : LevelTime, rawFirstCell p m q Set.univ
      rw [iUnion_rawFirstCell_univ p m hN₀]
      exact (SwarmActualHfull.raw_D_ne_top_iff_exists_isRegen (posPath p m U)
        (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U)).mpr
        ⟨_, (r + 1 : ℕ), by exact_mod_cast Nat.succ_pos r, (M1Bridge.isRegen_posPath_iff _ _ _ _ _).mpr hr⟩
    have hCmeas : MeasurableSet C :=
      MeasurableSet.iUnion fun q => measurableSet_rawFirstCell p m q MeasurableSet.univ
    have hCmass : arrayMeasure N C = 1 := (mem_ae_iff_prob_eq_one hCmeas).mp hC
    have hmap := restrict_rawCompleted_map_firstFutureZ p m N hN₀ hV (measure_ne_top _ _)
    change ((arrayMeasure N).restrict C).map (firstFutureZ p m) =
      (arrayMeasure N) C • normalizedStrictLaw p m N at hmap
    rw [Measure.restrict_eq_self_of_ae_mem hC, hCmass, one_smul,
      normalizedStrictLaw_eq_seedCond_map] at hmap
    have hmeas := measurableSet_eventually_record_density (N := N) a⁻¹
    have hfuture : ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
        a⁻¹ * (n : ℝ) ≤ (simultaneousRecordTimes (firstFutureZ p m U) n).card := by
      apply (ae_map_iff (measurable_firstFutureZ p m).aemeasurable hmeas).mp
      rw [hmap]
      exact (ae_map_iff (measurable_posPath p m N).aemeasurable hmeas).mpr hstar
    filter_upwards [hC, hfuture] with U hU hfutureU
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
    have hrec : SwarmChain.pathRec q.1.2 (q.1.1 : ℤ) (posPath p m U) :=
      ((mem_rawFirstCell p m q Set.univ U).mp hq).1.1
    rw [firstFutureZ_eq_of_rawFirstCell p m q hN₀ hq, SwarmChain.pathRel_relFuture] at hfutureU
    filter_upwards [(tendsto_sub_atTop_nat q.1.2).eventually hfutureU,
      eventually_ge_atTop (q.1.2 + q.1.2)] with n hn hlarge
    have ht : q.1.2 ≤ n := by omega
    have ht' : ((q.1.2 : ℕ) : ℝ) + ((q.1.2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlarge
    have hshift : (n : ℝ) / 2 ≤ ((n - q.1.2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub ht]
      linarith
    have hcard := card_simultaneousRecordTimes_pathRel_le hrec (n - q.1.2)
    rw [Nat.add_sub_of_le ht] at hcard
    calc
      a⁻¹ / 2 * (n : ℝ) = a⁻¹ * ((n : ℝ) / 2) := by ring
      _ ≤ a⁻¹ * ((n - q.1.2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hshift (by positivity)
      _ ≤ (simultaneousRecordTimes (SwarmChain.pathRel q.1.2 (q.1.1 : ℤ) (posPath p m U))
          (n - q.1.2)).card := hn
      _ ≤ (simultaneousRecordTimes (posPath p m U) n).card := by exact_mod_cast hcard

end Swarming.Diameter
