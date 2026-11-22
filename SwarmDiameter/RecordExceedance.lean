import SwarmDiameter.DyadicTail
import SwarmDiameter.RecordOccupation
import Swarm.ActualRecordGeometry
import Swarm.RecordClockLocal

open Filter MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmFresh SwarmRestart
open SwarmRecordMeas.Actual RawStrictTransport SimJump.RecKernel
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]

/-- On the event that every record level is reached, the first hitting time as
an extended natural equals the existing record clock. -/
theorem recordTime_posPath_eq_of_mem_reachAll {U : Array N} (hU : U ∈ ReachAll p m) (r : ℕ) :
    recordTime (posPath p m U) r = (recTimeA p m U r : ℕ∞) := by
  apply RegenPath.tau_eq_iff.mpr
  refine ⟨M4RecordGeom.exists_traj_eq_level hU r, ?_⟩
  intro n hn i hi
  have hc := (M4RecordGeom.isRecord_recTimeA_of_reach hU r).1 n hn
  have hl := RecordDefect.le_runMax (X := RecordoSupply.actX p m U) (n := n) i
  have h : RecordoSupply.actX p m U i n = (r : ℤ) := hi
  omega

/-- At each threshold the diameter probabilities at the record times converge.
The occupation formula counts record levels strictly before the first regeneration. -/
theorem tendsto_record_diameter_tail_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (x : ℝ) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let b := ∫⁻ U, (D U : ℝ≥0∞) ∂μstar
    let X := posPath (N := N) p m
    0 < b.toReal ∧ b ≠ ∞ ∧
      Tendsto (fun r => (arrayMeasure N).real
        {U | x < pathDiameter (recordTime (X U) r).toNat (X U)}) atTop
        (𝓝 ((∑' r : ℕ, μstar.real
          {U | r < D U ∧ x < pathDiameter (recordTime (X U) r).toNat (X U)}) / b.toReal)) := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let A (r : ℕ) : Set (RegenPath.Path N) := {X | ∃ s : ℕ,
    recordTime X r = (s : ℕ∞) ∧ x < pathDiameter s X}
  have hA (r : ℕ) : MeasurableSet (A r) := by
    have he : A r = ⋃ s : ℕ, {X | recordTime X r = (s : ℕ∞)} ∩ {X | x < pathDiameter s X} := by
      ext X
      simp only [A, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [he]
    exact MeasurableSet.iUnion fun s =>
      ((measurable_recordTime r) (measurableSet_singleton (s : ℕ∞))).inter
        (measurable_pathDiameter s measurableSet_Ioi)
  have hshift {X : RegenPath.Path N} {t d : ℕ} (hr : SwarmChain.pathRec t (d : ℤ) X) (r : ℕ) :
      SwarmChain.pathRel t (d : ℤ) X ∈ A r ↔ X ∈ A (d + r) := by
    let Y := SwarmChain.pathRel t (d : ℤ) X
    change (∃ s : ℕ, recordTime Y r = (s : ℕ∞) ∧ x < pathDiameter s Y) ↔
      (∃ v : ℕ, recordTime X (d + r) = (v : ℕ∞) ∧ x < pathDiameter v X)
    rw [recordTime_add_eq_of_pathRec hr r]
    constructor
    · rintro ⟨s, hs, hdiam⟩
      rw [hs, ← ENat.natCast_add]
      exact ⟨t + s, rfl, (pathDiameter_shift X t s (d : ℤ)) ▸ hdiam⟩
    · rintro ⟨v, hv, hdiam⟩
      have htv : (t : ℕ∞) ≤ (v : ℕ∞) := hv ▸ le_self_add
      have ht' := ENat.natCast_le_natCast.mp htv
      have he : v = t + (v - t) := by omega
      rw [he, ENat.natCast_add] at hv
      refine ⟨v - t, ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top t) hv, ?_⟩
      change x < pathDiameter (v - t) (fun n i => X (t + n) i - (d : ℤ))
      rw [pathDiameter_shift X t (v - t) (d : ℤ), Nat.add_sub_of_le ht']
      exact hdiam
  have hreach := ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN
  have hac : μstar ≪ arrayMeasure N := ProbabilityTheory.cond_absolutelyContinuous
  have hAeq {U : Array N} (hU : U ∈ ReachAll p m) (r : ℕ) :
      posPath p m U ∈ A r ↔ x < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) := by
    have he := recordTime_posPath_eq_of_mem_reachAll hU r
    change (∃ s : ℕ, recordTime (posPath p m U) r = (s : ℕ∞) ∧ x < pathDiameter s (posPath p m U)) ↔ _
    rw [he, ENat.toNat_natCast]
    simp only [ENat.natCast_inj, exists_eq_left']
  obtain ⟨hpos, hfin, ht⟩ := tendsto_record_event_occupation hp₀ hp₁ hm hN A hA hshift
  refine ⟨hpos, hfin, ?_⟩
  have hsame (r : ℕ) : μstar.real {U | r < firstLevel p m U ∧ posPath p m U ∈ A r} =
      μstar.real {U | r < firstLevel p m U ∧
        x < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U)} := by
    apply measureReal_congr
    filter_upwards [hac.ae_le hreach] with U hU
    exact propext (and_congr_right (fun _ => hAeq hU r))
  change Tendsto (fun r => (arrayMeasure N).real {U | posPath p m U ∈ A r}) atTop
    (𝓝 ((∑' r : ℕ, μstar.real {U | r < firstLevel p m U ∧ posPath p m U ∈ A r}) /
      (∫⁻ U, (firstLevel p m U : ℝ≥0∞) ∂μstar).toReal)) at ht
  rw [tsum_congr hsame] at ht
  apply ht.congr
  intro r
  apply measureReal_congr
  filter_upwards [hreach] with U hU
  exact propext (hAeq hU r)

omit [Nonempty (Fin N)] in
private theorem driftMartingale_sub_le_pos_sub {U : Array N} {s t : ℕ}
    (hp : (1 : ℝ) / 2 ≤ p) (hst : s ≤ t) (i : Fin N) :
    driftMartingale p m U t i - driftMartingale p m U s i ≤
      (posPath p m U t i : ℝ) - (posPath p m U s i : ℝ) := by
  have hc : excitedSteps p m U s i ≤ excitedSteps p m U t i := by
    apply Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hst)
  have hc' : (excitedSteps p m U s i : ℝ) ≤ (excitedSteps p m U t i : ℝ) := by
    exact_mod_cast hc
  unfold driftMartingale
  have h := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 2 * p - 1 by linarith)
  change _ ≤ ((trajectory p m U t).pos i : ℝ) - ((trajectory p m U s).pos i : ℝ)
  linarith

/-- The probability of a diameter exceedance inside a record interval is
bounded by the tail of its initial diameter, the tail of its duration, and
a martingale deviation over the first `u` steps after reaching the record. -/
theorem record_interval_exceedance_prob_le
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (r u : ℕ) (hu : 1 ≤ u) {x : ℝ} (hx : 0 < x) :
    let X := posPath (N := N) p m
    (arrayMeasure N).real {U | recordIntervalExceeds (X U) r x} ≤
      (arrayMeasure N).real {U | x / 2 < pathDiameter (recordTime (X U) r).toNat (X U)} +
      (arrayMeasure N).real {U | (u : ℕ∞) < recordDuration (X U) r} +
        (N : ℝ) * (2 * ((u : ℝ) + 1) * Real.exp (-(x ^ 2) / (64 * (u : ℝ)))) := by
  let X := posPath (N := N) p m
  let μ := arrayMeasure N
  let B : Set (Array N) := {U | x / 2 < pathDiameter (recordTime (X U) r).toNat (X U)}
  let C : Set (Array N) := {U | (u : ℕ∞) < recordDuration (X U) r}
  let J (i : Fin N) := ReachAll p m ∩
    StoppedWindow.stoppedMax (fun t U => driftMartingale p m U t i)
      (fun U => recTimeA p m U r) u (x / 2)
  let E : Set (Array N) := {U | recordIntervalExceeds (X U) r x}
  have hcover : ∀ᵐ U ∂μ, U ∈ E → U ∈ (B ∪ C) ∪ ⋃ i ∈ (Finset.univ : Finset (Fin N)), J i := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN] with U hU hE
    by_cases hB : U ∈ B
    · exact Or.inl (Or.inl hB)
    by_cases hC : U ∈ C
    · exact Or.inl (Or.inr hC)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hE
    let s := recTimeA p m U r
    have hs' : recordTime (X U) r = (s : ℕ∞) := recordTime_posPath_eq_of_mem_reachAll hU r
    have hs : s ≤ t := by
      rw [hs', ENat.natCast_le_natCast] at ht₁
      exact ht₁
    have hn' := recordTime_posPath_eq_of_mem_reachAll hU (r + 1)
    have hn : t < recTimeA p m U (r + 1) := by
      rw [hn', ENat.natCast_lt_natCast] at ht₂
      exact ht₂
    have hdu : t - s ≤ u := by
      have hle : recordDuration (X U) r ≤ (u : ℕ∞) := le_of_not_gt hC
      rw [recordDuration, hs', hn', ← ENat.natCast_sub, ENat.natCast_le_natCast] at hle
      omega
    have hinitial : pathDiameter s (X U) ≤ x / 2 := by
      apply le_of_not_gt
      change ¬x / 2 < pathDiameter (recordTime (X U) r).toNat (X U) at hB
      simpa only [hs', ENat.toNat_natCast] using hB
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (X U t)
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (X U t)
    have htwidth : pathDiameter t (X U) = ((X U t a - X U t i : ℤ) : ℝ) := by
      unfold pathDiameter LeaderDescent.spreadZ
      congr 1
      exact congrArg₂ (· - ·) ha hi
    have hmax : (X U t a : ℝ) ≤ (r : ℝ) := by
      have hpos : X U t a ≤ RecordDefect.runMax (RecordoSupply.actX p m U) t :=
        RecordDefect.le_runMax t a
      have hlt := M4RecordGeom.runMax_lt_of_lt_recTimeA hU hn
      apply Int.cast_le.mpr
      omega
    obtain ⟨j, hj⟩ := M4RecordGeom.exists_traj_eq_level hU r
    have hpos : (r : ℝ) - (X U s i : ℝ) ≤ x / 2 := by
      have hdiam := (sub_le_pathDiameter s (X U) j i).trans hinitial
      rw [Int.cast_sub] at hdiam
      have hjs : X U s j = (r : ℤ) := hj
      simpa only [hjs, Int.cast_natCast] using hdiam
    rw [htwidth, Int.cast_sub] at ht₃
    have hdiff : (X U t i : ℝ) - (X U s i : ℝ) ≤ -(x / 2) := by linarith
    have hmart := (driftMartingale_sub_le_pos_sub hp₀.le hs i).trans hdiff
    refine Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_univ i, ?_⟩⟩)
    refine ⟨hU, t - s, hdu, ?_⟩
    change x / 2 ≤ |driftMartingale p m U (s + (t - s)) i - driftMartingale p m U s i|
    rw [Nat.add_sub_of_le hs]
    simpa only [neg_neg] using (neg_le_neg hmart).trans (neg_le_abs _)
  change μ.real E ≤ μ.real B + μ.real C + _
  have hprob : μ.real E ≤ μ.real ((B ∪ C) ∪ ⋃ i ∈ (Finset.univ : Finset (Fin N)), J i) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)
  let _ : IsProbabilityMeasure μ := arrayMeasure_isProbabilityMeasure N
  have hj (i : Fin N) : μ.real (J i) ≤
      2 * ((u : ℝ) + 1) * Real.exp (-(x ^ 2) / (64 * (u : ℝ))) := by
    have h := StoppedWindow.measureReal_band_stoppedMax_le
      (μ := μ) (ℱ := Swarming.Enl.enlFilt p m)
      (Q := fun t U => driftMartingale p m U t i) (σ := fun U => recTimeA p m U r)
      (B := fun a => ClockFibre.clockFibre p m r a) (G := ReachAll p m)
      (fun t => RecordClock.stronglyMeasurable_driftMartingale p m t i)
      (fun t => RecordClock.integrable_driftMartingale hp₀ hp₁ m t i)
      (fun t => RecordClock.condExp_increments_driftMartingale hp₀ hp₁ m t i)
      (by norm_num : (0 : ℝ) < 2)
      (fun t U => RecordClock.abs_increment_driftMartingale hp₀ hp₁ m t i U)
      (fun a => ClockFibre.measurableSet_clockFibre p m r a)
      (fun a b hab => ClockFibre.disjoint_clockFibre p m r a b hab)
      (ClockFibre.reachAll_subset_iUnion_clockFibre p m r)
      (fun a U hU => ClockFibre.recTimeA_eq_of_mem_clockFibre hU.1 hU.2)
      hu (show 0 < x / 2 by positivity)
    have he : -((x / 2) ^ 2) / (4 * (u : ℝ) * 2 ^ 2) = -(x ^ 2) / (64 * (u : ℝ)) := by ring
    rwa [he] at h
  calc
    _ ≤ μ.real ((B ∪ C) ∪ ⋃ i ∈ (Finset.univ : Finset (Fin N)), J i) := hprob
    _ ≤ μ.real (B ∪ C) + μ.real (⋃ i ∈ (Finset.univ : Finset (Fin N)), J i) :=
      measureReal_union_le _ _
    _ ≤ μ.real B + μ.real C + (N : ℝ) *
        (2 * ((u : ℝ) + 1) * Real.exp (-(x ^ 2) / (64 * (u : ℝ)))) := by
      apply add_le_add (measureReal_union_le B C)
      apply (measureReal_biUnion_finset_le Finset.univ J).trans
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj i)

/-- Without a martingale estimate, two unit steps bound the increase in the
diameter per unit of time inside a record interval. -/
theorem record_interval_exceedance_prob_le_initial_or_duration
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (r : ℕ) (x : ℝ) :
    let X := posPath (N := N) p m
    (arrayMeasure N).real {U | recordIntervalExceeds (X U) r x} ≤
      (arrayMeasure N).real {U | x / 2 < pathDiameter (recordTime (X U) r).toNat (X U)} +
      (arrayMeasure N).real {U | x / 4 < ((recordDuration (X U) r).toNat : ℝ)} := by
  let X := posPath (N := N) p m
  let μ := arrayMeasure N
  let B : Set (Array N) := {U | x / 2 < pathDiameter (recordTime (X U) r).toNat (X U)}
  let C : Set (Array N) := {U | x / 4 < ((recordDuration (X U) r).toNat : ℝ)}
  let E : Set (Array N) := {U | recordIntervalExceeds (X U) r x}
  have hcover : ∀ᵐ U ∂μ, U ∈ E → U ∈ B ∪ C := by
    filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN] with U hU hx
    have h₀ := recordTime_posPath_eq_of_mem_reachAll hU r
    have h₁ := recordTime_posPath_eq_of_mem_reachAll hU (r + 1)
    have h := recordIntervalExceeds_imp_diameter_or_duration
      (fun n i => (posPath_step p m U n i).le) h₀ h₁ hx
    change x / 2 < pathDiameter (recordTime (X U) r).toNat (X U) ∨
      x / 4 < ((recordDuration (X U) r).toNat : ℝ)
    rw [h₀, recordDuration, h₀, h₁, ← ENat.natCast_sub, ENat.toNat_natCast, ENat.toNat_natCast]
    exact h
  exact (ENNReal.toReal_mono (measure_ne_top μ (B ∪ C)) (measure_mono_ae hcover)).trans
    (measureReal_union_le B C)

/-- The original array law has uniformly tight diameters at the record times. -/
theorem record_diameter_tight
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ r : ℕ, (arrayMeasure N).real
      {U | (K : ℝ) < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U)} ≤ ε := by
  let hm₀ : 1 ≤ m := by omega
  let Y := WCJF.ActPath.arrPath (N := N) p m hm₀
  have hμ := WCJF.ActPath.array_fullLaw (N := N) p hp₀ hp₁ hm hN
  obtain ⟨K, hK⟩ := M4Blk.dT_tight p m hp₀ hp₁ hm N hN (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  refine ⟨K, fun r => ?_⟩
  have hA : MeasurableSet {ω : ℕ → SwarmRec.RecState N m × ℕ | K < dT ω r} :=
    measurable_dT_eval r (MeasurableSet.of_discrete (s := Ioi K))
  specialize hK r
  rw [← hμ, Measure.map_apply (WCJF.ActPath.measurable_arrPath p m hm₀) hA] at hK
  have hmass := ENNReal.toReal_mono ENNReal.ofReal_ne_top hK
  rw [ENNReal.toReal_ofReal hε.le] at hmass
  apply le_trans ?_ hmass
  apply le_of_eq
  apply measureReal_congr
  filter_upwards [ClockFibre.ae_mem_reachAll (N := N) hp₀ hp₁ hm hN,
    M2RecordFinite.ae_defect_toNat_eq_two_mul_dmax (N := N) hp₀ hp₁ hm hN hm₀ r] with U hU he
  apply propext
  change (K : ℝ) < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U) ↔
    K < dT (Y U) r
  rw [recordTime_posPath_eq_of_mem_reachAll hU r, ENat.toNat_natCast]
  have hrec := M4RecordGeom.isRecord_recTimeA_of_reach hU
  have hwidth : pathDiameter (recTimeA p m U r) (posPath p m U) =
      (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r : ℝ) := by
    unfold pathDiameter LeaderDescent.spreadZ RecordDefect.defect
    congr 1
    exact congrArg (fun z : ℤ => z - _) (hrec r).2
  rw [hwidth]
  have hd : (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r : ℝ) =
      (dT (Y U) r : ℝ) := by
    have hnonneg := RecordDefect.defect_nonneg hrec r
    have he' := (Int.toNat_of_nonneg hnonneg).symm
    change (RecordDefect.defect (RecordoSupply.actX p m U) (recTimeA p m U) r).toNat =
      dT (Y U) r at he
    rw [he] at he'
    exact_mod_cast he'
  rw [hd]
  exact Nat.cast_lt

/-- A quantitative contraction of the diameter at record times yields the
upper tail with the same exponent. The contraction is needed at each fixed
scale for all sufficiently large record levels. -/
theorem record_diameter_tail_le_of_contraction
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B L₀ : ℕ} {K c γ : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hγ : 0 < γ)
    (hcontraction : ∀ L ≥ L₀, ∀ᶠ r : ℕ in atTop,
      (arrayMeasure N).real {U | (L : ℝ) < pathDiameter
        (recordTime (posPath p m U) (r + B * L)).toNat (posPath p m U)} ≤
      (arrayMeasure N).real {U | (2 * L : ℝ) < pathDiameter
        (recordTime (posPath p m U) r).toNat (posPath p m U)} +
      K * Real.exp (-c * (L : ℝ) ^ γ))
    {L : ℕ} (hL₀ : L₀ ≤ L) (hL : 1 ≤ L) :
    limsup (fun r => (arrayMeasure N).real
      {U | (L : ℝ) < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U)}) atTop ≤
      K / (1 - Real.exp (-c * ((2 : ℝ) ^ γ - 1))) * Real.exp (-c * (L : ℝ) ^ γ) := by
  let Q (L r : ℕ) : ℝ := (arrayMeasure N).real
    {U | (L : ℝ) < pathDiameter (recordTime (posPath p m U) r).toNat (posPath p m U)}
  let A (L : ℕ) := limsup (Q L) atTop
  have hlim (L : ℕ) : Tendsto (Q L) atTop (𝓝 (A L)) := by
    have h := (tendsto_record_diameter_tail_occupation (N := N) hp₀ hp₁ hm hN (L : ℝ)).2.2
    change Tendsto (Q L) atTop (𝓝 _) at h
    change Tendsto (Q L) atTop (𝓝 (limsup (Q L) atTop))
    rw [h.limsup_eq]
    exact h
  have hzero : Tendsto A atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun L => ha.trans_le (ge_of_tendsto' (hlim L) (fun _ => measureReal_nonneg))
    · intro a ha
      obtain ⟨J, hJ⟩ := record_diameter_tight hp₀ hp₁ hm hN (show 0 < a / 2 by linarith)
      filter_upwards [eventually_ge_atTop J] with l hl
      have hJl : (J : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
      have h : A l ≤ a / 2 := le_of_tendsto' (hlim l) fun r => by
        apply (measureReal_mono ?_ (measure_ne_top _ _)).trans (hJ r)
        intro U hU
        exact hJl.trans_lt hU
      exact h.trans_lt (by linarith)
  refine le_stretchedExp_of_dyadic_tail hK hc hγ hzero (fun l hl => ?_) hL₀ hL
  have hsh : Tendsto (fun r => Q l (r + B * l)) atTop (𝓝 (A l)) :=
    (hlim l).comp (tendsto_add_atTop_nat (B * l))
  refine le_of_tendsto_of_tendsto hsh ((hlim (2 * l)).add_const _) ?_
  change ∀ᶠ r : ℕ in atTop, Q l (r + B * l) ≤ Q (2 * l) r + K * Real.exp (-c * (l : ℝ) ^ γ)
  simpa only [Q, Nat.cast_mul, Nat.cast_ofNat] using hcontraction l hl

/-- To bound the duration of one record interval, it suffices to bound the
time to reach a later record level when the initial diameter is small. -/
theorem record_duration_limsup_le_of_advance
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {B u : ℕ} (hB : 1 ≤ B) {L a : ℝ}
    (hadvance : let X := posPath (N := N) p m
      ∀ᶠ r : ℕ in atTop, (arrayMeasure N).real
        {U | pathDiameter (recordTime (X U) r).toNat (X U) ≤ L ∧
          (u : ℕ∞) < recordTime (X U) (r + B) - recordTime (X U) r} ≤ a) :
    let X := posPath (N := N) p m
    limsup (fun r => (arrayMeasure N).real
      {U | (u : ℕ∞) < recordDuration (X U) r}) atTop ≤
    limsup (fun r => (arrayMeasure N).real
      {U | L < pathDiameter (recordTime (X U) r).toNat (X U)}) atTop + a := by
  let X := posPath (N := N) p m
  let μ := arrayMeasure N
  let W (r : ℕ) := {U | (u : ℕ∞) < recordDuration (X U) r}
  let A (r : ℕ) := {U | L < pathDiameter (recordTime (X U) r).toNat (X U)}
  let C (r : ℕ) := {U | pathDiameter (recordTime (X U) r).toNat (X U) ≤ L ∧
    (u : ℕ∞) < recordTime (X U) (r + B) - recordTime (X U) r}
  obtain ⟨_, _, hW⟩ := tendsto_record_duration_tail_occupation (N := N) hp₀ hp₁ hm hN u
  obtain ⟨_, _, hA⟩ := tendsto_record_diameter_tail_occupation (N := N) hp₀ hp₁ hm hN L
  have hWlim : Tendsto (fun r => μ.real (W r)) atTop (𝓝 (limsup (fun r => μ.real (W r)) atTop)) := by
    change Tendsto (fun r => μ.real (W r)) atTop (𝓝 _) at hW
    rw [hW.limsup_eq]
    exact hW
  have hAlim : Tendsto (fun r => μ.real (A r)) atTop (𝓝 (limsup (fun r => μ.real (A r)) atTop)) := by
    change Tendsto (fun r => μ.real (A r)) atTop (𝓝 _) at hA
    rw [hA.limsup_eq]
    exact hA
  apply le_of_tendsto_of_tendsto hWlim (hAlim.add_const a)
  filter_upwards [hadvance] with r hr
  have hsub : W r ⊆ A r ∪ C r := by
    intro U hU
    by_cases h : U ∈ A r
    · exact Or.inl h
    · have hmono := recordTime_mono (posPath_zero p m U) (posPath_step p m U)
      exact Or.inr ⟨le_of_not_gt h, lt_of_lt_of_le hU (tsub_le_tsub_right (hmono (by omega)) _)⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add_right hr _))

end Swarming.Diameter
