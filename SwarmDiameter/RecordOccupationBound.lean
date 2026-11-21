import SwarmDiameter.RecordOccupation

open Filter Finset MeasureTheory Set
open Swarming.Uniform SwarmFresh SwarmRestart RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]

private theorem sum_recordIntervals {f : ℕ → ℝ≥0∞} {s : ℕ → ℕ} {d : ℕ}
    (hzero : s 0 = 0) (hmono : ∀ r < d, s r ≤ s (r + 1)) :
    (∑ t ∈ range (s d), f t) = ∑ r ∈ range d, ∑ t ∈ Ico (s r) (s (r + 1)), f t := by
  induction d with
  | zero => simp [hzero]
  | succ d ih =>
    rw [sum_range_succ, ← ih (fun r hr => hmono r (by omega))]
    exact (sum_range_add_sum_Ico _ (hmono d (by omega))).symm

private theorem visitCount_le {X : RegenPath.Path N} {d t : ℕ} (x : ℝ) (u : ℕ)
    (hzero : recordTime X 0 = 0) (hmono : Monotone (recordTime X))
    (ht : recordTime X d = (t : ℕ∞)) :
    (∑ j ∈ range t, (Ici x).indicator (fun _ => (1 : ℝ≥0∞)) (pathDiameter j X)) ≤
      ∑ r ∈ range d,
        (({Y | recordIntervalExceeds Y r x} : Set (RegenPath.Path N)).indicator
          (fun _ => (u : ℝ≥0∞)) X + ((recordDuration X r).toNat - u : ℕ)) := by
  classical
  let s (r : ℕ) := (recordTime X r).toNat
  have hfin (r : ℕ) (hr : r ≤ d) : recordTime X r ≠ ⊤ :=
    ne_top_of_le_ne_top (ht ▸ ENat.natCast_ne_top t) (hmono hr)
  have hcast (r : ℕ) (hr : r ≤ d) : (s r : ℕ∞) = recordTime X r :=
    ENat.natCast_toNat (hfin r hr)
  have hnext (r : ℕ) (hr : r < d) : s r ≤ s (r + 1) := by
    exact ENat.natCast_le_natCast.mp (by
      rw [hcast r (by omega), hcast (r + 1) (by omega)]
      exact hmono (Nat.le_succ r))
  have hz : s 0 = 0 := by simp [s, hzero]
  have hd : s d = t := by simp [s, ht]
  rw [← hd, sum_recordIntervals hz hnext]
  apply sum_le_sum
  intro r hr
  have hr' := mem_range.mp hr
  have hw : (recordDuration X r).toNat = s (r + 1) - s r := by
    rw [recordDuration, ← hcast r (by omega), ← hcast (r + 1) (by omega),
      ← ENat.natCast_sub, ENat.toNat_natCast]
  by_cases he : recordIntervalExceeds X r x
  · rw [indicator_of_mem (show X ∈ {Y | recordIntervalExceeds Y r x} from he), hw]
    calc
      _ ≤ ∑ j ∈ Ico (s r) (s (r + 1)), (1 : ℝ≥0∞) :=
        sum_le_sum fun j _ => indicator_le_self' (fun _ _ => zero_le) (pathDiameter j X)
      _ = ((s (r + 1) - s r : ℕ) : ℝ≥0∞) := by simp [Nat.card_Ico]
      _ ≤ (u : ℝ≥0∞) + ((s (r + 1) - s r - u : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_add]
        exact_mod_cast (show s (r + 1) - s r ≤ u + (s (r + 1) - s r - u) by omega)
  · have hsum : ∑ j ∈ Ico (s r) (s (r + 1)),
        (Ici x).indicator (fun _ => (1 : ℝ≥0∞)) (pathDiameter j X) = 0 := by
      apply sum_eq_zero
      intro j hj
      apply indicator_of_notMem
      intro hx
      obtain ⟨h₁, h₂⟩ := mem_Ico.mp hj
      apply he
      refine ⟨j, ?_, ?_, hx⟩
      · rw [← hcast r (by omega)]
        exact ENat.natCast_le_natCast.mpr h₁
      · rw [← hcast (r + 1) (by omega)]
        exact ENat.natCast_lt_natCast.mpr h₂
    rw [hsum]
    exact zero_le

private theorem tsum_measure_before_eq_lintegral_count
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : Ω → ℕ}
    (hT : Measurable T) (A : ℕ → Set Ω) (hA : ∀ t, MeasurableSet (A t)) :
    (∑' t : ℕ, μ {ω | t < T ω ∧ ω ∈ A t}) =
      ∫⁻ ω, ∑ t ∈ range (T ω), (A t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
  let B (t : ℕ) := {ω | t < T ω ∧ ω ∈ A t}
  have hB (t : ℕ) : MeasurableSet (B t) := (measurableSet_Ioi.preimage hT).inter (hA t)
  change (∑' t, μ (B t)) = _
  have he : (∑' t : ℕ, μ (B t)) =
      ∫⁻ ω, ∑' t : ℕ, (B t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
    rw [lintegral_tsum (fun t => (measurable_const.indicator (hB t)).aemeasurable)]
    exact tsum_congr fun t => (lintegral_indicator_one (hB t)).symm
  rw [he]
  apply lintegral_congr
  intro ω
  rw [tsum_eq_sum (s := range (T ω))]
  · exact sum_congr rfl (fun t ht => by
      have h : t < T ω := mem_range.mp ht
      have heq : ω ∈ B t ↔ ω ∈ A t := and_iff_right h
      by_cases hm : ω ∈ A t
      · rw [indicator_of_mem (heq.mpr hm), indicator_of_mem hm]
      · rw [indicator_of_notMem (mt heq.mp hm), indicator_of_notMem hm])
  · intro t ht
    exact indicator_of_notMem (fun hw => ht (mem_range.mpr hw.1)) _

/-- Truncate each record interval at duration `u`. The expected number of visits
at diameter at least `x` before the first regeneration is bounded by `u` times
the expected number of record intervals with an exceedance, plus the sum of the
duration tails above `u` over those levels before the first regeneration. -/
theorem first_regeneration_diameter_occupation_le
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (x : ℝ) (u : ℕ) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let X := posPath (N := N) p m
    (∑' t : ℕ, μstar {U | t < firstTime p m U ∧ x ≤ pathDiameter t (X U)}) ≤
      (u : ℝ≥0∞) * (∑' r : ℕ, μstar {U | r < D U ∧ recordIntervalExceeds (X U) r x}) +
      ∑' r : ℕ, ∑' v : ℕ, μstar {U | r < D U ∧ ((u + v : ℕ) : ℕ∞) < recordDuration (X U) r} := by
  classical
  dsimp only
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let D := firstLevel (N := N) p m
  let X := posPath (N := N) p m
  let B (r : ℕ) := {U | r < D U ∧ recordIntervalExceeds (X U) r x}
  let C (r v : ℕ) := {U | r < D U ∧ ((u + v : ℕ) : ℕ∞) < recordDuration (X U) r}
  let f (r : ℕ) := (B r).indicator (fun _ => (1 : ℝ≥0∞))
  let g (r v : ℕ) := (C r v).indicator (fun _ => (1 : ℝ≥0∞))
  have hD := measurable_firstLevel (N := N) p m
  have hX := measurable_posPath p m N
  have hB (r : ℕ) : MeasurableSet (B r) :=
    (measurableSet_Ioi.preimage hD).inter (hX (measurableSet_recordIntervalExceeds r x))
  have hC (r v : ℕ) : MeasurableSet (C r v) :=
    (measurableSet_Ioi.preimage hD).inter
      (((measurable_recordDuration r).comp hX)
        (MeasurableSet.of_discrete (s := Ioi ((u + v : ℕ) : ℕ∞))))
  have hf (r : ℕ) : Measurable (f r) := measurable_const.indicator (hB r)
  have hg (r v : ℕ) : Measurable (g r v) := measurable_const.indicator (hC r v)
  have htime := measurable_firstTime (N := N) p m
  have hΔ (t : ℕ) : MeasurableSet {U | x ≤ pathDiameter t (X U)} :=
    ((measurable_pathDiameter t).comp hX) measurableSet_Ici
  change (∑' t : ℕ, μstar {U | t < firstTime p m U ∧ x ≤ pathDiameter t (X U)}) ≤
    (u : ℝ≥0∞) * (∑' r, μstar (B r)) + ∑' r, ∑' v, μstar (C r v)
  have hcount := tsum_measure_before_eq_lintegral_count μstar htime _ hΔ
  change (∑' t : ℕ, μstar {U | t < firstTime p m U ∧ x ≤ pathDiameter t (X U)}) = _ at hcount
  rw [hcount]
  have hraw : ∀ᵐ U ∂μstar, RegenPath.D (X U) ≠ ⊤ :=
    (ProbabilityTheory.cond_absolutelyContinuous : μstar ≪ arrayMeasure N).ae_le
      (ae_first_regeneration_finite hp₀ hp₁ hm hN)
  have hbound : (∫⁻ U, ∑ t ∈ range (firstTime p m U),
      ({V | x ≤ pathDiameter t (X V)} : Set (Array N)).indicator (fun _ => (1 : ℝ≥0∞)) U ∂μstar) ≤
      ∫⁻ U, (u : ℝ≥0∞) * (∑' r, f r U) + ∑' r, ∑' v, g r v U ∂μstar := by
    apply lintegral_mono_ae
    filter_upwards [hraw] with U hU
    obtain ⟨d, t, hd, hlevel, ht⟩ := (D_ne_top_iff_exists_firstBlock _).mp hU
    let q : LevelTime := ⟨(d, t), hd⟩
    have hN₀ : 0 < N := by omega
    have hcell := (rawFirstCell_univ_iff_D_tau p m q hN₀ U).mpr ⟨hlevel, ht⟩
    have hD' : D U = d := firstLevel_eq_of_rawFirstCell p m q hN₀ hcell
    have hT' : firstTime p m U = t := firstTime_eq_of_rawFirstCell p m q hN₀ hcell
    have hmono := recordTime_mono (posPath_zero p m U) (posPath_step p m U)
    have hclock : recordTime (X U) d = (t : ℕ∞) := ht
    have hfin (r : ℕ) (hr : r < d) : recordDuration (X U) r ≠ ⊤ := by
      have hs : recordTime (X U) (r + 1) ≠ ⊤ :=
        ne_top_of_le_ne_top (hclock ▸ ENat.natCast_ne_top t) (hmono (by omega))
      rw [recordDuration]
      exact ne_top_of_le_ne_top hs tsub_le_self
    rw [hT']
    calc
      _ = ∑ j ∈ range t, (Ici x).indicator (fun _ => (1 : ℝ≥0∞)) (pathDiameter j (X U)) := by
        apply sum_congr rfl
        intro j _
        by_cases he : x ≤ pathDiameter j (X U) <;> simp [he]
      _ ≤ _ := visitCount_le x u (recordTime_zero (posPath_zero p m U)) hmono hclock
      _ = _ := by
        rw [tsum_eq_sum (s := range d) (f := fun r => f r U), mul_sum,
          tsum_eq_sum (s := range d) (f := fun r => ∑' v, g r v U), ← sum_add_distrib]
        · apply sum_congr rfl
          intro r hr
          have hr' : r < d := mem_range.mp hr
          have hW := ENat.natCast_toNat (hfin r hr')
          rw [tsum_eq_sum (s := range ((recordDuration (X U) r).toNat - u))]
          · have hfg : (∑ v ∈ range ((recordDuration (X U) r).toNat - u), g r v U) =
                (((recordDuration (X U) r).toNat - u : ℕ) : ℝ≥0∞) := by
              calc
                _ = ∑ _ ∈ range ((recordDuration (X U) r).toNat - u), (1 : ℝ≥0∞) := by
                  apply sum_congr rfl
                  intro v hv
                  have hv' := mem_range.mp hv
                  have hc : U ∈ C r v := by
                    refine ⟨hD'.symm ▸ hr', ?_⟩
                    rw [← hW, ENat.natCast_lt_natCast]
                    omega
                  exact indicator_of_mem hc _
                _ = _ := by simp
            rw [hfg]
            by_cases he : recordIntervalExceeds (X U) r x <;> simp [f, B, hD', hr', he]
          · intro v hv
            apply indicator_of_notMem
            intro hc
            have hw := hc.2
            rw [← hW, ENat.natCast_lt_natCast] at hw
            exact hv (mem_range.mpr (by omega))
        · intro r hr
          have hr' : ¬r < d := fun h => hr (mem_range.mpr h)
          simp [g, C, hD', hr']
        · intro r hr
          have hr' : ¬r < d := fun h => hr (mem_range.mpr h)
          simp [f, B, hD', hr']
  refine hbound.trans_eq ?_
  have hmul : Measurable (fun U => (u : ℝ≥0∞) * (∑' r, f r U)) :=
    measurable_const.mul (Measurable.tsum hf)
  rw [lintegral_add_left hmul (fun U => ∑' r, ∑' v, g r v U), lintegral_const_mul _ (Measurable.tsum hf),
    lintegral_tsum (fun r => (hf r).aemeasurable),
    lintegral_tsum (fun r => (Measurable.tsum (hg r)).aemeasurable)]
  congr 1
  · congr 1
    exact tsum_congr (fun r => lintegral_indicator_one (hB r))
  · exact tsum_congr fun r => by
      rw [lintegral_tsum (fun v => (hg r v).aemeasurable)]
      exact tsum_congr (fun v => lintegral_indicator_one (hC r v))

private theorem tsum_measure_before_eq_mul_limsup
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : Ω → ℕ} (hD : Measurable D) (A : ℕ → Set Ω) (hA : ∀ r, MeasurableSet (A r))
    (q : ℕ → ℝ)
    (hpos : 0 < (∫⁻ ω, (D ω : ℝ≥0∞) ∂μ).toReal)
    (hfin : (∫⁻ ω, (D ω : ℝ≥0∞) ∂μ) ≠ ∞)
    (hlim : Tendsto q atTop
      (𝓝 ((∑' r : ℕ, μ.real {ω | r < D ω ∧ ω ∈ A r}) / (∫⁻ ω, (D ω : ℝ≥0∞) ∂μ).toReal))) :
    (∑' r : ℕ, μ {ω | r < D ω ∧ ω ∈ A r}) =
      (∫⁻ ω, (D ω : ℝ≥0∞) ∂μ) * ENNReal.ofReal (limsup q atTop) := by
  let b := ∫⁻ ω, (D ω : ℝ≥0∞) ∂μ
  let B (r : ℕ) := {ω | r < D ω ∧ ω ∈ A r}
  let a := ∑' r : ℕ, μ (B r)
  have ha : a ≠ ∞ := by
    apply ne_top_of_le_ne_top hfin
    change (∑' r : ℕ, μ (B r)) ≤ b
    rw [tsum_measure_before_eq_lintegral_count μ hD A hA]
    apply lintegral_mono
    intro ω
    calc
      _ ≤ ∑ _ ∈ range (D ω), (1 : ℝ≥0∞) :=
        sum_le_sum fun r _ => indicator_le_self' (fun _ _ => zero_le) ω
      _ = _ := by simp
  have he : limsup q atTop = a.toReal / b.toReal := by
    rw [hlim.limsup_eq]
    congr 1
    exact (ENNReal.tsum_toReal_eq (fun r => measure_ne_top μ (B r))).symm
  change a = b * ENNReal.ofReal (limsup q atTop)
  calc
    a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ = ENNReal.ofReal (b.toReal * limsup q atTop) := by
      rw [he, mul_comm b.toReal, div_mul_cancel₀ _ hpos.ne']
    _ = _ := by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

/-- An upper bound for the expected visit count, expressed entirely in terms
of the record probabilities under the original law and the mean first
regeneration level under the law conditioned on strict positivity. -/
theorem first_regeneration_diameter_occupation_le_record_limsup
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (x : ℝ) (u : ℕ) :
    let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
    let D := firstLevel (N := N) p m
    let X := posPath (N := N) p m
    (∑' t : ℕ, μstar {U | t < firstTime p m U ∧ x ≤ pathDiameter t (X U)}) ≤
      (∫⁻ U, (D U : ℝ≥0∞) ∂μstar) *
        ((u : ℝ≥0∞) * ENNReal.ofReal
          (limsup (fun r => (arrayMeasure N).real {U | recordIntervalExceeds (X U) r x}) atTop) +
          ∑' v : ℕ, ENNReal.ofReal (limsup
            (fun r => (arrayMeasure N).real {U | ((u + v : ℕ) : ℕ∞) < recordDuration (X U) r}) atTop)) := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let D := firstLevel (N := N) p m
  let X := posPath (N := N) p m
  let b := ∫⁻ U, (D U : ℝ≥0∞) ∂μstar
  have hD := measurable_firstLevel (N := N) p m
  have hX := measurable_posPath p m N
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure
    (SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN)
  let B (r : ℕ) := {U | recordIntervalExceeds (X U) r x}
  let C (r v : ℕ) := {U | ((u + v : ℕ) : ℕ∞) < recordDuration (X U) r}
  let q (r : ℕ) := (arrayMeasure N).real (B r)
  let q' (v r : ℕ) := (arrayMeasure N).real (C r v)
  obtain ⟨hb₀, hb, hlim⟩ := tendsto_record_interval_exceedance_occupation (N := N) hp₀ hp₁ hm hN x
  have hB (r : ℕ) : MeasurableSet (B r) := hX (measurableSet_recordIntervalExceeds r x)
  have hC (r v : ℕ) : MeasurableSet (C r v) :=
    ((measurable_recordDuration r).comp hX)
      (MeasurableSet.of_discrete (s := Ioi ((u + v : ℕ) : ℕ∞)))
  have he := tsum_measure_before_eq_mul_limsup μstar hD B hB q hb₀ hb hlim
  have he' (v : ℕ) := tsum_measure_before_eq_mul_limsup μstar hD (fun r => C r v)
    (fun r => hC r v) (q' v) hb₀ hb
    (tendsto_record_duration_tail_occupation (N := N) hp₀ hp₁ hm hN (u + v)).2.2
  refine (first_regeneration_diameter_occupation_le (N := N) hp₀ hp₁ hm hN x u).trans_eq ?_
  change (u : ℝ≥0∞) * (∑' r, μstar {U | r < D U ∧ U ∈ B r}) +
    (∑' r, ∑' v, μstar {U | r < D U ∧ U ∈ C r v}) =
    b * ((u : ℝ≥0∞) * ENNReal.ofReal (limsup q atTop) +
      ∑' v, ENNReal.ofReal (limsup (q' v) atTop))
  have hsum : (∑' r, ∑' v, μstar {U | r < D U ∧ U ∈ C r v}) =
      b * ∑' v, ENNReal.ofReal (limsup (q' v) atTop) := by
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
    exact tsum_congr he'
  rw [he, hsum, mul_add, mul_left_comm (u : ℝ≥0∞) b]

end Swarming.Diameter
