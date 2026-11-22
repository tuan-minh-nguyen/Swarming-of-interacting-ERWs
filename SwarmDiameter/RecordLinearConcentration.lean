import SwarmDiameter.RecordLinearClauses
import SwarmDiameter.LinearCutoff
import SwarmDiameter.BoundedGroupMeasurable
import SwarmDiameter.MinimumProgress

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl Swarming.Trajectory SwarmRecordMeas.Actual
open SepGroup.Model PaperBlock LocSum LocSumAct

namespace Swarming.Diameter

set_option autoImplicit false

private theorem measureReal_iUnion_le_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → Set Ω} {a : ℝ}
    (hE : ∀ i, μ.real (E i) ≤ a) : μ.real (⋃ i, E i) ≤ (Fintype.card ι : ℝ) * a := by
  refine (measureReal_iUnion_fintype_le E).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hE i))

private theorem card_recordSpatialInterval_le {r T L : ℕ} (hL : 1 ≤ L)
    (hr : (T + 3) * L ≤ r) :
    ((Finset.Icc (recordSpatialLo r T L : ℤ) (recordSpatialHi r T L : ℤ)).card : ℝ) ≤
      (2 * (T : ℝ) + 5) * L := by
  have hwidth := recordSpatialWidth hr
  have hle := recordSpatialLo_le_hi r T L
  have he : ((recordSpatialHi r T L : ℤ) + 1 - recordSpatialLo r T L).toNat =
      (2 * T + 4) * L + 1 := by omega
  rw [Int.card_Icc, he]
  push_cast
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith only [hL']

/-- On the record carrier, the position comparison and meeting estimates
hold simultaneously with exponential probability for each fixed error tolerance. -/
theorem record_linear_clauses_failure_le_exp {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hmN : m < N)
    (T : ℕ) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
        ¬ LinearBlockClauses (Xa p m U) (tauA p m U) r T L (linearPositionConstant p m N)
          (linearMinimumSpeed p N) (ε * (L : ℝ))}) ≤ K * Real.exp (-c * (L : ℝ)) := by
  classical
  have hN : 2 ≤ N := hm.trans hmN.le
  have hN₀ : 0 < N := by omega
  have hm₁ : 1 ≤ m := by omega
  let D := linearErrorFactor p m N T
  have hD : 0 < D := by
    have hd := linearStrictRate_pos hp₀ hp₁ m hN₀
    have hv := linearMinimumSpeed_pos hp₀ hN₀
    unfold D linearErrorFactor
    positivity
  let a := min 1 (ε / D)
  have ha : 0 < a := lt_min zero_lt_one (div_pos hε hD)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have hDa : D * a ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hD).mp (min_le_right _ _)
  obtain ⟨δ, cO, hδ, hcO, hO⟩ := record_small_set_minimum_occupation_failure_le_exp
    hp₀ hp₁ hmN T hT (D := 2 * (T : ℝ) + 5) (by positivity) ha
  obtain ⟨k, θ, hk, hθ, hpK, hθK, hpar, hrare⟩ := exists_linearCutoff hp₀ hp₁ m N T ha ha₁ hδ
  let K := 8 * (k : ℝ)
  let H := 4 * (N : ℝ) * (2 * ((k ^ 3 : ℕ) : ℝ) + 3)
  have hH : 0 < H := by unfold H; positivity
  let η := δ / (2 * H)
  have hη : 0 < η := by unfold η; positivity
  have hK : 1 ≤ K := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    unfold K
    linarith only [hk']
  obtain ⟨cQ, hcQ, hQ⟩ := record_spatial_bounds_failure_le_exp (N := N) hp₀ hp₁ m hk T
    (show 0 < a / 10 by positivity) hη
  obtain ⟨cM, hcM, hM⟩ := record_minimum_progress_failure_le_exp hp₀ hp₁ hm hmN T hT ha
  obtain ⟨cD, hcD, hDown⟩ := record_drift_martingale_failure_le_exp hp₀ hp₁ hm hN T hT ha
  obtain ⟨cW, hcW, hW⟩ := record_weighted_jump_failure_le_exp (N := N) hp₀ hp₁ m T hT
    (B := 2 * K) (by positivity) ha
  obtain ⟨cR, hcR, hR⟩ := recordTrialBad_le_exp (N := N) hp₀.le hp₁ (by omega : 0 < m) T ha
  let c := min cQ (min cM (min cD (min cO (min cW cR))))
  have hc := lt_min hcQ (lt_min hcM (lt_min hcD (lt_min hcO (lt_min hcW hcR))))
  let G := {J : Finset (Fin N) // J.Nonempty}
  let K' := 4 * (N : ℝ) + (Fintype.card G : ℝ) + (Fintype.card (G × G) : ℝ) + 1
  have hK' : 0 < K' := by unfold K'; positivity
  refine ⟨K', c, hK', hc, ?_⟩
  have htop := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := htop.eventually_ge_atTop ((Real.log (N : ℝ) / θ) / a)
  have hlarge := htop.eventually_ge_atTop (2 * (m : ℝ) / a)
  filter_upwards [eventually_ge_atTop k, hlog, hlarge, hQ, hM, hDown, hO, hW, hR]
    with L hkL hlogL hlargeL hQL hML hDL hOL hWL hRL
  intro r hr
  have hL := hk.trans hkL
  have hlog' : Real.log (N : ℝ) / θ ≤ a * (L : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ ha).mp hlogL
  have hlarge' : 2 * (m : ℝ) ≤ a * (L : ℝ) := by
    simpa only [mul_comm (L : ℝ) a] using (div_le_iff₀ ha).mp hlargeL
  let μ := arrayMeasure N
  let F := RecClockLG.recordCarrier (N := N) p m r L
  let σ (U : Array N) := recTimeA p m U r
  let I := Finset.Icc (recordSpatialLo r T L : ℤ) (recordSpatialHi r T L : ℤ)
  let E_Q : Set (Array N) := {U | ¬ RecordSpatialBounds p m k r T L U (a / 10) η}
  let E_M : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      (RecordDefect.runMin (Xa p m U) t : ℝ) <
        (RecordDefect.runMin (Xa p m U) s : ℝ) + linearMinimumSpeed p N * ((t : ℝ) - s) - a * (L : ℝ)}
  let E_D (i : Fin N) := RecordClock.stoppedWindowRec p m r (T * L) (a * L) i
  let E_O (g : G) := ⋃ S ∈ (I.powerset.filter fun S => (S.card : ℝ) ≤ δ * (L : ℝ)),
    recordMinimumOccupationBad p m r L T g.1 g.2 S (a * (L : ℝ))
  let E_W (g : G × G) : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      a * (L : ℝ) ≤ |∑ u ∈ Finset.Ico s t, weightedJump p m (boundedGroupCoeff p K θ m g.1.1 g.2.1) u U|}
  let E_R := recordTrialBad N p m (r : ℤ) T L a
  have hcover : F ∩ {U |
      ¬ LinearBlockClauses (Xa p m U) (tauA p m U) r T L (linearPositionConstant p m N)
        (linearMinimumSpeed p N) (ε * (L : ℝ))} ⊆
      E_Q ∪ (E_M ∪ ((⋃ i, E_D i) ∪ ((⋃ g, E_O g) ∪ ((⋃ g, E_W g) ∪ E_R)))) := by
    rintro U ⟨hU, hbad⟩
    by_contra hn
    apply hbad
    simp only [Set.mem_union, not_or] at hn
    have hQ' : RecordSpatialBounds p m k r T L U (a / 10) η := by
      by_contra h
      exact hn.1 h
    let S := boundedExceptionSites p m k (k ^ 3) (recordSpatialLo r T L) (recordSpatialHi r T L) U
    have hScard : (S.card : ℝ) ≤ δ * (L : ℝ) := by
      have hbound := card_boundedExceptionSites_le (ℓ := k ^ 3) hQ'.product
      have hηH : H * η = δ / 2 := by unfold η; field_simp
      change (S.card : ℝ) ≤ H * (_ + _) at hbound
      have hrareL := mul_le_mul_of_nonneg_right hrare (Nat.cast_nonneg (α := ℝ) L)
      change H * (bC p (qOf p m)) ^ k * ((2 * T + 4 : ℕ) : ℝ) * (L : ℝ) ≤ _ at hrareL
      nlinarith only [hbound, hrareL, congrArg (fun x : ℝ => x * (L : ℝ)) hηH]
    have hS : S ∈ I.powerset.filter (fun S => (S.card : ℝ) ≤ δ * (L : ℝ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (boundedExceptionSites_subset p m k (k ^ 3) _ _ U), hScard⟩
    have hinput : LinearRecordInputs p m k r T L U θ a η := by
      refine ⟨hQ', ?_, ?_, ?_, ?_, ?_⟩
      · intro s t hs hst ht
        by_contra! hb
        exact hn.2.1 ⟨hU, s, t, hs, hst, ht, hb⟩
      · intro i s t hs hst ht
        have hb : |driftMartingale p m U t i - driftMartingale p m U s i| ≤ a * (L : ℝ) := by
          by_contra! hb
          exact hn.2.2.1 (Set.mem_iUnion.mpr ⟨i, ClockLocMove.mem_stoppedWindow_of_pair
            (Q := fun n U => driftMartingale p m U n i) hs hst ht hb.le⟩)
        rw [M1DMart.Xa_excitedSteps_martingaleEq, M1DMart.Xa_excitedSteps_martingaleEq, abs_le] at hb
        have he : (excitedSteps p m U s i : ℝ) ≤ excitedSteps p m U t i := by
          exact_mod_cast M1DMart.monotone_excitedSteps p m U i hst
        have hμ : 0 ≤ 2 * p - 1 := by linarith
        change (Xa p m U i s : ℝ) - Xa p m U i t ≤ _
        nlinarith only [hb.1, mul_le_mul_of_nonneg_left he hμ]
      · intro J hJ hmem
        exact hn.2.2.2.1 (Set.mem_iUnion.mpr ⟨⟨J, hJ⟩,
          Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hmem⟩⟩⟩)
      · intro I J hI hJ s t hs hst ht
        by_contra! hb
        exact hn.2.2.2.2.1 (Set.mem_iUnion.mpr ⟨(⟨I, hI⟩, ⟨J, hJ⟩), hU, s, t, hs, hst, ht, hb.le⟩)
      · exact hn.2.2.2.2.2
    exact (linearBlockClauses_of_inputs hp₀ hp₁ hm₁ hN₀ hL hr hk hkL ha.le hθ hpK hθK hpar
      hlog' hlarge' hU hinput).mono_error (mul_le_mul_of_nonneg_right hDa (Nat.cast_nonneg L))
  let e (b : ℝ) := Real.exp (-b * (L : ℝ))
  have he {b : ℝ} (h : c ≤ b) : e b ≤ e c := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg h) (Nat.cast_nonneg _)
  have hcQ' : c ≤ cQ := min_le_left _ _
  have hcM' : c ≤ cM := (min_le_right _ _).trans (min_le_left _ _)
  have hcD' : c ≤ cD := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcO' : c ≤ cO := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hcW' : c ≤ cW := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hcR' : c ≤ cR := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hQ'' : μ.real E_Q ≤ 2 * (N : ℝ) * e c :=
    (hQL r hr).trans (mul_le_mul_of_nonneg_left (he hcQ') (by positivity))
  have hM'' : μ.real E_M ≤ (N : ℝ) * e c :=
    (hML r hr).trans (mul_le_mul_of_nonneg_left (he hcM') (by positivity))
  have hD'' : μ.real (⋃ i, E_D i) ≤ (N : ℝ) * e c := by
    simpa only [Fintype.card_fin] using (measureReal_iUnion_le_mul (E := E_D) fun i =>
      (hDL r i).trans (he hcD'))
  have hO'' : μ.real (⋃ g, E_O g) ≤ (Fintype.card G : ℝ) * e c :=
    measureReal_iUnion_le_mul fun g =>
      (hOL r g.1 g.2 I (card_recordSpatialInterval_le hL hr)).trans (he hcO')
  have hW'' : μ.real (⋃ g, E_W g) ≤ (Fintype.card (G × G) : ℝ) * e c :=
    measureReal_iUnion_le_mul fun g =>
      (hWL r (boundedGroupCoeff p K θ m g.1.1 g.2.1) (measurable_boundedGroupCoeff p K θ m g.1.1 g.2.1)
        (abs_boundedGroupCoeff_le hp₀.le hp₁.le hK θ m g.1.1 g.2.1 g.1.2 g.2.2)).trans (he hcW')
  have hR'' : μ.real E_R ≤ e c := (hRL r hr).trans (he hcR')
  have hWR := (measureReal_union_le (μ := μ) (⋃ g, E_W g) E_R).trans (add_le_add hW'' hR'')
  have hOWR := (measureReal_union_le (μ := μ) (⋃ g, E_O g) _).trans (add_le_add hO'' hWR)
  have hDOWR := (measureReal_union_le (μ := μ) (⋃ i, E_D i) _).trans (add_le_add hD'' hOWR)
  have hMDOWR := (measureReal_union_le (μ := μ) E_M _).trans (add_le_add hM'' hDOWR)
  have hall := (measureReal_union_le (μ := μ) E_Q _).trans (add_le_add hQ'' hMDOWR)
  refine (measureReal_mono hcover).trans (hall.trans_eq ?_)
  change _ = K' * e c
  unfold K'
  ring

end Swarming.Diameter
