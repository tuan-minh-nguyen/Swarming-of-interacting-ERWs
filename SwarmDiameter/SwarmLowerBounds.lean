import SwarmDiameter.LinearTrial
import SwarmDiameter.MaxGrowth
import SwarmDiameter.RecordDensity
import SwarmDiameter.SwarmRenewal
import SwarmDiameter.TailBounds
import SwarmDiameter.TwoWalkerTrial

open Filter Finset MeasureTheory Set
open Swarming.Enl Swarming.Uniform SwarmRestart
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ} [Nonempty (Fin N)]

private abbrev recordEvent (p : ℝ) (m N t : ℕ) : Set (Array N) :=
  {U | ∃ r : ℕ, RecordAt p m U t (r : ℤ)}

omit [Nonempty (Fin N)] in
private theorem recordTimes_eq (n : ℕ) (U : Array N) :
    recordTimes (recordEvent p m N) 0 n U = simultaneousRecordTimes (posPath p m U) n := by
  ext t
  rw [mem_recordTimes, mem_simultaneousRecordTimes]
  simp only [zero_le, true_and]
  rfl

private theorem measurable_diameter_enl (t : ℕ) :
    Measurable[enlMeas p m t] (fun U : Array N => pathDiameter t (posPath p m U)) := by
  let _ : MeasurableSpace (Array N) := enlMeas p m t
  have hX : Measurable[enlMeas p m t] (fun U : Array N => posPath p m U t) :=
    measurable_pi_iff.mpr (fun i => enl_pos_measurable p m t le_rfl i)
  exact (measurable_of_countable (fun f : Fin N → ℤ => pathDiameter 0 (fun _ => f))).comp hX

private theorem ae_log_pow_lower_of_swarm_trials
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (β : ℕ) {C P : ℝ} (hC : 0 < C) (hP : 0 < P) (L₀ : ℕ)
    (d : ℕ → ℕ) (hd₀ : ∀ L ≥ L₀, 0 < d L) (hd : ∀ L ≥ L₀, (d L : ℝ) ≤ P * (L : ℝ) ^ 3)
    (htrial : ∀ L ≥ L₀, ∀ t {G}, MeasurableSet[enlMeas p m t] G →
      G ⊆ recordEvent p m N t → Real.exp (-C * (L : ℝ)) * (arrayMeasure N).real G ≤
        (arrayMeasure N).real (G ∩ {U | (L : ℝ) ^ β ≤ pathDiameter (t + d L) (posPath p m U)})) :
    ∃ a : ℝ, 0 < a ∧ ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
      a * (Real.log (n : ℝ)) ^ β ≤ runningDiameter n (posPath p m U) := by
  obtain ⟨ρ, hρ, _, hρraw⟩ := exists_positive_simultaneousRecordDensity hp₀ hp₁ hm hN
  have hρ' : ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
      ρ * (n : ℝ) ≤ (recordTimes (recordEvent p m N) 0 n U).card := by
    simpa only [recordTimes_eq] using hρraw
  refine ae_log_pow_lower_of_record_trials (μ := arrayMeasure N) (ℱ := enlFilt p m)
    (fun t => measurableSet_simultaneousRecordAt_enl p m t) hρ hρ'
    measurable_diameter_enl (fun n k U h => runningDiameter_mono h (posPath p m U))
    (fun n U => pathDiameter_le_runningDiameter (t := n) le_rfl (posPath p m U))
    β (a := 1) one_pos hC hP L₀ d hd₀ hd ?_
  intro L hL t G hG hsub
  simpa only [one_mul] using htrial L hL t hG hsub

/-- The almost sure lower bound in Theorem 1.2 for two walkers or for a threshold
below the population. -/
theorem ae_log_pow_lower_of_two_or_lt
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (hregime : N = 2 ∨ m < N) :
    let β : ℕ := if N = 2 then 2 else 1
    ∃ a : ℝ, 0 < a ∧ ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
      a * (Real.log (n : ℝ)) ^ β ≤ runningDiameter n (posPath p m U) := by
  have hp : 0 < 1 - p := by linarith
  have hlog : Real.log (1 - p) < 0 := Real.log_neg hp (by linarith)
  rcases hregime with htwo | hlt
  · subst N
    apply ae_log_pow_lower_of_swarm_trials hp₀ hp₁ hm hN 2
      (C := 16 - 8 * Real.log (1 - p)) (P := 5) (by linarith) (by norm_num) 8 (fun L => 4 * L + L ^ 3)
    · intro L hL
      positivity
    · intro L hL
      have h₁ : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
      have h : (L : ℝ) ≤ (L : ℝ) ^ (3 : ℕ) := by
        simpa only [pow_one] using pow_le_pow_right₀ h₁ (by decide : (1 : ℕ) ≤ 3)
      push_cast
      linarith
    · intro L hL t G hG hsub
      have h := two_walker_exp_trial_mass_ge hp₀ hp₁ hm t hL hG (fun U hU => by
        obtain ⟨r, hr⟩ := hsub hU
        exact ⟨r, hr⟩)
      apply h.trans (measureReal_mono ?_ (measure_ne_top _ _))
      rintro U ⟨hU, hD⟩
      exact ⟨hU, (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) L)).trans hD⟩
  · have hne : N ≠ 2 := by omega
    simp only [if_neg hne]
    apply ae_log_pow_lower_of_swarm_trials hp₀ hp₁ hm hN 1
      (C := -2 * Real.log (1 - p)) (P := 1) (by linarith) one_pos 1 id
    · intro L hL
      exact zero_lt_one.trans_le hL
    · intro L hL
      have h₁ : (1 : ℝ) ≤ L := by exact_mod_cast hL
      simpa only [id_eq, one_mul, pow_one] using pow_le_pow_right₀ h₁ (by decide : (1 : ℕ) ≤ 3)
    · intro L _ t G hG hsub
      have h := linear_trial_mass_ge hp₀.le hp₁ hN t L hG (fun U hU i j => by
        obtain ⟨r, hr⟩ := hsub hU
        exact (hr.2 i).trans (hr.2 j).symm)
      have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.le] at h'
      have he : (1 - p) ^ (L * 2) = Real.exp (-(-2 * Real.log (1 - p)) * (L : ℝ)) := by
        rw [show -(-2 * Real.log (1 - p)) * (L : ℝ) = (↑(L * 2 : ℕ) : ℝ) * Real.log (1 - p)
          by push_cast; ring, Real.exp_nat_mul, Real.exp_log hp]
      rw [he] at h'
      apply h'.trans (measureReal_mono ?_ (measure_ne_top _ _))
      rintro U ⟨hU, hD⟩
      refine ⟨hU, ?_⟩
      change (L : ℝ) ^ (1 : ℕ) ≤ pathDiameter (t + L) (posPath p m U)
      change 2 * (L : ℝ) ≤ pathDiameter (t + L) (posPath p m U) at hD
      rw [pow_one]
      linarith [Nat.cast_nonneg (α := ℝ) L]

/-- The lower bounds for the running maximum and the limiting tail in the
two-walker and below-population regimes. The two bounds share one constant. -/
theorem exists_diameter_lower_bounds_of_two_or_lt
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N) (hregime : N = 2 ∨ m < N) :
    let β : ℕ := if N = 2 then 2 else 1
    let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
    ∃ (C : ℝ) (ν : ProbabilityMeasure ℝ), 1 ≤ C ∧
      (∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
        C⁻¹ * (Real.log (n : ℝ)) ^ β ≤ runningDiameter n (posPath p m U)) ∧
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution Δ atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, Real.exp (-C * x ^ (1 / (β : ℝ))) ≤ ν.toMeasure.real (Set.Ici x) := by
  let β : ℕ := if N = 2 then 2 else 1
  let Δ := fun n (U : Array N) => pathDiameter n (posPath p m U)
  let M := fun n (U : Array N) => runningDiameter n (posPath p m U)
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  have hV : arrayMeasure N (SwarmFB.seedSet (p := p) (m := m) (N := N)) ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure hV
  obtain ⟨a, ha, hlow⟩ := ae_log_pow_lower_of_two_or_lt hp₀ hp₁ hm hN hregime
  obtain ⟨ν, hnonneg, hweak, hformula⟩ := exists_diameter_occupationLaw hp₀ hp₁ hm hN
  let K := (∫⁻ U, (↑(RawStrictTransport.firstTime p m U) : ℝ≥0∞) ∂μstar).toReal
  have hK : 0 < K := by
    by_contra! hk
    have he : K = 0 := le_antisymm hk ENNReal.toReal_nonneg
    have h := (hformula Set.univ MeasurableSet.univ).1
    change ν.toMeasure.real Set.univ = _ / K at h
    rw [probReal_univ, he, div_zero] at h
    exact one_ne_zero h
  have hM (n : ℕ) : Measurable (M n) := (measurable_runningDiameter n).comp
    (measurable_posPath p m N)
  have hβ : 0 < β := by dsimp only [β]; split_ifs <;> decide
  have hprob (x : ℝ) (n : ℕ) : μstar.real {U | x ≤ M n U} ≤
      ((n : ℝ) + 1) * (K * ν.toMeasure.real (Set.Ici x)) := by
    have hs : {U | x ≤ M n U} = {U | ∃ t ≤ n, Δ t U ∈ Set.Ici x} := by
      ext U
      exact le_runningDiameter_iff n (posPath p m U)
    rw [hs]
    obtain ⟨he, _, _, hb⟩ := hformula (Set.Ici x) measurableSet_Ici
    rw [show K * ν.toMeasure.real (Set.Ici x) =
        ∑' t : ℕ, μstar.real {U | t < RawStrictTransport.firstTime p m U ∧ Δ t U ∈ Set.Ici x} by
      have h' := (eq_div_iff hK.ne').mp he
      simpa only [mul_comm] using h']
    exact hb n
  have hac : μstar ≪ arrayMeasure N := ProbabilityTheory.cond_absolutelyContinuous
  obtain ⟨c, hc, ht⟩ := eventually_exp_le_of_ae_log_pow_lower (μ := μstar) hβ ha hM (hac.ae_le hlow) hprob
  let C := max 1 (max a⁻¹ (c + max 0 (Real.log K)))
  have hC : 1 ≤ C := le_max_left _ _
  have hCa : a⁻¹ ≤ C := (le_max_left a⁻¹ _).trans (le_max_right 1 _)
  have hCc : c + max 0 (Real.log K) ≤ C := (le_max_right a⁻¹ _).trans (le_max_right 1 _)
  refine ⟨C, ν, hC, ?_, hnonneg, hweak, ?_⟩
  · filter_upwards [hlow] with U hU
    filter_upwards [hU, eventually_ge_atTop (1 : ℕ)] with n hn hn₁
    have hc₀ : 0 < C := zero_lt_one.trans_le hC
    have ha' : C⁻¹ ≤ a := by
      apply (inv_le_iff_one_le_mul₀ hc₀).mpr
      have hmul := mul_le_mul_of_nonneg_right hCa ha.le
      rw [inv_mul_cancel₀ ha.ne'] at hmul
      simpa only [mul_comm] using hmul
    have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn₁)
    exact (mul_le_mul_of_nonneg_right ha' (pow_nonneg hlog₀ _)).trans hn
  · let r : ℝ := 1 / (β : ℝ)
    have hr : 0 < r := by positivity
    filter_upwards [ht, (tendsto_rpow_atTop hr).eventually_ge_atTop 1] with x hx hx₁
    change (1 : ℝ) ≤ x ^ r at hx₁
    have hKc : Real.log K ≤ (C - c) * x ^ r := by
      calc
        _ ≤ max 0 (Real.log K) := le_max_right _ _
        _ ≤ max 0 (Real.log K) * x ^ r := le_mul_of_one_le_right (le_max_left _ _) hx₁
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hx₁)
    apply (mul_le_mul_iff_of_pos_left hK).mp
    calc
      _ = Real.exp (Real.log K - C * x ^ r) := by
        rw [show Real.log K - C * x ^ r = Real.log K + (-C * x ^ r) by ring,
          Real.exp_add, Real.exp_log hK]
      _ ≤ Real.exp (-c * x ^ r) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := hx

end Swarming.Diameter
