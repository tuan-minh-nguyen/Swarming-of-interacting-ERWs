import Swarm.Imports
import Swarm.TailLevel

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace TrialTail

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Γ : ℕ → Set Ω} {ρ : ℝ} {σ : ℕ → Ω → WithTop ℕ}
variable {ℱ : ℕ → MeasurableSpace Ω} {c : ℝ}

section OneStep

variable (hle : ∀ n, ℱ n ≤ m0)
variable (Hσ : ∀ i n, MeasurableSet[ℱ n] {p | σ i p = (n : WithTop ℕ)})
variable (HΓ : ∀ i k n, i < k → MeasurableSet[ℱ n] ({p | σ k p = (n : WithTop ℕ)} ∩ Γ i))
variable (Hmass : ∀ i n (H : Set Ω), MeasurableSet[ℱ n] H →
    H ⊆ {p | σ i p = (n : WithTop ℕ)} → ENNReal.ofReal c * μ H ≤ μ (H ∩ Γ i))
variable (HGamb : ∀ i, MeasurableSet (Γ i))
variable (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)

include hle Hσ HΓ Hmass HGamb hc0 hc1 hρ0 hρ1 in
/-- **The level-wise one-step estimate.**  On the record level `{σ k = j}` the conditional
mass bound `(trialp)` improves the product weight by the factor `1 - c + c ρ`. -/
theorem one_step (k j : ℕ) :
    ∫⁻ ω in {p | σ k p = (j : WithTop ℕ)}, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ
      ≤ ENNReal.ofReal (1 - c + c * ρ) *
          ∫⁻ ω in {p | σ k p = (j : WithTop ℕ)}, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ := by
  classical
  set B : Set Ω := {p | σ k p = (j : WithTop ℕ)} with hBdef
  have hρle : 0 ≤ ρ := le_of_lt hρ0
  have hBm : MeasurableSet[ℱ j] B := Hσ k j
  have hBamb : MeasurableSet B := hle j B hBm
  have hGamb : MeasurableSet (Γ k) := HGamb k
  have hth : 0 ≤ 1 - ρ := by linarith
  -- measurability of the cut weight
  have hwmeas : Measurable[ℱ j] (levelW Γ ρ σ k j) := measurable_levelW Hσ HΓ k j
  -- the conditional mass hypothesis in the form required by `weight_lemma`
  have hge : ∀ H, MeasurableSet[ℱ j] H →
      ENNReal.ofReal c * μ (H ∩ B) ≤ μ (H ∩ (Γ k ∩ B)) := by
    intro H hH
    have hHB : MeasurableSet[ℱ j] (H ∩ B) := hH.inter hBm
    have hsub : H ∩ B ⊆ {p | σ k p = (j : WithTop ℕ)} := Set.inter_subset_right
    have h := Hmass k j (H ∩ B) hHB hsub
    have heq : (H ∩ B) ∩ Γ k = H ∩ (Γ k ∩ B) := by
      rw [Set.inter_assoc, Set.inter_comm B (Γ k)]
    rw [heq] at h
    exact h
  have hweight := weight_lemma (m := ℱ j) (hle j) (B := B) (A := Γ k ∩ B) hge hwmeas
  -- identify the cut weight with `ofReal (trialW k)` on `B`
  have hBcongr : ∫⁻ ω in B, levelW Γ ρ σ k j ω ∂μ
      = ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ :=
    setLIntegral_congr_fun hBamb fun ω hω => by
      rw [levelW_apply hρle k j ω]
      exact if_pos hω
  have hAcongr : ∫⁻ ω in (Γ k ∩ B), levelW Γ ρ σ k j ω ∂μ
      = ∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ :=
    setLIntegral_congr_fun (hGamb.inter hBamb) fun ω hω => by
      rw [levelW_apply hρle k j ω]
      exact if_pos hω.2
  rw [hBcongr, hAcongr] at hweight
  -- the pointwise decomposition of the weight
  have hpt : ∀ ω ∈ B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω)
      + ENNReal.ofReal (1 - ρ) * (Γ k).indicator (fun ω => ENNReal.ofReal (trialW Γ ρ k ω)) ω
      = ENNReal.ofReal (trialW Γ ρ k ω) := by
    intro ω _
    rw [trialW_succ, ENNReal.ofReal_mul (trialW_nonneg Γ hρle k ω)]
    by_cases hg : ω ∈ Γ k
    · rw [Set.indicator_of_mem hg, trialFac, if_pos hg]
      rw [← ENNReal.ofReal_mul (trialW_nonneg Γ hρle k ω)]
      rw [← ENNReal.ofReal_mul hth]
      rw [← ENNReal.ofReal_add (mul_nonneg (trialW_nonneg Γ hρle k ω) hρle)
        (mul_nonneg hth (trialW_nonneg Γ hρle k ω))]
      congr 1
      ring
    · rw [Set.indicator_of_notMem hg, trialFac, if_neg hg, mul_zero, add_zero,
        ENNReal.ofReal_one, mul_one]
  -- integrate the pointwise identity over `B`
  have hS : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
      = (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ)
        + ENNReal.ofReal (1 - ρ) * ∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ := by
    have hcongr : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
        = ∫⁻ ω in B, (ENNReal.ofReal (trialW Γ ρ (k + 1) ω)
            + ENNReal.ofReal (1 - ρ) *
              (Γ k).indicator (fun ω => ENNReal.ofReal (trialW Γ ρ k ω)) ω) ∂μ :=
      setLIntegral_congr_fun hBamb fun ω hω => (hpt ω hω).symm
    rw [hcongr, lintegral_add_left (measurable_ofReal_trialW HGamb hρle (k + 1))]
    rw [lintegral_const_mul]
    · rw [setLIntegral_indicator hGamb]
    · exact (Measurable.indicator (measurable_ofReal_trialW HGamb hρle k) hGamb)
  -- finiteness bounds
  have hBle : μ B ≤ 1 := by
    have := measure_mono (μ := μ) (Set.subset_univ B)
    simpa using this
  have hSle : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ ≤ 1 := by
    calc ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
        ≤ ∫⁻ _ω in B, (1 : ℝ≥0∞) ∂μ :=
          setLIntegral_mono measurable_const fun ω _ => by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (trialW_le_one Γ hρle hρ1 k ω)
      _ = μ B := by rw [setLIntegral_const, one_mul]
      _ ≤ 1 := hBle
  have hLle : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ ≤ 1 := by
    calc ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ
        ≤ ∫⁻ _ω in B, (1 : ℝ≥0∞) ∂μ :=
          setLIntegral_mono measurable_const fun ω _ => by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (trialW_le_one Γ hρle hρ1 (k + 1) ω)
      _ = μ B := by rw [setLIntegral_const, one_mul]
      _ ≤ 1 := hBle
  have hPle : ∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ ≤ 1 := by
    calc ∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ
        ≤ ∫⁻ _ω in (Γ k ∩ B), (1 : ℝ≥0∞) ∂μ :=
          setLIntegral_mono measurable_const fun ω _ => by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (trialW_le_one Γ hρle hρ1 k ω)
      _ = μ (Γ k ∩ B) := by rw [setLIntegral_const, one_mul]
      _ ≤ 1 := by
          have h := measure_mono (μ := μ) (Set.subset_univ (Γ k ∩ B))
          simpa using h
  -- toReal arithmetic
  have hSfin : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hSle
  have hLfin : ∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hLle
  have hPfin : ∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hPle
  have hSR : (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal
      = (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ).toReal
        + (1 - ρ) * (∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal := by
    rw [hS, ENNReal.toReal_add hLfin (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hPfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hth]
  have hPc : c * (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal
      ≤ (∫⁻ ω in (Γ k ∩ B), ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hSfin)
      hPfin).mpr hweight
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at h
  have hfin : (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ (k + 1) ω) ∂μ).toReal
      ≤ (1 - c + c * ρ) * (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal := by
    have hsp : 0 ≤ (∫⁻ ω in B, ENNReal.ofReal (trialW Γ ρ k ω) ∂μ).toReal := ENNReal.toReal_nonneg
    nlinarith [hSR, hPc, hth, hc0, hsp]
  refine (ENNReal.toReal_le_toReal hLfin
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) hSfin)).mp ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by nlinarith)]
  exact hfin

end OneStep

end TrialTail
