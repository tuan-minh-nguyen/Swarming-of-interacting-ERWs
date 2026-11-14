/- N-uniform instantiation of the adapted-ledger occupation assembly. -/
import Swarm.ProjResidual
import Swarm.UniformKappa

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmProjRes

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly

/-- **N-uniform occupation front from the adapted projected ledger.**  Both remaining
inputs are explicitly quantified over all walker counts; `hZ` is not proved here. -/
theorem ae_occ_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (A : ℝ)
    (hZ : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    {C : ℝ}
    (h2 : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ C * Real.log ((t : ℝ) + 2) ^ 4) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ),
      ∀ᵐ U ∂(arrayMeasure N), ∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
        SwarmOccTwo.OccOfMax p m N i j U n
          ≤ max 1 (A + B) * ((runMax p m U i n : ℤ) : ℝ) + (1 / 8) * (n : ℝ) := by
  obtain ⟨B, hB, hJ⟩ := SwarmUniform.Jsum_eventual_uniform (p := p) hp0 hp1 hm (eps := 1 / 64) (by norm_num)
  refine ⟨B, hB, fun N => ?_⟩
  have hQ : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ Qpl p m (1 / 64) i j T U :=
    fun i j hij => ae_Qpl_lower (N := N) hp0 hp1 m i j (h2 N i j hij) (hvar N i j hij)
  exact ae_occ_of_proj_budgets (N := N) hp0 hp1 hm
    (by norm_num) (by norm_num) (by norm_num)
    (fun i j hij => hZ N i j hij) (fun i j _ => hJ N i j) hQ

/-- The corresponding lower-speed constant is one explicit function of `m`, `p` and the
record-cost coefficient; it does not depend on walker count. -/
theorem ae_speed_uniform {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (A : ℝ)
    (hZ : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      Zproj p m (1 / 64) i j T U ≤ A * ((runMax p m U i T : ℤ) : ℝ) + (1 / 64) * (T : ℝ))
    {C : ℝ}
    (h2 : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ t : ℕ,
      Integrable (fun U : Array N => projInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ (N : ℕ) (i j : Fin N), i ≠ j → ∀ t : ℕ,
      ∫ U, projInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)
        ≤ C * Real.log ((t : ℝ) + 2) ^ 4) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N,
      κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop := by
  obtain ⟨B, hB, hocc⟩ := ae_occ_uniform (p := p) hp0 hp1 hm A hZ h2 hvar
  refine ⟨7 / (40 * max 1 (A + B)), by positivity, fun N hN => ?_⟩
  filter_upwards [hocc N, SwarmHosc.trajectory_hosc (p := p) hp0 hp1 m N] with U hU hoscU i
  obtain ⟨j, hji⟩ := SwarmHosc.exists_ne_of_two_le hN i
  obtain ⟨N₁, hN₁⟩ := hU i j (Ne.symm hji)
  obtain ⟨N₂, hN₂⟩ := hU j i hji
  exact SwarmSpeed.liminf_speed
    (u := fun t => (trajectory p m U t).pos i)
    (v := fun t => (trajectory p m U t).pos j)
    (by simp [trajectory_zero, initialWalkState])
    (C := max 1 (A + B)) (B := 1) (le_max_left _ _) (N := max N₁ N₂)
    (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
    (hoscU i) (SwarmOccTwo.actual_pos_div_le_one (N := N) (p := p) (m := m) hp0 hp1 i U)

end SwarmProjRes


