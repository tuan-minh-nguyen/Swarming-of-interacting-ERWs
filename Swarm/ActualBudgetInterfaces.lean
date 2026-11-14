/-
  Actual-model residual interfaces after the verified `Z` and `J` budgets.

  `ZBudgetActual` and `JBudgetActual` supply the two upper budgets in coefficient-general form.
  This file merges their array-dependent onsets with the one remaining eventual lower-tail
  input for `Qcomp`.  It is a reduction theorem, not a proof of that input and not an assertion
  about arbitrary marginal `Swarm.IsInteractingLaw` systems.
-/
import Swarm.BallisticInterfaceActual
import Swarm.ZBudgetActual
import Swarm.JBudgetActual

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SwarmActualBudget

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-- The only remaining actual occupation-side stochastic input: one per-pair lower-tail budget
at the ledger's fixed parameters `eps = δ = 1/64`.  The onset may depend on the array. -/
def QResidual (p : ℝ) (m N : ℕ) : Prop :=
  ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
    -((1 / 64 : ℝ) * (T : ℝ)) ≤
      Qcomp p m (1 / 64) (fun t => alphaFun p m t i) i j U T

/-- Merging the verified `Z` and `J` upper bounds with `QResidual` produces exactly the accepted
coefficient-general interface.  Additive constants are all zero; their onsets are merged. -/
theorem interfacesGen_of_actual_budgets {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hQ : QResidual p m N) {i j : Fin N} (hij : i ≠ j) :
    ∃ B : ℝ, 0 < B ∧ SwarmBIA.InterfacesGen p m N (1 / 64) (1 / 64)
      (SwarmSpatial.targetParam p m + 1) B i j := by
  obtain ⟨B, hBpos, hJ⟩ := Swarming.Enl.JBudgetActual.Jsum_eventual (N := N)
    hp0 hp1 hm (i := i) (j := j) (by norm_num : (0 : ℝ) < 1 / 64)
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [Swarming.Enl.ZBudget.Zbudget_ae_runMax (N := N)
      hp0 hp1 hm (by norm_num : (0 : ℝ) < 1 / 64) i j, hJ, hQ i j hij]
    with U hZ hJU hQU
  obtain ⟨NZ, hZU⟩ := hZ
  obtain ⟨NJ, hJU⟩ := hJU
  obtain ⟨NQ, hQU⟩ := hQU
  refine ⟨max NZ (max NJ NQ), 0, 0, 0, ?_, ?_, ?_⟩
  · intro T hT
    have hZT := hZU T (le_trans (le_max_left _ _) hT)
    simpa only [← Swarming.Enl.ZBudget.runMax_eq_speed, add_zero] using hZT
  · intro T hT
    have hJT := hJU T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
    linarith
  · intro T hT
    have hQT := hQU T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
    linarith

/-- **Actual-model reduction: only `QResidual` remains.**  Once it is proved for every ordered
pair, there is a positive lower-speed coefficient for the concrete array trajectory, together
with the two-sided occupation front.  The generic `Swarm.Ballistic` quantifier is not claimed. -/
theorem actual_occupation_and_speed_of_hQ {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hQ : QResidual p m N) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᵐ U ∂(arrayMeasure N),
      (∀ i j : Fin N, i ≠ j → ∃ N₁ : ℕ, ∀ n ≥ N₁,
        SwarmOccTwo.OccOfMax p m N i j U n
          ≤ C * ((SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n : ℤ) : ℝ)
            + (1 / 8 : ℝ) * (n : ℝ)) ∧
      (∀ i : Fin N, κ ≤ liminf (fun n : ℕ => ((trajectory p m U n).pos i : ℝ) / n) atTop) := by
  let zero : Fin N := ⟨0, by omega⟩
  let one : Fin N := ⟨1, by omega⟩
  have hJall : ∀ i j : Fin N, ∃ B : ℝ, 0 < B ∧
      ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
        Jsum p m (1 / 64) i j U T ≤ B * ((runMax p m U i T : ℤ) : ℝ) +
          (1 / 64) * (T : ℝ) := by
    intro i j
    exact Swarming.Enl.JBudgetActual.Jsum_eventual (N := N) hp0 hp1 hm
      (by norm_num : (0 : ℝ) < 1 / 64)
  choose B hBpos hJ using hJall
  let Btot : ℝ := ∑ i : Fin N, ∑ j : Fin N, B i j
  have hBle (i j : Fin N) : B i j ≤ Btot := by
    calc B i j ≤ ∑ k : Fin N, B i k :=
      Finset.single_le_sum (fun k _ => (hBpos i k).le) (Finset.mem_univ j)
    _ ≤ Btot := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => (hBpos k l).le) (Finset.mem_univ i)
  have hBtot : 0 < Btot := lt_of_lt_of_le (hBpos zero one) (hBle zero one)
  set A : ℝ := SwarmSpatial.targetParam p m + 1 with hA
  have hcoef : ∀ i j : Fin N, i ≠ j →
      SwarmBIA.InterfacesGen p m N (1 / 64) (1 / 64) A Btot i j := by
    intro i j hij
    filter_upwards [Swarming.Enl.ZBudget.Zbudget_ae_runMax (N := N)
        hp0 hp1 hm (by norm_num : (0 : ℝ) < 1 / 64) i j, hJ i j, hQ i j hij]
      with U hZ hJU hQU
    obtain ⟨NZ, hZU⟩ := hZ
    obtain ⟨NJ, hJU⟩ := hJU
    obtain ⟨NQ, hQU⟩ := hQU
    refine ⟨max NZ (max NJ NQ), 0, 0, 0, ?_, ?_, ?_⟩
    · intro T hT
      have hZT := hZU T (le_trans (le_max_left _ _) hT)
      simpa only [← Swarming.Enl.ZBudget.runMax_eq_speed, hA, add_zero] using hZT
    · intro T hT
      have hJT := hJU T (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT)
      have hM0 : (0 : ℝ) ≤ ((runMax p m U i T : ℤ) : ℝ) := by
        exact_mod_cast zero_le_runMax p m U i T
      have hTM := mul_le_mul_of_nonneg_right (hBle i j) hM0
      linarith
    · intro T hT
      have hQT := hQU T (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
      simpa only [sub_zero] using hQT
  refine ⟨max 1 (A + Btot), 7 / (40 * max 1 (A + Btot)), lt_of_lt_of_le zero_lt_one
    (le_max_left _ _), by positivity, ?_⟩
  filter_upwards [SwarmBIA.actual_occ_coef_of_interfaces (N := N)
      (eps := (1 : ℝ) / 64) (δ := (1 : ℝ) / 64) (A := A) (B := Btot) hp0 hp1 hm
      (by norm_num) (by norm_num) (by norm_num) hcoef,
    SwarmBIA.actual_speed_coef_of_interfaces (N := N)
      (eps := (1 : ℝ) / 64) (δ := (1 : ℝ) / 64) (A := A) (B := Btot) hp0 hp1 hm hN
      (by norm_num) (by norm_num) (by norm_num) hcoef] with U hoccU hspeedU
  exact ⟨hoccU, hspeedU⟩

end SwarmActualBudget
