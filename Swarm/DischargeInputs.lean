/-
  **Direction G (m7), `DischargeInputs.lean`: the global one-step `Hpot` integral budget with no
  hypotheses left.**

  `GlobalIntegralBudget.lean` states the integral budget with two explicit hypotheses:
  the below-record restricted bound (Direction C/D) and the above-record restricted bound
  (Direction A).  Both have since been proved in the swarm and accepted by review:

  This module *reads* those files (it does not modify them: they are compiled with
  `lean -R <their dir> -o <my .build>/<Module>.olean`, so all output lands in my own `.build`)
  and discharges both hypotheses, giving

    `∫ HpotInc ≥ ∫ campaignWeight`   and   `∫ paperWeight ≤ ∫ HpotInc`

  with **no** hypotheses beyond the standing model assumptions `1/2 < p < 1`, `2 ≤ m`, `i ≠ j`.

  The paper-weight statement is the paper's one-step `(Zloss)` bound in mass form:
  `∫ [1{0 ≤ X_n^i ≤ M_n^j} - b_n a^{(X_n^i - M_n^j)} 1{M_n^j ≤ X_n^i}] ≤ ∫ (H_{n+1} - H_n)`.

  Still quarantined: no `Q`, no occupation, no regeneration, no Ballistic, no main theorem.
-/
import Swarm.GlobalIntegralBudget
import Swarm.AboveTower
import Swarm.BelowRecordHpotInc

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace Budget

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ### The below-region inputs, discharged -/

/-- The below-record region of the audited candidate is this file's `belowSet`. -/
theorem belowRecSet_eq_belowSet (p : ℝ) (m n : ℕ) (i j : Fin N) :
    belowRecSet p m n i j = belowSet p m n i j :=
  (belowSet_eq_lt_runMax p m n i j).symm

/-- **The campaign below-region hypothesis, discharged** from the accepted below-record module. -/
theorem below_hypothesis_discharged {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (fun U => (belowSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  refine below_hypothesis_of_lt_runMax ?_
  have h := HpotInc_belowRec_ge_neg_bRec (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j) hij
  have hset : belowRecSet p m n i j
      = {U : Array N | (trajectory p m U n).pos i < runMax p m U j n} := rfl
  rwa [hset] at h

/-- **The bracket dominates the paper's below-record gain indicator**: `≥ 1` in the interior
`0 ≤ x < M_n^j` (integrated `InteriorBound.interior_bracket_ge_one`) and `≥ 0` below zero
(the accepted `belowRec_bracket_nonneg`), i.e. `≥ 1{0 ≤ X_n^i}` on the below-record region. -/
theorem below_bracket_ge_posWeight {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {U : Array N} (hU : U ∈ belowSet p m n i j) :
    posWeight p m n i U
      ≤ alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
        - (1 - alphaFun p m n i U)
          * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1) := by
  by_cases hneg : (trajectory p m U n).pos i < 0
  · have h0 : posWeight p m n i U = 0 := by
      rw [posWeight, if_neg (by omega)]
    rw [h0]
    have hb := belowRec_bracket_nonneg (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j) hij
      (U := U) ((belowRecSet_eq_belowSet p m n i j).symm ▸ hU)
    linarith
  · have hx0 : (0 : ℤ) ≤ (trajectory p m U n).pos i := not_lt.mp hneg
    have h1 : posWeight p m n i U = 1 := by
      rw [posWeight, if_pos hx0]
    rw [h1]
    have hlt : (trajectory p m U n).pos i < runMax p m U j n :=
      (mem_belowSet_iff_lt p m n i j U).mp hU
    have hcast : (((trajectory p m U n).pos i).toNat : ℤ) = (trajectory p m U n).pos i :=
      Int.toNat_of_nonneg hx0
    have hkM : (((trajectory p m U n).pos i).toNat : ℤ) < runMax p m U j n := by
      rw [hcast]; exact hlt
    have hb := interior_bracket_ge_one (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j) hij
      (k := ((trajectory p m U n).pos i).toNat) (U := U) hcast.symm hkM
    have hz : hZpot (envH p m j U) ((trajectory p m U n).pos i)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((trajectory p m U n).pos i).toNat := by
      rw [hZpot_of_nonneg hx0]
      rfl
    have harg : (trajectory p m U n).pos i - 1
        = (((trajectory p m U n).pos i).toNat : ℤ) - 1 := by omega
    rw [hz, harg]
    exact hb

/-- **The sharpened (paper) below-region hypothesis, discharged**: from the accepted exact
`enlFilt` identity below the record plus the bracket bound. -/
theorem belowSharp_hypothesis_discharged {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (fun U => (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)) := by
  have hpt : ∀ U : Array N, (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U) U
      ≤ (belowSet p m n i j).indicator
          (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
            - (1 - alphaFun p m n i U)
              * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U := by
    intro U
    by_cases hU : U ∈ belowSet p m n i j
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
      exact below_bracket_ge_posWeight hp1 hp2 hij hU
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  have hid := condExp_HpotInc_belowRec (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j)
  have hset : belowRecSet p m n i j = belowSet p m n i j := belowRecSet_eq_belowSet p m n i j
  rw [hset] at hid
  have h1 : (fun U => (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] (belowSet p m n i j).indicator
          (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
            - (1 - alphaFun p m n i U)
              * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) :=
    Filter.Eventually.of_forall hpt
  exact h1.trans_eq hid.symm

/-! ### The above-region input, discharged (`2 ≤ m`) -/

/-- **The above-record hypothesis, discharged** from the accepted above-record tower module. -/
theorem above_hypothesis_discharged {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) :=
  fun g hg _ =>
    indicator_le_condExp_indicator_HpotInc_abovePosSet (p := p) hp1 hp2 m n hij hm hg

/-! ### The budgets with nothing left open -/

/-- **The global one-step budget, unconditionally** (all constants explicit, `g = 0` separated
from `g ≥ 1`). -/
theorem integral_HpotInc_ge_budget_discharged (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    (∫ U in belowSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N))
      + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
      + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
          (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N)
    ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_HpotInc_ge_budget (N := N) (p := p) hp1 hp2 hij
    (below_hypothesis_discharged hp1 hp2 hij) (above_hypothesis_discharged hp1 hp2 hm hij)

/-- **The global one-step budget in weight-function form, unconditionally.** -/
theorem integral_HpotInc_ge_campaignWeight_discharged (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, campaignWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_HpotInc_ge_campaignWeight (N := N) (p := p) hp1 hp2 hij
    (below_hypothesis_discharged hp1 hp2 hij) (above_hypothesis_discharged hp1 hp2 hm hij)

/-- **The paper's `(Zloss)` mass bound, unconditionally.**  The real integral of the paper's
one-step weight — `1{0 ≤ x ≤ r} - b_n a^{(x-r)} 1{r ≤ x}` at `r = M_n^j`, `x = X_n^i` — is
dominated by `∫ (H_{j,n+1}(X_{n+1}^i) - H_{j,n}(X_n^i))`. -/
theorem integral_HpotInc_ge_paperWeight_discharged (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_HpotInc_ge_paperWeight (N := N) (p := p) hp1 hp2 hij
    (belowSharp_hypothesis_discharged hp1 hp2 hij) (above_hypothesis_discharged hp1 hp2 hm hij)

/-- **The piecewise paper-level budget, unconditionally** (set-integral form). -/
theorem integral_HpotInc_ge_paper_pieces_discharged (p : ℝ) (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    (∫ U in belowSet p m n i j, posWeight p m n i U ∂(arrayMeasure N))
      + (∫ U in abovePosSet p m n i j 0, (1 - bRec p m n j U) ∂(arrayMeasure N))
      + ∑ g ∈ Finset.range n, ∫ U in abovePosSet p m n i j (g + 1),
          (-(bRec p m n j U * aRec p m ^ (g + 1))) ∂(arrayMeasure N)
    ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_HpotInc_ge_paper_pieces (N := N) (p := p) hp1 hp2 hij
    (belowSharp_hypothesis_discharged hp1 hp2 hij) (above_hypothesis_discharged hp1 hp2 hm hij)

end Budget
end Swarming.Enl
