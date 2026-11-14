/-
Literal weighted deterministic-start cells for the actual projected martingale
`Qpl`.  The only model input left abstract is the start-time filtration
condition and the predictable geometric carrier/envelope.  In particular,
this file does not assert that `recTimeA` is a stopping time.
-/
import Swarm.WeightedShiftCell
import Swarm.ProjOptionalLedger

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Classical
open scoped BigOperators ENNReal
open Swarming.Uniform
open ShiftedAdvance

namespace QplWeightedCell

/-- One actual `Qpl` increment is exactly its projected martingale increment. -/
theorem Qpl_succ_sub {N : ℕ} (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (t : ℕ) (U : Array N) :
    Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j t U =
      Swarming.Enl.ProjLedger.projInc p m eps i j t U := by
  simp only [Swarming.Enl.ProjLedger.Qpl, Finset.sum_range_succ]
  ring

/-- The literal weighted `OscStartCell` estimate for the actual `Qpl`.  All
adaptedness, integrability and centring obligations are discharged by
`ProjOptionalLedger`; no generic martingale process is substituted for it. -/
theorem measureReal_qpl_oscStartCell_le_of_ptrunc {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (eps : ℝ) (i j : Fin N)
    (hε : 0 < eps) {τ : Array N → ℕ} {s : ℕ} {A : Set (Array N)}
    (hA : MeasurableSet[Swarming.Enl.enlFilt p m s] A)
    (hτ : MeasurableSet[Swarming.Enl.enlFilt p m s] {U | τ U = s})
    {G : ℕ → Set (Array N)}
    (hG : ∀ k, MeasurableSet[Swarming.Enl.enlFilt p m (s + k)] (G k))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.projInc p m eps i j (s + k) U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (arrayMeasure N).real (A ∩ OscStartCell
        (Swarming.Enl.ProjLedger.Qpl p m eps i j) τ n δ s) ≤
      (arrayMeasure N).real (A ∩ {U | τ U = s}) *
        (2 * ((n : ℝ) + 1) * Real.exp (-(δ ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      (arrayMeasure N).real ((A ∩ {U | τ U = s}) ∩
        {U | ∃ k < n, U ∉ G k}) := by
  letI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hdiff : ∀ t, (fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (t + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j t U) =
      Swarming.Enl.ProjLedger.projInc p m eps i j t := by
    intro t
    funext U
    exact Qpl_succ_sub p m eps i j t U
  have hQm : ∀ k, StronglyMeasurable[Swarming.Enl.enlFilt p m (s + k + 1)]
      (fun U : Array N => Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U) := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m (s + k) eps i j
  have hQi : ∀ k, Integrable (fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U) (arrayMeasure N) := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m (s + k) i j hε
  have hQ0 : ∀ k, (arrayMeasure N)[fun U : Array N =>
      Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U |
        Swarming.Enl.enlFilt p m (s + k)] =ᵐ[arrayMeasure N] 0 := by
    intro k
    rw [hdiff]
    exact Swarming.Enl.ProjLedger.condExp_projInc_eq_zero hp0 hp1 m (s + k) i j hε
  have hbdd' : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k + 1) U -
        Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U| ≤ C := by
    intro k U hU
    rw [Qpl_succ_sub]
    exact hbdd k U hU
  exact measureReal_inter_oscStartCell_le_of_ptrunc hA hτ hG hQm hQi hQ0 hC hbdd' hn hδ

end QplWeightedCell
