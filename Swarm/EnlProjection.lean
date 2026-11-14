/-
  **The actual projected potential at a random record, under `enlFilt`.**

  The joint seed work proves the recursion under the finer record-enlarged information
  `enlRecMeas`.  Since `enlFilt ≤ enlRecMeas`, the tower rule returns it to the paper's
  enlarged filtration.  The seed is the conditional mean of the full-history potential,
  rather than its possibly unread record value.
-/
import Swarm.Joint

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- Deterministic affine iterates preserve integrability. -/
lemma integrable_phiIter {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (a : ℝ) (f : Ω → ℝ) (hf : Integrable f μ) (g : ℕ) :
    Integrable (fun ω => phiIter a g (f ω)) μ := by
  induction g with
  | zero => simpa only [phiIter_zero] using hf
  | succ k ih =>
      have h := (integrable_const (1 : ℝ)).add ((ih.add (integrable_const (1 : ℝ))).const_mul a)
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [phiIter_succ, Pi.add_apply]
      ring

/-- The conditional mean of a deterministic affine iterate. -/
lemma condExp_phiIter {N : ℕ} {m₀ : MeasurableSpace (Array N)} {μ : Measure (Array N)}
    [IsProbabilityMeasure μ] {K : MeasurableSpace (Array N)}
    (hK : K ≤ m₀)
    (a : ℝ) (f : Array N → ℝ) (hf : Integrable f μ) (g : ℕ) :
    condExp K μ (fun ω => phiIter a g (f ω))
      =ᵐ[μ] fun ω => phiIter a g (condExp K μ f ω) := by
  letI : MeasurableSpace (Array N) := m₀
  induction g with
  | zero => exact Filter.EventuallyEq.rfl
  | succ k ih =>
      have haff := condExp_affine_gen (μ := μ) (m := K) (m₀ := m₀) hK
        (fun ω => phiIter a k (f ω)) (integrable_phiIter a f hf k) a
      exact haff.trans (by
        filter_upwards [ih] with ω hω
        rw [phiIter_succ, hω])

/-- **The projected potential at a random record under the actual enlarged filtration.**
No full-history seed is assumed measurable for `enlFilt`; only its conditional mean enters. -/
theorem condExp_hof_record_enlFilt {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g))
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g
        (condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j) U) := by
  have hp0 : p ≠ 0 := by linarith
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hfiner : enlFilt p m n ≤ enlRecMeas (N := N) p m n j :=
    enlFilt_le_enlRecMeas p m n j
  have hfiner0 : enlRecMeas (N := N) p m n j ≤ (inferInstance : MeasurableSpace (Array N)) :=
    enlRecMeas_le p m n j
  have hint : Integrable (H0 p m n j) (arrayMeasure N) :=
    (recSeed_hypotheses_complete hp1 hp2 m n j).2.1
  have hinner := condExp_H0_complete (n := n) hp1 hp2 m j g
  have htower : condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + g))) :=
    (condExp_condExp_of_le (μ := arrayMeasure N) hfiner hfiner0).symm
  exact htower.trans ((condExp_congr_ae hinner).trans
    (condExp_phiIter (m₀ := (inferInstance : MeasurableSpace (Array N)))
      hle (aRec p m) (H0 p m n j) hint g))

/-- The affine one-step recursion of the actual conditional means at a random record. -/
theorem condExp_hof_record_enlFilt_succ {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + (g + 1)))
      =ᵐ[arrayMeasure N] fun U => 1 + aRec p m *
        (1 + condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + g)) U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h1 := condExp_hof_record_enlFilt (n := n) hp1 hp2 m j (g + 1)
  have h2 := condExp_hof_record_enlFilt (n := n) hp1 hp2 m j g
  filter_upwards [h1, h2] with U h1U h2U
  rw [h1U, h2U, phiIter_succ]

end Swarming.Enl


