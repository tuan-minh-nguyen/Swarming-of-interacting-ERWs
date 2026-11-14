/-
  **Joint closure of the full-history seed link (direction B + direction A).**

  `ShiftedSeed.lean` (direction B) reduces the projected recursion for the actual full-history
  potential `h_j(M_n^j + g)` to the single measurability input

      `Measurable[enlRecMeas p m n j] (H0 p m n j)`,
      `H0 p m n j U = hof p (SwarmLogRatio.siteMarks p m U j) (recVal j (prefOf p m n U)).toNat`.

      `seedH p m n j U = hof p (SwarmLogRatio.siteMarks p m U j) (recVal j (prefOf p m n U)).toNat`

  (identical body, so the two are definitionally equal).

  This file therefore closes the loop: it imports `SeedMeas` and `ShiftedSeed` and derives, with
  **no** measurability hypothesis, all `RecSeed` hypotheses and the paper's projected recursion
  for the actual trajectory and the actual `arrayMeasure N`.-/
import Swarm.ShiftedSeed
import Swarm.SeedMeas

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- Direction A's measurability result, read as measurability of `H0` (the two definitions have
the same body, so this is definitional). -/
theorem measurable_H0 {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (j : Fin N) :
    Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) :=
  measurable_seedH hp m n j

/-- **All `RecSeed` hypotheses for the actual full-history seed, with no extra input.** -/
theorem recSeed_hypotheses_complete {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (j : Fin N) :
    Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) ∧
      Integrable (H0 p m n j) (arrayMeasure N) ∧
      ∀ U : Array N, |H0 p m n j U| ≤ 2 * (n : ℝ) + 3 :=
  recSeed_hypotheses hp1 hp2 (by linarith) m n j (measurable_H0 hp1.le m n j)

/-- **The projected recursion for the actual full-history potential, unconditionally.**
`E[h_j(M_n^j + g) | enlRecMeas] = Φ^g (h_j(M_n^j))` almost surely, for the actual trajectory,
the actual `arrayMeasure N` and the actual site marks. -/
theorem condExp_H0_complete {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g))
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g (H0 p m n j U) :=
  condExp_H0 (by linarith) hp1 hp2 m j (measurable_H0 hp1.le m n j) g

/-- The same statement written with direction A's `seedH` in place of `H0`. -/
theorem condExp_seedH_complete {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g))
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g (seedH p m n j U) :=
  condExp_H0_complete hp1 hp2 m j g

/-- **The paper's display `e_{g+1} = 1 + a (1 + e_g)` for the actual potential, unconditionally.** -/
theorem condExp_H0_complete_succ {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + (g + 1)))
      =ᵐ[arrayMeasure N] fun U => 1 + aRec p m *
        (1 + condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + g)) U) :=
  condExp_H0_succ (by linarith) hp1 hp2 m j (measurable_H0 hp1.le m n j) g

end Swarming.Enl


