/-
General initial laws and wider raw horizons from the accepted coherent-window
support theorem.  The first results close the actual diagonal finite-window
family and hence its prefix-cylinder subfamily for an arbitrary initial
probability law.  No invariance, stationarity or positivity premise is added.
-/
import Swarm.CoherentWindowSupport
import Swarm.PrefixCyl

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
open SimJump

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace SwarmGeneralRawWindow

open SimJump.Record SwarmRec SwarmRawRecord SwarmArrayWords SwarmSegKernel
open Swarming Swarming.Uniform SwarmRestart
open SwarmRawGlobalCover SwarmMixedTrajectory SwarmRawWindowMass
open SwarmChainAssemble SwarmFinFuture SwarmFinHorizon SwarmFreshPos
open SwarmInfSeg SwarmFreshPrefix SwarmInitialTransport
open SwarmPrefix

attribute [local instance] Classical.propDecidable
attribute [local instance] maxRecordDecompFintype

variable {N m : ℕ}

/-- The accepted full Dirac raw-window identity is precisely the per-start
finite-chain profile required by the arbitrary-initial-law diagonal theorem. -/
theorem chainVec_rawWindow_profile_of_srSet
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    ∀ y : RecState N m, y ∈ srSet N m →
      (SwarmChain.chainVec (SwarmSegKernel.asegK (N := N) (m := m) p hm y)
        (SwarmSegKernel.pairK (N := N) (m := m) p hm) (K + 1))
        (rawWindowVec (N := N) (m := m) (K := K) C) =
      (arrayMeasure N) {U : Array N |
        FromVupto (N := N) p m K U (SwarmFreshState.walkStateOf y) ∧
          trajPat (N := N) p m K U (SwarmFreshState.walkStateOf y) ∈ C} := by
  intro y hy
  rw [SwarmRawGlobalCover.chainVec_rawWindow_eq_arrayMeasure
    p hm hp0 hp1 y hy K C hC]
  exact (SwarmFinHorizon.fresh_mass_finStrict_eq_of_srSet hm p hy K C).symm

/-- Every diagonal raw window has the `π(srSet)` times original-array mass
formula for an arbitrary initial probability measure. -/
theorem chainLaw_diagonal_window_eq_pi_srSet
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (K : ℕ) (C : Set (Fin (K + 1) → Fin N → ℤ)) (hC : MeasurableSet C) :
    SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π)
        (SwarmFinFuture.chainWindow K K C) =
      π (srSet N m) * (arrayMeasure N) {U : Array N |
        posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) K ⁻¹' C} := by
  exact SwarmMixedTrajectory.chainLaw_diagonal_window_eq_pi_srSet_of_profile
    p hm hp0.le hp1.le π K C hC
      (chainVec_rawWindow_profile_of_srSet p hm hp0 hp1 K C hC)

/-- The actual chain law satisfies the complete diagonal slice of
`FinHorizonWindow`, for every `K` and every measurable diagonal pattern. -/
theorem chainLaw_finHorizonWindowDiag
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] :
    SwarmPrefix.FinHorizonWindowDiag (N := N) (m := m) p π
      (SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π))
      (SwarmFinFuture.chainPath (N := N)) := by
  intro K C hC
  exact chainLaw_diagonal_window_eq_pi_srSet p hm hp0 hp1 π K C hC

/-- Consequently the actual chain law satisfies every `(K,n)` member whose
width-`n` pattern is the pullback of a measurable width-`K` pattern. -/
theorem chainLaw_finHorizonWindowPrefix
    (p : ℝ) (hm : 1 ≤ m) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] :
    SwarmPrefix.FinHorizonWindowPrefix (N := N) (m := m) p π
      (SwarmChainAssemble.chainLaw
        (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp0.le hp1.le π))
      (SwarmFinFuture.chainPath (N := N)) := by
  exact (SwarmPrefix.finHorizonWindowPrefix_iff_diag (N := N) (m := m)
    (p := p) (π := π) _ _).mpr (chainLaw_finHorizonWindowDiag p hm hp0 hp1 π)

end SwarmGeneralRawWindow
