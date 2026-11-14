/- Formal relation between the paper's projected potential and the optional
  projection of the campaign's static `Zpot`.  The two independently developed
  ledgers use the same paper object: the difference of the projected potential and
  the adapted record correction. -/
import Swarm.ProjLedger
import Swarm.ProjOptionalLedger

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Swarming.Enl.ProjLedgerBridge

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-- Projection commutes with evaluation at the measurable, integer-valued walker position.
On each level set, the integrand is the fixed-site potential, so uniqueness of conditional
expectation under the restricted measure identifies the two functions there. -/
theorem condExp_Hpot_at_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m : ℕ) (t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    (fun U => condExp (enlFilt p m t) (arrayMeasure N)
      (fun V => SwarmOcc.Hpot (envH p m j V) ((trajectory p m V t).pos i)) U)
      =ᵐ[arrayMeasure N]
      fun U => projH p m j t U ((trajectory p m U t).pos i) := by
  have hle : (enlFilt p m t : MeasurableSpace (Array N)) ≤
      (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le t
  have hg := integrable_Hpot_envH_T (N := N) hp0 hp1 m t i j hε
  have hpoint : ∀ᵐ U ∂(arrayMeasure N), ∀ y : ℤ,
      (trajectory p m U t).pos i = y →
      condExp (enlFilt p m t) (arrayMeasure N)
        (fun V => SwarmOcc.Hpot (envH p m j V) ((trajectory p m V t).pos i)) U
        = projH p m j t U y := by
    rw [MeasureTheory.ae_all_iff]
    intro y
    have hs : MeasurableSet[enlFilt p m t]
        {U : Array N | (trajectory p m U t).pos i = y} :=
      enl_pos_measurable p m t le_rfl i (measurableSet_singleton y)
    have hf : Integrable (fun V : Array N =>
        SwarmOcc.Hpot (envH p m j V) y) (arrayMeasure N) :=
      integrable_Hpot_site hp0 hp1 (by linarith) m j y
    have hlocal : (fun U => condExp (enlFilt p m t)
        ((arrayMeasure N).restrict {U : Array N | (trajectory p m U t).pos i = y})
        (fun V => SwarmOcc.Hpot (envH p m j V) y) U) =ᵐ[(arrayMeasure N).restrict
        {U : Array N | (trajectory p m U t).pos i = y}]
        condExp (enlFilt p m t) (arrayMeasure N)
          (fun V => SwarmOcc.Hpot (envH p m j V) ((trajectory p m V t).pos i)) := by
      refine (ae_eq_condExp_of_forall_setIntegral_eq
        (μ := (arrayMeasure N).restrict {U : Array N | (trajectory p m U t).pos i = y})
        (m := enlFilt p m t)
        (g := fun U => condExp (enlFilt p m t)
          ((arrayMeasure N).restrict {U : Array N | (trajectory p m U t).pos i = y})
          (fun V => SwarmOcc.Hpot (envH p m j V) y) U) hle hg.integrableOn
        (fun s _ _ => (integrable_condExp
          (μ := (arrayMeasure N).restrict {U : Array N | (trajectory p m U t).pos i = y})
          (m := enlFilt p m t) (f := fun V : Array N =>
            SwarmOcc.Hpot (envH p m j V) y)).integrableOn) ?_
        stronglyMeasurable_condExp.aestronglyMeasurable).trans
          (condExp_restrict_ae_eq_restrict hle hs hg)
      intro s hsm _
      rw [setIntegral_condExp hle hf.integrableOn hsm]
      refine setIntegral_congr_ae (hle _ hsm) ?_
      filter_upwards [ae_restrict_mem (hle _ hs)] with U hU hUy
      rw [hU]
    exact (ae_restrict_iff' (hle _ hs)).mp (by
      filter_upwards [hlocal.symm, condExp_restrict_ae_eq_restrict hle hs hf]
        with U hL hR
      simpa only [projH, ← Swarming.Enl.siteH_eq_envH p m j] using hL.trans hR)
  filter_upwards [hpoint] with U hU
  exact hU _ rfl

/-- **The paper's `Z` is the optional projection of static `Zpot`.** -/

theorem Zproj_eq_optional_projection {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    (fun U => Swarming.Enl.Zproj p m eps i j U t)
      =ᵐ[arrayMeasure N] (fun U => Swarming.Enl.ProjLedger.Zproj p m eps i j t U) := by
  have hsub := condExp_Hpot_sub_Fcorr (N := N) hp0 hp1 (m := m) (i := i)
    (j := j) (eps := eps) hε t
  filter_upwards [hsub, condExp_Hpot_at_pos (N := N) hp0 hp1 m t i j hε] with U hU hpos
  change projH p m j t U ((trajectory p m U t).pos i) - _ = _
  change _ = condExp (enlFilt p m t) (arrayMeasure N)
    (fun V => SwarmOcc.Hpot (envH p m j V) ((trajectory p m V t).pos i)) U - _ at hU
  rw [hpos] at hU
  exact hU.symm

end Swarming.Enl.ProjLedgerBridge

