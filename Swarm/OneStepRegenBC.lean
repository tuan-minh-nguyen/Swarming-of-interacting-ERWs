/-
# Discharging the `hstep` premise of `WCJF.RegenBC` for the actual Ionescu–Tulcea path law

`WCJF.RegenBC.ae_frequently_mem_of_kernel_force_of_tight` (public file
`Swarm/CondBC.lean`) takes as an explicit hypothesis the one-step Markov
identity

  `hstep : ∀ n, μ[indicator{ω | Y (n+1) ∈ F} | ℱ n] =ᵐ[μ] fun ω => (κ (Y n ω) F).toReal`,

which its own note (`areas/kac/COND_BC.md`, "Unproved premises", item 1) records as *not*
formalised.  This file proves that identity for the path law of an arbitrary Markov kernel —
the exact law `recordTraj p hp hp1 hm μ = homTraj (hitKKernel p hm) μ` is an instance of —
and composes it with the public conditional Borel–Cantelli passage, so that the frequency
statement no longer carries `hstep` as an assumption.

What is *not* claimed here: tightness (`htight`), any invariant measure, any stationary regime,
the regeneration construction, the common speed, or the paper's main theorem.  The only
remaining hypotheses of the capstone are the public kernel force estimate `hforce`, the
positivity of its constant, the concrete shape `Kset K = {y | dep y ≤ K}` and the path-law tail
bound `htight`.

No `sorry`, no custom axiom, no `native_decide`.
-/
import Swarm.OneStepPathLaw
import Swarm.CondBC

open MeasureTheory ProbabilityTheory Filter Topology
open MeasureTheory.Filtration
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace WCJF
namespace RegenBC

open WCJF.OneStepBridge

variable {X : Type*} [MeasurableSpace X]

/-! ### Adaptedness of the coordinate process -/

/-- The `n`-th coordinate is measurable for the canonical past filtration `piLE n`. -/
theorem measurable_eval_piLE (n : ℕ) :
    Measurable[↑(piLE (X := fun _ => X) n)] (fun ω : ℕ → X => ω n) := by
  rw [piLE_eq_comap_frestrictLe]
  refine measurable_iff_comap_le.mpr ?_
  have hev : Measurable
      (fun y : ((i : ↥(Finset.Iic n)) → X) => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  have hcomp : (fun ω : ℕ → X => ω n) =
      (fun y : ((i : ↥(Finset.Iic n)) → X) => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ∘
        (Preorder.frestrictLe (π := fun _ => X) n) := rfl
  rw [hcomp, ← MeasurableSpace.comap_comp]
  refine MeasurableSpace.comap_mono ?_
  exact measurable_iff_comap_le.mp (measurable_pi_apply _)

/-! ### The one-step Markov identity in the exact shape of `RegenBC.hstep` -/

/-- **`hstep` of `WCJF.RegenBC` for the Ionescu–Tulcea path law.**  This is
`WCJF.OneStepBridge.condExp_indicator_succ` with `Y n ω = ω n` and `ℱ n = piLE n`. -/
theorem hstep_pathLaw (κ : Kernel X X) [IsMarkovKernel κ]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀] {F : Set X} (hF : MeasurableSet F) :
    ∀ n, (pathLaw κ μ₀)[Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ)) |
        piLE (X := fun _ => X) n]
      =ᵐ[pathLaw κ μ₀] fun ω => (κ (ω n) F).toReal :=
  fun n => condExp_indicator_succ κ μ₀ n hF

/-! ### The conditional Borel–Cantelli passage with `hstep` discharged -/

/-- **The paper's frequency step for the actual Ionescu–Tulcea path law.**

Kernel force `hforce` on the exhaustion sets `Kset K = {y | dep y ≤ K}` and the path-law tail
bound `htight` imply that `F` is visited infinitely often, almost surely.  Compared with
`WCJF.RegenBC.ae_frequently_mem_of_kernel_force_of_tight`, the one-step Markov identity
`hstep` is *proved* here (`hstep_pathLaw`) rather than assumed. -/
theorem ae_frequently_mem_of_kernel_force_pathLaw
    (κ : Kernel X X) [IsMarkovKernel κ] (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    {F : Set X} (hF : MeasurableSet F) {Kset : ℕ → Set X} {c : ℕ → ℝ≥0∞}
    (hforce : ∀ K y, y ∈ Kset K → c K ≤ κ y F)
    (hc : ∀ K, 0 < (c K).toReal)
    {dep : X → ℕ} (hKset : ∀ K, Kset K = {y : X | dep y ≤ K})
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      pathLaw κ μ₀ {ω : ℕ → X | ω r ∉ Kset K} ≤ ε) :
    ∀ᵐ ω ∂(pathLaw κ μ₀), ∃ᶠ n in atTop, ω n ∈ F :=
  ae_frequently_mem_of_kernel_force_of_tight (μ := pathLaw κ μ₀)
    (ℱ := piLE (X := fun _ => X)) (Y := fun (n : ℕ) (ω : ℕ → X) => ω n)
    (fun n => measurable_eval_piLE n) hF hforce (hstep_pathLaw κ μ₀ hF) hc hKset htight

end RegenBC
end WCJF
