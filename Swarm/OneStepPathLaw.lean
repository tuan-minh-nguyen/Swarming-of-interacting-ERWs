/-
# The one-step Markov identity for the actual Ionescu–Tulcea path law

`Swarm/PathLaw.lean` defines the law of the whole record chain as
`homTraj κ μ = ProbabilityTheory.Kernel.trajMeasure μ (homFam κ)`, whose step family is the
composition of `κ` with the last coordinate of the partial trajectory.  Here we work with the
constant family `X n = X`, i.e. exactly the same construction for a single homogeneous kernel,
and prove:

* `map_pair_frestrictLe_succ` (the *tail factorisation* of the path law at time `n`): the joint
  law of the past `frestrictLe n ω` and the next point `ω (n+1)` is the composition-product of
  the past law with the next-step kernel;

* `condExp_indicator_succ` (**the one-step Markov identity, exact conditional-expectation
  equality**): for every measurable `F`,
  `P[indicator{ω | ω (n+1) ∈ F} | piLE n] =ᵐ[P] fun ω => (κ (ω n) F).toReal`,
  where `P` is the path law and `piLE n` is the canonical filtration of coordinates `≤ n`.
  This is precisely the `hstep` hypothesis of
  `WCJF.RegenBC.ae_frequently_mem_of_kernel_force_of_tight`, with the same kernel `κ` that
  drives the path law;

* `condDistrib_succ` (the regular-conditional-distribution form, under the standard-Borel
  hypotheses that Mathlib's `condDistrib` API asks for);

* `map_eval_succ` (restart, next-step form): the law of `ω (n+1)` under `P` is `κ` applied to
  the law of `ω n`.

Nothing here assumes a new invariant law, a stationary regime, an abstract replacement kernel
or a same-shaped Markov assumption: the identity is proved from the Ionescu–Tulcea construction
itself.  No `sorry`, no custom axiom, no `native_decide`.
-/
import Swarm.PathLaw
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Process.Filtration

open MeasureTheory ProbabilityTheory Filter Topology
open MeasureTheory.Filtration
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace WCJF
namespace OneStepBridge

variable {X : Type*} [MeasurableSpace X]

/-! ### The homogeneous family and its path law -/

/-- The homogeneous Ionescu–Tulcea family of a single kernel `κ`, in the shape required by
`ProbabilityTheory.Kernel.trajMeasure`: at step `n` the next point is drawn from `κ` at the
`n`-th coordinate of the partial trajectory.  This is the constant-`X` instance of the
repository's `SimJump.RecKernel.homFam`. -/
noncomputable def constFam (κ : Kernel X X) : ∀ n : ℕ,
    Kernel ((i : ↥(Finset.Iic n)) → X) X :=
  SimJump.RecKernel.homFam κ

theorem constFam_apply (κ : Kernel X X) (n : ℕ) (f : (i : ↥(Finset.Iic n)) → X) :
    constFam κ n f = κ (f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rw [constFam, SimJump.RecKernel.homFam_apply]

instance constFam.instIsMarkovKernel (κ : Kernel X X) [IsMarkovKernel κ] :
    ∀ n, IsMarkovKernel (constFam κ n) :=
  SimJump.RecKernel.homFam.instIsMarkovKernel κ

/-- The law of the whole chain driven by `κ`, started from `μ`. -/
noncomputable def pathLaw (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X) :
    Measure (ℕ → X) :=
  Kernel.trajMeasure (X := fun _ => X) μ (constFam κ)

instance pathLaw.instIsProbabilityMeasure (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] : IsProbabilityMeasure (pathLaw κ μ) := by
  rw [pathLaw]; infer_instance

/-! ### The tail factorisation of the path law -/

/-- **Tail factorisation at time `n`.**  The joint law of the past `frestrictLe n ω` and the
point `ω (n+1)` is the composition-product of the law of the past with the next-step kernel.
This is the exact one-step decomposition of the Ionescu–Tulcea path law at a deterministic
index, and the starting point of the Markov identity. -/
theorem map_pair_frestrictLe_succ (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    (pathLaw κ μ).map (fun ω : ℕ → X =>
        (Preorder.frestrictLe (π := fun _ => X) n ω, ω (n + 1)))
      = (pathLaw κ μ).map (Preorder.frestrictLe (π := fun _ => X) n) ⊗ₘ constFam κ n :=
  (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => X) (μ₀ := μ) (κ := constFam κ) (a := n)).symm

/-! ### Boundedness of the kernel mass as a real number -/

theorem kernel_apply_le_one {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (y : α) (F : Set β) : κ y F ≤ 1 := by
  have h2 : κ y F ≤ κ y Set.univ := measure_mono (Set.subset_univ F)
  rwa [measure_univ] at h2

theorem toReal_kernel_apply_le_one {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (y : α) (F : Set β) : (κ y F).toReal ≤ 1 := by
  calc (κ y F).toReal ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top
        (kernel_apply_le_one κ y F)
    _ = 1 := ENNReal.toReal_one

theorem kernel_apply_lt_top {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (y : α) (F : Set β) : κ y F < ⊤ :=
  lt_of_le_of_lt (kernel_apply_le_one κ y F) ENNReal.one_lt_top

/-! ### The one-step Markov identity -/

/-- **The exact one-step Markov identity of the Ionescu–Tulcea path law.**

For the law `pathLaw κ μ` of the chain driven by `κ` and every measurable `F`,
the conditional expectation of the indicator of `{ω | ω (n+1) ∈ F}` given the canonical
filtration `piLE n` of the past is exactly the kernel mass `κ (ω n) F`, as a real number.

This is the `hstep` of `WCJF.RegenBC.ae_frequently_mem_of_kernel_force_of_tight` for the
actual path law: no extra probabilistic hypothesis is used beyond the construction of the
path measure itself. -/
theorem condExp_indicator_succ (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) {F : Set X} (hF : MeasurableSet F) :
    (pathLaw κ μ)[Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ)) |
        piLE (X := fun _ => X) n]
      =ᵐ[pathLaw κ μ] fun ω => (κ (ω n) F).toReal := by
  classical
  set P : Measure (ℕ → X) := pathLaw κ μ with hPdef
  set f : (ℕ → X) → ((i : ↥(Finset.Iic n)) → X) :=
    Preorder.frestrictLe (π := fun _ => X) n with hfdef
  set G : (ℕ → X) → ℝ := fun ω => (κ (ω n) F).toReal with hGdef
  have hf_meas : Measurable f := by
    simpa [hfdef] using Preorder.measurable_frestrictLe (X := fun _ => X) n
  have hset : MeasurableSet {ω : ℕ → X | ω (n + 1) ∈ F} :=
    measurable_pi_apply (n + 1) hF
  have hGmeas : Measurable G := by
    have h1 : Measurable (fun ω : ℕ → X => (κ (ω n) F)) :=
      (Kernel.measurable_coe κ hF).comp (measurable_pi_apply n)
    simpa [hGdef] using h1.ennreal_toReal
  have hGint : Integrable G P := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact toReal_kernel_apply_le_one κ (ω n) F
  have hF_int : Integrable (Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hset
  have hG' : ∀ x : ℕ → X, G x
      = (fun y : ((i : ↥(Finset.Iic n)) → X) => (constFam κ n y F).toReal) (f x) := by
    intro x
    simp [hGdef, hfdef, constFam_apply]
  have hmeasG' : AEStronglyMeasurable
      (fun y : ((i : ↥(Finset.Iic n)) → X) => (constFam κ n y F).toReal) (P.map f) :=
    ((Kernel.measurable_coe (constFam κ n) hF).ennreal_toReal).aestronglyMeasurable
  -- the key set-integral identity on `piLE n`-measurable sets
  have hkey : ∀ s : Set (ℕ → X), MeasurableSet[piLE (X := fun _ => X) n] s → P s < ∞ →
      ∫ x in s, G x ∂P =
        ∫ x in s, Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ)) x ∂P := by
    intro s hs _
    rw [piLE_eq_comap_frestrictLe] at hs
    obtain ⟨t, htm, hts⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← hts]
    -- right-hand side: the measure of the intersection
    have hright : ∫ x in f ⁻¹' t,
        Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ)) x ∂P
        = (P (f ⁻¹' t ∩ {ω : ℕ → X | ω (n + 1) ∈ F})).toReal := by
      rw [← integral_indicator (hf_meas htm)]
      have hind : (f ⁻¹' t).indicator
          (Set.indicator {ω : ℕ → X | ω (n + 1) ∈ F} (fun _ => (1 : ℝ)))
          = ({ω : ℕ → X | ω (n + 1) ∈ F} ∩ f ⁻¹' t).indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases h1 : x ∈ f ⁻¹' t
        · by_cases h2 : x ∈ {ω : ℕ → X | ω (n + 1) ∈ F} <;>
            simp [Set.indicator, h1, h2]
        · simp [Set.indicator, h1]
      have h1 : ∫ x : ℕ → X,
          ({ω : ℕ → X | ω (n + 1) ∈ F} ∩ f ⁻¹' t).indicator (fun _ => (1 : ℝ)) x ∂P
          = P.real ({ω : ℕ → X | ω (n + 1) ∈ F} ∩ f ⁻¹' t) :=
        integral_indicator_one (hset.inter (hf_meas htm))
      rw [hind, h1, measureReal_def, Set.inter_comm]
    -- left-hand side: push forward along `f` and use the tail factorisation
    have hleft : ∫ x in f ⁻¹' t, G x ∂P
        = ∫ y in t, (constFam κ n y F).toReal ∂(P.map f) := by
      rw [setIntegral_congr_fun (hf_meas htm) (fun x _ => hG' x)]
      exact (setIntegral_map htm hmeasG' hf_meas.aemeasurable).symm
    have htoReal : ∫ y in t, (constFam κ n y F).toReal ∂(P.map f)
        = (∫⁻ y in t, constFam κ n y F ∂(P.map f)).toReal := by
      have h := integral_toReal (μ := (P.map f).restrict t)
        (f := fun y => constFam κ n y F)
        ((Kernel.measurable_coe (constFam κ n) hF).aemeasurable)
        (Eventually.of_forall fun y => kernel_apply_lt_top (constFam κ n) y F)
      simpa using h
    have hcomp : ∫⁻ y in t, constFam κ n y F ∂(P.map f)
        = ((P.map f) ⊗ₘ constFam κ n) (t ×ˢ F) :=
      (Measure.compProd_apply_prod htm hF).symm
    have hpair : (fun ω : ℕ → X => (f ω, ω (n + 1))) ⁻¹' (t ×ˢ F)
        = f ⁻¹' t ∩ {ω : ℕ → X | ω (n + 1) ∈ F} := by
      ext ω; simp
    have hmap : ((P.map f) ⊗ₘ constFam κ n) (t ×ˢ F)
        = P (f ⁻¹' t ∩ {ω : ℕ → X | ω (n + 1) ∈ F}) := by
      have hmpair : Measurable (fun ω : ℕ → X => (f ω, ω (n + 1))) :=
        hf_meas.prodMk (measurable_pi_apply (n + 1))
      rw [← map_pair_frestrictLe_succ κ μ n, Measure.map_apply hmpair (htm.prod hF), hpair]
    rw [hleft, htoReal, hcomp, hmap, hright]
  have hgm : AEStronglyMeasurable[↑(piLE (X := fun _ => X) n)] G P := by
    rw [piLE_eq_comap_frestrictLe]
    have h := AEStronglyMeasurable.comp_ae_measurable' hmeasG' hf_meas.aemeasurable
    refine h.congr ?_
    filter_upwards with x
    exact hG' x
  refine (ae_eq_condExp_of_forall_setIntegral_eq (piLE.le n) hF_int ?_ hkey hgm).symm
  intro s _ _
  exact hGint.integrableOn

/-! ### The regular-conditional-distribution form (standard Borel) -/

/-- **The conditional law of the next point given the past is the kernel at the current
state.**  This is the kernel-valued form of `condExp_indicator_succ`; it is Mathlib's
`condDistrib_trajMeasure` for the homogeneous family, and it needs the standard-Borel
hypothesis of the `condDistrib` API. -/
theorem condDistrib_succ (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    [StandardBorelSpace X] [Nonempty X] :
    condDistrib (fun ω : ℕ → X => ω (n + 1)) (Preorder.frestrictLe (π := fun _ => X) n) (pathLaw κ μ)
      =ᵐ[(pathLaw κ μ).map (Preorder.frestrictLe (π := fun _ => X) n)] ⇑(constFam κ n) :=
  Kernel.condDistrib_trajMeasure (X := fun _ => X) (μ₀ := μ) (κ := constFam κ) (a := n)

/-! ### Restart: the next marginal is the kernel applied to the current marginal -/

/-- **Restart, one-step form.**  The law of `ω (n+1)` is the kernel `κ` composed with the law
of `ω n`: the chain re-starts from the current state with the same transition kernel. -/
theorem map_eval_succ (κ : Kernel X X) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    (pathLaw κ μ).map (fun ω : ℕ → X => ω (n + 1))
      = constFam κ n ∘ₘ ((pathLaw κ μ).map (Preorder.frestrictLe (π := fun _ => X) n)) := by
  have hpair : Measurable (fun ω : ℕ → X =>
      (Preorder.frestrictLe (π := fun _ => X) n ω, ω (n + 1))) := by fun_prop
  have h := congrArg Measure.snd (map_pair_frestrictLe_succ κ μ n)
  rw [Measure.snd_compProd, Measure.snd, Measure.map_map measurable_snd hpair] at h
  simpa [Function.comp_def] using h

end OneStepBridge
end WCJF
