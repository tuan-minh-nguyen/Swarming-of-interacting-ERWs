/-
# The record chain as a path measure (Ionescu–Tulcea)

`ChainLink.lean` builds the stopped record kernel `hitKKernel` on `RecState N m`.  This file
constructs the **law of the whole record chain** on the trajectory space `ℕ → RecState N m`
using Mathlib's Ionescu–Tulcea theorem (`ProbabilityTheory.Kernel.trajMeasure`), and proves that
its one-dimensional marginals are exactly the iterates of the kernel:

  `(homTraj κ μ).map (fun ω => ω r) = (step κ)^[r] μ`.

Consequently the tightness input `htight` of
`Swarm/InfKernel.lean`'s `exists_invariant_measure_pos_hitKInf` is *literally* a
path-law tail probability,

  `(step hitKKernel)^[r] μ (exh N m K)ᶜ = (homTraj hitKKernel μ) {ω | ω r ∉ exh N m K}`,

and the same holds for the time-extended kernel `hitKKernelT` of `ChainLink.lean`.

No proof holes.  Imports `ChainLink`.
-/
import Swarm.ChainLink

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

variable {X : Type*} [MeasurableSpace X]

/-! ### The homogeneous Ionescu–Tulcea family of a single Markov kernel -/

/-- The homogeneous family of a single kernel `κ`, in the shape required by
`ProbabilityTheory.Kernel.trajMeasure`: at step `n` the next value is drawn from `κ` at the
`n`-th coordinate of the partial trajectory. -/
noncomputable def homFam (κ : Kernel X X) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → X) X :=
  κ.comap (fun f => f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

theorem homFam_apply (κ : Kernel X X) (n : ℕ) (f : (i : ↥(Finset.Iic n)) → X) :
    homFam κ n f = κ (f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rw [homFam, Kernel.comap_apply]

instance homFam.instIsMarkovKernel (κ : Kernel X X) [IsMarkovKernel κ] :
    ∀ n, IsMarkovKernel (homFam κ n) :=
  fun _ => Kernel.IsMarkovKernel.comap κ (measurable_pi_apply _)

/-- The `n`-th coordinate of a partial trajectory. -/
def evIic (n : ℕ) : ((i : ↥(Finset.Iic n)) → X) → X :=
  fun f => f ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The law of the whole chain started from `μ`. -/
noncomputable def homTraj (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X) :
    Measure (ℕ → X) :=
  ProbabilityTheory.Kernel.trajMeasure (X := fun _ => X) μ (homFam κ)

theorem homTraj_def (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X) :
    homTraj κ μ
      = (ProbabilityTheory.Kernel.traj (X := fun _ => X) (homFam κ) 0)
          ∘ₘ (μ.map (MeasurableEquiv.piUnique (fun _ => X)).symm) := rfl

/-- The composition of the `n`-th coordinate with the restriction to `≤ n` is the `n`-th
coordinate. -/
theorem evIic_comp_frestrictLe (n : ℕ) :
    evIic (X := X) n ∘ (Preorder.frestrictLe (π := fun _ => X) n) =
      fun ω : ℕ → X => ω n := by
  funext ω
  rfl

/-! ### The one-step recursion -/

theorem homTraj_map_succ (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X)
    [IsProbabilityMeasure μ] (b : ℕ) :
    (homTraj κ μ).map (fun ω : ℕ → X => ω (b + 1))
      = SwarmKB.step κ ((homTraj κ μ).map (fun ω : ℕ → X => ω b)) := by
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ => X) b :
      (ℕ → X) → ((i : ↥(Finset.Iic b)) → X)) := by fun_prop
  have hg : Measurable (fun f : (i : ↥(Finset.Iic b)) → X =>
      f ⟨b, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have hP : Measurable (fun x : ℕ → X =>
      ((Preorder.frestrictLe (π := fun _ => X) b) x, x (b + 1))) :=
    hfr.prodMk (measurable_pi_apply (b + 1))
  have hcomp := ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => X) (μ₀ := μ) (κ := homFam κ) (a := b)
  have hsnd : homFam κ b ∘ₘ (Measure.map (Preorder.frestrictLe (π := fun _ => X) b)
        (ProbabilityTheory.Kernel.trajMeasure (X := fun _ => X) μ (homFam κ)))
      = Measure.map (fun x : ℕ → X => x (b + 1))
        (ProbabilityTheory.Kernel.trajMeasure (X := fun _ => X) μ (homFam κ)) := by
    have h := congrArg Measure.snd hcomp
    rw [Measure.snd_compProd, Measure.snd, Measure.map_map measurable_snd hP] at h
    rwa [show (Prod.snd ∘ (fun x : ℕ → X =>
        ((Preorder.frestrictLe (π := fun _ => X) b) x, x (b + 1))))
      = (fun x : ℕ → X => x (b + 1)) from rfl] at h
  have hstep : homFam κ b ∘ₘ ((homTraj κ μ).map (Preorder.frestrictLe (π := fun _ => X) b))
      = ⇑κ ∘ₘ ((homTraj κ μ).map (fun x : ℕ → X => x b)) := by
    rw [homFam, ← Kernel.comp_deterministic_eq_comap κ hg, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map (μ :=
        (homTraj κ μ).map (Preorder.frestrictLe (π := fun _ => X) b)) hg,
      Measure.map_map hg hfr]
    rfl
  calc (homTraj κ μ).map (fun ω : ℕ → X => ω (b + 1))
      = homFam κ b ∘ₘ ((homTraj κ μ).map (Preorder.frestrictLe (π := fun _ => X) b)) :=
        hsnd.symm
    _ = ⇑κ ∘ₘ ((homTraj κ μ).map (fun ω : ℕ → X => ω b)) := hstep
    _ = SwarmKB.step κ ((homTraj κ μ).map (fun ω : ℕ → X => ω b)) := rfl

/-! ### The law of the initial coordinate -/

theorem homTraj_map_zero (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    (homTraj κ μ).map (fun ω : ℕ → X => ω 0) = μ := by
  have hval : ((default : ↥(Finset.Iic (0 : ℕ))) : ℕ) = 0 := by
    have h := Finset.mem_Iic.mp (default : ↥(Finset.Iic (0 : ℕ))).2
    omega
  have hev : (fun ω : ℕ → X => ω 0) =
      (MeasurableEquiv.piUnique (fun _ => X)) ∘
        (Preorder.frestrictLe (π := fun _ => X) 0) := by
    funext ω
    show ω 0 = ((Preorder.frestrictLe (π := fun _ => X) 0) ω) default
    rw [Preorder.frestrictLe_apply, hval]
  have hfr0 : (homTraj κ μ).map (Preorder.frestrictLe (π := fun _ => X) 0)
      = μ.map (MeasurableEquiv.piUnique (fun _ => X)).symm := by
    rw [homTraj_def, Measure.map_comp _ _ (by fun_prop),
      ProbabilityTheory.Kernel.traj_map_frestrictLe (b := 0),
      ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [hev,
    ← Measure.map_map (MeasurableEquiv.piUnique (fun _ => X)).measurable
      (by fun_prop : Measurable (Preorder.frestrictLe (π := fun _ => X) 0)), hfr0,
    Measure.map_map (MeasurableEquiv.piUnique (fun _ => X)).measurable
      (MeasurableEquiv.piUnique (fun _ => X)).symm.measurable,
    MeasurableEquiv.self_comp_symm, Measure.map_id]

/-! ### The marginals are the iterates -/

theorem homTraj_map_eval (κ : Kernel X X) [IsMarkovKernel κ] (μ : Measure X)
    [IsProbabilityMeasure μ] (r : ℕ) :
    (homTraj κ μ).map (fun ω : ℕ → X => ω r) = (SwarmKB.step κ)^[r] μ := by
  induction r with
  | zero => simpa using homTraj_map_zero κ μ
  | succ r ih =>
      rw [homTraj_map_succ κ μ r, ih, Function.iterate_succ_apply']

end RecKernel
end SimJump
