/-
# Finite windows determine a sequence law

The product form `(ℕ → α) × (ℕ → β) ≃ᵐ (ℕ → α × β)` is included because the
repository's `Bridge.JointLawIdentity` lives on `(ℕ → ℕ) × (ℕ → ℕ)` while the
finite-window statements live on `Fin n → ℕ × ℕ`.

No proof holes, no new axioms.
-/
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

set_option autoImplicit false

namespace M2WindowLaw

section Window

variable {β : Type*} [MeasurableSpace β]

/-- The projection of a sequence onto its first `n` coordinates. -/
def window (n : ℕ) : (ℕ → β) → (Fin n → β) := fun x i => x i

theorem measurable_window (n : ℕ) : Measurable (window (β := β) n) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ)

omit [MeasurableSpace β] in
@[simp] theorem window_apply (n : ℕ) (x : ℕ → β) (i : Fin n) :
    window (β := β) n x i = x i := rfl

/-- The `Fin n`-reindexing of the base set of a `Finset`-indexed cylinder. -/
def base (I : Finset ℕ) (n : ℕ) (h : ∀ i ∈ I, i < n) (S : Set (I → β)) :
    Set (Fin n → β) :=
  {f | (fun i : I => f (⟨i.val, h i.val i.property⟩ : Fin n)) ∈ S}

theorem measurableSet_base {I : Finset ℕ} {n : ℕ} {S : Set (I → β)}
    (h : ∀ i ∈ I, i < n) (hS : MeasurableSet S) :
    MeasurableSet (base I n h S) :=
  hS.preimage (measurable_pi_lambda (X := fun _ : I => β)
    (fun (f : Fin n → β) (i : I) => f (⟨i.val, h i.val i.property⟩ : Fin n))
    fun i => measurable_pi_apply (⟨i.val, h i.val i.property⟩ : Fin n))

omit [MeasurableSpace β] in
/-- **A `Finset`-cylinder is the preimage of a window base set.** -/
theorem cylinder_eq_window_preimage {I : Finset ℕ} {n : ℕ} {S : Set (I → β)}
    (h : ∀ i ∈ I, i < n) :
    cylinder I S = window (β := β) n ⁻¹' base I n h S :=
  rfl

/-- **Finite windows determine a probability law on a sequence space.** -/
theorem measure_eq_of_forall_window {μ ν : Measure (ℕ → β)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ n, μ.map (window (β := β) n) = ν.map (window (β := β) n)) : μ = ν := by
  classical
  refine MeasureTheory.ext_of_generate_finite (m0 := MeasurableSpace.pi) (μ := μ) (ν := ν)
    (measurableCylinders (α := fun _ : ℕ => β)) ?_ isPiSystem_measurableCylinders ?_ ?_
  · exact (generateFrom_measurableCylinders (α := fun _ : ℕ => β)).symm
  · intro t ht
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders (α := fun _ : ℕ => β) t).1 ht
    set n := I.sup id + 1 with hn
    have hlt : ∀ i ∈ I, i < n := fun i hi => by
      have hle := Finset.le_sup (f := id) hi
      simp only [id] at hle
      omega
    have hb := measurableSet_base (β := β) (S := S) hlt hS
    rw [cylinder_eq_window_preimage (β := β) hlt,
      ← Measure.map_apply (measurable_window n) hb, h n,
      Measure.map_apply (measurable_window n) hb]
  · rw [measure_univ, measure_univ]

end Window

section Product

variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [MeasurableSpace β]

/-- **The measurable equivalence `(ℕ → α) × (ℕ → β) ≃ᵐ (ℕ → α × β)`** obtained by currying. -/
def prodPiEquiv : ((ℕ → α) × (ℕ → β)) ≃ᵐ (ℕ → α × β) where
  toEquiv :=
    { toFun := fun p n => (p.1 n, p.2 n)
      invFun := fun q => (fun n => (q n).1, fun n => (q n).2)
      left_inv := by intro p; ext n <;> rfl
      right_inv := by intro q; ext n <;> rfl }
  measurable_toFun := measurable_pi_lambda (X := fun _ : ℕ => α × β)
    (fun (p : (ℕ → α) × (ℕ → β)) (n : ℕ) => (p.1 n, p.2 n)) fun n =>
    ((measurable_pi_apply n).comp measurable_fst).prodMk
      ((measurable_pi_apply n).comp measurable_snd)
  measurable_invFun := Measurable.prodMk
    (measurable_pi_lambda (X := fun _ : ℕ => α) (fun (q : ℕ → α × β) (n : ℕ) => (q n).1)
      fun n => measurable_fst.comp (measurable_pi_apply n))
    (measurable_pi_lambda (X := fun _ : ℕ => β) (fun (q : ℕ → α × β) (n : ℕ) => (q n).2)
      fun n => measurable_snd.comp (measurable_pi_apply n))

theorem measurable_prodPiEquiv : Measurable (prodPiEquiv (α := α) (β := β)) :=
  (prodPiEquiv (α := α) (β := β)).measurable_toFun

theorem measurable_prodPiEquiv_symm : Measurable (prodPiEquiv (α := α) (β := β)).symm :=
  (prodPiEquiv (α := α) (β := β)).symm.measurable_toFun

theorem window_comp_prodPiEquiv (n : ℕ) :
    window (β := α × β) n ∘ (prodPiEquiv (α := α) (β := β) : _ → ℕ → α × β)
      = fun p : (ℕ → α) × (ℕ → β) => fun r : Fin n => (p.1 r, p.2 r) := by
  funext p i
  rfl

/-- **Finite windows determine a probability law on a product of two sequence spaces.**
This is the form consumed by `Bridge.JointLawIdentity`. -/
theorem measure_eq_of_forall_window_prod {μ ν : Measure ((ℕ → α) × (ℕ → β))}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n, μ.map (fun p : (ℕ → α) × (ℕ → β) => fun r : Fin n => (p.1 r, p.2 r))
      = ν.map (fun p : (ℕ → α) × (ℕ → β) => fun r : Fin n => (p.1 r, p.2 r))) : μ = ν := by
  have hprobμ : IsProbabilityMeasure (μ.map (prodPiEquiv (α := α) (β := β))) :=
    Measure.isProbabilityMeasure_map (measurable_prodPiEquiv (α := α) (β := β)).aemeasurable
  have hprobν : IsProbabilityMeasure (ν.map (prodPiEquiv (α := α) (β := β))) :=
    Measure.isProbabilityMeasure_map (measurable_prodPiEquiv (α := α) (β := β)).aemeasurable
  have key : ∀ n, (μ.map (prodPiEquiv (α := α) (β := β))).map (window (β := α × β) n)
      = (ν.map (prodPiEquiv (α := α) (β := β))).map (window (β := α × β) n) := by
    intro n
    rw [Measure.map_map (measurable_window n) (measurable_prodPiEquiv (α := α) (β := β)),
      Measure.map_map (measurable_window n) (measurable_prodPiEquiv (α := α) (β := β)),
      window_comp_prodPiEquiv]
    exact h n
  have hmain : μ.map (prodPiEquiv (α := α) (β := β))
      = ν.map (prodPiEquiv (α := α) (β := β)) := measure_eq_of_forall_window key
  have hid : ((prodPiEquiv (α := α) (β := β)).symm :
      (ℕ → α × β) → (ℕ → α) × (ℕ → β)) ∘ (prodPiEquiv (α := α) (β := β)) = id := by
    funext p
    rfl
  have h1 : (μ.map (prodPiEquiv (α := α) (β := β))).map (prodPiEquiv (α := α) (β := β)).symm
      = μ := by
    rw [Measure.map_map (measurable_prodPiEquiv_symm (α := α) (β := β))
      (measurable_prodPiEquiv (α := α) (β := β)), hid, Measure.map_id]
  have h2 : (ν.map (prodPiEquiv (α := α) (β := β))).map (prodPiEquiv (α := α) (β := β)).symm
      = ν := by
    rw [Measure.map_map (measurable_prodPiEquiv_symm (α := α) (β := β))
      (measurable_prodPiEquiv (α := α) (β := β)), hid, Measure.map_id]
  rw [← h1, ← h2, hmain]

end Product

end M2WindowLaw
