/-
# The finite-window (`π`-system) reduction of the chain-side residual `FinHorizonFamily`

`FinHorizonHstruct.FinHorizonFamily` is

  `(★)  μ (Φ ⁻¹' (finStrict K ∩ B)) = π(F) · P(posPath ∈ finStrict K ∩ B)`   for all `K` and all
  measurable `B ⊆ ℕ → Fin N → ℤ`.

`B` is an *arbitrary* measurable subset of the full infinite path space, so at first sight `(★)`
looks like it needs a conditional-independence / disintegration statement about the future of the
chain given its first `K` steps: `finStrict K` reads only the times `≤ K`, but `B` may read any
time.

This file proves that this future dependence is **not** an additional obstruction: it is pure
measure theory.  Gluing Dynkin's `π`-λ theorem on the trace of `finStrict K` with the fact that the
finite path cylinders are a `π`-system generating the path `σ`-algebra gives

  `(★)` for all `B`   ⟺   `(★)` for all *finite-window* sets `pathPat n ⁻¹' C`.

Concretely: `FinHorizonFamily_iff_window`.  The right-hand side is a finite-dimensional statement
at every `n` (a sum over jump words of length `n` on the array side and a finite
Ionescu–Tulcea integral over the first `n+1` enriched coordinates on the chain side), so the
residual is reduced to a genuinely finite word/cylinder identity, with no future-`σ`-algebra
hypothesis and no regular conditional distribution anywhere.

Main results:

* `isPiSystem_pathCyl` / `generateFrom_pathCyl`: the finite path cylinders form a `π`-system that
  generates the path `σ`-algebra.
* `measure_finStrict_inter_eq_of_pathCyl`: if two finite measures agree on `finStrict K ∩ cyl` for
  every finite cylinder, they agree on `finStrict K ∩ B` for every measurable `B`.  This is the
  Dynkin step, proved by induction on measurable sets with the finiteness of `μ (finStrict K)`.
* `FinHorizonWindow`: the finite-window family `(★)`, and `FinHorizonFamily_iff_window`: `(★)` ⟺
  `(★)` restricted to finite windows.
* `hstruct_mass_form_of_window`: the `π(F)·P(V ∩ B)` form of the paper's `hstruct` follows from
  the window family (via `FinHorizonHstruct.hstruct_of_finHorizonFamily`).

Scope: no invariant `π`, no tightness, no `RegenAvail`, no stationarity and no positivity of `π(F)`
is used or claimed; `π` is an arbitrary probability on record states and `μ` an arbitrary ambient
probability law with a measurable path map `Φ`.  The window family itself is *not* proved here.
-/
import Swarm.FinHorizonHstruct
import Swarm.ChainAssemble
import Swarm.InfSeg
import Swarm.InfSegCompat

open MeasureTheory Set
open scoped ENNReal
open SimJump
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec SwarmFresh SwarmFreshPos

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmFinHorizon

attribute [local instance] Classical.propDecidable

variable {N m : ℕ}

/-! ## 1. The finite path cylinders -/

/-- `pathPat` is measurable. -/
theorem measurable_pathPat (n : ℕ) : Measurable (pathPat (N := N) n) := by
  refine measurable_pi_iff.mpr fun k => ?_
  refine measurable_pi_iff.mpr fun i => ?_
  exact (measurable_pi_apply (X := fun _ : Fin N => ℤ) i).comp
    (measurable_pi_apply (X := fun _ : ℕ => (Fin N → ℤ)) (k : ℕ))

/-- The family of finite path cylinders: "the first `n+1` positions lie in `C`". -/
def pathCyl (N : ℕ) : Set (Set (ℕ → Fin N → ℤ)) :=
  {s | ∃ (n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)), MeasurableSet C ∧
    pathPat (N := N) n ⁻¹' C = s}

/-- A cylinder over the first `n+1` positions is also a cylinder over the first `n'+1` positions
for every `n' ≥ n`.  This is what makes `pathCyl` closed under binary intersections without any
compatibility between word lengths. -/
theorem pathCyl_mono_window {n n' : ℕ} (hn : n ≤ n') {C : Set (Fin (n + 1) → Fin N → ℤ)}
    (hC : MeasurableSet C) :
    ∃ C' : Set (Fin (n' + 1) → Fin N → ℤ), MeasurableSet C' ∧
      pathPat (N := N) n ⁻¹' C = pathPat (N := N) n' ⁻¹' C' := by
  refine ⟨{f : Fin (n' + 1) → Fin N → ℤ |
      (fun k : Fin (n + 1) => f ⟨(k : ℕ), by omega⟩) ∈ C}, ?_, ?_⟩
  · exact hC.preimage (measurable_pi_iff.mpr fun k => measurable_pi_apply _)
  · ext X
    simp only [mem_preimage, mem_ofPred_eq]
    rfl

/-- The finite path cylinders are a `π`-system. -/
theorem isPiSystem_pathCyl : IsPiSystem (pathCyl N) := by
  rintro s1 ⟨n1, C1, hC1, rfl⟩ s2 ⟨n2, C2, hC2, rfl⟩ -
  rcases le_total n1 n2 with h | h
  · obtain ⟨C1', hC1', heq⟩ := pathCyl_mono_window (N := N) h hC1
    refine ⟨n2, C1' ∩ C2, hC1'.inter hC2, ?_⟩
    rw [heq, Set.preimage_inter]
  · obtain ⟨C2', hC2', heq⟩ := pathCyl_mono_window (N := N) h hC2
    refine ⟨n1, C1 ∩ C2', hC1.inter hC2', ?_⟩
    rw [heq, Set.preimage_inter, Set.inter_comm]

/-- Every finite path cylinder is measurable. -/
theorem measurableSet_of_mem_pathCyl {s : Set (ℕ → Fin N → ℤ)} (hs : s ∈ pathCyl N) :
    MeasurableSet s := by
  obtain ⟨n, C, hC, rfl⟩ := hs
  exact hC.preimage (measurable_pathPat n)

/-- The finite path cylinders generate the path `σ`-algebra. -/
theorem generateFrom_pathCyl :
    MeasurableSpace.generateFrom (pathCyl N)
      = (inferInstance : MeasurableSpace (ℕ → Fin N → ℤ)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun t ht =>
    measurableSet_of_mem_pathCyl (N := N) ht) ?_
  have hpi := MeasurableSpace.pi_eq_generateFrom_projections
    (α := fun _ : ℕ => (Fin N → ℤ)) (mα := fun _ => inferInstance)
  refine hpi.symm ▸ MeasurableSpace.generateFrom_le fun B hB => ?_
  obtain ⟨i, A, hA, rfl⟩ := hB
  refine MeasurableSpace.measurableSet_generateFrom ⟨i, {f : Fin (i + 1) → Fin N → ℤ | f ⟨i, by omega⟩ ∈ A},
    hA.preimage (measurable_pi_apply _), ?_⟩
  ext X
  simp only [mem_preimage, mem_ofPred_eq]
  rfl

/-! ## 2. The Dynkin step on the trace of `finStrict K` -/

/-- **Agreement on all finite cylinders propagates to all measurable sets, inside `finStrict K`.**

Two measures on path space that are finite on `finStrict K` and agree there on every finite
cylinder also agree there on every measurable `B`.  The proof is the `π`-λ theorem, in the form
`MeasurableSpace.induction_on_inter`, applied to the `π`-system of finite cylinders; the
`finStrict K` factor is carried through by hand, and its finiteness is what makes the complement
step work (`μ (F ∩ tᶜ) = μ F - μ (F ∩ t)`). -/
theorem measure_finStrict_inter_eq_of_pathCyl {K : ℕ} {μ1 μ2 : Measure (ℕ → Fin N → ℤ)}
    (_h1 : μ1 (finStrict (N := N) K) ≠ ⊤) (h2 : μ2 (finStrict (N := N) K) ≠ ⊤)
    (h : ∀ (n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)), MeasurableSet C →
      μ1 (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C)
        = μ2 (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C)) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ1 (finStrict (N := N) K ∩ B) = μ2 (finStrict (N := N) K ∩ B) := by
  have hF : MeasurableSet (finStrict (N := N) K) := measurableSet_finStrict K
  have hFK : μ1 (finStrict (N := N) K) = μ2 (finStrict (N := N) K) := by
    have := h 0 univ MeasurableSet.univ
    simpa using this
  -- the split identity `μ (F ∩ tᶜ) + μ (F ∩ t) = μ F`
  have hsplit : ∀ (μ : Measure (ℕ → Fin N → ℤ)) (t : Set (ℕ → Fin N → ℤ)), MeasurableSet t →
      μ (finStrict (N := N) K ∩ tᶜ) + μ (finStrict (N := N) K ∩ t)
        = μ (finStrict (N := N) K) := by
    intro μ t ht
    rw [← measure_union (s₁ := finStrict (N := N) K ∩ tᶜ)
      (s₂ := finStrict (N := N) K ∩ t) (Set.disjoint_left.mpr fun x hx hy => hx.2 hy.2)
      (hF.inter ht)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_union]
    tauto
  have key : ∀ s : Set (ℕ → Fin N → ℤ), MeasurableSet s →
      μ1 (finStrict (N := N) K ∩ s) = μ2 (finStrict (N := N) K ∩ s) := by
    intro s hs
    refine MeasurableSpace.induction_on_inter
      (m := (inferInstance : MeasurableSpace (ℕ → Fin N → ℤ)))
      (C := fun s _ => μ1 (finStrict (N := N) K ∩ s) = μ2 (finStrict (N := N) K ∩ s))
      (s := pathCyl N) generateFrom_pathCyl.symm isPiSystem_pathCyl ?_ ?_ ?_ ?_ s hs
    · simp
    · rintro t ⟨n, C, hC, rfl⟩
      exact h n C hC
    · intro t htm ih
      have e1 := hsplit μ1 t htm
      have e2 := hsplit μ2 t htm
      rw [ih, hFK] at e1
      have hc : μ2 (finStrict (N := N) K ∩ t) ≠ ⊤ :=
        ne_top_of_le_ne_top h2 (measure_mono Set.inter_subset_left)
      exact (ENNReal.add_left_inj hc).mp (e1.trans e2.symm)
    · intro f hfd hfm ihf
      have hdisj : Pairwise (fun i j => Disjoint (finStrict (N := N) K ∩ f i)
          (finStrict (N := N) K ∩ f j)) :=
        fun i j hij => (hfd hij).mono Set.inter_subset_right Set.inter_subset_right
      have hmeas : ∀ i, MeasurableSet (finStrict (N := N) K ∩ f i) := fun i => hF.inter (hfm i)
      calc μ1 (finStrict (N := N) K ∩ ⋃ i, f i)
          = μ1 (⋃ i, finStrict (N := N) K ∩ f i) := by rw [Set.inter_iUnion]
        _ = ∑' i, μ1 (finStrict (N := N) K ∩ f i) := measure_iUnion hdisj hmeas
        _ = ∑' i, μ2 (finStrict (N := N) K ∩ f i) := tsum_congr ihf
        _ = μ2 (⋃ i, finStrict (N := N) K ∩ f i) := (measure_iUnion hdisj hmeas).symm
        _ = μ2 (finStrict (N := N) K ∩ ⋃ i, f i) := by rw [Set.inter_iUnion]
  exact fun B hB => key B hB

/-! ## 3. The finite-window family `(★)` -/

/-- **The finite-window version of the residual `(★)`.**  Only finite cylinders of the path are
tested.  `n` is the window width; the case `n = K` is the "first `K+1` positions" slice, and the
cases `n > K` are the accumulated finite future cylinders. -/
def FinHorizonWindow (p : ℝ) (π : Measure (RecState N m)) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Φ : Ω → (ℕ → Fin N → ℤ)) : Prop :=
  ∀ (K : ℕ) (n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)), MeasurableSet C →
    μ (Φ ⁻¹' (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C))
      = π (srSet N m) * (arrayMeasure N)
          {U : Array N | posPath p m U ∈ finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C}

/-- The window family is an instance of the full family (no measure theory). -/
theorem finHorizonFamily_of_window {p : ℝ} {π : Measure (RecState N m)}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure π] {Φ : Ω → (ℕ → Fin N → ℤ)} (hΦ : Measurable Φ)
    (h : FinHorizonWindow (N := N) (m := m) p π μ Φ) :
    FinHorizonFamily (N := N) (m := m) p π μ Φ := by
  intro K B hB
  set ν : Measure (ℕ → Fin N → ℤ) := (arrayMeasure N).map (posPath p m) with hν
  have hνfin : ν univ ≠ ⊤ := by
    rw [hν, Measure.map_apply (measurable_posPath p m N) MeasurableSet.univ]
    simp
  have h1 : (μ.map Φ) (finStrict (N := N) K) ≠ ⊤ := by
    rw [Measure.map_apply hΦ (measurableSet_finStrict K)]
    exact measure_ne_top _ _
  have h2 : (π (srSet N m) • ν) (finStrict (N := N) K) ≠ ⊤ := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_ne_top (measure_ne_top _ _)
      (ne_top_of_le_ne_top hνfin (measure_mono (Set.subset_univ _)))
  have hcyl : ∀ (n : ℕ) (C : Set (Fin (n + 1) → Fin N → ℤ)), MeasurableSet C →
      (μ.map Φ) (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C)
        = (π (srSet N m) • ν) (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C) := by
    intro n C hC
    have hmeas : MeasurableSet (finStrict (N := N) K ∩ pathPat (N := N) n ⁻¹' C) :=
      (measurableSet_finStrict K).inter (hC.preimage (measurable_pathPat n))
    rw [Measure.map_apply hΦ hmeas, Measure.smul_apply, hν,
      Measure.map_apply (measurable_posPath p m N) hmeas]
    exact h K n C hC
  have hmain := measure_finStrict_inter_eq_of_pathCyl (N := N) h1 h2 hcyl B hB
  have hmeas : MeasurableSet (finStrict (N := N) K ∩ B) :=
    (measurableSet_finStrict K).inter hB
  rw [Measure.map_apply hΦ hmeas, Measure.smul_apply, hν,
    Measure.map_apply (measurable_posPath p m N) hmeas] at hmain
  exact hmain

/-- The full family is a window family (immediate). -/
theorem window_of_finHorizonFamily {p : ℝ} {π : Measure (RecState N m)}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Φ : Ω → (ℕ → Fin N → ℤ)}
    (h : FinHorizonFamily (N := N) (m := m) p π μ Φ) :
    FinHorizonWindow (N := N) (m := m) p π μ Φ :=
  fun K n C hC => h K (pathPat (N := N) n ⁻¹' C) (hC.preimage (measurable_pathPat n))

/-- **The finite-window reduction.**  The chain-side residual `(★)` is *equivalent* to its
restriction to finite path windows.  No conditional independence, disintegration or future
`σ`-algebra statement is hidden in the difference. -/
theorem FinHorizonFamily_iff_window {p : ℝ} {π : Measure (RecState N m)}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure π] {Φ : Ω → (ℕ → Fin N → ℤ)} (hΦ : Measurable Φ) :
    FinHorizonFamily (N := N) (m := m) p π μ Φ
      ↔ FinHorizonWindow (N := N) (m := m) p π μ Φ :=
  ⟨window_of_finHorizonFamily, finHorizonFamily_of_window hΦ⟩

/-- **`hstruct` from the finite-window family**: the `π(F)·P(V ∩ B)` mass form of the paper's
structural identity follows from the finite-window residual alone. -/
theorem hstruct_mass_form_of_window [IsProbabilityMeasure (arrayMeasure N)] (hm : 1 ≤ m) (p : ℝ)
    (π : Measure (RecState N m)) [IsProbabilityMeasure π] (hπ : 0 < π (srSet N m))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Φ : Ω → (ℕ → Fin N → ℤ)) (hΦ : Measurable Φ)
    (A : Set Ω) (hA : A = Φ ⁻¹' strictPos (N := N))
    (h : FinHorizonWindow (N := N) (m := m) p π μ Φ) :
    ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
      μ (A ∩ Φ ⁻¹' B)
        = π (srSet N m) * (arrayMeasure N)
            {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} :=
  hstruct_mass_form_of_finHorizon (N := N) hm p π hπ Φ hΦ A hA
    (finHorizonFamily_of_window hΦ h)

end SwarmFinHorizon


