/-
# Kolmogorov extension for non-compact factors via a compact factor with a measurable retraction

`Swarm/KolExt.lean` proves existence of the projective limit of a countable projective family of
probability measures when every factor is a **compact** second-countable T2 space with the given
Borel σ-algebra.  `areas/kac/RecTop.lean` shows the record-state space `SwarmRec.RecState N m` is
σ-compact and **not** compact for `2 ≤ N`, so `KolExt` cannot be instantiated at it; that is the
obstruction recorded in `areas/kac/KAC_EXTENSION.md` §2 for the existence of a stationary version
of the record chain.

This file proves the extension theorem for factors that are not compact, but admit a **measurable
embedding into a compact metrizable space with a measurable left inverse**:

* `e : α → γ` injective and measurable, `r : γ → α` measurable with `r ∘ e = id`.

The proof is purely functorial: push the window laws forward along `e`, extend with
`SwarmKol.exists_isProjectiveLimit` (which needs the compact factor `γ`), and pull back along `r`.
Nothing is lost because on each window `r` and `e` are mutually inverse, so
`((P J).map (e on J)).map (r on J) = P J` by `Measure.map_map` and `Measure.map_id`
(`isProjectiveLimit_map_retrPi`).  No tightness, no Prokhorov theorem, no regularity of measures and
no concentration/a.e. argument is used.

## Main results

* `SwarmKolNC.exists_isProjectiveLimit_of_compactRetract` — extension when every factor admits such
  a compact retract.
* `SwarmKolNC.exists_isProjectiveLimit_of_countable` — the countable case, where the compact retract
  `[0,1] ⊇ embC δ` is constructed explicitly.
* `SwarmKolNC.exists_stationary_isProjectiveLimit_of_compactRetract` — the `ℤ`-indexed
  shift-stationary form producing the shift-invariant (hence invertible) two-sided law.
* `SwarmKolNC.recRetr` / `recEmb` — the concrete compact retract of the record-state space
  `SwarmRec.RecState N m` onto `[0,1] × (Fin N → ℤ → Fin (m+1))` (all of the non-compactness of the
  record-state space sits in the half-distance vector `Fin N → ℕ`, which is countable, so `embC`
  compactifies it; the local-time profile is already a compact product).
* `SwarmKolNC.exists_stationary_isProjectiveLimit_recState` — consequently the stationary two-sided
  extension exists for **any** shift-stationary projective family of probability measures on windows
  of record states.  The only remaining input is the family itself (the record window laws, its
  projectivity and its shift-stationarity), which is a statement about the record dynamics and is
  not constructed here.

No claim about `MainClaim`, `Ballistic`, common speed, the invariant record law, regeneration,
`h1` or `h2`.
-/
import Swarm.KolExt
import Swarm.RecordState

open MeasureTheory Set Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace SwarmKolNC

/-- The compact metric space `[0,1]`. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-! ## Measurability into a countable space with measurable singletons -/

section CountableCodomain

variable {γ β : Type*} [MeasurableSpace γ] [MeasurableSpace β]

/-- A function into a countable space whose singletons are measurable is measurable as soon as the
preimages of singletons are measurable. -/
theorem measurable_of_countable_codomain [Countable β] [MeasurableSingletonClass β]
    (f : γ → β) (h : ∀ b, MeasurableSet (f ⁻¹' {b})) : Measurable f := by
  intro s _
  have hEq : f ⁻¹' s = ⋃ b ∈ s, f ⁻¹' ({b} : Set β) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    exact ⟨fun hx => ⟨f x, hx, rfl⟩, fun ⟨b, hb, hxb⟩ => hxb ▸ hb⟩
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable s) fun b _ => h b

/-- Every subset of a countable space with measurable singletons is measurable. -/
theorem measurableSet_of_countable [Countable β] [MeasurableSingletonClass β] (s : Set β) :
    MeasurableSet s :=
  Set.Countable.measurableSet (Set.to_countable s)

end CountableCodomain

/-! ## Measurability of the shift and of a window reindexing -/

section Shifts

variable {β : Type*} [MeasurableSpace β]

/-- Measurability of the shift of a two-sided path.  (`SwarmKol.measurable_pathShift` carries the
compactness instance of its section; the map itself needs none.) -/
theorem measurable_pathShift' (k : ℤ) : Measurable (SwarmKol.pathShift (β := β) k) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- Measurability of the reindexing of a window under a shift. -/
theorem measurable_winReindex' (k : ℤ) (I : Finset ℤ) :
    Measurable (SwarmKol.winReindex (β := β) k I) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply _

end Shifts

/-! ## A uniform compactification of a countable type -/

section Core

variable (δ : Type*) [Countable δ] [Nonempty δ]

/-- A fixed injection of a countable type into `ℕ`. -/
noncomputable def natInjC : δ → ℕ := (Countable.exists_injective_nat δ).choose

theorem natInjC_injective : Function.Injective (natInjC δ) :=
  (Countable.exists_injective_nat δ).choose_spec

/-- The injection `a ↦ 1 / (n a + 1)` of a countable type into the compact metric space `[0,1]`.
It depends on the type only, so it is the same function at every index of an indexed family with
constant fibres. -/
noncomputable def embC : δ → UnitInterval := fun a =>
  ⟨1 / ((natInjC δ a : ℝ) + 1), by
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by positivity)]
      have h : (0 : ℝ) ≤ (natInjC δ a : ℝ) := Nat.cast_nonneg _
      linarith⟩

theorem embC_injective : Function.Injective (embC δ) := by
  intro a b hab
  have hv : 1 / ((natInjC δ a : ℝ) + 1) = 1 / ((natInjC δ b : ℝ) + 1) :=
    congrArg Subtype.val hab
  have ha : ((natInjC δ a : ℝ) + 1) ≠ 0 := by positivity
  have hb : ((natInjC δ b : ℝ) + 1) ≠ 0 := by positivity
  rw [div_eq_div_iff ha hb] at hv
  have h2 : (natInjC δ a : ℝ) = (natInjC δ b : ℝ) := by linarith
  exact natInjC_injective δ (Nat.cast_injective h2)

/-- A left inverse of `embC`, junk off the range of `embC`. -/
noncomputable def retrC : UnitInterval → δ := by
  classical
  exact fun y => if h : y ∈ Set.range (embC δ) then h.choose else Classical.arbitrary δ

theorem retrC_embC (a : δ) : retrC δ (embC δ a) = a := by
  classical
  have hmem : embC δ a ∈ Set.range (embC δ) := ⟨a, rfl⟩
  unfold retrC
  rw [dif_pos hmem]
  exact embC_injective δ hmem.choose_spec

theorem embC_retrC {y : UnitInterval} (hy : y ∈ Set.range (embC δ)) :
    embC δ (retrC δ y) = y := by
  classical
  unfold retrC
  rw [dif_pos hy]
  exact hy.choose_spec

theorem retrC_of_not_mem {y : UnitInterval} (hy : y ∉ Set.range (embC δ)) :
    retrC δ y = Classical.arbitrary δ := by
  classical
  unfold retrC
  rw [dif_neg hy]

theorem measurable_embC [MeasurableSpace δ] [MeasurableSingletonClass δ] :
    Measurable (embC δ) := measurable_of_countable _

theorem countable_range_embC : (Set.range (embC δ)).Countable := Set.countable_range _

/-- The left inverse is measurable: it is the inverse of the injection on the range of the
injection (countable, hence Borel) and constant off it. -/
theorem measurable_retrC [MeasurableSpace δ] [MeasurableSingletonClass δ] :
    Measurable (retrC δ) := by
  classical
  refine measurable_of_countable_codomain _ fun a => ?_
  by_cases ha : a = Classical.arbitrary δ
  · have hpre : retrC δ ⁻¹' {a} = {embC δ a} ∪ (Set.range (embC δ))ᶜ := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_compl_iff]
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range (embC δ)
        · exact Or.inl (by rw [← embC_retrC (δ := δ) hyr, ← hy])
        · rw [retrC_of_not_mem (δ := δ) hyr] at hy
          exact Or.inr hyr
      · rintro (h1 | h2)
        · rw [h1]
          exact retrC_embC δ a
        · rw [retrC_of_not_mem (δ := δ) h2]
          exact ha.symm
    rw [hpre]
    exact (measurableSet_singleton (embC δ a)).union
      (Set.Countable.measurableSet (countable_range_embC δ)).compl
  · have hpre : retrC δ ⁻¹' {a} = {embC δ a} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hy
        by_cases hyr : y ∈ Set.range (embC δ)
        · rw [← embC_retrC (δ := δ) hyr, ← hy]
        · rw [retrC_of_not_mem (δ := δ) hyr] at hy
          exact absurd hy.symm ha
      · intro hy
        rw [hy]
        exact retrC_embC δ a
    rw [hpre]
    exact measurableSet_singleton _

end Core

/-! ## Extension for factors with a compact measurable retract -/

section Abstract

variable {ι : Type*} [Countable ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, MeasurableSpace (γ i)]
  [∀ i, T2Space (γ i)] [∀ i, CompactSpace (γ i)] [∀ i, SecondCountableTopology (γ i)]
  [∀ i, BorelSpace (γ i)] [∀ i, Nonempty (γ i)]
variable {e : ∀ i, α i → γ i} {r : ∀ i, γ i → α i}

/-- Coordinatewise embedding of a finite window by the factor embeddings. -/
noncomputable def embWin (e : ∀ i, α i → γ i) (J : Finset ι) :
    (Π j : J, α j) → (Π j : J, γ j) := fun v j => e (j : ι) (v j)

/-- Coordinatewise retraction of a finite window. -/
noncomputable def retrWin (r : ∀ i, γ i → α i) (J : Finset ι) :
    (Π j : J, γ j) → (Π j : J, α j) := fun v j => r (j : ι) (v j)

/-- Coordinatewise retraction of the full product. -/
noncomputable def retrPi (r : ∀ i, γ i → α i) : (Π i, γ i) → (Π i, α i) := fun y i => r i (y i)

theorem measurable_embWin (he : ∀ i, Measurable (e i)) (J : Finset ι) :
    Measurable (embWin e J) :=
  measurable_pi_lambda _ fun j => (he (j : ι)).comp (measurable_pi_apply j)

theorem measurable_retrWin (hr : ∀ i, Measurable (r i)) (J : Finset ι) :
    Measurable (retrWin r J) :=
  measurable_pi_lambda _ fun j => (hr (j : ι)).comp (measurable_pi_apply j)

theorem measurable_retrPi (hr : ∀ i, Measurable (r i)) : Measurable (retrPi r) :=
  measurable_pi_lambda _ fun i => (hr i).comp (measurable_pi_apply i)

theorem retrWin_embWin (hri : ∀ i, Function.LeftInverse (r i) (e i)) (J : Finset ι) :
    Function.LeftInverse (retrWin r J) (embWin e J) :=
  fun v => funext fun j => hri (j : ι) (v j)

variable {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

/-- The window laws pushed forward to the compact factors. -/
noncomputable def pushFamily (e : ∀ i, α i → γ i)
    (P : ∀ J : Finset ι, Measure (Π j : J, α j)) (J : Finset ι) :
    Measure (Π j : J, γ j) :=
  (P J).map (embWin e J)

theorem isProjectiveMeasureFamily_pushFamily (he : ∀ i, Measurable (e i))
    (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamily (pushFamily e P) := by
  intro I J hJI
  have hcomp : (embWin e J) ∘ (Finset.restrict₂ (π := α) hJI)
      = (Finset.restrict₂ (π := γ) hJI) ∘ (embWin e I) := by
    funext v j
    simp only [Function.comp_apply, embWin, Finset.restrict₂]
  simp only [pushFamily]
  rw [hP I J hJI, Measure.map_map (measurable_embWin he J)
      (Finset.measurable_restrict₂ (X := α) hJI)]
  rw [Measure.map_map (Finset.measurable_restrict₂ (X := γ) hJI) (measurable_embWin he I), hcomp]

/-- Pulling a projective limit of the pushed-forward family back along the retraction gives a
projective limit of the original family.  Only `Function.LeftInverse (retrWin J) (embWin J)` is
used: no a.e. statement, no concentration and no regularity. -/
theorem isProjectiveLimit_map_retrPi (he : ∀ i, Measurable (e i)) (hr : ∀ i, Measurable (r i))
    (hri : ∀ i, Function.LeftInverse (r i) (e i)) {ν : Measure (Π i, γ i)}
    (hν : IsProjectiveLimit ν (pushFamily e P)) :
    IsProjectiveLimit (ν.map (retrPi r)) P := by
  intro I
  have hswap : ((I.restrict : (Π i, α i) → (Π j : I, α j)) ∘ retrPi r)
      = (retrWin r I) ∘ (I.restrict : (Π i, γ i) → (Π j : I, γ j)) := by
    funext y j
    rfl
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_retrPi hr), hswap,
    ← Measure.map_map (measurable_retrWin hr I) (Finset.measurable_restrict I), hν I]
  simp only [pushFamily]
  rw [Measure.map_map (measurable_retrWin hr I) (measurable_embWin he I),
    show retrWin r I ∘ embWin e I = id from funext (retrWin_embWin hri I), Measure.map_id]

/-- **Kolmogorov extension for factors with a compact measurable retract.**  If every factor `α i`
embeds measurably into a compact second-countable T2 space `γ i` with a measurable left inverse,
then every projective family of probability measures on finite windows of `Π i, α i` has a projective
limit.  The factors `α i` themselves need not be compact, second countable or even topological. -/
theorem exists_isProjectiveLimit_of_compactRetract (he : ∀ i, Measurable (e i))
    (hr : ∀ i, Measurable (r i)) (hri : ∀ i, Function.LeftInverse (r i) (e i))
    (hP : IsProjectiveMeasureFamily P) (hprob : ∀ J, IsProbabilityMeasure (P J)) :
    ∃ μ : Measure (Π i, α i), IsProjectiveLimit μ P := by
  classical
  have hprob' : ∀ J, IsProbabilityMeasure (pushFamily e P J) := fun J =>
    Measure.isProbabilityMeasure_map (measurable_embWin he J).aemeasurable
  obtain ⟨ν, hν⟩ := SwarmKol.exists_isProjectiveLimit (α := γ) (P := pushFamily e P)
    (isProjectiveMeasureFamily_pushFamily he hP) hprob'
  exact ⟨ν.map (retrPi r), isProjectiveLimit_map_retrPi he hr hri hν⟩

end Abstract

/-! ## The countable case, as an instance -/

section Countable

variable {ι : Type*} [Countable ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  [∀ i, Countable (α i)] [∀ i, MeasurableSingletonClass (α i)] [∀ i, Nonempty (α i)]
variable {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

/-- The compact retract of a family of countable factors: `[0,1]` with the uniform embedding. -/
theorem exists_isProjectiveLimit_of_countable (hP : IsProjectiveMeasureFamily P)
    (hprob : ∀ J, IsProbabilityMeasure (P J)) :
    ∃ μ : Measure (Π i, α i), IsProjectiveLimit μ P :=
  exists_isProjectiveLimit_of_compactRetract (γ := fun _ : ι => UnitInterval)
    (e := fun i => embC (α i)) (r := fun i => retrC (α i))
    (fun i => measurable_embC (α i)) (fun i => measurable_retrC (α i))
    (fun i => retrC_embC (α i)) hP hprob

end Countable

/-! ## The shift-stationary two-sided form -/

section Stationary

variable {β : Type*} [MeasurableSpace β]
variable {γ : Type*} [TopologicalSpace γ] [MeasurableSpace γ] [T2Space γ] [CompactSpace γ]
  [SecondCountableTopology γ] [BorelSpace γ] [Nonempty γ]
variable {e : β → γ} {r : γ → β}
variable {P : ∀ J : Finset ℤ, Measure (Π j : J, β)}

/-- **Stationary two-sided extension for factors with a compact measurable retract.**  A
shift-stationary projective family of probability measures on windows of `ℤ → β` has a
shift-invariant probability projective limit, provided `β` embeds measurably into a compact
second-countable T2 space with a measurable left inverse.  This is
`SwarmKol.exists_stationary_isProjectiveLimit` with the compactness hypothesis on the state space
replaced by the existence of such a retract; the shift invariance of the compact factor makes the
pushforward family shift-stationary. -/
theorem exists_stationary_isProjectiveLimit_of_compactRetract (he : Measurable e)
    (hr : Measurable r) (hri : Function.LeftInverse r e)
    (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => β) P)
    (hprob : ∀ J, IsProbabilityMeasure (P J))
    (hstat : ∀ (k : ℤ) (I : Finset ℤ),
      P (I.image (fun i => i + k)) = (P I).map (SwarmKol.winReindex (β := β) k I)) :
    ∃ ν : Measure (ℤ → β), IsProjectiveLimit (α := fun _ : ℤ => β) ν P ∧ IsProbabilityMeasure ν ∧
      ∀ k : ℤ, ν.map (SwarmKol.pathShift (β := β) k) = ν := by
  classical
  -- instantiate the abstract material at the constant families
  have he' : ∀ _ : ℤ, Measurable (fun x : β => e x) := fun _ => he
  have hr' : ∀ _ : ℤ, Measurable (fun x : γ => r x) := fun _ => hr
  have hri' : ∀ _ : ℤ, Function.LeftInverse (fun x : γ => r x) (fun x : β => e x) :=
    fun _ => hri
  have hQstat : ∀ (k : ℤ) (I : Finset ℤ),
      (pushFamily (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e) P)
          (I.image (fun i => i + k))
        = ((pushFamily (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e) P) I).map
            (SwarmKol.winReindex (β := γ) k I) := by
    intro k I
    have hcomp : (embWin (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e)
          (I.image (fun i => i + k))) ∘ (SwarmKol.winReindex (β := β) k I)
        = (SwarmKol.winReindex (β := γ) k I) ∘
          (embWin (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e) I) := by
      funext v j
      exact congrArg (fun x : ↥I => e (v x)) (Subtype.ext rfl)
    simp only [pushFamily]
    rw [hstat k I, Measure.map_map (measurable_embWin he' _)
        (measurable_winReindex' (β := β) k I)]
    rw [Measure.map_map (measurable_winReindex' (β := γ) k I) (measurable_embWin he' I), hcomp]
  have hQprob : ∀ J, IsProbabilityMeasure
      (pushFamily (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e) P J) := fun J =>
    Measure.isProbabilityMeasure_map (measurable_embWin he' J).aemeasurable
  obtain ⟨ν, hν, hνprob, hνshift⟩ :=
    SwarmKol.exists_stationary_isProjectiveLimit (β := γ)
      (P := pushFamily (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => e) P)
      (isProjectiveMeasureFamily_pushFamily he' hP) hQprob hQstat
  haveI := hνprob
  refine ⟨ν.map (retrPi (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => r)),
    isProjectiveLimit_map_retrPi he' hr' hri' hν, ?_, fun k => ?_⟩
  · exact Measure.isProbabilityMeasure_map (measurable_retrPi hr').aemeasurable
  · have hswap : (SwarmKol.pathShift (β := β) k) ∘
        (retrPi (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => r))
        = (retrPi (α := fun _ : ℤ => β) (γ := fun _ : ℤ => γ) (fun _ => r)) ∘
          (SwarmKol.pathShift (β := γ) k) := by
      funext y i
      rfl
    rw [Measure.map_map (measurable_pathShift' (β := β) k) (measurable_retrPi hr'), hswap,
      ← Measure.map_map (measurable_retrPi hr') (measurable_pathShift' (β := γ) k), hνshift k]

end Stationary

end SwarmKolNC
