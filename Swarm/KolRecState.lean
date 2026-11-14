/-
# The stationary two-sided extension for the record-state space

`areas/kac/RecTop.lean` shows `SwarmRec.RecState N m` is not compact for `2 ≤ N`, so the
compact-factor Kolmogorov extension `SwarmKol.exists_isProjectiveLimit` cannot be instantiated at it.
This file supplies the compact measurable retract that `SwarmKolNC.exists_stationary_isProjectiveLimit_of_compactRetract`
needs:

* all of the non-compactness of `RecState N m = {p : (Fin N → ℕ) × (Fin N → ℤ → Fin (m+1)) // …}`
  sits in the half-distance vector `Fin N → ℕ`, a *countable* type, which is compactified by
  `embC (Fin N → ℕ) : (Fin N → ℕ) → [0,1]`;
* the local-time profile `Fin N → ℤ → Fin (m+1)` is already a product of finite sets, hence compact,
  metrizable and second countable;
* hence `RecGamma N m := [0,1] × (Fin N → ℤ → Fin (m+1))` is compact metrizable, second countable,
  with the Borel σ-algebra `recEmb` embeds `RecState N m` into it, and `recRetr` (junk off the image)
  is a measurable left inverse.

Consequently: **for every shift-stationary projective family of probability measures on windows of
record states there is a shift-invariant probability on `ℤ → RecState N m` with those window laws**
(`exists_stationary_isProjectiveLimit_recState`).  This is exactly the form of the residual of
`areas/kac/KAC_EXTENSION.md` §2 with the non-compactness obstruction removed: the remaining input is
the family `P` itself — the record window laws, their projectivity and their shift-stationarity —
which is a statement about the record dynamics (an invariant probability of the stopped record
kernel and the chain-composition computation) and is *not* produced here, and is not a consequence
of invariance alone.

No claim about the actual record window laws, `MainClaim`, `Ballistic`, common speed, regeneration,
`h1` or `h2`.
-/
import Swarm.KolRetract

open MeasureTheory Set Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace SwarmKolNC

open SwarmRec

/-- The compact ambient space used to compactify the record-state space: the compactified
half-distance vector and the (already compact) local-time profile. -/
abbrev RecGamma (N m : ℕ) : Type := UnitInterval × (Fin N → ℤ → Fin (m + 1))


/-! ## A base record state -/

/-- The record state with every walker at half-distance `0` and the single local time `1` at `0`
(otherwise `0`).  Its existence needs at least one walker. -/
noncomputable def recState0 (N m : ℕ) (hN : 0 < N) : RecState N m :=
  ⟨(fun _ => 0, fun _ x => if x = 0 then 1 else 0), by
    refine ⟨⟨⟨0, hN⟩, rfl⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i x hx
      show (if x = 0 then (1 : Fin (m + 1)) else 0) = 0
      rw [if_neg (ne_of_gt hx)]
    · intro i
      show (1 : Fin (m + 1)) ≤ (if (0 : ℤ) = 0 then (1 : Fin (m + 1)) else 0)
      rw [if_pos rfl]
    · intro i
      show (if (0 : ℤ) = 0 then (1 : Fin (m + 1)) else 0) = (if (0 : ℕ) = 0 then 1 else 0)
      rw [if_pos rfl, if_pos rfl]⟩

/-- The time-zero record state: the half-distance vector read off the record state and the cap-`0`
local-time profile. -/
noncomputable def gammaPoint (hN : 0 < N) (p : RecGamma N m) : RecGamma N m := p

/-! ## The compact embedding and its measurable left inverse -/

/-- The half distances of a record state, read as an element of the countable type `Fin N → ℕ`. -/
noncomputable def recDist (y : RecState N m) : Fin N → ℕ := fun i => dist2 y i

/-- The compact embedding of the record-state space. -/
noncomputable def recEmb (y : RecState N m) : RecGamma N m :=
  (embC (Fin N → ℕ) (recDist y), y.val.2)

/-- Removing the junk from the ambient compact space: the pair of the retracted half distances and
the local-time profile. -/
noncomputable def recClean (p : RecGamma N m) : Amb N m :=
  (retrC (Fin N → ℕ) p.1, p.2)

/-- The cleaned point when it is a record state, and a fixed record state otherwise. -/
noncomputable def recSafe (hN : 0 < N) (p : RecGamma N m) : Amb N m := by
  classical
  exact if recClean p ∈ recSet N m then recClean p else (recState0 N m hN).val

theorem recSafe_mem (hN : 0 < N) (p : RecGamma N m) : recSafe hN p ∈ recSet N m := by
  classical
  by_cases h : recClean p ∈ recSet N m
  · unfold recSafe
    rw [if_pos h]
    exact h
  · unfold recSafe
    rw [if_neg h]
    exact (recState0 N m hN).2

/-- The measurable left inverse of `recEmb`. -/
noncomputable def recRetr (hN : 0 < N) (p : RecGamma N m) : RecState N m :=
  ⟨recSafe hN p, recSafe_mem hN p⟩

/-! ### Measurability -/

theorem continuous_recDist (i : Fin N) :
    Continuous fun y : RecState N m => dist2 y i := by
  have h1 : Continuous fun p : Amb N m => p.1 i := (continuous_apply i).comp continuous_fst
  simpa only [dist2, Function.comp_def] using h1.comp continuous_subtype_val

theorem measurable_recEmb : Measurable (recEmb (N := N) (m := m)) := by
  refine Measurable.prod ?_ ?_
  · refine (measurable_embC (Fin N → ℕ)).comp ?_
    exact measurable_pi_lambda _ fun i => (continuous_recDist (N := N) (m := m) i).measurable
  · exact (continuous_snd.comp continuous_subtype_val).measurable

theorem measurable_recClean : Measurable (recClean (N := N) (m := m)) := by
  refine Measurable.prod ?_ measurable_snd
  exact (measurable_retrC (Fin N → ℕ)).comp measurable_fst

theorem measurable_recSafe (hN : 0 < N) : Measurable (recSafe (N := N) (m := m) hN) := by
  have hs : MeasurableSet (recClean ⁻¹' recSet N m) :=
    (measurableSet_recSet N m).preimage measurable_recClean
  unfold recSafe
  exact Measurable.ite hs measurable_recClean measurable_const

theorem measurable_recRetr (hN : 0 < N) : Measurable (recRetr (N := N) (m := m) hN) :=
  Measurable.subtype_mk (measurable_recSafe hN) (h := recSafe_mem hN)

/-! ### The retraction identity -/

theorem recClean_recEmb (y : RecState N m) : recClean (recEmb y) = y.val := by
  refine Prod.ext ?_ rfl
  exact retrC_embC (δ := Fin N → ℕ) (a := recDist y)

theorem recRetr_recEmb (hN : 0 < N) (y : RecState N m) : recRetr hN (recEmb y) = y := by
  have hmem : recClean (recEmb y) ∈ recSet N m := by
    rw [recClean_recEmb]
    exact y.2
  have hsafe : recSafe hN (recEmb y) = y.val := by
    unfold recSafe
    rw [if_pos hmem, recClean_recEmb]
  exact Subtype.ext hsafe

/-! ## The stationary two-sided extension for record windows -/

/-- **The stationary two-sided extension for windows of record states.**  Any shift-stationary
projective family of probability measures on finite windows of `RecState N m` has a shift-invariant
probability projective limit, i.e. an invertible measure-preserving two-sided system with those
window laws.  This is the statement of the residual of `KAC_EXTENSION.md` §2 with its non-compactness
obstruction removed; the family `P` itself is the remaining input. -/
theorem exists_stationary_isProjectiveLimit_recState (N m : ℕ) (hN : 0 < N)
    {P : ∀ J : Finset ℤ, Measure (Π j : J, RecState N m)}
    (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => RecState N m) P)
    (hprob : ∀ J, IsProbabilityMeasure (P J))
    (hstat : ∀ (k : ℤ) (I : Finset ℤ),
      P (I.image (fun i => i + k)) = (P I).map (SwarmKol.winReindex (β := RecState N m) k I)) :
    ∃ ν : Measure (ℤ → RecState N m),
      IsProjectiveLimit (α := fun _ : ℤ => RecState N m) ν P ∧ IsProbabilityMeasure ν ∧
        ∀ k : ℤ, ν.map (SwarmKol.pathShift (β := RecState N m) k) = ν := by
  haveI hTop : ∀ _ : ℤ, TopologicalSpace (RecGamma N m) := fun _ => inferInstance
  haveI hMeas : ∀ _ : ℤ, MeasurableSpace (RecGamma N m) := fun _ => inferInstance
  haveI hT2 : ∀ _ : ℤ, T2Space (RecGamma N m) := fun _ => inferInstance
  haveI hComp : ∀ _ : ℤ, CompactSpace (RecGamma N m) := fun _ => inferInstance
  haveI hSec : ∀ _ : ℤ, SecondCountableTopology (RecGamma N m) := fun _ => inferInstance
  haveI hBorel : ∀ _ : ℤ, BorelSpace (RecGamma N m) := fun _ => inferInstance
  haveI hNe : ∀ _ : ℤ, Nonempty (RecGamma N m) := fun _ => inferInstance
  exact exists_stationary_isProjectiveLimit_of_compactRetract (γ := RecGamma N m)
    (e := recEmb (N := N) (m := m)) (r := recRetr (N := N) (m := m) hN)
    measurable_recEmb (measurable_recRetr hN) (recRetr_recEmb hN) hP hprob hstat

/-! ## Non-vacuity: a concrete shift-stationary window family -/

/-- The point mass at a fixed record state is a shift-stationary projective family of record-window
laws, so the hypotheses of `exists_stationary_isProjectiveLimit_recState` are satisfiable.  This
shows the extension theorem is not vacuous; it is of course not the record chain. -/
theorem exists_stationary_recState_dirac (N m : ℕ) (hN : 0 < N) :
    ∃ ν : Measure (ℤ → RecState N m),
      IsProjectiveLimit (α := fun _ : ℤ => RecState N m) ν
          (fun I => Measure.dirac (fun _ : I => recState0 N m hN)) ∧
        IsProbabilityMeasure ν ∧
          ∀ k : ℤ, ν.map (SwarmKol.pathShift (β := RecState N m) k) = ν := by
  refine exists_stationary_isProjectiveLimit_recState N m hN ?_ (fun _ => inferInstance) ?_
  · intro I J hJI
    rw [Measure.map_dirac]
    congr 1
  · intro k I
    rw [Measure.map_dirac]
    congr 1


end SwarmKolNC
