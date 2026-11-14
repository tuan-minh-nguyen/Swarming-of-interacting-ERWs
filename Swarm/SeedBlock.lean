/-
# Factoring a probability over a finite block of coordinates

`SwarmBlock.block_measure_inter` factors the array law over two disjoint *blocks* of
coordinates.  This file turns it into the shape used by the regeneration seed argument: if an
event `C` only depends on the coordinates of a finite set `Q`, and an event `Φ` only depends on
the coordinates outside `Q`, then `P(C ∩ Φ) = P(C) · P(Φ)`.

The "only depends" hypothesis is stated as a plain implication between the truth values at two
arrays agreeing on `Q`, so no σ-algebra bookkeeping is needed to state it; measurability of `C`
and `Φ` is required separately.
-/
import Swarm.RestartRecord
import Swarm.BlockIndep

open MeasureTheory Set
open Swarming Swarming.Uniform

namespace SwarmSeed

variable {N : ℕ}

/-- The extension of a function of the coordinates in `Q` to the whole array, filling the
complementary coordinates with `0`. -/
noncomputable def extendQ (Q : Finset (Fin N × ℤ × ℕ)) (V : (↑(Q : Set (Fin N × ℤ × ℕ))) → ℝ) :
    Array N :=
  fun q => if h : q ∈ Q then V ⟨q, h⟩ else 0

theorem measurable_extendQ (Q : Finset (Fin N × ℤ × ℕ)) :
    Measurable (extendQ (N := N) Q) := by
  refine measurable_pi_iff.mpr fun q => ?_
  by_cases h : q ∈ Q
  · have hfun : (fun V : (↑(Q : Set (Fin N × ℤ × ℕ))) → ℝ => extendQ Q V q) =
        fun V => V ⟨q, h⟩ := by
      funext V; simp [extendQ, h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun V : (↑(Q : Set (Fin N × ℤ × ℕ))) → ℝ => extendQ Q V q) = fun _ => (0 : ℝ) := by
      funext V; simp [extendQ, h]
    rw [hfun]
    exact measurable_const

/-- The extension of a function of the coordinates *outside* `Q` to the whole array. -/
noncomputable def extendQT (Q : Finset (Fin N × ℤ × ℕ))
    (V : (↑((Q : Set (Fin N × ℤ × ℕ))ᶜ) → ℝ)) : Array N :=
  fun q => if h : q ∈ ((Q : Set (Fin N × ℤ × ℕ))ᶜ) then V ⟨q, h⟩ else 0

theorem measurable_extendQT (Q : Finset (Fin N × ℤ × ℕ)) :
    Measurable (extendQT (N := N) Q) := by
  refine measurable_pi_iff.mpr fun q => ?_
  by_cases h : q ∈ ((Q : Set (Fin N × ℤ × ℕ))ᶜ)
  · have hfun : (fun V : (↑((Q : Set (Fin N × ℤ × ℕ))ᶜ) → ℝ) => extendQT Q V q) =
        fun V => V ⟨q, h⟩ := by
      funext V; simp [extendQT, h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun V : (↑((Q : Set (Fin N × ℤ × ℕ))ᶜ) → ℝ) => extendQT Q V q) =
        fun _ => (0 : ℝ) := by
      funext V; simp [extendQT, h]
    rw [hfun]
    exact measurable_const

theorem extendQ_agree (Q : Finset (Fin N × ℤ × ℕ))
    (V : (↑(Q : Set (Fin N × ℤ × ℕ))) → ℝ) (q : Fin N × ℤ × ℕ) (hq : q ∈ Q) :
    extendQ Q V q = V ⟨q, hq⟩ := by
  simp [extendQ, hq]

theorem extendQT_agree (Q : Finset (Fin N × ℤ × ℕ))
    (V : (↑((Q : Set (Fin N × ℤ × ℕ))ᶜ) → ℝ)) (q : Fin N × ℤ × ℕ)
    (hq : q ∈ ((Q : Set (Fin N × ℤ × ℕ))ᶜ)) : extendQT Q V q = V ⟨q, hq⟩ := by
  simp [extendQT, hq]

/-- **Block factorization from a determinacy hypothesis.**  If `C` depends only on the
coordinates in the finite set `Q` and `Φ` only on the coordinates outside `Q`, then
`P(C ∩ Φ) = P(C) · P(Φ)`. -/
theorem cylinder_factor {C Φ : Set (Array N)} (hC : MeasurableSet C) (hΦ : MeasurableSet Φ)
    {Q : Finset (Fin N × ℤ × ℕ)}
    (hCd : ∀ U U' : Array N, (∀ q ∈ Q, U q = U' q) → (C U ↔ C U'))
    (hΦd : ∀ U U' : Array N, (∀ q, q ∉ Q → U q = U' q) → (Φ U ↔ Φ U')) :
    (arrayMeasure N) (C ∩ Φ) = (arrayMeasure N) C * (arrayMeasure N) Φ := by
  classical
  set S : Set (Fin N × ℤ × ℕ) := (↑Q : Set (Fin N × ℤ × ℕ)) with hS
  set T : Set (Fin N × ℤ × ℕ) := (↑Q : Set (Fin N × ℤ × ℕ))ᶜ with hT
  have hdisj : Disjoint S T := by
    rw [hS, hT]
    exact disjoint_compl_right
  have hCeq : C = S.domRestrict ⁻¹' (extendQ Q ⁻¹' C) := by
    ext U
    simp only [mem_preimage]
    have hagree : ∀ q ∈ Q, U q = extendQ Q (S.domRestrict U) q := by
      intro q hq
      rw [extendQ_agree Q _ q hq]
      rfl
    exact ⟨fun h => (hCd U _ hagree).mp h, fun h => (hCd U _ hagree).mpr h⟩
  have hΦeq : Φ = T.domRestrict ⁻¹' (extendQT Q ⁻¹' Φ) := by
    ext U
    simp only [mem_preimage]
    have hagree : ∀ q, q ∉ Q → U q = extendQT Q (T.domRestrict U) q := by
      intro q hq
      have hqT : q ∈ T := by simpa [hT] using hq
      rw [extendQT_agree Q _ q hqT]
      rfl
    exact ⟨fun h => (hΦd U _ hagree).mp h, fun h => (hΦd U _ hagree).mpr h⟩
  have hmain : (arrayMeasure N) (S.domRestrict ⁻¹' (extendQ Q ⁻¹' C) ∩
      T.domRestrict ⁻¹' (extendQT Q ⁻¹' Φ))
      = (arrayMeasure N) (S.domRestrict ⁻¹' (extendQ Q ⁻¹' C))
        * (arrayMeasure N) (T.domRestrict ⁻¹' (extendQT Q ⁻¹' Φ)) :=
    SwarmBlock.block_measure_inter (fun _ : Fin N × ℤ × ℕ => uniform01) hdisj
      ((measurable_extendQ Q) hC) ((measurable_extendQT Q) hΦ)
  rw [hCeq, hΦeq]
  exact hmain

end SwarmSeed
