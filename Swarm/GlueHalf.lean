/-
# Finite-L gluing IV: `d_y = spread(τ_y)` and the `BadHalf` bridge

At a record time the paper's defect `d_y = y − min_i X^i_{τ_y}` *is* the spread of the pack,
and `HblkTwo.BadHalf` is exactly the failure of `2 d_{r+BL} ≤ L`.  This file proves the two
bridges:

* `spreadS_univ_tau` — `spread_ι(τ_y) = d_y`;
* `not_badHalf_of_defect_le` — `2 d_{r+BL} ≤ L` implies `¬ BadHalf B q r L` for the record
  sequence `q = (fun u => (d_u).toNat, τ)`;
* `measure_badHalf_le` — measure level: the mass of `BadHalf` is at most the mass of the
  complement of the *halving input* `{2 d_{r+BL} ≤ L}`.

So `HalfClauseAt` follows as soon as the halving input is shown to hold off an event of small
measure; the deterministic gluing files `GlueCore`/`GlueMeet` reduce that input to the local
good field.  Nothing here is probabilistic.
-/
import Swarm.GlueMeet
import Swarm.HblkTwo

open Finset
open scoped BigOperators

namespace Glue

open RecordDefect LocalFluid MeasureTheory

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- At a record time the spread of the whole pack is the paper's defect. -/
theorem spreadS_univ_tau {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) (y : ℕ) :
    spreadS X (Finset.univ) (τ y) = defect X τ y := by
  have h1 : sMax X (Finset.univ) (τ y) = (y : ℤ) := by
    rw [sMax_of_nonempty Finset.univ_nonempty]
    exact (hτ y).2
  have h2 : sMin X (Finset.univ) (τ y) = runMin X (τ y) := by
    rw [sMin_of_nonempty Finset.univ_nonempty]
    rfl
  unfold spreadS defect
  rw [h1, h2]

/-- The halving input `2 d_{r+BL} ≤ L` rules out `BadHalf`. -/
theorem not_badHalf_of_defect_le {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {B L r : ℕ} (h : 2 * defect X τ (r + B * L) ≤ (L : ℤ)) :
    ¬ HblkTwo.BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  rintro ⟨-, h2⟩
  simp only [] at h2
  have hnonneg : 0 ≤ defect X τ (r + B * L) := defect_nonneg hτ (r + B * L)
  have hcast : (((defect X τ (r + B * L)).toNat : ℕ) : ℤ) = defect X τ (r + B * L) :=
    Int.toNat_of_nonneg hnonneg
  have hnat : 2 * (defect X τ (r + B * L)).toNat ≤ L := by
    have h1 : ((2 * (defect X τ (r + B * L)).toNat : ℕ) : ℤ) ≤ (L : ℤ) := by
      push_cast
      rw [hcast]
      exact h
    exact_mod_cast h1
  have hle : (defect X τ (r + B * L)).toNat ≤ L / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  omega

/-- Measure form: `BadHalf` is dominated by the complement of the halving input. -/
theorem measure_badHalf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ) (hτ : ∀ ω, IsRecord (X ω) (τ ω)) {B L r : ℕ} :
    μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | ¬ (2 * defect (X ω) (τ ω) (r + B * L) ≤ (L : ℤ))} := by
  refine measure_mono ?_
  intro ω hω hcon
  exact not_badHalf_of_defect_le (hτ ω) hcon hω

end Glue
