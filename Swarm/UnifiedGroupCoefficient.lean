/-
# One source-scale carrier and coefficient for every walker group

This is independent coordinator work for the local-good assembly.  The existing
`LocalGoodCore.CU` depends on the finite group `A`.  `CUmax` is its maximum over
all finite subsets of `Fin N`.  The corresponding `(locsum)` event is common,
and the finite group count raises the corresponding `Loccoord` bound directly.

The file deliberately does not assert a stopped-clock estimate, full `locmove`,
block tightness or velocity.  It establishes the common carrier and the coefficient
comparisons needed by those later steps.
-/
import Swarm.LocalGoodCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace RecordGroupUniform

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model
open LocalGood Loccoord

variable (N : ℕ) [Nonempty (Fin N)]

/-- The maximum of the concrete `(locsum)` constants over all walker groups.
The domain is a finite type, so no analytic boundedness premise is used. -/
noncomputable def CUmax (p : ℝ) (m : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun A : Finset (Fin N) => CU p m A)

/-- The maximum dominates every group's concrete `(locsum)` constant. -/
theorem CU_le_CUmax (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    CU p m A ≤ CUmax N p m := by
  exact Finset.le_sup' (f := fun A : Finset (Fin N) => CU p m A) (Finset.mem_univ A)

/-- The maximum is at least the canonical constant, in particular at least one. -/
theorem one_le_CUmax (p : ℝ) (m : ℕ) : 1 ≤ CUmax N p m := by
  have h := CU_le_CUmax (N := N) p m (∅ : Finset (Fin N))
  exact (one_le_CU (N := N) p m ∅).trans h

/-- The common concrete constant is positive. -/
theorem CUmax_pos (p : ℝ) (m : ℕ) : 0 < CUmax N p m := by
  have h := CU_le_CUmax (N := N) p m (∅ : Finset (Fin N))
  exact (CU_pos (N := N) p m ∅).trans_le h

/-- The common constant is also above the boundary required by `(locsum)`. -/
theorem Mb_lt_CUmax (p : ℝ) (m : ℕ) :
    LocSum.Mb p (LocSumAct.qOf p m) < CUmax N p m := by
  have h := CU_le_CUmax (N := N) p m (∅ : Finset (Fin N))
  exact (Mb_lt_CU (N := N) p m ∅).trans_le h

/-- The coefficient appearing directly before the distance/error in the
`Loccoord`/`Locmove` formulas when `CUmax` is used. -/
noncomputable def commonCoordCoefficient (p : ℝ) (m : ℕ) : ℝ :=
  (2 * CUmax N p m + 1) / 2

/-- The coefficient appearing for a particular group using its own `CU`. -/
noncomputable def groupCoordCoefficient (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : ℝ :=
  (2 * CU p m A + 1) / 2

/-- Group-dependent coefficients are uniformly controlled. -/
theorem groupCoordCoefficient_le (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    groupCoordCoefficient N p m A ≤ commonCoordCoefficient N p m := by
  unfold groupCoordCoefficient commonCoordCoefficient
  have h := CU_le_CUmax (N := N) p m A
  linarith

/-- Every group coefficient is at least one. -/
theorem one_le_groupCoordCoefficient (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    1 ≤ groupCoordCoefficient N p m A := by
  unfold groupCoordCoefficient
  have h := one_le_CU (N := N) p m A
  linarith

/-- The common coordinate coefficient is at least one. -/
theorem one_le_commonCoordCoefficient (p : ℝ) (m : ℕ) :
    1 ≤ commonCoordCoefficient N p m := by
  unfold commonCoordCoefficient
  have h := one_le_CUmax (N := N) p m
  linarith

/-- The common coefficient still satisfies the positivity condition for
`LocMoveCompose.gammaRate`. -/
theorem gammaRate_mul_common {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {A : Finset (Fin N)} (hA : A.Nonempty) :
    1 ≤ LocMoveCompose.gammaRate p m A * commonCoordCoefficient N p m := by
  have hg : 0 ≤ LocMoveCompose.gammaRate p m A :=
    (LocalGood.gammaRate_pos (N := N) (m := m) hp0 hp1 hA).le
  have h := LocalGood.gammaRate_mul_CU (N := N) (m := m) hp0 hp1 hA
  unfold commonCoordCoefficient
  have hle : CU p m A ≤ CUmax N p m := CU_le_CUmax (N := N) p m A
  have hprod : LocMoveCompose.gammaRate p m A * CU p m A ≤
      LocMoveCompose.gammaRate p m A * CUmax N p m :=
    mul_le_mul_of_nonneg_left hle hg
  linarith

/-- The source coefficient used before the initial leader surplus. -/
noncomputable def sourceCoefficient (p : ℝ) (m : ℕ) : ℝ :=
  1 + commonCoordCoefficient N p m ^ 2

/-- The source coefficient at a group-specific concrete constant. -/
noncomputable def groupSourceCoefficient (p : ℝ) (m : ℕ) (A : Finset (Fin N)) : ℝ :=
  1 + groupCoordCoefficient N p m A ^ 2

/-- All group-dependent source coefficients are below the common one. -/
theorem groupSourceCoefficient_le (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    groupSourceCoefficient N p m A ≤ sourceCoefficient N p m := by
  have h := groupCoordCoefficient_le (N := N) p m A
  have hnonneg : 0 ≤ groupCoordCoefficient N p m A :=
    le_trans zero_le_one (one_le_groupCoordCoefficient (N := N) p m A)
  have hc : 0 ≤ commonCoordCoefficient N p m :=
    le_trans zero_le_one (one_le_commonCoordCoefficient (N := N) p m)
  have hmul : 0 ≤ (commonCoordCoefficient N p m - groupCoordCoefficient N p m A) *
      (commonCoordCoefficient N p m + groupCoordCoefficient N p m A) :=
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg hc hnonneg)
  unfold groupSourceCoefficient sourceCoefficient
  nlinarith [hmul]

/-- The group-specific source coefficient is strictly positive. -/
theorem groupSourceCoefficient_pos (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    0 < groupSourceCoefficient N p m A := by
  have hc := one_le_groupCoordCoefficient (N := N) p m A
  unfold groupSourceCoefficient
  positivity

/-- The common source coefficient is strictly positive. -/
theorem sourceCoefficient_pos (p : ℝ) (m : ℕ) : 0 < sourceCoefficient N p m := by
  have hc := one_le_commonCoordCoefficient (N := N) p m
  unfold sourceCoefficient
  positivity

/-- The reciprocal source coefficients have the correct order. -/
theorem inv_sourceCoefficient_le (p : ℝ) (m : ℕ) (A : Finset (Fin N)) :
    (sourceCoefficient N p m)⁻¹ ≤ (groupSourceCoefficient N p m A)⁻¹ := by
  exact inv_anti₀ (groupSourceCoefficient_pos (N := N) p m A)
    (groupSourceCoefficient_le (N := N) p m A)

/-- One common `(locsum)` carrier, at `r-real ≥ (T+3)L`, with its direct
`Loccoord` content at the worst group coefficient.  This calls only the existing
`LocCoordPaper.loccoord_full_window_T3`; its rate constants may depend on T. -/
theorem exists_loccoord_common {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (T : ℕ) :
    ∃ c_T C_T : ℝ, 0 < c_T ∧ 1 ≤ C_T ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ,
      (T + 3) * L ≤ r →
      (arrayMeasure N)
          (LocSumR1.LsBad N p m (CUmax N p m) ((2 * T + 4) * L) (r - (T + 2) * L))
        ≤ ENNReal.ofReal (C_T * Real.exp (-c_T * (L : ℝ) ^ (1 / 16 : ℝ))) ∧
      ∀ U : Array N,
        U ∉ LocSumR1.LsBad N p m (CUmax N p m) ((2 * T + 4) * L) (r - (T + 2) * L) →
        ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
        (hX0 : 0 ≤ Xmin p m U B hB s) →
        r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
        (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
        Swarming.Group.average B (fun k =>
          HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
          ≤ commonCoordCoefficient N p m *
              (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
            + C_T * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨c, C, hc, hC, L₀, h⟩ := LocCoordPaper.loccoord_full_window_T3
    (N := N) hp0 hp1 hm (one_le_CUmax (N := N) p m) (Mb_lt_CUmax (N := N) p m) T
  refine ⟨c, C, hc, hC, L₀, ?_⟩
  intro L hL r hr
  obtain ⟨hprob, hbody⟩ := h L hL r hr
  refine ⟨hprob, ?_⟩
  intro U hU B hB s t hst hX0 hXmin hRmax
  have hmain := hbody U hU B hB s t hst hX0 hXmin hRmax
  exact hmain

end RecordGroupUniform
