/-
  **The right-jump law after adjoining the record environment.**
-/
import Swarm.JumpWeights

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-- The fresh right-jump measure integral on the enlarged record information. -/
theorem setIntegral_stepUp_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    (arrayMeasure N).real (A ∩ stepUp p m n i) =
      ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
  exact setIntegral_weight_gen p m (S := recInfo (N := N) m j g)
    (fun γ => prefRead_subset_recInfo j g γ)
    (stepUp p m n i) (fun _ => stepUp p m n i)
    (fun γ => alphaOf p m n γ i) (alphaFun p m n i) A hA
    (fun _ _ _ => Iff.rfl) (fun _ => StepCross.measurable_stepUp p m n i)
    (fun γ U hU => alphaFun_eq_alphaOf_on_prefix p m hU i)
    (fun s hs => enlMeas_le_infoPiece p m n j g _ (measurable_alphaFun_enl p m n i hs))
    (fun U => (alphaFun_mem_Icc hp0 hp1 m n i U).1)
    (fun U => (alphaFun_mem_Icc hp0 hp1 m n i U).2)
    (fun γ {B} hB => fresh_stepUp_gen p hp0 hp1 γ i (recInfo (N := N) m j g γ)
      (prefRead_subset_recInfo j g γ) (fr_notMem_recInfo γ hij g) hB)

/-- The conditional expectation of the actual right-jump indicator under `infoPiece`. -/
theorem condExp_stepUp_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N) (stepUpInd p m n i)
      =ᵐ[arrayMeasure N] alphaFun p m n i := by
  exact condExp_indicator_weight_gen (N := N) p m (S := recInfo (N := N) m j g)
    (fun γ => prefRead_subset_recInfo j g γ) (stepUp p m n i)
    (StepCross.measurable_stepUp p m n i) (alphaFun p m n i)
    (fun s hs => enlMeas_le_infoPiece p m n j g _ (measurable_alphaFun_enl p m n i hs))
    (fun U => (alphaFun_mem_Icc hp0 hp1 m n i U).1)
    (fun U => (alphaFun_mem_Icc hp0 hp1 m n i U).2)
    (fun {A} hA => setIntegral_stepUp_infoPiece p hp0 hp1 hij g hA)

end Swarming.Enl


namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-- Joint real integral of the next right jump and a strictly above-record site mark. -/
theorem setIntegral_up_siteMark_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece p m n j g] A) :
    (arrayMeasure N).real (A ∩ (stepUp p m n i ∩
        {U : Array N | SiteMark p m U j
          (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))})) =
      (1 - p) ^ (m - 1) * ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
  let q : ℝ := (1 - p) ^ (m - 1)
  have hq0 : 0 ≤ (1 - p) := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact pow_le_one₀ (by linarith) (by linarith)
  let E : Set (Array N) := stepUp p m n i ∩
    {U : Array N | SiteMark p m U j (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))}
  let V : Pref N n → Set (Array N) := fun γ => stepUp p m n i ∩
    {U : Array N | SiteMark p m U j (recVal j γ + ((g + 1 : ℕ) : ℤ))}
  have hEval : ∀ (γ : Pref N n) (U : Array N), U ∈ prefAgree p m γ → (U ∈ E ↔ (V γ) U) := by
    intro γ U hU
    simp only [E, V, Set.mem_inter_iff, Set.mem_ofPred_eq, recVal_prefOf_of_mem hU j]
    exact Iff.rfl
  have hV : ∀ γ, MeasurableSet (V γ) := fun γ =>
    (StepCross.measurable_stepUp p m n i).inter
      (measurableSet_siteMark_array p m j (recVal j γ + ((g + 1 : ℕ) : ℤ)))
  have hWmeas : Measurable[infoPiece (N := N) p m n j g]
      (fun U => q * alphaFun p m n i U) := by
    exact measurable_const.mul (fun s hs =>
      enlMeas_le_infoPiece p m n j g _ (measurable_alphaFun_enl p m n i hs))
  calc
    (arrayMeasure N).real (A ∩ E) = ∫ U in A, q * alphaFun p m n i U ∂(arrayMeasure N) := by
      apply setIntegral_weight_gen p m (S := recInfo (N := N) m j g)
        (fun γ => prefRead_subset_recInfo j g γ) E V
        (fun γ => q * alphaOf p m n γ i) (fun U => q * alphaFun p m n i U) A hA hEval hV
        (fun γ U hU => by rw [alphaFun_eq_alphaOf_on_prefix p m hU i]) hWmeas
        (fun U => mul_nonneg hq (alphaFun_mem_Icc hp0 hp1 m n i U).1)
        (fun U => by
          have ha1 := (alphaFun_mem_Icc hp0 hp1 m n i U).2
          calc q * alphaFun p m n i U ≤ q * 1 := mul_le_mul_of_nonneg_left ha1 hq
            _ = q := mul_one q
            _ ≤ 1 := hq1)
        (fun γ {B} hB => by
          have hm := fresh_up_siteMark_gen (m := m) (n := n) (i := i) (j := j) (i0 := i) p hp0 hp1 γ (recInfo (N := N) m j g γ)
            (prefRead_subset_recInfo j g γ) (x := recVal j γ + ((g + 1 : ℕ) : ℤ))
            (fr_notMem_recInfo γ hij g) (fun k _ hmem => by
              have hle := recInfo_site_le (m := m) j g γ hmem rfl
              have hlt : ((g : ℕ) : ℤ) < ((g + 1 : ℕ) : ℤ) := by
                exact_mod_cast Nat.lt_succ_self g
              linarith)
            hij hB
          dsimp [V]
          simp only [Set.inter_assoc, Nat.cast_add, Nat.cast_one] at hm ⊢
          rw [hm]
          calc
            (ENNReal.ofReal (1 - p)) ^ (m - 1) * ENNReal.ofReal (alphaOf p m n γ i) *
                arrayMeasure N (prefAgree p m γ ∩ B) =
              ENNReal.ofReal ((1 - p) ^ (m - 1) * alphaOf p m n γ i) *
                arrayMeasure N (prefAgree p m γ ∩ B) :=
by
                simp only [ENNReal.ofReal_pow hq0,
                  ENNReal.ofReal_mul (pow_nonneg hq0 _)]
            _ = ENNReal.ofReal (q * alphaOf p m n γ i) *
                arrayMeasure N (prefAgree p m γ ∩ B) := by rfl)
    _ = q * ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) := by
      rw [integral_const_mul]

/-- The joint conditional indicator law at the next right jump and next fresh site. -/
theorem condExp_up_siteMark_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (g : ℕ) :
    condExp (infoPiece (N := N) p m n j g) (arrayMeasure N)
        ((stepUp p m n i ∩ {U : Array N | SiteMark p m U j
          (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))}).indicator (fun _ => (1 : ℝ)))
      =ᵐ[arrayMeasure N] fun U => (1 - p) ^ (m - 1) * alphaFun p m n i U := by
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := by positivity
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact condExp_indicator_weight_gen (N := N) p m (S := recInfo (N := N) m j g)
    (fun γ => prefRead_subset_recInfo j g γ)
    (stepUp p m n i ∩ {U : Array N | SiteMark p m U j
      (recVal j (prefOf p m n U) + ((g + 1 : ℕ) : ℤ))})
    ((StepCross.measurable_stepUp p m n i).inter
      (measurableSet_randomSiteMark p m n j g))
    (fun U => (1 - p) ^ (m - 1) * alphaFun p m n i U)
    (measurable_const.mul (fun s hs =>
      enlMeas_le_infoPiece p m n j g _ (measurable_alphaFun_enl p m n i hs)))
    (fun U => mul_nonneg hq0 (alphaFun_mem_Icc hp0 hp1 m n i U).1)
    (fun U => by
      have ha1 := (alphaFun_mem_Icc hp0 hp1 m n i U).2
      calc (1 - p) ^ (m - 1) * alphaFun p m n i U ≤ (1 - p) ^ (m - 1) * 1 :=
        mul_le_mul_of_nonneg_left ha1 hq0
        _ = (1 - p) ^ (m - 1) := mul_one _
        _ ≤ 1 := hq1)
    (fun {A} hA => by
      simpa only [integral_const_mul] using setIntegral_up_siteMark_infoPiece p hp0 hp1 hij g hA)

end Swarming.Enl


