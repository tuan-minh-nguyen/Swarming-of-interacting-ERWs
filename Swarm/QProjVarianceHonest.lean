import Swarm.QOrthogonalActual
import Swarm.MartingaleLimit
import Swarm.QDefect
import Swarm.ActualBudgetInterfaces

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace Swarming.Enl.ProjHonest

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl VdriftAssembly

variable {N : ℕ}

/-! ## 0. The `L²` contraction of conditional expectation on the actual array -/

lemma norm_rpow_two (x : ℝ) : ‖x‖ ^ (2 : ℝ) = x ^ 2 := by
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- **Conditional Jensen in `L²`**: `(E[f | 𝓕_T])² ≤ᵐ E[f² | 𝓕_T]`. -/
theorem sq_condExp_le_enl {p : ℝ} (m T : ℕ) {f : Array N → ℝ}
    (hf2 : Integrable (fun U => f U ^ 2) (arrayMeasure N)) :
    (fun U => condExp (enlFilt p m T) (arrayMeasure N) f U ^ 2)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m T) (arrayMeasure N) (fun U => f U ^ 2) := by
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  have hf2' : Integrable (fun U => ‖f U‖ ^ (2 : ℝ)) (arrayMeasure N) :=
    hf2.congr (Filter.Eventually.of_forall fun U => (norm_rpow_two (f U)).symm)
  have h := Integrable.norm_condExp_rpow_le (μ := arrayMeasure N) (m := enlFilt p m T)
    (f := f) (p := 2) (by norm_num) hf2'
  have hR : condExp (enlFilt p m T) (arrayMeasure N) (fun U => ‖f U‖ ^ (2 : ℝ))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m T) (arrayMeasure N) (fun U => f U ^ 2) :=
    condExp_congr_ae (Filter.Eventually.of_forall fun U => norm_rpow_two (f U))
  filter_upwards [h, hR] with U hU hUR
  rw [hUR] at hU
  rwa [norm_rpow_two] at hU

theorem integrable_sq_condExp_enl {p : ℝ} (m T : ℕ) {f : Array N → ℝ}
    (hf : AEStronglyMeasurable f (arrayMeasure N))
    (hf2 : Integrable (fun U => f U ^ 2) (arrayMeasure N)) :
    Integrable (fun U => condExp (enlFilt p m T) (arrayMeasure N) f U ^ 2) (arrayMeasure N) := by
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  have hM : MemLp f 2 (arrayMeasure N) := (memLp_two_iff_integrable_sq hf).2 hf2
  have hM' : MemLp (condExp (enlFilt p m T) (arrayMeasure N) f) 2 (arrayMeasure N) :=
    hM.condExp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsm : StronglyMeasurable (fun U => condExp (enlFilt p m T) (arrayMeasure N) f U) :=
    (stronglyMeasurable_condExp (f := f) (m := enlFilt p m T)
      (μ := arrayMeasure N)).mono ((enlFilt p m).le T)
  exact (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).1 hM'

theorem integral_sq_condExp_le_enl {p : ℝ} (m T : ℕ) {f : Array N → ℝ}
    (hf : AEStronglyMeasurable f (arrayMeasure N))
    (hf2 : Integrable (fun U => f U ^ 2) (arrayMeasure N)) :
    ∫ U, condExp (enlFilt p m T) (arrayMeasure N) f U ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, f U ^ 2 ∂(arrayMeasure N) := by
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  have h := sq_condExp_le_enl (N := N) (p := p) m T hf2
  have hint := integrable_sq_condExp_enl (N := N) (p := p) m T hf hf2
  calc ∫ U, condExp (enlFilt p m T) (arrayMeasure N) f U ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, condExp (enlFilt p m T) (arrayMeasure N) (fun U => f U ^ 2) U
          ∂(arrayMeasure N) := by
        apply integral_mono_ae
        · exact hint
        · exact integrable_condExp
        · exact h
    _ = ∫ U, f U ^ 2 ∂(arrayMeasure N) := integral_condExp ((enlFilt p m).le T)

/-! ## 1. The projected increment and the terminal defect -/

/-- The increment of the optional projection of the raw compensator. -/
noncomputable def pjInc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) : Array N → ℝ :=
  fun U => Qproj p m eps i j (t + 1) U - Qproj p m eps i j t U

/-- The exact terminal defect `Qcomp t - Qproj t` (the realised terminal environment
fluctuation of the potential, by `Qcomp_sub_Qproj_eq_Hpot`). -/
noncomputable def qDef (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) : Array N → ℝ :=
  fun U => Qcomp p m eps (fun r => alphaFun p m r i) i j U t - Qproj p m eps i j t U

/-- `Qproj 0 =ᵐ 0`. -/
theorem Qproj_zero (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) :
    Qproj p m eps i j 0 =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h : (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U 0)
      = fun _ => (0 : ℝ) := by
    funext U
    exact Qcomp_zero p m eps (fun r => alphaFun p m r i) i j U
  rw [Qproj, h]
  exact Filter.EventuallyEq.of_eq (condExp_const ((enlFilt p m).le 0) (0 : ℝ))

/-- Every value of the optional projection is integrable. -/
theorem integrable_Qproj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (T : ℕ) :
    Integrable (Qproj p m eps i j T) (arrayMeasure N) := by
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le T)) := inferInstance
  haveI : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U T) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε T
  exact integrable_condExp (m := enlFilt p m T) (μ := arrayMeasure N)

theorem integrable_pjInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ) :
    Integrable (pjInc p m eps i j t) (arrayMeasure N) :=
  (integrable_Qproj (N := N) hp0 hp1 hε i j (t + 1)).sub
    (integrable_Qproj (N := N) hp0 hp1 hε i j t)

theorem integrable_qDef {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ) :
    Integrable (qDef p m eps i j t) (arrayMeasure N) :=
  (integrable_Qcomp hp0 hp1 hε t).sub (integrable_Qproj (N := N) hp0 hp1 hε i j t)

/-- Pointwise telescoping of the projected increments. -/
theorem sum_pjInc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    ∑ t ∈ Finset.range T, pjInc p m eps i j t U
      = Qproj p m eps i j T U - Qproj p m eps i j 0 U :=
  Finset.sum_range_sub (fun t => Qproj p m eps i j t U) T

/-- **The projected increment is the `𝓕_{t+1}`-conditional mean of the raw increment plus the
terminal defect.**  Nothing here is an adaptedness assumption: the conditional expectation is a
genuine averaging, and `qDef t` is the exact terminal environment fluctuation of the potential. -/
theorem pjInc_eq_condExp {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {eps : ℝ}
    (hε : 0 < eps) (i j : Fin N) (t : ℕ) :
    pjInc p m eps i j t
      =ᵐ[arrayMeasure N] condExp (enlFilt p m (t + 1)) (arrayMeasure N)
          (fun U => SwarmActualBudget.qInc p m eps i j t U + qDef p m eps i j t U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le (t + 1))) := inferInstance
  have hI1 : Integrable (fun U : Array N =>
      Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)) (arrayMeasure N) :=
    integrable_Qcomp hp0 hp1 hε (t + 1)
  have hI2 : Integrable (Qproj p m eps i j t) (arrayMeasure N) :=
    integrable_Qproj (N := N) hp0 hp1 hε i j t
  have hsm : StronglyMeasurable[enlFilt p m (t + 1)] (Qproj p m eps i j t) :=
    (stronglyMeasurable_condExp (f := fun U => Qcomp p m eps (fun r => alphaFun p m r i) i j U t)
      (m := enlFilt p m t) (μ := arrayMeasure N)).mono
      (Filtration.mono (enlFilt p m) (Nat.le_succ t))
  have hfix : condExp (enlFilt p m (t + 1)) (arrayMeasure N) (Qproj p m eps i j t)
      =ᵐ[arrayMeasure N] Qproj p m eps i j t :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable ((enlFilt p m).le (t + 1)) hsm hI2)
  have hsub : condExp (enlFilt p m (t + 1)) (arrayMeasure N)
      (fun U : Array N => Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
        - Qproj p m eps i j t U)
      =ᵐ[arrayMeasure N] pjInc p m eps i j t := by
    refine (condExp_sub hI1 hI2 (enlFilt p m (t + 1))).trans ?_
    filter_upwards [hfix] with U hU
    simp only [Qproj, pjInc, Pi.sub_apply] at hU ⊢
    rw [hU]
  refine hsub.symm.trans ?_
  refine condExp_congr_ae (Filter.EventuallyEq.of_eq ?_)
  funext U
  simp only [qDef, SwarmActualBudget.qInc]
  ring

/-- The defect in terms of the realised terminal potential: `qDef t = Z_t - E[Z_t | 𝓕_t]`. -/
theorem qDef_eq_centredZpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ) :
    qDef p m eps i j t =ᵐ[arrayMeasure N]
      fun U => Zpot p m eps i j U t
        - condExp (enlFilt p m t) (arrayMeasure N)
            (fun U => Zpot p m eps i j U t) U :=
  Qcomp_sub_Qproj_eq (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t


/-! ## 2. Second-moment budget of the projected increment -/

/-- The defect written as the centred terminal potential, pointwise form of
`qDef_eq_centredZpot`. -/
theorem qDef_ae_le_sq {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ) :
    (fun U => qDef p m eps i j t U ^ 2) ≤ᵐ[arrayMeasure N]
      fun U => 2 * Zpot p m eps i j U t ^ 2
        + 2 * condExp (enlFilt p m t) (arrayMeasure N)
            (fun U => Zpot p m eps i j U t) U ^ 2 := by
  filter_upwards [qDef_eq_centredZpot (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t]
    with U hU
  rw [hU]
  nlinarith [sq_nonneg (Zpot p m eps i j U t
    + condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t) U)]

/-- **The squared defect is bounded by four times the squared terminal potential.** -/
theorem integral_sq_qDef_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ)
    (hZ2 : Integrable (fun U => Zpot p m eps i j U t ^ 2) (arrayMeasure N)) :
    ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 4 * ∫ U, Zpot p m eps i j U t ^ 2 ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hZ : Integrable (fun U => Zpot p m eps i j U t) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε t
  have hc2 : Integrable (fun U => condExp (enlFilt p m t) (arrayMeasure N)
      (fun U => Zpot p m eps i j U t) U ^ 2) (arrayMeasure N) :=
    integrable_sq_condExp_enl (N := N) (p := p) m t hZ.aestronglyMeasurable hZ2
  have hjc := integral_sq_condExp_le_enl (N := N) (p := p) m t hZ.aestronglyMeasurable hZ2
  have hmaj : Integrable (fun U => 2 * Zpot p m eps i j U t ^ 2
      + 2 * condExp (enlFilt p m t) (arrayMeasure N)
          (fun U => Zpot p m eps i j U t) U ^ 2) (arrayMeasure N) :=
    (hZ2.const_mul 2).add (hc2.const_mul 2)
  have haele := qDef_ae_le_sq (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t
  have hmeassq : AEStronglyMeasurable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N) :=
    (integrable_qDef (N := N) hp0 hp1 hε i j t).aestronglyMeasurable.pow 2
  have hint : Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' hmaj hmeassq ?_
    filter_upwards [haele] with U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hU
  have hmono := integral_mono_ae hint hmaj haele
  rw [integral_add (hZ2.const_mul 2) (hc2.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith

theorem integrable_sq_qDef {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ)
    (hZ2 : Integrable (fun U => Zpot p m eps i j U t ^ 2) (arrayMeasure N)) :
    Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hZ : Integrable (fun U => Zpot p m eps i j U t) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε t
  have hc2 : Integrable (fun U => condExp (enlFilt p m t) (arrayMeasure N)
      (fun U => Zpot p m eps i j U t) U ^ 2) (arrayMeasure N) :=
    integrable_sq_condExp_enl (N := N) (p := p) m t hZ.aestronglyMeasurable hZ2
  have haele := qDef_ae_le_sq (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t
  refine Integrable.mono' ((hZ2.const_mul 2).add (hc2.const_mul 2))
    ((integrable_qDef (N := N) hp0 hp1 hε i j t).aestronglyMeasurable.pow 2) ?_
  filter_upwards [haele] with U hU
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hU

/-- `(a+b)² ≤ 2a² + 2b²`. -/
theorem sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Square integrability of the projected increment** from the raw increment and the defect. -/
theorem integrable_sq_pjInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N))
    (hd2 : ∀ t, Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N)) (t : ℕ) :
    Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hq1 : Integrable (SwarmActualBudget.qInc p m eps i j t) (arrayMeasure N) :=
    SwarmActualBudget.integrable_qInc hp0 hp1 hε t
  have hd1 : Integrable (qDef p m eps i j t) (arrayMeasure N) :=
    integrable_qDef (N := N) hp0 hp1 hε i j t
  have hf2 : Integrable (fun U => (SwarmActualBudget.qInc p m eps i j t U
      + qDef p m eps i j t U) ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' ((hq2 t).const_mul 2 |>.add ((hd2 t).const_mul 2)) ?_ ?_
    · exact ((hq1.aestronglyMeasurable.add hd1.aestronglyMeasurable)).pow 2
    · filter_upwards with U
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_add_le_two _ _
  have hf : AEStronglyMeasurable (fun U => SwarmActualBudget.qInc p m eps i j t U
      + qDef p m eps i j t U) (arrayMeasure N) :=
    hq1.aestronglyMeasurable.add hd1.aestronglyMeasurable
  have hce := integrable_sq_condExp_enl (N := N) (p := p) m (t + 1) hf hf2
  refine hce.congr ?_
  filter_upwards [pjInc_eq_condExp (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t] with U hU
  rw [hU]

/-- **`L²`/Jensen budget of the projected increment.** -/
theorem integral_sq_pjInc_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N))
    (hd2 : ∀ t, Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N)) (t : ℕ) :
    ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 2 * ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        + 2 * ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set a : Array N → ℝ := fun U => SwarmActualBudget.qInc p m eps i j t U with ha
  set b : Array N → ℝ := fun U => qDef p m eps i j t U with hb
  have hq1 : Integrable a (arrayMeasure N) :=
    SwarmActualBudget.integrable_qInc hp0 hp1 hε t
  have hd1 : Integrable b (arrayMeasure N) := integrable_qDef (N := N) hp0 hp1 hε i j t
  have hf2 : Integrable (fun U => (a U + b U) ^ 2) (arrayMeasure N) := by
    refine Integrable.mono' ((hq2 t).const_mul 2 |>.add ((hd2 t).const_mul 2)) ?_ ?_
    · exact ((hq1.aestronglyMeasurable.add hd1.aestronglyMeasurable)).pow 2
    · filter_upwards with U
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_add_le_two _ _
  have hJ := integral_sq_condExp_le_enl (N := N) (p := p) m (t + 1)
    (hq1.aestronglyMeasurable.add hd1.aestronglyMeasurable) hf2
  have hconv : ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      = ∫ U, condExp (enlFilt p m (t + 1)) (arrayMeasure N)
          (fun U => a U + b U) U ^ 2 ∂(arrayMeasure N) := by
    refine integral_congr_ae ?_
    filter_upwards [pjInc_eq_condExp (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t]
      with U hU
    rw [hU]
  rw [hconv]
  refine le_trans hJ ?_
  have hpt : ∀ U : Array N, (a U + b U) ^ 2 ≤ 2 * a U ^ 2 + 2 * b U ^ 2 :=
    fun U => sq_add_le_two _ _
  have hmaj : Integrable (fun U => 2 * a U ^ 2 + 2 * b U ^ 2) (arrayMeasure N) :=
    ((hq2 t).const_mul 2).add ((hd2 t).const_mul 2)
  have hmono := integral_mono hf2 hmaj hpt
  rw [integral_add ((hq2 t).const_mul 2) ((hd2 t).const_mul 2),
    integral_const_mul, integral_const_mul] at hmono
  exact hmono

/-! ## 3. The projected increments are pairwise orthogonal (no adaptedness needed) -/

private theorem orthogonal_pjInc_lt {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (h2 : ∀ t, Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N))
    {s t : ℕ} (hst : s < t) :
    ∫ U, pjInc p m eps i j s U * pjInc p m eps i j t U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hm : Martingale (fun (T : ℕ) (U : Array N) => Qproj p m eps i j T U)
      (enlFilt p m) (arrayMeasure N) :=
    martingale_Qproj (N := N) hp0 hp1 (m := m) (i := i) (j := j) (eps := eps) hε
  have hsmt : s + 1 ≤ t := hst
  have hsm : StronglyMeasurable[enlFilt p m t] (pjInc p m eps i j s) := by
    have h1 : StronglyMeasurable[enlFilt p m (s + 1)] (Qproj p m eps i j (s + 1)) :=
      stronglyMeasurable_condExp (f := fun U =>
        Qcomp p m eps (fun r => alphaFun p m r i) i j U (s + 1))
        (m := enlFilt p m (s + 1)) (μ := arrayMeasure N)
    have h2' : StronglyMeasurable[enlFilt p m (s + 1)] (Qproj p m eps i j s) :=
      (stronglyMeasurable_condExp (f := fun U =>
        Qcomp p m eps (fun r => alphaFun p m r i) i j U s)
        (m := enlFilt p m s) (μ := arrayMeasure N)).mono
        (Filtration.mono (enlFilt p m) (Nat.le_succ s))
    exact ((h1.sub h2').mono (Filtration.mono (enlFilt p m) hsmt))
  have hgm : Integrable (fun U => pjInc p m eps i j s U
      * MartingaleLimit.inc (fun (T : ℕ) (U : Array N) => Qproj p m eps i j T U) t U)
      (arrayMeasure N) := by
    have heq : (fun U => pjInc p m eps i j s U
        * MartingaleLimit.inc (fun (T : ℕ) (U : Array N) => Qproj p m eps i j T U) t U)
        = fun U => pjInc p m eps i j s U * pjInc p m eps i j t U := rfl
    rw [heq]
    exact QOrth.integrable_mul_of_sq
      (integrable_pjInc (N := N) hp0 hp1 hε i j s).aestronglyMeasurable
      (integrable_pjInc (N := N) hp0 hp1 hε i j t).aestronglyMeasurable (h2 s) (h2 t)
  exact MartingaleLimit.integral_mul_inc_eq_zero (μ := arrayMeasure N) (ℱ := enlFilt p m)
    hm hsm hgm

theorem orthogonal_pjInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (h2 : ∀ t, Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N)) :
    ∀ s t : ℕ, s ≠ t →
      ∫ U, pjInc p m eps i j s U * pjInc p m eps i j t U ∂(arrayMeasure N) = 0 := by
  intro s t hst
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · exact orthogonal_pjInc_lt (N := N) hp0 hp1 hε i j h2 hlt
  · rw [show (fun U : Array N => pjInc p m eps i j s U * pjInc p m eps i j t U)
        = fun U => pjInc p m eps i j t U * pjInc p m eps i j s U from by
      funext U; ring]
    exact orthogonal_pjInc_lt (N := N) hp0 hp1 hε i j h2 hlt

/-- **The exact variance ledger of the projected martingale.** -/
theorem integral_sq_Qproj_eq_sum {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (h2 : ∀ t, Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N)) (T : ℕ) :
    ∫ U, Qproj p m eps i j T U ^ 2 ∂(arrayMeasure N)
      = ∑ t ∈ Finset.range T, ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have horth := orthogonal_pjInc (N := N) hp0 hp1 (m := m) (eps := eps) hε i j h2
  have hint : ∀ t, Integrable (pjInc p m eps i j t) (arrayMeasure N) :=
    fun t => integrable_pjInc (N := N) hp0 hp1 hε i j t
  have h := QOrth.integral_blk_sq (μ := arrayMeasure N) (d := pjInc p m eps i j)
    hint h2 horth 0 T
  simp only [Nat.zero_add] at h
  rw [← h]
  have h0 := Qproj_zero (N := N) p m eps i j
  refine integral_congr_ae ?_
  filter_upwards [h0] with U hU
  have hpt : QOrth.blk (pjInc p m eps i j) 0 T U = Qproj p m eps i j T U := by
    rw [QOrth.blk_sub]
    simp only [Nat.zero_add, QOrth.Q, Finset.sum_range_zero, sub_zero]
    rw [sum_pjInc, hU]
    simp only [Pi.zero_apply, sub_zero]
  rw [hpt]


/-- **Concrete `L²` chain for the projected increment**: raw increment plus realised terminal
potential.  This is the quantitative form of "keep the terminal fluctuation explicit". -/
theorem integral_sq_pjInc_le_Zpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N))
    (hZ2 : ∀ t, Integrable (fun U => Zpot p m eps i j U t ^ 2) (arrayMeasure N)) (t : ℕ) :
    ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 2 * ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        + 8 * ∫ U, Zpot p m eps i j U t ^ 2 ∂(arrayMeasure N) := by
  have hd2 : ∀ t, Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N) :=
    fun t => integrable_sq_qDef (N := N) hp0 hp1 hε i j t (hZ2 t)
  have h1 := integral_sq_pjInc_le (N := N) hp0 hp1 (m := m) (eps := eps) hε i j hq2 hd2 t
  have h2 := integral_sq_qDef_le (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t (hZ2 t)
  linarith

/-! ## 4. Dyadic summability: the projected criterion from the raw and defect criteria -/

/-- The dyadic weight of the accepted criterion. -/
noncomputable def dyaW (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 / 4 ^ k

theorem dyaW_nonneg (k : ℕ) : 0 ≤ dyaW k := by
  unfold dyaW; positivity

/-- **Reduction of the projected dyadic variance criterion.**  The weighted dyadic second-moment
series of the *projected* increments is summable as soon as the corresponding series for the raw
increment and for the exact terminal defect are.  No projection is substituted for `qInc`. -/
theorem summable_dyaW_pjInc_of_raw_defect {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N))
    (hd2 : ∀ t, Integrable (fun U => qDef p m eps i j t U ^ 2) (arrayMeasure N))
    (hraw : Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)))
    (hdef : Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N))) :
    Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hstep : ∀ k : ℕ,
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
          ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        ≤ 2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
          + 2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N)) := by
    intro k
    have h1 : ∑ t ∈ Finset.range (2 ^ (k + 1)),
          ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        ≤ ∑ t ∈ Finset.range (2 ^ (k + 1)),
            (2 * ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
              + 2 * ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N)) :=
      Finset.sum_le_sum (fun t _ =>
        integral_sq_pjInc_le (N := N) hp0 hp1 (m := m) (eps := eps) hε i j hq2 hd2 t)
    have h2 : ∑ t ∈ Finset.range (2 ^ (k + 1)),
            (2 * ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
              + 2 * ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N))
        = 2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
          + 2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [← h2]
    exact h1
  have hnn : ∀ k : ℕ, 0 ≤ dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N) := by
    intro k
    refine mul_nonneg (dyaW_nonneg k) (Finset.sum_nonneg (fun t _ => ?_))
    exact integral_nonneg (fun U => sq_nonneg _)
  have hle : ∀ k : ℕ, dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
      ≤ 2 * (dyaW k * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)))
          + 2 * (dyaW k * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N))) := by
    intro k
    have h := mul_le_mul_of_nonneg_left (hstep k) (dyaW_nonneg k)
    calc dyaW k * ∑ t ∈ Finset.range (2 ^ (k + 1)),
          ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N)
        ≤ dyaW k * (2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N))
          + 2 * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N))) := h
      _ = 2 * (dyaW k * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, SwarmActualBudget.qInc p m eps i j t U ^ 2 ∂(arrayMeasure N)))
          + 2 * (dyaW k * (∑ t ∈ Finset.range (2 ^ (k + 1)),
              ∫ U, qDef p m eps i j t U ^ 2 ∂(arrayMeasure N))) := by ring
  refine Summable.of_nonneg_of_le hnn hle ?_
  exact (hraw.mul_left 2).add (hdef.mul_left 2)

/-! ## 5. The strong law for the projected martingale -/

/-- **The projected half of `hQ`.**  `Qproj` is a genuine martingale, its increments are pairwise
orthogonal by `orthogonal_pjInc`, and the accepted adaptedness-free strong law
(`QOrth.eventually_lower_bound`) gives the one-sided lower budget.  No adaptedness of the raw
`Qcomp`, and no identification of `Qcomp` with `Qproj`, is used anywhere. -/
theorem qproj_lower_bound_of_dyadic {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (h2 : ∀ t, Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N))
    (hvar : Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m eps i j t U ^ 2 ∂(arrayMeasure N))) :
    ∀ δ : ℝ, 0 < δ → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -(δ * (T : ℝ)) ≤ Qproj p m eps i j T U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hint : ∀ t, Integrable (pjInc p m eps i j t) (arrayMeasure N) :=
    fun t => integrable_pjInc (N := N) hp0 hp1 hε i j t
  have horth := orthogonal_pjInc (N := N) hp0 hp1 (m := m) (eps := eps) hε i j h2
  have hmain := QOrth.eventually_lower_bound (μ := arrayMeasure N) hint h2 horth hvar
  intro δ hδ
  filter_upwards [hmain, Qproj_zero (N := N) p m eps i j] with U hU h0
  obtain ⟨N₀, hN₀⟩ := hU δ hδ
  refine ⟨N₀, fun T hT => ?_⟩
  have h := hN₀ T hT
  have hQ : QOrth.Q (pjInc p m eps i j) T U = Qproj p m eps i j T U := by
    simp only [QOrth.Q]
    rw [sum_pjInc, h0]
    simp only [Pi.zero_apply, sub_zero]
  rwa [hQ] at h

/-- The `1/128` one-sided budget for the projected martingale. -/
theorem qproj_budget_of_dyadic {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (i j : Fin N)
    (h2 : ∀ t, Integrable (fun U => pjInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N))) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qproj p m (1 / 64) i j T U :=
  qproj_lower_bound_of_dyadic (N := N) hp0 hp1 (m := m) (eps := 1 / 64) (by norm_num) i j h2
    hvar (1 / 128) (by norm_num)

/-- **The honest two-budget composition into the raw `QResidual`.**  The first input is the
projected dyadic variance criterion (proved here to give the projected budget); the second is the
one-sided budget for the *exact terminal defect* `qDef = Qcomp - Qproj`, which is
`Z_t - E[Z_t | 𝓕_t]` and is **not** proved here.  Nothing in this statement replaces the raw
`Qcomp` by its projection. -/
theorem qresidual_of_proj_dyadic_and_fluct {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ}
    (h2 : ∀ i j : Fin N, i ≠ j → ∀ t,
      Integrable (fun U => pjInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ i j : Fin N, i ≠ j → Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)))
    (hfluct : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ qDef p m (1 / 64) i j T U) :
    SwarmActualBudget.QResidual p m N := by
  have hproj : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qproj p m (1 / 64) i j T U :=
    fun i j hij => qproj_budget_of_dyadic (N := N) hp0 hp1 (m := m) i j (h2 i j hij) (hvar i j hij)
  exact qresidual_of_proj_and_fluct (N := N) (p := p) m hproj hfluct


/-! ## 6. A conditional bridge: raw orthogonality holds if the terminal potential is revealed

`QIncrementAdapted.not_stronglyMeasurable_Zpot_one` shows the hypothesis below is **false** at the
actual model (`m ≥ 3`, `i ≠ j`, all `p ∈ (1/2,1)`).  The point of recording the bridge is exactness:
the only obstruction to raw orthogonality in this route is the revealedness of the terminal
potential, and nothing weaker is being assumed anywhere else. -/

/-- If the realised terminal potential `Z_t` is `𝓕_t`-measurable then the exact defect vanishes. -/
theorem qDef_eq_zero_of_revealed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N) (t : ℕ) {g : Array N → ℝ}
    (hg : StronglyMeasurable[enlFilt p m t] g)
    (hZg : (fun U => Zpot p m eps i j U t) =ᵐ[arrayMeasure N] g) :
    qDef p m eps i j t =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  haveI : SigmaFinite ((arrayMeasure N).trim ((enlFilt p m).le t)) := inferInstance
  have hZ : Integrable (fun U => Zpot p m eps i j U t) (arrayMeasure N) :=
    integrable_Zpot hp0 hp1 m i j hε t
  have hgint : Integrable g (arrayMeasure N) := hZ.congr hZg
  have hc : condExp (enlFilt p m t) (arrayMeasure N) (fun U => Zpot p m eps i j U t)
      =ᵐ[arrayMeasure N] g :=
    (condExp_congr_ae hZg).trans
      (Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable ((enlFilt p m).le t) hg hgint))
  filter_upwards [qDef_eq_centredZpot (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t,
    hZg, hc] with U h1 h2 h3
  rw [h1, h2, h3, sub_self]
  simp only [Pi.zero_apply]

/-- If every defect vanishes then the raw increment agrees a.e. with the projected increment. -/
theorem qInc_eq_pjInc_of_qDef_zero {p : ℝ} (m : ℕ) (eps : ℝ) (i j : Fin N)
    (h : ∀ t, qDef p m eps i j t =ᵐ[arrayMeasure N] 0) (t : ℕ) :
    SwarmActualBudget.qInc p m eps i j t =ᵐ[arrayMeasure N] pjInc p m eps i j t := by
  have h1 := h (t + 1)
  have h0 := h t
  filter_upwards [h1, h0] with U hU1 hU0
  have h1' : Qcomp p m eps (fun r => alphaFun p m r i) i j U (t + 1)
      = Qproj p m eps i j (t + 1) U := by
    simpa only [qDef, Pi.zero_apply, sub_eq_zero] using hU1
  have h0' : Qcomp p m eps (fun r => alphaFun p m r i) i j U t
      = Qproj p m eps i j t U := by
    simpa only [qDef, Pi.zero_apply, sub_eq_zero] using hU0
  simp only [SwarmActualBudget.qInc, pjInc]
  rw [h1', h0']

/-- **Conditional bridge**: if the realised terminal potential were `𝓕_t`-revealed for every `t`,
then the *raw* increments `qInc` would be pairwise orthogonal.  The hypothesis is refuted at the
actual model by `QIncrementAdapted.not_stronglyMeasurable_Zpot_one`; the theorem isolates the
missing input exactly. -/
theorem raw_orthogonal_of_revealed_terminal {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hrev : ∀ t, ∃ g : Array N → ℝ, StronglyMeasurable[enlFilt p m t] g ∧
      (fun U => Zpot p m eps i j U t) =ᵐ[arrayMeasure N] g)
    (h2 : ∀ t, Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N))
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N)) :
    ∀ s t : ℕ, s ≠ t →
      ∫ U, SwarmActualBudget.qInc p m eps i j s U
        * SwarmActualBudget.qInc p m eps i j t U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hzero : ∀ t, qDef p m eps i j t =ᵐ[arrayMeasure N] 0 := by
    intro t
    obtain ⟨g, hg, hZg⟩ := hrev t
    exact qDef_eq_zero_of_revealed (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t hg hZg
  have heq : ∀ t, SwarmActualBudget.qInc p m eps i j t =ᵐ[arrayMeasure N]
      pjInc p m eps i j t := fun t => qInc_eq_pjInc_of_qDef_zero m eps i j hzero t
  have horth := orthogonal_pjInc (N := N) hp0 hp1 (m := m) (eps := eps) hε i j h2
  intro s t hst
  have hst' : (fun U : Array N => SwarmActualBudget.qInc p m eps i j s U
        * SwarmActualBudget.qInc p m eps i j t U)
      =ᵐ[arrayMeasure N] fun U => pjInc p m eps i j s U * pjInc p m eps i j t U := by
    filter_upwards [heq s, heq t] with U h1 h2'
    rw [h1, h2']
  rw [integral_congr_ae hst']
  exact horth s t hst


/-! ## 7. Unconditional second moments: the terminal potential is deterministically bounded

The estimates here use only two elementary facts about the actual model: the walker is at
`|X_t| ≤ t` (`ZBudget.abs_pos_le_time`) and the site potential grows at most linearly in the site
index (`hof_le_lin`).  They give a crude quadratic-in-`t` deterministic bound on `Z_t` and hence,
with conditional Jensen, on the exact defect `qDef t = Z_t − E[Z_t | 𝓕_t]`.  This makes the
defect's square integrability unconditional; it is far too weak to prove any dyadic summability,
and no such claim is made. -/

lemma rhoOf_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : (1 : ℝ) / 2 ≤ p) (b : Bool) :
    SwarmMarks.rhoOf p b ≤ 1 := by
  cases b with
  | false => rw [SwarmMarks.rhoOf_false]
  | true =>
      rw [SwarmMarks.rhoOf_true, div_le_one hp0]
      linarith

theorem hof_le_lin {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (ω : ℕ → Bool) (n : ℕ) :
    SwarmMarks.hof p ω n ≤ 2 * (n : ℝ) + 3 := by
  have hp0 : (0 : ℝ) < p := by linarith
  induction n with
  | zero =>
      rw [SwarmMarks.hof_zero, SwarmMarks.hstep_eq_rho hp0.ne']
      have h := rhoOf_le_one hp0 hp1 (ω 0)
      nlinarith
  | succ k ih =>
      rw [SwarmMarks.hof_succ, SwarmMarks.hstep_eq_rho hp0.ne']
      have h := rhoOf_le_one hp0 hp1 (ω (k + 1))
      have h0 : (1 : ℝ) ≤ SwarmMarks.hof p ω k := SwarmMarks.one_le_hof hp1 hp2 ω k
      have h1 : (0 : ℝ) ≤ 1 + SwarmMarks.hof p ω k := by linarith
      have h2 : SwarmMarks.rhoOf p (ω (k + 1)) * (1 + SwarmMarks.hof p ω k)
          ≤ 1 * (1 + SwarmMarks.hof p ω k) :=
        mul_le_mul_of_nonneg_right h h1
      have h4 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [h4]
      nlinarith

theorem abs_Hpot_envH_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m t : ℕ)
    (j : Fin N) (U : Array N) {x : ℤ} (hx : |x| ≤ (t : ℤ)) :
    |SwarmOcc.Hpot (envH p m j U) x| ≤ (t : ℝ) * (2 * (t : ℝ) + 3) := by
  have hxt : |(x : ℝ)| ≤ (t : ℝ) := by exact_mod_cast hx
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  by_cases hneg : x ≤ 0
  · rw [SwarmOcc.Hpot_of_nonpos hneg, abs_of_nonpos (by exact_mod_cast hneg)]
    have hx' : -(x : ℝ) ≤ (t : ℝ) := by
      have h1 : -(x : ℝ) = |(x : ℝ)| := by
        rw [abs_of_nonpos (by exact_mod_cast hneg)]
      rw [h1]; exact hxt
    have h3 : (0 : ℝ) ≤ (t : ℝ) * (2 * (t : ℝ) + 3) := by positivity
    have h4 : ((t : ℝ)) ≤ (t : ℝ) * (2 * (t : ℝ) + 3) := by
      have : (1 : ℝ) ≤ 2 * (t : ℝ) + 3 := by linarith
      nlinarith
    linarith
  · push Not at hneg
    rw [SwarmOcc.Hpot, if_neg (by linarith : ¬ x ≤ 0)]
    change |∑ u ∈ Finset.range x.toNat,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u|
      ≤ (t : ℝ) * (2 * (t : ℝ) + 3)
    have hxnn : 0 ≤ x := by omega
    have ht_le : x.toNat ≤ t := by
      have h1 : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hxnn
      have h2 : x ≤ (t : ℤ) := le_trans (le_abs_self x) hx
      omega
    have hnn : ∀ u ∈ Finset.range x.toNat,
        (0 : ℝ) ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u := by
      intro u _
      have := SwarmMarks.one_le_hof hp0.le hp1 (SwarmLogRatio.siteMarks p m U j) u
      linarith
    have hbd : ∀ u ∈ Finset.range x.toNat,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u ≤ 2 * (t : ℝ) + 3 := by
      intro u hu
      have hu' : u < x.toNat := Finset.mem_range.mp hu
      have hu'' : u ≤ t := by omega
      have h1 := hof_le_lin hp0.le hp1 (SwarmLogRatio.siteMarks p m U j) u
      have h2 : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast hu''

      linarith
    rw [abs_of_nonneg (Finset.sum_nonneg hnn)]
    have hsum : ∑ u ∈ Finset.range x.toNat,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u
        ≤ (x.toNat : ℝ) * (2 * (t : ℝ) + 3) := by
      calc ∑ u ∈ Finset.range x.toNat,
            SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u
          ≤ ∑ u ∈ Finset.range x.toNat, (2 * (t : ℝ) + 3) := Finset.sum_le_sum hbd
        _ = (x.toNat : ℝ) * (2 * (t : ℝ) + 3) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard : (x.toNat : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_le
    have h3 : (0 : ℝ) ≤ 2 * (t : ℝ) + 3 := by linarith
    nlinarith [hsum, hcard, ht0, h3]

theorem abs_Zpot_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (t : ℕ) (U : Array N) :
    |Zpot p m eps i j U t|
      ≤ (t : ℝ) * (2 * (t : ℝ) + 3) + (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
  have hx : |((trajectory p m U t).pos i)| ≤ (t : ℤ) := ZBudget.abs_pos_le_time p m U i t
  have h1 := abs_Hpot_envH_le (N := N) hp0 hp1 m t j U hx
  have h2 := abs_Fcorr_bRec_le (N := N) hp0 hp1 m t j (eps := eps) hε U
    ((trajectory p m U t).pos i - runMax p m U j t)
  have h3 : (0 : ℝ) ≤ (t : ℝ) * (2 * (t : ℝ) + 3) := by positivity
  have h4 : (0 : ℝ) ≤ (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) := by
    have ha := aRec_lt_one hp0 hp1 m
    have ha0 := zero_le_aRec hp0 hp1 m
    have : (0 : ℝ) < 1 - aRec p m := by linarith
    positivity
  simp only [Zpot]
  exact (abs_sub _ _).trans (by linarith)

theorem integrable_sq_Zpot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    Integrable (fun U : Array N => Zpot p m eps i j U t ^ 2) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hZ := integrable_Zpot hp0 hp1 m i j hε t
  set B : ℝ := (t : ℝ) * (2 * (t : ℝ) + 3)
    + (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) with hBdef
  have hB : (0 : ℝ) ≤ B := by
    have ha := aRec_lt_one hp0 hp1 m
    have ha0 := zero_le_aRec hp0 hp1 m
    have h1 : (0 : ℝ) < 1 - aRec p m := by linarith
    rw [hBdef]; positivity
  refine Integrable.mono' (integrable_const (B ^ 2)) (hZ.aestronglyMeasurable.pow 2) ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := abs_Zpot_le (N := N) hp0 hp1 m i j hε t U
  have h1 : |Zpot p m eps i j U t| ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (by rw [hBdef]; exact h) 2
  simpa [sq_abs] using h1

/-- **The defect is square integrable at the actual model** — unconditionally, with no
hypothesis beyond `1/2 < p < 1` and `0 < eps`.  The bound used is crude and deterministic. -/
theorem integrable_sq_qDef_uncond {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    Integrable (fun U : Array N => qDef p m eps i j t U ^ 2) (arrayMeasure N) :=
  integrable_sq_qDef (N := N) hp0 hp1 (m := m) (eps := eps) hε i j t
    (integrable_sq_Zpot (N := N) hp0 hp1 m i j hε t)

/-- **The defect is deterministically bounded** — a.e., by the same crude bound derived for
`Z_t` and its conditional expectation (conditional Jensen at the level of the sup norm). -/
theorem abs_qDef_le_ae {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) (i j : Fin N)
    {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), |qDef p m eps i j t U|
      ≤ 2 * ((t : ℝ) * (2 * (t : ℝ) + 3)
        + (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2)) := by
  set B : ℝ := (t : ℝ) * (2 * (t : ℝ) + 3)
    + (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - aRec p m) ^ 2) with hBdef
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := enlFilt p m t)
    (μ := arrayMeasure N) (f := fun U => Zpot p m eps i j U t) (R := B)
    (Filter.Eventually.of_forall fun U => by
      rw [hBdef]
      exact abs_Zpot_le (N := N) hp0 hp1 m i j hε t U)
  filter_upwards [qDef_eq_centredZpot (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t,
    hc] with U h1 h2
  rw [h1, hBdef] at *
  have hZ := abs_Zpot_le (N := N) hp0 hp1 m i j hε t U
  rw [hBdef] at hZ ⊢
  exact (abs_sub _ _).trans (by linarith)

/-- **Square integrability of the projected increment needs only the raw increment.**  The
terminal-defect part is supplied unconditionally by `integrable_sq_qDef_uncond`. -/
theorem integrable_sq_pjInc' {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    {eps : ℝ} (hε : 0 < eps) (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m eps i j t U ^ 2)
      (arrayMeasure N)) (t : ℕ) :
    Integrable (fun U => pjInc p m eps i j t U ^ 2) (arrayMeasure N) :=
  integrable_sq_pjInc (N := N) hp0 hp1 (m := m) (eps := eps) hε i j hq2
    (fun t => integrable_sq_qDef_uncond (N := N) hp0 hp1 m i j hε t) t


/-! ## 8. The one-budget form: only the raw second moments are assumed -/

/-- The `1/128` projected budget with the projected second moments *derived* from the raw ones. -/
theorem qproj_budget_of_dyadic_of_raw {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (i j : Fin N)
    (hq2 : ∀ t, Integrable (fun U => SwarmActualBudget.qInc p m (1 / 64) i j t U ^ 2)
      (arrayMeasure N))
    (hvar : Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N))) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qproj p m (1 / 64) i j T U :=
  qproj_budget_of_dyadic (N := N) hp0 hp1 (m := m) i j
    (fun t => integrable_sq_pjInc' (N := N) hp0 hp1 (m := m) (eps := 1 / 64) (by norm_num) i j
      hq2 t) hvar


/-- **The raw-moment form of the two-budget composition into `QResidual`.**  Only the raw
increment's second moments are assumed; the projected ones are derived
(`integrable_sq_pjInc'`), and the defect's square integrability is unconditional
(`integrable_sq_qDef_uncond`).  The two remaining inputs are exactly the projected dyadic
variance series and the one-sided terminal-defect budget. -/
theorem qresidual_of_raw_dyadic_and_fluct {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ}
    (hq2 : ∀ i j : Fin N, i ≠ j → ∀ t,
      Integrable (fun U => SwarmActualBudget.qInc p m (1 / 64) i j t U ^ 2) (arrayMeasure N))
    (hvar : ∀ i j : Fin N, i ≠ j → Summable (fun k : ℕ => dyaW k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, pjInc p m (1 / 64) i j t U ^ 2 ∂(arrayMeasure N)))
    (hfluct : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ qDef p m (1 / 64) i j T U) :
    SwarmActualBudget.QResidual p m N := by
  have hproj : ∀ i j : Fin N, i ≠ j → ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T : ℕ, N₀ ≤ T →
      -((1 / 128 : ℝ) * (T : ℝ)) ≤ Qproj p m (1 / 64) i j T U :=
    fun i j hij => qproj_budget_of_dyadic_of_raw (N := N) hp0 hp1 (m := m) i j
      (hq2 i j hij) (hvar i j hij)
  exact qresidual_of_proj_and_fluct (N := N) (p := p) m hproj hfluct

end Swarming.Enl.ProjHonest
