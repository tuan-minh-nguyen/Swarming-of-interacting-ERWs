/- Strong law for the paper's adapted projected martingale and its optional-projection
  form.  Only conditional Jensen and the accepted increment envelopes are used. -/
import Swarm.ProjHSpatial
import Swarm.ProjLedgerBridge
import Swarm.ProjResidual

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Swarming.Enl.ProjectedBound

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-- Conditional centring loses only an explicit factor four in a second-moment estimate.
This subtype is used to avoid any adaptation assumption on the uncentred increment. -/
theorem integrable_and_integral_centred_sq_le {f : Array N → ℝ} (n : ℕ)
    (hf : Integrable f (arrayMeasure N)) (hf2 : Integrable (fun U => f U ^ 2) (arrayMeasure N)) :
    Integrable (fun U => (f U - condExp (enlFilt p m n) (arrayMeasure N) f U) ^ 2)
      (arrayMeasure N) ∧
      ∫ U, (f U - condExp (enlFilt p m n) (arrayMeasure N) f U) ^ 2 ∂(arrayMeasure N)
        ≤ 4 * ∫ U, f U ^ 2 ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hcj : Integrable (fun U => condExp (enlFilt p m n) (arrayMeasure N) f U ^ 2)
      (arrayMeasure N) :=
    ProjHonest.integrable_sq_condExp_enl (N := N) (p := p) m n hf.aestronglyMeasurable hf2
  have hP2 : Integrable (fun U => (f U - condExp (enlFilt p m n) (arrayMeasure N) f U) ^ 2)
      (arrayMeasure N) := Integrable.mono'
      ((hf2.const_mul 2).add (hcj.const_mul 2))
      ((hf.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable).pow 2) (by
        filter_upwards with U
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        show (f U - condExp (enlFilt p m n) (arrayMeasure N) f U) ^ 2 ≤
          2 * f U ^ 2 + 2 * condExp (enlFilt p m n) (arrayMeasure N) f U ^ 2
        nlinarith [sq_nonneg (f U + condExp (enlFilt p m n) (arrayMeasure N) f U)])
  refine ⟨hP2, ?_⟩
  have hc_le := ProjHonest.integral_sq_condExp_le_enl (N := N) (p := p) m n
    hf.aestronglyMeasurable hf2
  have hInt : Integrable (fun U => 2 * f U ^ 2 + 2 * condExp (enlFilt p m n) (arrayMeasure N) f U ^ 2)
      (arrayMeasure N) := (hf2.const_mul 2).add (hcj.const_mul 2)
  have hle : ∀ᵐ U ∂(arrayMeasure N),
      (f U - condExp (enlFilt p m n) (arrayMeasure N) f U) ^ 2
        ≤ 2 * f U ^ 2 + 2 * condExp (enlFilt p m n) (arrayMeasure N) f U ^ 2 := by
    filter_upwards with U
    nlinarith [sq_nonneg (f U + condExp (enlFilt p m n) (arrayMeasure N) f U),
      sq_nonneg (condExp (enlFilt p m n) (arrayMeasure N) f U)]
  have hmono := integral_mono_ae hP2 hInt hle
  rw [integral_add (hf2.const_mul 2) (hcj.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  exact hmono.trans (by nlinarith only [hc_le])

/-- The paper's centred projected increments retain a logarithmic second-moment bound. -/
theorem exists_qincProj_moment {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U => (qincProj p m eps i j U t) ^ 2) (arrayMeasure N) ∧
      ∫ U, (qincProj p m eps i j U t) ^ 2 ∂(arrayMeasure N)
        ≤ C * Real.log ((t : ℝ) + 2) ^ 4 := by
  obtain ⟨C, hC, hraw⟩ := exists_integral_sq_ZJincProj_le (N := N)
    (by linarith) hp0 hp1 hm i j hε
  refine ⟨4 * C, by positivity, fun t => ?_⟩
  obtain ⟨hraw2, hrawle⟩ := hraw t
  obtain ⟨hint, hle⟩ := integrable_and_integral_centred_sq_le (p := p) (m := m) t
    (integrable_ZJincProj hp0 hp1 (by linarith) m t i j hε) hraw2
  refine ⟨?_, hle.trans ?_⟩
  · simpa only [qincProj] using hint
  · have hb : 0 ≤ Real.log ((t : ℝ) + 2) ^ 4 := by positivity
    nlinarith [hrawle, hC.le, hb]

/-- The two projected increment constructions are almost-everywhere interchangeable. -/
theorem projInc_eq_qincProj {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (m t : ℕ) (i j : Fin N) {eps : ℝ} (hε : 0 < eps) :
    ProjLedger.projInc p m eps i j t =ᵐ[arrayMeasure N] fun U => qincProj p m eps i j U t := by
  have hD : (fun U => ProjLedger.Zproj p m eps i j (t + 1) U
        - ProjLedger.Zproj p m eps i j t U + Jcorr p m eps i j U t)
      =ᵐ[arrayMeasure N] (fun U => ZJincProj p m eps i j U t) := by
    filter_upwards [ProjLedgerBridge.Zproj_eq_optional_projection (N := N) (m := m)
        hp0 hp1 (t + 1) i j hε,
      ProjLedgerBridge.Zproj_eq_optional_projection (N := N) (m := m) hp0 hp1 t i j hε]
      with U hnext hnow
    simp only [ZJincProj, JcorrProj, Jcorr]
    rw [← hnext, ← hnow]
  have hmean := (condExp_congr_ae hD).symm.trans
    (ProjLedger.condExp_proj_ledger_eq_Edrift (N := N) hp0 hp1 m t i j hε)
  filter_upwards [hD, hmean] with U hU hc
  simp only [ProjLedger.projInc, qincProj]
  rw [hU, hc]

/-- The same second-moment bound applies to the optional-projection assembly, with identical
constants across all walker counts. -/
theorem exists_optional_moment {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun U => (ProjLedger.projInc p m eps i j t U) ^ 2) (arrayMeasure N) ∧
      ∫ U, (ProjLedger.projInc p m eps i j t U) ^ 2 ∂(arrayMeasure N)
        ≤ C * Real.log ((t : ℝ) + 2) ^ 4 := by
  obtain ⟨C, hC, hmain⟩ := exists_qincProj_moment (N := N) hp0 hp1 hm (i := i) (j := j) hε
  refine ⟨C, hC, fun t => ?_⟩
  obtain ⟨hint, hle⟩ := hmain t
  have heq := projInc_eq_qincProj (N := N) hp0 hp1 m t i j hε
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [heq] with U hU; rw [hU]
  · refine le_trans ?_ hle
    exact (integral_congr_ae (heq.mono fun U hU => congrArg (fun x : ℝ => x ^ 2) hU)).le

/-- **The paper's projected `Q` obeys the martingale strong law, unconditionally in N. -/
theorem QProj_div_tendsto_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} {eps : ℝ} (hε : 0 < eps) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun T : ℕ => QProj p m eps i j U T / T) atTop (𝓝 0) := by
  obtain ⟨C, hC, hmom⟩ := exists_qincProj_moment (N := N) hp0 hp1 hm (i := i) (j := j) hε
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hinc : ∀ t : ℕ, MartingaleLimit.inc (fun T U => QProj p m eps i j U T) t
      = fun U => qincProj p m eps i j U t := by
    intro t; funext U
    simp only [MartingaleLimit.inc_apply, QProj, Finset.sum_range_succ]
    ring
  have hmain := MartingaleLimit.martingale_strong_law_of_log_variance
    (μ := arrayMeasure N) (ℱ := enlFilt (N := N) p m) (C := C)
    (Q := fun T U => QProj p m eps i j U T)
    (martingale_QProj hp0 hp1 (by linarith) m i j hε)
    (fun t => by simpa only [hinc t] using (hmom t).1)
    (fun t => by simpa only [hinc t] using (hmom t).2)
  filter_upwards [hmain] with U hU
  simpa only [QProj, Finset.range_zero, Finset.sum_empty, sub_zero] using hU

/-- The optional-projection strong law, in the shape consumed by ProjectedUniform. -/
theorem ae_Qpl_lower {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin N) : ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤ ProjLedger.Qpl p m (1 / 64) i j T U := by
  obtain ⟨C, hC, hmom⟩ := exists_optional_moment (N := N) hp0 hp1 hm (i := i) (j := j)
    (eps := 1 / 64) (by norm_num)
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hinc : ∀ t : ℕ, MartingaleLimit.inc (fun T U => ProjLedger.Qpl p m (1 / 64) i j T U) t
      = ProjLedger.projInc p m (1 / 64) i j t := by
    intro t; funext U
    simp only [MartingaleLimit.inc_apply, ProjLedger.Qpl, Finset.sum_range_succ]
    ring
  have hmain := MartingaleLimit.martingale_strong_law_of_log_variance
    (μ := arrayMeasure N) (ℱ := enlFilt (N := N) p m) (C := C)
    (Q := fun T U => ProjLedger.Qpl p m (1 / 64) i j T U)
    (ProjLedger.martingale_Qpl hp0 hp1 m (by norm_num) (i := i) (j := j))
    (fun t => by simpa only [hinc] using (hmom t).1)
    (fun t => by simpa only [hinc] using (hmom t).2)
  filter_upwards [hmain] with U hU
  have hzero : ProjLedger.Qpl p m (1 / 64) i j 0 U = 0 := by simp [ProjLedger.Qpl]
  have hlim : Tendsto (fun T => ProjLedger.Qpl p m (1 / 64) i j T U / (T : ℝ)) atTop (𝓝 0) := by
    simp only [hzero, sub_zero] at hU
    exact hU
  exact SwarmProjRes.tendsto_zero_div_eventually_lower (by norm_num) hlim

end Swarming.Enl.ProjectedBound


