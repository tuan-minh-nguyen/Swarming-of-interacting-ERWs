import SwarmDiameter.SwarmRenewal
import SwarmDiameter.TailBounds

open Filter MeasureTheory Set
open Swarming.Uniform SwarmFresh SwarmRestart RawInitialPathLaw RawStrictTransport SwarmRawTimeStrictSum
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

variable {p : ℝ} {m N : ℕ} [Nonempty (Fin N)]

private theorem measurableSet_eventually_runningDiameter_le (C : ℝ) (β : ℕ) :
    MeasurableSet {X : RegenPath.Path N | ∀ᶠ n : ℕ in atTop,
      runningDiameter n X ≤ C * (Real.log (n : ℝ)) ^ β} := by
  simp only [eventually_atTop]
  apply (Measurable.exists (ι := ℕ) ?_).setOf
  intro k
  apply Measurable.forall
  intro n
  exact measurable_const.imp (measurableSet_setOfPred.mp
    (measurable_runningDiameter n measurableSet_Iic))

private theorem eventually_runningDiameter_le_of_shift {X : RegenPath.Path N}
    {t β : ℕ} {d : ℤ} {C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, runningDiameter n (fun u i => X (t + u) i - d) ≤
      C * (Real.log (n : ℝ)) ^ β) :
    ∀ᶠ n : ℕ in atTop, runningDiameter n X ≤ C * (Real.log (n : ℝ)) ^ β := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => C * (Real.log (n : ℝ)) ^ β) atTop atTop := by
    exact (tendsto_pow_atTop (by omega : β ≠ 0) |>.comp hlog).const_mul_atTop hC
  filter_upwards [(tendsto_sub_atTop_nat t).eventually h,
    eventually_ge_atTop (t + 1), hdiv.eventually_ge_atTop (runningDiameter t X)] with n hn ht hprefix
  apply Finset.sup'_le
  intro j hj
  have hjn : j ≤ n := by simpa using hj
  by_cases hjt : j ≤ t
  · exact (pathDiameter_le_runningDiameter hjt X).trans hprefix
  · have hshift := pathDiameter_shift X t (j - t) d
    rw [Nat.add_sub_of_le (by omega : t ≤ j)] at hshift
    have h₁ : 1 ≤ ((n - t : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - t by omega)
    have h₂ : ((n - t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n t
    have hle := Real.log_le_log (zero_lt_one.trans_le h₁) h₂
    calc
      pathDiameter j X = pathDiameter (j - t) (fun u i => X (t + u) i - d) := hshift.symm
      _ ≤ runningDiameter (n - t) (fun u i => X (t + u) i - d) :=
        pathDiameter_le_runningDiameter (Nat.sub_le_sub_right hjn t) _
      _ ≤ C * (Real.log ((n - t : ℕ) : ℝ)) ^ β := hn
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg h₁) hle _) hC.le

/-- A stretched exponential occupation bound in the first regeneration interval
suffices for the logarithmic upper bound under the original law. -/
theorem ae_log_pow_upper_of_regeneration_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {β : ℕ} (hβ : 0 < β) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ x : ℝ in atTop,
      (∑' t : ℕ, (SwarmFB.seedCond (p := p) (m := m) (N := N)).real
        {U | t < firstTime p m U ∧ x ≤ pathDiameter t (posPath p m U)}) ≤
        Real.exp (-c * x ^ (1 / (β : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
      runningDiameter n (posPath p m U) ≤ C * (Real.log (n : ℝ)) ^ β := by
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let _ : IsProbabilityMeasure μstar := SwarmFB.seedCond_isProbabilityMeasure
    (SwarmSeed.strictPos_measure_ne_zero hp₀ hp₁ hm hN)
  obtain ⟨ν, _, _, hformula⟩ := exists_diameter_occupationLaw hp₀ hp₁ hm hN
  have hprob : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      μstar.real {U | x ≤ runningDiameter n (posPath p m U)} ≤
        ((n : ℝ) + 1) * Real.exp (-c * x ^ (1 / (β : ℝ))) := by
    filter_upwards [h] with x hx
    intro n
    have he : {U : Array N | x ≤ runningDiameter n (posPath p m U)} =
        {U | ∃ t ≤ n, pathDiameter t (posPath p m U) ∈ Ici x} := by
      ext U
      exact le_runningDiameter_iff n (posPath (N := N) p m U)
    rw [he]
    exact ((hformula (Ici x) measurableSet_Ici).2.2.2 n).trans
      (mul_le_mul_of_nonneg_left hx (by positivity))
  obtain ⟨C, hC, hstar⟩ := ae_log_pow_upper_of_tail hβ hc hprob
  have hmeas := measurableSet_eventually_runningDiameter_le (N := N) C β
  have hfuture : ∀ᵐ U ∂arrayMeasure N, ∀ᶠ n : ℕ in atTop,
      runningDiameter n (firstFutureZ p m U) ≤ C * (Real.log (n : ℝ)) ^ β := by
    apply (ae_map_iff (measurable_firstFutureZ p m).aemeasurable hmeas).mp
    rw [map_firstFutureZ_eq hp₀ hp₁ hm hN]
    exact (ae_map_iff (measurable_posPath p m N).aemeasurable hmeas).mpr hstar
  refine ⟨C, hC, ?_⟩
  filter_upwards [ae_first_regeneration_finite hp₀ hp₁ hm hN, hfuture] with U hfin hU
  have hN₀ : 0 < N := by omega
  have hcell : U ∈ ⋃ q : LevelTime, rawFirstCell p m q univ := by
    rw [iUnion_rawFirstCell_univ p m hN₀]
    exact hfin
  obtain ⟨q, hq⟩ := mem_iUnion.mp hcell
  rw [firstFutureZ_eq_of_rawFirstCell p m q hN₀ hq] at hU
  exact eventually_runningDiameter_le_of_shift (d := (q.1.1 : ℤ)) (t := q.1.2) hβ hC hU

/-- A stretched exponential bound on the first-regeneration visit count
bounds the upper tail of the limiting diameter law. -/
theorem exists_diameter_limit_with_upper_tail_of_regeneration_occupation
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    {β : ℕ} (hβ : 0 < β) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ x : ℝ in atTop,
      (∑' t : ℕ, (SwarmFB.seedCond (p := p) (m := m) (N := N)).real
        {U | t < firstTime p m U ∧ x ≤ pathDiameter t (posPath p m U)}) ≤
        Real.exp (-c * x ^ (1 / (β : ℝ)))) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ᵐ x ∂ν.toMeasure, 0 ≤ x) ∧
      TendstoInDistribution (fun n (U : Array N) => pathDiameter n (posPath p m U))
        atTop (id : ℝ → ℝ) (fun _ => arrayMeasure N) ν.toMeasure ∧
      ∀ᶠ x : ℝ in atTop, ν.toMeasure.real (Ici x) ≤ Real.exp (-(c / 2) * x ^ (1 / (β : ℝ))) := by
  obtain ⟨ν, hnonneg, hweak, hformula⟩ := exists_diameter_occupationLaw hp₀ hp₁ hm hN
  let μstar := SwarmFB.seedCond (p := p) (m := m) (N := N)
  let b := (∫⁻ U, (firstTime p m U : ℝ≥0∞) ∂μstar).toReal
  have hb : 0 < b := by
    by_contra! hb₀
    have he : b = 0 := le_antisymm hb₀ ENNReal.toReal_nonneg
    have hu := (hformula univ MeasurableSet.univ).1
    change ν.toMeasure.real univ = _ / b at hu
    rw [probReal_univ, he, div_zero] at hu
    exact one_ne_zero hu
  let r : ℝ := 1 / (β : ℝ)
  have hr : 0 < r := one_div_pos.mpr (by exact_mod_cast hβ)
  have ht : Tendsto (fun x : ℝ => Real.exp ((c / 2) * x ^ r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop hr).const_mul_atTop (half_pos hc))
  refine ⟨ν, hnonneg, hweak, ?_⟩
  filter_upwards [h, ht.eventually_ge_atTop b⁻¹] with x hx hxb
  have hf := (hformula (Ici x) measurableSet_Ici).1
  change ν.toMeasure.real (Ici x) =
    (∑' t : ℕ, μstar.real {U | t < firstTime p m U ∧ x ≤ pathDiameter t (posPath p m U)}) / b at hf
  rw [hf, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-c * x ^ r) * b⁻¹ := mul_le_mul_of_nonneg_right hx (inv_pos.mpr hb).le
    _ ≤ Real.exp (-c * x ^ r) * Real.exp ((c / 2) * x ^ r) :=
      mul_le_mul_of_nonneg_left hxb (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Swarming.Diameter
