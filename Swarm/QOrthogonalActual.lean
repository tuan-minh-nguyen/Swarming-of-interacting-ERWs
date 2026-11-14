/-
  `QOrthogonalStrongLaw` applied to the raw actual-model compensator.

  This file supplies interfaces only.  It does not prove that raw increments are square
  integrable, pairwise orthogonal, or almost everywhere measurable in the one-step filtration.
  The raw pointwise adaptedness countermodel remains in force.  Its optional projection is a
  different process and is not substituted here.
-/
import Swarm.QOrthogonalStrongLaw
import Swarm.ActualBudgetInterfaces
import Swarm.QIncrementAdapted

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace SwarmActualBudget

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.VdriftAssembly

variable {N : ℕ}

/-- The increment of the raw actual compensator, without replacing it by a projected version. -/
noncomputable def qInc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (t : ℕ) (U : Array N) : ℝ :=
  Qcomp p m eps (fun s => alphaFun p m s i) i j U (t + 1) -
    Qcomp p m eps (fun s => alphaFun p m s i) i j U t

theorem sum_qInc (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (U : Array N) (T : ℕ) :
    QOrth.Q (qInc p m eps i j) T U = Qcomp p m eps (fun s => alphaFun p m s i) i j U T := by
  simp only [QOrth.Q, qInc]
  rw [Qcomp_eq_sum_increments]
  exact Finset.sum_congr rfl fun t _ => Qcomp_succ_sub p m eps (fun s => alphaFun p m s i) i j U t

theorem integrable_qInc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} (hε : 0 < eps) {i j : Fin N} (t : ℕ) :
    Integrable (qInc p m eps i j t) (arrayMeasure N) :=
  integrable_Qcomp_increment hp0 hp1 hε

/-- **Orthogonality from one-step a.e. measurability.**  This is weaker than pointwise
`StronglyMeasurable`; the latter was refuted for `ZJinc`.  Nothing here proves the a.e.
premise for the actual raw process. -/
theorem orthogonal_of_aeMeasurable {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {eps : ℝ} (hε : 0 < eps) {i j : Fin N} {s t : ℕ} (hst : s < t)
    (hs : AEStronglyMeasurable[enlFilt p m (s + 1)] (qInc p m eps i j s) (arrayMeasure N))
    (h2 : ∀ r : ℕ, Integrable (fun U => (qInc p m eps i j r U) ^ 2) (arrayMeasure N)) :
    ∫ U, qInc p m eps i j s U * qInc p m eps i j t U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hprod : Integrable (fun U => qInc p m eps i j s U * qInc p m eps i j t U)
      (arrayMeasure N) := QOrth.integrable_mul_of_sq
    (integrable_qInc hp0 hp1 hε (i := i) (j := j) s).aestronglyMeasurable
    (integrable_qInc hp0 hp1 hε (i := i) (j := j) t).aestronglyMeasurable (h2 s) (h2 t)
  have hzero := condExp_Qcomp_increment_eq_zero_of_le
    (N := N) (p := p) (m := m) (i := i) (j := j) (hst := Nat.succ_le_of_lt hst)
    hp0 hp1 hε
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    (m := enlFilt p m (s + 1)) (μ := arrayMeasure N) hs hprod
    (integrable_qInc hp0 hp1 hε (i := i) (j := j) t)
  have hcond : condExp (enlFilt p m (s + 1)) (arrayMeasure N)
      (fun U => qInc p m eps i j s U * qInc p m eps i j t U)
      =ᵐ[arrayMeasure N] 0 := by
    refine hpull.trans ?_
    filter_upwards [hzero] with U hU
    have hUt : (condExp (enlFilt p m (s + 1)) (arrayMeasure N)
        (qInc p m eps i j t)) U = 0 := hU
    change qInc p m eps i j s U * (condExp (enlFilt p m (s + 1))
      (arrayMeasure N) (qInc p m eps i j t)) U = 0
    rw [hUt]
    simp
  rw [← integral_condExp (μ := arrayMeasure N) (f :=
    fun U => qInc p m eps i j s U * qInc p m eps i j t U) ((enlFilt p m).le (s + 1))]
  simpa using integral_congr_ae hcond

/-- **The actual `QResidual` from raw pairwise orthogonality and the sharpened dyadic variance
criterion.**  The `Z` and `J` budgets are not reopened: they are consumed independently by the
occupation interface. -/
theorem qResidual_of_orthogonal {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N}
    (h2 : ∀ t : ℕ, Integrable (fun U => (qInc p m (1 / 64) i j t U) ^ 2) (arrayMeasure N))
    (horth : ∀ s t : ℕ, s ≠ t →
      ∫ U, qInc p m (1 / 64) i j s U * qInc p m (1 / 64) i j t U
        ∂(arrayMeasure N) = 0)
    (hvar : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / 4 ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, (qInc p m (1 / 64) i j t U) ^ 2 ∂(arrayMeasure N))) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤
        Qcomp p m (1 / 64) (fun s => alphaFun p m s i) i j U T := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hint : ∀ t : ℕ, Integrable (qInc p m (1 / 64) i j t) (arrayMeasure N) :=
    integrable_qInc hp0 hp1 (by norm_num)
  have hmain := QOrth.eventually_lower_bound (μ := arrayMeasure N) hint h2 horth hvar
  filter_upwards [hmain] with U hU
  simpa only [sum_qInc] using hU (1 / 64 : ℝ) (by norm_num)

/-- The same reduction with a.e. one-step measurability replacing the direct orthogonality
assumption.  The raw `QResidual` and variance requirement remain entirely non-vacuous. -/
theorem qResidual_of_aeMeasurable {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N}
    (hmeas : ∀ t : ℕ, AEStronglyMeasurable[enlFilt p m (t + 1)]
      (qInc p m (1 / 64) i j t) (arrayMeasure N))
    (h2 : ∀ t : ℕ, Integrable (fun U => (qInc p m (1 / 64) i j t U) ^ 2) (arrayMeasure N))
    (hvar : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / 4 ^ k *
      ∑ t ∈ Finset.range (2 ^ (k + 1)),
        ∫ U, (qInc p m (1 / 64) i j t U) ^ 2 ∂(arrayMeasure N))) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ N₀ : ℕ, ∀ T ≥ N₀,
      -((1 / 64 : ℝ) * (T : ℝ)) ≤
        Qcomp p m (1 / 64) (fun s => alphaFun p m s i) i j U T := by
  have horth : ∀ s t : ℕ, s ≠ t →
      ∫ U, qInc p m (1 / 64) i j s U * qInc p m (1 / 64) i j t U
        ∂(arrayMeasure N) = 0 := by
    intro s t hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact orthogonal_of_aeMeasurable hp0 hp1 (by norm_num) hst (hmeas s) h2
    · rw [show (fun U => qInc p m (1 / 64) i j s U * qInc p m (1 / 64) i j t U)
        = fun U => qInc p m (1 / 64) i j t U * qInc p m (1 / 64) i j s U from by
        funext U; rw [mul_comm]]
      exact orthogonal_of_aeMeasurable hp0 hp1 (by norm_num) hts (hmeas t) h2
  exact qResidual_of_orthogonal hp0 hp1 h2 horth hvar

end SwarmActualBudget
