/-
# The excitation-density interface of the campaign's actual model

* the actual array `(arrayMeasure N, trajectory p m)`, giving concrete statements about the
  interacting model (pathwise `limsup` upper bound, and "speed exists iff density has a limit");
* the campaign's `SwarmAudit.CommonLimit` interface (`AuditCone.lean`), which is shown to be
  equivalent to the same statement with the position replaced by the excitation density.

Neither file proves `Swarm.Ballistic` or `Swarm.MainClaim`; they give the exact form in which
the remaining content is a positive excitation-density bound.
-/
import Swarm.Imports
import Swarm.DensReduction
import Swarm.AuditCone

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmDens

variable {N : ℕ} {m : ℕ} {p : ℝ}

/-! ## 1. The campaign's `CommonLimit` is a common-density statement -/

/-- `SwarmAudit.CommonLimit` with the position replaced by the excitation term `(2p-1)ρ`. -/
def CommonDensity (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
      ∃ v : ℝ, ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto (fun n => densTerm p X m n ω i) atTop (𝓝 v)

/-- **`CommonLimit` is exactly its excitation-density form**, with the same generic
quantifiers and the same limit value. -/
theorem commonLimit_iff_density (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) :
    SwarmAudit.CommonLimit m p ↔ CommonDensity m p := by
  constructor
  · rintro h N Ω _ μ _ X 𝓕 hN hlaw
    obtain ⟨v, hv⟩ := h N Ω μ X 𝓕 hN hlaw
    refine ⟨v, ae_all_iff.mpr fun i => ?_⟩
    exact (ae_tendsto_pos_div_iff (X := X) (m := m) hlaw hp1 hp2 i (v := v)).mp
      (hv.mono fun ω hω => hω i)
  · rintro h N Ω _ μ _ X 𝓕 hN hlaw
    obtain ⟨v, hv⟩ := h N Ω μ X 𝓕 hN hlaw
    refine ⟨v, ae_all_iff.mpr fun i => ?_⟩
    exact (ae_tendsto_pos_div_iff (X := X) (m := m) hlaw hp1 hp2 i (v := v)).mpr
      (hv.mono fun ω hω => hω i)

/-! ## 2. The actual interacting array -/

/-- The actual model's normalised position and its excitation density have the same `liminf`,
almost surely, for every walker. -/
theorem actual_ae_liminf_pos_div_eq (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      liminf (fun n => ((Swarming.Trajectory.trajectory p m U n).pos j : ℝ) / (n : ℝ)) atTop
        = liminf (fun n => densTerm p (fun t U => (Swarming.Trajectory.trajectory p m U t).pos)
            m n U j) atTop := by
  haveI := Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  exact ae_liminf_pos_div_eq (SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m)
    hp0.le hp1.le j

/-- **The actual model's pathwise upper bound**: `limsup X_n^j/n ≤ 2p-1` almost surely, with no
convergence hypothesis.  This is strictly stronger than the mean-level
`Swarm.speed_le_two_p_sub_one`, which assumes the limit exists. -/
theorem actual_ae_limsup_pos_div_le (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      limsup (fun n => ((Swarming.Trajectory.trajectory p m U n).pos j : ℝ) / (n : ℝ)) atTop
        ≤ 2 * p - 1 := by
  haveI := Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  exact ae_limsup_pos_div_le (SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m)
    hp0.le hp1.le j

/-- **The actual model's speed exists iff its excitation density has a limit**, and then the two
are equal: `v = (2p-1)·lim_n (1/n)#{t < n : excited}` pathwise. -/
theorem actual_ae_tendsto_pos_div_iff (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N)
    {v : ℝ} :
    (∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
        Tendsto (fun n => ((Swarming.Trajectory.trajectory p m U n).pos j : ℝ) / (n : ℝ))
          atTop (𝓝 v))
      ↔ (∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
        Tendsto (fun n => densTerm p (fun t U => (Swarming.Trajectory.trajectory p m U t).pos)
            m n U j) atTop (𝓝 v)) := by
  haveI := Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  exact ae_tendsto_pos_div_iff (SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m)
    hp0.le hp1.le j

/-- **The exact two-conjunct form of the final target.**  On the paper's parameter range,
`Swarm.MainClaim m p` is equivalent to `Ballistic m p` (positive excitation density, uniform in
`N`) together with the *common excitation-density limit* of `CommonDensity`.  This is the
`MainClaim = Ballistic ∧ CommonLimit` decomposition of `AuditCone.lean` with the common limit
replaced by its exact density form, i.e. the second conjunct is also purely a statement about
the excitation density. -/
theorem mainClaim_iff_ballistic_density (hm : 2 ≤ m) (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    Swarm.MainClaim m p ↔ Swarm.Ballistic m p ∧ CommonDensity m p := by
  constructor
  · intro h
    refine ⟨Swarm.ballistic_of_mainClaim h, (commonLimit_iff_density hp1.le hp2.le).mp ?_⟩
    obtain ⟨κ, hκ, hmain⟩ := h
    intro N Ω _ μ _ X 𝓕 hN hlaw
    obtain ⟨v, -, -, hv⟩ := hmain N Ω μ X 𝓕 hN hlaw
    exact ⟨v, hv⟩
  · rintro ⟨hb, hd⟩
    exact SwarmAudit.mainClaim_of_ballistic_commonLimit_audit hm hp1 hp2 hb
      ((commonLimit_iff_density hp1.le hp2.le).mpr hd)

/-- **The actual model's pathwise interval**: `0 ≤ liminf X_n^j/n` and `limsup X_n^j/n ≤ 2p-1`
almost surely, with no convergence hypothesis. -/
theorem actual_ae_pos_div_interval (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      0 ≤ liminf (fun n => ((Swarming.Trajectory.trajectory p m U n).pos j : ℝ) / (n : ℝ))
            atTop ∧
        limsup (fun n => ((Swarming.Trajectory.trajectory p m U n).pos j : ℝ) / (n : ℝ))
            atTop ≤ 2 * p - 1 := by
  haveI := Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  exact ae_pos_div_interval (SwarmCross.Actual.actual_isInteractingLaw (N := N) hp0 hp1 m)
    hp0.le hp1.le j

end SwarmDens
