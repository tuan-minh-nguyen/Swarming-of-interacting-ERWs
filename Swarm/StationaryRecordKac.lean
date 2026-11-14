/-
Stationary record law and the actual first-strict-return/Kac bound from one π.

The two-sided `ν` is the canonical Markov record law for `hitKKernel`.  The
path functional and its normalized fresh law are those of the canonical
segment-enriched chain.  Neither is identified with the raw uniform array,
and the defective selected-band recurrence is not used.
-/
import Swarm.InitialLawTransport
import Swarm.InfSegStationary
import Swarm.RecStationary
import Swarm.ChainRegenKac

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmStationaryRecord

open SimJump SwarmChainRegen SwarmConcat SwarmFinFuture SwarmFreshCompose

variable {N m : ℕ}

/-- The record-state coordinate of the first enriched atom has exactly the
supplied invariant law `π`.  The proof uses `asegK_snd`, the actual marginal
of the horizon-free stopped record kernel from `recordkernel/InfKernel`. -/
theorem infLaw_recordState_zero (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) π) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (fun A => (A 0).2) = π := by
  have hpair : (SwarmSegKernel.pairLaw (N := N) (m := m) p hm π).map Prod.snd = π := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS, SwarmSegKernel.pairLaw,
      Measure.bind_apply (measurable_snd hS)
        (SwarmSegKernel.measurable_asegK (N := N) (m := m) p hm).aemeasurable]
    calc
      (∫⁻ y, SwarmSegKernel.asegK (N := N) (m := m) p hm y (Prod.snd ⁻¹' S) ∂π) =
          ∫⁻ y, (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) y S ∂π := by
        apply lintegral_congr
        intro y
        have h := congrArg (fun μ : Measure (SwarmRec.RecState N m) => μ S)
          (SwarmSegKernel.asegK_snd p hm y)
        rwa [Measure.map_apply measurable_snd hS] at h
      _ = (π.bind (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm)) S := by
        rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
      _ = π S := by rw [Kernel.Invariant.def hinv]
  change Measure.map (Prod.snd ∘ fun A => A 0)
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π) = π
  rw [← Measure.map_map measurable_snd (measurable_pi_apply 0),
    SwarmInfSeg.map_eval_zero p hm hp hp1 π]
  exact hpair

/-- Every record-state coordinate of the canonical enriched trajectory has the
same supplied invariant law `π`.  This uses the genuine invariance of
`hitKKernel`, through shift stationarity of the enriched trajectory. -/
theorem infLaw_recordState_eval (p : ℝ) (hm : 1 ≤ m)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (SimJump.RecKernel.hitKKernel (N := N) (m := m) p hm) π) (n : ℕ) :
    (SwarmInfSeg.infLaw (N := N) (m := m) p hm hp hp1 π).map
      (fun A => (A n).2) = π := by
  have hiter (k : ℕ) (A : ℕ → SwarmInfSeg.Pair N m) :
      ((SwarmChainAssemble.trajShift (N := N) (m := m))^[k] A) 0 = A k := by
    induction k generalizing A with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply, ih]
        rfl
  have heval : (fun A : ℕ → SwarmInfSeg.Pair N m => (A n).2) =
      (fun A => (A 0).2) ∘ (SwarmChainAssemble.trajShift (N := N) (m := m))^[n] := by
    funext A
    exact congrArg Prod.snd (hiter n A).symm
  have hshift := (SwarmInfSeg.measurePreserving_trajShift
    (N := N) (m := m) p hm hp hp1 π hinv).iterate n
  have hev0 : Measurable (fun A : ℕ → SwarmInfSeg.Pair N m => (A 0).2) :=
    measurable_snd.comp (measurable_pi_apply 0)
  have hmeasShift : Measurable (SwarmChainAssemble.trajShift (N := N) (m := m))^[n] :=
    (SwarmChainAssemble.measurable_trajShift (N := N) (m := m)).iterate n
  rw [heval, ← Measure.map_map hev0 hmeasShift, hshift.map_eq]
  exact infLaw_recordState_zero p hm hp hp1 π hinv

/-- One genuine invariant record law gives, simultaneously:

* the two-sided stationary projective limit with exactly the `hitKKernel`
  Markov windows;
* every record-state marginal of the one-sided segment-enriched trajectory;
* integrability and the two numerical Kac bounds for the actual positive-level
  first regeneration statistic under its normalized strict fresh law.

Only `π`, its invariance, and the already-established positivity of
`π(srSet)` are supplied.  Strict-path positivity is proved by the model
parameter theorem, not added as another premise. -/
theorem exists_stationary_recordLaw_and_firstRegenLevel_mean_bound_model
    (hm : 2 ≤ m) (hN : 2 ≤ N) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (π : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant
      (RecKernel.hitKKernel (N := N) (m := m) p (show 1 ≤ m by omega)) π)
    (hπ : 0 < π (SwarmRec.srSet N m)) :
    ∃ ν : Measure (ℤ → SwarmRec.RecState N m),
      IsProjectiveLimit (α := fun _ : ℤ => SwarmRec.RecState N m) ν
        (SwarmChain.winLaw π
          (RecKernel.hitKKernel (N := N) (m := m) p (show 1 ≤ m by omega))) ∧
      IsProbabilityMeasure ν ∧
      (∀ k : ℤ, ν.map (SwarmKol.pathShift (β := SwarmRec.RecState N m) k) = ν) ∧
      (∀ n : ℕ,
        (SwarmInfSeg.infLaw (N := N) (m := m) p (show 1 ≤ m by omega)
          hp0.le hp1.le π).map (fun A => (A n).2) = π) ∧
      Integrable (fun q => (firstRegenLevel q : ℝ))
        ((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ∧
      1 ≤ ∫ q, (firstRegenLevel q : ℝ)
        ∂((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ∧
      ∫ q, (firstRegenLevel q : ℝ)
        ∂((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ≤
        ((π (SwarmRec.srSet N m) * strictLaw p m N Set.univ)⁻¹).toReal := by
  obtain ⟨ν, hproj, hprob, hstat⟩ :=
    SwarmChain.exists_stationary_recordLaw_of_invariant
      (N := N) (m := m) (show 0 < N by omega) p hp0.le hp1.le
      (show 1 ≤ m by omega) π hinv
  obtain ⟨hint, hlower, hupper⟩ :=
    SwarmChainRegen.chainLaw_firstRegenLevel_mean_bound_model
      (N := N) (m := m) hm hN hp0 hp1 π hinv hπ
  exact ⟨ν, hproj, hprob, hstat,
    fun n => infLaw_recordState_eval p (show 1 ≤ m by omega) hp0.le hp1.le π hinv n,
    hint, hlower, hupper⟩

/-- Tightness is the only remaining stochastic input for the whole stationary
record/Kac package.  The invariant probability and its positive simultaneous-
record mass are constructed by `exists_invariant_measure_pos_hitKInf_feller`;
no invariance, stationarity, positivity, or freshness premise is added here. -/
theorem exists_stationary_recordLaw_and_firstRegenLevel_mean_bound_of_tight
    (hm : 2 ≤ m) (hN : 2 ≤ N) {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    (μ₀ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ₀]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (RecKernel.hitKKernel (N := N) (m := m) p
        (show 1 ≤ m by omega)))^[r] μ₀ (SwarmRec.exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (SwarmRec.RecState N m), ∃ hprob : IsProbabilityMeasure π,
      Kernel.Invariant (RecKernel.hitKKernel (N := N) (m := m) p
        (show 1 ≤ m by omega)) π ∧
      0 < π (SwarmRec.srSet N m) ∧
      ∃ ν : Measure (ℤ → SwarmRec.RecState N m),
        IsProjectiveLimit (α := fun _ : ℤ => SwarmRec.RecState N m) ν
          (SwarmChain.winLaw π
            (RecKernel.hitKKernel (N := N) (m := m) p (show 1 ≤ m by omega))) ∧
        IsProbabilityMeasure ν ∧
        (∀ k : ℤ, ν.map (SwarmKol.pathShift (β := SwarmRec.RecState N m) k) = ν) ∧
        (∀ n : ℕ,
          (@SwarmInfSeg.infLaw N m p (show 1 ≤ m by omega)
            hp0.le hp1.le π hprob).map (fun A => (A n).2) = π) ∧
        Integrable (fun q => (firstRegenLevel q : ℝ))
          ((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ∧
        1 ≤ ∫ q, (firstRegenLevel q : ℝ)
          ∂((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ∧
        ∫ q, (firstRegenLevel q : ℝ)
          ∂((strictLaw p m N Set.univ)⁻¹ • strictLaw p m N) ≤
          ((π (SwarmRec.srSet N m) * strictLaw p m N Set.univ)⁻¹).toReal := by
  obtain ⟨π, hprob, hinv, hπ⟩ :=
    RecKernel.exists_invariant_measure_pos_hitKInf_feller
      (N := N) (m := m) p hp0.le hp1.le hp1 (show 1 ≤ m by omega)
      (show 0 < N by omega) μ₀ htight
  letI := hprob
  obtain ⟨ν, hproj, hνprob, hstat, hmarg, hint, hlower, hupper⟩ :=
    exists_stationary_recordLaw_and_firstRegenLevel_mean_bound_model
      (N := N) (m := m) hm hN hp0 hp1 π hinv hπ
  exact ⟨π, hprob, hinv, hπ, ν, hproj, hνprob, hstat, hmarg, hint, hlower, hupper⟩

end SwarmStationaryRecord
