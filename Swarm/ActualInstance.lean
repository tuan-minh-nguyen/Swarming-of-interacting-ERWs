/-
The actual recursive trajectory is an instance of the assembly's marginal interacting law.
-/
import Swarm.CondExp
import Swarm.Assembly.Model

namespace SwarmCross.Actual

open MeasureTheory Set Filter
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open Swarming.StepCross Swarming.Transition
open scoped ENNReal BigOperators Topology

variable {N : ℕ}

/-- The two definitions of path local time coincide pointwise. -/
lemma localTime_eq_assembly (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) (i : Fin N) (x : ℤ) :
    Swarm.localTime (fun t (U : Array N) => (trajectory p m U t).pos) n U i x =
      localTime (fun t => (trajectory p m U t).pos i) n x := by
  unfold Swarm.localTime localTime
  rw [Finset.card_filter]

lemma otherVisits_eq_assembly (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) (i : Fin N) :
    otherVisits (trajectory p m U n).ell i ((trajectory p m U n).pos i) =
      Swarm.otherVisits (fun t (U : Array N) => (trajectory p m U t).pos) n U i
        ((trajectory p m U n).pos i) := by
  classical
  unfold Swarm.otherVisits otherVisits
  simp_rw [ell_eq_localTime, localTime_eq_assembly]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), if_pos rfl, Nat.add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]

lemma excited_iff_assembly (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) (i : Fin N) :
    Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i) ↔
      Swarm.Excited (fun t (U : Array N) => (trajectory p m U t).pos) m n U i := by
  unfold Excited Swarm.Excited
  rw [otherVisits_eq_assembly]

lemma rightProb_eq_alphaFun (p : ℝ) (m : ℕ) (n : ℕ) (U : Array N) (i : Fin N) :
    Swarm.rightProb p (fun t (U : Array N) => (trajectory p m U t).pos) m n U i =
      alphaFun p m n i U := by
  unfold Swarm.rightProb alphaFun currentAlpha rightProbability
  by_cases h : Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i)
  · rw [if_pos h, if_pos ((excited_iff_assembly p m n U i).mp h)]
    ring
  · rw [if_neg h, if_neg (fun hc => h ((excited_iff_assembly p m n U i).mpr hc))]
    ring

lemma upSet_eq_stepUp (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) :
    Swarm.upSet (fun t (U : Array N) => (trajectory p m U t).pos) n i = stepUp p m n i := rfl

lemma excitedSet_eq_alpha_gt {p : ℝ} (hp : 1 / 2 < p) (m : ℕ) (n : ℕ) (i : Fin N) :
    Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i =
      {U : Array N | 1 / 2 < alphaFun p m n i U} := by
  ext U
  change Swarm.Excited (fun t (U : Array N) => (trajectory p m U t).pos) m n U i ↔ _
  rw [← excited_iff_assembly]
  unfold alphaFun currentAlpha rightProbability
  by_cases h : Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i)
  · simp only [h, if_true, Set.mem_ofPred_eq, true_iff]
    convert hp using 1
  · simp [h]

lemma measurableSet_excitedSet {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (i : Fin N) :
    MeasurableSet (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i) := by
  rw [excitedSet_eq_alpha_gt hp0]
  have hmeas : Measurable (alphaFun (N := N) p m n i) :=
    fun s hs => pathMeas_le (N := N) p m n _ (measurable_alphaFun p m n i hs)
  exact measurableSet_lt measurable_const hmeas

/-- The actual marginal one-step formula on every event of the nested path filtration. -/
theorem measureReal_inter_upSet {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (n : ℕ) (i : Fin N) {A : Set (Array N)} (hA : MeasurableSet[pathMeas p m n] A) :
    (arrayMeasure N).real
        (A ∩ Swarm.upSet (fun t (U : Array N) => (trajectory p m U t).pos) n i) =
      1 / 2 * (arrayMeasure N).real A + (p - 1 / 2) *
        (arrayMeasure N).real
          (A ∩ Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i) := by
  have hμ : (arrayMeasure N).real
        (A ∩ Swarm.upSet (fun t (U : Array N) => (trajectory p m U t).pos) n i) =
      ∫ U in A, Swarm.rightProb p
        (fun t (U : Array N) => (trajectory p m U t).pos) m n U i ∂(arrayMeasure N) := by
    rw [upSet_eq_stepUp]
    calc
      (arrayMeasure N).real (A ∩ stepUp p m n i) =
          ∫ U in A, alphaFun p m n i U ∂(arrayMeasure N) :=
        setIntegral_stepUp_eq hp0 hp1 m n i hA
      _ = ∫ U in A, Swarm.rightProb p
          (fun t (U : Array N) => (trajectory p m U t).pos) m n U i ∂(arrayMeasure N) :=
        setIntegral_congr_fun (pathMeas_le (N := N) p m n A hA)
          (fun U _ => (rightProb_eq_alphaFun p m n U i).symm)
  rw [hμ]
  have hE : MeasurableSet (Swarm.excitedSet
      (fun t (U : Array N) => (trajectory p m U t).pos) m n i) :=
    measurableSet_excitedSet hp0 hp1 m n i
  have hfun : (fun U : Array N => Swarm.rightProb p
      (fun t (U : Array N) => (trajectory p m U t).pos) m n U i) =
      (fun U => 1 / 2 + (p - 1 / 2) *
        (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i).indicator
          (fun _ => (1 : ℝ)) U) := by
    funext U
    unfold Swarm.rightProb
    by_cases h : Swarm.Excited (fun t (U : Array N) => (trajectory p m U t).pos) m n U i
    · simp [Swarm.excitedSet, h]
    · simp [Swarm.excitedSet, h]
  rw [hfun, integral_add (integrable_const _)
    (((integrable_const (1 : ℝ)).indicator hE).const_mul _),
    integral_const_mul, integral_const]
  have hind : ∫ U in A,
      (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i).indicator
        (fun _ => (1 : ℝ)) U ∂(arrayMeasure N) =
      ((arrayMeasure N).restrict A).real
        (Swarm.excitedSet (fun t (U : Array N) => (trajectory p m U t).pos) m n i) := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := (arrayMeasure N).restrict A) (1 : ℝ) hE)
  rw [hind]
  simp only [Measure.real, MeasureTheory.Measure.restrict_apply_univ,
    Measure.restrict_apply hE, smul_eq_mul]
  rw [Set.inter_comm]
  ring

/-- **The actual recursive trajectory satisfies `Swarm.IsInteractingLaw`** on its verified
nested path filtration. The joint product law is stronger; this theorem supplies the weaker
marginal interface used by the abstract assembly. -/
theorem actual_isInteractingLaw {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) :
    Swarm.IsInteractingLaw (pathFilt (N := N) p m) (arrayMeasure N)
      (fun t (U : Array N) => (trajectory p m U t).pos) m p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun n i => pos_adapted p m i n
  · intro U i
    rfl
  · intro n U i
    exact StepCross.pos_succ_eq_or p m U n i
  · exact fun n i A hA => measureReal_inter_upSet hp0 hp1 m n i hA

end SwarmCross.Actual


