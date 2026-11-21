import Swarm.SyncAttemptForce
import Swarm.EnlJoint
import Swarm.Reflect.Basic

open Finset MeasureTheory Set
open Swarming.Enl Swarming.Uniform SwarmCross

namespace Swarming.Diameter

variable {N m : ℕ} {p : ℝ}

/-- The mass of a prescribed sequence when each one-step weight is constant
on the event determined by the past and the prescribed prefix. -/
theorem word_mass_eq_mul_prod (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (n k : ℕ) (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) (w : ℕ → ℝ)
    (hweight : ∀ u < k, EqOn (weightFun p m (n + u) (ε u)) (fun _ => w u)
      (G ∩ evWord p m n univ ε u)) :
    (arrayMeasure N).real (G ∩ evWord p m n univ ε k) =
      (∏ u ∈ range k, w u) * (arrayMeasure N).real G := by
  induction k with
  | zero => simp [evWord_zero]
  | succ k ih =>
    let G' := G ∩ evWord p m n univ ε k
    have hG' : MeasurableSet[enlMeas p m (n + k)] G' :=
      ((enlMeas_le_add N p m n k) G hG).inter (measurableSet_evWord_enl p m n univ ε k)
    have hG'₀ : MeasurableSet G' := enlMeas_le p m (n + k) _ hG'
    have hpat : patSetA p m (n + k) univ (ε k) = patSet p m (n + k) (ε k) := by
      ext U
      simp [patSetA, patSet]
    rw [evWord_succ, ← Set.inter_assoc, hpat]
    change (arrayMeasure N).real (G' ∩ patSet p m (n + k) (ε k)) = _
    rw [enl_setIntegral_pattern p hp₀ hp₁ (ε k) (hε k) hG',
      setIntegral_congr_fun hG'₀ (hweight k (by omega)), setIntegral_const, smul_eq_mul]
    dsimp only [G']
    rw [ih (fun u hu => hweight u (by omega)), Finset.prod_range_succ]
    ring

/-- A prescribed sequence of jumps has the mass of a symmetric walk sequence
when the right-jump probabilities are one half on each prefix event. -/
theorem symmetric_word_mass_eq (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (n k : ℕ) (ε : ℕ → Fin N → ℤ) (hε : ∀ u i, ε u i = 1 ∨ ε u i = -1)
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsym : ∀ u < k, ∀ U ∈ G ∩ evWord p m n univ ε u, ∀ i,
      alphaFun p m (n + u) i U = 1 / 2) :
    (arrayMeasure N).real (G ∩ evWord p m n univ ε k) =
      (1 / 2 : ℝ) ^ (k * N) * (arrayMeasure N).real G := by
  rw [word_mass_eq_mul_prod hp₀ hp₁ n k ε hε hG (fun _ => (1 / 2 : ℝ) ^ N)]
  · simp [← pow_mul, Nat.mul_comm]
  · intro u hu U hU
    unfold weightFun
    calc
      _ = ∏ _i : Fin N, (1 / 2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hsym u hu U hU i]
        split_ifs <;> norm_num
      _ = _ := by simp

/-- The signed jumps of a finite sequence, extended by right jumps. -/
def signedSteps {k : ℕ} (ω : Fin k → Fin N → Bool) (u : ℕ) (i : Fin N) : ℤ :=
  if h : u < k then SwarmReflect.step (ω ⟨u, h⟩ i) else 1

theorem signedSteps_is_unit {k : ℕ} (ω : Fin k → Fin N → Bool) (u : ℕ) (i : Fin N) :
    signedSteps ω u i = 1 ∨ signedSteps ω u i = -1 := by
  unfold signedSteps
  split_ifs
  · exact SwarmReflect.step_eq _
  · exact Or.inl rfl

private theorem disjoint_word_events (n k : ℕ) :
    Pairwise (fun ω η : Fin k → Fin N → Bool =>
      Disjoint (evWord p m n univ (signedSteps ω) k) (evWord p m n univ (signedSteps η) k)) := by
  intro ω η hne
  rw [Set.disjoint_left]
  intro U hU hU'
  apply hne
  funext u i
  let _ : Nonempty (Fin N) := ⟨i⟩
  have h₁ := SyncAttemptForce.evWord_step_of_mem hU u.isLt (Finset.mem_univ i)
  have h₂ := SyncAttemptForce.evWord_step_of_mem hU' u.isLt (Finset.mem_univ i)
  rw [h₁, add_right_inj] at h₂
  have h : SwarmReflect.step (ω u i) = SwarmReflect.step (η u i) := by
    simpa only [signedSteps, dif_pos u.isLt, Fin.eta] using h₂
  cases hω : ω u i <;> cases hη : η u i <;> simp_all

/-- Distinct finite jump sequences determine disjoint events. -/
theorem words_mass_eq_sum (n k : ℕ) (W : Finset (Fin k → Fin N → Bool))
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G) :
    (arrayMeasure N).real (⋃ ω ∈ W, G ∩ evWord p m n univ (signedSteps ω) k) =
      ∑ ω ∈ W, (arrayMeasure N).real (G ∩ evWord p m n univ (signedSteps ω) k) := by
  apply measureReal_biUnion_finset (h := fun _ _ => measure_ne_top _ _)
  · intro ω _ η _ hne
    exact (disjoint_word_events (p := p) (m := m) n k hne).mono inter_subset_right inter_subset_right
  · intro ω _
    exact (enlMeas_le p m n _ hG).inter
      (enlMeas_le p m (n + k) _ (measurableSet_evWord_enl p m n univ (signedSteps ω) k))

/-- A finite collection of distinct symmetric jump sequences has mass equal to
its cardinality times the mass of one sequence. -/
theorem symmetric_words_mass_eq (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (n k : ℕ) (W : Finset (Fin k → Fin N → Bool))
    {G : Set (Array N)} (hG : MeasurableSet[enlMeas p m n] G)
    (hsym : ∀ ω ∈ W, ∀ u < k, ∀ U ∈ G ∩ evWord p m n univ (signedSteps ω) u, ∀ i,
      alphaFun p m (n + u) i U = 1 / 2) :
    (arrayMeasure N).real (⋃ ω ∈ W, G ∩ evWord p m n univ (signedSteps ω) k) =
      (W.card : ℝ) * ((1 / 2 : ℝ) ^ (k * N) * (arrayMeasure N).real G) := by
  rw [words_mass_eq_sum n k W hG, Finset.sum_congr rfl (fun ω hω =>
    symmetric_word_mass_eq hp₀ hp₁ n k _ (signedSteps_is_unit ω) hG (hsym ω hω))]
  simp

end Swarming.Diameter
