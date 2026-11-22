import Swarm.FrozenBase
import Swarm.ClockFibreAzuma
import Swarm.ProjHRecord
import Swarm.GlobalPaperCondExp

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmSpeed.Frozen SwarmStop SwarmRecordMeas.Actual
open Swarming.Enl.VdriftAssembly
open scoped ENNReal Function

set_option autoImplicit false

namespace Swarming.Diameter

variable {N : ℕ}

/-- Survival in the open interval \((a,b+1)\) from time \(s\) through time \(s+n\). -/
def intervalSurvival (p : ℝ) (m : ℕ) (i : Fin N) (a b s n : ℕ) : Set (Array N) :=
  {U | ((s + n : ℕ) : WithTop ℕ) < exitAfterStart p m i a b s U}

theorem mem_intervalSurvival_iff {p : ℝ} {m : ℕ} {i : Fin N} {a b s n : ℕ} {U : Array N} :
    U ∈ intervalSurvival p m i a b s n ↔
      ∀ u : ℕ, s ≤ u → u ≤ s + n →
        (a : ℤ) < (trajectory p m U u).pos i ∧ (trajectory p m U u).pos i < ((b + 1 : ℕ) : ℤ) := by
  constructor
  · intro h u hsu hun
    exact trajExit_interior p m (by exact_mod_cast hsu)
      ((show (u : WithTop ℕ) ≤ ((s + n : ℕ) : WithTop ℕ) by exact_mod_cast hun).trans_lt h)
  · intro h
    change ((s + n : ℕ) : WithTop ℕ) < exitAfterStart p m i a b s U
    apply lt_of_not_ge
    intro hn
    obtain ⟨u, hun, hsu, hout⟩ := (trajExit_le_iff p m (s + n)).mp hn
    obtain ⟨h₁, h₂⟩ := h u (by exact_mod_cast hsu) hun
    exact hout.elim (not_le_of_gt h₁) (not_le_of_gt h₂)

theorem measurableSet_intervalSurvival (p : ℝ) (m : ℕ) (i : Fin N) (a b s n : ℕ) :
    MeasurableSet[enlFilt p m (s + n)] (intervalSurvival p m i a b s n) := by
  have h := isStoppingTime_exitAfterStart p m i a b s (s + n)
  convert h.compl using 1
  ext U
  simp only [intervalSurvival, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rfl

private theorem integral_HpotInc_ge_measure_of_below {p : ℝ} {m t : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m t] A)
    (hbelow : ∀ U ∈ A, 0 ≤ (trajectory p m U t).pos i ∧
      (trajectory p m U t).pos i < runMax p m U j t) :
    (arrayMeasure N).real A ≤ ∫ U in A, HpotInc p m t i j U ∂arrayMeasure N := by
  let μ := arrayMeasure N
  let f := HpotInc p m t i j
  have hf : Integrable f μ := Budget.integrable_HpotInc hp₀ hp₁ (by linarith) m t i j
  have hA₀ : MeasurableSet A := (enlFilt p m).le t A hA
  have hle := Budget.paperWeight_le_condExp_discharged (N := N) (m := m) (n := t) hp₀ hp₁ hm hij
  have hineq : ∫ U in A, (1 : ℝ) ∂μ ≤ ∫ U in A, μ[f | enlFilt p m t] U ∂μ := by
    apply setIntegral_mono_on_ae (integrableOn_const (by finiteness)) integrable_condExp.integrableOn hA₀
    filter_upwards [hle] with U hU hmem
    obtain ⟨h₀, hlt⟩ := hbelow U hmem
    have hpos : 0 ≤ (trajectory p m U t).pos i ∧
        (trajectory p m U t).pos i ≤ runMax p m U j t := ⟨h₀, hlt.le⟩
    have he : Budget.paperWeight p m t i j U = 1 := by
      simp only [Budget.paperWeight, if_pos hpos, if_neg (not_le_of_gt hlt), mul_zero, sub_zero]
    exact he ▸ hU
  rw [setIntegral_condExp ((enlFilt p m).le t) hf hA] at hineq
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using hineq

/-- The quenched potential is nondecreasing. -/
theorem Hpot_envH_monotone {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1)
    (j : Fin N) (U : Array N) : Monotone (SwarmOcc.Hpot (envH p m j U)) := by
  apply monotone_int_of_le_succ
  intro z
  apply sub_nonneg.mp
  rw [SwarmOcc.Hpot_succ_sub]
  split
  · exact zero_le_one.trans (SwarmMarks.one_le_hof hp₀ hp₁ _ _)
  · exact zero_le_one

private theorem stopped_position_interval {p : ℝ} {m : ℕ} {i : Fin N} {a b s : ℕ} {U : Array N}
    (hstart : (a : ℤ) < (trajectory p m U s).pos i ∧
      (trajectory p m U s).pos i < ((b + 1 : ℕ) : ℤ)) (n : ℕ) :
    (a : ℤ) ≤ zWalk p m i a b s (s + n) U ∧
      zWalk p m i a b s (s + n) U ≤ ((b + 1 : ℕ) : ℤ) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, show zWalk p m i a b s s U = (trajectory p m U s).pos i from
      stoppedProcess_eq_of_le (exitAfterStart_le p m i a b s U)]
    exact ⟨hstart.1.le, hstart.2.le⟩
  | succ n ih =>
    by_cases h : U ∈ intervalSurvival p m i a b s n
    · have hlt : ((s + n : ℕ) : WithTop ℕ) < exitAfterStart p m i a b s U := h
      have hnext := next_coe_le_exit_of_lt p m i (n := s + n) hlt
      have hi := (mem_intervalSurvival_iff.mp h) (s + n) (Nat.le_add_right _ _) le_rfl
      have he : zWalk p m i a b s (s + n + 1) U = (trajectory p m U (s + n + 1)).pos i :=
        stoppedProcess_eq_of_le (by exact_mod_cast hnext)
      rw [Nat.add_succ, he]
      rcases pos_succ_eq_add_one_or_sub_one p m U i (s + n) with hstep | hstep <;> omega
    · have hstop : exitAfterStart p m i a b s U ≤ ((s + n : ℕ) : WithTop ℕ) := le_of_not_gt h
      have hstop' : exitAfterStart p m i a b s U ≤ ((s + (n + 1) : ℕ) : WithTop ℕ) :=
        hstop.trans (by exact_mod_cast Nat.le_succ (s + n))
      have h₀ : zWalk p m i a b s (s + n) U =
          (trajectory p m U (exitAfterStart p m i a b s U).untopA).pos i :=
        stoppedProcess_eq_of_ge hstop
      have h₁ : zWalk p m i a b s (s + (n + 1)) U =
          (trajectory p m U (exitAfterStart p m i a b s U).untopA).pos i :=
        stoppedProcess_eq_of_ge hstop'
      rwa [h₁.trans h₀.symm]

/-- If the other walker has reached the right endpoint and its potential
difference across the interval is bounded by \(D\), the survival probability
through \(n\) steps on an adapted event is at most \(D/n\) times its mass. -/
theorem interval_survival_prob_le_div {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {a b s n : ℕ} (hn : 0 < n)
    {D : ℝ} {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    (hstart : ∀ U ∈ A, (a : ℤ) < (trajectory p m U s).pos i ∧
      (trajectory p m U s).pos i < ((b + 1 : ℕ) : ℤ))
    (hmax : ∀ U ∈ A, ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j s)
    (hspan : ∀ U ∈ A, SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) -
      SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D) :
    (arrayMeasure N).real (A ∩ intervalSurvival p m i a b s n) ≤
      D / (n : ℝ) * (arrayMeasure N).real A := by
  classical
  let μ := arrayMeasure N
  let S (k : ℕ) := intervalSurvival p m i a b s k
  let f (k : ℕ) := (S k).indicator (HpotInc p m (s + k) i j)
  let Y (U : Array N) (k : ℕ) := SwarmOcc.Hpot (envH p m j U) (zWalk p m i a b s (s + k) U)
  have hA₀ : MeasurableSet A := (enlFilt p m).le s A hA
  have hS (k : ℕ) : MeasurableSet (S k) :=
    (enlFilt p m).le _ _ (measurableSet_intervalSurvival p m i a b s k)
  have hf (k : ℕ) : IntegrableOn (f k) A μ :=
    ((Budget.integrable_HpotInc hp₀ hp₁ (by linarith) m (s + k) i j).indicator (hS k)).integrableOn
  have hbound (k : ℕ) (hk : k < n) : μ.real (A ∩ S n) ≤ ∫ U in A, f k U ∂μ := by
    have hAm : MeasurableSet[enlFilt p m (s + k)] (A ∩ S k) :=
      ((enlFilt p m).mono (Nat.le_add_right _ _) _ hA).inter
        (measurableSet_intervalSurvival p m i a b s k)
    have hmono : A ∩ S n ⊆ A ∩ S k := fun U hU =>
      ⟨hU.1, mem_intervalSurvival_iff.mpr (fun u hsu hu =>
        mem_intervalSurvival_iff.mp hU.2 u hsu (hu.trans (Nat.add_le_add_left hk.le _)))⟩
    have hcond := integral_HpotInc_ge_measure_of_below hp₀ hp₁ hm hij hAm (fun U hU => by
      have h₁ := mem_intervalSurvival_iff.mp hU.2 (s + k) (Nat.le_add_right _ _) le_rfl
      exact ⟨(Int.natCast_nonneg a).trans h₁.1.le, h₁.2.trans_le
        ((hmax U hU.1).trans (runMax_mono p m U j (Nat.le_add_right _ _)))⟩)
    rw [show (∫ U in A, f k U ∂μ) = ∫ U in A ∩ S k, HpotInc p m (s + k) i j U ∂μ by
      dsimp only [f]
      exact setIntegral_indicator (hS k)]
    exact (measureReal_mono hmono (measure_ne_top _ _)).trans hcond
  have hdiff (U : Array N) (k : ℕ) : f k U = Y U (k + 1) - Y U k := by
    by_cases hU : U ∈ S k
    · have hlt : ((s + k : ℕ) : WithTop ℕ) < exitAfterStart p m i a b s U := hU
      have h₁ : zWalk p m i a b s (s + k) U = (trajectory p m U (s + k)).pos i :=
        stoppedProcess_eq_of_le hlt.le
      have h₂ : zWalk p m i a b s (s + k + 1) U = (trajectory p m U (s + k + 1)).pos i :=
        stoppedProcess_eq_of_le (by exact_mod_cast next_coe_le_exit_of_lt p m i (n := s + k) hlt)
      simp only [f, Set.indicator_of_mem hU, Y, Nat.add_succ, h₁, h₂]
      rfl
    · have hstop : exitAfterStart p m i a b s U ≤ ((s + k : ℕ) : WithTop ℕ) := le_of_not_gt hU
      have hstop' : exitAfterStart p m i a b s U ≤ ((s + (k + 1) : ℕ) : WithTop ℕ) :=
        hstop.trans (by exact_mod_cast Nat.le_succ (s + k))
      have h₀ : zWalk p m i a b s (s + k) U =
          (trajectory p m U (exitAfterStart p m i a b s U).untopA).pos i :=
        stoppedProcess_eq_of_ge hstop
      have h₁ : zWalk p m i a b s (s + (k + 1)) U =
          (trajectory p m U (exitAfterStart p m i a b s U).untopA).pos i :=
        stoppedProcess_eq_of_ge hstop'
      have hEq := h₁.trans h₀.symm
      simp only [f, Set.indicator_of_notMem hU, Y, hEq, sub_self]
  have hsum : (n : ℝ) * μ.real (A ∩ S n) ≤ ∫ U in A, ∑ k ∈ Finset.range n, f k U ∂μ := by
    rw [integral_finsetSum _ (fun k _ => hf k)]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.range n) (fun k hk => hbound k (Finset.mem_range.mp hk)))
  have hbudget : (∫ U in A, ∑ k ∈ Finset.range n, f k U ∂μ) ≤ D * μ.real A := by
    have hle := setIntegral_mono_on ((integrable_finsetSum _ fun k _ => hf k) :
      IntegrableOn (fun U => ∑ k ∈ Finset.range n, f k U) A μ)
      (integrableOn_const (C := D) (by finiteness)) hA₀
      (fun U hU => by
        simp only [hdiff]
        rw [Finset.sum_range_sub]
        have h₀ := (stopped_position_interval (hstart U hU) 0).1
        have h₁ := (stopped_position_interval (hstart U hU) n).2
        have hmon := Hpot_envH_monotone (m := m) hp₀.le hp₁ j U
        exact (sub_le_sub (hmon h₁) (hmon h₀)).trans (hspan U hU))
    simpa only [setIntegral_const, smul_eq_mul, mul_comm (μ.real A)] using hle
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have h : μ.real (A ∩ S n) ≤ (D * μ.real A) / (n : ℝ) :=
    (le_div_iff₀ hn₀).mpr (by rw [mul_comm]; exact hsum.trans hbudget)
  exact h.trans_eq (by ring)

/-- If every time interval has length at least twice the potential difference,
iterating the survival estimate costs a factor of one half per interval. -/
theorem interval_survival_prob_le_pow_half {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) {a b s n : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 2 * D ≤ (n : ℝ)) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m s] A)
    (hmax : ∀ U ∈ A, ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j s)
    (hspan : ∀ U ∈ A, SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) -
      SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D) (k : ℕ) :
    (arrayMeasure N).real (A ∩ intervalSurvival p m i a b s (k * n)) ≤
      (1 / 2 : ℝ) ^ k * (arrayMeasure N).real A := by
  let μ := arrayMeasure N
  induction k with
  | zero =>
    simpa only [pow_zero, one_mul] using
      (measureReal_mono (μ := μ) (inter_subset_left (t := intervalSurvival p m i a b s (0 * n)))
        (measure_ne_top _ _))
  | succ k ih =>
    let S := A ∩ intervalSurvival p m i a b s (k * n)
    have hS : MeasurableSet[enlFilt p m (s + k * n)] S :=
      ((enlFilt p m).mono (Nat.le_add_right _ _) _ hA).inter
        (measurableSet_intervalSurvival p m i a b s (k * n))
    have hStep := interval_survival_prob_le_div hp₀ hp₁ hm hij hn hS
      (fun U hU => (mem_intervalSurvival_iff.mp hU.2) (s + k * n) (Nat.le_add_right _ _) le_rfl)
      (fun U hU => (hmax U hU.1).trans (runMax_mono p m U j (Nat.le_add_right _ _)))
      (fun U hU => hspan U hU.1)
    have hsub : A ∩ intervalSurvival p m i a b s ((k + 1) * n) ⊆
        S ∩ intervalSurvival p m i a b (s + k * n) n := by
      rintro U ⟨hUA, hU⟩
      have h := mem_intervalSurvival_iff.mp hU
      rw [Nat.succ_mul, ← Nat.add_assoc] at h
      exact ⟨⟨hUA, mem_intervalSurvival_iff.mpr fun u hs hu => h u hs (by omega)⟩,
        mem_intervalSurvival_iff.mpr fun u hs hu => h u (by omega) hu⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hhalf : D / (n : ℝ) ≤ (1 : ℝ) / 2 := (div_le_iff₀ hn').mpr (by linarith only [hD])
    calc
      _ ≤ μ.real (S ∩ intervalSurvival p m i a b (s + k * n) n) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ D / (n : ℝ) * μ.real S := hStep
      _ ≤ (1 / 2 : ℝ) * μ.real S := mul_le_mul_of_nonneg_right hhalf measureReal_nonneg
      _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * μ.real A) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- On nonnegative integer arguments the potential difference is the finite
sum of site increments between the endpoints. -/
theorem Hpot_nat_sub_eq_sum_Ico (h : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    SwarmOcc.Hpot h (b : ℤ) - SwarmOcc.Hpot h (a : ℤ) = ∑ z ∈ Finset.Ico a b, h z := by
  have he (k : ℕ) : SwarmOcc.Hpot h (k : ℤ) = ∑ z ∈ Finset.range k, h z := by
    cases k with
    | zero => simp [SwarmOcc.Hpot]
    | succ k => simp [SwarmOcc.Hpot]
  rw [he, he, ← sum_range_add_sum_Ico _ hab]
  ring

private theorem measurableSet_interval_potential_bound
    {p : ℝ} {m a b s : ℕ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hab : a ≤ b + 1) (j : Fin N) (D : ℝ) :
    MeasurableSet[enlFilt p m s] {U | ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j s ∧
      SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D} := by
  let := enlFilt (N := N) p m s
  let G : Set (Array N) := {U | ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j s}
  have hG : MeasurableSet G := measurableSet_le measurable_const (measurable_runMax_enl p m s j)
  have hsum : Measurable (fun U => ∑ z ∈ Finset.Ico a (b + 1), belowSeed p m s j z U) :=
    Finset.measurable_sum _ (fun z _ => measurable_belowSeed hp₀ m s j z)
  have heq : {U : Array N | ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j s ∧
      SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D} =
    G ∩ {U | (∑ z ∈ Finset.Ico a (b + 1), belowSeed p m s j z U) ≤ D} := by
    ext U
    refine and_congr_right (fun hU => ?_)
    rw [Hpot_nat_sub_eq_sum_Ico _ hab]
    have he : (∑ z ∈ Finset.Ico a (b + 1), belowSeed p m s j z U) =
        ∑ z ∈ Finset.Ico a (b + 1), envH p m j U z := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' : (z : ℤ) < ((b + 1 : ℕ) : ℤ) := by exact_mod_cast (Finset.mem_Ico.mp hz).2
      exact belowSeed_eq_hof m s j z (by rw [← runMax_eq_recVal]; exact hz'.trans_le hU)
    change _ ≤ D ↔ (∑ z ∈ Finset.Ico a (b + 1), belowSeed p m s j z U) ≤ D
    rw [he]
  exact heq ▸ hG.inter (measurableSet_le hsum measurable_const)

/-- Iterated exit-time bound at a fixed offset after a record. The potential
difference is evaluated below the other walker's already reached level. -/
theorem record_offset_interval_survival_prob_le
    [Nonempty (Fin N)] {p : ℝ} {m a b : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (hab : a ≤ b + 1) (r v k : ℕ) {n : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 2 * D ≤ (n : ℝ)) :
    (arrayMeasure N).real {U | U ∈ ReachAll p m ∧
      ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j (recTimeA p m U r + v) ∧
      SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D ∧
      U ∈ intervalSurvival p m i a b (recTimeA p m U r + v) (k * n)} ≤ (1 / 2 : ℝ) ^ k := by
  let μ := arrayMeasure N
  let A (s : ℕ) := ClockFibre.clockFibre (N := N) p m r s ∩ {U |
    ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j (s + v) ∧
    SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D}
  let E (s : ℕ) := A s ∩ intervalSurvival p m i a b (s + v) (k * n)
  have hA (s : ℕ) : MeasurableSet[enlFilt p m (s + v)] (A s) :=
    ((enlFilt p m).mono (Nat.le_add_right _ _) _ (ClockFibre.measurableSet_clockFibre p m r s)).inter
      (measurableSet_interval_potential_bound (s := s + v) hp₀.le hab j D)
  have hAm (s : ℕ) : MeasurableSet (A s) := (enlFilt p m).le _ _ (hA s)
  have hd : Pairwise (Disjoint on A) := fun s t h =>
    (ClockFibre.disjoint_clockFibre p m r s t h).mono inter_subset_left inter_subset_left
  have hprob (s : ℕ) : μ (E s) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * μ (A s) := by
    have h := interval_survival_prob_le_pow_half hp₀ hp₁ hm hij hn hD (hA s)
      (fun U hU => hU.2.1) (fun U hU => hU.2.2) k
    have h := ENNReal.ofReal_le_ofReal h
    rwa [ENNReal.ofReal_mul (by positivity), measureReal_def, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  have hcover : {U | U ∈ ReachAll p m ∧ ((b + 1 : ℕ) : ℤ) ≤ runMax p m U j (recTimeA p m U r + v) ∧
      SwarmOcc.Hpot (envH p m j U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m j U) (a : ℤ) ≤ D ∧
      U ∈ intervalSurvival p m i a b (recTimeA p m U r + v) (k * n)} ⊆ ⋃ s, E s := by
    rintro U ⟨hU, hmax, hspan, hsurv⟩
    obtain ⟨s, hS⟩ := mem_iUnion.mp (ClockFibre.reachAll_subset_iUnion_clockFibre p m r hU)
    rw [ClockFibre.recTimeA_eq_of_mem_clockFibre hU hS] at hmax hsurv
    exact mem_iUnion.mpr ⟨s, ⟨hS, hmax, hspan⟩, hsurv⟩
  have hsum : (∑' s, μ (A s)) ≤ 1 := by
    rw [← measure_iUnion hd hAm, ← measure_univ (μ := μ)]
    exact measure_mono (subset_univ _)
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc
    _ ≤ μ (⋃ s, E s) := measure_mono hcover
    _ ≤ ∑' s, μ (E s) := measure_iUnion_le E
    _ ≤ ∑' s, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * μ (A s) := ENNReal.tsum_le_tsum hprob
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * (∑' s, μ (A s)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * 1 := mul_le_mul_right hsum _
    _ = _ := mul_one _

end Swarming.Diameter
