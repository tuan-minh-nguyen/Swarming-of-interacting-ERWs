import Swarm.RecordClockLocal
import Swarm.ClockLocMove

open Filter Finset MeasureTheory Set
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRecordMeas.Actual

set_option autoImplicit false

namespace Swarming.Diameter

/-- Two-endpoint deviations of the trajectory martingale on an interval
starting at the record time plus a fixed offset. -/
theorem record_offset_martingale_window_prob_le
    {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (i : Fin N) (r v : ℕ) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real (ReachAll p m ∩ StoppedWindow.stoppedWindow
      (fun t U => driftMartingale p m U t i) (fun U => recTimeA p m U r + v) n ε) ≤
        2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(ε ^ 2) / (16 * (n : ℝ))) := by
  let B (t : ℕ) : Set (Array N) :=
    if v ≤ t then ClockFibre.clockFibre (N := N) p m r (t - v) else ∅
  have hB (t : ℕ) : MeasurableSet[enlFilt p m t] (B t) := by
    by_cases h : v ≤ t
    · rw [show B t = ClockFibre.clockFibre p m r (t - v) by simp only [B, if_pos h]]
      exact (enlFilt p m).mono (Nat.sub_le t v) _ (ClockFibre.measurableSet_clockFibre p m r (t - v))
    · simp only [B, if_neg h, MeasurableSet.empty]
  have hBd (t u : ℕ) (hne : t ≠ u) : Disjoint (B t) (B u) := by
    by_cases ht : v ≤ t <;> by_cases hu : v ≤ u
    · simpa only [B, if_pos ht, if_pos hu] using
        ClockFibre.disjoint_clockFibre (N := N) p m r (t - v) (u - v) (by omega)
    · simp only [B, if_neg hu, disjoint_empty]
    · simp only [B, if_neg ht, empty_disjoint]
    · simp only [B, if_neg ht, if_neg hu, disjoint_empty]
  have hcover : ReachAll p m ⊆ ⋃ t, B t := by
    intro U hU
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (ClockFibre.reachAll_subset_iUnion_clockFibre p m r hU)
    refine Set.mem_iUnion.mpr ⟨t + v, ?_⟩
    simpa only [B, if_pos (Nat.le_add_left v t), Nat.add_sub_cancel] using ht
  have htime (t : ℕ) : ReachAll p m ∩ B t ⊆ {U | recTimeA p m U r + v = t} := by
    rintro U ⟨hU, ht⟩
    by_cases h : v ≤ t
    · simp only [B, if_pos h] at ht
      rw [Set.mem_ofPred_eq, ClockFibre.recTimeA_eq_of_mem_clockFibre hU ht, Nat.sub_add_cancel h]
    · simp only [B, if_neg h, Set.mem_empty_iff_false] at ht
  have h := StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := arrayMeasure N) (ℱ := enlFilt p m) (Q := fun t U => driftMartingale p m U t i)
    (σ := fun U => recTimeA p m U r + v) (B := B) (G := ReachAll p m)
    (fun t => RecordClock.stronglyMeasurable_driftMartingale p m t i)
    (fun t => RecordClock.integrable_driftMartingale hp₀ hp₁ m t i)
    (fun t => RecordClock.condExp_increments_driftMartingale hp₀ hp₁ m t i)
    (by norm_num : (0 : ℝ) < 2)
    (fun t U => RecordClock.abs_increment_driftMartingale hp₀ hp₁ m t i U)
    hB hBd hcover htime hn hε
  rwa [show (4 : ℝ) * (n : ℝ) * 2 ^ 2 = 16 * (n : ℝ) by ring] at h

private theorem currentExcited_eq_zero_of_runMax_lt {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {U : Array 2}
    {i j : Fin 2} (hij : i ≠ j) {t : ℕ}
    (h : runMax p m U j t < (trajectory p m U t).pos i) :
    currentExcited m (U := U) (p := p) t i = 0 := by
  classical
  let x := (trajectory p m U t).pos i
  have hell : (trajectory p m U t).ell j x = 0 := by
    rw [ell_eq_localTime]
    apply localTime_eq_zero_of_ne
    intro s hs
    exact ne_of_lt (((le_runMax p m U j s).trans (runMax_mono p m U j hs)).trans_lt h)
  have htwo (k : Fin 2) : k = i ∨ k = j := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hv : otherVisits (trajectory p m U t).ell i x = 0 := by
    unfold otherVisits
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · simp only [if_pos hk]
    · have hk' := (htwo k).resolve_left hk
      rw [if_neg hk, hk', hell]
  have he : ¬ Excited m (trajectory p m U t).ell i x := by
    rw [Excited, hv]
    omega
  exact if_neg he

/-- Before the other walker has reached a level, an excursion above that
level has no excited steps. Its displacement equals the martingale increment. -/
theorem two_walker_front_displacement_eq_martingale {p : ℝ} {m : ℕ} (hm : 1 ≤ m)
    {U : Array 2} {i j : Fin 2} (hij : i ≠ j) {s t : ℕ} (hst : s ≤ t) {h : ℤ}
    (hfront : ∀ u : ℕ, s ≤ u → u < t → h ≤ (trajectory p m U u).pos i ∧ runMax p m U j u < h) :
    (trajectory p m U t).pos i - ((trajectory p m U s).pos i : ℝ) =
      driftMartingale p m U t i - driftMartingale p m U s i := by
  have he (u : ℕ) (hs : s ≤ u) (ht : u < t) : currentExcited m (U := U) (p := p) u i = 0 :=
    currentExcited_eq_zero_of_runMax_lt hm hij ((hfront u hs ht).2.trans_le (hfront u hs ht).1)
  have hA : excitedSteps p m U t i = excitedSteps p m U s i := by
    unfold excitedSteps
    rw [← sum_range_add_sum_Ico _ hst]
    have hsum : ∑ u ∈ Ico s t, currentExcited m (U := U) (p := p) u i = 0 :=
      Finset.sum_eq_zero (fun u hu => he u (mem_Ico.mp hu).1 (mem_Ico.mp hu).2)
    rw [hsum, add_zero]
  simp only [driftMartingale, hA]
  ring

/-- The positive excursion probability used before the second walker reaches
the level of the first. The level can be chosen from the path. -/
theorem two_walker_front_excursion_prob_le {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 1 ≤ m) {i j : Fin 2} (hij : i ≠ j) (r v : ℕ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (arrayMeasure 2).real {U | U ∈ ReachAll p m ∧ ∃ (h : ℤ) (s t : ℕ),
      recTimeA p m U r + v ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + v + n ∧
      (trajectory p m U s).pos i = h ∧ (h : ℝ) + x ≤ ((trajectory p m U t).pos i : ℝ) ∧
      (∀ u : ℕ, s ≤ u → u < t → h ≤ (trajectory p m U u).pos i ∧ runMax p m U j u < h)} ≤
        2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(x ^ 2) / (16 * (n : ℝ))) := by
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (record_offset_martingale_window_prob_le (m := m) hp₀ hp₁ i r v hn hx)
  rintro U ⟨hU, h, s, t, hs, hst, ht, hX, hdist, hfront⟩
  refine ⟨hU, ClockLocMove.mem_stoppedWindow_of_pair hs hst ht ?_⟩
  have hd := two_walker_front_displacement_eq_martingale hm hij hst hfront
  have hXr : ((trajectory p m U s).pos i : ℝ) = (h : ℝ) := by exact_mod_cast hX
  exact (show x ≤ driftMartingale p m U t i - driftMartingale p m U s i by
    linarith only [hd, hdist, hXr]).trans (le_abs_self _)

end Swarming.Diameter
