import SwarmDiameter.RecordExitTime
import SwarmDiameter.RecordMartingaleAtOffset
import Swarm.MartClauseActual

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmRecordMeas.Actual

set_option autoImplicit false

namespace Swarming.Diameter

/-- A nearest-neighbour passage from below a level to above it has a last
visit to the level before the final time. -/
theorem exists_start_of_front_excursion {p : ℝ} {m : ℕ} {U : Array 2} {i : Fin 2} {q t : ℕ}
    {h : ℤ} (hqt : q ≤ t) (hq : (trajectory p m U q).pos i ≤ h)
    (ht : h < (trajectory p m U t).pos i) :
    ∃ s : ℕ, q ≤ s ∧ s ≤ t ∧ (trajectory p m U s).pos i = h ∧
      ∀ u : ℕ, s ≤ u → u ≤ t → h ≤ (trajectory p m U u).pos i := by
  classical
  let X (s : ℕ) := (trajectory p m U s).pos i
  let A := (Finset.Icc q t).filter (fun s => X s ≤ h)
  have hA : A.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hqt⟩, hq⟩⟩
  let s := A.max' hA
  obtain ⟨hs, hXs⟩ := Finset.mem_filter.mp (A.max'_mem hA)
  obtain ⟨hqs, hst⟩ := Finset.mem_Icc.mp hs
  change q ≤ s at hqs
  change s ≤ t at hst
  change X s ≤ h at hXs
  change h < X t at ht
  have hst' : s < t := lt_of_le_of_ne hst fun he => by rw [he] at hXs; omega
  have hafter (u : ℕ) (hsu : s < u) (hut : u ≤ t) : h < X u := by
    by_contra! hh
    have hmem : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqs.trans hsu.le, hut⟩, hh⟩
    exact (not_le_of_gt hsu) (Finset.le_max' A u hmem)
  have he : X s = h := by
    have hnext := hafter (s + 1) (by omega) (by omega)
    rcases pos_succ_eq_add_one_or_sub_one p m U i s with hjump | hjump
    · change X (s + 1) = X s + 1 at hjump
      omega
    · change X (s + 1) + 1 = X s at hjump
      omega
  refine ⟨s, hqs, hst, he, ?_⟩
  intro u hsu hut
  rcases hsu.eq_or_lt with rfl | hsu
  · exact he.ge
  · exact (hafter u hsu hut).le

/-- The leading walker reaches a higher level while the other walker stays
inside \((a,b+1)\) below the leader's original running maximum \(b+1\). -/
def frontReachesBeforeExit (p : ℝ) (m r v a b : ℕ) (i j : Fin 2) (x : ℝ) : Set (Array 2) :=
  {U | U ∈ ReachAll p m ∧
    let q := recTimeA p m U r + v
    let h : ℤ := ((b + 1 : ℕ) : ℤ)
    (trajectory p m U q).pos i ≤ h ∧ h ≤ runMax p m U i q ∧ runMax p m U j q < h ∧
    ∃ t ≥ q, (h : ℝ) + x ≤ ((trajectory p m U t).pos i : ℝ) ∧
      U ∈ intervalSurvival p m j a b q (t - q)}

/-- The probability of reaching the higher level before the trailing walker
exits is bounded by the survival probability and the excursion deviation. -/
theorem two_walker_passage_order_prob_le {p : ℝ} {m a b : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) {i j : Fin 2} (hij : i ≠ j) (hab : a ≤ b + 1) (r v k : ℕ) {n : ℕ}
    (hn : 0 < n) (hk : 0 < k) {D x : ℝ} (hD : 2 * D ≤ (n : ℝ)) (hx : 0 < x) :
    (arrayMeasure 2).real (frontReachesBeforeExit p m r v a b i j x ∩ {U |
      SwarmOcc.Hpot (envH p m i U) ((b + 1 : ℕ) : ℤ) - SwarmOcc.Hpot (envH p m i U) (a : ℤ) ≤ D}) ≤
      (1 / 2 : ℝ) ^ k + 2 * (((k * n : ℕ) : ℝ) + 1) ^ 2 *
        Real.exp (-(x ^ 2) / (16 * ((k * n : ℕ) : ℝ))) := by
  let μ := arrayMeasure 2
  let q (U : Array 2) := recTimeA p m U r + v
  let h : ℤ := ((b + 1 : ℕ) : ℤ)
  let K := k * n
  let E : Set (Array 2) := {U | U ∈ ReachAll p m ∧ h ≤ runMax p m U i (q U) ∧
    SwarmOcc.Hpot (envH p m i U) h - SwarmOcc.Hpot (envH p m i U) (a : ℤ) ≤ D ∧
      U ∈ intervalSurvival p m j a b (q U) K}
  let F : Set (Array 2) := {U | U ∈ ReachAll p m ∧ ∃ (h : ℤ) (s t : ℕ),
    q U ≤ s ∧ s ≤ t ∧ t ≤ q U + K ∧ (trajectory p m U s).pos i = h ∧
      (h : ℝ) + x ≤ ((trajectory p m U t).pos i : ℝ) ∧
      (∀ u : ℕ, s ≤ u → u < t → h ≤ (trajectory p m U u).pos i ∧ runMax p m U j u < h)}
  have hsub : frontReachesBeforeExit p m r v a b i j x ∩ {U |
      SwarmOcc.Hpot (envH p m i U) h - SwarmOcc.Hpot (envH p m i U) (a : ℤ) ≤ D} ⊆ E ∪ F := by
    rintro U ⟨⟨hU, hs, hMi, hMj, t, ht, hpos, hsurv⟩, hspan⟩
    have hi := mem_intervalSurvival_iff.mp hsurv
    by_cases htime : t ≤ q U + K
    · apply Or.inr
      have hpos' : h < (trajectory p m U t).pos i := by
        exact_mod_cast (show (h : ℝ) < ((trajectory p m U t).pos i : ℝ) by linarith only [hpos, hx])
      obtain ⟨s, hqs, hst, he, ha⟩ := exists_start_of_front_excursion ht hs hpos'
      refine ⟨hU, h, s, t, hqs, hst, htime, he, hpos, ?_⟩
      intro u hsu hut
      refine ⟨ha u hsu hut.le, ?_⟩
      obtain ⟨w, hwu, hw⟩ := exists_eq_runMax p m U j u
      rw [← hw]
      by_cases hwq : q U ≤ w
      · exact (hi w hwq (by omega)).2
      · exact ((le_runMax p m U j w).trans
          (runMax_mono p m U j (le_of_lt (lt_of_not_ge hwq)))).trans_lt hMj
    · apply Or.inl
      exact ⟨hU, hMi, hspan, mem_intervalSurvival_iff.mpr (fun u hu hu' => hi u hu (by omega))⟩
  have hK : 1 ≤ K := Nat.mul_pos hk hn
  have he : μ.real E ≤ (1 / 2 : ℝ) ^ k :=
    record_offset_interval_survival_prob_le hp₀ hp₁ hm hij.symm hab r v k hn hD
  have hf := two_walker_front_excursion_prob_le hp₀ hp₁ (by omega : 1 ≤ m) hij r v hK hx
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le E F).trans (add_le_add he hf))

/-- A leftward displacement of size at least \(x\) is bounded by a negative
trajectory martingale deviation, since the excitation count is nondecreasing. -/
theorem record_offset_backward_displacement_prob_le
    {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (i : Fin N) (r v : ℕ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (arrayMeasure N).real {U | U ∈ ReachAll p m ∧ ∃ s t : ℕ,
      recTimeA p m U r + v ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + v + n ∧
        x ≤ ((trajectory p m U s).pos i : ℝ) - ((trajectory p m U t).pos i : ℝ)} ≤
      2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(x ^ 2) / (16 * (n : ℝ))) := by
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (record_offset_martingale_window_prob_le (m := m) hp₀ hp₁ i r v hn hx)
  rintro U ⟨hU, s, t, hs, hst, ht, hd⟩
  have hA : (excitedSteps p m U s i : ℝ) ≤ (excitedSteps p m U t i : ℝ) := by
    exact_mod_cast M1DMart.monotone_excitedSteps p m U i hst
  have hp : 0 ≤ 2 * p - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hA hp
  refine ⟨hU, ClockLocMove.mem_stoppedWindow_of_pair hs hst ht ?_⟩
  have h : x ≤ -(driftMartingale p m U t i - driftMartingale p m U s i) := by
    unfold driftMartingale
    linarith only [hd, hprod]
  exact h.trans (neg_le_abs _)

end Swarming.Diameter
