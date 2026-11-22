import SwarmDiameter.TwoWalkerPassage
import SwarmDiameter.PathDiameter
import Swarm.ActualRecordGeometry
import Swarm.RestartRecord

open Finset Set Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRecordMeas.Actual SwarmRestart

set_option autoImplicit false

namespace Swarming.Diameter

private theorem pos_lt_before_record {p : ℝ} {m r u : ℕ} {U : Array 2} (hU : U ∈ ReachAll p m)
    (hu : u < recTimeA p m U r) (i : Fin 2) : (trajectory p m U u).pos i < (r : ℤ) :=
  (RecordDefect.le_runMax (X := RecordoSupply.actX p m U) (n := u) i).trans_lt
    ((M4RecordGeom.isRecord_recTimeA_of_reach hU r).1 u hu)

/-- Every individual running maximum is at most the swarm's record level
at its first attainment. -/
theorem individual_runMax_le_record {p : ℝ} {m r : ℕ} {U : Array 2} (hU : U ∈ ReachAll p m)
    (i : Fin 2) : runMax p m U i (recTimeA p m U r) ≤ (r : ℤ) := by
  obtain ⟨t, ht, he⟩ := exists_eq_runMax p m U i (recTimeA p m U r)
  rw [← he]
  rcases ht.eq_or_lt with rfl | hlt
  · exact M4RecordGeom.actX_le_level hU r i
  · exact (pos_lt_before_record hU hlt i).le

/-- On a record interval with no large martingale deviation, the second
walker reaches the record level while both positions and both running
maxima stay within the indicated bounds at the time of that visit. -/
theorem two_walker_meeting_of_no_deviations {p : ℝ} {m r L x K : ℕ} {U : Array 2}
    (hp : (1 : ℝ) / 2 ≤ p) (hm : 1 ≤ m) (hU : U ∈ ReachAll p m)
    (hx : 1 ≤ x) (hxL : x ≤ 2 * L) (hr : 4 * L ≤ r)
    (hdiam : pathDiameter (recTimeA p m U r) (posPath p m U) ≤ 2 * (L : ℝ))
    (hexit : ∀ i j : Fin 2, i ≠ j → (r : ℤ) ≤ runMax p m U i (recTimeA p m U r) →
      U ∉ intervalSurvival p m j (r - 4 * L) (r - 1) (recTimeA p m U r) K)
    (hmart : ∀ i : Fin 2, U ∉ StoppedWindow.stoppedWindow
      (fun t V => driftMartingale p m V t i) (fun V => recTimeA p m V r) K (x : ℝ)) :
    ∃ η : ℕ, recTimeA p m U r ≤ η ∧ η ≤ recTimeA p m U r + K ∧
      ∀ i : Fin 2, ((r - x : ℕ) : ℤ) ≤ (trajectory p m U η).pos i ∧
        (r : ℤ) ≤ runMax p m U i η ∧ runMax p m U i η ≤ (r : ℤ) + (x : ℤ) := by
  classical
  let σ := recTimeA p m U r
  let X (i : Fin 2) (t : ℕ) := (trajectory p m U t).pos i
  let M (i : Fin 2) (t : ℕ) := runMax p m U i t
  have hrp : 1 ≤ r := by omega
  have hrx : x ≤ r := by omega
  have hzero (i : Fin 2) : M i σ ≤ (r : ℤ) := individual_runMax_le_record hU i
  obtain ⟨i, hi⟩ := M4RecordGeom.exists_traj_eq_level hU r
  change X i σ = (r : ℤ) at hi
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card (Fin 2)) i
  have hij := hji.symm
  have htwo (a : Fin 2) : a = i ∨ a = j := by fin_cases i <;> fin_cases j <;> fin_cases a <;> simp_all
  have hdiff (a : Fin 2) {s t : ℕ} (hs : σ ≤ s) (hst : s ≤ t) (ht : t ≤ σ + K) :
      |driftMartingale p m U t a - driftMartingale p m U s a| < (x : ℝ) :=
    lt_of_not_ge (fun h => hmart a (ClockLocMove.mem_stoppedWindow_of_pair hs hst ht h))
  have hback (a : Fin 2) {t : ℕ} (ht : σ ≤ t) (htK : t ≤ σ + K) :
      (X a σ : ℝ) - (x : ℝ) < (X a t : ℝ) := by
    have hA : (excitedSteps p m U σ a : ℝ) ≤ (excitedSteps p m U t a : ℝ) := by
      exact_mod_cast M1DMart.monotone_excitedSteps p m U a ht
    have h := (abs_lt.mp (hdiff a le_rfl ht htK)).1
    unfold driftMartingale at h
    have hprod := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 * p - 1 by linarith)
    change -(x : ℝ) < (X a t : ℝ) - _ - ((X a σ : ℝ) - _) at h
    linarith only [h, hprod]
  have hMi : M i σ = (r : ℤ) :=
    (hzero i).antisymm (hi.ge.trans (le_runMax p m U i σ))
  have hcast : ((r - x : ℕ) : ℤ) = (r : ℤ) - (x : ℤ) := Nat.cast_sub hrx
  by_cases hj : X j σ = (r : ℤ)
  · refine ⟨σ, le_rfl, Nat.le_add_right _ _, fun a => ?_⟩
    have ha : X a σ = (r : ℤ) := (htwo a).elim (fun h => h.symm ▸ hi) (fun h => h.symm ▸ hj)
    have hM : (r : ℤ) ≤ M a σ := ha.ge.trans (le_runMax p m U a σ)
    change ((r - x : ℕ) : ℤ) ≤ X a σ ∧ (r : ℤ) ≤ M a σ ∧ M a σ ≤ (r : ℤ) + (x : ℤ)
    rw [ha, hcast]
    exact ⟨by omega, hM, (hzero a).trans (by omega)⟩
  have hstartJ : (r : ℤ) - 2 * (L : ℤ) ≤ X j σ := by
    have h := (sub_le_pathDiameter σ (posPath p m U) i j).trans hdiam
    change ((X i σ - X j σ : ℤ) : ℝ) ≤ 2 * (L : ℝ) at h
    rw [hi] at h
    have hi' : ((r : ℤ) - X j σ : ℤ) ≤ 2 * (L : ℤ) := by exact_mod_cast h
    omega
  have hex : ∃ u : ℕ, σ ≤ u ∧ u ≤ σ + K ∧ (r : ℤ) ≤ X j u := by
    by_contra! h
    apply hexit i j hij hMi.ge
    apply mem_intervalSurvival_iff.mpr
    intro u hu huK
    rw [Nat.sub_add_cancel hrp, Nat.cast_sub hr]
    push_cast
    refine ⟨?_, h u hu huK⟩
    have hback' := hback j hu huK
    have hstartJr : (r : ℝ) - 2 * (L : ℝ) ≤ (X j σ : ℝ) := by exact_mod_cast hstartJ
    have hxLr : (x : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hxL
    exact_mod_cast (show (r : ℝ) - 4 * (L : ℝ) < (X j u : ℝ) by linarith only [hback', hstartJr, hxLr])
  let η := Nat.find hex
  have hη : σ ≤ η ∧ η ≤ σ + K ∧ (r : ℤ) ≤ X j η := Nat.find_spec hex
  have hση : σ < η := lt_of_le_of_ne hη.1 (fun h => hj (le_antisymm
    ((le_runMax p m U j σ).trans (hzero j)) (h ▸ hη.2.2)))
  have hj_before (u : ℕ) (hu : u < η) : X j u < (r : ℤ) := by
    by_cases hus : σ ≤ u
    · exact lt_of_not_ge (fun hh => Nat.find_min hex hu ⟨hus, hu.le.trans hη.2.1, hh⟩)
    · exact pos_lt_before_record hU (lt_of_not_ge hus) j
  have hj_eta : X j η = (r : ℤ) := by
    have hb := hj_before (η - 1) (by omega)
    have hsuc : η - 1 + 1 = η := by omega
    rcases pos_succ_eq_add_one_or_sub_one p m U j (η - 1) with hh | hh
    · change X j (η - 1 + 1) = X j (η - 1) + 1 at hh
      rw [hsuc] at hh
      exact le_antisymm (by omega) hη.2.2
    · change X j (η - 1 + 1) + 1 = X j (η - 1) at hh
      rw [hsuc] at hh
      exact le_antisymm (by omega) hη.2.2
  have hjM : M j η = (r : ℤ) := by
    obtain ⟨u, hu, he⟩ := exists_eq_runMax p m U j η
    change X j u = M j η at he
    have hle := hj_eta.ge.trans (le_runMax p m U j η)
    change (r : ℤ) ≤ M j η at hle
    rcases hu.eq_or_lt with rfl | hlt
    · exact he.symm.trans hj_eta
    · exact False.elim ((not_lt_of_ge (he ▸ hle)) (hj_before u hlt))
  have hiM : M i η ≤ (r : ℤ) + (x : ℤ) := by
    by_contra! hbig
    obtain ⟨u, hu, he⟩ := exists_eq_runMax p m U i η
    change X i u = M i η at he
    have hs : σ ≤ u := by
      by_contra! h
      have := pos_lt_before_record hU h i
      change X i u < (r : ℤ) at this
      omega
    have hb : (r : ℤ) < X i u := by omega
    obtain ⟨s, hss, hsu, hlevel, hfront⟩ := exists_start_of_front_excursion hs hi.le hb
    have hc : ∀ v : ℕ, s ≤ v → v < u → (r : ℤ) ≤ X i v ∧ M j v < (r : ℤ) := by
      intro v hvs hvu
      obtain ⟨w, hw, hew⟩ := exists_eq_runMax p m U j v
      change X j w = M j v at hew
      exact ⟨hfront v hvs hvu.le, hew ▸ hj_before w (hw.trans_lt (hvu.trans_le hu))⟩
    have hmartEq := two_walker_front_displacement_eq_martingale hm hij hsu hc
    have hlt := (abs_lt.mp (hdiff i hss hsu (hu.trans hη.2.1))).2
    have hsr : (X i s : ℝ) = (r : ℝ) := by exact_mod_cast hlevel
    have hlr : (r : ℝ) + (x : ℝ) < (X i u : ℝ) := by exact_mod_cast (he.symm ▸ hbig)
    change (X i u : ℝ) - (X i s : ℝ) = _ at hmartEq
    linarith only [hmartEq, hlt, hsr, hlr]
  refine ⟨η, hη.1, hη.2.1, fun a => ?_⟩
  rcases htwo a with ha | ha
  · subst a
    have h := hback i hη.1 hη.2.1
    rw [hi] at h
    have hf : (r : ℤ) - (x : ℤ) ≤ X i η := by
      exact_mod_cast (show (r : ℝ) - (x : ℝ) ≤ (X i η : ℝ) by exact h.le)
    exact ⟨hcast.le.trans hf, hMi.ge.trans (runMax_mono p m U i hη.1), hiM⟩
  · subst a
    change ((r - x : ℕ) : ℤ) ≤ X j η ∧ (r : ℤ) ≤ M j η ∧ M j η ≤ (r : ℤ) + (x : ℤ)
    rw [hj_eta, hjM, hcast]
    omega

end Swarming.Diameter
