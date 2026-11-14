/-
  **`(Smom₄)` step 2: off the bad-run event the static maximum is `O(L)`.**

  This file combines the deterministic tail bound of `Smom4Run.lean` with the run bound for the
  potential (`SwarmMpot.hfix_le_of_no_long_run`) and the bad-run event of
  `SwarmMpot.BadRun` (`MpotMoment.lean`), and records the two elementary bounds on
  `1 + staticMax` used by the moment integration in `Smom4Main.lean`:

  * `one_add_staticMax_le_of_notMem_badRun`: on the complement of `BadRun p m I n L` (some row of
    `I` has `L` consecutive unmarked sites among the sites `0,…,n+1`), for every `U`,
    `1 + staticMax p m n I hI U ≤ A p · (1 + L)` with `A p = 5·p/(2p-1) + 2`;
  * `one_add_staticMax_le_crude`: the a-priori bound `1 + staticMax ≤ 4(n+2) + 5`;
  * measurability and integrability of `(1 + staticMax)^4`.

  Everything is for the actual `arrayMeasure N` objects; no hypothesis on the law of the array is
  used here beyond the definitions.
-/
import Swarm.Smom4Run

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmSmom4

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance SwarmJointDrift SwarmSiteDiff SwarmMpot

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. The ratio sequence of the mark weight is `{1, (1-p)/p}`-valued -/

theorem rq_omegaN_nonneg (hp : 1 / 2 < p) (hp1 : p < 1) (U : Array N) (i : Fin N) (u : ℕ) :
    0 ≤ rq (omegaN p m U i) u :=
  rq_nonneg (omegaAt_pos p m U hp.le i (u : ℤ)) (omegaAt_le_one p m U hp1.le i (u : ℤ))

theorem rq_omegaN_le_one (hp : 1 / 2 < p) (hp1 : p ≤ 1) (U : Array N) (i : Fin N) (u : ℕ) :
    rq (omegaN p m U i) u ≤ 1 :=
  rq_le_one (omegaAt_pos p m U hp.le i (u : ℤ)) (one_half_le_omegaAt p m U hp.le i (u : ℤ))

theorem rq_omegaN_val {U : Array N} {i : Fin N} (u : ℕ) :
    rq (omegaN p m U i) u = 1 ∨ rq (omegaN p m U i) u = (1 - p) / p := by
  rcases omegaN_eq_half_or (p := p) (m := m) U i u with h | h
  · exact Or.inr (rq_eq_of_p h)
  · exact Or.inl (rq_eq_one_of_half h)

/-! ### 2. No long unmarked run implies a linear bound on the truncated tail `G_i` -/

theorem Gtail_le_of_no_long_run (hp : 1 / 2 < p) (hp1 : p < 1) {U : Array N} {i : Fin N}
    {n L : ℕ} (hL : 1 ≤ L) (h : NoLongRun p m U i (n + 1) L) {x : ℕ} (hx : x < n + 2) :
    Gtail p m U i x (n + 2) ≤ 1 + (L : ℝ) * Kp p := by
  have hwin : ∀ a, a + L ≤ n + 2 → ∃ j, j < L ∧ rq (omegaN p m U i) (a + j) = (1 - p) / p := by
    intro a ha
    obtain ⟨j, hj, hs⟩ := h a ha
    exact ⟨j, hj, rq_eq_of_p ((omegaN_eq_p_iff hp U i (a + j)).mpr hs)⟩
  have hGS : GS (rq (omegaN p m U i)) x (n + 2) ≤ (L : ℝ) * Kp p :=
    GS_le_of_no_long_run hp hp1.le (rq_omegaN_nonneg hp hp1 U i) (rq_omegaN_le_one hp hp1.le U i)
      (rq_omegaN_val (p := p) (m := m) (U := U) (i := i)) hL hwin x
  rw [Gtail_eq_one_add_GS]
  linarith

/-! ### 3. The constant and the bound off `BadRun` -/

/-- `A p = 5·p/(2p-1) + 2`. -/
noncomputable def Astat (p : ℝ) : ℝ := 5 * Kp p + 2

theorem Astat_pos {p : ℝ} (hp : 1 / 2 < p) : 0 < Astat p := by
  have h := Kp_pos hp
  unfold Astat
  linarith

theorem Astat_ge_one {p : ℝ} (hp : 1 / 2 < p) : 1 ≤ Astat p := by
  have h := Kp_pos hp
  unfold Astat
  nlinarith

theorem two_p_div_le {p : ℝ} (hp : 1 / 2 < p) :
    2 * p / (2 * p - 1) = 2 * Kp p := by
  unfold Kp
  ring

/-- **Off `BadRun`**: `1 + staticMax ≤ A p · (1 + L)`. -/
theorem one_add_staticMax_le_of_notMem_badRun (hp : 1 / 2 < p) (hp1 : p < 1)
    {U : Array N} {n L : ℕ} (I : Finset (Fin N)) (hI : I.Nonempty) (hL : 1 ≤ L)
    (h : U ∉ BadRun p m I n L) :
    1 + staticMax p m n I hI U ≤ Astat p * (1 + (L : ℝ)) := by
  have hp' : 1 / 2 ≤ p := hp.le
  have hKp := Kp_pos hp
  have hKp1 := one_le_Kp hp hp1.le
  -- each summand of the static maximum
  have hterm : ∀ i ∈ I, ∀ x, x < n + 2 →
      hfix (omegaN p m U i) x + Gtail p m U i x (n + 2) ≤ (5 * Kp p + 1) * (1 + (L : ℝ)) := by
    intro i hi x hx
    have hh : hfix (omegaN p m U i) x
        ≤ (2 * p / (2 * p - 1)) * (1 + (L : ℝ)) :=
      le_trans (le_windowMax (p := p) (m := m) (n := n) (i := i) (U := U) hx)
        (windowMax_le_of_noLongRun hp hp1.le hL (notMem_badRun_imp h hi hL))
    have hG : Gtail p m U i x (n + 2) ≤ 1 + (L : ℝ) * Kp p :=
      Gtail_le_of_no_long_run hp hp1 hL (notMem_badRun_imp h hi hL) hx
    rw [two_p_div_le hp] at hh
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith
  have hsup : staticMax p m n I hI U ≤ (5 * Kp p + 1) * (1 + (L : ℝ)) := by
    unfold staticMax Swarming.Group.maximumOn
    refine Finset.sup'_le hI (fun i => (Finset.range (n + 2)).sup'
      ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2))) fun i hi => ?_
    refine Finset.sup'_le _ _ fun x hx => hterm i hi x (Finset.mem_range.mp hx)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h5 : (5 * Kp p + 1) * (1 + (L : ℝ)) + 1
      ≤ (5 * Kp p + 2) * (1 + (L : ℝ)) := by nlinarith
  unfold Astat
  nlinarith [hsup, h5]

/-! ### 4. The a-priori bound -/

/-- The pointwise a-priori bound `1 + staticMax ≤ 4(n+2) + 5`. -/
theorem one_add_staticMax_le_crude {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) (U : Array N) :
    1 + staticMax p m n I hI U ≤ 4 * ((n : ℝ) + 2) + 5 := by
  have h1 := staticMax_le (p := p) hp hp1 (m := m) (n := n) (hI := hI) U
  have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h1
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem one_le_staticMax' {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) (U : Array N) :
    1 ≤ staticMax p m n I hI U :=
  one_le_staticMax hp hp1 hI U

/-! ### 5. Measurability and integrability of `(1 + staticMax)^4` -/

theorem measurable_staticMax_add_one (p : ℝ) (m n : ℕ) (I : Finset (Fin N)) (hI : I.Nonempty) :
    Measurable fun U : Array N => 1 + staticMax p m n I hI U :=
  measurable_const.add (measurable_staticMax p m n I hI)

theorem integrable_staticMax_fourth {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) :
    Integrable (fun U : Array N => (1 + staticMax p m n I hI U) ^ 4) (arrayMeasure N) := by
  have hbound : ∀ U, |(1 + staticMax p m n I hI U) ^ 2| ≤ (4 * ((n : ℝ) + 2) + 5) ^ 2 := by
    intro U
    have h1 := one_add_staticMax_le_crude hp hp1 (m := m) (n := n) (hI := hI) U
    have h2 := one_le_staticMax' hp hp1 (m := m) (n := n) (hI := hI) U
    have h0 : (0 : ℝ) ≤ 1 + staticMax p m n I hI U := by linarith
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 (by linarith) 2
  have hm2 : AEStronglyMeasurable (fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
      (arrayMeasure N) := by
    have hfun : (fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
        = (fun U : Array N => 1 + staticMax p m n I hI U)
          * (fun U : Array N => 1 + staticMax p m n I hI U) := by
      funext U
      rw [Pi.mul_apply, pow_two]
    rw [hfun]
    exact ((measurable_staticMax_add_one p m n I hI).mul
      (measurable_staticMax_add_one p m n I hI)).aestronglyMeasurable
  have h := integrable_sq_of_abs_bound (f := fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
    hm2 (by positivity) hbound
  refine h.congr (Eventually.of_forall fun U => ?_)
  show ((1 + staticMax p m n I hI U) ^ 2) ^ 2 = (1 + staticMax p m n I hI U) ^ 4
  ring

end SwarmSmom4
