import SwarmDiameter.RecordTrialConcentration
import Swarm.GammaStrictWindow
import Swarm.RecClockLocgroup

open Finset Set Filter MeasureTheory
open Swarming.Uniform Swarming.Enl SwarmRecordMeas.Actual
open Swarming.GammaStrict

namespace Swarming.Diameter

set_option autoImplicit false

attribute [local instance 10] Classical.propDecidable

/-- A deficit of successful trials in an integer subinterval of the
deterministic interval around the record level. -/
noncomputable def recordTrialBad (N : ℕ) (p : ℝ) (m : ℕ) (r : ℤ) (T L : ℕ) (ε : ℝ) :
    Set (Array N) :=
  ⋃ A ∈ (properGroups N).attach, ⋃ ab ∈ ambFamily r T L, {U |
    (((Finset.Icc ab.1 ab.2).filter
        (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card : ℝ)
      < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ) - ε * L}

theorem recordTrialBad_le_exp {N : ℕ} {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p < 1) (hm : 0 < m) (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real (recordTrialBad N p m (r : ℤ) T L ε) ≤ Real.exp (-c * (L : ℝ)) := by
  obtain ⟨c, hc, h⟩ := gamma_trial_concentration hp₀ hp₁ hm N T hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with L hL
  intro r hr
  exact hL (r : ℤ) (by exact_mod_cast hr)

/-- Successful trials on a separated record interval give distinct strict
times, with a count proportional to the increase of the leading record. -/
theorem record_strictTimes_lower {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m r T L : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r)
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    {A : Finset (Fin N)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {s t : ℕ} (hs : recTimeA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ recTimeA p m U r + T * L)
    (hsep : ∀ u ∈ Finset.Ico s t, SwarmJointDrift.SepSet p m u A Aᶜ U)
    {ε : ℝ} (hε : 0 ≤ ε) (htrial : U ∉ recordTrialBad N p m (r : ℤ) T L ε) :
    (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) -
      (ε * (L : ℝ) + 2 * (m : ℝ)) ≤ (strictTimes p m hA U s t).card := by
  let y := runMaxA p m U hA s + 1
  let z := runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)
  let q : ℝ := (1 - p) ^ ((2 * m - 1) * A.card)
  have hq : q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg (sub_nonneg.mpr hp₁.le) _, pow_le_one₀ (by linarith) (by linarith)⟩
  have hAp : A ∈ properGroups N := mem_properGroups.mpr ⟨hA, by
    intro h
    rw [h] at hAc
    simp at hAc⟩
  have hcount : q * ((z - y + 1).toNat : ℝ) - ε * (L : ℝ) ≤ (recWindowCount p m hA U s t : ℝ) := by
    by_cases hyz : y ≤ z
    · have hrec := RecClockLG.recHyp_at_record hU
      have hlo : (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hA (recTimeA p m U r) := by
        obtain ⟨i, hi⟩ := hA
        exact (hrec.1 i).trans (pos_le_runMaxA_pos hi)
      have hhi : runMaxA p m U hA (recTimeA p m U r) ≤ (r : ℤ) :=
        Finset.sup'_le _ _ (fun i _ => hrec.2 i)
      have hT := Nat.mul_le_mul_right L (show T ≤ T + 3 by omega)
      have hcast : ((T + 3) * L : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
      have hab : (y, z) ∈ ambFamily (r : ℤ) T L :=
        record_window_mem_ambFamily hL hs hst (by omega) hcast hlo hhi hyz
      have he : (z - y).toNat + 1 = (z - y + 1).toNat := by omega
      by_contra! hbad
      apply htrial
      refine Set.mem_biUnion (Finset.mem_attach _ ⟨A, hAp⟩) (Set.mem_biUnion hab ?_)
      change (recWindowCount p m hA U s t : ℝ) <
        q * ((z - y).toNat + 1 : ℝ) - ε * (L : ℝ)
      have he' : ((z - y).toNat + 1 : ℝ) = ((z - y + 1).toNat : ℝ) := by exact_mod_cast he
      rwa [he']
    · have he : (z - y + 1).toNat = 0 := by omega
      rw [he, Nat.cast_zero, mul_zero, zero_sub]
      exact (neg_nonpos.mpr (mul_nonneg hε (Nat.cast_nonneg _))).trans (Nat.cast_nonneg _)
  have hcard : (recWindowCount p m hA U s t : ℝ) ≤ (strictTimes p m hA U s t).card := by
    rw [← winFinishes_card_eq_recWindowCount p m hA U s t]
    exact_mod_cast Finset.card_le_card (winFinishes_subset_strictTimes hm hsep)
  have hdiff : ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) - 2 * (m : ℝ) ≤
      ((z - y + 1).toNat : ℝ) := by
    exact_mod_cast (show runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ) ≤
      ((z - y + 1).toNat : ℤ) by dsimp only [y, z]; omega)
  change q * ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) -
    (ε * (L : ℝ) + 2 * (m : ℝ)) ≤ _
  linarith only [hcount.trans hcard, mul_le_mul_of_nonneg_left hdiff hq.1,
    mul_le_mul_of_nonneg_left hq.2 (show 0 ≤ 2 * (m : ℝ) by positivity)]

end Swarming.Diameter
