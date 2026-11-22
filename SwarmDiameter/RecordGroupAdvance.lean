import SwarmDiameter.RecordGroupDrift
import SwarmDiameter.RecordTrialConcentration
import Swarm.GammaStrictWindow
import Swarm.LocMoveH

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl
open SwarmRecordMeas.Actual SepGroup.Model SwarmJointDrift Swarming.GammaStrict
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

attribute [local instance 10] Classical.propDecidable

private theorem sum_group_drift_le_of_trial_counts
    {N : ℕ} {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) {U : Array N} {s t : ℕ}
    (hsep : ∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U)
    {e : ℝ}
    (hcnt : (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
      - e ≤ (recWindowCount p m hA U s t : ℝ)) :
    ∑ u ∈ Finset.Ico s t, Cavg p m u A Aᶜ U
      ≤ -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / (A.card : ℝ)) *
          ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
        + (2 * p - 1) / (A.card : ℝ) * (2 * (m : ℝ) + e) := by
  let S := strictTimes p m hA U s t
  have hcard : (recWindowCount p m hA U s t : ℝ) ≤ (S.card : ℝ) := by
    rw [← winFinishes_card_eq_recWindowCount p m hA U s t]
    exact_mod_cast Finset.card_le_card (winFinishes_subset_strictTimes hm hsep)
  have hb (u : ℕ) (hu : u ∈ S) : Cavg p m u A Aᶜ U ≤ -(2 * p - 1) / (A.card : ℝ) := by
    obtain ⟨hut, hstr⟩ := mem_strictTimes_iff.mp hu
    obtain ⟨i, hi, hα, hw⟩ := exists_leader_of_mem_StrictAt hm hstr
    exact cavg_le_neg_card hp₀.le hp₁.le m u U A Aᶜ hA hi hα
      (by simpa only [compl_compl] using hw)
      (fun _ hj => corr_nonpos_of_sep hp₀.le hp₁.le disjoint_compl_right (hsep u hut) hj)
  have hq : (1 - p) ^ ((2 * m - 1) * A.card) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg (sub_nonneg.mpr hp₁.le) _, pow_le_one₀ (by linarith) (by linarith)⟩
  have hcast : (((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℕ) : ℤ)
      ≥ runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ) :=
    by omega
  have hR := (show (((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℕ) : ℝ)
      ≥ ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) - 2 * (m : ℝ) by
    exact_mod_cast hcast)
  apply LocMove.sum_Ico_le_gamma_rate hp₀ hp₁ m A hA (strictTimes_subset U s t) hb
    (fun u hu _ => cavg_nonpos hp₀.le hp₁.le m u U A Aᶜ hA disjoint_compl_right (hsep u hu))
  have h₁ := mul_le_mul_of_nonneg_left hR hq.1
  have h₂ := mul_le_mul_of_nonneg_left hq.2 (show 0 ≤ 2 * (m : ℝ) by positivity)
  linarith [hcnt.trans hcard]

/-- On separated intervals, trials at successive record levels produce
a negative term proportional to the advance of the leading group's record.
The additive error is `ε * L`, with exceptional probability at most
`exp (-c * L ^ (1 / 3))`. -/
theorem record_group_advance_drift_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
            (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
            -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / (A.card : ℝ)) *
              ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) + ε * (L : ℝ) <
              WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨a, ha, htrials⟩ := gamma_trial_concentration hp₀.le hp₁ (by omega : 0 < m)
    N T (show 0 < ε / 4 by positivity)
  obtain ⟨b, hb, hdrift⟩ := record_group_drift_failure_le_cube_root hp₀ hp₁ hm N T hT (half_pos hε)
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let c := min a b / 2
  have hc : 0 < c := half_pos (lt_min ha hb)
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hlarge := (Real.tendsto_exp_atTop.comp (htop.const_mul_atTop hc)).eventually_ge_atTop 2
  have hlargeL := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (8 * (m : ℝ) / ε)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), htrials, hdrift, hlarge, hlargeL] with L hL htr hdr hbig hLbig
  intro r hr A hA hAc
  let μ := arrayMeasure N
  let B : Set (Array N) := ⋃ A ∈ (properGroups N).attach, ⋃ ab ∈ ambFamily r T L, {U : Array N |
    (((Finset.Icc ab.1 ab.2).filter
      (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card : ℝ)
      < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ) - (ε / 4) * L}
  let E : Set (Array N) := RecClockLG.recordCarrier p m r L ∩ {U |
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
      ε / 2 * (L : ℝ) < WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc -
        ∑ u ∈ Finset.Ico s t, Cavg p m u A Aᶜ U}
  have hcast : ((T + 3) * L : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hB : μ.real B ≤ Real.exp (-a * (L : ℝ)) := htr r hcast
  have hE : μ.real E ≤ Real.exp (-b * R L) := hdr r hr A Aᶜ hA hAc disjoint_compl_right
  have hAp : A ∈ properGroups N := mem_properGroups.mpr ⟨hA, by
    intro h
    rw [h] at hAc
    simp at hAc⟩
  have hκ : (2 * p - 1) / (A.card : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr hA
    exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
  have herr : 2 * (m : ℝ) ≤ ε / 4 * L := by
    have h := (div_le_iff₀ hε).mp hLbig
    linarith
  have hLp : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hq : 0 ≤ (1 - p) ^ ((2 * m - 1) * A.card) := pow_nonneg (sub_nonneg.mpr hp₁.le) _
  have hcover : RecClockLG.recordCarrier p m r L ∩ {U |
      ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
          -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / (A.card : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) + ε * (L : ℝ) <
            WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc} ⊆ B ∪ E := by
    rintro U ⟨hU, s, t, hs, hst, ht, hsep, hdev⟩
    by_cases hgood : U ∈ B
    · exact Or.inl hgood
    let y := runMaxA p m U hA s + 1
    let z := runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)
    have hcnt : (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
      - ε / 4 * L ≤ (recWindowCount p m hA U s t : ℝ) := by
      by_cases hyz : y ≤ z
      · have hrec := RecClockLG.recHyp_at_record hU
        have hmin : (r : ℤ) - (L : ℤ) ≤ runMaxA p m U hA (recTimeA p m U r) := by
          obtain ⟨i, hi⟩ := hA
          exact (hrec.1 i).trans (pos_le_runMaxA_pos hi)
        have hmax : runMaxA p m U hA (recTimeA p m U r) ≤ (r : ℤ) :=
          Finset.sup'_le _ _ (fun i _ => hrec.2 i)
        have hT' := Nat.mul_le_mul_right L (show T ≤ T + 3 by omega)
        have hab : (y, z) ∈ ambFamily r T L :=
          record_window_mem_ambFamily hL hs hst (by omega) hcast hmin hmax hyz
        have hlen : (z - y).toNat + 1 =
            (runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat := by
          dsimp only [y, z] at hyz ⊢
          omega
        by_contra! hbad
        apply hgood
        refine Set.mem_biUnion (Finset.mem_attach _ ⟨A, hAp⟩) (Set.mem_biUnion hab ?_)
        change (recWindowCount p m hA U s t : ℝ) <
          (1 - p) ^ ((2 * m - 1) * A.card) * ((z - y).toNat + 1 : ℝ) - ε / 4 * L
        rw [← Nat.cast_one, ← Nat.cast_add, hlen]
        simpa only [Nat.cast_one] using hbad
      · have hz : (runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat = 0 := by
          dsimp only [y, z] at hyz
          omega
        rw [hz, Nat.cast_zero, mul_zero, zero_sub]
        exact (neg_nonpos.mpr (by positivity)).trans (Nat.cast_nonneg _)
    have hd := sum_group_drift_le_of_trial_counts hp₀ hp₁ (by omega : 1 ≤ m) A hA hsep hcnt
    have hrem : (2 * p - 1) / (A.card : ℝ) * (2 * (m : ℝ) + ε / 4 * L) ≤ ε / 2 * L := by
      calc
        _ ≤ 1 * (2 * (m : ℝ) + ε / 4 * L) := mul_le_mul_of_nonneg_right hκ.2 (by positivity)
        _ ≤ _ := by linarith
    exact Or.inr ⟨hU, s, t, hs, hst, ht, hsep, by linarith⟩
  have hV : 1 ≤ R L := Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hVcube : R L ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hVL : R L ≤ (L : ℝ) := by
    rw [← hVcube]
    exact le_self_pow₀ hV (by decide)
  have h₁ : Real.exp (-a * (L : ℝ)) ≤ Real.exp (-(min a b) * R L) := by
    apply Real.exp_le_exp.mpr
    have ha₁ := mul_le_mul_of_nonneg_left hVL ha.le
    have ha₂ := mul_le_mul_of_nonneg_right (min_le_left a b) (zero_le_one.trans hV)
    linarith
  have h₂ : Real.exp (-b * R L) ≤ Real.exp (-(min a b) * R L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right a b))
      (zero_le_one.trans hV))
  refine (measureReal_mono hcover (measure_ne_top μ _)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hB hE).trans ?_))
  calc
    _ ≤ 2 * Real.exp (-(min a b) * R L) := by linarith
    _ ≤ Real.exp (c * R L) * Real.exp (-(min a b) * R L) :=
      mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [c, R]; ring

end Swarming.Diameter
