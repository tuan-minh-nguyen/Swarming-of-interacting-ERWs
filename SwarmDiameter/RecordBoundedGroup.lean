import SwarmDiameter.BoundedGroupMean
import Swarm.GammaStrictWindow

open Finset
open Swarming.Uniform Swarming.Group Swarming.Trajectory
open SwarmRecordMeas.Actual SepGroup.Model SwarmJointDrift LocGroupSimul Loccoord
open Swarming.GammaStrict SwarmLogRatio

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ} [Nonempty (Fin N)]

/-- Lower endpoint of the integer interval containing all sites used in
the bounded comparison. -/
def recordSpatialLo (r T L : ℕ) : ℕ := r - (T + 2) * L

/-- Upper endpoint of the integer interval containing all sites used in
the bounded comparison. -/
def recordSpatialHi (r T L : ℕ) : ℕ := r + (T + 2) * L

theorem record_position_in_spatial_interval {p : ℝ} {m r T L : ℕ} (hL : 1 ≤ L)
    (hr : (T + 3) * L ≤ r) {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    {n : ℕ} (hs : recTimeA p m U r ≤ n) (ht : n ≤ recTimeA p m U r + T * L) (i : Fin N) :
    (recordSpatialLo r T L : ℤ) + 1 ≤ X p m U n i ∧ X p m U n i ≤ (recordSpatialHi r T L : ℤ) := by
  have hrec := RecClockLG.recHyp_at_record hU
  have hlo := RecHyp_pos_ge hrec hs ht i
  have hhi := (le_runMax p m U i n).trans (RecHyp_runMax_bounds hrec hs ht i).2
  have ha : (T + 2) * L ≤ r :=
    (Nat.mul_le_mul_right L (show T + 2 ≤ T + 3 by omega)).trans hr
  unfold recordSpatialLo recordSpatialHi
  push_cast [Nat.cast_sub ha] at hlo hhi ⊢
  change _ ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ _
  have hh : (1 : ℤ) ≤ L := by exact_mod_cast hL
  constructor <;> nlinarith only [hlo, hhi, hh]

/-- In a record interval, the bounded group comparison can lose drift only
when the minimum of the second group is in the exceptional set. -/
theorem record_boundedGroupGap_sub_le {p θ : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m r T L k ℓ : ℕ}
    (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) (hk : 1 ≤ k) (hka : k ≤ recordSpatialLo r T L)
    (hpK : 1 ≤ (2 * p - 1) * (8 * (k : ℝ))) (hθ : 0 < θ) (hθK : θ * (8 * (k : ℝ)) ≤ 1)
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    {n : ℕ} (hs : recTimeA p m U r ≤ n) (ht : n ≤ recTimeA p m U r + T * L)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIJ : Disjoint I J) (hsep : SepSet p m n I J U) :
    let K : ℝ := 8 * (k : ℝ)
    let S := boundedExceptionSites p m k ℓ (recordSpatialLo r T L) (recordSpatialHi r T L) U
    boundedGroupGap p K θ m U (n + 1) I J - boundedGroupGap p K θ m U n I J ≤
      average I (boundedCorrection p K m U n Jᶜ) +
        θ * K ^ 2 + (J.card : ℝ) * Real.exp (-θ * (ℓ : ℝ)) +
        (if Xmin p m U J hJ n ∈ S then (1 : ℝ) else 0) +
        weightedJump p m (boundedGroupCoeff p K θ m I J) n U := by
  intro K S
  let a := recordSpatialLo r T L
  let b := recordSpatialHi r T L
  let v := Xmin p m U J hJ n
  have hK : 1 ≤ K := by
    have hh : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [K]; linarith only [hh]
  obtain ⟨i, hi⟩ := hI
  have hiJ : i ∈ Jᶜ := Finset.mem_compl.mpr (fun hj => Finset.disjoint_left.mp hIJ hi hj)
  have hpos := record_position_in_spatial_interval hL hr hU hs ht
  have hvs : v ∈ Finset.Icc (a : ℤ) (b : ℤ) := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' hJ (X p m U n)
    change v = X p m U n j at hj
    rw [hj, Finset.mem_Icc]
    exact ⟨by have := (hpos j).1; dsimp only [a]; omega, (hpos j).2⟩
  have hnear (hv : v ∉ S) (j : Fin N) (hj : j ∈ J)
      (hjv : (X p m U n j : ℝ) - (v : ℝ) ≤ (ℓ : ℝ)) :
      boundedSlope K (wA p m U n Jᶜ) (X p m U n j).toNat ≤ K - 2 := by
    let y := (X p m U n j - 1).toNat
    have hy : (y : ℤ) = X p m U n j - 1 := Int.toNat_of_nonneg (by
      have := (hpos j).1
      omega)
    have hy' : y + 1 = (X p m U n j).toNat := by omega
    have hya : a ≤ y := by
      have := (hpos j).1
      dsimp only [a]
      omega
    have hyb : y < b := by
      have := (hpos j).2
      dsimp only [b]
      omega
    have hyR : (y : ℤ) < runMax p m U i n := by
      have h₁ := hsep.2 i hi j hj
      have h₂ : X p m U n j ≤ runMax p m U j n := le_runMax p m U j n
      have h₃ : X p m U n i ≤ runMax p m U i n := le_runMax p m U i n
      omega
    have hbound := boundedSlope_wA_le_finiteSlope hK hp₀ hp₁ hiJ (hka.trans hya) hyR
    rw [hy'] at hbound
    refine hbound.trans (finiteSlope_le_cap_sub_two hp₀ hp₁ hk ?_)
    by_contra! hP
    have hgap : X p m U n j - v ≤ (ℓ : ℤ) := by exact_mod_cast hjv
    have hvj : v ≤ X p m U n j := Finset.inf'_le (X p m U n) hj
    have hd : |v - (y : ℤ)| ≤ (ℓ : ℤ) + 1 := by rw [abs_le, hy]; omega
    exact hv (mem_boundedExceptionSites hvs i (Finset.mem_Ico.mpr ⟨hya, hyb⟩) hd hP)
  have hmin := weighted_comparisonMean_ge hp₀.le hp₁.le hK hpK hθ m U n hJ
    (fun j _ => hsep.1 j) S ℓ hnear
  have havg : average I (comparisonMean p K m U n Jᶜ) ≤
      1 + average I (boundedCorrection p K m U n Jᶜ) := by
    have h := average_mono (s := I) (fun j _ =>
      comparisonMean_le_one_add hp₀.le hp₁.le hK m U n Jᶜ j (hsep.1 j))
    rw [average_add, group_average_const ⟨i, hi⟩] at h
    exact h
  have hstep := boundedGroupGap_sub_le_means hp₀.le hp₁.le hK hθ hθK m U n ⟨i, hi⟩ hJ hsep
  linarith only [hmin, havg, hstep]

omit [Nonempty (Fin N)] in
/-- A lower bound on the comparison in terms of the two group minima. -/
theorem positionGap_le_boundedGroupGap {p K θ : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (hθ : 0 < θ) (m : ℕ) (U : Array N) (n : ℕ)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (hmin : Xmin p m U J hJ n ≤ Xmin p m U I hI n) :
    (Xmin p m U I hI n : ℝ) - (Xmin p m U J hJ n : ℝ) ≤ boundedGroupGap p K θ m U n I J := by
  let H := boundedHA p m K U n Jᶜ
  let v := Xmin p m U J hJ n
  let u := Xmin p m U I hI n
  let z (i : Fin N) := H (X p m U n i)
  have ha : ∃ j ∈ J, z j ≤ H v := by
    obtain ⟨j, hj, hv⟩ := Finset.exists_mem_eq_inf' hJ (X p m U n)
    change v = X p m U n j at hv
    exact ⟨j, hj, (congrArg H hv.symm).le⟩
  have hb (i : Fin N) (hi : i ∈ I) : H v + ((u : ℝ) - (v : ℝ)) ≤ z i := by
    have hx : u ≤ X p m U n i := Finset.inf'_le (X p m U n) hi
    have hx' : (u : ℝ) ≤ (X p m U n i : ℝ) := by exact_mod_cast hx
    have h := (boundedPotential_sub_bounds hK (wA_pos p m U hp₀ n Jᶜ)
      (wA_le_one p m U hp₁ n Jᶜ) (hmin.trans hx)).1
    change _ ≤ z i - H v at h
    linarith only [h, hx']
  have h := le_groupComparison_of_bounds hθ hI hJ ha hb
  change H v + ((u : ℝ) - (v : ℝ)) - H v ≤ boundedGroupGap p K θ m U n I J at h
  simpa only [add_sub_cancel_left] using h

omit [Nonempty (Fin N)] in
/-- An upper bound on the comparison using any upper bound on the
positions of the first group. -/
theorem boundedGroupGap_le_of_position_upper {p K θ : ℝ}
    (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1) (hK : 1 ≤ K) (hθ : 0 < θ)
    (m : ℕ) (U : Array N) (n : ℕ) {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty)
    {y : ℤ} (hy : ∀ i ∈ I, X p m U n i ≤ y) :
    boundedGroupGap p K θ m U n I J ≤
      boundedHA p m K U n Jᶜ y - boundedHA p m K U n Jᶜ (Xmin p m U J hJ n) +
        Real.log (J.card : ℝ) / θ := by
  have hH := monotone_boundedHA hp₀ hp₁ hK m U n Jᶜ
  exact groupComparison_le_of_bounds hθ hI hJ (fun j hj => hH (Finset.inf'_le (X p m U n) hj))
    (fun i hi => hH (hy i hi))

omit [Nonempty (Fin N)] in
theorem sum_boundedCorrection_le_zero {p K : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1)
    (hK : 1 ≤ K) (m : ℕ) (U : Array N) {s t : ℕ} {I J : Finset (Fin N)} (hIJ : Disjoint I J)
    (hsep : ∀ u ∈ Finset.Ico s t, SepSet p m u I J U) :
    (∑ u ∈ Finset.Ico s t, average I (boundedCorrection p K m U u Jᶜ)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro u hu
  unfold average
  exact div_nonpos_of_nonpos_of_nonneg
    (Finset.sum_nonpos (fun j hj => boundedCorrection_nonpos_of_sep hp₀ hp₁ hK m U u hIJ (hsep u hu) hj))
    (Nat.cast_nonneg _)

omit [Nonempty (Fin N)] in
/-- Trials producing distinct strict times bound the sum of the
bounded drift corrections over the separated interval. -/
theorem sum_boundedCorrection_le_of_strictTimes {p K : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hK : 1 ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (U : Array N) {s t : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty)
    (hsep : ∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U)
    {q e : ℝ} (hcount : q - e ≤ (strictTimes p m hA U s t).card) :
    (∑ u ∈ Finset.Ico s t, average A (boundedCorrection p K m U u A)) ≤
      -((2 * p - 1) / (A.card : ℝ)) * q + ((2 * p - 1) / (A.card : ℝ)) * e := by
  let d := (2 * p - 1) / (A.card : ℝ)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hd : 0 ≤ d := div_nonneg (by linarith) hApos.le
  let S := strictTimes p m hA U s t
  have hnonpos (u : ℕ) (hu : u ∈ Finset.Ico s t) (j : Fin N) (hj : j ∈ A) :
      boundedCorrection p K m U u A j ≤ 0 := by
    simpa only [compl_compl] using boundedCorrection_nonpos_of_sep hp₀.le hp₁.le hK m U u
      disjoint_compl_right (hsep u hu) hj
  have hsum (u : ℕ) (hu : u ∈ S) :
      average A (boundedCorrection p K m U u A) ≤ -d := by
    obtain ⟨hu', hstrict⟩ := mem_strictTimes_iff.mp hu
    obtain ⟨j, hj, hα, hw⟩ := exists_leader_of_mem_StrictAt hm hstrict
    have hn := boundedCorrection_le_of_strict hp₀.le hp₁.le hK m U u A j hα
      (by simpa only [compl_compl] using hw)
    have he (i : Fin N) (hi : i ∈ A) : boundedCorrection p K m U u A i ≤
        if i = j then -(2 * p - 1) else 0 := by
      by_cases hh : i = j
      · subst i
        simpa using hn
      · exact (if_neg hh).symm ▸ hnonpos u hu' i hi
    have hb := Finset.sum_le_sum he
    simp only [Finset.sum_ite_eq', hj, if_pos] at hb
    unfold average
    rw [show -d = -(2 * p - 1) / (A.card : ℝ) by dsimp only [d]; rw [neg_div]]
    exact div_le_div_of_nonneg_right hb hApos.le
  have hh := LocMove.sum_Ico_le_of_strict_lower (κ' := 1) (R := q) hd
    (strictTimes_subset U s t) hsum
    (fun u hu _ => div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos (hnonpos u hu)) hApos.le)
    (by simpa only [one_mul] using hcount)
  simpa only [mul_one] using hh

/-- Summation of the bounded group comparison over a record subinterval. -/
theorem record_boundedGroupGap_interval_le {p θ : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m r T L k ℓ : ℕ}
    (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) (hk : 1 ≤ k) (hka : k ≤ recordSpatialLo r T L)
    (hpK : 1 ≤ (2 * p - 1) * (8 * (k : ℝ))) (hθ : 0 < θ) (hθK : θ * (8 * (k : ℝ)) ≤ 1)
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    {s t : ℕ} (hs : recTimeA p m U r ≤ s) (hst : s ≤ t) (ht : t ≤ recTimeA p m U r + T * L)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty) (hIJ : Disjoint I J)
    (hsep : ∀ u ∈ Finset.Ico s t, SepSet p m u I J U) {ε : ℝ}
    (hpar : θ * (8 * (k : ℝ)) ^ 2 + (J.card : ℝ) * Real.exp (-θ * (ℓ : ℝ)) ≤ ε)
    (hocc : ∑ u ∈ Finset.Ico s t, (if Xmin p m U J hJ u ∈
        boundedExceptionSites p m k ℓ (recordSpatialLo r T L) (recordSpatialHi r T L) U then (1 : ℝ) else 0)
        ≤ ε * (L : ℝ))
    (hmart : |∑ u ∈ Finset.Ico s t, weightedJump p m (boundedGroupCoeff p (8 * (k : ℝ)) θ m I J) u U|
      ≤ ε * (L : ℝ)) :
    boundedGroupGap p (8 * (k : ℝ)) θ m U t I J - boundedGroupGap p (8 * (k : ℝ)) θ m U s I J ≤
      (∑ u ∈ Finset.Ico s t, average I (boundedCorrection p (8 * (k : ℝ)) m U u Jᶜ)) +
        ε * ((t : ℝ) - s) + 2 * ε * (L : ℝ) := by
  let K := 8 * (k : ℝ)
  let W (u : ℕ) := boundedGroupGap p K θ m U u I J
  let C (u : ℕ) := average I (boundedCorrection p K m U u Jᶜ)
  let S := boundedExceptionSites p m k ℓ (recordSpatialLo r T L) (recordSpatialHi r T L) U
  let O (u : ℕ) : ℝ := if Xmin p m U J hJ u ∈ S then 1 else 0
  let M (u : ℕ) := weightedJump p m (boundedGroupCoeff p K θ m I J) u U
  have hstep (u : ℕ) (hu : u ∈ Finset.Ico s t) :
      W (u + 1) - W u ≤ C u + ε + O u + M u := by
    obtain ⟨hsu, hut⟩ := Finset.mem_Ico.mp hu
    have h := record_boundedGroupGap_sub_le hp₀ hp₁ (ℓ := ℓ) hL hr hk hka hpK hθ hθK hU
      (hs.trans hsu) (hut.le.trans ht) hI hJ hIJ (hsep u hu)
    change W (u + 1) - W u ≤ C u + θ * K ^ 2 + (J.card : ℝ) * Real.exp (-θ * (ℓ : ℝ)) + O u + M u at h
    linarith only [h, hpar]
  have hall := Finset.sum_le_sum (s := Finset.Ico s t) hstep
  rw [Finset.sum_Ico_sub W hst] at hall
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hst] at hall
  change W t - W s ≤ (∑ u ∈ Finset.Ico s t, C u) + ε * ((t : ℝ) - s) + 2 * ε * (L : ℝ)
  have hO : (∑ u ∈ Finset.Ico s t, O u) ≤ ε * (L : ℝ) := hocc
  have hM : (∑ u ∈ Finset.Ico s t, M u) ≤ ε * (L : ℝ) := (le_abs_self _).trans hmart
  nlinarith only [hall, hO, hM]

end Swarming.Diameter
