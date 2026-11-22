import SwarmDiameter.RecordGroupAdvance
import SwarmDiameter.RecordGroupMaximum
import SwarmDiameter.RecordGroupPotential
import Swarm.PaperBlock

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Enl SwarmRecordMeas.Actual
open SwarmJointDrift SepGroup.Model Loccoord LocGroupSimul
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- The local movement estimate for two separated complementary groups.
The coefficient is independent of the length of the time interval and the
choice of group. The exceptional probability has the cube-root rate. -/
theorem record_group_movement_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N : ℕ) [Nonempty (Fin N)] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : ℕ), 1 ≤ T → ∀ {ε : ℝ}, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
        ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
          (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
            ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
              (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
              C * ((runMaxA p m U hA s : ℝ) - (Xmin p m U A hA s : ℝ)) -
                ((t - s : ℕ) : ℝ) / C + ε * L <
                WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc})
            ≤ 3 * Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hpot⟩ := record_group_potential_failure_le_cube_root hp₀ hp₁ hm
  let D := max K (RecordGroupUniform.commonCoordCoefficient N p m)
  have hD : 1 ≤ D := hK.trans (le_max_left _ _)
  have hDp : 0 < D := zero_lt_one.trans_le hD
  let C := 1 + D ^ 2
  have hC : 1 ≤ C := by dsimp only [C]; linarith [sq_nonneg D]
  refine ⟨C, hC, ?_⟩
  intro T hT ε hε
  obtain ⟨a, ha, hpa⟩ := hpot N T (half_pos hε)
  obtain ⟨b, hb, hpb⟩ := record_group_maximum_failure_le_cube_root hp₀ hp₁ hm N T hT (half_pos hε)
  obtain ⟨d, hd, hpd⟩ := record_group_advance_drift_failure_le_cube_root hp₀ hp₁ hm N T hT hε
  let c := min a (min b d)
  have hc : 0 < c := lt_min ha (lt_min hb hd)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpa, hpb, hpd] with L hpL hmL hdL
  intro r hr A hA hAc
  let μ := arrayMeasure N
  let F := RecClockLG.recordCarrier (N := N) p m r L
  let V := (L : ℝ) ^ (1 / 3 : ℝ)
  let γ := LocMoveCompose.gammaRate p m A
  let E₁ : Set (Array N) := F ∩ {U |
    ∃ (A : Finset (Fin N)) (hA : A.Nonempty) (n a b : ℕ),
      recTimeA p m U r ≤ n ∧ n ≤ recTimeA p m U r + T * L ∧
      r - (T + 2) * L ≤ a ∧ a ≤ b ∧ (b : ℤ) ≤ runMaxA p m U hA n ∧
      K * ((b : ℝ) - (a : ℝ)) + (ε / 2) * L <
        HA p m U n A (b : ℤ) - HA p m U n A (a : ℤ)}
  let E₂ : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
      Mnow p m t Aᶜ hAc U - Mnow p m s Aᶜ hAc U < ((t - s : ℕ) : ℝ) - (ε / 2) * L}
  let E₃ : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
      -γ * ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) + ε * L <
        WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc}
  have hJ : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using hA
  have hE₂ : μ.real E₂ ≤ Real.exp (-b * V) := by
    have h := hmL r hr Aᶜ hAc hJ
    simpa only [E₂, compl_compl] using h
  have hγp : 0 < γ := LocMove.gamma_rate_pos hp₀ hp₁ m A hA
  have hγD : 1 ≤ γ * D := (RecordGroupUniform.gammaRate_mul_common N hp₀ hp₁ hA).trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hγp.le)
  have hcover : F ∩ {U |
      ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u A Aᶜ U) ∧
        C * ((runMaxA p m U hA s : ℝ) - (Xmin p m U A hA s : ℝ)) -
          ((t - s : ℕ) : ℝ) / C + ε * L <
          WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc} ⊆ E₁ ∪ (E₂ ∪ E₃) := by
    rintro U ⟨hU, s, t, hs, hst, ht, hsep, hbad⟩
    by_contra hnone
    have h₁ : U ∉ E₁ := fun h => hnone (Or.inl h)
    have h₂ : U ∉ E₂ := fun h => hnone (Or.inr (Or.inl h))
    have h₃ : U ∉ E₃ := fun h => hnone (Or.inr (Or.inr h))
    let x := Xmin p m U A hA s
    let y := runMaxA p m U hA t
    have hxy : x ≤ y := Xmin_le_Rmax U hA hst
    have hxx : x ≤ runMaxA p m U hA s := Xmin_le_Rmax U hA le_rfl
    have hx : ((r - (T + 2) * L : ℕ) : ℤ) ≤ x := by
      have hrec := RecClockLG.recHyp_at_record hU
      have hTL := LocOccCarrierAssembly.T2L_le_r hr
      have hcut := Nat.mul_le_mul_right L (show T + 1 ≤ T + 2 by omega)
      rw [Nat.cast_sub hTL]
      refine Finset.le_inf' _ _ fun k _ => ?_
      have h := RecHyp_pos_ge hrec hs (hst.trans ht) k
      have hcast : (((T + 1) * L : ℕ) : ℤ) ≤ (((T + 2) * L : ℕ) : ℤ) := by exact_mod_cast hcut
      change _ ≤ (Swarming.Trajectory.trajectory p m U s).pos k
      omega
    have hx0 : 0 ≤ x := (Int.natCast_nonneg _).trans hx
    have hy0 : 0 ≤ y := hx0.trans hxy
    have ha := Int.toNat_le_toNat hx
    rw [Int.toNat_natCast] at ha
    have hpBound : HA p m U t A y - HA p m U t A x ≤
        K * ((y : ℝ) - (x : ℝ)) + (ε / 2) * L := by
      by_contra! hf
      apply h₁
      refine ⟨hU, A, hA, t, x.toNat, y.toNat, hs.trans hst, ht, ha, Int.toNat_le_toNat hxy, ?_, ?_⟩
      · rw [Int.toNat_of_nonneg hy0]
      · rw [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hx0]
        have hxc : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx0
        have hyc : (y.toNat : ℝ) = (y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hy0
        rwa [hxc, hyc]
    have hAavg : Anow p m t A Aᶜ U - Anow p m s A Aᶜ U ≤
        D * ((y : ℝ) - (x : ℝ)) + (ε / 2) * L := by
      have hmono : Monotone (HA p m U t A) :=
        SepGroup.HZ_mono (wA_pos p m U hp₀.le t A) (wA_le_one p m U hp₁.le t A)
      have havg : Anow p m t A Aᶜ U - Anow p m s A Aᶜ U ≤
          HA p m U t A y - HA p m U t A x := by
        simp only [Anow, compl_compl, ← SwarmQVariance.average_sub_group]
        refine (average_mono (g := fun _ => HA p m U t A y - HA p m U t A x) ?_).trans ?_
        · intro k hk
          have ht' := hmono (le_runMax_pos p m U t k |>.trans (le_runMaxA (hA := hA) hk))
          change HA p m U t A (X p m U t k) ≤ HA p m U t A y at ht'
          have hs' : HA p m U t A x ≤ HA p m U t A (X p m U s k) :=
            hmono (Finset.inf'_le (fun j => X p m U s j) hk)
          have htmon := SepGroup.HZ_diff_nonneg
            (wA_pos p m U hp₀.le s A) (wA_le_one p m U hp₁.le s A)
            (wA_pos p m U hp₀.le t A) (wA_le_one p m U hp₁.le t A)
            (wA_mono_time p m U hp₀.le hst A) (X p m U s k)
          change 0 ≤ HA p m U s A (X p m U s k) - HA p m U t A (X p m U s k) at htmon
          linarith
        · have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hA
          simp only [Swarming.Group.average, Finset.sum_const, nsmul_eq_mul]
          field_simp
          exact le_rfl
      have hnn : 0 ≤ (y : ℝ) - (x : ℝ) := sub_nonneg.mpr (by exact_mod_cast hxy)
      exact havg.trans (hpBound.trans (add_le_add_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn) _))
    let R := ((y - runMaxA p m U hA s : ℤ) : ℝ)
    let R₀ := ((runMaxA p m U hA s : ℝ) - (x : ℝ))
    let w := WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc
    have hR : 0 ≤ R := by
      dsimp only [R, y]
      exact_mod_cast sub_nonneg.mpr (runMaxA_mono hst)
    have hR₀ : 0 ≤ R₀ := sub_nonneg.mpr (by exact_mod_cast hxx)
    have hsum : (y : ℝ) - (x : ℝ) = R + R₀ := by
      dsimp only [R, R₀]
      push_cast
      ring
    have hmax : ((t - s : ℕ) : ℝ) - ε / 2 * L ≤ Mnow p m t Aᶜ hAc U - Mnow p m s Aᶜ hAc U :=
      le_of_not_gt (fun h => h₂ ⟨hU, s, t, hs, hst, ht, hsep, h⟩)
    have hw : w ≤ D * R + D * R₀ - ((t - s : ℕ) : ℝ) + ε * L := by
      rw [hsum, mul_add] at hAavg
      dsimp only [w]
      rw [WA_eq, WA_eq]
      linarith
    have hw' : w ≤ -γ * R + ε * L :=
      le_of_not_gt (fun h => h₃ ⟨hU, s, t, hs, hst, ht, hsep, h⟩)
    have hγR : R / D ≤ γ * R := by
      rw [div_le_iff₀ hDp]
      nlinarith [mul_le_mul_of_nonneg_right hγD hR]
    have hneg : -γ * R + ε * L ≤ -R / D + ε * L := by
      rw [neg_mul, neg_div]
      exact add_le_add_left (neg_le_neg hγR) _
    have hbound := LocMoveCompose.convex_combine_sharp hD hR hR₀ hw (hw'.trans hneg)
    rw [max_self] at hbound
    exact (not_lt_of_ge hbound) hbad
  have hr₀ : 0 ≤ V := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he (z : ℝ) (hz : c ≤ z) : Real.exp (-z * V) ≤ Real.exp (-c * V) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) hr₀)
  refine (measureReal_mono hcover (measure_ne_top μ _)).trans ((measureReal_union_le _ _).trans ?_)
  have he₁ := (hpL r hr).trans (he a (min_le_left _ _))
  have he₂ := hE₂.trans (he b ((min_le_right a (min b d)).trans (min_le_left _ _)))
  have he₃ := (hdL r hr A hA hAc).trans (he d ((min_le_right a (min b d)).trans (min_le_right _ _)))
  exact (add_le_add he₁ ((measureReal_union_le _ _).trans (add_le_add he₂ he₃))).trans_eq (by ring)

end Swarming.Diameter
