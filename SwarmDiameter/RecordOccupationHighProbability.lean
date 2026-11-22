import SwarmDiameter.ProjectedPotentialOscillation
import SwarmDiameter.RecordOccupationMartingale
import SwarmDiameter.RecordOccupationEstimate

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmRecordMeas.Actual
open Swarming.Enl Swarming.Enl.ProjLedger SwarmMarks SwarmLogRatio
open LocOccCarrierAssembly LocOccCarrier
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- The probability bound for the occupation estimate on the entire record
interval. The coefficient of the record increments depends only on the
parameters of the walk. The additive error is `ε * L`, and its failure
probability has the cube-root rate. -/
theorem record_occupation_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N T : ℕ) [Nonempty (Fin N)], 1 ≤ T → ∀ {ε : ℝ}, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
        ∀ (i j : Fin N), i ≠ j →
          (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
            ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
              C * (((runMax p m U i t : ℤ) : ℝ) - ((trajectory p m U s).pos i : ℝ) +
                max 0 (((runMax p m U i s : ℤ) : ℝ) - (runMax p m U j s : ℝ))) +
                ((t : ℝ) - (s : ℝ)) / 8 + ε * L <
              ∑ u ∈ Finset.Ico s t, (if (trajectory p m U u).pos i ≤ runMax p m U j u then
                (1 : ℝ) else 0)})
            ≤ 3 * Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  let D := 1 + K
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  let C := (2 * D + QplWindow.Lc p m) + 2 * CJc p m * (2 * D) + 1
  let C' := 2 * D + 1 + 2 * KFc p m + 4 * CJc p m * (2 * D) + 2 * 1 + 1 + 4 / (1 - aRec p m)
  have hCJ := CJc_nonneg hp₀ hp₁ m
  have hLc := QplWindow.Lc_nonneg hp₀ hp₁ m
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith
  have hC' : 0 < C' := by
    have hKF := KFc_nonneg hp₀ hp₁ m
    have hden := one_sub_aRec_pos hp₀ hp₁ m
    dsimp only [C']
    positivity
  refine ⟨C, hC, ?_⟩
  intro N T _ hT ε hε
  let δ := ε / C'
  have hδ : 0 < δ := div_pos hε hC'
  have hδe : C' * δ = ε := by dsimp only [δ]; field_simp
  obtain ⟨a, ha, hspat⟩ := hlocal N (2 * T + 4) hδ
  obtain ⟨b, hb, hproj⟩ := record_projH_oscillation_le_cube_root hp₀ hp₁ hm N T hT hδ
  obtain ⟨d, hd, hmart⟩ := record_Qpl_oscillation_le_cube_root hp₀ hp₁ hm N T hT
    (α := 1 / 8) (by norm_num) hδ
  let c := min a (min b d)
  have hc : 0 < c := lt_min ha (lt_min hb hd)
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hlarge := htop.eventually_ge_atTop (1 / δ)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspat, hproj, hmart, hlarge]
    with L hL hsL hpL hmL hlargeL
  intro r hr i j hij
  let μ := arrayMeasure N
  let F := RecClockLG.recordCarrier (N := N) p m r L
  let σ (U : Array N) := recTimeA p m U r
  let V := R L
  let A := A0 r T L
  let W := Lw T L
  let E := δ * (L : ℝ)
  let S : Set (Array N) := {U |
    (∃ (k : Fin N) (v : ℕ), v ≤ (2 * T + 4) * L ∧
        V < hof p (siteMarks p m U k) (A - 1 + v)) ∨
    (∃ (k : Fin N) (v n : ℕ), v ≤ (2 * T + 4) * L ∧ n ≤ (2 * T + 4) * L + 1 ∧
      K * n + E < ∑ x ∈ Finset.Ico (A - 1 + v) (A - 1 + v + n), hof p (siteMarks p m U k) x ^ 2)}
  let P : Set (Array N) := F ∩ {U |
    ∃ y ∈ Finset.Ico A (A + W), ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      E ≤ |projH p m j t U (y : ℤ) - projH p m j s U (y : ℤ)|}
  let M : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      E ≤ |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U|}
  have hS : μ.real S ≤ Real.exp (-a * V) := hsL (A - 1)
  have hP : μ.real P ≤ Real.exp (-b * V) := hpL r hr j
  have hM : μ.real M ≤ Real.exp (-d * V) := hmL r hr i j
  have hV : 1 ≤ V := Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hV3 : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V, R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hVE : V ^ 2 ≤ E := by
    have hx := (div_le_iff₀ hδ).mp hlargeL
    have hy := mul_le_mul_of_nonneg_right hx (sq_nonneg V)
    dsimp only [E]
    rw [← hV3]
    nlinarith only [hy]
  have hwindow : W + 1 ≤ (2 * T + 4) * L := by
    dsimp only [W, Lw]
    have h : (2 * T + 4) * L = (2 * T + 2) * L + 2 * L := by ring
    omega
  have hgood {U : Array N} (hU : U ∈ F) (hS' : U ∉ S) (hP' : U ∉ P) (hM' : U ∉ M)
      {s0 s t : ℕ} (hs0 : s0 = σ U)
      (hcarr : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L)
      (hs : s0 ≤ s) (hst : s ≤ t) (ht : t ≤ s0 + T * L) :
      (∀ a b : ℕ, A ≤ a → b ≤ A + W → a ≤ b →
        ∑ x ∈ Finset.Ico a b, hof p (siteMarks p m U j) x ^ 2
          ≤ 2 * D * ((b : ℝ) - (a : ℝ)) + E) ∧
      (∀ y ∈ Finset.Ico (A - 1) (A + W), hof p (siteMarks p m U j) y ≤ V) ∧
      Qpl p m (1 / 8) i j s U - Qpl p m (1 / 8) i j t U ≤ E ∧
      projH p m j t U ((trajectory p m U s).pos i) -
        projH p m j s U ((trajectory p m U s).pos i) ≤ E := by
    obtain ⟨hlo, hhi, -⟩ := carrier_cell_window hcarr hr i j hs (by omega : s ≤ s0 + T * L)
    have hX : ((trajectory p m U s).pos i).toNat ∈ Finset.Ico A (A + W) := by
      dsimp only [A, W]
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hXc : ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ) = (trajectory p m U s).pos i :=
      Int.toNat_of_nonneg (by omega)
    subst s0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a' b' ha' hb' hab'
      have hd' : (A - 1) + (a' - (A - 1)) = a' := by omega
      have hbound : ∑ x ∈ Finset.Ico a' b', hof p (siteMarks p m U j) x ^ 2 ≤
          K * (b' - a' : ℕ) + E := by
        by_contra! hf
        apply hS'
        refine Or.inr ⟨j, a' - (A - 1), b' - a', by omega, by omega, ?_⟩
        rwa [hd', Nat.add_sub_of_le hab']
      rw [Nat.cast_sub hab'] at hbound
      have hnonneg : 0 ≤ (b' : ℝ) - (a' : ℝ) := sub_nonneg.mpr (by exact_mod_cast hab')
      exact hbound.trans (add_le_add_left
        (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith : K ≤ 2 * D) hnonneg) _)
    · intro y hy
      obtain ⟨hy₁, hy₂⟩ := Finset.mem_Ico.mp hy
      apply le_of_not_gt
      intro he
      apply hS'
      refine Or.inl ⟨j, y - (A - 1), by omega, ?_⟩
      rwa [Nat.add_sub_of_le hy₁]
    · have h := not_le.mp (show ¬ E ≤ |Qpl p m (1 / 8) i j t U - Qpl p m (1 / 8) i j s U| from
        fun h => hM' ⟨hU, s, t, hs, hst, ht, h⟩)
      linarith [(abs_lt.mp h).1]
    · have h := not_le.mp (show ¬ E ≤ |projH p m j t U ((trajectory p m U s).pos i) -
        projH p m j s U ((trajectory p m U s).pos i)| from fun h =>
          hP' ⟨hU, _, hX, s, t, hs, hst, ht, by rwa [hXc]⟩)
      exact (abs_lt.mp h).2.le
  have hae (s0 s t : ℕ) : ∀ᵐ U ∂μ,
      U ∈ F → U ∉ S → U ∉ P → U ∉ M → σ U = s0 →
      s0 ≤ s → s ≤ t → t ≤ s0 + T * L →
      ∑ u ∈ Finset.Ico s t, (if (trajectory p m U u).pos i ≤ runMax p m U j u then
        (1 : ℝ) else 0) ≤ C * (((runMax p m U i t : ℤ) : ℝ) - ((trajectory p m U s).pos i : ℝ) +
        max 0 (((runMax p m U i s : ℤ) : ℝ) - (runMax p m U j s : ℝ))) +
        ((t : ℝ) - (s : ℝ)) / 8 + ε * L := by
    by_cases htime : s0 ≤ s ∧ s ≤ t ∧ t ≤ s0 + T * L
    · obtain ⟨hs, hst, ht⟩ := htime
      filter_upwards [record_occupation_estimate_of_local_bounds hp₀ hp₁ hm hij hD hL hV hVE
        hr hs hst ht] with U he hF hS' hP' hM' hσ _ _ _
      have hcarr : U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L := by
        obtain ⟨s', hs'⟩ := Set.mem_iUnion.mp (RecClockLG.subset_iUnion_recordBand p m r L hF)
        have hh : σ U = s' := RecClockLG.recTimeA_eq_of_mem_band hF.1 hs'
        rw [hσ] at hh
        rw [hh, ← RecClockLG.recordBand_eq_recordPrefixBand p m r L s']
        exact hs'
      obtain ⟨hls, hloc, hqpl, hosc⟩ := hgood hF hS' hP' hM' hσ.symm hcarr hs hst ht
      have hbound := he hcarr hls hloc hqpl hosc
      obtain ⟨hlo, -⟩ := carrier_cell_window hcarr hr i j hs (by omega : s ≤ s0 + T * L)
      rw [toNat_cast_real (by omega : 0 ≤ (trajectory p m U s).pos i),
        toNat_cast_real (zero_le_runMax p m U i s), toNat_cast_real (zero_le_runMax p m U i t),
        toNat_cast_real (zero_le_runMax p m U j s)] at hbound
      change _ ≤ C * _ + _ + C' * E at hbound
      dsimp only [E] at hbound
      rw [← mul_assoc, hδe] at hbound
      have htelescope : ((runMax p m U i t : ℝ) - (runMax p m U i s : ℝ)) +
          ((runMax p m U i s : ℝ) - ((trajectory p m U s).pos i : ℝ)) =
          (runMax p m U i t : ℝ) - ((trajectory p m U s).pos i : ℝ) := by ring
      rwa [htelescope] at hbound
    · exact Filter.Eventually.of_forall fun _ _ _ _ _ _ hs hst ht => False.elim (htime ⟨hs, hst, ht⟩)
  have hall := ae_all_iff.mpr (fun s0 => ae_all_iff.mpr (fun s => ae_all_iff.mpr (hae s0 s)))
  have hsub : ∀ᵐ U ∂μ, U ∈ F ∩ {U |
      ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
        C * (((runMax p m U i t : ℤ) : ℝ) - ((trajectory p m U s).pos i : ℝ) +
          max 0 (((runMax p m U i s : ℤ) : ℝ) - (runMax p m U j s : ℝ))) +
          ((t : ℝ) - (s : ℝ)) / 8 + ε * L <
        ∑ u ∈ Finset.Ico s t, (if (trajectory p m U u).pos i ≤ runMax p m U j u then
          (1 : ℝ) else 0)} → U ∈ S ∪ (P ∪ M) := by
    filter_upwards [hall] with U hU
    rintro ⟨hF, s, t, hs, hst, ht, hbad⟩
    by_contra hnone
    exact (not_lt_of_ge (hU (σ U) s t hF (fun h => hnone (Or.inl h))
      (fun h => hnone (Or.inr (Or.inl h))) (fun h => hnone (Or.inr (Or.inr h)))
      rfl hs hst ht)) hbad
  have hr₀ : 0 ≤ V := zero_le_one.trans hV
  have he (z : ℝ) (hz : c ≤ z) : Real.exp (-z * V) ≤ Real.exp (-c * V) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) hr₀)
  refine (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
    ((measureReal_union_le _ _).trans ?_)
  have he₁ := hS.trans (he a (min_le_left _ _))
  have he₂ := hP.trans (he b ((min_le_right a (min b d)).trans (min_le_left _ _)))
  have he₃ := hM.trans (he d ((min_le_right a (min b d)).trans (min_le_right _ _)))
  exact (add_le_add he₁ ((measureReal_union_le _ _).trans (add_le_add he₂ he₃))).trans_eq (by ring)

end Swarming.Diameter
