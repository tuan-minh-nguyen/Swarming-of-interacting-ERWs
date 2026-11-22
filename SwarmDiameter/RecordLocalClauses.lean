import SwarmDiameter.RecordGroupMovement
import SwarmDiameter.RecordOccupationHighProbability
import Swarm.MartClauseActual

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Model Swarming.Enl Swarming.Trajectory SwarmRecordMeas.Actual
open SepGroup.Model Loccoord PaperBlock SwarmJointDrift
open scoped Topology

set_option autoImplicit false

namespace Swarming.Diameter

private theorem measureReal_iUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → Set Ω} {a : ℝ}
    (hE : ∀ i, μ.real (E i) ≤ a) : μ.real (⋃ i, E i) ≤ (Fintype.card ι : ℝ) * a := by
  refine (measureReal_iUnion_fintype_le E).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hE i))

private theorem record_drift_martingale_failure_le_exp
    {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, ∀ i : Fin N,
      (arrayMeasure N).real (RecordClock.stoppedWindowRec p m r (T * L) (ε * L) i) ≤
        Real.exp (-c * (L : ℝ)) := by
  let d := ε ^ 2 / (16 * (T : ℝ))
  have hT₀ : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hp := LocSumR1.eventually_poly_mul_exp_le (C := 2 * ((T : ℝ) + 1) ^ 2)
    (by positivity) hd 2
  have htop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), htop.eventually hp] with L hL hpL
  intro r i
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL₀ : (0 : ℝ) < L := zero_lt_one.trans_le hLr
  have hδ : 0 < ε * (L : ℝ) := mul_pos hε hL₀
  refine (RecordClock.measureReal_stoppedWindowRec hp₀ hp₁ hm hN r i (Nat.mul_le_mul hT hL) hδ).trans ?_
  have hrate : (ε * (L : ℝ)) ^ 2 / (16 * ((T * L : ℕ) : ℝ)) = d * (L : ℝ) := by
    push_cast
    dsimp only [d]
    field_simp
  have hlen : ((T * L : ℕ) : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
    push_cast
    linarith
  calc
    _ ≤ 2 * (((T : ℝ) + 1) * L) ^ 2 * Real.exp (-d * (L : ℝ)) := by
      rw [neg_div, hrate, neg_mul]
      gcongr
    _ = (2 * ((T : ℝ) + 1) ^ 2) * (L : ℝ) ^ 2 * Real.exp (-d * (L : ℝ)) := by ring
    _ ≤ _ := hpL

/-- The local clauses of the deterministic record estimate hold simultaneously
with a prescribed error `ε * L` and exceptional probability `K * exp (-c * L ^ (1 / 3))`.
The coefficient `C` is chosen before the time interval and error tolerance. -/
theorem record_local_clauses_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N : ℕ) [Nonempty (Fin N)] (hN : 2 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : ℕ), 1 ≤ T → ∀ {ε : ℝ}, 0 < ε →
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
        let CT := ε * (L : ℝ) / (L : ℝ) ^ (3 / 4 : ℝ)
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ¬ (BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U) C CT T L r ∧
            JoinStep.MartClause (Xa p m U) (tauA p m U) (fun i n => excitedSteps p m U n i)
              (2 * p - 1) CT T L r)})
          ≤ K * Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  classical
  obtain ⟨C₁, hC₁, hoc⟩ := record_occupation_failure_le_cube_root hp₀ hp₁ hm
  obtain ⟨C₂, hC₂, hpot⟩ := record_group_potential_failure_le_cube_root hp₀ hp₁ hm
  obtain ⟨C₃, hC₃, hmov⟩ := record_group_movement_failure_le_cube_root hp₀ hp₁ hm N
  let C := max C₁ (max C₂ C₃)
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  have hC₂' : C₂ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₃' : C₃ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro T hT ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨a₁, h₁, ho⟩ := hoc N T hT hε
  obtain ⟨a₂, h₂, hp⟩ := hpot N T hδ
  obtain ⟨a₃, h₃, hw⟩ := hmov T hT hδ
  obtain ⟨a₄, h₄, hg⟩ := record_separated_group_failure_le_cube_root hp₀ hp₁ hm N T hT hδ
  obtain ⟨a₅, h₅, hmart⟩ := record_drift_martingale_failure_le_exp hp₀ hp₁ hm hN T hT hε
  let c := min a₁ (min a₂ (min a₃ (min a₄ a₅)))
  have hc : 0 < c := lt_min h₁ (lt_min h₂ (lt_min h₃ (lt_min h₄ h₅)))
  let P := {ij : Fin N × Fin N // ij.1 ≠ ij.2}
  let A := {A : Finset (Fin N) // A.Nonempty ∧ Aᶜ.Nonempty}
  let G := {IJ : Finset (Fin N) × Finset (Fin N) //
    IJ.1.Nonempty ∧ IJ.2.Nonempty ∧ Disjoint IJ.1 IJ.2}
  let K : ℝ := (Fintype.card P : ℝ) * 3 + 1 + (Fintype.card A : ℝ) * 3 +
    (Fintype.card G : ℝ) + N
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 / δ)
  refine ⟨K, c, by dsimp only [K]; positivity, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge, ho, hp, hw, hg, hmart]
    with L hL hLbig hoL hpL hwL hgL hmL
  intro r hr
  let CT := ε * (L : ℝ) / (L : ℝ) ^ (3 / 4 : ℝ)
  let μ := arrayMeasure N
  let F := RecClockLG.recordCarrier (N := N) p m r L
  let σ (U : Array N) := recTimeA p m U r
  let V := (L : ℝ) ^ (1 / 3 : ℝ)
  let E₁ (ij : P) : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      C₁ * ((runMax p m U ij.1.1 t : ℝ) - ((trajectory p m U s).pos ij.1.1 : ℝ) +
        max 0 ((runMax p m U ij.1.1 s : ℝ) - (runMax p m U ij.1.2 s : ℝ))) +
        ((t : ℝ) - (s : ℝ)) / 8 + ε * L <
      ∑ u ∈ Finset.Ico s t, (if (trajectory p m U u).pos ij.1.1 ≤ runMax p m U ij.1.2 u then
        (1 : ℝ) else 0)}
  let E₂ : Set (Array N) := F ∩ {U |
    ∃ (A : Finset (Fin N)) (hA : A.Nonempty) (n a b : ℕ),
      σ U ≤ n ∧ n ≤ σ U + T * L ∧ r - (T + 2) * L ≤ a ∧ a ≤ b ∧
        (b : ℤ) ≤ runMaxA p m U hA n ∧
        C₂ * ((b : ℝ) - (a : ℝ)) + δ * L <
          HA p m U n A (b : ℤ) - HA p m U n A (a : ℤ)}
  let E₃ (a : A) : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u a.1 a.1ᶜ U) ∧
      C₃ * ((runMaxA p m U a.2.1 s : ℝ) - (Xmin p m U a.1 a.2.1 s : ℝ)) -
        ((t - s : ℕ) : ℝ) / C₃ + δ * L <
        WA p m U t a.1 a.1ᶜ a.2.1 a.2.2 - WA p m U s a.1 a.1ᶜ a.2.1 a.2.2}
  let E₄ (g : G) : Set (Array N) := F ∩ {U |
    ∃ s t : ℕ, σ U ≤ s ∧ s ≤ t ∧ t ≤ σ U + T * L ∧
      (∀ u ∈ Finset.Ico s t, SepSet p m u g.1.1 g.1.2 U) ∧
      δ * L < WA p m U t g.1.1 g.1.2 g.2.1 g.2.2.1 - WA p m U s g.1.1 g.1.2 g.2.1 g.2.2.1}
  let E₅ (i : Fin N) := RecordClock.stoppedWindowRec p m r (T * L) (ε * L) i
  have hLr : (0 : ℝ) < L := by exact_mod_cast (zero_lt_one.trans_le hL)
  have hCT : CT * (L : ℝ) ^ (3 / 4 : ℝ) = ε * L := by dsimp only [CT]; field_simp
  have hround : δ * (L : ℝ) + 2 ≤ ε * L := by
    have h := (div_le_iff₀ hδ).mp hLbig
    dsimp only [δ] at h ⊢
    nlinarith only [h]
  have hcover : F ∩ {U |
      ¬ (BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U) C CT T L r ∧
        JoinStep.MartClause (Xa p m U) (tauA p m U) (fun i n => excitedSteps p m U n i)
          (2 * p - 1) CT T L r)} ⊆
      (⋃ ij, E₁ ij) ∪ (E₂ ∪ ((⋃ a, E₃ a) ∪ ((⋃ g, E₄ g) ∪ (⋃ i, E₅ i)))) := by
    rintro U ⟨hU, hbad⟩
    by_contra hnone
    apply hbad
    have h₁' (ij : P) : U ∉ E₁ ij := fun h => hnone (Or.inl (Set.mem_iUnion.mpr ⟨ij, h⟩))
    have h₂' : U ∉ E₂ := fun h => hnone (Or.inr (Or.inl h))
    have h₃' (a : A) : U ∉ E₃ a := fun h => hnone (Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨a, h⟩))))
    have h₄' (g : G) : U ∉ E₄ g :=
      fun h => hnone (Or.inr (Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨g, h⟩)))))
    have h₅' (i : Fin N) : U ∉ E₅ i :=
      fun h => hnone (Or.inr (Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩)))))
    have hsep (I J : Finset (Fin N)) {s t : ℕ} (hs : tauA p m U r ≤ s)
        (ht : t ≤ tauA p m U r + T * L)
        (h : ∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) I J u) :
        ∀ u ∈ Finset.Ico s t, SepSet p m u I J U := by
      intro u hu
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hu
      exact sepSet_of_sep p m u I J U
        (fun i => nonneg_of_carrier p m r L T U hU hr (hs.trans hlo) (hhi.le.trans ht) i)
        (h u hlo hhi)
    refine ⟨⟨⟨Hc_mono p m U hp₀.le hp₁.le, Hc_unit p m U hp₀.le hp₁.le, ?_, ?_, ?_⟩, ?_⟩,
      M1DMart.two_p_sub_one_pos hp₀, M1DMart.monotone_excitedSteps p m U, ?_⟩
    · intro A n hA _ hn ht a b ha hab hb
      have hTL := LocOccCarrierAssembly.T2L_le_r hr
      have halow : ((r - (T + 2) * L : ℕ) : ℤ) ≤ a := by rwa [Nat.cast_sub hTL]
      have ha0 : 0 ≤ a := (Int.natCast_nonneg _).trans halow
      have hb0 := ha0.trans hab
      have hlow := Int.toNat_le_toNat halow
      rw [Int.toNat_natCast] at hlow
      have hhi : (b.toNat : ℤ) ≤ runMaxA p m U hA n := by
        rwa [Int.toNat_of_nonneg hb0, ← sMaxM_eq_runMaxA p m U A hA n]
      have hreal : HA p m U n A b - HA p m U n A a ≤
          C₂ * ((b : ℝ) - (a : ℝ)) + δ * L := by
        by_contra! h
        apply h₂'
        refine ⟨hU, A, hA, n, a.toNat, b.toNat, hn, ht, hlow, Int.toNat_le_toNat hab, hhi, ?_⟩
        rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0]
        have hac : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha0
        have hbc : (b.toNat : ℝ) = (b : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hb0
        rwa [hac, hbc]
      rw [hCT]
      push_cast
      have hc₂ := mul_le_mul_of_nonneg_right hC₂' (sub_nonneg.mpr (by exact_mod_cast hab) :
        0 ≤ (b : ℝ) - (a : ℝ))
      have hceil := Hc_diff_le p m U A n a b
      push_cast at hceil
      linarith only [hceil, hreal, hc₂, hround]
    · intro B s t hB hB' hs hst ht hsep'
      have hBc : Bᶜ.Nonempty := by
        rw [Finset.compl_eq_univ_sdiff]
        refine Finset.sdiff_nonempty.mpr (fun h => hB' ?_)
        exact Finset.eq_univ_iff_forall.mpr (fun i => h (Finset.mem_univ i))
      let a : A := ⟨B, hB, hBc⟩
      have hsepB : ∀ u ∈ Finset.Ico s t, SepSet p m u B Bᶜ U := by
        simpa only [Finset.compl_eq_univ_sdiff] using hsep B (Finset.univ \ B) hs ht hsep'
      have hb := not_lt.mp (show ¬ _ from fun h => h₃' a ⟨hU, s, t, hs, hst, ht, hsepB, h⟩)
      change WA p m U t B Bᶜ hB hBc - WA p m U s B Bᶜ hB hBc ≤
        C₃ * ((runMaxA p m U hB s : ℝ) - (Xmin p m U B hB s : ℝ)) -
          ((t - s : ℕ) : ℝ) / C₃ + δ * L at hb
      rw [Wst_eq_Wpot, Wst_eq_Wpot, ← Finset.compl_eq_univ_sdiff,
        sMaxM_eq_runMaxA p m U B hB s, sMin_eq_Xmin p m U B hB s, hCT]
      have hx : 0 ≤ (runMaxA p m U hB s : ℝ) - (Xmin p m U B hB s : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast Xmin_le_Rmax U hB (s := s) le_rfl)
      have hcoef := mul_le_mul_of_nonneg_right hC₃' hx
      have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) (t - s))
        (zero_lt_one.trans_le hC₃) hC₃'
      have htW := Wpot_le_WA_add_one p m U B Bᶜ hB hBc t
      have hsW := WA_sub_one_le_Wpot p m U B Bᶜ hB hBc s
      rw [compl_compl] at htW hsW
      linarith only [htW, hsW, hb, hcoef, hdiv, hround]
    · intro i j hij t ht hTL
      let ij : P := ⟨(i, j), hij⟩
      have hb := not_lt.mp (show ¬ _ from fun h => h₁' ij ⟨hU, _, t, le_rfl, ht, hTL, h⟩)
      rw [hCT]
      simp only [LocalFluid.occTerm, LocalFluid.occGap, runMaxI_eq, Nat.cast_sub ht]
      change _ ≤ C * (((runMax p m U i t : ℝ) - (runMax p m U i (σ U) : ℝ)) +
        ((runMax p m U i (σ U) : ℝ) - ((trajectory p m U (σ U)).pos i : ℝ)) +
        max 0 ((runMax p m U i (σ U) : ℝ) - (runMax p m U j (σ U) : ℝ))) +
        ((t : ℝ) - (σ U : ℝ)) / 8 + ε * L
      rw [sub_add_sub_cancel]
      have hcoef : (0 : ℝ) ≤
          (runMax p m U i t : ℝ) - ((trajectory p m U (σ U)).pos i : ℝ) +
            max 0 ((runMax p m U i (σ U) : ℝ) - (runMax p m U j (σ U) : ℝ)) :=
        add_nonneg (sub_nonneg.mpr (by exact_mod_cast le_runMax_of_le p m U t i ht)) (le_max_left _ _)
      change (∑ u ∈ Finset.Ico (σ U) t, (if (trajectory p m U u).pos i ≤ runMax p m U j u then
        (1 : ℝ) else 0)) ≤ C₁ * ((runMax p m U i t : ℝ) - ((trajectory p m U (σ U)).pos i : ℝ) +
        max 0 ((runMax p m U i (σ U) : ℝ) - (runMax p m U j (σ U) : ℝ))) +
        ((t : ℝ) - (σ U : ℝ)) / 8 + ε * L at hb
      change (∑ u ∈ Finset.Ico (σ U) t, (if (trajectory p m U u).pos i ≤ runMax p m U j u then
        (1 : ℝ) else 0)) ≤ C * _ + _ + ε * L
      have hc' := mul_le_mul_of_nonneg_right (le_max_left C₁ (max C₂ C₃)) hcoef
      exact hb.trans (add_le_add (add_le_add hc' le_rfl) le_rfl)
    · intro I J hd hI hJ s t hs hst ht hsep'
      let g : G := ⟨(I, J), hI, hJ, hd⟩
      have hb : WA p m U t I J hI hJ - WA p m U s I J hI hJ ≤ δ * L := by
        by_contra! h
        exact h₄' g ⟨hU, s, t, hs, hst, ht, hsep I J hs ht hsep', h⟩
      rw [hCT, ← Finset.compl_eq_univ_sdiff]
      linarith [Wpot_le_WA_add_one p m U I J hI hJ t, WA_sub_one_le_Wpot p m U I J hI hJ s]
    · intro i s t hs hst ht
      rw [hCT]
      have hb : |driftMartingale p m U t i - driftMartingale p m U s i| ≤ ε * L := by
        by_contra! h
        exact h₅' i (ClockLocMove.mem_stoppedWindow_of_pair
          (Q := fun n U => driftMartingale p m U n i) hs hst ht h.le)
      rw [M1DMart.Xa_excitedSteps_martingaleEq, M1DMart.Xa_excitedSteps_martingaleEq] at hb
      convert hb using 2
      ring
  have hV : 1 ≤ V := Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hV3 : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hVL : V ≤ (L : ℝ) := by rw [← hV3]; exact le_self_pow₀ hV (by decide)
  have he (z : ℝ) (hz : c ≤ z) : Real.exp (-z * V) ≤ Real.exp (-c * V) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) (zero_le_one.trans hV))
  have he₁ (ij : P) : μ.real (E₁ ij) ≤ 3 * Real.exp (-c * V) :=
    (hoL r hr ij.1.1 ij.1.2 ij.2).trans (mul_le_mul_of_nonneg_left (he a₁ (min_le_left _ _)) (by norm_num))
  have he₂ : μ.real E₂ ≤ Real.exp (-c * V) := (hpL r hr).trans
    (he a₂ ((min_le_right _ _).trans (min_le_left _ _)))
  have he₃ (a : A) : μ.real (E₃ a) ≤ 3 * Real.exp (-c * V) :=
    (hwL r hr a.1 a.2.1 a.2.2).trans (mul_le_mul_of_nonneg_left
      (he a₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) (by norm_num))
  have he₄ (g : G) : μ.real (E₄ g) ≤ Real.exp (-c * V) :=
    (hgL r hr g.1.1 g.1.2 g.2.1 g.2.2.1 g.2.2.2).trans
      (he a₄ ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
  have he₅ (i : Fin N) : μ.real (E₅ i) ≤ Real.exp (-c * V) := by
    refine (hmL r i).trans ((Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hVL (neg_nonpos.mpr h₅.le))).trans ?_)
    exact he a₅ ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  refine (measureReal_mono hcover (measure_ne_top μ _)).trans ?_
  calc
    _ ≤ (Fintype.card P : ℝ) * (3 * Real.exp (-c * V)) +
        (Real.exp (-c * V) + ((Fintype.card A : ℝ) * (3 * Real.exp (-c * V)) +
          ((Fintype.card G : ℝ) * Real.exp (-c * V) + (Fintype.card (Fin N) : ℝ) * Real.exp (-c * V)))) := by
      exact (measureReal_union_le _ _).trans (add_le_add (measureReal_iUnion_le_card_mul he₁)
        ((measureReal_union_le _ _).trans (add_le_add he₂
          ((measureReal_union_le _ _).trans (add_le_add (measureReal_iUnion_le_card_mul he₃)
            ((measureReal_union_le _ _).trans (add_le_add (measureReal_iUnion_le_card_mul he₄)
              (measureReal_iUnion_le_card_mul he₅))))))))
    _ = _ := by rw [Fintype.card_fin]; dsimp only [K, V]; ring

end Swarming.Diameter
