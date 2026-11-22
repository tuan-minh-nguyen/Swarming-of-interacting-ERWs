import SwarmDiameter.LinearBlockGeometry
import SwarmDiameter.RecordSpatialConcentration
import SwarmDiameter.RecordLinearTrialCount
import SwarmDiameter.RecordMinimumOccupation

open Finset Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl Swarming.Group
open SwarmRecordMeas.Actual PaperBlock SepGroup.Model Loccoord SwarmJointDrift LocSum LocSumAct

namespace Swarming.Diameter

set_option autoImplicit false

noncomputable def linearMinimumSpeed (p : ℝ) (N : ℕ) : ℝ := (2 * p - 1) / (N : ℝ)

noncomputable def linearStrictRate (p : ℝ) (m N : ℕ) : ℝ :=
  (2 * p - 1) * (1 - p) ^ ((2 * m - 1) * N) / (N : ℝ)

noncomputable def linearPositionConstant (p : ℝ) (m N : ℕ) : ℝ :=
  let C := 10 * Lb p (qOf p m)
  let k := linearStrictRate p m N
  C + (C + k) / (k * linearMinimumSpeed p N)

noncomputable def linearErrorFactor (p : ℝ) (m N T : ℕ) : ℝ :=
  let k := linearStrictRate p m N
  (T : ℝ) + 6 + ((T : ℝ) + 6 + k) / (k * linearMinimumSpeed p N)

theorem linearMinimumSpeed_pos {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) {N : ℕ} (hN : 0 < N) :
    0 < linearMinimumSpeed p N :=
  div_pos (by linarith) (by exact_mod_cast hN)

theorem linearStrictRate_pos {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (m : ℕ) {N : ℕ} (hN : 0 < N) : 0 < linearStrictRate p m N :=
  div_pos (mul_pos (by linarith) (pow_pos (sub_pos.mpr hp₁) _)) (by exact_mod_cast hN)

theorem one_le_linearPositionConstant {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (m : ℕ) {N : ℕ} (hN : 0 < N) : 1 ≤ linearPositionConstant p m N := by
  have hpq : 0 < qOf p m := pow_pos (by linarith) _
  have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hC := one_le_Lb hp₀ hp₁ hpq hq₁
  have hv := linearMinimumSpeed_pos hp₀ hN
  have hd := linearStrictRate_pos hp₀ hp₁ m hN
  change 1 ≤ 10 * Lb p (qOf p m) + _
  have hpos : 0 ≤ (10 * Lb p (qOf p m) + linearStrictRate p m N) /
      (linearStrictRate p m N * linearMinimumSpeed p N) :=
    div_nonneg (by linarith only [hC, hd]) (mul_nonneg hd.le hv.le)
  linarith only [hC, hpos]

variable {N : ℕ} [Nonempty (Fin N)]

/-- The measured estimates used on the record interval. -/
structure LinearRecordInputs (p : ℝ) (m k r T L : ℕ) (U : Array N)
    (θ ε η : ℝ) : Prop where
  spatial : RecordSpatialBounds p m k r T L U (ε / 10) η
  minimum : ∀ s t, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (RecordDefect.runMin (Xa p m U) s : ℝ) + linearMinimumSpeed p N * ((t : ℝ) - s) - ε * (L : ℝ) ≤
      (RecordDefect.runMin (Xa p m U) t : ℝ)
  down : ∀ i s t, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    (X p m U s i : ℝ) - X p m U t i ≤ ε * (L : ℝ)
  occupation : ∀ (J : Finset (Fin N)) (hJ : J.Nonempty),
    U ∉ recordMinimumOccupationBad p m r L T J hJ
      (boundedExceptionSites p m k (k ^ 3) (recordSpatialLo r T L) (recordSpatialHi r T L) U)
      (ε * (L : ℝ))
  noise : ∀ (I J : Finset (Fin N)), I.Nonempty → J.Nonempty → ∀ s t,
    recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
    |∑ u ∈ Finset.Ico s t, weightedJump p m (boundedGroupCoeff p (8 * (k : ℝ)) θ m I J) u U| ≤ ε * (L : ℝ)
  trials : U ∉ recordTrialBad N p m (r : ℤ) T L ε

private theorem global_min_eq_Xmin_of_sep {p : ℝ} {m n : ℕ} {U : Array N}
    {J : Finset (Fin N)} (hJ : J.Nonempty) (hsep : SepSet p m n Jᶜ J U) :
    Xmin p m U J hJ n = RecordDefect.runMin (Xa p m U) n := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    by_cases hi : i ∈ J
    · exact Finset.inf'_le (X p m U n) hi
    · obtain ⟨j, hj⟩ := hJ
      have h := hsep.2 i (Finset.mem_compl.mpr hi) j hj
      have hj' := le_runMax p m U j n
      change X p m U n j ≤ runMax p m U j n at hj'
      have hm := Finset.inf'_le (X p m U n) hj
      change Xmin p m U J ⟨j, hj⟩ n ≤ X p m U n i
      change Xmin p m U J ⟨j, hj⟩ n ≤ X p m U n j at hm
      omega
  · exact Finset.le_inf' _ _ (fun j _ => RecordDefect.runMin_le (X := Xa p m U) n j)

private theorem boundedGroupGap_le_spatial {p θ ε η : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    {m k r T L n : ℕ} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) (hk : 1 ≤ k) (hkL : k ≤ L)
    (hθ : 0 < θ) (hlog : Real.log (N : ℝ) / θ ≤ ε * (L : ℝ))
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    (hs : recTimeA p m U r ≤ n) (ht : n ≤ recTimeA p m U r + T * L)
    (hsp : RecordSpatialBounds p m k r T L U (ε / 10) η)
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    {y : ℤ} (hy : ∀ i ∈ I, X p m U n i ≤ y) (hvy : Xmin p m U J hJ n ≤ y)
    (hR : y ≤ runMaxA p m U hJc n) :
    boundedGroupGap p (8 * (k : ℝ)) θ m U n I J ≤
      (10 * Lb p (qOf p m)) * ((y : ℝ) - Xmin p m U J hJ n) + 2 * ε * (L : ℝ) := by
  have hK : (1 : ℝ) ≤ 8 * (k : ℝ) := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [hkr]
  obtain ⟨j, hj, hv⟩ := Finset.exists_mem_eq_inf' hJ (X p m U n)
  let v := Xmin p m U J hJ n
  change v = X p m U n j at hv
  have hpos := record_position_in_spatial_interval hL hr hU hs ht j
  have hvl : (recordSpatialLo r T L : ℤ) ≤ v := by
    rw [hv]
    omega
  have hhi : y ≤ (recordSpatialHi r T L : ℤ) := by
    apply hR.trans
    apply Finset.sup'_le
    intro i _
    have h := (LocGroupSimul.RecHyp_runMax_bounds (RecClockLG.recHyp_at_record hU) hs ht i).2
    unfold recordSpatialHi
    push_cast at h ⊢
    nlinarith only [h, Nat.cast_nonneg (α := ℤ) L]
  let a := v.toNat
  let b := y.toNat
  have ha : (a : ℤ) = v := Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) hvl)
  have hb : (b : ℤ) = y := Int.toNat_of_nonneg (le_trans (le_trans (Int.natCast_nonneg _) hvl) hvy)
  have hlo : recordSpatialLo r T L ≤ a := by omega
  have hab : a ≤ b := by omega
  have hbh : b ≤ recordSpatialHi r T L := by omega
  have hpotential := boundedHA_sub_le_of_Q_sum hp₀ hp₁ hk ((hkL.trans (recordSpatialLo_ge hr)).trans hlo)
    hJc hab (hb.trans_le hR) (fun i => hsp.slope i a b hlo hab hbh)
  have he₁ : (a : ℝ) = (v : ℝ) := by exact_mod_cast ha
  have he₂ : (b : ℝ) = (y : ℝ) := by exact_mod_cast hb
  rw [ha, hb, he₁, he₂] at hpotential
  have hcard : (J.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_univ J).trans_eq (Fintype.card_fin N)
  have hc₀ : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.mpr hJ
  have hsoft := (div_le_div_of_nonneg_right (Real.log_le_log hc₀ hcard) hθ.le).trans hlog
  have hbound := boundedGroupGap_le_of_position_upper hp₀.le hp₁.le hK hθ m U n hI hJ hy
  change boundedGroupGap p (8 * (k : ℝ)) θ m U n I J ≤
    boundedHA p m (8 * (k : ℝ)) U n Jᶜ y - boundedHA p m (8 * (k : ℝ)) U n Jᶜ v +
      Real.log (J.card : ℝ) / θ at hbound
  linarith only [hpotential, hsoft, hbound]

omit [Nonempty (Fin N)] in
private theorem linearStrictRate_le_group {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1)
    (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty) :
    linearStrictRate p m N ≤ (2 * p - 1) / (A.card : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) := by
  have hp : 0 ≤ 1 - p := by linarith
  have hcard : A.card ≤ N := (Finset.card_le_univ A).trans_eq (Fintype.card_fin N)
  have hA₀ : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hD : (2 * p - 1) / (N : ℝ) ≤ (2 * p - 1) / (A.card : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) hA₀ (by exact_mod_cast hcard)
  have he : (1 - p) ^ ((2 * m - 1) * N) ≤ (1 - p) ^ ((2 * m - 1) * A.card) :=
    pow_le_pow_of_le_one hp (by linarith) (Nat.mul_le_mul_left _ hcard)
  unfold linearStrictRate
  rw [mul_div_right_comm]
  exact mul_le_mul hD he (pow_nonneg hp _) (div_nonneg (by linarith) hA₀.le)

/-- The comparison estimates on the actual record interval, in position
form. The lower bound on minimum advance also bounds the time for a
separated group to meet its complement. -/
theorem linearBlockClauses_of_inputs {p θ ε η : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m k r T L : ℕ} (hm : 1 ≤ m)
    (hN : 0 < N) (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) (hk : 1 ≤ k) (hkL : k ≤ L)
    (hε : 0 ≤ ε) (hθ : 0 < θ) (hpK : 1 ≤ (2 * p - 1) * (8 * (k : ℝ)))
    (hθK : θ * (8 * (k : ℝ)) ≤ 1)
    (hpar : θ * (8 * (k : ℝ)) ^ 2 + (N : ℝ) * Real.exp (-θ * ((k ^ 3 : ℕ) : ℝ)) ≤ ε)
    (hlog : Real.log (N : ℝ) / θ ≤ ε * (L : ℝ)) (hlarge : 2 * (m : ℝ) ≤ ε * (L : ℝ))
    {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
    (h : LinearRecordInputs p m k r T L U θ ε η) :
    LinearBlockClauses (Xa p m U) (tauA p m U) r T L (linearPositionConstant p m N)
      (linearMinimumSpeed p N) (linearErrorFactor p m N T * ε * (L : ℝ)) := by
  let C := 10 * Lb p (qOf p m)
  let v := linearMinimumSpeed p N
  let d := linearStrictRate p m N
  let D := linearErrorFactor p m N T
  let K := 8 * (k : ℝ)
  let σ := recTimeA p m U r
  have hK : 1 ≤ K := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [K]
    linarith only [hkr]
  have hv : 0 < v := linearMinimumSpeed_pos hp₀ hN
  have hd : 0 < d := linearStrictRate_pos hp₀ hp₁ m hN
  have hdv := mul_pos hd hv
  have hC : 0 ≤ C := by
    have hq : 0 < qOf p m := pow_pos (by linarith) _
    have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hh := one_le_Lb hp₀ hp₁ hq hq₁
    dsimp only [C]
    linarith only [hh]
  have hCweak : C ≤ linearPositionConstant p m N :=
    le_add_of_nonneg_right (div_nonneg (add_nonneg hC hd.le) hdv.le)
  have hCmeet : (C + d) / (d * v) ≤ linearPositionConstant p m N :=
    le_add_of_nonneg_left hC
  have hDweak : (T : ℝ) + 6 ≤ D :=
    le_add_of_nonneg_right (div_nonneg (by positivity) hdv.le)
  have hDmeet : ((T : ℝ) + 6 + d) / (d * v) ≤ D :=
    le_add_of_nonneg_left (by positivity)
  have he : 0 ≤ ε * (L : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
  have herror (q : ℝ) (hq : q ≤ D) : q * (ε * (L : ℝ)) ≤ D * ε * (L : ℝ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hq he
  have hD₁ : (1 : ℝ) ≤ D := by linarith only [hDweak, Nat.cast_nonneg (α := ℝ) T]
  have hsmall : ε * (L : ℝ) ≤ D * ε * (L : ℝ) := by simpa only [one_mul] using herror 1 hD₁
  have hsepActual {I J : Finset (Fin N)} {s t : ℕ} (hs : σ ≤ s) (ht : t ≤ σ + T * L)
      (hsep : ∀ u ∈ Finset.Icc s t, Glue.Sep (Xa p m U) I J u) :
      ∀ u ∈ Finset.Icc s t, SepSet p m u I J U := by
    intro u hu
    obtain ⟨hu₀, hu₁⟩ := Finset.mem_Icc.mp hu
    exact sepSet_of_sep p m u I J U (fun i =>
      nonneg_of_carrier p m r L T U hU hr (hs.trans hu₀) (hu₁.trans ht) i) (hsep u hu)
  have hsum {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty) (hIJ : I ⊆ Jᶜ)
      {s t : ℕ} (hs : σ ≤ s) (hst : s ≤ t) (ht : t ≤ σ + T * L)
      (hsep : ∀ u ∈ Finset.Icc s t, SepSet p m u Jᶜ J U) :
      boundedGroupGap p K θ m U t I J - boundedGroupGap p K θ m U s I J ≤
        (∑ u ∈ Finset.Ico s t, average I (boundedCorrection p K m U u Jᶜ)) +
          ((T : ℝ) + 2) * (ε * (L : ℝ)) := by
    have hdi : Disjoint I J := Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_compl.mp (hIJ hi)) hj)
    have hIsep (u : ℕ) (hu : u ∈ Finset.Ico s t) : SepSet p m u I J U := by
      obtain ⟨hus, hut⟩ := Finset.mem_Ico.mp hu
      have hh := hsep u (Finset.mem_Icc.mpr ⟨hus, hut.le⟩)
      exact ⟨hh.1, fun i hi j hj => hh.2 i (hIJ hi) j hj⟩
    have hcard : (J.card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_le_univ J).trans_eq (Fintype.card_fin N)
    have hθc := (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)).trans hpar
    have hocc : ∑ u ∈ Finset.Ico s t, (if Xmin p m U J hJ u ∈
        boundedExceptionSites p m k (k ^ 3) (recordSpatialLo r T L) (recordSpatialHi r T L) U then (1 : ℝ) else 0)
        ≤ ε * (L : ℝ) := by
      by_contra! hb
      apply h.occupation J hJ
      refine ⟨hU, s, t, hs, hst, ht, ?_, hb⟩
      intro u hu
      obtain ⟨hus, hut⟩ := Finset.mem_Ico.mp hu
      have hh := hsep u (Finset.mem_Icc.mpr ⟨hus, hut.le⟩)
      obtain ⟨j, hj, hminj⟩ := Finset.exists_mem_eq_inf' hJ (X p m U u)
      refine ⟨global_min_eq_Xmin_of_sep hJ hh, ?_⟩
      change 0 ≤ J.inf' hJ (X p m U u)
      rw [hminj]
      exact hh.1 j
    have hw := record_boundedGroupGap_interval_le hp₀ hp₁ hL hr hk (hkL.trans (recordSpatialLo_ge hr))
      hpK hθ hθK hU hs hst ht hI hJ hdi hIsep hθc hocc (h.noise I J hI hJ s t hs hst ht)
    have hlen : (t : ℝ) - s ≤ (T : ℝ) * (L : ℝ) := by
      have hn : t ≤ s + T * L := ht.trans (Nat.add_le_add_right hs _)
      have hh : (t : ℝ) ≤ (s : ℝ) + (T : ℝ) * (L : ℝ) := by exact_mod_cast hn
      linarith only [hh]
    nlinarith only [hw, mul_le_mul_of_nonneg_left hlen hε]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i s t hs hst ht
    exact (h.down i s t hs hst ht).trans hsmall
  · intro s t hs hst ht
    have hh := h.minimum s t hs hst ht
    linarith only [hh, hsmall]
  · intro J i hi s t hs hst ht hsep
    have hsep' := hsepActual hs ht hsep
    have hsA := hsep s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩)
    have hJ := hsA.2.2.1
    have hJc := hsA.2.1
    let I : Finset (Fin N) := {i}
    have hI : I.Nonempty := Finset.singleton_nonempty _
    have hIJ : I ⊆ Jᶜ := Finset.singleton_subset_iff.mpr hi
    have hdi : Disjoint I J := Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_compl.mp (hIJ hi)) hj)
    have hIsep (u : ℕ) (hu : u ∈ Finset.Ico s t) : SepSet p m u I J U := by
      have hh := hsep' u (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hu).1, (Finset.mem_Ico.mp hu).2.le⟩)
      exact ⟨hh.1, fun j hj l hl => hh.2 j (hIJ hj) l hl⟩
    have hw := hsum hI hJ hIJ hs hst ht hsep'
    have hcorr := sum_boundedCorrection_le_zero hp₀.le hp₁.le hK m U hdi hIsep
    have hmin (u : ℕ) (hu : u ∈ Finset.Icc s t) : Xmin p m U J hJ u ≤ X p m U u i :=
      (global_min_eq_Xmin_of_sep hJ (hsep' u hu)).le.trans (RecordDefect.runMin_le (X := Xa p m U) u i)
    have hupper := boundedGroupGap_le_spatial hp₀ hp₁ hL hr hk hkL hθ hlog hU hs (hst.trans ht)
      h.spatial hI hJ hJc (fun j hj => by
        have hj' : j = i := Finset.mem_singleton.mp hj
        rw [hj']) (hmin s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩))
      (pos_le_runMaxA_pos hi)
    have hlower := positionGap_le_boundedGroupGap hp₀.le hp₁.le hK hθ m U t hI hJ
      (show Xmin p m U J hJ t ≤ Xmin p m U I hI t by
        simpa [I, Xmin] using hmin t (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩))
    have hlower' : (X p m U t i : ℝ) - (Xmin p m U J hJ t : ℝ) ≤ boundedGroupGap p K θ m U t I J := by
      simpa [I, Xmin] using hlower
    have hgap : 0 ≤ (X p m U s i : ℝ) - Xmin p m U J hJ s :=
      sub_nonneg.mpr (by exact_mod_cast hmin s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩))
    have hlarge' := mul_le_mul_of_nonneg_right hCweak hgap
    have he' := herror ((T : ℝ) + 4) (by linarith only [hDweak])
    rw [sMin_eq_Xmin p m U J hJ s, sMin_eq_Xmin p m U J hJ t]
    change (X p m U t i : ℝ) - (Xmin p m U J hJ t : ℝ) ≤ _
    nlinarith only [hw, hcorr, hupper, hlower', hlarge', he']
  · intro J s t hs hst ht hsep
    have hsep' := hsepActual hs ht hsep
    have hsA := hsep s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩)
    let A := Jᶜ
    have hA : A.Nonempty := hsA.2.1
    have hJ := hsA.2.2.1
    have hAc : Aᶜ.Nonempty := by simpa only [A, compl_compl] using hJ
    have hsepA (u : ℕ) (hu : u ∈ Finset.Ico s t) : SepSet p m u A Aᶜ U := by
      simpa only [A, compl_compl] using hsep' u (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hu).1, (Finset.mem_Ico.mp hu).2.le⟩)
    let R (u : ℕ) := runMaxA p m U hA u
    let G : ℝ := (Glue.sMaxM (Xa p m U) Finset.univ s : ℝ) - RecordDefect.runMin (Xa p m U) s
    have hminEq (u : ℕ) (hu : u ∈ Finset.Icc s t) :
        Xmin p m U J hJ u = RecordDefect.runMin (Xa p m U) u :=
      global_min_eq_Xmin_of_sep hJ (hsep' u hu)
    have hminR (u : ℕ) : RecordDefect.runMin (Xa p m U) u ≤ R u := by
      obtain ⟨i, hi⟩ := hA
      exact (RecordDefect.runMin_le (X := Xa p m U) u i).trans (pos_le_runMaxA_pos hi)
    have hRbound : R s ≤ Glue.sMaxM (Xa p m U) Finset.univ s := by
      change runMaxA p m U hA s ≤ _
      rw [← sMaxM_eq_runMaxA p m U A hA s, Glue.sMaxM, Glue.sMaxM, dif_pos hA, dif_pos Finset.univ_nonempty]
      exact Finset.sup'_le hA _ (fun i _ => Finset.le_sup' (fun i => LocalFluid.runMaxI (Xa p m U) i s) (Finset.mem_univ i))
    have hG : 0 ≤ G := sub_nonneg.mpr (by exact_mod_cast (hminR s).trans hRbound)
    have hGs : (R s : ℝ) - (Xmin p m U J hJ s : ℝ) ≤ G := by
      rw [hminEq s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩)]
      exact sub_le_sub_right (by exact_mod_cast hRbound) _
    have hupper := boundedGroupGap_le_spatial hp₀ hp₁ hL hr hk hkL hθ hlog hU hs (hst.trans ht)
      h.spatial hA hJ hA (fun i hi => pos_le_runMaxA_pos hi)
      ((hminEq s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩)).le.trans (hminR s)) (le_rfl : R s ≤ R s)
    have hnonneg : 0 ≤ boundedGroupGap p K θ m U t A J := by
      have hmin : Xmin p m U J hJ t ≤ Xmin p m U A hA t := by
        rw [hminEq t (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩)]
        exact Finset.le_inf' _ _ (fun i _ => RecordDefect.runMin_le (X := Xa p m U) t i)
      refine (sub_nonneg.mpr (by exact_mod_cast hmin)).trans
        (positionGap_le_boundedGroupGap hp₀.le hp₁.le hK hθ m U t hA hJ hmin)
    have hw := hsum hA hJ (show A ⊆ Jᶜ from le_rfl) hs hst ht hsep'
    have hcount := record_strictTimes_lower hp₀ hp₁ hm hL hr hU hA hAc hs hst ht hsepA hε h.trials
    have hcorr := sum_boundedCorrection_le_of_strictTimes hp₀ hp₁ hK hm U A hA hsepA hcount
    have hcorr' := hcorr
    have hRnonneg : 0 ≤ (R t : ℝ) - R s := by
      exact sub_nonneg.mpr (by exact_mod_cast runMaxA_mono (hA := hA) hst)
    have hrate := mul_le_mul_of_nonneg_right (linearStrictRate_le_group hp₀ hp₁ m hA) hRnonneg
    have hfac : (2 * p - 1) / (A.card : ℝ) ≤ 1 := by
      have hf : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr hA
      exact (div_le_one (by linarith only [hf])).mpr (by linarith only [hp₁, hf])
    have hfee := mul_le_mul_of_nonneg_right hfac
      (show 0 ≤ ε * (L : ℝ) + 2 * (m : ℝ) by positivity)
    have hmeet : d * ((R t : ℝ) - R s) ≤ C * G + ((T : ℝ) + 6) * (ε * (L : ℝ)) := by
      push_cast at hcorr'
      nlinarith only [hw, hcorr', hrate, hfee, hlarge, hnonneg, hupper, mul_le_mul_of_nonneg_left hGs hC]
    have hmin := h.minimum s t hs hst ht
    have htMin : (RecordDefect.runMin (Xa p m U) t : ℝ) ≤ R t := by exact_mod_cast hminR t
    have hRlower : v * ((t : ℝ) - s) ≤ ((R t : ℝ) - R s) + G + ε * (L : ℝ) := by
      rw [hminEq s (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩)] at hGs
      linarith only [hmin, htMin, hGs]
    have h₁ : (d * v) * ((t : ℝ) - s) ≤ (C + d) * G + ((T : ℝ) + 6 + d) * (ε * (L : ℝ)) := by
      nlinarith only [hmeet, mul_le_mul_of_nonneg_left hRlower hd.le]
    have h₂ : (t : ℝ) - s ≤ ((C + d) / (d * v)) * G + (((T : ℝ) + 6 + d) / (d * v)) * (ε * (L : ℝ)) := by
      have hh : (t : ℝ) - s ≤ ((C + d) * G + ((T : ℝ) + 6 + d) * (ε * (L : ℝ))) / (d * v) :=
        (le_div_iff₀ hdv).mpr (by nlinarith only [h₁])
      convert hh using 1
      ring
    exact h₂.trans (add_le_add (mul_le_mul_of_nonneg_right hCmeet hG) (herror _ hDmeet))

end Swarming.Diameter
