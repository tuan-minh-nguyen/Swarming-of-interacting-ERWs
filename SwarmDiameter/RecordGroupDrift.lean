import SwarmDiameter.MarkedSpatialTail
import SwarmDiameter.SeparatedGroupStep
import Swarm.LocOccCarrierAssembly
import Swarm.LocMaxWindow

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmRecordMeas.Actual SwarmMarks
open SepGroup.Model SwarmJointDrift LocGroupQ LocGroupSimul SiteWindow
open LocOccCarrierAssembly StoppedWindow
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- On the record interval, the accumulated conditional drift plus
`ε * L` bounds the change in the group observable on every separated
subinterval. The exceptional probability is at most `exp (-c * L ^ (1 / 3))`. -/
theorem record_group_drift_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
            (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
            ε * (L : ℝ) < WA p m U t I J hI hJ - WA p m U s I J hI hJ -
              ∑ u ∈ Finset.Ico s t, Cavg p m u I J U})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨_, _, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  obtain ⟨a, ha, hspatial⟩ := hlocal N (2 * T + 4) (show (0 : ℝ) < 1 by norm_num)
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let d := (ε / 2) ^ 2 / (4096 * (T : ℝ))
  have hTp : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
  have hd : 0 < d := by dsimp only [d]; positivity
  let b := min a (d / 2)
  have hb : 0 < b := lt_min ha (half_pos hd)
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hpoly := LocSumR1.eventually_poly_mul_exp_le
    (C := 2 * ((T : ℝ) + 1)) (by positivity) hd 3
  have hlarge := (Real.tendsto_exp_atTop.comp (htop.const_mul_atTop (half_pos hb))).eventually_ge_atTop 2
  refine ⟨b / 2, half_pos hb, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspatial, htop.eventually hpoly, hlarge]
    with L hL hsp hpL hlargeL
  intro r hr I J hI hJ hij
  let μ := arrayMeasure N
  let V := R L
  let B := 2 * V + 6
  let A := A0 r T L
  let n := T * L
  let K := I ∪ J
  have hK : K.Nonempty := hI.mono Finset.subset_union_left
  let S (u : ℕ) : Set (Array N) := {U | SepSet p m u I J U ∧
    EfixWin p m u J K hK A U ≤ B ∧ ∀ k ∈ K, A + 1 ≤ (X p m U u k).toNat}
  let E : Set (Array N) := {U | ∃ (i : Fin N) (y : ℕ),
    y ∈ Finset.Ico (A - 1) (A + Lw T L + 1) ∧ V < hof p (SwarmLogRatio.siteMarks p m U i) y}
  have hLp : (0 : ℝ) < L := by exact_mod_cast (zero_lt_one.trans_le hL)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hV : 1 ≤ V := Real.one_le_rpow hLr (by norm_num)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hn : 1 ≤ n := Nat.mul_le_mul hT hL
  have hδ : 0 < ε / 2 * (L : ℝ) := mul_pos (half_pos hε) hLp
  have hE : μ.real E ≤ Real.exp (-a * V) := by
    refine (measureReal_mono ?_ (measure_ne_top μ _)).trans (hsp (A - 1))
    rintro U ⟨i, y, hy, hf⟩
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Ico.mp hy
    refine Or.inl ⟨i, y - (A - 1), ?_, ?_⟩
    · have he : (2 * T + 4) * L = (2 * T + 2) * L + 2 * L := by ring
      dsimp only [Lw] at hy₂
      omega
    · rw [Nat.add_sub_of_le hy₁]
      exact hf
  have hS (u : ℕ) : MeasurableSet[posFilt N p m u] (S u) := by
    have hpos : MeasurableSet[posFilt N p m u]
        {U : Array N | ∀ k ∈ K, A + 1 ≤ (X p m U u k).toNat} := by
      rw [show {U : Array N | ∀ k ∈ K, A + 1 ≤ (X p m U u k).toNat} =
        ⋂ k ∈ K, {U : Array N | A + 1 ≤ (X p m U u k).toNat} by ext U; simp]
      refine MeasurableSet.biInter (Finset.countable_toSet K) fun k _ => ?_
      exact measurableSet_le measurable_const
        ((measurable_of_countable Int.toNat).comp (measurable_pos_posFilt p m k le_rfl))
    exact (measurableSet_sepSet p m u I J).inter
      ((measurableSet_le (measurable_EfixWin p m u J K hK A) measurable_const).inter hpos)
  have hSep (u : ℕ) : S u ⊆ {U | SepSet p m u I J U} := fun _ hU => hU.1
  have hFix (u : ℕ) (U : Array N) (hU : U ∈ S u) : EfixWin p m u J K hK A U ≤ B := hU.2.1
  have hPos (u : ℕ) (U : Array N) (hU : U ∈ S u) : ∀ k ∈ K,
      A + 1 ≤ (X p m U u k).toNat := hU.2.2
  let ξ (u : ℕ) := centeredGroupStep p m u I J hI hJ (S u)
  let Q := LocMart.psum ξ
  have hmTail := measureReal_record_centeredGroupStep_le hp₀ hp₁ I J hI hJ r L
    hS hSep hB hPos hFix hn hδ
  have hae (u : ℕ) : ∀ᵐ U ∂μ, U ∈ S u →
      WA p m U (u + 1) I J hI hJ - WA p m U u I J hI hJ ≤ ξ u U + Cavg p m u I J U :=
    (ae_centeredGroupStep_bounds hp₀ hp₁ I J hI hJ (hS u) (hSep u) hB.le
      (hPos u) (hFix u)).mono fun _ h => h.2
  have hall := ae_all_iff.mpr hae
  have hmem {U : Array N} (hU : U ∈ RecClockLG.recordCarrier p m r L)
      (hE : U ∉ E) {u : ℕ} (hu : recTimeA p m U r ≤ u) (hun : u ≤ recTimeA p m U r + n)
      (hsep : SepSet p m u I J U) : U ∈ S u := by
    have hrec := RecClockLG.recHyp_at_record hU
    have hlow := RecHyp_pos_ge hrec hu hun
    have hhigh := RecHyp_runMax_bounds hrec hu hun
    have hAeq : (A : ℤ) = (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) := by
      apply Int.ofNat_sub
      exact T2L_le_r hr
    have hD : (T + 2) * L = (T + 1) * L + L := by ring
    have hApos (k : Fin N) : (A : ℤ) + 1 ≤ X p m U u k := by
      have h := hlow k
      change (r : ℤ) - (((T + 1) * L : ℕ) : ℤ) ≤ X p m U u k at h
      rw [hAeq, hD, Nat.cast_add]
      omega
    have hP (k : Fin N) : A + 1 ≤ (X p m U u k).toNat := by
      have h := hApos k
      omega
    obtain ⟨i, hi, hlead⟩ := exists_leader_in_I I J hI hJ hsep
    have hiK : i ∈ K := Finset.mem_union_left _ hi
    have hiJ : i ∈ Jᶜ := Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp hij hi h)
    have hR := Rmax_le_leader I J hI hi hlead
    have hRM : A ≤ (runMax p m U i u).toNat := by
      have h := le_runMax_pos p m U u i
      have h' := hApos i
      omega
    have hcover (v : ℕ) (hv : A ≤ v + 1) (hvtop : v ≤ xTop p m u K hK U) :
        v ∈ Finset.Ico (A - 1) (A + Lw T L + 1) := by
      have htop := (xTop_le_succ_Rmax p m u K hK U).trans (Nat.succ_le_succ hR)
      have hi' := (hhigh i).2
      have hsum : A + Lw T L = r + T * L + 1 := by
        dsimp only [A, A0, Lw]
        have hLw : (2 * T + 2) * L = (T + 2) * L + T * L := by ring
        have hrr := T2L_le_r hr
        omega
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hh := hfix_of_locmax_window (p := p) (by linarith : p ≠ 0) hK
      (fun j y hy => le_of_not_gt (fun hh => hE ⟨j, y, hy, hh⟩)) hcover i
    exact ⟨hsep, EfixWin_le_of_window hp₀.le hp₁.le hK U hiK hiJ hR hRM hV hh,
      fun k _ => hP k⟩
  have hSub : ∀ᵐ U ∂μ, U ∈ RecClockLG.recordCarrier p m r L ∩ {U |
      ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + n ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
        ε * (L : ℝ) < WA p m U t I J hI hJ - WA p m U s I J hI hJ -
          ∑ u ∈ Finset.Ico s t, Cavg p m u I J U} →
      U ∈ E ∪ (RecClockLG.recordCarrier p m r L ∩
        stoppedMax Q (fun U => recTimeA p m U r) n (ε / 2 * (L : ℝ))) := by
    filter_upwards [hall] with U hU
    rintro ⟨hc, s, t, hs, hst, ht, hsep, hdev⟩
    by_cases hE : U ∈ E
    · exact Or.inl hE
    refine Or.inr ⟨hc, ?_⟩
    have hsum := Finset.sum_le_sum (s := Finset.Ico s t) fun u hu => by
      obtain ⟨hub, hut⟩ := Finset.mem_Ico.mp hu
      exact hU u (hmem hc hE (by omega) (by omega) (hsep u hu))
    rw [Finset.sum_Ico_sub (fun u => WA p m U u I J hI hJ) hst,
      Finset.sum_add_distrib] at hsum
    have hQ : (∑ u ∈ Finset.Ico s t, ξ u U) = Q t U - Q s U := by
      simp only [Q, LocMart.psum, Finset.sum_Ico_eq_sub _ hst]
    rw [hQ] at hsum
    let σ := recTimeA p m U r
    change ∃ k ≤ n, ε / 2 * (L : ℝ) ≤ |Q (σ + k) U - Q σ U|
    change σ ≤ s at hs
    change t ≤ σ + n at ht
    by_contra! hsmall
    have h₁ := hsmall (s - σ) (by omega)
    have h₂ := hsmall (t - σ) (by omega)
    rw [Nat.add_sub_cancel' hs] at h₁
    rw [Nat.add_sub_cancel' (hs.trans hst)] at h₂
    linarith [(abs_lt.mp h₁).1, (abs_lt.mp h₂).2]
  have hVcube : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V, R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hrate : Real.exp (-((ε / 2 * (L : ℝ)) ^ 2) / (4 * (n : ℝ) * (4 * B) ^ 2))
      ≤ Real.exp (-d * V) := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
    have hBV : 4 * B ≤ 32 * V := by dsimp only [B]; linarith
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBV 2)
      (show 0 ≤ (d * V) * (4 * (n : ℝ)) by positivity)
    calc
      _ = (d * V) * (4 * (n : ℝ)) * (4 * B) ^ 2 := by ring
      _ ≤ (d * V) * (4 * (n : ℝ)) * (32 * V) ^ 2 := he
      _ = _ := by rw [show (n : ℝ) = (T : ℝ) * L from Nat.cast_mul _ _, ← hVcube]
                  dsimp only [d]
                  field_simp
                  ring
  have hmart : μ.real (RecClockLG.recordCarrier p m r L ∩
        stoppedMax Q (fun U => recTimeA p m U r) n (ε / 2 * (L : ℝ)))
      ≤ Real.exp (-(d / 2) * V) := by
    refine hmTail.trans ?_
    have hn' : (n : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
      dsimp only [n]
      push_cast
      linarith
    calc
      _ ≤ 2 * (((T : ℝ) + 1) * L) * Real.exp (-d * V) := by gcongr
      _ = (2 * ((T : ℝ) + 1)) * V ^ 3 * Real.exp (-d * V) := by rw [hVcube]; ring
      _ ≤ _ := hpL
  refine (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hSub)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hE hmart).trans ?_))
  have h₁ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left a (d / 2))) (zero_le_one.trans hV))
  have h₂ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right a (d / 2))) (zero_le_one.trans hV))
  calc
    _ ≤ 2 * Real.exp (-b * V) := by linarith
    _ ≤ Real.exp ((b / 2) * V) * Real.exp (-b * V) :=
      mul_le_mul_of_nonneg_right hlargeL (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [V]; ring

/-- The separated-group bound in the manuscript's local estimates. -/
theorem record_separated_group_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty), Disjoint I J →
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
            (∀ u ∈ Finset.Ico s t, SepSet p m u I J U) ∧
            ε * (L : ℝ) < WA p m U t I J hI hJ - WA p m U s I J hI hJ})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨c, hc, h⟩ := record_group_drift_failure_le_cube_root hp₀ hp₁ hm N T hT hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with L hL
  intro r hr I J hI hJ hij
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hL r hr I J hI hJ hij)
  rintro U ⟨hU, s, t, hs, hst, ht, hsep, hdev⟩
  refine ⟨hU, s, t, hs, hst, ht, hsep, ?_⟩
  have hd : ∑ u ∈ Finset.Ico s t, Cavg p m u I J U ≤ 0 :=
    Finset.sum_nonpos fun u hu => cavg_nonpos hp₀.le hp₁.le m u U I J hI hij (hsep u hu)
  linarith

end Swarming.Diameter
