import SwarmDiameter.MarkedSpatialTail
import Swarm.LocOccCarrierAssembly
import Swarm.ClockLocMove

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmRecordMeas.Actual SwarmMarks
open SepGroup.Model SwarmJointDrift LocGroupSimul LocOccCarrierAssembly
open LocMoveLocal LocMoveMart
open scoped ENNReal Topology

set_option autoImplicit false

namespace Swarming.Diameter

/-- On a separated subinterval, the maximum of the group potential over
the trailing group grows at least at unit rate up to an error of `ε * L`.
The exceptional probability on the record interval is at most
`exp (-c * L ^ (1 / 3))`. -/
theorem record_group_maximum_failure_le_cube_root
    {p : ℝ} {m : ℕ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (N T : ℕ) [Nonempty (Fin N)] (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (J : Finset (Fin N)) (hJ : J.Nonempty), Jᶜ.Nonempty →
        (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩ {U |
          ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
            (∀ u ∈ Finset.Ico s t, SepSet p m u Jᶜ J U) ∧
            Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε * (L : ℝ)})
          ≤ Real.exp (-c * (L : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨_, _, hlocal⟩ := arrayMeasure_local_hof_estimates hp₀ hp₁ hm
  obtain ⟨a, ha, hspatial⟩ := hlocal N (2 * T + 4) (show (0 : ℝ) < 1 by norm_num)
  let R (L : ℕ) := (L : ℝ) ^ (1 / 3 : ℝ)
  let d := ε ^ 2 / (16 * (T : ℝ))
  have hTp : (0 : ℝ) < T := by exact_mod_cast (zero_lt_one.trans_le hT)
  have hd : 0 < d := by dsimp only [d]; positivity
  let b := min a (d / 2)
  have hb : 0 < b := lt_min ha (half_pos hd)
  have htop : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hpoly := LocSumR1.eventually_poly_mul_exp_le
    (C := 2 * ((T : ℝ) + 1) ^ 2) (by positivity) hd 6
  have hlarge := (Real.tendsto_exp_atTop.comp (htop.const_mul_atTop (half_pos hb))).eventually_ge_atTop 2
  refine ⟨b / 2, half_pos hb, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspatial, htop.eventually hpoly, hlarge]
    with L hL hsp hpL hlargeL
  intro r hr J hJ hJc
  let μ := arrayMeasure N
  let V := R L
  let A := A0 r T L
  let n := T * L
  let E : Set (Array N) := {U | ∃ (i : Fin N) (y : ℕ),
    y ∈ Finset.Ico (A - 1) (A + Lw T L + 1) ∧ V < hof p (SwarmLogRatio.siteMarks p m U i) y}
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hV : 1 ≤ V := Real.one_le_rpow hLr (by norm_num)
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hn : 1 ≤ n := Nat.mul_le_mul hT hL
  have hδ : 0 < ε * (L : ℝ) := mul_pos hε (zero_lt_one.trans_le hLr)
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
  let Q := ClockLocMove.LG p m J hJ V
  let F := RecClockLG.recordCarrier (N := N) p m r L ∩
    StoppedWindow.stoppedWindow Q (fun U => recTimeA p m U r) n (ε * (L : ℝ))
  have hmain := ClockLocMove.measureReal_recordClock_LGpair_le (m := m) hp₀.le hp₁.le J hJ hVp r L n hn hδ
  have heq : ∀ᵐ U ∂μ, ∀ t, ClockLocMove.lTr p m J hJ V t U = LdM p m t J hJ V U :=
    ae_all_iff.mpr (ClockLocMove.ae_lTr_eq hp₀.le hp₁.le J hJ hVp.le)
  have hmax (s t : ℕ) : ∀ᵐ U ∂μ, s ≤ t →
      (∀ u ∈ Finset.Ico s t, GoodStep p m u J V U) →
      ((t - s : ℕ) : ℝ) + ∑ u ∈ Finset.Ico s t, LdM p m u J hJ V U
        ≤ Mnow p m t J hJ U - Mnow p m s J hJ U := by
    by_cases hst : s ≤ t
    · exact (Mnow_good_window_ge hp₀ hp₁ m J hJ V hst).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => False.elim (hst h)
  have hall := ae_all_iff.mpr (fun s => ae_all_iff.mpr (hmax s))
  have hsub : ∀ᵐ U ∂μ, U ∈ RecClockLG.recordCarrier p m r L ∩ {U |
      ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
        (∀ u ∈ Finset.Ico s t, SepSet p m u Jᶜ J U) ∧
        Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε * (L : ℝ)} →
      U ∈ E ∪ F := by
    filter_upwards [heq, hall] with U hU hmaxU
    rintro ⟨hrec, s, t, hs, hst, ht, hsep, hbad⟩
    by_cases hEU : U ∈ E
    · exact Or.inl hEU
    obtain ⟨i, hi⟩ := hJc
    have hh := RecClockLG.recHyp_at_record hrec
    have hA := A0_cast (T2L_le_r hr)
    have hAw := A0_add_Lw_cast (T2L_le_r hr)
    have hsum : (T + 2) * L = (T + 1) * L + L := by ring
    have hgood (u : ℕ) (hu : u ∈ Finset.Ico s t) : GoodStep p m u J V U := by
      obtain ⟨hus, hut⟩ := Finset.mem_Ico.mp hu
      refine goodStep_of_sep_of_leader_bound hp₀.le hp₁.le hJ hi (hsep u hu) ?_
      intro j hj z hz
      rw [Loccoord.hfix_omegaN_eq_hof (show p ≠ 0 by linarith)]
      apply le_of_not_gt
      intro hzV
      apply hEU
      refine ⟨i, z.toNat, ?_, hzV⟩
      have hlow := RecHyp_pos_ge hh (hs.trans hus) (show u ≤ recTimeA p m U r + T * L by omega) j
      have hM := (RecHyp_runMax_bounds hh (hs.trans hus) (show u ≤ recTimeA p m U r + T * L by omega) j).2
      have hpos : (A : ℤ) + 1 ≤ X p m U u j := by
        change (r : ℤ) - (((T + 1) * L : ℕ) : ℤ) ≤ X p m U u j at hlow
        change ((A0 r T L : ℕ) : ℤ) + 1 ≤ X p m U u j
        rw [hA, hsum, Nat.cast_add]
        omega
      have hhigh : X p m U u j ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) :=
        (le_runMax_pos p m U u j).trans hM
      have hzmem : z = X p m U u j ∨ z = X p m U u j + 1 ∨ z = X p m U u j - 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
      have hzlo : (A : ℤ) ≤ z := by rcases hzmem with rfl | rfl | rfl <;> omega
      have hzhi : z ≤ (r : ℤ) + ((T * L : ℕ) : ℤ) + 1 := by
        rcases hzmem with rfl | rfl | rfl <;> omega
      change ((A : ℕ) : ℤ) + ((Lw T L : ℕ) : ℤ) = _ at hAw
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hW := hmaxU s t hst hgood
    have hQ : (∑ u ∈ Finset.Ico s t, LdM p m u J hJ V U) = Q t U - Q s U := by
      simp only [Q, ClockLocMove.LG, LocMart.psum, ← Finset.sum_Ico_eq_sub _ hst, hU]
    rw [hQ] at hW
    refine Or.inr ⟨hrec, ClockLocMove.mem_stoppedWindow_of_pair hs hst ht ?_⟩
    have ha := neg_abs_le (Q t U - Q s U)
    linarith
  have hVcube : V ^ (3 : ℕ) = (L : ℝ) := by
    dsimp only [V, R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hrate : Real.exp (-(ε * (L : ℝ)) ^ 2 / (4 * (n : ℝ) * (2 * V) ^ 2))
      = Real.exp (-d * V) := by
    congr 1
    rw [show (n : ℝ) = (T : ℝ) * L from Nat.cast_mul _ _, ← hVcube]
    dsimp only [d]
    field_simp
    ring
  have hF : μ.real F ≤ Real.exp (-(d / 2) * V) := by
    refine hmain.trans ?_
    have hn' : (n : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
      dsimp only [n]
      push_cast
      linarith
    calc
      _ ≤ 2 * (((T : ℝ) + 1) * L) ^ 2 * Real.exp (-d * V) := by rw [hrate]; gcongr
      _ = (2 * ((T : ℝ) + 1) ^ 2) * V ^ 6 * Real.exp (-d * V) := by rw [← hVcube]; ring
      _ ≤ _ := hpL
  refine (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hE hF).trans ?_))
  have h₁ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left a (d / 2))) hVp.le)
  have h₂ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right a (d / 2))) hVp.le)
  calc
    _ ≤ 2 * Real.exp (-b * V) := by linarith
    _ ≤ Real.exp ((b / 2) * V) * Real.exp (-b * V) :=
      mul_le_mul_of_nonneg_right hlargeL (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [V]; ring

end Swarming.Diameter
