import Swarm.LocOccSingleWindow

open Finset Filter MeasureTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross
open Swarming.Enl Swarming.Enl.ProjLedger Swarming.Enl.VdriftAssembly
open SwarmMarks SwarmLogRatio LocOccCarrier LocOccCarrierAssembly SummedSlope.Model

set_option autoImplicit false

namespace Swarming.Diameter

variable {N : ℕ} [Nonempty (Fin N)]

/-- The occupation estimate on a record interval with a variable potential
bound and additive error. The squared potential bound controls the two
endpoint corrections. -/
theorem record_occupation_estimate_of_local_bounds
    {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin N} (hij : i ≠ j) {C : ℝ} (hC1 : 1 ≤ C)
    {L : ℕ} (hL : 1 ≤ L) {T r s0 s t : ℕ}
    {V E : ℝ} (hV : 1 ≤ V) (hVE : V ^ 2 ≤ E)
    (hr : (T + 3) * L ≤ r) (hs0s : s0 ≤ s) (hst : s ≤ t) (htT : t ≤ s0 + T * L) :
    ∀ᵐ U ∂(arrayMeasure N),
      U ∈ ActualRecordFiltration.recordPrefixBand (N := N) p m r s0 L →
      -- `(locsum)` on the window `[A0, A0+Lw)`
      (∀ a b : ℕ, A0 r T L ≤ a → b ≤ A0 r T L + Lw T L → a ≤ b →
        ∑ x ∈ Finset.Ico a b, (hof p (siteMarks p m U j) x) ^ 2
          ≤ 2 * C * ((b : ℝ) - (a : ℝ)) + E) →
      -- `(locmax)` on `[A0-1, A0+Lw)`: the left boundary site `A0-1` is what bounds `b_n`
      (∀ y ∈ Finset.Ico (A0 r T L - 1) (A0 r T L + Lw T L),
        hof p (siteMarks p m U j) y ≤ V) →
      -- the one-sided adapted projected `Qpl` window
      Qpl p m (1 / 8) i j s U - Qpl p m (1 / 8) i j t U ≤ E →
      -- the projected oscillation pair at the carrier's start site
      projH p m j t U ((trajectory p m U s).pos i) -
        projH p m j s U ((trajectory p m U s).pos i) ≤ E →
      ∑ u ∈ Finset.Ico s t,
          (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0)
        ≤ ((2 * C + Lc p m) + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + ((t : ℝ) - (s : ℝ)) / 8
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 1 + 1
              + 4 / (1 - aRec p m)) * E := by
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hVle : V ≤ E := (by nlinarith [mul_le_mul_of_nonneg_left hV hV0] : V ≤ V ^ 2).trans hVE
  have hE : 1 ≤ E := hV.trans hVle
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hβ0 : 0 ≤ E / (2 * C) := by positivity
  have hβE : E / (2 * C) ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC1) hE0]
  have hA1 : 1 ≤ A0 r T L := one_le_A0 hL hr
  filter_upwards [ae_forall_projH_eq_Hpot_of_le_record (N := N) (p := p) hp1 hp2
      (by linarith : p ≠ 0) m t j,
    ae_forall_projH_closed_form (N := N) (p := p) hp1 hp2 m (n := t) j,
    eRec_zero_bounds_ae (N := N) (p := p) hp1 hp2 m (n := t) j,
    LocOcc.ae_step_ledger_actual (N := N) hp1 hp2 hm hij (ε := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) s i j
      (eps := 1 / 8) (by norm_num),
    Swarming.Enl.ProjLedgerBridge.Zproj_eq_optional_projection (N := N) hp1 hp2 (m := m) t i j
      (eps := 1 / 8) (by norm_num)]
    with U hbelow hcl hbnd hledger hbrS hbrT
  intro hU hlsq hloc hqpl hoscPair
  -- ### the cell fields, from adapted record-carrier membership
  have hcell : ∀ u : ℕ, s0 ≤ u → u ≤ s0 + T * L →
      (A0 r T L : ℤ) ≤ (trajectory p m U u).pos i ∧
      (trajectory p m U u).pos i < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
      (A0 r T L : ℤ) ≤ runMax p m U j u ∧
      runMax p m U j u < (A0 r T L : ℤ) + (Lw T L : ℤ) ∧
      (A0 r T L : ℤ) ≤ runMax p m U i u ∧
      runMax p m U i u + 1 ≤ (A0 r T L : ℤ) + (Lw T L : ℤ) :=
    fun u h1 h2 => carrier_cell_window hU hr i j h1 h2
  have hA0nn : (0 : ℤ) ≤ (A0 r T L : ℤ) := by
    have : (1 : ℤ) ≤ (A0 r T L : ℤ) := by exact_mod_cast hA1
    linarith
  have hcellX : ∀ u : ℕ, s ≤ u → u ≤ t →
      A0 r T L ≤ ((trajectory p m U u).pos i).toNat ∧
        ((trajectory p m U u).pos i).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨h1', h2', -, -, -, -⟩ := hcell u (by omega) (by omega)
    constructor <;> omega
  have hcellMj : ∀ u : ℕ, s ≤ u → u ≤ t →
      A0 r T L ≤ (runMax p m U j u).toNat ∧ (runMax p m U j u).toNat < A0 r T L + Lw T L := by
    intro u h1 h2
    obtain ⟨-, -, hlo, hhi, -, -⟩ := hcell u (by omega) (by omega)
    constructor <;> omega
  have hcellMi : A0 r T L ≤ (runMax p m U i t).toNat ∧
      (runMax p m U i t).toNat + 1 ≤ A0 r T L + Lw T L := by
    obtain ⟨-, -, -, -, hlo, hhi⟩ := hcell t (by omega) htT
    constructor <;> omega
  -- ### nonnegativity and casts on the window
  have hnonneg : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i := by
    intro u h1 h2
    have hc := (hcell u (by omega) (by omega)).1
    linarith
  have hnonneg' : ∀ u : ℕ, s ≤ u → u ≤ t → 0 ≤ (trajectory p m U u).pos i :=
    fun u h1 h2 => hnonneg u h1 (by omega)
  have hcast : ∀ u : ℕ, s ≤ u → u ≤ t →
      ((((trajectory p m U u).pos i).toNat : ℕ) : ℤ) = (trajectory p m U u).pos i :=
    fun u h1 h2 => Int.toNat_of_nonneg (hnonneg u h1 h2)
  have hrecCast : (((runMax p m U j t).toNat : ℕ) : ℤ) = recVal j (prefOf p m t U) := by
    rw [runMax_eq_recVal]
    exact Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j t)
  -- ### the summed above-record slope fields, from the closed form
  have he1 : 0 ≤ eRec p m t j 0 U := le_trans zero_le_one hbnd.1
  have hslopeLo : ∀ x : ℕ, x < (runMax p m U j t).toNat →
      projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ)
        = hof p (siteMarks p m U j) x := by
    intro x hx
    have hx' : (x : ℤ) < recVal j (prefOf p m t U) := by
      rw [← hrecCast]
      exact_mod_cast hx
    have h := SummedSlope.Model.projH_step_below_eq (p := p) (m := m) hp1 hp2 (t := t) (U := U) hbelow hx'
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hslopeHi0 : ∀ x : ℕ, (runMax p m U j t).toNat ≤ x →
      0 ≤ projH p m j t U ((x + 1 : ℕ) : ℤ) - projH p m j t U ((x : ℕ) : ℤ) := by
    intro x hx
    set g := x - (runMax p m U j t).toNat with hg
    have hxe : (runMax p m U j t).toNat + g = x := by omega
    have h1 : ((x : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g : ℤ) := by
      conv_lhs => rw [← hxe]
      push_cast
      rw [hrecCast]
    have h2 : ((x + 1 : ℕ) : ℤ) = recVal j (prefOf p m t U) + ((g + 1 : ℕ) : ℤ) := by
      push_cast
      rw [h1]
      ring
    rw [h2, h1]
    exact SummedSlope.Model.projH_step_above_nonneg (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 g
  have hsumHi : ∀ u w : ℕ, (runMax p m U j t).toNat ≤ u → u ≤ w →
      projH p m j t U ((w : ℕ) : ℤ) - projH p m j t U ((u : ℕ) : ℤ)
        ≤ Lc p m * ((w : ℝ) - (u : ℝ)) + bRec p m t j U / (1 - aRec p m) := by
    intro u w hu huw
    set g1 := u - (runMax p m U j t).toNat with hg1
    set g2 := w - (runMax p m U j t).toNat with hg2
    have hue : (runMax p m U j t).toNat + g1 = u := by omega
    have hwe : (runMax p m U j t).toNat + g2 = w := by omega
    have hg12 : g1 ≤ g2 := by omega
    have h1 : ((u : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g1 : ℤ) := by
      conv_lhs => rw [← hue]
      push_cast
      rw [hrecCast]
    have h2 : ((w : ℕ) : ℤ) = recVal j (prefOf p m t U) + (g2 : ℤ) := by
      conv_lhs => rw [← hwe]
      push_cast
      rw [hrecCast]
    have hR : ((w : ℝ) - (u : ℝ)) = ((g2 : ℝ) - (g1 : ℝ)) := by
      conv_lhs => rw [← hwe, ← hue]
      push_cast
      ring
    have hmain := SummedSlope.Model.projH_sum_above_le (p := p) (m := m) hp1 hp2 (t := t) (U := U) hcl he1 hg12
    have hdef : eRec p m t j 0 U / (1 - aRec p m) ≤ bRec p m t j U / (1 - aRec p m) :=
      div_le_div_of_nonneg_right hbnd.2 (le_of_lt (one_sub_aRec_pos hp1 hp2 m))
    rw [hR, h1, h2]
    linarith [hmain, hdef]
  -- ### the additive defect from `b_n` and the `(locmax)` cap
  have hbrec : bRec p m t j U ≤ V + 2 := by
    refine SummedSlope.Model.bRec_le_succ_cap (p := p) (m := m) hp1 hp2 (j := j) (t := t) (U := U)
      (A := A0 r T L) (Mv := Lw T L) (V := V) hA1 hV ?_ hloc
    rw [← runMax_eq_recVal]
    exact hcellMj t hst le_rfl
  have hCaddL : bRec p m t j U / (1 - aRec p m)
      ≤ (4 / (1 - aRec p m)) * E := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith [hVle, hE]) (one_sub_aRec_pos hp1 hp2 m).le
  have hCa : (0 : ℝ) ≤ bRec p m t j U / (1 - aRec p m) := by
    have hden : (0 : ℝ) < 1 - aRec p m := one_sub_aRec_pos hp1 hp2 m
    have h3 : (0 : ℝ) < bRec p m t j U := by linarith [Swarming.Enl.three_le_bRec hp1 hp2 m t j U]
    positivity
  -- ### the remaining fields
  have hCJ0 : (0 : ℝ) ≤ CJc p m := CJc_nonneg hp1 hp2 m
  have hKF0 : (0 : ℝ) ≤ KFc p m := KFc_nonneg hp1 hp2 m
  have hoccP : ∀ u : ℕ, s ≤ u → u < t →
      SwarmOcc.occInd (fun r => (trajectory p m U r).pos i) (fun r => runMax p m U j r) u
        = if ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat then (1 : ℝ) else 0 :=
    fun u h1 h2 => LocOccEnd.occInd_eq_toNat_toNat (p := p) m U (hnonneg' u h1 (le_of_lt h2))
  have hcap : ∀ u : ℕ, s ≤ u → u ≤ t →
      (hof p (siteMarks p m U j) ((runMax p m U j u).toNat)) ^ 2 ≤ (V) ^ 2 := by
    intro u h1 h2
    have hm := hcellMj u h1 h2
    have hloc' : ∀ y ∈ Finset.Ico (A0 r T L) (A0 r T L + Lw T L),
        hof p (siteMarks p m U j) y ≤ V := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
      exact hloc y (Finset.mem_Ico.mpr ⟨by omega, hy2⟩)
    exact hof_sq_record_le (N := N) hp1 hp2 (m := m) (U := U) (j := j) u
      (A := A0 r T L) (Mv := Lw T L) (V := V) hV0 hloc'
      (Finset.mem_Ico.mpr ⟨hm.1, hm.2⟩)
  -- ### the two endpoint decompositions
  have hZs : Zproj p m (1 / 8) i j s U
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s) := by
    rw [← hbrS]
    show Swarming.Enl.Zproj p m (1 / 8) i j U s
      = projH p m j s U ((((trajectory p m U s).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
            ((trajectory p m U s).pos i - runMax p m U j s)
    rw [hcast s le_rfl (by omega)]
    rfl
  have hZt : Zproj p m (1 / 8) i j t U
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t) := by
    rw [← hbrT]
    show Swarming.Enl.Zproj p m (1 / 8) i j U t
      = projH p m j t U ((((trajectory p m U t).pos i).toNat : ℕ) : ℤ)
        - SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
            ((trajectory p m U t).pos i - runMax p m U j t)
    rw [hcast t hst le_rfl]
    rfl
  -- ### the summed `(lococc)` bound on the `occInd` carrier
  have hcore : ∑ u ∈ Finset.Ico s t,
        SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u
      ≤ (2 * C + Lc p m + 2 * CJc p m * (2 * C) + 1) *
            ((((runMax p m U i t).toNat : ℝ) - ((runMax p m U i s).toNat : ℝ))
              + (((runMax p m U i s).toNat : ℝ) - (((trajectory p m U s).pos i).toNat : ℝ))
              + max 0 (((runMax p m U i s).toNat : ℝ) - ((runMax p m U j s).toNat : ℝ)))
          + 1 / 8 * ((t : ℝ) - (s : ℝ))
          + (2 * C + 1 + 2 * KFc p m + 4 * CJc p m * (2 * C) + 2 * 1 + 1
              + 4 / (1 - aRec p m)) * E :=
    SummedSlope.lococc_summed
      (X := fun u => ((trajectory p m U u).pos i).toNat)
      (Mi := fun u => (runMax p m U i u).toNat)
      (Mj := fun u => (runMax p m U j u).toNat)
      (occ := fun u => SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
        (fun r => runMax p m U j r) u)
      (J := fun u => Jcorr p m (1 / 8) i j U u)
      (Z := fun u => Zproj p m (1 / 8) i j u U)
      (Q := fun u => Qpl p m (1 / 8) i j u U)
      (H := fun t y => projH p m j t U (y : ℤ))
      (Fs := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m s j U)
        ((trajectory p m U s).pos i - runMax p m U j s))
      (Ft := SwarmOcc.Fcorr (aRec p m) (1 / 8) (bRec p m t j U)
        ((trajectory p m U t).pos i - runMax p m U j t))
      (h := fun x => hof p (siteMarks p m U j) x)
      (wt := fun x => (hof p (siteMarks p m U j) x) ^ 2)
      (A := A0 r T L) (Lw := Lw T L) (K := 2 * C) (β := E / (2 * C))
      (Kp := Lc p m) (CH := 1) (KQ := 1) (KF := KFc p m) (CJ := CJc p m)
      (ε := 1 / 8) (L34 := E) (Cadd := bRec p m t j U / (1 - aRec p m))
      (CaddK := 4 / (1 - aRec p m))
      hst hoccP hledger hZs hZt
      (fun x => LocOccEnd.hof_nonneg hp1 hp2 (siteMarks p m U j) x)
      (fun x => le_refl ((hof p (siteMarks p m U j) x) ^ 2))
      hslopeLo hslopeHi0 hsumHi
      (by
        have he : 2 * C * (E / (2 * C)) = E := by field_simp
        rwa [he])
      (by rw [hcast s le_rfl hst, one_mul]; exact hoscPair)
      (by rw [one_mul]; linarith)
      (LocOccEnd.abs_Fcorr_endpoint_le hp1 hp2 (ε := 1 / 8) (i := i) (j := j)
        (by norm_num) U s ((hcap s le_rfl hst).trans hVE))
      (LocOccEnd.abs_Fcorr_endpoint_le hp1 hp2 (ε := 1 / 8) (i := i) (j := j)
        (by norm_num) U t ((hcap t hst le_rfl).trans hVE))
      (fun nx => Jstruct_all (N := N) hp1 hp2 (m := m) (i := i) (j := j) U nx)
      (fun nx => runMax_toNat_mono (le_of_lt (Nat.lt_succ_self nx)))
      (fun nx => runMax_toNat_step nx)
      (fun nx h1 h2 =>
        calc ((trajectory p m U (nx + 1)).pos i).toNat
            ≤ (runMax p m U i (nx + 1)).toNat :=
              pos_toNat_le_runMax (hnonneg' (nx + 1) (by omega) (by omega))
          _ ≤ (runMax p m U i t).toNat := runMax_toNat_mono (by omega))
      (runMax_toNat_mono hst)
      (pos_toNat_le_runMax (hnonneg' s (le_refl s) hst))
      (pos_toNat_le_runMax (hnonneg' t hst (le_refl t)))
      (hcellX s le_rfl (by omega)).1
      (hcellMj s le_rfl (by omega)).1
      (le_of_lt (hcellX t hst le_rfl).2)
      hcellMi.2
      (le_of_lt (hcellMj t hst le_rfl).2)
      (by linarith) hβ0 (Lc_nonneg hp1 hp2 m) hCJ0 (by norm_num) hKF0 (by norm_num)
      hE0 hE hβE hCa hCaddL
  -- ### back to the paper's literal indicator `1{X_u^i <= M_u^j}`
  have hsum : (∑ u ∈ Finset.Ico s t,
        (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0))
      = ∑ u ∈ Finset.Ico s t,
          SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
            (fun r => runMax p m U j r) u := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hu
    have hnn := hnonneg' u h1 (le_of_lt h2)
    have hiff := LocOccEnd.toNat_le_toNat_iff hnn (zero_le_runMax p m U j u)
    by_cases h : ((trajectory p m U u).pos i).toNat ≤ (runMax p m U j u).toNat
    · have hA1 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 1 :=
        if_pos (hiff.mp h)
      have hB1 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 1 := by rw [hoccP u h1 h2, if_pos h]
      rw [hA1, hB1]
    · have hA0 : (if (trajectory p m U u).pos i ≤ runMax p m U j u then (1 : ℝ) else 0) = 0 :=
        if_neg (fun hc => h (hiff.mpr hc))
      have hB0 : SwarmOcc.occInd (fun r => (trajectory p m U r).pos i)
          (fun r => runMax p m U j r) u = 0 := by rw [hoccP u h1 h2, if_neg h]
      rw [hA0, hB0]
  rw [hsum]
  have hcoef : (1 / 8 : ℝ) * ((t : ℝ) - (s : ℝ)) = ((t : ℝ) - (s : ℝ)) / 8 := by ring
  rw [hcoef] at hcore
  exact hcore

end Swarming.Diameter
