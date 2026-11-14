/-
# One measured bad event, exponentially small, off which the paper's block clauses hold

This file assembles the four measured lanes into **one** event with **one** `exf` profile, off
which the paper's local `BlkCoin.BlockClauses` hold:

    badEvent = SingleBad.badAll            (the deterministic universal family ∪ the ambient Γ-count)
             ∪ moveFailCanonAll            (the simultaneous windowed (locmove) failure, canonical geometry)
             ∪ {¬ runWindow …}             (the finite run event on the record window)

* `badAll` obeys `exf` by `exists_famBad_le_at` + `SingleBad.exists_measureReal_ambBadAll_le`;
* `moveFailCanonAll` obeys `2^N` times the per-group measured `(locmove)` bound
  (`WindowMeas.measureReal_moveFailCanonAll_le`), whose exponential windows are turned into the
  profile by `WindowLocal` and whose polynomial prefactor is absorbed by `WindowAbsorb`;
* `¬ runWindow` obeys `RunWindow.arrayMeasure_runWindow_compl_le_auto` (**no** clock-cutoff
  hypothesis), and its two terms are absorbed: the clock term because `r ≥ (T+3)L`, and the
  finite-run term because `Kc p L ≈ xOf L` from below and `(1-q)^{Kc p L} = exf c_Q L`.

Off `badEvent` and on the record carrier, `WindowBlock.blockClauses_of_not_bad` derives
`BlockClauses` at `Cfin`/`CTfin` from the *proved* canonical geometry.

## Exact scope (read this before quoting the result)

* `2m < N` is required — the record-clock tail and hence the run-window measurement are only
  available there (`RunWindow.recTimeA_tail_regime_empty` records the `N ≤ 2m` obstruction).  The
  result therefore **does not** cover `N ≤ 2m`, in particular not `N = m = 2`.
* The profile threshold has the explicit polynomial restriction `r ≤ L²` on the record level.
  It is needed **only** for the finite-run term: the union bound
  `N·(clockCut + TL + 3)·(1-q)^{Kc}` grows linearly in `r` (since `clockCut ~ r`), so no `exf`
  bound uniform in all `r` can be extracted from it.  The two run-window terms are kept verbatim
  inside the proof of `exists_badEvent_le` (the union bound is `h3` there); no separate
  unrestricted-`r` declaration is exposed, and this file makes no claim in that regime beyond
  the proved `RunWindow.arrayMeasure_runWindow_compl_le_auto`.
* Both sides are stated for a fixed `N`: `Cerr, CT, cT, L₀` may depend on `N, m, p, T`.  What is
  *not* assumed anywhere is a good event's probability, a stationary law, coalescence, or the
  velocity.  `RunWindow`, `MWin`, `SingleBad`, `LocOccDerived` and `LocalGoodFamily` remain the
  only probabilistic inputs, and every one of them is a proved measured statement.
-/
import Swarm.WindowBlock
import Swarm.RunWindowMeasured

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace WindowMain

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The single measured bad event of the windowed local clauses.** -/
noncomputable def badEvent (p : ℝ) (m : ℕ) (Cerr : ℝ) (r T L : ℕ) : Set (Array N) :=
  SingleBad.badAll (N := N) p m Cerr r T L
    ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
    ∪ {U : Array N | ¬ RunWindow.runWindow (N := N) p m r T L (AstarPos.Kc p L) U}

/-! ## 1. Absorbing the polynomial prefactors of the finite-run term -/

theorem ofNat_cast_le (T L : ℕ) :
    (((T + 3) * L : ℕ) : ℝ) + 1 ≤ ((T : ℝ) + 4) * ((L : ℝ) + 1) := by
  have hT : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  push_cast
  nlinarith

theorem clockCut_le_quad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) {m : ℕ} (hmN : 2 * m < N)
    {T r L : ℕ} (hrL : (r : ℝ) ≤ (L : ℝ) ^ 2) :
    ((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ)
      ≤ (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5) * ((L : ℝ) + 1) ^ 2 := by
  have hμ : 0 < RunWindow.runMu N p m := RunWindow.runMu_pos hp0 hmN
  have hcc := RunWindow.clockCut_le (N := N) hp0 m r hmN
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hcast : ((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ)
      = (RunWindow.clockCut N p m r : ℝ) + ((T : ℝ) * (L : ℝ) + 3) := by push_cast; ring
  rw [hcast]
  have hkey : 2 * (N : ℝ) * (r : ℝ) / RunWindow.runMu N p m
      ≤ 2 * (N : ℝ) / RunWindow.runMu N p m * ((L : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ hμ]
    have h1 : 2 * (N : ℝ) * (r : ℝ)
        ≤ 2 * (N : ℝ) * ((L : ℝ) ^ 2) := by
      have hN : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
      nlinarith
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : 2 * (N : ℝ) * ((L : ℝ) ^ 2)
        ≤ 2 * (N : ℝ) / RunWindow.runMu N p m * ((L : ℝ) + 1) ^ 2
            * RunWindow.runMu N p m := by
      field_simp
      nlinarith
    linarith
  have hrest : (T : ℝ) * (L : ℝ) + 3 ≤ ((T : ℝ) + 5) * ((L : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((L : ℝ) + 1), hL0, hT0]
  have hcoef : (0 : ℝ) ≤ 2 * (N : ℝ) / RunWindow.runMu N p m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (sq_nonneg ((L : ℝ) + 1)) hcoef]

/-- **The finite-run term is dominated by the profile**: `(1-q)^{Kc p L}` decays like
`xOf L` once the floor lower bound `Kc p L ≥ (ρ/2)·xOf L` is available. -/
theorem exists_pow_le_exfKc {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∃ cQ : ℝ, 0 < cQ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) ≤ LocalGoodAll.exf cQ L := by
  have hρ : (0 : ℝ) < 1 - (1 - p) / p := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hq0 : 0 < (1 - p) ^ (m - 1) :=
    pow_pos (by linarith : (0 : ℝ) < 1 - p) _
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hq1' : (1 - p) ^ (m - 1) < 1 := by
    have hm1 : 1 ≤ m - 1 := by omega
    have hle := pow_le_pow_of_le_one (by linarith : (0:ℝ) ≤ 1 - p) (by linarith) hm1
    have h1 : (1 - p) ^ 1 = 1 - p := pow_one _
    rw [h1] at hle
    linarith
  obtain ⟨Lx, hLx⟩ : ∃ Lx : ℕ, ∀ L ≥ Lx, 2 / (1 - (1 - p) / p) ≤ LocSumAct.xOf L := by
    have := LocSumAct.xOf_tendsto.eventually
      (eventually_ge_atTop (2 / (1 - (1 - p) / p)))
    exact eventually_atTop.1 this
  have hlog : Real.log (1 - (1 - p) ^ (m - 1)) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  refine ⟨-(Real.log (1 - (1 - p) ^ (m - 1))) * ((1 - (1 - p) / p) / 2), ?_,
    max Lx 1, fun L hL => ?_⟩
  · have := hρ
    nlinarith
  · have hLx' : Lx ≤ L := le_trans (le_max_left _ _) hL
    have hxge : 2 / (1 - (1 - p) / p) ≤ LocSumAct.xOf L := hLx L hLx'
    have hxnn : (0 : ℝ) ≤ LocSumAct.xOf L := LocalGoodAll.xOf_nonneg L
    have hKc : (1 - (1 - p) / p) / 2 * LocSumAct.xOf L ≤ (AstarPos.Kc p L : ℝ) := by
      have hle : LocSumAct.xOf L * (1 - (1 - p) / p) - 1
          ≤ (AstarPos.Kc p L : ℝ) := by
        have h := Nat.lt_floor_add_one (LocSumAct.xOf L * (1 - (1 - p) / p))
        have h2 : ((⌊LocSumAct.xOf L * (1 - (1 - p) / p)⌋₊ : ℕ) : ℝ)
            = (AstarPos.Kc p L : ℝ) := rfl
        rw [h2] at h
        linarith
      have hx2 : 1 ≤ LocSumAct.xOf L * (1 - (1 - p) / p) / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        have h2 : 2 ≤ LocSumAct.xOf L * (1 - (1 - p) / p) := by
          rw [div_le_iff₀ hρ] at hxge
          linarith
        linarith
      nlinarith
    exact WindowAbsorb.pow_le_exf hq0 hq1' (by linarith) hKc


theorem exists_badEvent_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) (hmN : 2 * m < N) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → (r : ℝ) ≤ (L : ℝ) ^ 2 →
        (arrayMeasure N).real (badEvent (N := N) p m Cerr r T L) ≤ CT * LocalGoodAll.exf cT L := by

  classical
  -- the deterministic local-good family at the shared `Cerr`
  obtain ⟨Cerr, cL, hCerr1, hcL, L₁, hbadLS, hccLS⟩ :=
    LocalGoodFamily.commonLocsumFacts (N := N) hp0 hp1 hm T
  obtain ⟨CTb, cTb, hCTb, hcTb, Lb, hboundFam⟩ :=
    LocalGoodFamily.exists_famBad_le_at (N := N) hp0 hp1 hm hT hN
      (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
      UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
      UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J UniversalFamily.grpAllFam_disj
      hCerr1 hcL hbadLS hccLS
  obtain ⟨CTa, ca, hCTa, hca, La, hboundA⟩ :=
    SingleBad.exists_measureReal_ambBadAll_le (N := N) (m := m) hp0.le hp1 (by omega) T
  obtain ⟨Lk, hLk⟩ := SingleBad.exists_Kc' hp0 hp1
  obtain ⟨cQ, hcQ, Lq, hpowQ⟩ := exists_pow_le_exfKc hp0 hp1 hm
  -- the rates
  have hμ : 0 < RunWindow.runMu N p m := RunWindow.runMu_pos (N := N) hp0 hmN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have := RunWindow.N_pos (N := N); exact_mod_cast this
  set cR : ℝ := ((T : ℝ) + 3) * RunWindow.runMu N p m / (64 * (N : ℝ)) with hcRdef
  have hcR : 0 < cR := by
    rw [hcRdef]; positivity
  set cE : ℝ := WindowMeas.rateEnv T N with hcEdef
  have hcE : 0 < cE := WindowMeas.rateEnv_pos T N
  set cMin : ℝ := min (min (min cTb ca) (min cE cL)) (min cR cQ) with hcMindef
  have hcMin : 0 < cMin := by
    rw [hcMindef]
    exact lt_min (lt_min (lt_min hcTb hca) (lt_min hcE hcL)) (lt_min hcR hcQ)
  set cT : ℝ := cMin / 2 with hcTdef
  have hcT : 0 < cT := by rw [hcTdef]; linarith
  have hltT : ∀ x ∈ ({cTb, ca, cE, cL, cR, cQ} : Finset ℝ), cT < x := by
    intro x hx
    have hx' : x = cTb ∨ x = ca ∨ x = cE ∨ x = cL ∨ x = cR ∨ x = cQ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hx0 : 0 < x := by
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcTb
      · exact hca
      · exact hcE
      · exact hcL
      · exact hcR
      · exact hcQ
    have hmin : cMin ≤ x := by
      rw [hcMindef]
      rcases hx' with h | h | h | h | h | h
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · subst h; simp
      · subst h; simp
    rw [hcTdef]; linarith
  have hcTb' : cT < cTb := hltT cTb (by simp)
  have hca' : cT < ca := hltT ca (by simp)
  have hcE' : cT < cE := hltT cE (by simp)
  have hcL' : cT < cL := hltT cL (by simp)
  have hcR' : cT < cR := hltT cR (by simp)
  have hcQ' : cT < cQ := hltT cQ (by simp)
  -- the four absorptions
  obtain ⟨M1, hM1, hM1ge, Lm1, hm1⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := CTb + CTa) (c₀ := min cTb ca) (cT := cT) (by linarith) hcT
    (lt_min hcTb' hca') 0
  obtain ⟨M2, hM2, hM2ge, Lm2, hm2⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) (c₀ := cE) (cT := cT)
    (by positivity) hcT hcE' 2
  obtain ⟨M3, hM3, hM3ge, Lm3, hm3⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * Cerr) (c₀ := cL) (cT := cT) (by positivity) hcT hcL' 0
  obtain ⟨M4, hM4, hM4ge, Lm4, hm4⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (N : ℝ) * (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5))
    (c₀ := cQ) (cT := cT) (by positivity) hcT hcQ' 2
  refine ⟨Cerr, hCerr1, M1 + M2 + M3 + M4 + 2 * (N : ℝ), cT, by positivity, hcT,
    L₁ + Lb + La + Lk + Lq + Lm1 + Lm2 + Lm3 + Lm4 + 2, ?_⟩
  · -- the measure bound
    intro L hL r hr hrL
    have hL₁ : L₁ ≤ L := by omega
    have hLb : Lb ≤ L := by omega
    have hLa : La ≤ L := by omega
    have hLk' : Lk ≤ L := by omega
    have hLq : Lq ≤ L := by omega
    have hLm1 : Lm1 ≤ L := by omega
    have hLm2 : Lm2 ≤ L := by omega
    have hLm3 : Lm3 ≤ L := by omega
    have hLm4 : Lm4 ≤ L := by omega
    have hL2 : 2 ≤ L := by omega
    have hL1 : 1 ≤ L := by omega
    -- (1) `badAll`
    have h1 : (arrayMeasure N).real (SingleBad.badAll (N := N) p m Cerr r T L)
        ≤ M1 * LocalGoodAll.exf cT L := by
      refine le_trans (measureReal_union_le (μ := arrayMeasure N)
        (UniversalFamily.univBad (N := N) p m Cerr r T L)
        (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
      refine le_trans (add_le_add (hboundFam L hLb r hr) (hboundA L hLa r hr)) ?_
      refine le_trans (LocalGoodAll.exf_two hCTb.le hCTa.le hcTb hca L) ?_
      simpa only [pow_zero, mul_one] using hm1 L hLm1
    -- (2) the canonical `(locmove)` union
    have h2 : (arrayMeasure N).real
        (WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
          (LocalGoodFamily.Cmax (N := N) p m)
          (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
          ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
        ≤ (M2 + M3) * LocalGoodAll.exf cT L := by
      have hmain := WindowMeas.measureReal_moveFailCanonAll_le (N := N) hp0 hp1 (m := m)
        (by omega) hT hCerr1 hcL hbadLS hccLS L (by omega) r hr
      rw [← hcEdef] at hmain
      refine le_trans hmain ?_
      have hpoly : ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
          ≤ ((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2 := by
        have h := ofNat_cast_le T L
        have h0 : (0 : ℝ) ≤ (((T + 3) * L : ℕ) : ℝ) + 1 := by positivity
        have h0' : (0 : ℝ) ≤ ((T : ℝ) + 4) * ((L : ℝ) + 1) := by positivity
        nlinarith only [h, h0, h0']
      have hsplit : (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (WindowMeas.rateEnv T N) L + Cerr * LocalGoodAll.exf cL L)
          ≤ ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L
            + ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L := by
        have e1 : (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L)
            ≤ ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
              * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by
          have hpos : (0 : ℝ) < LocalGoodAll.exf (WindowMeas.rateEnv T N) L :=
            WindowAbsorb.exf_pos _ _
          have hstep : 4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
              ≤ 4 * (((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2) := by
            nlinarith only [hpoly]
          calc (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2
                * LocalGoodAll.exf (WindowMeas.rateEnv T N) L)
              = (2 : ℝ) ^ N * (4 * ((((T + 3) * L : ℕ) : ℝ) + 1) ^ 2)
                * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by ring
            _ ≤ (2 : ℝ) ^ N * (4 * (((T : ℝ) + 4) ^ 2 * ((L : ℝ) + 1) ^ 2))
                * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by
                apply mul_le_mul_of_nonneg_right _ hpos.le
                exact mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
                * LocalGoodAll.exf (WindowMeas.rateEnv T N) L := by ring
        have e2 : (2 : ℝ) ^ N * (Cerr * LocalGoodAll.exf cL L)
            = ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L := by ring
        nlinarith only [e1, e2]
      refine le_trans hsplit ?_
      have hA := hm2 L hLm2
      have hB := hm3 L hLm3
      have h2' : ((2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) * ((L : ℝ) + 1) ^ 2
            * LocalGoodAll.exf (WindowMeas.rateEnv T N) L
          ≤ M2 * LocalGoodAll.exf cT L := by
        exact hA
      have h3' : ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L ≤ M3 * LocalGoodAll.exf cT L := by
        have := hB
        simp only [pow_zero, mul_one] at this ⊢
        exact this
      have : (0 : ℝ) < LocalGoodAll.exf cT L := WindowAbsorb.exf_pos _ _
      nlinarith only [h2', h3', this]
    -- (3) the run-window complement
    have h3 : (arrayMeasure N).real
        {U : Array N | ¬ RunWindow.runWindow (N := N) p m r T L (AstarPos.Kc p L) U}
        ≤ (2 * (N : ℝ) + M4) * LocalGoodAll.exf cT L := by
      have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
      have hr1 : 1 ≤ r := by
        have h1 : 1 * L ≤ (T + 3) * L := Nat.mul_le_mul_right L (by omega)
        omega
      have hrun := RunWindow.arrayMeasure_runWindow_compl_le_auto (N := N) (p := p) hp0 hp1
        m hm r T L (AstarPos.Kc p L) hK hmN hr1
      refine le_trans hrun ?_
      -- the clock term
      have hclock : 2 * (N : ℝ)
            * Real.exp (-((r : ℝ) * RunWindow.runMu N p m / (64 * (N : ℝ))))
          ≤ 2 * (N : ℝ) * LocalGoodAll.exf cT L := by
        have hexp : Real.exp (-((r : ℝ) * RunWindow.runMu N p m / (64 * (N : ℝ))))
            ≤ Real.exp (-cR * (L : ℝ)) := by
          apply Real.exp_le_exp.mpr
          rw [hcRdef]
          have hr' : ((T : ℝ) + 3) * (L : ℝ) ≤ (r : ℝ) := by
            have : (((T + 3) * L : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
            push_cast at this
            linarith
          have hden : (0 : ℝ) < 64 * (N : ℝ) := by positivity
          have hkey : ((T : ℝ) + 3) * (L : ℝ) ≤ (r : ℝ) := by
            have hc : (((T + 3) * L : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
            push_cast at hc
            linarith
          have hnum : ((T : ℝ) + 3) * RunWindow.runMu N p m * (L : ℝ)
              ≤ (r : ℝ) * RunWindow.runMu N p m := by nlinarith only [hkey, hμ]
          have h1 : ((T : ℝ) + 3) * RunWindow.runMu N p m / (64 * (N : ℝ)) * (L : ℝ)
              ≤ (r : ℝ) * RunWindow.runMu N p m / (64 * (N : ℝ)) := by
            have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hden)
            calc ((T : ℝ) + 3) * RunWindow.runMu N p m / (64 * (N : ℝ)) * (L : ℝ)
                = ((T : ℝ) + 3) * RunWindow.runMu N p m * (L : ℝ) / (64 * (N : ℝ)) := by ring
              _ ≤ (r : ℝ) * RunWindow.runMu N p m / (64 * (N : ℝ)) := hdiv
          have := neg_le_neg h1
          simpa only [neg_mul] using this
        have hexp2 : Real.exp (-cR * (L : ℝ)) ≤ LocalGoodAll.exf cT L :=
          WindowAbsorb.exp_neg_mul_le_exf hcT hcR'.le hL1
        have hposN : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (le_trans hexp hexp2) hposN
      -- the finite-run term
      have hpow : (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)
          ≤ LocalGoodAll.exf cQ L := hpowQ L hLq
      have hq0 : 0 ≤ (1 - p) ^ (m - 1) := by
        apply pow_nonneg; linarith
      have hq1 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hqnn : 0 ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      have hcut := clockCut_le_quad (N := N) hp0 (m := m) (T := T) hmN (r := r) (L := L) hrL
      have hpolycut : (N : ℝ) * (((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
          ≤ (N : ℝ) * (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5)
            * ((L : ℝ) + 1) ^ 2 := by
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith
      have hfin : (N : ℝ) * ((((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L))
          ≤ ((N : ℝ) * (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5))
              * ((L : ℝ) + 1) ^ 2 * LocalGoodAll.exf cQ L := by
        have hexpnn : (0 : ℝ) ≤ LocalGoodAll.exf cQ L := (WindowAbsorb.exf_pos cQ L).le
        have step1 : (N : ℝ) * ((((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
              * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L))
            ≤ (N : ℝ) * ((((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
              * LocalGoodAll.exf cQ L) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have step2 : (N : ℝ) * ((((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
              * LocalGoodAll.exf cQ L)
            = (N : ℝ) * (((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
              * LocalGoodAll.exf cQ L := by ring
        have step3 : (N : ℝ) * (((RunWindow.clockCut N p m r + T * L + 3 : ℕ) : ℝ))
              * LocalGoodAll.exf cQ L
            ≤ ((N : ℝ) * (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5)
                * ((L : ℝ) + 1) ^ 2) * LocalGoodAll.exf cQ L :=
          mul_le_mul_of_nonneg_right hpolycut hexpnn
        linarith [step1, step2, step3]
      have hfin2 : ((N : ℝ) * (2 * (N : ℝ) / RunWindow.runMu N p m + (T : ℝ) + 5))
            * ((L : ℝ) + 1) ^ 2 * LocalGoodAll.exf cQ L
          ≤ M4 * LocalGoodAll.exf cT L := by
        have := hm4 L hLm4
        simpa only [pow_zero, mul_one] using this
      have hpos : (0 : ℝ) < LocalGoodAll.exf cT L := WindowAbsorb.exf_pos _ _
      linarith [hclock, hfin, hfin2]
    -- assemble
    have hbad : badEvent (N := N) p m Cerr r T L
        = SingleBad.badAll (N := N) p m Cerr r T L
          ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
              (LocalGoodFamily.Cmax (N := N) p m)
              (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
              ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
          ∪ {U : Array N | ¬ RunWindow.runWindow (N := N) p m r T L (AstarPos.Kc p L) U} := rfl
    rw [hbad]
    have h12 := measureReal_union_le (μ := arrayMeasure N)
      (SingleBad.badAll (N := N) p m Cerr r T L)
      (WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
    have h123 := measureReal_union_le (μ := arrayMeasure N)
      (SingleBad.badAll (N := N) p m Cerr r T L
        ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L))
      {U : Array N | ¬ RunWindow.runWindow (N := N) p m r T L (AstarPos.Kc p L) U}
    have hexp := (WindowAbsorb.exf_pos cT L).le
    have hsum1 : M1 * LocalGoodAll.exf cT L + (M2 + M3) * LocalGoodAll.exf cT L
        + (2 * (N : ℝ) + M4) * LocalGoodAll.exf cT L
        = (M1 + M2 + M3 + M4 + 2 * (N : ℝ)) * LocalGoodAll.exf cT L := by ring
    rw [← hsum1]
    linarith [h123, h12, h1, h2, h3]

end WindowMain
