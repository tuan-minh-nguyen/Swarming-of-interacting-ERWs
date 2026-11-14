/-
# The single measured bad event of the windowed local clauses, for **every** `N ≥ 2`

`WindowMain.exists_badEvent_blockClauses` (`WindowFinal`) states: one event
`badEvent = badAll ∪ moveFailCanonAll ∪ {¬ runWindow}` with one profile `CT · exf cT L`, off which
(on the record carrier) the paper's `BlkCoin.BlockClauses` hold — but only for `2m < N` and
`r ≤ L²`.

This file removes the `2m < N` restriction.  The only place `WindowLe.exists_badEvent_le` used it
was the finite-run term: the record-clock tail `2·N·exp(−rμ/(64N))` and the cutoff
`⌈2Nr/μ⌉₊`, whose drift `μ = (2p−1)(N−2m)` is non-positive for `N ≤ 2m`.  Using the
**position-level** run event of `RunPosMeas` (`runWindowPos`, level `r + T·L + 1`) that term is
replaced by

    P(¬ runWindowPos) ≤ N·(r + T·L + 1)·(1−q)^{Kc p L} ,

which is all-N, has no clock term, and is *smaller* than the clock-cutoff expression it replaces
(`r + T·L + 1 ≤ ⌈2Nr/μ⌉₊ + T·L + 4` on the relevant regime).  The `r ≤ L²` absorption
(`N·(r+TL+1) ≤ N·(T+3)·(L+1)²`) is the same degree-2 polynomial absorption as before, so the
profile constants are of the same shape.

* `badEventPos` — the same event with `{¬ runWindowPos}` as the third component.
* `exists_badEventPos_le` — the profile `CT · exf cT L`, every `N ≥ 2`, `r ≤ L²` retained.
* `exists_badEventPos_blockClauses` — off `badEventPos` and on the record carrier, the paper's
  `BlockClauses` at `Cfin`/`CTfin`, every `N ≥ 2`.

Scope, displayed: `2 ≤ N` (all `N`, including `N ≤ 2m` and `N = m = 2`), `2 ≤ m`, `1/2 < p < 1`,
`T ≥ 1`, `(T+3)·L ≤ r`, and the explicit polynomial restriction `r ≤ L²` — which is *not*
removed here (it is needed for the profile, in the run term exactly as before).  No good event's
probability, no stationary law, no coalescence, no velocity is assumed.
-/
import Swarm.RunPosMeas
import Swarm.WindowLe

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

namespace WindowPosAllN

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 0. The event and its arithmetic -/

/-- **The single measured bad event, with the position-level run event.**  Identical to
`WindowMain.badEvent` except that the third component is `¬ runWindowPos` at the deterministic
level `r + T·L + 1`. -/
noncomputable def badEventPos (p : ℝ) (m : ℕ) (Cerr : ℝ) (r T L : ℕ) : Set (Array N) :=
  SingleBad.badAll (N := N) p m Cerr r T L
    ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
        (LocalGoodFamily.Cmax (N := N) p m)
        (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
        ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
    ∪ {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U}

/-- **The polynomial absorption of the position level**: `r ≤ L²` gives
`r + T·L + 1 ≤ (T+3)·(L+1)²`. -/
theorem runLevel_poly {r T L : ℕ} (hT : (0 : ℝ) ≤ (T : ℝ)) (hrL : (r : ℝ) ≤ (L : ℝ) ^ 2) :
    (((r + T * L + 1 : ℕ)) : ℝ) ≤ ((T : ℝ) + 3) * ((L : ℝ) + 1) ^ 2 := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hcast : (((r + T * L + 1 : ℕ)) : ℝ) = (r : ℝ) + (T : ℝ) * (L : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  have h1 : (L : ℝ) ≤ ((L : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : (L : ℝ) ^ 2 + 1 ≤ ((L : ℝ) + 1) ^ 2 * 3 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 hT
  nlinarith [h3, h2]

/-! ## 1. The profile, for every `N ≥ 2` -/

theorem exists_badEventPos_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → (r : ℝ) ≤ (L : ℝ) ^ 2 →
        (arrayMeasure N).real (badEventPos (N := N) p m Cerr r T L) ≤ CT * LocalGoodAll.exf cT L
    := by
  classical
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
  obtain ⟨cQ, hcQ, Lq, hpowQ⟩ := WindowMain.exists_pow_le_exfKc hp0 hp1 hm
  set cE : ℝ := WindowMeas.rateEnv T N with hcEdef
  have hcE : 0 < cE := WindowMeas.rateEnv_pos T N
  set cMin : ℝ := min (min (min cTb ca) (min cE cL)) cQ with hcMindef
  have hcMin : 0 < cMin := by
    rw [hcMindef]
    exact lt_min (lt_min (lt_min hcTb hca) (lt_min hcE hcL)) hcQ
  set cT : ℝ := cMin / 2 with hcTdef
  have hcT : 0 < cT := by rw [hcTdef]; linarith
  have hltT : ∀ x ∈ ({cTb, ca, cE, cL, cQ} : Finset ℝ), cT < x := by
    intro x hx
    have hx' : x = cTb ∨ x = ca ∨ x = cE ∨ x = cL ∨ x = cQ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hx0 : 0 < x := by
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact hcTb
      · exact hca
      · exact hcE
      · exact hcL
      · exact hcQ
    have hmin : cMin ≤ x := by
      rw [hcMindef]
      rcases hx' with h | h | h | h | h
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
    (C₁ := (N : ℝ) * ((T : ℝ) + 3))
    (c₀ := cQ) (cT := cT) (by positivity) hcT hcQ' 2
  refine ⟨Cerr, hCerr1, M1 + M2 + M3 + M4, cT, by positivity, hcT,
    L₁ + Lb + La + Lk + Lq + Lm1 + Lm2 + Lm3 + Lm4 + 2, ?_⟩
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
      have h := WindowMain.ofNat_cast_le T L
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
        ≤ M2 * LocalGoodAll.exf cT L := hA
    have h3' : ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L ≤ M3 * LocalGoodAll.exf cT L := by
      have := hB
      simpa only [pow_zero, mul_one] using this
    have hpos2 : (0 : ℝ) < LocalGoodAll.exf cT L := WindowAbsorb.exf_pos _ _
    nlinarith only [h2', h3', hpos2]
  -- (3) the position-level run-window complement: no clock term at all
  have h3 : (arrayMeasure N).real
      {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U}
      ≤ M4 * LocalGoodAll.exf cT L := by
    have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
    have hrun := WindowPos.arrayMeasure_runWindowPos_compl_le (N := N) (p := p) hp0 hp1 hm
      r T L (AstarPos.Kc p L) hK
    refine le_trans hrun ?_
    have hpow : (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)
        ≤ LocalGoodAll.exf cQ L := hpowQ L hLq
    have hqnn : (0 : ℝ) ≤ (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) := by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      have h2 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
      have h3 : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      positivity
    have hpoly : (N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ))
        ≤ ((N : ℝ) * ((T : ℝ) + 3)) * ((L : ℝ) + 1) ^ 2 := by
      have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1 := runLevel_poly (r := r) (T := T) (L := L) hTnn hrL
      nlinarith only [h1, hNnn]
    calc (N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L))
        = ((N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ)))
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) := by ring
      _ ≤ (((N : ℝ) * ((T : ℝ) + 3)) * ((L : ℝ) + 1) ^ 2)
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) :=
          mul_le_mul_of_nonneg_right hpoly hqnn
      _ ≤ (((N : ℝ) * ((T : ℝ) + 3)) * ((L : ℝ) + 1) ^ 2) * LocalGoodAll.exf cQ L :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ M4 * LocalGoodAll.exf cT L := hm4 L hLm4
  -- assemble
  have hbad : badEventPos (N := N) p m Cerr r T L
      = SingleBad.badAll (N := N) p m Cerr r T L
        ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
        ∪ {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U} :=
    rfl
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
    {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U}
  have hexp := (WindowAbsorb.exf_pos cT L).le
  have hsum1 : M1 * LocalGoodAll.exf cT L + (M2 + M3) * LocalGoodAll.exf cT L
      + M4 * LocalGoodAll.exf cT L
      = (M1 + M2 + M3 + M4) * LocalGoodAll.exf cT L := by ring
  rw [← hsum1]
  linarith [h123, h12, h1, h2, h3]


/-! ## 2. The same event measured for **all** `r ≥ (T+3)·L`: the `r`-dependence is one factor

`exists_badEventPos_le` restricts to `r ≤ L²` so that the run term's linear `r`-dependence can be
absorbed by a degree-2 polynomial in `L`.  This theorem keeps the exact scope `(T+3)·L ≤ r` for
*every* `r`, at the price of carrying that dependence explicitly: the measured profile of
`badEventPos` is a sum of one `L`-only profile (the two `badTwo` lanes) and the single run term
`N·(r + T·L + 1)·exf cQ L`.  So the whole `r`-dependence of the bad event is
`N·(r + T·L + 1)` on the finite-run lane — nothing else. -/
theorem exists_badEventPos_le_allR {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT cQ : ℝ, 0 < CT ∧ 0 < cT ∧ 0 < cQ ∧ ∃ L₀ : ℕ,
      ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (badEventPos (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L
            + ((N : ℝ) * (((r + T * L + 1 : ℕ)) : ℝ)) * LocalGoodAll.exf cQ L := by
  classical
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
  obtain ⟨cQ, hcQ, Lq, hpowQ⟩ := WindowMain.exists_pow_le_exfKc hp0 hp1 hm
  set cE : ℝ := WindowMeas.rateEnv T N with hcEdef
  have hcE : 0 < cE := WindowMeas.rateEnv_pos T N
  set cMin : ℝ := min (min (min cTb ca) (min cE cL)) cQ with hcMindef
  have hcMin : 0 < cMin := by
    rw [hcMindef]
    exact lt_min (lt_min (lt_min hcTb hca) (lt_min hcE hcL)) hcQ
  set cT : ℝ := cMin / 2 with hcTdef
  have hcT : 0 < cT := by rw [hcTdef]; linarith
  have hltT : ∀ x ∈ ({cTb, ca, cE, cL, cQ} : Finset ℝ), cT < x := by
    intro x hx
    have hx' : x = cTb ∨ x = ca ∨ x = cE ∨ x = cL ∨ x = cQ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hx0 : 0 < x := by
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact hcTb
      · exact hca
      · exact hcE
      · exact hcL
      · exact hcQ
    have hmin : cMin ≤ x := by
      rw [hcMindef]
      rcases hx' with h | h | h | h | h
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
  have hcQ' : cT < cQ := hltT cQ (by simp)
  obtain ⟨M1, hM1, hM1ge, Lm1, hm1⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := CTb + CTa) (c₀ := min cTb ca) (cT := cT) (by linarith) hcT
    (lt_min hcTb' hca') 0
  obtain ⟨M2, hM2, hM2ge, Lm2, hm2⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * 4 * ((T : ℝ) + 4) ^ 2) (c₀ := cE) (cT := cT)
    (by positivity) hcT hcE' 2
  obtain ⟨M3, hM3, hM3ge, Lm3, hm3⟩ := WindowAbsorb.exists_poly_mul_exf_le
    (C₁ := (2 : ℝ) ^ N * Cerr) (c₀ := cL) (cT := cT) (by positivity) hcT hcL' 0
  refine ⟨Cerr, hCerr1, M1 + M2 + M3, cT, cQ, by linarith, hcT, hcQ,
    L₁ + Lb + La + Lk + Lq + Lm1 + Lm2 + Lm3 + 2, ?_⟩
  intro L hL r hr
  have hL₁ : L₁ ≤ L := by omega
  have hLb : Lb ≤ L := by omega
  have hLa : La ≤ L := by omega
  have hLk' : Lk ≤ L := by omega
  have hLq : Lq ≤ L := by omega
  have hLm1 : Lm1 ≤ L := by omega
  have hLm2 : Lm2 ≤ L := by omega
  have hLm3 : Lm3 ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have h1 : (arrayMeasure N).real (SingleBad.badAll (N := N) p m Cerr r T L)
      ≤ M1 * LocalGoodAll.exf cT L := by
    refine le_trans (measureReal_union_le (μ := arrayMeasure N)
      (UniversalFamily.univBad (N := N) p m Cerr r T L)
      (Swarming.Enl.ambBadAll (N := N) p m (r : ℤ) T L)) ?_
    refine le_trans (add_le_add (hboundFam L hLb r hr) (hboundA L hLa r hr)) ?_
    refine le_trans (LocalGoodAll.exf_two hCTb.le hCTa.le hcTb hca L) ?_
    simpa only [pow_zero, mul_one] using hm1 L hLm1
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
      have h := WindowMain.ofNat_cast_le T L
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
        ≤ M2 * LocalGoodAll.exf cT L := hA
    have h3' : ((2 : ℝ) ^ N * Cerr) * LocalGoodAll.exf cL L ≤ M3 * LocalGoodAll.exf cT L := by
      have := hB
      simpa only [pow_zero, mul_one] using this
    have hpos2 : (0 : ℝ) < LocalGoodAll.exf cT L := WindowAbsorb.exf_pos _ _
    nlinarith only [h2', h3', hpos2]
  have h3 : (arrayMeasure N).real
      {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U}
      ≤ ((N : ℝ) * (((r + T * L + 1 : ℕ)) : ℝ)) * LocalGoodAll.exf cQ L := by
    have hK : 1 ≤ AstarPos.Kc p L := (hLk L hLk').1
    have hrun := WindowPos.arrayMeasure_runWindowPos_compl_le (N := N) (p := p) hp0 hp1 hm
      r T L (AstarPos.Kc p L) hK
    refine le_trans hrun ?_
    have hpow : (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L)
        ≤ LocalGoodAll.exf cQ L := hpowQ L hLq
    have hqnn : (0 : ℝ) ≤ (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) := by
      have h1 : (0 : ℝ) ≤ 1 - p := by linarith
      have h2 : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
      have h3 : (0 : ℝ) ≤ 1 - (1 - p) ^ (m - 1) := by linarith
      positivity
    calc (N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ) * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L))
        = ((N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ)))
            * (1 - (1 - p) ^ (m - 1)) ^ (AstarPos.Kc p L) := by ring
      _ ≤ ((N : ℝ) * (((r + T * L + 1 : ℕ) : ℝ))) * LocalGoodAll.exf cQ L :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbad : badEventPos (N := N) p m Cerr r T L
      = SingleBad.badAll (N := N) p m Cerr r T L
        ∪ WindowMeas.moveFailCanonAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) (RecClockLG.Astar r T L)
        ∪ {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U} :=
    rfl
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
    {U : Array N | ¬ WindowPos.runWindowPos (N := N) p m r T L (AstarPos.Kc p L) U}
  have hsum1 : M1 * LocalGoodAll.exf cT L + (M2 + M3) * LocalGoodAll.exf cT L
      = (M1 + M2 + M3) * LocalGoodAll.exf cT L := by ring
  rw [← hsum1]
  linarith [h123, h12, h1, h2, h3]

end WindowPosAllN

