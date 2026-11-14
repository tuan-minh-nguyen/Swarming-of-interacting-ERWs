/-
# deriving the paper's `(lococc)` premise from the measured universal event

## What this file does

* `LocalFluid.LocOcc (Xa p m U) (tauA p m U) Cfin (CTtot p m T Cerr) T L r` — the paper's
  `(lococc)` display at the common coefficient `Cfin`, and
* `PaperBlock.MoveCarrier` — the `(locmax)` good-window content for `(locmove)`.

This file discharges the **first** of these, and nothing else, off the *same* measured event.
The `(lococc)` display itself is a theorem of the public martingale lane: on `recordCarrier`
and off the finite-family bad event, `OccPaperPointwise.familyGood_lococcPaper_expanded` gives
the paper's display with honest `ℤ` casts, coefficient `Kocc = PaperBlock.Cocc` and remainder
coefficient `LocOccPaperScale.CTocc`.  What was missing is the *dictionary* between that display
and the tightness lane's `LocalFluid.LocOcc`:

* the record-dependent bracket of the display is *definitionally* `occTerm + occGap` once
  `LocalFluid.runMaxI` is identified with the paper's `M^i_n` (`PaperBlock.runMaxI_eq`) and
  `Xa` with `trajectory.pos` (`SepGroup.Model.X_apply`);
* the display's `(t - s)/8` must be read as `((n - τ_r)/8)` (`Nat.cast_sub`);
* the display's coefficient `Cocc` is `≤ Cfin = max paperC Cocc`, and the bracket it multiplies
  is nonnegative (`runMaxI` is monotone in time and dominates the position), so the coefficient
  transfer is monotone;
* the display's remainder coefficient `CTocc` is **not** dominated by `CTtot`, so one common
  error coefficient `CTfin = max CTtot CTocc` is introduced.  This is the only change to the
  paper's constants: `CTfin` depends on `p, m, T` and `Cerr` only — not on `N`, not on `L`, not on
  the walker group — and it is *proved* to bound both coefficients.  A consumer that chooses its
  block size and window (`B`, `T`) existentially per `N`, as `ProfileBridge.CubicBlockClauses`
  does, absorbs the change by raising `T`; a consumer with a fixed `T` would additionally need
  `CTocc ≤ CTtot`, which is not claimed.

## What is *not* claimed

* `PaperBlock.MoveCarrier` is retained as an explicit premise of the final bundle, exactly as
  before.  No positivity or probability statement about it is made here.
* No new probabilistic estimate is added: the only null set is `UniversalFamily.univBad`.
* No coalescence, block probability, tightness, invariant law, velocity or `MainClaim`.
-/
import Swarm.PaperBlock
import Swarm.OccPaperPointwise
import Swarm.UniversalFamily

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open SepGroup RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs

namespace LocOccDerived

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. One common coefficient in front of `L^{3/4}` -/

/-- **The `(lococc)` remainder coefficient is a `T`-dependent constant and can be absorbed.**
`CTtot` is the maximum of the `(locmove)`, `(loccoord)` and `(locgroup)` remainders; the
`(lococc)` display of the martingale lane produces `CTocc`.  The paper allows one `C_T` for all
clauses, so the honest common choice is the maximum of the two.  `CTfin` depends on
`N, m, p, T` (through `Cerr`) only — not on `L`, not on the walker group. -/
noncomputable def CTfin (p : ℝ) (m T : ℕ) (Cerr : ℝ) : ℝ :=
  max (PaperBlock.CTtot p m T Cerr) (LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T)

theorem CTtot_le_CTfin (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    PaperBlock.CTtot p m T Cerr ≤ CTfin p m T Cerr := le_max_left _ _

theorem CTocc_le_CTfin (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T ≤ CTfin p m T Cerr :=
  le_max_right _ _

theorem three_le_CTfin (p : ℝ) (m T : ℕ) (Cerr : ℝ) :
    (3 : ℝ) ≤ CTfin p m T Cerr :=
  le_trans (PaperBlock.three_le_CTtot p m T Cerr) (CTtot_le_CTfin p m T Cerr)

theorem CTfin_pos (p : ℝ) (m T : ℕ) (Cerr : ℝ) : 0 < CTfin p m T Cerr :=
  lt_of_lt_of_le (by norm_num) (three_le_CTfin p m T Cerr)

/-- The `(lococc)` coefficient of the public display **is** `PaperBlock.Cocc`. -/
theorem Kocc_Ccan_eq_Cocc (p : ℝ) (m : ℕ) :
    LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m) = PaperBlock.Cocc p m := rfl

theorem Kocc_Ccan_le_Cfin (p : ℝ) (m : ℕ) :
    LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m) ≤ PaperBlock.Cfin (N := N) p m := by
  rw [Kocc_Ccan_eq_Cocc]
  exact le_max_right _ _

/-- **The explicit `L34`/`L_w` remainder is dominated by the single coefficient `CTfin`.**

`OccPaperPointwise.L34_le_CTocc` absorbs the display's `L34 L (Lw T L)` remainder into
`CTocc · L^{3/4}` (with the canonical `Lw T L = (2T+2)L+1`); composing it with
`CTocc ≤ CTfin` gives the paper's single `C_T L^{3/4}`. -/
theorem L34_absorbed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m T : ℕ} {L : ℕ}
    (hL : 1 ≤ L) {Cerr : ℝ} :
    (2 * LocOccSiteRate.Ccan p m + 1 + 2 * KFc p m
        + 4 * CJc p m * (2 * LocOccSiteRate.Ccan p m) + 2 * 2 + 1 + 4 / (1 - aRec p m))
        * L34 L (Lw T L)
      ≤ CTfin p m T Cerr * ((L : ℝ) ^ (3 / 4 : ℝ)) :=
  le_trans (OccPaperPointwise.L34_le_CTocc hp0 hp1 (LocOccSiteRate.one_le_Ccan p m) T hL)
    (mul_le_mul_of_nonneg_right (CTocc_le_CTfin p m T Cerr)
      (Real.rpow_nonneg (Nat.cast_nonneg L) (3 / 4 : ℝ)))

/-! ## 2. The dictionary between the display and `LocalFluid.LocOcc` -/

/-- The display's `toNat`-free record bracket is `occTerm + occGap`. -/
theorem occTerm_add_occGap_eq {p : ℝ} {m : ℕ} {U : Array N} (i j : Fin N) (r n : ℕ) :
    LocalFluid.occTerm (PaperBlock.Xa p m U) i (PaperBlock.tauA p m U r) n
        + LocalFluid.occGap (PaperBlock.Xa p m U) i j (PaperBlock.tauA p m U r)
      = (((Swarming.Trajectory.runMax p m U i n : ℤ) : ℝ)
          - ((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ))
        + (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
          - (((trajectory p m U (PaperBlock.tauA p m U r)).pos i : ℤ) : ℝ))
        + max 0 (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
          - ((Swarming.Trajectory.runMax p m U j (PaperBlock.tauA p m U r) : ℤ) : ℝ)) := by
  simp only [LocalFluid.occTerm, LocalFluid.occGap, PaperBlock.runMaxI_eq, PaperBlock.tauA,
    PaperBlock.Xa, SepGroup.Model.X_apply]

/-- The display's record bracket is nonnegative, so the coefficient transfer is monotone. -/
theorem record_bracket_nonneg {p : ℝ} {m : ℕ} {U : Array N} (i j : Fin N) {r n : ℕ}
    (hn : PaperBlock.tauA p m U r ≤ n) :
    (0 : ℝ) ≤ (((Swarming.Trajectory.runMax p m U i n : ℤ) : ℝ)
          - ((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ))
        + (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
          - (((trajectory p m U (PaperBlock.tauA p m U r)).pos i : ℤ) : ℝ))
        + max 0 (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
          - ((Swarming.Trajectory.runMax p m U j (PaperBlock.tauA p m U r) : ℤ) : ℝ)) := by
  have hmono : ((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
      ≤ ((Swarming.Trajectory.runMax p m U i n : ℤ) : ℝ) := by
    have h1 := LocalFluid.runMaxI_mono (PaperBlock.Xa p m U) i hn
    rw [PaperBlock.runMaxI_eq, PaperBlock.runMaxI_eq] at h1
    exact_mod_cast h1
  have hpos : (((trajectory p m U (PaperBlock.tauA p m U r)).pos i : ℤ) : ℝ)
      ≤ ((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ) := by
    have h2 := LocalFluid.le_runMaxI (PaperBlock.Xa p m U) i (PaperBlock.tauA p m U r)
    rw [PaperBlock.runMaxI_eq] at h2
    have h3 : PaperBlock.Xa p m U i (PaperBlock.tauA p m U r)
        = (trajectory p m U (PaperBlock.tauA p m U r)).pos i := by
      simp only [PaperBlock.Xa, SepGroup.Model.X_apply]
    rw [h3] at h2
    exact_mod_cast h2
  have hgap : (0 : ℝ) ≤ max 0 (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
      - ((Swarming.Trajectory.runMax p m U j (PaperBlock.tauA p m U r) : ℤ) : ℝ)) :=
    le_max_left _ _
  linarith

/-- **`(lococc)` in the tightness lane's shape, from the paper-shape display.**

This is the deterministic conversion.  The display is consumed exactly in the shape produced by
`OccPaperPointwise.familyGood_lococcPaper_expanded`; no hypothesis on the display's content is
added, and the record/shift casts carry the proof that the window is nonempty (`hn`). -/
theorem locOcc_of_display {p : ℝ} {m : ℕ} {T L r : ℕ} {Cerr : ℝ} {U : Array N}
    (hL : 1 ≤ L)
    (hdisp : ∀ (q : Fin N × Fin N), q ∈ offDiag (N := N) →
      ∀ s t : ℕ, recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
        ∑ u ∈ Finset.Ico s t,
            (if (trajectory p m U u).pos q.1 ≤ Swarming.Trajectory.runMax p m U q.2 u
              then (1 : ℝ) else 0)
          ≤ LocOccPaperScale.Kocc p m (LocOccSiteRate.Ccan p m) *
              ((((Swarming.Trajectory.runMax p m U q.1 t : ℤ) : ℝ)
                  - ((Swarming.Trajectory.runMax p m U q.1 s : ℤ) : ℝ))
                + (((Swarming.Trajectory.runMax p m U q.1 s : ℤ) : ℝ)
                  - (((trajectory p m U s).pos q.1 : ℤ) : ℝ))
                + max 0 (((Swarming.Trajectory.runMax p m U q.1 s : ℤ) : ℝ)
                  - ((Swarming.Trajectory.runMax p m U q.2 s : ℤ) : ℝ)))
            + ((t : ℝ) - (s : ℝ)) / 8
            + LocOccPaperScale.CTocc p m (LocOccSiteRate.Ccan p m) T *
                ((L : ℝ) ^ (3 / 4 : ℝ))) :
    LocalFluid.LocOcc (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (PaperBlock.Cfin (N := N) p m) (CTfin p m T Cerr) T L r := by
  intro i j hij n hn hnT
  have hmain := hdisp (i, j) (LocOccAllPairs.mem_offDiag.2 hij)
    (PaperBlock.tauA p m U r) n le_rfl hn hnT
  -- the target, written in the display's own vocabulary
  have hgoal : (∑ u ∈ Finset.Ico (PaperBlock.tauA p m U r) n,
        (if (trajectory p m U u).pos i ≤ Swarming.Trajectory.runMax p m U j u
          then (1 : ℝ) else 0))
      ≤ PaperBlock.Cfin (N := N) p m *
          ((((Swarming.Trajectory.runMax p m U i n : ℤ) : ℝ)
              - ((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ))
            + (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
              - (((trajectory p m U (PaperBlock.tauA p m U r)).pos i : ℤ) : ℝ))
            + max 0 (((Swarming.Trajectory.runMax p m U i (PaperBlock.tauA p m U r) : ℤ) : ℝ)
              - ((Swarming.Trajectory.runMax p m U j (PaperBlock.tauA p m U r) : ℤ) : ℝ)))
        + ((n - PaperBlock.tauA p m U r : ℕ) : ℝ) / 8
        + CTfin p m T Cerr * ((L : ℝ) ^ (3 / 4 : ℝ)) := by
    have hbr := record_bracket_nonneg (N := N) (p := p) (m := m) (U := U) i j (r := r) (n := n) hn
    have hK := mul_le_mul_of_nonneg_right (Kocc_Ccan_le_Cfin (N := N) p m) hbr
    have hCT := mul_le_mul_of_nonneg_right (CTocc_le_CTfin p m T Cerr)
      (Real.rpow_nonneg (Nat.cast_nonneg L) (3 / 4 : ℝ))
    have hcast : ((n : ℝ) - ((PaperBlock.tauA p m U r : ℕ) : ℝ))
        = ((n - PaperBlock.tauA p m U r : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]
    linarith [hmain, hK, hCT, hcast]
  -- and the target *is* the `LocalFluid.LocOcc` body
  simpa only [PaperBlock.Xa, SepGroup.Model.X_apply, PaperBlock.runMaxI_eq, LocalFluid.occTerm,
    LocalFluid.occGap, PaperBlock.tauA] using hgoal

/-- **`(lococc)` off the measured universal bad event.**

On the paper's record carrier and off `UniversalFamily.univBad`, the actual trajectory satisfies
`LocalFluid.LocOcc` at the common coefficient `Cfin = max paperC Cocc` with the error coefficient
`CTfin`.  This is `PaperBlock.paper_local_clauses`'s first premise, proved rather than assumed.

`hm` and `hT` are the paper's standing hypotheses (`m ≥ 2`, `T ≥ 1`); they are kept so that this
theorem's hypothesis list is the one the surrounding bundle and the paper use.  The implication
itself needs only the record carrier, `L ≥ 1`, `(T+3)L ≤ r` and the exclusion of `univBad`. -/
theorem locOcc_of_not_univBad {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {T : ℕ} (hT : 1 ≤ T) {L r : ℕ} (hL : 1 ≤ L) (hr : (T + 3) * L ≤ r) {Cerr : ℝ}
    {U : Array N} (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hnot : U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L) :
    LocalFluid.LocOcc (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (PaperBlock.Cfin (N := N) p m) (CTfin p m T Cerr) T L r :=
  locOcc_of_display (N := N) hL
    (fun q hq => OccPaperPointwise.familyGood_lococcPaper_expanded (N := N) hp0 hp1 hL hr hcarr
      (moveFam := UniversalFamily.moveAllFam (N := N)) (hne := UniversalFamily.moveAllFam_ne)
      (hco := UniversalFamily.moveAllFam_co)
      (grpFam := UniversalFamily.grpAllFam (N := N))
      (hI := UniversalFamily.grpAllFam_I) (hJ := UniversalFamily.grpAllFam_J) hnot q hq)

/-! ## 3. The paper-local bundle with the `(lococc)` premise removed

Everything below repeats `PaperBlock.paper_local_clauses`'s assembly with exactly one change: the
`(lococc)` field is *proved* (`locOcc_of_not_univBad`), and the error coefficient is the enlarged
`CTfin`.  The other four clauses are transferred from `CTtot` to `CTfin`, which is monotone because
`L^{3/4} ≥ 0`. -/

open PaperBlock

/-- `C_T`-monotonicity of the `L^{3/4}` remainder. -/
theorem mul_CT_mono {CT CT' : ℝ} (h : CT ≤ CT') (L : ℕ) :
    CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ CT' * (L : ℝ) ^ (3 / 4 : ℝ) :=
  mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg L) (3 / 4 : ℝ))

/-- The measured bundle: the paper-local bundle `BlkCoin.BlockClauses` on the actual record
carrier, off the single measured bad event `UniversalFamily.univBad`, at the common coefficient
`Cfin = max paperC Cocc` and the common error coefficient `CTfin = max CTtot CTocc`.

The only remaining premise is `PaperBlock.MoveCarrier`, the `(locmax)` good-window content of
`(locmove)`.  The `(lococc)` premise of `PaperBlock.paper_local_clauses` is discharged by
`locOcc_of_not_univBad`; the measure bound on `univBad` is the same one. -/
theorem paper_local_clauses_occ {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        MoveCarrier p m r T L U →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
            (Cfin (N := N) p m) (CTfin p m T Cerr) T L r) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    UniversalFamily.exists_universal_bad_and_good (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, max L₀ 1, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left L₀ 1) hL) r hr
  · intro L hL r hr U hcarr hnot hmove
    have hL₀ : L₀ ≤ L := le_trans (le_max_left L₀ 1) hL
    have hL1 : 1 ≤ L := le_trans (le_max_right L₀ 1) hL
    obtain ⟨-, -, -, -, -, -, hlocgroup, hsum⟩ := hgood L hL₀ r hr U hcarr hnot
    have hCTle : CTtot p m T Cerr ≤ CTfin p m T Cerr := CTtot_le_CTfin p m T Cerr
    -- `hmono`, `hunit`
    have hmono : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        Hc p m U A n x ≤ Hc p m U A n y :=
      fun A n _ _ hxy => PaperBlock.Hc_mono p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    have hunit : ∀ (A : Finset (Fin N)) (n : ℕ) {x y : ℤ}, x ≤ y →
        y - x ≤ Hc p m U A n y - Hc p m U A n x :=
      fun A n _ _ hxy => PaperBlock.Hc_unit p m U (le_of_lt hp0) (le_of_lt hp1) A n hxy
    -- `(loccoord)` at `CTfin`
    have hcoord : ∀ (A : Finset (Fin N)) (n : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ n → n ≤ tauA p m U r + T * L → ∀ a0 b0 : ℤ,
        (r : ℤ) - (((T + 2) * L : ℕ) : ℤ) ≤ a0 → a0 ≤ b0 →
        b0 ≤ Glue.sMaxM (Xa p m U) A n →
        ((Hc p m U A n b0 - Hc p m U A n a0 : ℤ) : ℝ)
          ≤ Cfin (N := N) p m * ((b0 - a0 : ℤ) : ℝ)
            + CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A n hA _ h1 h2 a0 b0 ha hab hb
      have h := PaperBlock.hcoord_clause_fin (N := N) hp0 hp1 hL1 hr hcarr hsum hCerr1
        A hA n h1 h2 a0 b0 ha hab hb
      have h2' := mul_CT_mono hCTle L
      linarith
    -- `(locmove)` at `Cfin`, `CTfin`
    have hwmove : ∀ (A : Finset (Fin N)) (s t : ℕ), A.Nonempty → A ≠ Finset.univ →
        tauA p m U r ≤ s → s ≤ t → t ≤ tauA p m U r + T * L →
        (∀ u : ℕ, s ≤ u → u < t → Glue.Sep (Xa p m U) A (Finset.univ \ A) u) →
        Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) t
            - Glue.Wst (Hc p m U) (Xa p m U) A (Finset.univ \ A) s
          ≤ Cfin (N := N) p m
              * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
            - ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
            + CTfin p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) := by
      intro A s t hAn hAn' hs hst ht hsep
      have hAc : Aᶜ.Nonempty := by
        rw [UniversalFamily.compl_nonempty_iff_ne_univ]; exact hAn'
      obtain ⟨hamb, hW, hstep⟩ := hmove A hAn s t hs hst ht hsep
      have hfamBad : U ∉ LocalGoodFamily.famBad (N := N) p m Cerr
          (UniversalFamily.moveAllFam (N := N)) UniversalFamily.moveAllFam_ne
          UniversalFamily.moveAllFam_co (UniversalFamily.grpAllFam (N := N))
          UniversalFamily.grpAllFam_I UniversalFamily.grpAllFam_J r T L := hnot
      have hpc := PaperBlock.wmove_clause (N := N) hp0 hp1 hL1 hAn hAc
        (fun s t hs hst ht hamb hW hstep =>
          LocCoordGeomCarrier.familyGood_locmove_paperWindow_good3 (N := N) hcarr hr hfamBad A
            (UniversalFamily.mem_moveAllFam.mpr ⟨hAn, hAc⟩) s t hs hst ht hamb hW hstep)
        s t hs hst ht hamb hW hstep
      obtain ⟨i0, hi0⟩ := hAn
      have hspread : (0 : ℝ) ≤
          ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) := by
        have h5 : Glue.sMin (Xa p m U) A s ≤ Glue.sMaxM (Xa p m U) A s :=
          le_trans (Glue.sMin_le (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0)
            (le_trans (PaperBlock.le_runMaxI p m U i0 s)
              (Glue.le_sMaxM (X := Xa p m U) (S := A) (n := s) (i := i0) ⟨i0, hi0⟩ hi0))
        have h6 : ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ) ≤ ((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) :=
          Int.cast_le.mpr h5
        linarith
      have hCpc : (0 : ℝ) < LocMovePaper.paperC (N := N) p m :=
        LocMovePaper.paperC_pos (N := N) p m
      have hCmono := PaperBlock.paperC_le_Cfin (N := N) p m
      have e1 : LocMovePaper.paperC (N := N) p m
            * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ))
          ≤ Cfin (N := N) p m
            * (((Glue.sMaxM (Xa p m U) A s : ℤ) : ℝ) - ((Glue.sMin (Xa p m U) A s : ℤ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hCmono hspread
      have e2 : ((t - s : ℕ) : ℝ) / Cfin (N := N) p m
          ≤ ((t - s : ℕ) : ℝ) / LocMovePaper.paperC (N := N) p m :=
        div_le_div_of_nonneg_left (by positivity) hCpc hCmono
      have e3 := mul_CT_mono hCTle L
      linarith
    -- `(lococc)`, proved rather than assumed
    have hocc : LocalFluid.LocOcc (Xa p m U) (tauA p m U)
        (Cfin (N := N) p m) (CTfin p m T Cerr) T L r :=
      locOcc_of_not_univBad (N := N) hp0 hp1 hm hT hL1 hr hcarr hnot
    -- `(locgroup)` at `CTfin`
    refine ⟨⟨hmono, hunit, hcoord, hwmove, hocc⟩, ?_⟩
    intro I J hdisj hI hJ s t hs hst ht hsep
    have h := PaperBlock.group_clause (N := N) (Cerr := Cerr) hL1 hcarr hr hlocgroup I J hdisj hI hJ
      s t hs hst ht hsep
    have h2' := mul_CT_mono hCTle L
    linarith

end LocOccDerived
