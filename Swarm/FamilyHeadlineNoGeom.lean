/-
# The family headline with the two `(loccoord)` carriers discharged

`LocalGoodFamily.exists_famBad_and_good` exports eight clauses off `famBad`.  Two of them carry the
`(loccoord)` geometric carrier:

* the `(locmove)` clause has the hypothesis `U ∈ ClockLocMove.locCoordGeom p m A hA r T L s t`
  and is stated for windows up to `τ_r + (T+3)L`;
* the `(loccoord)` clause has `U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t` and no time window
  at all.

`LocCoordGeomCarrier` proves that on the record carrier the carrier is automatic on the paper's
window.  This file re-exports the headline with **two extra conjuncts** — the same two displays at
the paper's window `[τ_r, τ_r + TL]` and with no geometric hypothesis — at the *same* constants
`Cerr`, `CT`, `cT`, `L₀`.  The statement is therefore strictly stronger than the headline (same
witnesses, more consequences), not a relaxation, and it is not a new probabilistic input: every
extra clause is derived from the headline's own clause plus `mem_locCoordGeom_of_carrier`.
-/
import Swarm.LocMovePaperWindow

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open LocOccCarrierAssembly SummedSlope.Model
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl
open LocOccSingleWindow LocOccAllPairs LocOccSingleWindowAllPairs
open LocalGoodFamily

namespace LocCoordGeomCarrier

variable {N : ℕ} [Nonempty (Fin N)]

/-- **The family headline with the `(locmove)` and `(loccoord)` carriers discharged** at the
paper's window `[τ_r, τ_r+TL]`, at the headline's own constants. -/
theorem exists_famBad_and_good_noGeom {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {T : ℕ} (hT : 1 ≤ T) (hN : 2 ≤ N)
    (moveFam : Finset (Finset (Fin N))) (hne : ∀ A ∈ moveFam, A.Nonempty)
    (hco : ∀ A ∈ moveFam, Aᶜ.Nonempty)
    (grpFam : Finset (Finset (Fin N) × Finset (Fin N)))
    (hI : ∀ q ∈ grpFam, q.1.Nonempty) (hJ : ∀ q ∈ grpFam, q.2.Nonempty)
    (hdisj : ∀ q ∈ grpFam, Disjoint q.1 q.2) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧
      (∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
        ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
          (arrayMeasure N).real
              (famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L)
            ≤ CT * LocalGoodAll.exf cT L) ∧
      (∃ Lg : ℕ, ∀ L ≥ Lg, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ famBad (N := N) p m Cerr moveFam hne hco grpFam hI hJ r T L →
        (∀ j : Fin N, ∀ u : ℕ,
            BddAbove (Set.range fun n' => Gtrunc p (siteMarks p m U j) n' (u + 1))) ∧
          U ∈ RecordClock.locMartGood (N := N) p m r T L ∧
          (∀ (A : Finset (Fin N)) (hA : A ∈ moveFam), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + (T + 3) * L →
            locmoveGood p m A (hne A hA) (r : ℤ) T L (RecClockLG.Bstar L)
              (recTimeA p m U r) s t U →
            U ∈ ClockLocMove.locCoordGeom p m A (hne A hA) r T L s t →
            WA p m U t A Aᶜ (hne A hA) (hco A hA) - WA p m U s A Aᶜ (hne A hA) (hco A hA)
              ≤ locmoveRHS (N := N) p m A (hne A hA) L (LocalGoodFamily.Cmax (N := N) p m)
                  (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
                  ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U) ∧
          (∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
            U ∈ ClockLocMove.locCoordGeom p m B hB r T L s t →
            Swarming.Group.average B
                (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
              ≤ LocalGoodFamily.Cmax (N := N) p m
                  * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
                + Cerr * (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          OccDisplayNull.occFace (N := N) p m (LocOccSiteRate.Ccan p m) r T L
            (recTimeA p m U r) U ∧
          (∀ s0 : ℕ, U ∈ LocOccFibreSum.band p m r L s0 →
            U ∈ LocOccSingleWindowAllPairs.GoodWinAllPairs (N := N) p m
              (LocOccSiteRate.Ccan p m) r T L s0) ∧
          (∀ (q : Finset (Fin N) × Finset (Fin N)) (hq : q ∈ grpFam), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            (∀ u ∈ Finset.Ico s t, SepSet p m u q.1 q.2 U) →
            WA p m U t q.1 q.2 (hI q hq) (hJ q hq) - WA p m U s q.1 q.2 (hI q hq) (hJ q hq)
              ≤ (L : ℝ) ^ ((3 : ℝ) / 4)) ∧
          (∀ j : Fin N, ∀ a0 b0 : ℕ,
            LocOccCarrierAssembly.A0 r T L ≤ a0 →
            b0 ≤ LocOccCarrierAssembly.A0 r T L + LocOccCarrierAssembly.Lw T L → a0 ≤ b0 →
            ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
              ≤ 2 * LocOccSiteRate.Ccan p m * ((b0 : ℝ) - (a0 : ℝ))
                + 6 * LocOccSiteRate.Ccan p m
                  * ((betaT (LocSumAct.xOf (LocOccCarrierAssembly.Lw T L)) : ℕ) : ℝ)) ∧
          -- extra conjunct 1: `(locmove)` at the paper's window, no geometric carrier
          (∀ (A : Finset (Fin N)) (hA : A ∈ moveFam), ∀ s t : ℕ,
            recTimeA p m U r ≤ s → s ≤ t → t ≤ recTimeA p m U r + T * L →
            locmoveGood p m A (hne A hA) (r : ℤ) T L (RecClockLG.Bstar L)
              (recTimeA p m U r) s t U →
            WA p m U t A Aᶜ (hne A hA) (hco A hA) - WA p m U s A Aᶜ (hne A hA) (hco A hA)
              ≤ locmoveRHS (N := N) p m A (hne A hA) L (LocalGoodFamily.Cmax (N := N) p m)
                  (betaOf (N := N) p m T L Cerr) ((L : ℝ) ^ ((3 : ℝ) / 4))
                  ((L : ℝ) ^ ((3 : ℝ) / 4)) s t U) ∧
          -- extra conjunct 2: `(loccoord)` at the paper's window, no geometric carrier
          (∀ (B : Finset (Fin N)) (hB : B.Nonempty) (s t : ℕ), s ≤ t →
            recTimeA p m U r ≤ s → t ≤ recTimeA p m U r + T * L →
            Swarming.Group.average B
                (fun k => HA p m U t B (X p m U t k) - HA p m U s B (X p m U s k))
              ≤ LocalGoodFamily.Cmax (N := N) p m
                  * (((runMaxA p m U hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
                + Cerr * (L : ℝ) ^ ((3 : ℝ) / 4))) := by
  obtain ⟨Cerr, hCerr1, hmeas, Lg, hLg⟩ :=
    exists_famBad_and_good (N := N) hp0 hp1 hm hT hN moveFam hne hco grpFam hI hJ hdisj
  refine ⟨Cerr, hCerr1, hmeas, Lg, ?_⟩
  intro L hL r hr U hcarr hbad
  obtain ⟨hpot, hmart, hlocmove, hloccoord, hocc, hgood, hlocgroup, hlocsum⟩ :=
    hLg L hL r hr U hcarr hbad
  refine ⟨hpot, hmart, hlocmove, hloccoord, hocc, hgood, hlocgroup, hlocsum, ?_, ?_⟩
  · exact familyGood_locmove_paperWindow (N := N) hcarr hr hbad
  · intro B hB s t hst hτs htT
    exact hloccoord B hB s t hst
      (mem_locCoordGeom_of_carrier (N := N) hcarr hr B hB s t hτs hst htT)

end LocCoordGeomCarrier

