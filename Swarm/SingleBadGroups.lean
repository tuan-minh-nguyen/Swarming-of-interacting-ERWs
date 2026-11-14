/-
# The simultaneous windowed `(locmove)` failure event over **all** nonempty proper groups

`MWin.paper_local_clauses_win` and `SingleBadBlock.exists_blockClauses_of_badAll` need

  `U ∉ locMoveFailAtClockWin …` **for every** nonempty proper group `A`,

i.e. the intersection of `2^N - 2` measured events, which is not itself presented as a measured
event.  This file closes that quantifier: the finite union `moveFailAll` over
`Swarming.Enl.properGroups N` is a *single* set, its complement gives the per-group exclusions,
and its measure is at most `#properGroups ≤ 2^N` times any common per-group bound
(`MWin.measureReal_locMoveFailAtClockWin_le` is uniform in `A`: its bound
`2(K+1)² e^{-ε₁²/(4K(2·stepEnv p B)²)} + 2(K+1)² e^{-ε₂²/(4K(2B)²)} + e_b` does not mention `A`).

The per-group bound is *not* reproved here; `measureReal_moveFailAll_le` consumes it as a
hypothesis, so that no numerical conversion is silently bundled.  The residual numerical step
(`polynomial × exp (-c √L)` into the `exf` profile `exp (-c' L^{1/16})`) is listed in `NOTES.md`
and is not claimed.
-/
import Swarm.SingleBadBlock

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ LocGroupWindow
open SwarmMarks SwarmLogRatio LocSumAct LocSumR1 LocOccCarrier LocOccAllStarts
open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual
open ActualRecordFiltration LocGroupSimul LocMoveCompose LocMoveLocal LocMoveMart
open Loccoord Swarming.Enl ClockLocMove LocMovePaper LocalGoodFamily PaperBlock
open LocCoordGeomCarrier

namespace SingleBadGroups

variable {N : ℕ} [Nonempty (Fin N)]

/-- A nonempty proper group has nonempty complement. -/
theorem compl_nonempty_of_mem_properGroups {A : Finset (Fin N)}
    (hA : A ∈ Swarming.Enl.properGroups (N := N)) : Aᶜ.Nonempty := by
  rw [UniversalFamily.compl_nonempty_iff_ne_univ]
  exact (Swarming.Enl.mem_properGroups.mp hA).2

/-- The windowed failure event does not depend on the proofs of nonemptiness. -/
theorem locMoveFailAtClockWin_congr (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA hA' : A.Nonempty)
    (hAc hAc' : Aᶜ.Nonempty) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ)
    (geom : ℕ → ℕ → Set (Array N)) (Aw : ℕ) (U : Array N) :
    MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U
      ↔ MWin.locMoveFailAtClockWin p m A hA' hAc' r T L B C β ε₁ ε₂ geom Aw U := by
  rw [Subsingleton.elim hA hA', Subsingleton.elim hAc hAc']

/-- **The simultaneous windowed `(locmove)` failure event** over every nonempty proper group,
at the same coefficient and error data and the same window family `geom`, `Aw`. -/
noncomputable def moveFailAll (p : ℝ) (m : ℕ) (r T L : ℕ) (B C β ε₁ ε₂ : ℝ)
    (geom : ℕ → ℕ → Set (Array N)) (Aw : ℕ) : Set (Array N) :=
  ⋃ A ∈ Swarming.Enl.properGroups (N := N),
    (if h : A ∈ Swarming.Enl.properGroups (N := N) then
      ({U : Array N | MWin.locMoveFailAtClockWin p m A (Swarming.Enl.mem_properGroups.mp h).1
        (compl_nonempty_of_mem_properGroups h) r T L B C β ε₁ ε₂ geom Aw U} : Set (Array N))
      else (∅ : Set (Array N)))

/-- Membership in the simultaneous event, at the canonical proofs of the group family. -/
theorem mem_moveFailAll {p : ℝ} {m r T L : ℕ} {B C β ε₁ ε₂ : ℝ}
    {geom : ℕ → ℕ → Set (Array N)} {Aw : ℕ} {U : Array N} {A : Finset (Fin N)}
    (hA : A ∈ Swarming.Enl.properGroups (N := N))
    (hc : MWin.locMoveFailAtClockWin p m A (Swarming.Enl.mem_properGroups.mp hA).1
      (compl_nonempty_of_mem_properGroups hA) r T L B C β ε₁ ε₂ geom Aw U) :
    U ∈ moveFailAll (N := N) p m r T L B C β ε₁ ε₂ geom Aw := by
  refine Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨hA, ?_⟩⟩
  rw [dif_pos hA]
  exact hc

/-- **Avoiding the single simultaneous event excludes the failure of every proper group.** -/
theorem not_mem_locMoveFailAtClockWin_of_not_mem_moveFailAll {p : ℝ} {m r T L : ℕ}
    {B C β ε₁ ε₂ : ℝ} {geom : ℕ → ℕ → Set (Array N)} {Aw : ℕ} {U : Array N}
    (h : U ∉ moveFailAll (N := N) p m r T L B C β ε₁ ε₂ geom Aw)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    ¬ MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U := by
  intro hc
  have hne : A ≠ Finset.univ := by
    rw [← UniversalFamily.compl_nonempty_iff_ne_univ]
    exact hAc
  have hmem : A ∈ Swarming.Enl.properGroups (N := N) :=
    Swarming.Enl.mem_properGroups.mpr ⟨hA, hne⟩
  refine h (mem_moveFailAll (p := p) (m := m) (r := r) (T := T) (L := L) (B := B) (C := C)
    (β := β) (ε₁ := ε₁) (ε₂ := ε₂) (geom := geom) (Aw := Aw) (U := U) hmem ?_)
  exact (locMoveFailAtClockWin_congr p m hA
    (Swarming.Enl.mem_properGroups.mp hmem).1 hAc (compl_nonempty_of_mem_properGroups hmem)
    r T L B C β ε₁ ε₂ geom Aw U).mp hc

/-- **The finite-union bound for the simultaneous event.**  A common per-group bound `κ`
(which is what `MWin.measureReal_locMoveFailAtClockWin_le` provides: its expression does not
mention the group) is paid once per nonempty proper group. -/
theorem measureReal_moveFailAll_le {p : ℝ} {m r T L : ℕ} {B C β ε₁ ε₂ κ : ℝ}
    {geom : ℕ → ℕ → Set (Array N)} {Aw : ℕ}
    (hper : ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
      (arrayMeasure N).real
        {U : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U}
        ≤ κ) :
    (arrayMeasure N).real (moveFailAll (N := N) p m r T L B C β ε₁ ε₂ geom Aw)
      ≤ ((Swarming.Enl.properGroups (N := N)).card : ℝ) * κ := by
  refine le_trans (measureReal_biUnion_finset_le
    (Swarming.Enl.properGroups (N := N))
    (fun A => if h : A ∈ Swarming.Enl.properGroups (N := N) then
      ({U : Array N | MWin.locMoveFailAtClockWin p m A (Swarming.Enl.mem_properGroups.mp h).1
        (compl_nonempty_of_mem_properGroups h) r T L B C β ε₁ ε₂ geom Aw U} : Set (Array N))
      else (∅ : Set (Array N)))) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => κ) ?_) ?_
  · intro A hA
    rw [dif_pos hA]
    exact hper A (Swarming.Enl.mem_properGroups.mp hA).1
      (compl_nonempty_of_mem_properGroups hA)
  · rw [Finset.sum_const, nsmul_eq_mul]

/-- The same bound with the explicit family size `#properGroups ≤ 2^N`. -/
theorem measureReal_moveFailAll_le_pow {p : ℝ} {m r T L : ℕ} {B C β ε₁ ε₂ κ : ℝ}
    {geom : ℕ → ℕ → Set (Array N)} {Aw : ℕ} (hκ : 0 ≤ κ)
    (hper : ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty),
      (arrayMeasure N).real
        {U : Array N | MWin.locMoveFailAtClockWin p m A hA hAc r T L B C β ε₁ ε₂ geom Aw U}
        ≤ κ) :
    (arrayMeasure N).real (moveFailAll (N := N) p m r T L B C β ε₁ ε₂ geom Aw)
      ≤ ((2 : ℝ) ^ N) * κ := by
  refine le_trans (measureReal_moveFailAll_le hper) ?_
  have hcard : ((Swarming.Enl.properGroups (N := N)).card : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := Swarming.Enl.card_properGroups_le (N := N)
    calc ((Swarming.Enl.properGroups (N := N)).card : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ N := by push_cast; ring
  exact mul_le_mul_of_nonneg_right hcard hκ

/-! ## The block clauses with **one** event per lane

Combining `SingleBadBlock.exists_blockClauses_of_badAll` with the quantifier closing above: the
paper's local block clauses hold off the single event `badAll` and the single event
`moveFailAll`, both of which are measured (the first with the `exf` profile, the second with
`measureReal_moveFailAll_le` times the per-group bound). -/

/-- **Block clauses off the single bad event and the single simultaneous failure event.** -/
theorem exists_blockClauses_of_badAll_moveFail {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (SingleBad.badAll (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ U : Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ SingleBad.badAll (N := N) p m Cerr r T L →
        (∀ n ∈ Finset.Ico (recTimeA p m U r) (recTimeA p m U r + T * L),
          ∀ i : Fin N, SwarmRun.RunsOK (siteMarks p m U i) (n + 3) (AstarPos.Kc p L)) →
        ∀ (geom : ℕ → ℕ → Set (Array N)),
          (∀ s t : ℕ, s ≤ t → U ∈ geom s t) →
          U ∉ moveFailAll (N := N) p m r T L (RecClockLG.Bstar L)
            (LocalGoodFamily.Cmax (N := N) p m)
            (LocalGoodFamily.betaOf (N := N) p m T L Cerr)
            ((L : ℝ) ^ ((3 : ℝ) / 4)) ((L : ℝ) ^ ((3 : ℝ) / 4)) geom
            (RecClockLG.Astar r T L) →
        BlkCoin.BlockClauses (Xa p m U) (tauA p m U) (Hc p m U)
            (Cfin (N := N) p m) (LocOccDerived.CTfin p m T Cerr) T L r) := by
  obtain ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    SingleBadBlock.exists_blockClauses_of_badAll (N := N) hp0 hp1 hm hN hT
  refine ⟨Cerr, hCerr1, CT, cT, hCT, hcT, L₀, hbound, ?_⟩
  intro L hL r hr U hcarr hnot hrun geom hgeom hnotall
  refine hgood L hL r hr U hcarr hnot hrun geom hgeom ?_
  intro A hA hAc
  exact not_mem_locMoveFailAtClockWin_of_not_mem_moveFailAll hnotall A hA hAc

/-! ## Axiom audit -/


end SingleBadGroups
