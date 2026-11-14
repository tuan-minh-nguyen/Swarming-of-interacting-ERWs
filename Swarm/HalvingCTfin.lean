/-
# `(locmart)` and `(half)` at the sharp common coefficient `CTfin = max CTtot CTocc`

`LocOccDerived.paper_local_clauses_occ` produces the block clauses
`BlkCoin.BlockClauses (Xa) (tauA) (Hc) Cfin (LocOccDerived.CTfin p m T Cerr) T L r` on the
record carrier, off the measured event `UniversalFamily.univBad`, with `MoveCarrier` as the only
remaining local premise.  `LocOccDerived.CTfin = max (PaperBlock.CTtot) (CTocc)` dominates the
`CTtot` at which `M1DMart.martClause_of_locMartGood` is stated, so the `(locmart)` clause is
available at the *same* coefficient `CTfin` by monotonicity in `C_T`.

This file therefore redoes the halving at `CTfin`, with `(locmart)` supplied by the measured
event and the numerical block supplied by `M1DNum.exists_halving_thresholds`.  Two results:

* `halving_CTfin_mart` - the deterministic clause: on the record carrier, off `univBad`
  (only through the block clauses), inside the measured `(locmart)` event, with **one**
  coalescence time `s` in the sharp subwindow, `2 d_{r+BL} ≤ L`.  Residuals exactly
  `(BlockClauses at CTfin, one coalescence time)`.
* `halving_measured_CTfin` - the measured bundle: there is `Cerr ≥ 1` with the exponential
  bound on `univBad`, an explicit `L₀`, such that for every `L ≥ L₀` and every record level `r`
  the clause holds for every `U` on the record carrier off `univBad` satisfying
  `PaperBlock.MoveCarrier`.  **Residuals exactly `(MoveCarrier, one coalescence time)`**;
  `MartClause`, the `C_T` arithmetic, the `η` range and `HalfLmin` are all discharged.

Exact boundary.  No `UniformHalfClause`, `KnotCoalesceAll`, `FluidHalfDataAll`, no
old-schedule `PaperTimeClause`, no `NoCoalescence` event, no stationarity, no invariant, no
`d_T` bound.  The `MoveCarrier` premise is *kept* as a premise, not assumed away: producing it
from the measured local-good windows is a different direction.
-/
import Swarm.MartClauseActual
import Swarm.HalfNumerics
import Swarm.HalfSharp
import Swarm.LocOccDerived

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRecordMeas SwarmRecordMeas.Actual
open RecordDefect Glue FluidLimit LocalFluid JoinStep

namespace M1DMart

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. `MartClause` is monotone in the error coefficient -/

/-- A larger `C_T` weakens `MartClause.hbound`, so the clause is monotone in `C_T`. -/
theorem martClause_mono {ι : Type*} {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {A : ι → ℕ → ℕ}
    {μ CT CT' : ℝ} {T L r : ℕ} (h : JoinStep.MartClause X τ A μ CT T L r) (hle : CT ≤ CT') :
    JoinStep.MartClause X τ A μ CT' T L r := by
  obtain ⟨hμ, hA, hb⟩ := h
  refine ⟨hμ, hA, fun i s t h1 h2 h3 => ?_⟩
  have h0 : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  exact le_trans (hb i s t h1 h2 h3) (mul_le_mul_of_nonneg_right hle h0)

/-! ## 2. `(locmart)` at `CTfin` -/

/-- **`(locmart)` at the sharp common coefficient `CTfin = max CTtot CTocc`.**

On the measured event `RecordClock.locMartGood`, the clause holds at the `LocOccDerived` error
coefficient — the same coefficient as the public block clauses of
`LocOccDerived.paper_local_clauses_occ`. -/
theorem martClause_CTfin_of_locMartGood {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m T L r : ℕ}
    {Cerr : ℝ} {U : Array N}
    (hU : U ∈ RecordClock.locMartGood (N := N) p m r T L) :
    JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (fun i n => excitedSteps p m U n i) (2 * p - 1)
      (LocOccDerived.CTfin p m T Cerr) T L r :=
  martClause_mono (martClause_of_locMartGood hp hU)
    (LocOccDerived.CTtot_le_CTfin p m T Cerr)

/-- The `(locmart)` failure set at `CTfin`. -/
def martClauseBadCTfin (p : ℝ) (m T L r : ℕ) (Cerr : ℝ) : Set (Array N) :=
  {U | ¬ JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
    (fun i n => excitedSteps p m U n i) (2 * p - 1)
    (LocOccDerived.CTfin p m T Cerr) T L r}

/-- The `CTfin` failure set is contained in the measured `(locmart)` bad event. -/
theorem martClauseBadCTfin_subset_locMartBad {p : ℝ} (hp : (1 : ℝ) / 2 < p)
    (m T L r : ℕ) (Cerr : ℝ) :
    martClauseBadCTfin (N := N) p m T L r Cerr
      ⊆ RecordClock.locMartBad (N := N) p m r T L := by
  intro U hU
  have hnot : ¬ U ∈ RecordClock.locMartGood (N := N) p m r T L :=
    fun hg => hU (martClause_CTfin_of_locMartGood hp hg)
  simpa [RecordClock.locMartBad, RecordClock.locMartGood] using hnot

/-- **The measured profile of `(locmart)` at `CTfin`.** -/
theorem exists_martClauseBadCTfin_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) (hT : 1 ≤ T) (Cerr : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ,
      (arrayMeasure N).real (martClauseBadCTfin (N := N) p m T L r Cerr)
        ≤ Real.exp (-c * RecordClock.xOf L) := by
  obtain ⟨c, hc, L₀, hL₀⟩ := RecordClock.exists_locMartBad_le (N := N) hp0 hp1 hm hN T hT
  refine ⟨c, hc, L₀, fun L hL r => ?_⟩
  refine le_trans (measureReal_mono (martClauseBadCTfin_subset_locMartBad hp0 m T L r Cerr)
    (measure_ne_top _ _)) (hL₀ L hL r)

/-! ## 3. The halving at `CTfin` with `(locmart)` and the numerics discharged -/

/-- **The sharp halving at `CTfin`, with `MartClause` supplied by the measured event and the
whole numerical block absorbed into an explicit `L₀`.** -/
theorem halving_CTfin_mart {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) {m : ℕ} (Cerr : ℝ) :
    ∀ T : ℕ, 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) ≤ T →
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ (r B s : ℕ) (U : Array N) {i₀ j₀ : Fin N},
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∈ RecordClock.locMartGood (N := N) p m r T L →
      BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (PaperBlock.Hc p m U) (PaperBlock.Cfin (N := N) p m)
        (LocOccDerived.CTfin p m T Cerr) T L r →
      defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) →
      (T + 3) * L ≤ r →
      i₀ ≠ j₀ →
      PaperBlock.tauA p m U r + 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) * L ≤ s →
      (Glue.spreadS (PaperBlock.Xa p m U) (Finset.univ : Finset (Fin N)) s : ℝ)
        ≤ HalfEps (PaperBlock.Cfin (N := N) p m) (Finset.univ : Finset (Fin N)).card
          * (L : ℝ) →
      PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L →
      s ≤ PaperBlock.tauA p m U (r + B * L) →
      2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) ≤ (L : ℤ) := by
  intro T hT64
  obtain ⟨L₀, hL₀⟩ :=
    M1DNum.exists_halving_thresholds (C := PaperBlock.Cfin (N := N) p m)
      (CT := LocOccDerived.CTfin p m T Cerr) (PaperBlock.Cfin_pos p m)
      (Finset.univ : Finset (Fin N)).card
  refine ⟨max L₀ 1, ?_⟩
  intro L hL r B s U i₀ j₀ hcarr hLM hBC hdr hr hij hs₀ hspread hrecT hrecB
  have hL₀' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨hnum, hηdef, hη, hLmin⟩ := hL₀ L hL₀'
  exact JoinStep.halving_of_coalesce_sharp (ι := Fin N)
    (X := PaperBlock.Xa p m U) (τ := PaperBlock.tauA p m U)
    (H := PaperBlock.Hc p m U) (A := fun i n => excitedSteps p m U n i) (μ := 2 * p - 1)
    (C := PaperBlock.Cfin (N := N) p m) (CT := LocOccDerived.CTfin p m T Cerr)
    (T := T) (L := L) (r := r) (η := ⌈LocOccDerived.CTfin p m T Cerr
      * (L : ℝ) ^ ((3 : ℝ) / 4)⌉₊) (B := B) (s := s)
    (M1D.isRecord_Xa hcarr) (PaperBlock.Xa_step p m U) hBC.base
    (martClause_CTfin_of_locMartGood hp0 hLM)
    (PaperBlock.Cfin_pos p m) (LocOccDerived.CTfin_pos p m T Cerr).le hdr hr hL1 hij
    hnum hT64 hηdef hs₀ hspread hη hLmin hrecT hrecB

/-! ## 4. The measured bundle: residuals `(MoveCarrier, one coalescence time)` -/

/-- **The sharp halving on the measured local-good bundle at `CTfin`.**

There are `Cerr ≥ 1`, an explicit exponential profile on `UniversalFamily.univBad`, and an
explicit `L₀`, such that for every `L ≥ L₀` and every record level `r` with `(T+3)L ≤ r`: for
every `U` on the record carrier that avoids `univBad`, satisfies `PaperBlock.MoveCarrier`, and
lies in the measured `(locmart)` event, and for **one** time `s` in the sharp subwindow
`[τ_r + 64⌈Cfin⌉L, τ_{r+BL}]` with pack spread `≤ HalfEps·L`, one has `2 d_{r+BL} ≤ L`
(provided the advance deadline `τ_{r+BL} ≤ τ_r + TL`).

The only inputs beyond the measured events are `MoveCarrier` and the coalescence time `s`. -/
theorem halving_measured_CTfin {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) {T : ℕ} (hT : 1 ≤ T)
    (hT64 : 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) ≤ T) :
    ∃ Cerr : ℝ, 1 ≤ Cerr ∧ ∃ CT cT : ℝ, 0 < CT ∧ 0 < cT ∧ ∃ L₀ : ℕ,
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
        (arrayMeasure N).real (UniversalFamily.univBad (N := N) p m Cerr r T L)
          ≤ CT * LocalGoodAll.exf cT L) ∧
      (∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r → ∀ (U : Array N) {i₀ j₀ : Fin N},
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
        PaperBlock.MoveCarrier p m r T L U →
        U ∈ RecordClock.locMartGood (N := N) p m r T L →
        i₀ ≠ j₀ →
        ∀ (B s : ℕ),
          PaperBlock.tauA p m U r + 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) * L ≤ s →
          s ≤ PaperBlock.tauA p m U (r + B * L) →
          (Glue.spreadS (PaperBlock.Xa p m U) (Finset.univ : Finset (Fin N)) s : ℝ)
            ≤ HalfEps (PaperBlock.Cfin (N := N) p m) (Finset.univ : Finset (Fin N)).card
              * (L : ℝ) →
          PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L →
          2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) ≤ (L : ℤ)) := by
  obtain ⟨Cerr, hCerr, CT, cT, hCT, hcT, Lb, hbound, hblock⟩ :=
    LocOccDerived.paper_local_clauses_occ (N := N) hp0 hp1 hm hN (T := T) hT
  obtain ⟨Lh, hLh⟩ := halving_CTfin_mart (N := N) hp0 (Cerr := Cerr) T hT64
  refine ⟨Cerr, hCerr, CT, cT, hCT, hcT, max Lb Lh, ?_, ?_⟩
  · intro L hL r hr
    exact hbound L (le_trans (le_max_left _ _) hL) r hr
  · intro L hL r hr U i₀ j₀ hcarr hnot hmove hLM hij B s hs₀ hsB hspread hrecT
    have hdr : defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) := by
      rw [M4D.Xa_eq_actX, M4D.tauA_eq]
      exact LocCoordGeomCarrier.defect_le_of_carrier (N := N) hcarr
    exact hLh L (le_trans (le_max_right _ _) hL) r B s U hcarr hLM
      (hblock L (le_trans (le_max_left _ _) hL) r hr U hcarr hnot hmove)
      hdr hr hij hs₀ hspread hrecT hsB

end M1DMart
