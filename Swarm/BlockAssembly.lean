/-
# from the local-good block clauses to `HblkTwo.BadBlk` and the paper profile

## What this file does

`Swarm/ProfileBridge.lean` already proves the literal theorem from the paper's `(blkprob)`
(`M4Term.PaperBadBlockProfile`).  What is missing is the *measured* bridge that turns the actual
local-good randomisation into that block estimate.  This file builds the deterministic and
measure-theoretic part of that bridge and states the remaining inputs as named,
non-probabilistic residuals at the paper's own constants and at the actual types.
28 declarations, no proof holes, standard foundational axioms only.

## The chain, every step proved here

1. `paperProfile_eq_exf` — `TightAvail.paperProfile C c L = ofReal (C * LocalGoodAll.exf c L)`: the
   terminal adapter and the local-good lane use the same `L ↦ L^(1/16)` profile.
2. `measure_le_ofReal_of_measureReal_le` — the `.real` bound on `univBad` produced by
   `UniversalFamily.exists_universal_bad_and_good` becomes an `ℝ≥0∞` bound.
3. `Xa_eq_actX`, `tauA_eq` — the local-good lane's `(Xa, tauA)` *is* the actual
   `(actX, recTimeA)`; `ae_reach` — the record clock exists almost surely.
4. `badBlk_ae_subset_univBad` — **the source's step 9.**  On the full-measure set where the record
   clock exists, `{U | BadBlk B C₀ T (arrQ p m U) r L}` is contained mod `arrayMeasure N` in the
   single universal bad event `univBad Cerr r T L`, given a pointwise producer
   `BlockClauses → GoodSeq` off `univBad`.  `BadBlk`'s own `d_r ≤ L` *is* `recordCarrier`'s defect
   conjunct (`defect X τ r = r - runMin X (τ r)`), so no defect mass is used; the only measure
   theory is `measure_mono_ae`.
5. `paperBadBlockProfile_of_localGood` — `M4Term.PaperBadBlockProfile p m` from the three
   residuals `CarrierLocOcc` (direction A), `CarrierMove` (direction B), `PaperBlockGeometry`.
   `PaperBlock.paper_local_clauses` supplies the one exponential profile; `b = Cfin²` and the
   schedule-admissible `T` of `exists_schedule_T b hb` are fixed *before* the bad event is
   measured, and `C₀ ≥ B + T + 3` gives `(T+3)L ≤ C₀L ≤ r`.
6. `main_claim_of_localGood` — the literal theorem (one `κ > 0` before `N`, one deterministic
   `v ∈ [κ, 2p-1]`, every walker, almost surely under `Swarming.Uniform.arrayMeasure N`) from those
   three residuals.
7. `paperBlockGeometry_of_time_half` — the source's §§2–8 reduce `PaperBlockGeometry` to its two
   surviving block inequalities: `PaperTimeClause` (`(time)`) and a uniform `(half)` clause.
   `(diam)` is `HblkTwo.twoBlock_goodBlock` plus `goodBlock_iff_goodSeq`.
8. `uniformHalfClause_of_fluidJoin` — the uniform `(half)` clause is *exactly*
   `FluidJoin.exists_uniform_half_of_fluid_join` at `ι = Fin N`, with the verbatim `hgeo`
   argument `FluidHalfData`; `paperBlockGeometry_of_fluid` feeds it in.
9. `uniformHalfClause_of_knotCoalescence` — the same clause is also *exactly*
   `DefectKnot.exists_uniform_half_of_knot_coalescence`, with the verbatim `hcoal` argument
   `KnotCoalesceData`; `paperBlockGeometry_of_time_knot` feeds that in instead.
10. `main_claim_of_fluid` and `main_claim_of_knot` — the literal theorem from `CarrierLocOcc`,
    `CarrierMove`, `PaperTimeClause` and either fluid endpoint.

## Exact boundary

Nothing here is a probability estimate: `(lococc)` (`CarrierLocOcc`), the `(locmove)` good-window
carrier (`CarrierMove`), the source's `(time)` clause (`PaperTimeClause`) and the fluid coalescence
data (`FluidHalfData` or `KnotCoalesceData`) remain explicit premises, stated with the paper's
`(BTchoice)` schedule (`b ≥ 0`, `T ≥ 64·Cfin`, `B > (1+64Cfin)(1+b)^(N-1) + 1`, `B - 2 < T`,
`C₀ ≥ B + T + 3`).  No `NoCoalescence` event, no stationarity, no invariant law, and no velocity
claim appears.  `PaperBlockGeometry` is *not* derived from a probability statement.
-/
import Swarm.ProfileBridge
import Swarm.PaperBlock
import Swarm.UniversalFamily
import Swarm.FluidJoinHcoal
import Swarm.LocCoordGeomCarrier

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators BoundedContinuousFunction

namespace M4D

open Swarming Swarming.Uniform RecordDefect SwarmRecordMeas SwarmRecordMeas.Actual
open SwarmM4C SwarmM4C.LawBridge HblkTwo HblkFinal M4Term RecordoSupply

/-! ## 1. The two profiles agree -/

/-- `TightAvail.paperProfile` is the terminal adapter's shape of `LocalGoodAll.exf`.  No
constant is changed: both are `C * exp (-c L^(1/16))`. -/
theorem paperProfile_eq_exf (C c : ℝ) (L : ℕ) :
    TightAvail.paperProfile C c L = ENNReal.ofReal (C * LocalGoodAll.exf c L) := by
  rw [TightAvail.paperProfile, LocalGoodAll.exf, LocSumAct.xOf, neg_mul]

/-! ## 2. From a `.real` bound to an `ℝ≥0∞` bound -/

/-- A real-valued upper bound on the measure of a finite-measure set is an `ℝ≥0∞` bound. -/
theorem measure_le_ofReal_of_measureReal_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ Set.univ ≠ ⊤) {s : Set α} {a : ℝ} (h : μ.real s ≤ a) :
    μ s ≤ ENNReal.ofReal a := by
  have hne : μ s ≠ ⊤ := ne_top_of_le_ne_top hμ (measure_mono (Set.subset_univ s))
  have hreal : μ.real s = (μ s).toReal := measureReal_def μ s
  rw [hreal] at h
  calc μ s = ENNReal.ofReal (μ s).toReal := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal h

/-- `arrayMeasure` is a probability measure, so every set has finite measure. -/
theorem arrayMeasure_ne_top {N : ℕ} {s : Set (Swarming.Uniform.Array N)} :
    (Swarming.Uniform.arrayMeasure N) s ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [measure_univ]; exact ENNReal.one_ne_top)
    (measure_mono (Set.subset_univ s))

/-! ## 3. The two trajectory carriers agree -/

/-- The local-good lane's position family is the actual trajectory. -/
theorem Xa_eq_actX {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m : ℕ)
    (U : Swarming.Uniform.Array N) : PaperBlock.Xa p m U = actX p m U := rfl

/-- The local-good lane's record clock is the canonically defaulted one. -/
theorem tauA_eq {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m : ℕ)
    (U : Swarming.Uniform.Array N) :
    PaperBlock.tauA p m U = fun r => recTimeA p m U r := rfl

/-- The actual record clock exists almost surely (`M4RecordGeom.ae_reachAll`). -/
theorem ae_reach {N : ℕ} [Nonempty (Fin N)] {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), U ∈ ReachAll p m :=
  M4RecordGeom.ae_reachAll hp0 hp1 hm hN

/-! ## 4. From a pointwise block producer to the measured inclusion -/

/-- **The source's step 9.**  If, off the single universal bad event and on the record carrier
with the paper's block clauses, the three block inequalities hold, then the paper's bad block
event is contained in the universal bad event, up to the full-measure set on which the actual
record clock exists.

`BadBlk` already carries `d_r ≤ L`, which together with `ReachAll` gives the record carrier, so
the containment is genuine: no defect-mass or coalescence probability is used. -/
theorem badBlk_ae_subset_univBad {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    {Cerr : ℝ} {L₀ : ℕ} {BB CC TT : ℕ}
    (hprod : ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, CC * L ≤ r →
      ∀ U : Swarming.Uniform.Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r L →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r TT L →
        GoodSeq BB CC TT (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r L)
    {L r : ℕ} (hL : L₀ ≤ L) (hr : CC * L ≤ r) :
    {U : Swarming.Uniform.Array N | BadBlk BB CC TT (HblkFinal.arrQ p m U) r L}
      ≤ᵐ[Swarming.Uniform.arrayMeasure N]
      UniversalFamily.univBad (N := N) p m Cerr r TT L := by
  filter_upwards [ae_reach (N := N) hp0 hp1 hm hN] with U hreach hbad
  have hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L :=
    ⟨hreach, by simpa only [HblkFinal.arrQ, RecordDefect.defect, Set.mem_ofPred_eq] using hbad.1⟩
  by_contra hnot
  exact hbad.2 (hprod L hL r hr U hcarr hnot)

/-! ## 5. The three residuals at the paper's constants -/

/-- **Direction A's premise.**  The paper's `(lococc)` display at the common coefficient `Cfin`,
on the actual record carrier off the single universal bad event, uniformly in the window
parameters.  This is exactly the hypothesis `hocc` of `PaperBlock.paper_local_clauses`. -/
def CarrierLocOcc (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (T : ℕ) (Cerr : ℝ) (L r : ℕ),
    (T + 3) * L ≤ r →
    ∀ U : Swarming.Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
      LocalFluid.LocOcc (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (PaperBlock.Cfin (N := N) p m) (PaperBlock.CTtot p m T Cerr) T L r

/-- **Direction B's premise.**  The paper's `(locmove)` good-window carrier `(locmax)` on the
actual record carrier off the single universal bad event.  This is exactly the hypothesis
`hmove` of `PaperBlock.paper_local_clauses`. -/
def CarrierMove (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (T : ℕ) (Cerr : ℝ) (L r : ℕ),
    (T + 3) * L ≤ r →
    ∀ U : Swarming.Uniform.Array N,
      U ∈ RecClockLG.recordCarrier (N := N) p m r L →
      U ∉ UniversalFamily.univBad (N := N) p m Cerr r T L →
      PaperBlock.MoveCarrier p m r T L U

/-- **The deterministic compactness conclusion of the source's `tight` proof (its §§2–8).**

For every admissible schedule `(b, T, Cerr)` — `b ≥ 0`, `T ≥ 64 ×` the `(locmove)` coefficient,
`Cerr ≥ 1` — there are the paper's `(BTchoice)` block size `B` and constants `C₀ ≥ B + T + 3`,
`L₀` with `B > (1+64C)(1+b)^{N-1} + 1` and `B - 2 < T`, such that on the record carrier, given the
paper's block clauses at those coefficients, the three block inequalities `(time)`, `(half)`,
`(diam)` hold for every `r ≥ C₀ L` and `L ≥ L₀`.

The local-good event has already been consumed by `PaperBlock`; this statement is pure geometry
and contains no probability. -/
def PaperBlockGeometry (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (T : ℕ) (Cerr : ℝ),
    0 ≤ b → 1 ≤ T → 1 ≤ Cerr → 64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
    (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 →
    ∃ (B C₀ L₀ : ℕ), 1 ≤ B ∧ B + T + 3 ≤ C₀ ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      (B : ℝ) - 2 < (T : ℝ) ∧
      ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
        ∀ U : Swarming.Uniform.Array N,
          U ∈ RecClockLG.recordCarrier (N := N) p m r L →
          BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
              (PaperBlock.Hc p m U) (PaperBlock.Cfin (N := N) p m)
              (PaperBlock.CTtot p m T Cerr) T L r →
          GoodSeq B C₀ T (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r L

/-! ## 6. The paper's schedule: `T` above `64 Cfin` can be chosen -/

/-- **The paper's `T` exists at every `b ≥ 0`.**  For every `b ≥ 0` there is a window parameter
`T` simultaneously above `64 Cfin` and above the `(BTchoice)` schedule bound
`(1+64Cfin)(1+b)^{N-1} + 2`, so that a block size `B` with
`(1+64Cfin)(1+b)^{N-1} - 1 < B - 2 < T` exists.  This is what makes `PaperTimeClause` and
`PaperBlockGeometry` non-vacuous: they are only demanded at admissible `T`. -/
theorem exists_schedule_T {N : ℕ} {p : ℝ} {m : ℕ} (b : ℝ) (hb : 0 ≤ b) :
    ∃ T : ℕ, 1 ≤ T ∧ 64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 := by
  set x : ℝ := (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) with hx
  refine ⟨⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ + 1, by omega, ?_, ?_⟩
  · have h1 : 64 * PaperBlock.Cfin (N := N) p m
        ≤ max (64 * PaperBlock.Cfin (N := N) p m) (x + 5) := le_max_left _ _
    have h2 : max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)
        ≤ (⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ : ℝ)
        ≤ ((⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    linarith
  · have h1 : x + 5 ≤ max (64 * PaperBlock.Cfin (N := N) p m) (x + 5) := le_max_right _ _
    have h2 : max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)
        ≤ (⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ + 1 : ℕ) : ℝ)
        = (⌈max (64 * PaperBlock.Cfin (N := N) p m) (x + 5)⌉₊ : ℝ) + 1 := by
      push_cast; ring
    rw [h3]
    linarith

/-! ## 7. `PaperBadBlockProfile` from the three residuals -/

/-- **The measured bridge.**  `M4Term.PaperBadBlockProfile p m` — the paper's `(blkprob)` in its
own profile — follows from

* `CarrierLocOcc`: the paper's `(lococc)` display (direction A),
* `CarrierMove`: the paper's `(locmove)` good-window carrier (direction B),
* `PaperBlockGeometry`: the deterministic `(time)`/`(half)`/`(diam)` conclusion (direction D).

No further probabilistic input is used: `PaperBlock.paper_local_clauses` supplies the universal
bad event with its one exponential profile, and `badBlk_ae_subset_univBad` converts the
deterministic block statement into the measured inclusion.  The window parameter `T` is chosen at
`⌈64 Cfin⌉₊ + 1`, which is the paper's "`T` above `64C`" constraint, before the bad event is
measured; `b = Cfin²` is the paper's choice. -/
theorem paperBadBlockProfile_of_localGood {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (hgeo : PaperBlockGeometry p m) :
    PaperBadBlockProfile p m := by
  intro N inst hN
  letI : Nonempty (Fin N) := inst
  -- the paper's `b = C^2`, and `T` above the `(BTchoice)` schedule bound for that `b`
  set b : ℝ := PaperBlock.Cfin (N := N) p m ^ 2 with hbdef
  have hb : 0 ≤ b := by rw [hbdef]; positivity
  obtain ⟨T, hT1, hT64, hTsch⟩ := exists_schedule_T (N := N) (p := p) (m := m) b hb
  -- the single universal bad event at the paper's own constants
  obtain ⟨Cerr, hCerr, CT, cT, hCT, hcT, L₀, hbound, hgood⟩ :=
    PaperBlock.paper_local_clauses (N := N) hp0 hp1 hm hN (T := T) hT1
  obtain ⟨B, C₀, L₀g, hB, hC₀, hBB, hBT, hgeoU⟩ :=
    hgeo N hN b T Cerr hb hT1 hCerr hT64 hTsch
  refine ⟨B, T, C₀, hB, CT, cT, max L₀ L₀g, hCT.le, hcT, ?_⟩
  intro L hL1 hL r hr
  -- `(T+3)L ≤ C₀L ≤ r`
  have h4C₀ : T + 3 ≤ C₀ := by omega
  -- the pointwise producer on the good event
  have hprod : ∀ (L' : ℕ), max L₀ L₀g ≤ L' → ∀ r' : ℕ, C₀ * L' ≤ r' →
      ∀ U : Swarming.Uniform.Array N,
        U ∈ RecClockLG.recordCarrier (N := N) p m r' L' →
        U ∉ UniversalFamily.univBad (N := N) p m Cerr r' T L' →
        GoodSeq B C₀ T (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r' L' := by
    intro L' hL' r' hrU U hcarr hnot
    have hLa : L₀ ≤ L' := le_trans (le_max_left _ _) hL'
    have hLb : L₀g ≤ L' := le_trans (le_max_right _ _) hL'
    have hTL : (T + 3) * L' ≤ r' := le_trans (Nat.mul_le_mul_right L' h4C₀) hrU
    refine hgeoU L' hLb r' hrU U hcarr ?_
    exact hgood L' hLa r' hTL U hcarr hnot
      (hocc N hN T Cerr L' r' hTL U hcarr hnot)
      (hmove N hN T Cerr L' r' hTL U hcarr hnot)
  calc (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N | BadBlk B C₀ T (HblkFinal.arrQ p m U) r L}
      ≤ (Swarming.Uniform.arrayMeasure N)
          (UniversalFamily.univBad (N := N) p m Cerr r T L) :=
        measure_mono_ae (badBlk_ae_subset_univBad (N := N) hp0 hp1 hm hN (m := m)
          (Cerr := Cerr) (L₀ := max L₀ L₀g) (BB := B) (CC := C₀) (TT := T) hprod hL hr)
    _ ≤ ENNReal.ofReal (CT * LocalGoodAll.exf cT L) :=
        measure_le_ofReal_of_measureReal_le arrayMeasure_ne_top
          (hbound L (le_trans (le_max_left _ _) hL) r
            (le_trans (Nat.mul_le_mul_right L h4C₀) hr))
    _ = TightAvail.paperProfile CT cT L := (paperProfile_eq_exf CT cT L).symm

/-- **The literal theorem from the three residuals.**

For every `1/2 < p < 1` and `m ≥ 2` there is a single `κ > 0` chosen before `N` such that for
every `N ≥ 2` there is one deterministic `v ∈ [κ, 2p-1]` with, almost surely under the actual
array measure, every walker's normalised position converging to `v`. -/
theorem main_claim_of_localGood {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (hgeo : PaperBlockGeometry p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) :=
  main_claim_of_paper_badblock_profile hp0 hp1 hm
    (paperBadBlockProfile_of_localGood hp0 hp1 hm hocc hmove hgeo)

/-! ## 8. The paper's `(time)` clause and the uniform `(half)` clause -/

/-- **The paper's `(time)` clause on the local-good event.**

At the paper's `(BTchoice)` schedule — `b ≥ 0`, `T ≥ 64 ×` the `(locmove)` coefficient `Cfin`,
and `B`, `C₀ ≥ B + T + 3` chosen with `B > (1+64Cfin)(1+b)^{N-1} + 1`, `B - 2 < T` — the record
advances `B L` levels within `T L` steps, uniformly over `r ≥ C₀ L`, on the record carrier
carrying the paper's block clauses.

The `B`-schedule inequalities are part of the statement, exactly as in `(BTchoice)`. -/
def PaperTimeClause (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (T : ℕ) (Cerr : ℝ),
    0 ≤ b → 1 ≤ T → 1 ≤ Cerr → 64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
    (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 →
    ∃ (B C₀ L₀ : ℕ), 1 ≤ B ∧ B + T + 3 ≤ C₀ ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      (B : ℝ) - 2 < (T : ℝ) ∧
      ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
        ∀ U : Swarming.Uniform.Array N,
          U ∈ RecClockLG.recordCarrier (N := N) p m r L →
          BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
              (PaperBlock.Hc p m U) (PaperBlock.Cfin (N := N) p m)
              (PaperBlock.CTtot p m T Cerr) T L r →
          PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L

/-- **The paper's `(half)` clause**, uniformly over *all* actual nearest-neighbour families with
first-passage record times at every admissible starting level, on `{d_r ≤ L} ∩ {(time)}`.

This is the exact conclusion of `FluidJoin.exists_uniform_half_of_fluid_join`; nothing about the
given array enters, so the statement is a deterministic statement about nearest-neighbour paths. -/
def UniformHalfClause (N : ℕ) [Nonempty (Fin N)] (C₀ B T : ℕ) : Prop :=
  ∃ L₀ : ℕ, ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
    ∀ (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ), IsRecord X τ →
      (∀ (i : Fin N) (n : ℕ), |X i (n + 1) - X i n| = 1) →
      defect X τ r ≤ (L : ℤ) →
      τ (r + B * L) - τ r ≤ T * L →
      2 * defect X τ (r + B * L) ≤ (L : ℤ)

/-! ## 9. The fluid data and the promoted finite-scale fluid-join endpoint -/

/-- The verbatim `hgeo` argument of `FluidJoin.exists_uniform_half_of_fluid_join`: on every
compactness limit of the local-good record interpolants, the one-sided drift vanishes, the
source's meeting rule `(meet)` holds, and coincidence on contact `(coincide)` holds.

This is a deterministic statement about the limiting fluid path; it is the only fluid input this
file consumes, and it contains no probability and no `NoCoalescence` event. -/
def FluidHalfData (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ B Tn : ℕ) (C b : ℝ) : Prop :=
  ∀ (hTn : (0 : ℝ) ≤ (Tn : ℝ)),
  ∀ (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ),
    (∀ n, IsRecord (X n) (τ n)) →
    (∀ n, C₀ * scale n ≤ level n) →
    Tendsto scale atTop atTop →
    ∀ (hscale : ∀ n, 0 < scale n),
      (∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ)) →
      (∀ (n : ℕ) (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1) →
      (∀ n, τ n (level n + B * scale n) - τ n (level n) ≤ Tn * scale n) →
      ∀ (x : ι → BoundedContinuousFunction (Set.Icc (0 : ℝ) (Tn : ℝ)) ℝ) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ i, TendstoUniformly
          (fun n => ⇑(FluidInterpolation.recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i))
          (fun t => x i t) atTop) →
        ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
          (∀ (n : ℕ) (i : ι) (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ (Tn : ℝ) →
            -(ε (φ n)) ≤
              FluidLimit.scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                  (scale (φ n)) i ⌊(scale (φ n) : ℝ) * t⌋₊
              - FluidLimit.scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n)))
                  (scale (φ n)) i ⌊(scale (φ n) : ℝ) * s⌋₊) ∧
          FluidMerge.JoinRuleFrom (FluidJoin.restrictToIcc hTn x) (64 * C) b (Tn : ℝ) ∧
          FluidMerge.StickyOn (FluidJoin.restrictToIcc hTn x) (64 * C) (Tn : ℝ)

def FluidHalfDataAll (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (C₀ B T : ℕ),
    0 ≤ b → 64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
    (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 →
    (B : ℝ) - 2 < (T : ℝ) →
    FluidHalfData (Fin N) C₀ B T (PaperBlock.Cfin (N := N) p m) b


theorem uniformHalfClause_of_fluidJoin {N : ℕ} [Nonempty (Fin N)] {C₀ B T : ℕ} {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (h64 : 64 * C ≤ (T : ℝ))
    (hBB : (1 + 64 * C) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < (T : ℝ))
    (hdat : FluidHalfData (Fin N) C₀ B T C b) :
    UniformHalfClause N C₀ B T := by
  have hTn : (0 : ℝ) ≤ (T : ℝ) := le_trans (by linarith : (0 : ℝ) ≤ 64 * C) h64
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hBB' : (1 + 64 * C) * (1 + b) ^ (Fintype.card (Fin N) - 1) - 1 < (B : ℝ) - 2 := by
    simpa using hBB
  obtain ⟨L₀, hL⟩ := FluidJoin.exists_uniform_half_of_fluid_join (ι := Fin N) C₀ B T hTn hB0
    hC hb h64 hBB' hBT (hdat hTn)
  exact ⟨L₀, fun L hL' r hr X τ hrec hnn hd ht => hL L hL' r hr X τ hrec hnn hd ht⟩


/-- **The source's §§2–8 reduce `PaperBlockGeometry` to its two surviving block inequalities.**

`(diam)` is nearest-neighbour record geometry (`HblkTwo.twoBlock_goodBlock`), so the deterministic
compactness conclusion is exactly `(time)` plus `(half)`.  The two clauses are read at the *same*
schedule `(b, T, Cerr, B, C₀)`, which is why the schedule is part of both residuals. -/
theorem paperBlockGeometry_of_time_half {p : ℝ} {m : ℕ}
    (htime : PaperTimeClause p m)
    (hhalf : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (C₀ B T : ℕ), 0 ≤ b →
      64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 →
      (B : ℝ) - 2 < (T : ℝ) →
      UniformHalfClause N C₀ B T) :
    PaperBlockGeometry p m := by
  intro N inst hN b T Cerr hb hT1 hCerr hT64 hTsch
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, C₀, L₀t, hB, hC₀, hBB, hBT, htimeU⟩ :=
    htime N hN b T Cerr hb hT1 hCerr hT64 hTsch
  obtain ⟨L₀h, hhalfU⟩ := hhalf N hN b C₀ B T hb hT64 hBB hBT
  refine ⟨B, C₀, max L₀t L₀h, hB, hC₀, hBB, hBT, ?_⟩
  intro L hL r hr U hcarr hblk
  have hLt : L₀t ≤ L := le_trans (le_max_left _ _) hL
  have hLh : L₀h ≤ L := le_trans (le_max_right _ _) hL
  have hτ : IsRecord (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) := by
    rw [Xa_eq_actX, tauA_eq]
    exact LocCoordGeomCarrier.isRecord_recTimeA_of_carrier (N := N) hcarr
  have hne : ∀ (i : Fin N) (n : ℕ),
      |PaperBlock.Xa p m U i (n + 1) - PaperBlock.Xa p m U i n| = 1 :=
    PaperBlock.Xa_step p m U
  have hdr : defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) := by
    rw [Xa_eq_actX, tauA_eq]
    exact LocCoordGeomCarrier.defect_le_of_carrier (N := N) hcarr
  have ht : PaperBlock.tauA p m U (r + B * L) - PaperBlock.tauA p m U r ≤ T * L := by
    have h := htimeU L hLt r hr U hcarr hblk
    omega
  have hh : 2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L)
      ≤ (L : ℤ) :=
    hhalfU L hLh r hr (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) hτ hne hdr ht
  have hGB : RecordoSupply.GoodBlock (defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U))
      (PaperBlock.tauA p m U) T C₀ B r L :=
    HblkTwo.twoBlock_goodBlock hτ hne (by omega : B + T + 1 ≤ C₀) hdr ht hh
  have hGS := (SwarmM4C.LawBridge.goodBlock_iff_goodSeq
    (d := defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U))
    (fun u => RecordDefect.defect_nonneg hτ u) (τ := PaperBlock.tauA p m U)).1 hGB
  simpa only [HblkFinal.arrQ, Xa_eq_actX, tauA_eq] using hGS


theorem paperBlockGeometry_of_fluid {p : ℝ} {m : ℕ}
    (htime : PaperTimeClause p m) (hfluid : FluidHalfDataAll p m) :
    PaperBlockGeometry p m :=
  paperBlockGeometry_of_time_half htime
    (fun N inst hN b C₀ B T hb h64 hBB hBT => by
      letI : Nonempty (Fin N) := inst
      exact uniformHalfClause_of_fluidJoin (N := N) (PaperBlock.Cfin_pos p m).le hb h64 hBB hBT
        (hfluid N hN b C₀ B T hb h64 hBB hBT))

/-! ## 10. The literal theorem from the paper's two surviving block inputs -/

/-- **The literal Theorem 1.1 from the paper's `(time)` clause, the promoted fluid-join `(half)`
clause, the `(lococc)` display and the `(locmove)` good-window carrier.** -/
theorem main_claim_of_fluid {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (htime : PaperTimeClause p m) (hfluid : FluidHalfDataAll p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) :=
  main_claim_of_localGood hp0 hp1 hm hocc hmove
    (paperBlockGeometry_of_fluid htime hfluid)

/-- The same reduction at the level of the paper's `(blkprob)`. -/
theorem paperBadBlockProfile_of_fluid {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (htime : PaperTimeClause p m) (hfluid : FluidHalfDataAll p m) :
    PaperBadBlockProfile p m :=
  paperBadBlockProfile_of_localGood hp0 hp1 hm hocc hmove
    (paperBlockGeometry_of_fluid htime hfluid)

/-! ## 11. The same `(half)` input from the promoted `DefectKnot` endpoint -/

/-- The knot-coalescence hypothesis of `DefectKnot.exists_uniform_half_of_knot_coalescence`,
verbatim: every compactness limit of admissible record sequences is coalesced at every fluid
time `θ ≥ B`.

This is the source's `(5.6)`/`(5.12)` read at the exact knot, and it is a deterministic statement
about the limiting fluid configuration. -/
def KnotCoalesceData (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ B Tn : ℕ) : Prop :=
  ∀ (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ),
    (∀ n, IsRecord (X n) (τ n)) →
    (∀ n, C₀ * scale n ≤ level n) →
    Tendsto scale atTop atTop →
    ∀ (hscale : ∀ n, 0 < scale n),
      (∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ)) →
      (∀ (n : ℕ) (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1) →
      (∀ n, τ n (level n + B * scale n) - τ n (level n) ≤ Tn * scale n) →
      ∀ (x : ι → BoundedContinuousFunction (Set.Icc (0 : ℝ) (Tn : ℝ)) ℝ) (φ : ℕ → ℕ),
        StrictMono φ →
        (∀ i, TendstoUniformly
          (fun n => ⇑(FluidInterpolation.recordFamily X τ level scale hscale (Tn : ℝ) (φ n) i))
          (fun t => x i t) atTop) →
        ∀ θ : Set.Icc (0 : ℝ) (Tn : ℝ), (B : ℝ) ≤ (θ : ℝ) → ∀ i j, x i θ = x j θ

/-- **The uniform `(half)` clause is the promoted `DefectKnot` endpoint.** -/
theorem uniformHalfClause_of_knotCoalescence {N : ℕ} [Nonempty (Fin N)] {C₀ B T : ℕ}
    (hdat : KnotCoalesceData (Fin N) C₀ B T) :
    UniformHalfClause N C₀ B T :=
  DefectKnot.exists_uniform_half_of_knot_coalescence C₀ B T (Nat.cast_nonneg T)
    (Nat.cast_nonneg B) hdat

/-- Knot coalescence at every admissible scale and every admissible schedule. -/
def KnotCoalesceAll (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (C₀ B T : ℕ),
    KnotCoalesceData (Fin N) C₀ B T

/-- **`PaperBlockGeometry` from the paper's `(time)` clause and knot coalescence.** -/
theorem paperBlockGeometry_of_time_knot {p : ℝ} {m : ℕ}
    (htime : PaperTimeClause p m) (hknot : KnotCoalesceAll p m) :
    PaperBlockGeometry p m :=
  paperBlockGeometry_of_time_half htime
    (fun N inst hN _b C₀ B T _ _ _ _ => by
      letI : Nonempty (Fin N) := inst
      exact uniformHalfClause_of_knotCoalescence (hknot N hN C₀ B T))

/-- **The literal Theorem 1.1 from `(time)`, knot coalescence, `(lococc)` and `(locmove)`.** -/
theorem main_claim_of_knot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (htime : PaperTimeClause p m) (hknot : KnotCoalesceAll p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) :=
  main_claim_of_localGood hp0 hp1 hm hocc hmove
    (paperBlockGeometry_of_time_knot htime hknot)

/-- The same at the level of the paper's `(blkprob)`. -/
theorem paperBadBlockProfile_of_knot {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hocc : CarrierLocOcc p m) (hmove : CarrierMove p m)
    (htime : PaperTimeClause p m) (hknot : KnotCoalesceAll p m) :
    PaperBadBlockProfile p m :=
  paperBadBlockProfile_of_localGood hp0 hp1 hm hocc hmove
    (paperBlockGeometry_of_time_knot htime hknot)

end M4D
