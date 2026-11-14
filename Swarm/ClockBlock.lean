/-
# `(block)` from the proved `(time)` clause and the paper's `(half)` clause

`ClockSharp.paperTimeClauseSharp` proves the paper's `(time)` clause at the paper's own
`(BTchoice)` schedule.  This file performs the *only* remaining deterministic step of
Proposition `tight`'s block argument at that schedule:

  `(time) ∧ (half)  =>  (block)`   (`GoodSeq`),

by the paper's `(diam)` lemma, which is already public: `HblkTwo.twoBlock_goodBlock` converts
`(time)` plus `(half)` into `RecordoSupply.GoodBlock` (its third conjunct, the "`max d_u <= C₀L`"
inequality, is *derived* there from `(time)` and nearest-neighbour geometry, not assumed), and
`LawBridge.goodBlock_iff_goodSeq` restates that as the `GoodSeq` consumed by `BadBlk`.

`paperBlockGeometrySharp_of_time_half` then assembles the sharp-schedule version of
`M4D.PaperBlockGeometry`: the `∃ B C₀ L₀` is produced, `G - 1 < B - 2` (the paper's geometric
bound) and `B - 2 < T` both hold, and the pointwise conclusion `GoodSeq` holds for all
`L >= L₀`, `r >= C₀ L`, on `recordCarrier` carrying `BlkCoin.BlockClauses`.

## Exact boundary

The single remaining premise is `UniformHalfClause` — the paper's `(half)` clause — in exactly
the shape `M4D.paperBlockGeometry_of_time_half` already consumes, so a `(half)` package
(direction D) plugs in unchanged.  `(time)` is no longer a premise.  Nothing probabilistic is
proved here, no `BadBlk`/measure statement is made, no velocity is claimed.
-/
import Swarm.ClockSharp
import Swarm.HblkTwo
import Swarm.LawBridge
import Swarm.HblkFinal

open Finset MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M3C

open RecordDefect RecordoSupply SwarmRecordMeas SwarmRecordMeas.Actual

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The lane's position and clock are the actual ones -/

/-- The local-good lane's position family is the actual trajectory. -/
theorem Xa_eq_actX (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) :
    PaperBlock.Xa p m U = actX p m U := rfl

/-- The local-good lane's record clock is the canonical defaulted one. -/
theorem tauA_eq (p : ℝ) (m : ℕ) (U : Swarming.Uniform.Array N) :
    PaperBlock.tauA p m U = fun r => recTimeA p m U r := rfl

/-! ## 2. The paper's `(half)` clause, verbatim -/

/-- The paper's `(half)` clause `d_{r+BL} <= L/2`, uniformly over *all* nearest-neighbour
families with first-passage record times at every admissible starting level, on
`{d_r <= L} ∩ {(time)}`.  This is the identical statement that
`M4D.paperBlockGeometry_of_time_half` consumes, so it needs no conversion. -/
def UniformHalfClause (N : ℕ) [Nonempty (Fin N)] (C₀ B T : ℕ) : Prop :=
  ∃ L₀ : ℕ, ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
    ∀ (X : Fin N → ℕ → ℤ) (τ : ℕ → ℕ), IsRecord X τ →
      (∀ (i : Fin N) (n : ℕ), |X i (n + 1) - X i n| = 1) →
      defect X τ r ≤ (L : ℤ) →
      τ (r + B * L) - τ r ≤ T * L →
      2 * defect X τ (r + B * L) ≤ (L : ℤ)

/-! ## 3. `(time) ∧ (half) => (block)` -/

/-- **`(block)` from `(time)` and `(half)`, on the record carrier.**  Purely deterministic: the
first inequality is `htime` (supplied by the proved `(time)` clause), the second is the paper's
`(half)` clause, and the third (the "`max d_u <= C₀L`" bound) is *derived* by the public `(diam)`
lemma `HblkTwo.twoBlock_goodBlock`, exactly as in the paper. -/
theorem goodSeq_of_time_half {p : ℝ} {m : ℕ} {B C₀ T : ℕ} {r L : ℕ}
    (hC₀ : B + T + 1 ≤ C₀)
    {U : Swarming.Uniform.Array N}
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (htime : PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L)
    (hhalf : 2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) ≤ (L : ℤ)) :
    SwarmM4C.LawBridge.GoodSeq B C₀ T
      (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r L := by
  have hτ : IsRecord (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) :=
    LocCoordGeomCarrier.isRecord_recTimeA_of_carrier hcarr
  have hne : ∀ (i : Fin N) (n : ℕ),
      |PaperBlock.Xa p m U i (n + 1) - PaperBlock.Xa p m U i n| = 1 :=
    PaperBlock.Xa_step p m U
  have hdr : defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) :=
    LocCoordGeomCarrier.defect_le_of_carrier hcarr
  have ht : PaperBlock.tauA p m U (r + B * L) - PaperBlock.tauA p m U r ≤ T * L := by omega
  have hGB : RecordoSupply.GoodBlock (defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U))
      (PaperBlock.tauA p m U) T C₀ B r L :=
    HblkTwo.twoBlock_goodBlock hτ hne hC₀ hdr ht hhalf
  have hGS := (SwarmM4C.LawBridge.goodBlock_iff_goodSeq
    (d := defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U))
    (fun u => RecordDefect.defect_nonneg hτ u) (τ := PaperBlock.tauA p m U)).1 hGB
  simpa only [HblkFinal.arrQ, Xa_eq_actX, tauA_eq] using hGS

/-! ## 4. The sharp-schedule `PaperBlockGeometry` -/

/-- **`M4D.PaperBlockGeometry` at the paper's `(BTchoice)` schedule, with `(time)` proved, at an
arbitrary error coefficient `CTf T Cerr`.** -/
def PaperBlockGeometrySharpAt (CTf : ℕ → ℝ → ℝ) (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (T : ℕ) (Cerr : ℝ),
    0 ≤ b → 1 ≤ T → 1 ≤ Cerr → 64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
    (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (T : ℝ) - 3 →
    8 * PaperBlock.Cfin (N := N) p m *
        (((⌈(1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1)⌉₊ : ℕ) : ℝ) + 7)
        / 3 < (T : ℝ) →
    ∃ (B C₀ L₀ : ℕ), 1 ≤ B ∧ B + T + 3 ≤ C₀ ∧
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 ∧
      (B : ℝ) - 2 < (T : ℝ) ∧
      ∀ (L : ℕ), L₀ ≤ L → ∀ r : ℕ, C₀ * L ≤ r →
        ∀ U : Swarming.Uniform.Array N,
          U ∈ RecClockLG.recordCarrier (N := N) p m r L →
          BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
              (PaperBlock.Hc p m U) (PaperBlock.Cfin (N := N) p m)
              (CTf T Cerr) T L r →
          SwarmM4C.LawBridge.GoodSeq B C₀ T
            (HblkFinal.arrQ p m U).1 (HblkFinal.arrQ p m U).2 r L

/-- The `M4D.PaperBlockGeometry` instance: the paper's `CTtot`. -/
def PaperBlockGeometrySharp (p : ℝ) (m : ℕ) : Prop :=
  PaperBlockGeometrySharpAt (fun T Cerr => PaperBlock.CTtot p m T Cerr) p m

/-- **The paper's `(half)` clause is the only remaining block premise.**

`hhalf` has *exactly* the shape `M4D.paperBlockGeometry_of_time_half` consumes (same arguments,
same order, `UniformHalfClause` verbatim), so any `(half)` package drops in unchanged; `(time)`
is supplied by `paperTimeClauseSharpAt`.  The witness schedule is the paper's own: `B` first from
the geometric bound, `C₀ = B + T + 3`, `L₀` the max of the clock threshold and `(half)`'s.
The error coefficient `CTf` is arbitrary, so this covers both the `CTtot` lane (`M4D`) and the
sharper `CTfin` lane (`LocOccDerived`). -/
theorem paperBlockGeometrySharpAt_of_time_half (CTf : ℕ → ℝ → ℝ) {p : ℝ} {m : ℕ}
    (hhalf : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (C₀ B T : ℕ), 0 ≤ b →
      64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 →
      (B : ℝ) - 2 < (T : ℝ) →
      UniformHalfClause N C₀ B T) :
    PaperBlockGeometrySharpAt CTf p m := by
  intro N inst hN b T Cerr hb hT1 hCerr hT64 hTsch hTsharp
  have hC1 : 1 ≤ PaperBlock.Cfin (N := N) p m := PaperBlock.one_le_Cfin (N := N) p m
  -- the proved `(time)` clause supplies `B`, `C₀` and the clock threshold
  obtain ⟨B, C₀, L₀t, hB, hC₀, hBB, hBsharp, htimeU⟩ :=
    paperTimeClauseSharpAt CTf p m N hN b T Cerr hb hT1 hCerr hT64 hTsch hTsharp
  have hBT : (B : ℝ) - 2 < (T : ℝ) :=
    blt_of_sharpSchedule (B := (B : ℝ)) (T := (T : ℝ))
      (C := PaperBlock.Cfin (N := N) p m) hC1 (by exact_mod_cast hB) hBsharp
  -- the paper's `(half)` clause at the same schedule
  obtain ⟨L₀h, hhalfU⟩ := hhalf N hN b C₀ B T hb hT64 hBB hBT
  refine ⟨B, C₀, max L₀t L₀h, hB, hC₀, hBB, hBT, ?_⟩
  intro L hL r hr U hcarr hblk
  have hLt : L₀t ≤ L := le_trans (le_max_left _ _) hL
  have hLh : L₀h ≤ L := le_trans (le_max_right _ _) hL
  have hτ : IsRecord (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) :=
    LocCoordGeomCarrier.isRecord_recTimeA_of_carrier hcarr
  have hne : ∀ (i : Fin N) (n : ℕ),
      |PaperBlock.Xa p m U i (n + 1) - PaperBlock.Xa p m U i n| = 1 :=
    PaperBlock.Xa_step p m U
  have hdr : defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ) :=
    LocCoordGeomCarrier.defect_le_of_carrier hcarr
  have htim : PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L :=
    htimeU L hLt r hr U hcarr hblk
  have ht : PaperBlock.tauA p m U (r + B * L) - PaperBlock.tauA p m U r ≤ T * L := by omega
  have hh : 2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) ≤ (L : ℤ) :=
    hhalfU L hLh r hr (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) hτ hne hdr ht
  exact goodSeq_of_time_half (N := N) (C₀ := C₀) (B := B) (T := T) (r := r) (L := L)
    (by omega) hcarr htim hh

/-- The `CTtot` instance of `paperBlockGeometrySharpAt_of_time_half`. -/
theorem paperBlockGeometrySharp_of_time_half {p : ℝ} {m : ℕ}
    (hhalf : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (C₀ B T : ℕ), 0 ≤ b →
      64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 →
      (B : ℝ) - 2 < (T : ℝ) →
      UniformHalfClause N C₀ B T) :
    PaperBlockGeometrySharp p m :=
  paperBlockGeometrySharpAt_of_time_half (fun T Cerr => PaperBlock.CTtot p m T Cerr) hhalf

end M3C
