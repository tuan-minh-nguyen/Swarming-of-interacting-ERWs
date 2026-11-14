/-
# The `(half)` clause at the actual trajectory from the measured clauses and ONE coalescence time

`M4D.UniformHalfClause` is false (`HalfRefute.halfClause_false`) and so are its two proposed
supplies (`CoalesceRefute`).  The paper's `(half)` is *not* a statement about arbitrary record
paths: it is the deterministic content of the local-good event plus **one coalescence time** in
the sharp subwindow `[τ_r + 64⌈C⌉L, τ_{r+BL}]`.  The public `Swarm/EndpointHalving.lean`
already isolates exactly that statement (`JoinStep.halving_of_coalesce_sharp`, with the lag
*derived* from `(locmart)`+`(lococc)` and no window-lag hypothesis at all); this file instantiates
it at the actual trajectory and packages it in the `∃ L₀, ∀ L ≥ L₀` form the block geometry needs.

Residual, exactly: the block clauses at `(Cfin, CTtot)` on the record carrier (the accepted
`LocOccDerived.paper_local_clauses_occ` supplies them at `CTfin` off `univBad`), the martingale
clause `(locmart)` (`MartClause`), the explicit eventual numerical thresholds, and
**one** time `s ∈ [τ_r+64⌈C⌉L, τ_{r+BL}]` with `spreadS s ≤ HalfEps·L` — the paper's coalescence
time, i.e. the source's `NoCoalescence` complement.  No lag hypothesis, no probability, no
stationarity, no invariance.
-/
import Swarm.BlockAssembly
import Swarm.EndpointHalving

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace M1D

open RecordDefect Glue FluidLimit LocalFluid JoinStep Swarming

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- The actual trajectory carries a first-passage record clock on the record carrier. -/
theorem isRecord_Xa {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m r L : ℕ}
    {U : Swarming.Uniform.Array N} (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L) :
    IsRecord (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) := by
  rw [M4D.Xa_eq_actX, M4D.tauA_eq]
  exact LocCoordGeomCarrier.isRecord_recTimeA_of_carrier (N := N) hcarr

/-- **The `(half)` clause at the actual trajectory of `U`**, with the lag derived from `(locmart)`
and `(lococc)` and with one coalescence time in the sharp subwindow. -/
theorem halving_measured {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ} {Cerr μ : ℝ}
    {A : Fin N → ℕ → ℕ} {T L r B η s : ℕ} (U : Swarming.Uniform.Array N)
    (hcarr : U ∈ RecClockLG.recordCarrier (N := N) p m r L)
    (hBC : BlkCoin.BlockClauses (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (PaperBlock.Hc p m U)
      (PaperBlock.Cfin (N := N) p m) (PaperBlock.CTtot p m T Cerr) T L r)
    (hM : JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) A μ
      (PaperBlock.CTtot p m T Cerr) T L r)
    (hdr : defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) r ≤ (L : ℤ))
    (hr : (T + 3) * L ≤ r) (hL1 : 1 ≤ L) {i₀ j₀ : Fin N} (hij : i₀ ≠ j₀)
    (hnum : JoinStep.Numerics (PaperBlock.Cfin (N := N) p m) (PaperBlock.CTtot p m T Cerr) L)
    (hT64 : 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) ≤ T)
    (hηdef : PaperBlock.CTtot p m T Cerr * (L : ℝ) ^ (3 / 4 : ℝ) ≤ (η : ℝ))
    (hs₀ : PaperBlock.tauA p m U r + 64 * Nat.ceil (PaperBlock.Cfin (N := N) p m) * L ≤ s)
    (hspread : (Glue.spreadS (PaperBlock.Xa p m U) (Finset.univ : Finset (Fin N)) s : ℝ)
      ≤ JoinStep.HalfEps (PaperBlock.Cfin (N := N) p m) (Finset.univ : Finset (Fin N)).card
        * (L : ℝ))
    (hη : (η : ℝ) ≤ JoinStep.HalfEps (PaperBlock.Cfin (N := N) p m)
      (Finset.univ : Finset (Fin N)).card * (L : ℝ))
    (hLmin : JoinStep.HalfLmin (PaperBlock.Cfin (N := N) p m)
      (Finset.univ : Finset (Fin N)).card ≤ (L : ℝ))
    (hrecT : PaperBlock.tauA p m U (r + B * L) ≤ PaperBlock.tauA p m U r + T * L)
    (hrecB : s ≤ PaperBlock.tauA p m U (r + B * L)) :
    2 * defect (PaperBlock.Xa p m U) (PaperBlock.tauA p m U) (r + B * L) ≤ (L : ℤ) :=
  JoinStep.halving_of_coalesce_sharp (ι := Fin N) (X := PaperBlock.Xa p m U)
    (τ := PaperBlock.tauA p m U) (H := PaperBlock.Hc p m U) (A := A) (μ := μ)
    (C := PaperBlock.Cfin (N := N) p m) (CT := PaperBlock.CTtot p m T Cerr)
    (T := T) (L := L) (r := r) (η := η) (B := B) (s := s)
    (isRecord_Xa hcarr) (PaperBlock.Xa_step p m U) hBC.base hM
    (PaperBlock.Cfin_pos p m) (PaperBlock.CTtot_pos p m T Cerr).le hdr hr hL1 hij hnum hT64
    hηdef hs₀ hspread hη hLmin hrecT hrecB

