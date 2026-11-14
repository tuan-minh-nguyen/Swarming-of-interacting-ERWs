/-
# `(time)` at the sharp common error coefficient `CTfin = max CTtot CTocc`

`tightness/LocOccDerived.paper_local_clauses_occ` produces
`BlkCoin.BlockClauses (Xa) (tauA) (Hc) Cfin (LocOccDerived.CTfin p m T Cerr) T L r` on
`recordCarrier ∖ univBad`, from the single measured universal event.  The `(time)` clause reads
only `.base.occ`, and `ClockSharp.paperTimeClauseSharpAt` is proved at an *arbitrary* error
coefficient, so the `CTfin` instance is immediate: no separate proof, no new hypothesis.
The clock threshold `L0` is larger than at `CTtot` (`CTfin >= CTtot`), which the statement
records explicitly through `exists_L0_timeSharp`.

## Exact boundary

No probability, no measure, no `PaperBlock.MoveCarrier`.  `(half)`/`(diam)`/`BadBlk` untouched.
-/
import Swarm.ClockSharp
import Swarm.ClockBlock
import Swarm.LocOccDerived

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M3C

/-- **`(time)` at `CTfin`.**  The `LocOccDerived` lane's `BlockClauses` (with
`CTfin = max CTtot CTocc`) implies the record advance `tau (r + B*L) <= tau r + T*L` at the
paper's `(BTchoice)` schedule. -/
theorem paperTimeClauseSharpAt_CTfin (p : ℝ) (m : ℕ) :
    PaperTimeClauseSharpAt (fun T Cerr => LocOccDerived.CTfin p m T Cerr) p m :=
  paperTimeClauseSharpAt (fun T Cerr => LocOccDerived.CTfin p m T Cerr) p m

end M3C

namespace M3C

/-! ## `(block)` at `CTfin` -/

/-- **The sharp `PaperBlockGeometry` at `CTfin`**, from the paper's `(half)` clause alone: the
first block inequality is `paperTimeClauseSharpAt_CTfin`, which is the `LocOccDerived` lane. -/
theorem paperBlockGeometrySharpAt_CTfin {p : ℝ} {m : ℕ}
    (hhalf : ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N → ∀ (b : ℝ) (C₀ B T : ℕ), 0 ≤ b →
      64 * PaperBlock.Cfin (N := N) p m ≤ (T : ℝ) →
      (1 + 64 * PaperBlock.Cfin (N := N) p m) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 →
      (B : ℝ) - 2 < (T : ℝ) →
      UniformHalfClause N C₀ B T) :
    PaperBlockGeometrySharpAt (fun T Cerr => LocOccDerived.CTfin p m T Cerr) p m :=
  paperBlockGeometrySharpAt_of_time_half (fun T Cerr => LocOccDerived.CTfin p m T Cerr) hhalf

end M3C
