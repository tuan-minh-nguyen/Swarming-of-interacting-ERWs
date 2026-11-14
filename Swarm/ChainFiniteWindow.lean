/-
# The concatenated chain path is a finite function of finitely many segments

The finite-window residual `SwarmFinHorizon.FinHorizonWindow` tests `finStrict K` against path
cylinders `pathPat n ⁻¹' C`.  For that to be a *finite* word sum on the chain side, the path up to
time `max K n` must depend on finitely many enriched coordinates of the trajectory — and it does,
because every record step lasts at least one step (`cum k ≥ k`), so time `n` lies in a segment of
index `≤ n`.

This file proves that cleanly, in the form the word decomposition consumes:

* `Chain.cum_eq_of_seg_eq`, `Chain.X_eq_of_seg_eq`: two chains that agree on their first `K+1`
  segments have the same cumulative record times up to `K+1` and the same concatenated path up to
  time `K`;
* `chainOf_X_eq_of_agree`: two compatible enriched trajectories that agree on their first `K+1`
  coordinates assemble into chains with the same concatenated path up to time `K`.

So on the compatible set, `Φ` restricted to `{X ∈ finStrict K ∩ pathPat n ⁻¹' C}` is a function of
the first `max K n + 1` coordinates, and the chain side of the window family is a finite
Ionescu–Tulcea integral over at most `max K n + 1` enriched steps — i.e. a finite sum over word
sequences of bounded length, not an infinite object.  Nothing is assumed about `π` or `μ`.
-/
import Swarm.HorizonWindow
import Swarm.ChainAssemble
import Swarm.InfSeg

open MeasureTheory Set
open scoped ENNReal
open SimJump
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmRec SwarmFresh SwarmFreshPos

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmFinHorizon

variable {N m : ℕ}

/-- Two chains agreeing on their first `K+1` segments have the same record times up to `K+1`. -/
theorem Chain.cum_eq_of_seg_eq {c d : SwarmConcat.Chain N} {K : ℕ}
    (h : ∀ j, j ≤ K → c.seg j = d.seg j) :
    ∀ j, j ≤ K + 1 → c.cum j = d.cum j := by
  intro j hj
  induction j with
  | zero => rw [SwarmConcat.Chain.cum_zero, SwarmConcat.Chain.cum_zero]
  | succ j ih =>
      rw [SwarmConcat.Chain.cum_succ, SwarmConcat.Chain.cum_succ, ih (by omega)]
      rw [h j (by omega)]

/-- **The concatenated path up to time `K` only sees the first `K+1` segments.** -/
theorem Chain.X_eq_of_seg_eq {c d : SwarmConcat.Chain N} {K : ℕ}
    (h : ∀ j, j ≤ K → c.seg j = d.seg j) {n : ℕ} (hn : n ≤ K) (i : Fin N) :
    c.X n i = d.X n i := by
  have hblk : c.blk n ≤ K := by
    refine le_trans (c.blk_le ?_) hn
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (c.le_cum (n + 1))
  have h1 : c.cum (c.blk n) ≤ n := c.cum_blk_le n
  have h2 : n < c.cum (c.blk n + 1) := c.blk_spec n
  have hcum : c.cum (c.blk n) = d.cum (c.blk n) :=
    Chain.cum_eq_of_seg_eq h (c.blk n) (by omega)
  have hcum2 : c.cum (c.blk n + 1) = d.cum (c.blk n + 1) :=
    Chain.cum_eq_of_seg_eq h (c.blk n + 1) (by omega)
  have hd1 : d.cum (c.blk n) ≤ n := by rw [← hcum]; exact h1
  have hd2 : n < d.cum (c.blk n + 1) := by rw [← hcum2]; exact h2
  rw [SwarmConcat.Chain.X_block c h1 h2 i, SwarmConcat.Chain.X_block d hd1 hd2 i,
    hcum, h (c.blk n) hblk]

/-- **The assembled path is determined by the first `K+1` enriched coordinates.**  On the
compatible set, agreement of two trajectories on coordinates `0, …, K` forces agreement of the
concatenated paths at every time `≤ K`. -/
theorem chainOf_X_eq_of_agree {K : ℕ} {A A' : ℕ → SwarmConcat.Seg N × SwarmRec.RecState N m}
    (hA : SwarmChainAssemble.TrajCompat A) (hA' : SwarmChainAssemble.TrajCompat A')
    (hagree : ∀ j, j ≤ K → A j = A' j) :
    ∀ n, n ≤ K → ∀ i : Fin N,
      (SwarmChainAssemble.chainOf A).X n i = (SwarmChainAssemble.chainOf A').X n i := by
  have hseg : ∀ j, j ≤ K → (SwarmChainAssemble.chainOf A).seg j
      = (SwarmChainAssemble.chainOf A').seg j := by
    intro j hj
    rw [SwarmChainAssemble.chainOf_seg_of_compat hA,
      SwarmChainAssemble.chainOf_seg_of_compat hA', hagree j hj]
  exact fun n hn i => Chain.X_eq_of_seg_eq hseg hn i

end SwarmFinHorizon


