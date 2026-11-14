/-
# The actual `(locmart)` clause `JoinStep.MartClause` at the real record clock

Question posed by the direction: *does the public measured fibre `RecordClock.locMartGood`
supply `JoinStep.MartClause` outright, or is an exact translation needed?*

Answer: it supplies it outright, with the compensator clock being the **actual excitation
count** `A^i_n = Σ_{t<n} 1{excited}` and drift `μ = 2p-1`, i.e. exactly the paper's display
`(mart)`.  The only work is the deterministic translation

* `Swarming.Trajectory.driftMartingale p m U n i = X^i_n - (2p-1) * (excitedSteps p m U n i)`
  is *definitionally* the compensated expression of `MartClause.hbound`, so the two absolute
  values are visibly the same real number;
* `excitedSteps` is monotone in `n` (nonnegative summands over a growing `range`);
* `0 < 2p-1` for `p > 1/2`;
* the `C_T = 1` constant of the measured fibre weakens to the single paper error coefficient
  `PaperBlock.CTtot` because `3 ≤ CTtot`.

Consequences proved here, in order.

* `monotone_excitedSteps`, `two_p_sub_one_pos` - the two standing hypotheses of `MartClause`.
* `Xa_excitedSteps_martingaleEq` - the definitional identity
  `driftMartingale p m U n i
     = ((PaperBlock.Xa p m U i n : ℤ) : ℝ) - (2p-1) * ((excitedSteps p m U n i : ℕ) : ℝ)`.
* `martClause_of_locMartGood` - **`JoinStep.MartClause` on the measured good event**, at the
  actual trajectory `PaperBlock.Xa`, the real record clock `PaperBlock.tauA`, the compensator
  `excitedSteps` and `μ = 2p-1`, with the paper's error coefficient `PaperBlock.CTtot`.
  This is unconditional apart from membership in `RecordClock.locMartGood`; no carrier
  `{d_r ≤ L}`, no `(lococc)`, no coalescence time, no stationarity.
* `martClauseAt` - the same predicate packaged as a set-membership.
* `martClauseBad_subset_locMartBad` - the failure set is *contained* in the measured bad event
  of `RecordClock`, so the exponential complement profile of the good event transfers with
  **no** extra probability input.
* `measureReal_martClauseBad_le`, `exists_martClauseBad_le` - the measured profile
  `μ{¬ MartClause} ≤ exp(-c L^{1/16})` for all large `L`.
* `eventually_martClauseBad_le` - the same as an `∀ᶠ L` statement.

Exact boundary.  Nothing here asserts `(lococc)`, `MoveCarrier`, a coalescence time, `d_T`
tightness, the half clause or a common speed; and no refuted interface
(`UniformHalfClause`, `KnotCoalesceAll`, `FluidHalfDataAll`) is used.
-/
import Swarm.PaperBlock
import Swarm.OccPaperPointwise

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
open Swarming Swarming.Uniform Swarming.Trajectory SwarmRecordMeas SwarmRecordMeas.Actual

namespace M1DMart

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The two standing hypotheses of the clause -/

/-- The excitation count is nondecreasing in time: `excitedSteps n = Σ_{t<n} 1{excited}`. -/
theorem monotone_excitedSteps (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    Monotone (fun n : ℕ => excitedSteps p m U n i) := by
  intro a b hab
  have hsub : Finset.range a ⊆ Finset.range b := Finset.range_subset_range.mpr hab
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le _)

/-- The paper's drift `μ = 2p-1` is positive for `p > 1/2`. -/
theorem two_p_sub_one_pos {p : ℝ} (hp : (1 : ℝ) / 2 < p) : (0 : ℝ) < 2 * p - 1 := by
  linarith

/-! ## 2. The definitional identity behind `(locmart)` -/

/-- `driftMartingale` is literally the compensated increment appearing in
`JoinStep.MartClause.hbound`: the position as a real number minus `(2p-1)` times the
excitation count. -/
theorem Xa_excitedSteps_martingaleEq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    driftMartingale p m U n i
      = ((PaperBlock.Xa p m U i n : ℤ) : ℝ)
        - (2 * p - 1) * ((excitedSteps p m U n i : ℕ) : ℝ) := by
  simp only [driftMartingale, PaperBlock.Xa, SepGroup.Model.X]

/-! ## 3. `MartClause` on the measured good event -/

/-- **The paper's `(locmart)` clause at the actual trajectory, record clock and compensator.**

On the measured good event `RecordClock.locMartGood p m r T L` (complement
`≤ exp(-c L^{1/16})`, `RecordClock.exists_locMartBad_le`), the clause `JoinStep.MartClause`
holds with

* `X = PaperBlock.Xa p m U` (the actual positions),
* `τ = PaperBlock.tauA p m U` (the real record clock `recTimeA`),
* `A i n = excitedSteps p m U n i` (the paper's excited-step count, display `(mart)`),
* `μ = 2p-1`,
* `CT = PaperBlock.CTtot p m T Cerr` (the single paper error coefficient).

The measured fibre `OccPaperPointwise.locMartGood_paper` supplies the bound at `C_T = 1`;
`PaperBlock.three_le_CTtot` weakens it to `CTtot`. -/
theorem martClause_of_locMartGood {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m T L r : ℕ}
    {Cerr : ℝ} {U : Array N}
    (hU : U ∈ RecordClock.locMartGood (N := N) p m r T L) :
    JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
      (fun i n => excitedSteps p m U n i) (2 * p - 1)
      (PaperBlock.CTtot p m T Cerr) T L r := by
  classical
  have hL34nn : (0 : ℝ) ≤ (L : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  refine ⟨two_p_sub_one_pos hp, fun i => monotone_excitedSteps p m U i, ?_⟩
  intro i s t h1 h2 h3
  have h := OccPaperPointwise.locMartGood_paper (N := N) hU i s t h1 h2 h3
  have e1 : driftMartingale p m U t i - driftMartingale p m U s i
      = (((PaperBlock.Xa p m U i t : ℤ) : ℝ) - ((PaperBlock.Xa p m U i s : ℤ) : ℝ))
        - (2 * p - 1)
            * (((excitedSteps p m U t i : ℕ) : ℝ) - ((excitedSteps p m U s i : ℕ) : ℝ)) := by
    rw [Xa_excitedSteps_martingaleEq, Xa_excitedSteps_martingaleEq]
    ring
  rw [e1] at h
  refine le_trans h ?_
  have h3' : (1 : ℝ) ≤ PaperBlock.CTtot p m T Cerr :=
    le_trans (by norm_num) (PaperBlock.three_le_CTtot p m T Cerr)
  calc (L : ℝ) ^ ((3 : ℝ) / 4) = 1 * (L : ℝ) ^ ((3 : ℝ) / 4) := (one_mul _).symm
    _ ≤ PaperBlock.CTtot p m T Cerr * (L : ℝ) ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h3' hL34nn

/-! ## 4. The failure set and its exponential profile -/

/-- The `MartClause` predicate of §3 as a set membership. -/
def martClauseAt (p : ℝ) (m T L r : ℕ) (Cerr : ℝ) (U : Array N) : Prop :=
  JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
    (fun i n => excitedSteps p m U n i) (2 * p - 1)
    (PaperBlock.CTtot p m T Cerr) T L r

theorem mem_martClauseAt_iff {p : ℝ} {m T L r : ℕ} {Cerr : ℝ} {U : Array N} :
    martClauseAt (N := N) p m T L r Cerr U ↔
      JoinStep.MartClause (PaperBlock.Xa p m U) (PaperBlock.tauA p m U)
        (fun i n => excitedSteps p m U n i) (2 * p - 1)
        (PaperBlock.CTtot p m T Cerr) T L r := Iff.rfl

/-- The failure set of the actual `MartClause`. -/
def martClauseBad (p : ℝ) (m T L r : ℕ) (Cerr : ℝ) : Set (Array N) :=
  {U | ¬ martClauseAt (N := N) p m T L r Cerr U}

/-- **The failure set is contained in the measured bad event.**  Hence the exponential
complement profile of `RecordClock.locMartBad` pays for the `MartClause` failure with no
additional probabilistic input. -/
theorem martClauseBad_subset_locMartBad {p : ℝ} (hp : (1 : ℝ) / 2 < p)
    (m T L r : ℕ) (Cerr : ℝ) :
    martClauseBad (N := N) p m T L r Cerr ⊆ RecordClock.locMartBad (N := N) p m r T L := by
  intro U hU
  have hnot : ¬ U ∈ RecordClock.locMartGood (N := N) p m r T L :=
    fun hg => hU (martClause_of_locMartGood hp hg)
  simpa [RecordClock.locMartBad, RecordClock.locMartGood] using hnot

/-- Measured bound on the failure set, transferred from the `(locmart)` union bound. -/
theorem measureReal_martClauseBad_le {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m : ℕ}
    (r T L : ℕ) (Cerr : ℝ) :
    (arrayMeasure N).real (martClauseBad (N := N) p m T L r Cerr) ≤
      (arrayMeasure N).real (RecordClock.locMartBad (N := N) p m r T L) :=
  measureReal_mono (martClauseBad_subset_locMartBad hp m T L r Cerr) (measure_ne_top _ _)

/-- **The measured complement profile of the actual `MartClause`.**

There are `c > 0` and `L₀` such that for every `L ≥ L₀` and every record level `r`, the
probability that the actual `(locmart)` clause fails at the record window is at most
`exp(-c L^{1/16})`.  Nothing is assumed about `d_r`, `(lococc)` or a coalescence time. -/
theorem exists_martClauseBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) (hT : 1 ≤ T) (Cerr : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ r : ℕ,
      (arrayMeasure N).real (martClauseBad (N := N) p m T L r Cerr)
        ≤ Real.exp (-c * RecordClock.xOf L) := by
  obtain ⟨c, hc, L₀, hL₀⟩ := RecordClock.exists_locMartBad_le (N := N) hp0 hp1 hm hN T hT
  refine ⟨c, hc, L₀, ?_⟩
  intro L hL r
  exact le_trans (measureReal_martClauseBad_le hp0 r T L Cerr) (hL₀ L hL r)

/-- The same profile as an eventual statement in `L`. -/
theorem eventually_martClauseBad_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (T : ℕ) (hT : 1 ≤ T) (Cerr : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ,
      (arrayMeasure N).real (martClauseBad (N := N) p m T L r Cerr)
        ≤ Real.exp (-c * RecordClock.xOf L) := by
  obtain ⟨c, hc, L₀, hL₀⟩ := exists_martClauseBad_le (N := N) hp0 hp1 hm hN T hT Cerr
  exact ⟨c, hc, eventually_atTop.2 ⟨L₀, fun L hL => hL₀ L hL⟩⟩

end M1DMart
