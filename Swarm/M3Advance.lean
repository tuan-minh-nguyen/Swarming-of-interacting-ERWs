/-
# Route d3: the source record-advance clause at explicit constants, from the
# excitation-occupation stall reduction

## What this file does

The frontier (`QuantitativeRestrictedBand.advanceClauseAt_of_three_tails`,
`RecordAdvanceWindow.advanceClauseAt_of_defect_and_swarmStall`) reduces the
paper's record-advance clause `SourceTightAvail.AdvanceClauseAt` to three
single-level tails, each uniform in the starting level `r >= C₀ ℓ`:

* the defect tail at the two block endpoints `r` and `r + Bℓ`, at the hardwired
  threshold `ℓ/8`;
* the swarm window-stall tail `RecordAdvanceWindow.swarmStall`.

`ExcOccupation.stall_subset_defect_union_mart` removes the excitation surplus
from the third tail: on the stall event either the defect at the record fibre is
at least `θ = cℓ/(2N)`, or some walker's drift martingale moves by `θ` inside the
window, where `c = cCoef N p m B T = (2p-1)(N-2m)T - NB`.

This file performs the *assembly* that turns that reduction into the source
clause with an explicit summable profile:

1. `defectSet_subset_defectHigh` — at the explicit parameter condition
   `c ≥ N/4` the variable-`θ` defect alternative of the stall reduction is
   contained in the hardwired `ℓ/8` defect event.  So the *same* uniform defect
   profile `q` controls the defect input of the advance clause at both block
   endpoints **and** the defect alternative of the stall reduction; no new
   defect scale is introduced.
2. `swarmStall_measure_le_add_exp` — the stall mass at level `ℓ` is at most
   `q ℓ` plus the martingale-jump profile
   `2N · exp(-θ²/(16 Tℓ))`.
3. `expRate`/`expRate_profile_le_cubic` — the exponent re-organises **exactly**
   to `exp(-α ℓ)` with `α = c²/(64 T N²)`, i.e. the profile is *geometric* in
   `ℓ` and uniformly bounded in the starting level `r`; it is therefore
   dominated by an explicit cubic profile `(96 N/α³)(ℓ+1)⁻³`.  No summability
   input is left over.
4. `advanceClauseAt_of_profiles` / `advanceClauseAt_cubic_of_profiles` — the
   literal `SourceTightAvail.AdvanceClauseAt` at `C₀ = B+T+1`, with the profile
   `q + q + (q + e)`, in cubic form.
5. `exists_T_cCoef_ge` / `exists_T_C₀_of_cubic_profiles` — for every block size
   `B ≥ 1` and every slope threshold there is an explicit `T` above both the
   source threshold `⌈2B/κ⌉₊+2` and the coefficient threshold `c ≥ N/4`; hence
   the `∀ T`-quantified consumer `SourceTightAvail.record_tightness_of_block_
   clauses_at` can be instantiated at this `T`.
6. `advanceClause_tightAvail` — the source clause `TightAvail.AdvanceClause`
   (whose `T` is *hardwired* to `⌈2B/κ⌉₊+2`) follows exactly when the
   coefficient condition `c ≥ N/4` already holds at that minimal `T`; this is
   the precise compatibility condition of the two interfaces, and it is the
   reason the `AdvanceClauseAt` family (free `T`) is the correct target.

## The two inputs that remain, stated exactly

* `DefectProfile q` (`hq`): a uniform-in-level profile for the `ℓ/8` defect at
  the actual record clock — the paper's `(tightlaw)` rate.  This is the
  pre-existing input of the frontier; it is **not** replaced or weakened here.
* `MartJumpProfile` (`hmart`): the `K`-free drift-martingale jump tail at the
  *record* fibre `τ_r`, at the single threshold `θ = cℓ/(2N)` and window
  `W = Tℓ`.  `ExcOccupation.martJumpSet_inter_recordTime_le` proves this only
  truncated to `{τ_r ≤ K}`, with the cost `(K+1)`; the truncation-free form is
  the countable clock-fibre sum, and it is consumed here as an explicit
  hypothesis of exactly that shape (no optional stopping, no record-time tail
  premise, no hidden `K`).

Nothing here proves the defect tail, the martingale-jump profile, the halving
clause, an invariant law, `MainClaim` or `PaperClaim`.
-/
import Swarm.ExcOccupation
import Swarm.RecordAdvanceWindow
import Swarm.SourceTightAvail

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace M3Advance

open Swarming Swarming.Uniform RecordDefect
open QuantitativeRestrictedBand RecordAdvanceWindow ExcOcc

variable {N m : ℕ} [Nonempty (Fin N)]

/-! ## 0. Finiteness and the real/`ℝ≥0∞` bridge on the actual array -/

theorem arrayMeasure_ne_top (s : Set (Array N)) : (arrayMeasure N) s ≠ ⊤ := by
  have h : (arrayMeasure N) s ≤ 1 := by
    have hle := measure_mono (Set.subset_univ s) (μ := arrayMeasure N)
    simpa using hle
  exact ne_top_of_le_ne_top (by simp) h

/-- The `ℝ≥0∞` measure of a set is the `ofReal` of its `Measure.real` value; this
is the only conversion used to move the `ExcOcc` real-valued Azuma bound into the
`ℝ≥0∞`-valued profile of the source clause. -/
theorem ofReal_measureReal (s : Set (Array N)) :
    ENNReal.ofReal ((arrayMeasure N).real s) = (arrayMeasure N) s := by
  rw [Measure.real_def]
  exact ENNReal.ofReal_toReal (arrayMeasure_ne_top s)

/-! ## 1. The stall set is the frontier's swarm window-stall set

`ExcOcc.stallSet` is *definitionally* `RecordAdvanceWindow.swarmStall`; recording
it as a lemma lets the `ExcOcc` reduction be applied to the frontier's event. -/

theorem stallSet_eq_swarmStall (p : ℝ) (m B T r L : ℕ) :
    ExcOcc.stallSet (N := N) p m B T r L
      = RecordAdvanceWindow.swarmStall (N := N) p m B T r L := rfl

/-! ## 2. From the variable threshold `cL/(2N)` to the hardwired defect scale `L/8`

The stall reduction produces the defect alternative at the *level-dependent*
threshold `θ_ℓ = cℓ/(2N)`, while the frontier's advance clause consumes the
defect only at the hardwired threshold `ℓ/8`.  The two thresholds are ordered
exactly when the drift coefficient dominates `N/4`; then the smaller event
`{defect ≥ θ_ℓ}` is contained in `{defect ≥ ℓ/8}`, so a single uniform profile
`q` serves both purposes. -/

theorem cCoef_eq (p : ℝ) (m B T : ℕ) :
    ExcOcc.cCoef N p m B T
      = (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (T : ℝ) - (N : ℝ) * (B : ℝ) := by
  unfold ExcOcc.cCoef
  ring

/-- The coefficient threshold `c ≥ N/4` puts `θ_ℓ = cℓ/(2N)` above `ℓ/8`. -/
theorem eighth_le_theta {p : ℝ} {m B T : ℕ} (hN : 0 < N)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T) (ℓ : ℕ) :
    (ℓ : ℝ) / 8 ≤ ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  have hkey : (ℓ : ℝ) / 8 = ((N : ℝ) / 4) * ((ℓ : ℝ) / (2 * (N : ℝ))) := by
    field_simp
    ring
  rw [hkey]
  have hpos : (0 : ℝ) ≤ (ℓ : ℝ) / (2 * (N : ℝ)) := by positivity
  calc ((N : ℝ) / 4) * ((ℓ : ℝ) / (2 * (N : ℝ)))
      ≤ ExcOcc.cCoef N p m B T * ((ℓ : ℝ) / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hc hpos
    _ = ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)) := by ring

/-- **Variable threshold ⟶ hardwired scale.**  At `c ≥ N/4` the defect
alternative of `ExcOcc.stall_subset_defect_union_mart` is contained in the
frontier's `ℓ/8` defect event at the same level `r`. -/
theorem defectSet_subset_defectHigh {p : ℝ} {m B T r ℓ : ℕ} (hN : 0 < N)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T) :
    ExcOcc.defectSet (N := N) p m r (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)))
      ⊆ QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ := by
  intro U hU
  simp only [ExcOcc.defectSet, QuantitativeRestrictedBand.defectHigh,
    Set.mem_ofPred_eq] at hU ⊢
  exact (eighth_le_theta hN hc ℓ).trans hU

/-! ## 3. The stall profile from the martingale-jump profile -/

/-- **The `K`-free drift-martingale jump profile at the record fibre.**  This is
*exactly* the statement that `ExcOccupation.martJumpSet_inter_recordTime_le`
proves with the record time truncated to `{τ_r ≤ K}` (at the cost `(K+1)`), with
the truncation removed by summation over the clock fibres `{τ_r = n}`.  The
threshold is the single one the stall reduction produces, `θ = cℓ/(2N)`, and the
window is `W = Tℓ`; the bound is uniform in the starting level `r` because both
sides only involve `ℓ`. -/
def MartJumpProfile (N : ℕ) [Nonempty (Fin N)] (p : ℝ) (m B T C₀ : ℕ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
    (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r (T * ℓ)
        (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))))
      ≤ (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
          / (16 * ((T * ℓ : ℕ) : ℝ))))

/-- **The swarm-stall tail at one level.**  The stall mass is bounded by the
uniform `ℓ/8` defect profile plus the martingale-jump profile, with no excitation
term and no record-time truncation. -/
theorem swarmStall_measure_le_add_exp {p : ℝ} (hp : (1 : ℝ) / 2 < p)
    {m B T r ℓ : ℕ} (hmN : 2 * m ≤ N) (hN : 0 < N)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T)
    (hmart : (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r (T * ℓ)
        (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))))
      ≤ (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
          / (16 * ((T * ℓ : ℕ) : ℝ))))) :
    (arrayMeasure N) (RecordAdvanceWindow.swarmStall (N := N) p m B T r ℓ)
      ≤ (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ)
        + ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
            / (16 * ((T * ℓ : ℕ) : ℝ))))) := by
  classical
  set θ : ℝ := ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ)) with hθ
  have hsub : RecordAdvanceWindow.swarmStall (N := N) p m B T r ℓ
      ⊆ QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ
        ∪ ExcOcc.martJumpSet (N := N) p m r (T * ℓ) θ := by
    rw [← stallSet_eq_swarmStall (N := N) p m B T r ℓ]
    intro U hU
    by_cases h : U ∈ ExcOcc.defectSet (N := N) p m r θ
    · exact Or.inl (defectSet_subset_defectHigh hN hc h)
    · exact Or.inr (ExcOcc.stall_subset_defect_union_mart (N := N) hp hmN hN hU h)
  calc (arrayMeasure N) (RecordAdvanceWindow.swarmStall (N := N) p m B T r ℓ)
      ≤ (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ
          ∪ ExcOcc.martJumpSet (N := N) p m r (T * ℓ) θ) := measure_mono hsub
    _ ≤ (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ)
          + (arrayMeasure N) (ExcOcc.martJumpSet (N := N) p m r (T * ℓ) θ) :=
        measure_union_le _ _
    _ ≤ (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ)
          + ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(θ ^ 2)
              / (16 * ((T * ℓ : ℕ) : ℝ))))) := by
        refine add_le_add le_rfl ?_
        rw [← ofReal_measureReal (N := N) (ExcOcc.martJumpSet (N := N) p m r (T * ℓ) θ)]
        exact ENNReal.ofReal_le_ofReal hmart


/-! ## 4. The exponent is geometric in the level

At the stall threshold `θ_ℓ = cℓ/(2N)` and window `W = Tℓ` the Azuma exponent is

  `θ_ℓ² / (16 T ℓ) = c² ℓ / (64 T N²)`,

i.e. *linear* in the level `ℓ` with rate `α = c²/(64 T N²)`, and independent of the
starting level `r`.  So the martingale-jump profile decays geometrically in `ℓ`,
uniformly in `r`; in particular it costs nothing in the campaign's cubic
summability budget. -/

/-- The rate of the record-fibre martingale-jump profile, `α = c²/(64 T N²)`. -/
noncomputable def expRate (p : ℝ) (m B T : ℕ) : ℝ :=
  ExcOcc.cCoef N p m B T ^ 2 / (64 * (T : ℝ) * (N : ℝ) ^ 2)

/-- The record-fibre martingale-jump profile `ℓ ↦ 2N exp(-α ℓ)`. -/
noncomputable def expProfile (p : ℝ) (m B T : ℕ) : ℕ → ℝ≥0∞ :=
  fun ℓ => ENNReal.ofReal ((N : ℝ) * (2 * Real.exp (-(expRate (N := N) p m B T * (ℓ : ℝ)))))

/-- Explicit cubic majorant constant of the geometric profile,
`2N + 96N/α³` (the `2N` handles the level `ℓ = 0`). -/
noncomputable def expCubic (p : ℝ) (m B T : ℕ) : ℝ :=
  2 * (N : ℝ) + 96 * (N : ℝ) / (expRate (N := N) p m B T) ^ 3

theorem expRate_pos {p : ℝ} {m B T : ℕ} (hN : 0 < N) (hT : 0 < T)
    (hc : 0 < ExcOcc.cCoef N p m B T) : 0 < expRate (N := N) p m B T := by
  unfold expRate
  have : (0 : ℝ) < (64 : ℝ) * (T : ℝ) * (N : ℝ) ^ 2 := by positivity
  positivity

/-- **Exact re-organisation of the Azuma exponent** into the linear-in-`ℓ` rate. -/
theorem theta_exp_eq {p : ℝ} {m B T ℓ : ℕ} (hN : 0 < N) (hT : 0 < T) (hℓ : 0 < ℓ) :
    -((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
        / (16 * ((T * ℓ : ℕ) : ℝ))
      = -(expRate (N := N) p m B T * (ℓ : ℝ)) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hT' : (T : ℝ) ≠ 0 := by positivity
  have hℓ' : (ℓ : ℝ) ≠ 0 := by positivity
  have hcast : ((T * ℓ : ℕ) : ℝ) = (T : ℝ) * (ℓ : ℝ) := by push_cast; ring
  unfold expRate
  rw [hcast]
  field_simp
  ring

/-- **The geometric profile is cubically dominated.**  `exp(-α x) ≤ 48/(α³(x+1)³)`
for `x ≥ 1`, from `(αx)³/6 ≤ exp(αx)`. -/
theorem exp_neg_le_cubic {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-(α * x)) ≤ 48 * (α ^ 3)⁻¹ * (x + 1)⁻¹ ^ 3 := by
  have hfac : (α * x) ^ 3 / 6 ≤ Real.exp (α * x) := by
    have h := Real.pow_div_factorial_le_exp (α * x) (le_of_lt (by positivity)) 3
    norm_num at h
    exact h
  have hpos : (0 : ℝ) < (α * x) ^ 3 / 6 := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.exp_neg]
  refine ((inv_le_inv₀ (Real.exp_pos _) hpos).2 hfac).trans ?_
  have hL : ((α * x) ^ 3 / 6)⁻¹ = 6 / (α * x) ^ 3 := by field_simp
  have hR : 48 * (α ^ 3)⁻¹ * (x + 1)⁻¹ ^ 3 = 48 / (α ^ 3 * (x + 1) ^ 3) := by
    field_simp
  rw [hL, hR, div_le_div_iff₀ (by positivity : (0 : ℝ) < (α * x) ^ 3)
        (by positivity : (0 : ℝ) < α ^ 3 * (x + 1) ^ 3)]
  have h2x : x + 1 ≤ 2 * x := by linarith
  have hcube : (x + 1) ^ 3 ≤ 8 * x ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x + 1) h2x 3
    have h2x3 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    linarith [h, h2x3.symm.le, h2x3.le]
  have hαx3 : (α * x) ^ 3 = α ^ 3 * x ^ 3 := by ring
  have hmul : 6 * (α ^ 3 * (x + 1) ^ 3) ≤ 6 * (α ^ 3 * (8 * x ^ 3)) := by
    have h6 : (0 : ℝ) ≤ 6 * α ^ 3 := by positivity
    have h := mul_le_mul_of_nonneg_left hcube h6
    calc 6 * (α ^ 3 * (x + 1) ^ 3) = (6 * α ^ 3) * (x + 1) ^ 3 := by ring
      _ ≤ (6 * α ^ 3) * (8 * x ^ 3) := h
      _ = 6 * (α ^ 3 * (8 * x ^ 3)) := by ring
  rw [hαx3]
  linarith [hmul]

/-- The geometric profile, cubically dominated with the explicit constant
`expCubic = 2N + 96N/α³`.  Valid at every level `ℓ`, including `ℓ = 0`. -/
theorem expProfile_le_cubic {p : ℝ} {m B T : ℕ} (hN : 0 < N) (hT : 0 < T)
    (hc : 0 < ExcOcc.cCoef N p m B T) :
    ∀ ℓ : ℕ, expProfile (N := N) p m B T ℓ
      ≤ ENNReal.ofReal (expCubic (N := N) p m B T * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
  intro ℓ
  have hα : 0 < expRate (N := N) p m B T := expRate_pos hN hT hc
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h96 : (0 : ℝ) ≤ 96 * (N : ℝ) / (expRate (N := N) p m B T) ^ 3 := by positivity
  have hcoef : 96 * (N : ℝ) / (expRate (N := N) p m B T) ^ 3
      ≤ expCubic (N := N) p m B T := by
    unfold expCubic
    linarith [show (0 : ℝ) ≤ 2 * (N : ℝ) by positivity]
  rcases Nat.eq_zero_or_pos ℓ with h0 | h1
  · subst h0
    apply ENNReal.ofReal_le_ofReal
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have hsimp : expCubic (N := N) p m B T * ((0 : ℝ) + 1)⁻¹ ^ 3
        = expCubic (N := N) p m B T := by norm_num
    rw [hsimp]
    unfold expCubic
    linarith
  · have hx : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h1
    have hkey : Real.exp (-(expRate (N := N) p m B T * (ℓ : ℝ)))
        ≤ 48 * ((expRate (N := N) p m B T) ^ 3)⁻¹ * ((ℓ : ℝ) + 1)⁻¹ ^ 3 :=
      exp_neg_le_cubic hα hx
    apply ENNReal.ofReal_le_ofReal
    have h2 : 2 * Real.exp (-(expRate (N := N) p m B T * (ℓ : ℝ)))
        ≤ 2 * (48 * ((expRate (N := N) p m B T) ^ 3)⁻¹ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
      linarith [hkey]
    have h3 : (N : ℝ) * (2 * Real.exp (-(expRate (N := N) p m B T * (ℓ : ℝ))))
        ≤ (N : ℝ) * (2 * (48 * ((expRate (N := N) p m B T) ^ 3)⁻¹
            * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) :=
      mul_le_mul_of_nonneg_left h2 hN0
    refine h3.trans ?_
    have hcoe : (N : ℝ) * (2 * (48 * ((expRate (N := N) p m B T) ^ 3)⁻¹
          * (((ℓ : ℝ) + 1))⁻¹ ^ 3))
        = (96 * (N : ℝ) / (expRate (N := N) p m B T) ^ 3) * (((ℓ : ℝ) + 1))⁻¹ ^ 3 := by
      field_simp
      ring
    rw [hcoe]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-! ## 5. The stall tail in profile form -/

/-- **The swarm-stall profile.**  At the explicit coefficient threshold
`c ≥ N/4` the stall mass at level `ℓ` is bounded by the uniform `ℓ/8` defect
profile plus the geometric record-fibre martingale profile; no record-time
truncation and no excitation term appear. -/
theorem swarmStall_measure_le_expProfile {p : ℝ} (hp : (1 : ℝ) / 2 < p)
    {m B T r ℓ : ℕ} (hmN : 2 * m ≤ N) (hN : 0 < N) (hT : 0 < T) (hℓ : 0 < ℓ)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T)
    (hmart : (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r (T * ℓ)
        (ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))))
      ≤ (N : ℝ) * (2 * Real.exp (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
          / (16 * ((T * ℓ : ℕ) : ℝ))))) :
    (arrayMeasure N) (RecordAdvanceWindow.swarmStall (N := N) p m B T r ℓ)
      ≤ (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ)
        + expProfile (N := N) p m B T ℓ := by
  have hcpos : 0 < ExcOcc.cCoef N p m B T := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hmain := swarmStall_measure_le_add_exp (N := N) hp hmN hN hc hmart
  have hexp : Real.exp (-((ExcOcc.cCoef N p m B T * (ℓ : ℝ) / (2 * (N : ℝ))) ^ 2)
      / (16 * ((T * ℓ : ℕ) : ℝ))) = Real.exp (-(expRate (N := N) p m B T * (ℓ : ℝ))) := by
    rw [theta_exp_eq hN hT hℓ]
  rw [hexp] at hmain
  simpa only [expProfile] using hmain


/-! ## 6. Choosing `T`: the coefficient condition and the source threshold

The stall reduction needs `c = (2p-1)(N-2m)T - NB > 0` to bite at all, and the
translation of §2 needs `c ≥ N/4`.  Both are *monotone* in `T` and both are
satisfiable at every `N > 2m` because `(2p-1)(N-2m) > 0`; the source ledger
(`SourceTightAvail.record_tightness_of_block_clauses_at`) only requires
`T ≥ ⌈2B/κ⌉₊ + 2` and `C₀ ≥ B+T+1`, so there is no obstruction to enlarging `T`.
This is what makes the *free-`T`* clause `AdvanceClauseAt` the correct target: the
source's hardwired minimal `T` in `TightAvail.AdvanceClause` may well violate
`c ≥ N/4`, and then the stall reduction is vacuous at that `T` (see
`advanceClause_tightAvail` below for the exact condition under which the
hardwired form does follow). -/

theorem cCoef_mono {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B : ℕ} (hmN : 2 * m ≤ N)
    {T₁ T₂ : ℕ} (hT : T₁ ≤ T₂) :
    ExcOcc.cCoef N p m B T₁ ≤ ExcOcc.cCoef N p m B T₂ := by
  have hA : (0 : ℝ) ≤ (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) := by
    have h1 : (0 : ℝ) ≤ 2 * p - 1 := by linarith
    have h2 : (0 : ℝ) ≤ (N : ℝ) - 2 * (m : ℝ) := by
      have h3 : ((2 * m : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
      push_cast at h3
      linarith
    exact mul_nonneg h1 h2
  have hcast : (T₁ : ℝ) ≤ (T₂ : ℝ) := by exact_mod_cast hT
  rw [cCoef_eq p m B T₁, cCoef_eq p m B T₂]
  nlinarith

/-- **The coefficient `c ≥ N/4` is reachable above any `T₀`, for every `N > 2m`.** -/
theorem exists_T_cCoef_ge {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m : ℕ} (hmN : 2 * m < N)
    (hmN' : 2 * m ≤ N) (B T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := by omega
    exact_mod_cast h
  have hApos : 0 < (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) := by
    have h1 : (0 : ℝ) < 2 * p - 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) - 2 * (m : ℝ) := by
      have h3 : ((2 * m : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hmN
      push_cast at h3
      linarith
    exact mul_pos h1 h2
  set A : ℝ := (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) with hA
  set M : ℝ := (N : ℝ) * (B : ℝ) + (N : ℝ) / 4 with hM
  refine ⟨max T₀ (max 1 ⌈M / A⌉₊), le_max_left _ _, ?_⟩
  have hmono : ExcOcc.cCoef N p m B ⌈M / A⌉₊
      ≤ ExcOcc.cCoef N p m B (max T₀ (max 1 ⌈M / A⌉₊)) :=
    cCoef_mono (N := N) hp hmN' (le_trans (le_max_right _ _) (le_max_right _ _))
  have hceil : M / A ≤ ((⌈M / A⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hbase : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B ⌈M / A⌉₊ := by
    have h2 : M ≤ A * ((⌈M / A⌉₊ : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hceil hApos.le
      have hMA : M / A * A = M := div_mul_cancel₀ M hApos.ne'
      linarith [h, hMA]
    have hce : ExcOcc.cCoef N p m B ⌈M / A⌉₊
        = A * ((⌈M / A⌉₊ : ℕ) : ℝ) - (N : ℝ) * (B : ℝ) := by
      rw [cCoef_eq p m B ⌈M / A⌉₊]
    rw [hce]
    have hMsub : M - (N : ℝ) * (B : ℝ) = (N : ℝ) / 4 := by
      rw [hM]
      ring
    linarith [h2]
  exact hbase.trans hmono

/-! ## 7. The advance clause with the geometric profile -/

/-- **Main assembly.**  At `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, `2m < N`, for any
`T ≥ 1` with `c = (2p-1)(N-2m)T - NB ≥ N/4` and `C₀ ≥ B+T+1`, the literal source
record-advance clause `SourceTightAvail.AdvanceClauseAt` holds at
`C₀ = B+T+1` with the profile

  `q + q + (q + e)`,  `e ℓ = 2N · exp(-α ℓ)`,  `α = c²/(64 T N²)`,

where `q` is *any* uniform-in-level profile for the hardwired `ℓ/8` defect and
the third `q` absorbs the defect alternative of the stall reduction.  The
martingale-jump profile `e` is uniform in the starting level `r` and geometric in
`ℓ`. -/
theorem advanceClauseAt_of_profiles {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hmN : 2 * m < N)
    (B T C₀ : ℕ) (hT : 1 ≤ T) (hC₀ : B + T + 1 ≤ C₀)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T)
    (q : ℕ → ℝ≥0∞)
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ) ≤ q ℓ)
    (hmart : MartJumpProfile N p m B T C₀) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀
      (q + q + (q + expProfile (N := N) p m B T)) := by
  have hNpos : 0 < N := by omega
  refine RecordAdvanceWindow.advanceClauseAt_of_defect_and_swarmStall (N := N) hp0 hp1 hm hN
    B T C₀ hC₀ q q (q + expProfile (N := N) p m B T) hq ?_ ?_
  · intro ℓ hℓ r hr
    exact hq ℓ hℓ (r + B * ℓ) (le_trans hr (Nat.le_add_right _ _))
  · intro ℓ hℓ r hr
    have hmain := swarmStall_measure_le_expProfile (N := N) hp0 hmN.le hNpos hT hℓ hc
      (hmart ℓ hℓ r hr)
    simpa only [Pi.add_apply] using
      hmain.trans (add_le_add (hq ℓ hℓ r hr) (le_refl (expProfile (N := N) p m B T ℓ)))

/-! ## 8. The cubic profile -/

/-- Sum of two cubically dominated profiles (the binary form of
`QuantitativeRestrictedBand.cubic_add_three`). -/
theorem cubic_add_two {q₁ q₂ : ℕ → ℝ≥0∞} {K₁ K₂ : ℝ}
    (h₁ : 0 ≤ K₁) (h₂ : 0 ≤ K₂)
    (hq₁ : ∀ ℓ : ℕ, q₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3))
    (hq₂ : ∀ ℓ : ℕ, q₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) :
    ∀ ℓ : ℕ, (q₁ + q₂) ℓ ≤
      ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
  intro ℓ
  have hA : (0 : ℝ) ≤ K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3 := by positivity
  have hB : (0 : ℝ) ≤ K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3 := by positivity
  have hadd : ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
      + ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
      = ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
    rw [← ENNReal.ofReal_add hA hB]
    congr 1
    ring
  calc (q₁ + q₂) ℓ = q₁ ℓ + q₂ ℓ := rfl
    _ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
          + ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := add_le_add (hq₁ ℓ) (hq₂ ℓ)
    _ = ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := hadd

/-- **The profile `q + q + (q + e)` is cubic.**  With `e` the geometric profile
of rate `α = c²/(64TN²)` and constant `expCubic = 2N + 96N/α³`, a cubic defect
profile `K₁(ℓ+1)⁻³` gives a cubic advance profile with constant
`3K₁ + 2N + 96N/α³`.  This is the exact constant the campaign's summability
ledger consumes; nothing is lost in the geometric tail. -/
theorem profile_cubic {p : ℝ} {m B T : ℕ} (hN : 0 < N) (hT : 0 < T)
    (hc : 0 < ExcOcc.cCoef N p m B T)
    (q : ℕ → ℝ≥0∞) {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hqc : ∀ ℓ : ℕ, q ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) :
    ∀ ℓ : ℕ, (q + q + (q + expProfile (N := N) p m B T)) ℓ
      ≤ ENNReal.ofReal ((3 * K₁ + expCubic (N := N) p m B T)
          * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
  have hE : (0 : ℝ) ≤ expCubic (N := N) p m B T := by
    have hα : 0 < expRate (N := N) p m B T := expRate_pos hN hT hc
    unfold expCubic
    positivity
  have hqq := cubic_add_two (q₁ := q) (q₂ := q) (K₁ := K₁) (K₂ := K₁) hK₁ hK₁ hqc hqc
  have hqe := cubic_add_two (q₁ := q) (q₂ := expProfile (N := N) p m B T)
    (K₁ := K₁) (K₂ := expCubic (N := N) p m B T) hK₁ hE hqc
    (expProfile_le_cubic hN hT hc)
  have h2K : (0 : ℝ) ≤ K₁ + K₁ := by linarith
  have hKE : (0 : ℝ) ≤ K₁ + expCubic (N := N) p m B T := by linarith
  have hfin := cubic_add_two (q₁ := q + q) (q₂ := q + expProfile (N := N) p m B T)
    (K₁ := K₁ + K₁) (K₂ := K₁ + expCubic (N := N) p m B T) h2K hKE hqq hqe
  intro ℓ
  refine (hfin ℓ).trans (le_of_eq ?_)
  congr 1
  ring

/-- **The advance clause with a cubic profile.**  Combines
`advanceClauseAt_of_profiles` with the cubic domination of the geometric
martingale-jump profile. -/
theorem advanceClauseAt_cubic_of_profiles {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hmN : 2 * m < N)
    (B T C₀ : ℕ) (hT : 1 ≤ T) (hC₀ : B + T + 1 ≤ C₀)
    (hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T)
    (q : ℕ → ℝ≥0∞) {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hqc : ∀ ℓ : ℕ, q ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3))
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ) ≤ q ℓ)
    (hmart : MartJumpProfile N p m B T C₀) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀
        (q + q + (q + expProfile (N := N) p m B T))
      ∧ (∀ ℓ : ℕ, (q + q + (q + expProfile (N := N) p m B T)) ℓ
          ≤ ENNReal.ofReal ((3 * K₁ + expCubic (N := N) p m B T)
              * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) := by
  have hcpos : 0 < ExcOcc.cCoef N p m B T := by
    have : (0 : ℝ) < (N : ℝ) := by
      have h : 0 < N := by omega
      exact_mod_cast h
    linarith
  exact ⟨advanceClauseAt_of_profiles (N := N) hp0 hp1 hm hN hmN B T C₀ hT hC₀ hc q hq hmart,
    profile_cubic (N := N) (by omega) hT hcpos q hK₁ hqc⟩

/-! ## 9. The source clause `TightAvail.AdvanceClause` at the hardwired `T`

`TightAvail.AdvanceClause` fixes `T = ⌈2B/κ⌉₊ + 2` and `C₀ = B+T+1`, so it is
`AdvanceClauseAt` at that *minimal* `T`.  The stall reduction then requires the
coefficient condition at that `T`, which is an explicit comparison between the
proved slope `κ` and the model parameters; it is **not** automatic, and when it
fails the hardwired form is not reachable this way (the free-`T` form is). -/

theorem advanceClause_tightAvail {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hmN : 2 * m < N)
    (B : ℕ) (κ : ℝ)
    (hcompat : (N : ℝ) / 4
      ≤ ExcOcc.cCoef N p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2))
    (q : ℕ → ℝ≥0∞)
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
      (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ) ≤ q ℓ)
    (hmart : MartJumpProfile N p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2)
      (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)) :
    TightAvail.AdvanceClause (N := N) p m B κ
      (q + q + (q + expProfile (N := N) p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2))) := by
  have hT : 1 ≤ ⌈2 * (B : ℝ) / κ⌉₊ + 2 := by omega
  have h := advanceClauseAt_of_profiles (N := N) hp0 hp1 hm hN hmN B
    (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) hT le_rfl hcompat q hq hmart
  simpa only [TightAvail.AdvanceClause, SourceTightAvail.AdvanceClauseAt] using h

/-! ## 10. The payload: actual-clock record-distance tightness

The source ledger `SourceTightAvail.record_tightness_of_block_clauses_at` produces
the ballistic slope `κ` and turns the *two* block clauses into tightness of the
actual record distance `dT` along the canonical stopped-record path law
`recordTrajT` started at `zeroState`.  Feeding it the advance clause proved above,
the advance tail disappears from its inputs: what remains is

* the uniform `ℓ/8` defect profile `q` (cubic),
* the `K`-free record-fibre martingale-jump profile `MartJumpProfile`,
* the halving clause `HalfClauseAt` at the same `C₀` (cubic),
* the explicit coefficient condition `c ≥ N/4` at the chosen `T`.

Note that the theorem is stated for every admissible pair `(T, C₀)`, so the
caller is free to take `T` above the coefficient threshold `T_c` supplied by
`exists_T_cCoef_ge`; the source threshold `T ≥ ⌈2B/κ⌉₊ + 2` and `C₀ ≥ B+T+1` are
kept verbatim. -/

theorem exists_tightness_of_cubic_profiles {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hmN : 2 * m < N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (q : ℕ → ℝ≥0∞) (K₁ : ℝ), 0 ≤ K₁ →
      (∀ ℓ : ℕ, q ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ (ℓ r : ℕ),
        (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ) ≤ q ℓ) →
      ∀ (q₂ : ℕ → ℝ≥0∞) (K₂ : ℝ), 0 ≤ K₂ →
      (∀ ℓ : ℕ, q₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      ∀ (T C₀ : ℕ), ⌈2 * (B : ℝ) / κ⌉₊ + 2 ≤ T → B + T + 1 ≤ C₀ →
      (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B T →
      MartJumpProfile N p m B T C₀ →
      SourceTightAvail.HalfClauseAt (N := N) p m B C₀ q₂ →
      ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
        (SimJump.RecKernel.recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (SwarmRecordMeas.StartLaw.zeroState (N := N) (m := m)
            (by omega : 1 ≤ m), (0 : ℕ))))
          {ω | K < SimJump.RecKernel.dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, H⟩ :=
    SourceTightAvail.record_tightness_of_block_clauses_at (N := N) hp0 hp1 hm hN B hB
  have hNpos : 0 < N := by omega
  refine ⟨κ, hκ, fun q K₁ hK₁ hqc hq q₂ K₂ hK₂ hq₂ T C₀ hT hC₀ hc hmart hhalf => ?_⟩
  have hT1 : 1 ≤ T := by omega
  have hcpos : 0 < ExcOcc.cCoef N p m B T := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    linarith
  have hE : (0 : ℝ) ≤ expCubic (N := N) p m B T := by
    have hα : 0 < expRate (N := N) p m B T := expRate_pos hNpos hT1 hcpos
    unfold expCubic
    positivity
  have hK : (0 : ℝ) ≤ 3 * K₁ + expCubic (N := N) p m B T := by linarith
  obtain ⟨hadv, hprof⟩ :=
    advanceClauseAt_cubic_of_profiles (N := N) hp0 hp1 hm hN hmN B T C₀ hT1 hC₀ hc q hK₁ hqc
      (fun ℓ _ r _ => hq ℓ r) hmart
  exact H T C₀ hT hC₀ (q + q + (q + expProfile (N := N) p m B T)) q₂
    (3 * K₁ + expCubic (N := N) p m B T) K₂ hK hK₂ hprof hq₂ hadv hhalf

/-! ## 11. Non-vacuity of the parameter regime

The assembly of §7 needs `2m < N` and `c ≥ N/4` simultaneously; both are checked
here at concrete parameters.  Nothing about the two stochastic inputs is claimed
by these examples. -/

/-- At `p = 3/4`, `N = 4`, `m = 1` (so `2m = 2 < 4 = N`), `B = 1` and `T = 5`:
`c = (2p-1)(N-2m)T - NB = (1/2)·2·5 - 4 = 1` and `N/4 = 1`, i.e. the coefficient
condition holds with equality. -/
theorem cCoef_four_example : (4 : ℝ) / 4 ≤ ExcOcc.cCoef 4 (3 / 4) 1 1 5 := by
  rw [cCoef_eq]
  norm_num

/-- The same parameters give the explicit rate `α = c²/(64 T N²) = 1/5120`. -/
theorem expRate_four_example : expRate (N := 4) (3 / 4) 1 1 5 = 1 / 5120 := by
  unfold expRate
  rw [cCoef_eq]
  norm_num

/-- The explicit cubic constant at those parameters: `expCubic = 2N + 96N/α³`
with `N = 4`, `α = 1/5120`, i.e. `8 + 384·5120³`. -/
theorem expCubic_four_example :
    expCubic (N := 4) (3 / 4) 1 1 5 = 8 + 384 * 5120 ^ 3 := by
  unfold expCubic expRate
  rw [cCoef_eq]
  norm_num

/-! ## 12. The hardwired clause at the *proved* slope bound `κ ≤ 2p-1`

`ActualInvariantKac.exists_kappa_invariant_of_advance_and_auxiliary_badTime` consumes
the *hardwired* `TightAvail.AdvanceClause` at the slope `κ` of
`ActualCanonicalRate.actual_uniform_ballistic_kappa_le`, which proves
`κ ≤ 2p-1` (public theorem `areas/assembly/ActualCanonicalRate.lean:38`; it is
cited here as a hypothesis rather than imported, to keep the dependency closure
of this package unchanged).  At that slope the minimal source choice
`T = ⌈2B/κ⌉₊ + 2 ≥ 2B/κ` already forces

  `c = (2p-1)(N-2m)T - NB ≥ (2p-1)(N-2m)·(2B/κ) - NB ≥ 2B(N-2m) - NB = B(N-4m)`,

so the coefficient condition `c ≥ N/4` holds as soon as `B(N-4m) ≥ N/4`, i.e.
`B ≥ N / (4(N-4m))`.  This is automatic for **every** `B ≥ 1` once `N ≥ 16m/3`.
In particular the stall route reaches the hardwired clause that the invariant/Kac
consumer needs, with no enlargement of `T`, on that explicit parameter range; for
`N ≤ 4m` (and for small `B` when `2m < N < 4m`) it does not, which is exactly the
limitation of using `N - 2m` excitation surplus against a block of `B` levels. -/

theorem advanceClause_tightAvail_of_kappa_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (hmN : 2 * m < N)
    (B : ℕ) {κ : ℝ} (hκpos : 0 < κ) (hκle : κ ≤ 2 * p - 1)
    (hBscale : (N : ℝ) ≤ 4 * (B : ℝ) * ((N : ℝ) - 4 * (m : ℝ)))
    (q : ℕ → ℝ≥0∞)
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
      (arrayMeasure N) (QuantitativeRestrictedBand.defectHigh (N := N) p m r ℓ) ≤ q ℓ)
    (hmart : MartJumpProfile N p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2)
      (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)) :
    TightAvail.AdvanceClause (N := N) p m B κ
      (q + q + (q + expProfile (N := N) p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2))) := by
  have ha : (0 : ℝ) < 2 * p - 1 := by linarith
  have hD : (0 : ℝ) < (N : ℝ) - 2 * (m : ℝ) := by
    have h : ((2 * m : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    push_cast at h
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := by omega
    exact_mod_cast h
  have hceil : 2 * (B : ℝ) / κ ≤ ((⌈2 * (B : ℝ) / κ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hTcast : ((⌈2 * (B : ℝ) / κ⌉₊ + 2 : ℕ) : ℝ) = ((⌈2 * (B : ℝ) / κ⌉₊ : ℕ) : ℝ) + 2 := by
    push_cast
    ring
  have hTge : 2 * (B : ℝ) / κ ≤ ((⌈2 * (B : ℝ) / κ⌉₊ + 2 : ℕ) : ℝ) := by
    rw [hTcast]
    linarith
  have hkey : 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ))
      ≤ (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * ((⌈2 * (B : ℝ) / κ⌉₊ + 2 : ℕ) : ℝ) := by
    have hcoef : (0 : ℝ) ≤ (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) :=
      le_of_lt (mul_pos ha hD)
    have hstep1 := mul_le_mul_of_nonneg_left hTge hcoef
    have hstep2 : 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ))
        ≤ (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (2 * (B : ℝ) / κ) := by
      have hrat : (1 : ℝ) ≤ (2 * p - 1) / κ := by
        rw [le_div_iff₀ hκpos]
        linarith
      have h2 : (0 : ℝ) ≤ 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ)) := by
        have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
        nlinarith [hD]
      have h3 : 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ))
          * ((2 * p - 1) / κ) = (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (2 * (B : ℝ) / κ) := by
        field_simp
      calc 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ))
          = 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ)) * 1 := by ring
        _ ≤ 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ)) * ((2 * p - 1) / κ) :=
            mul_le_mul_of_nonneg_left hrat h2
        _ = (2 * p - 1) * ((N : ℝ) - 2 * (m : ℝ)) * (2 * (B : ℝ) / κ) := h3
    linarith [hstep1, hstep2]
  have hc : (N : ℝ) / 4 ≤ ExcOcc.cCoef N p m B (⌈2 * (B : ℝ) / κ⌉₊ + 2) := by
    rw [cCoef_eq]
    have h4 : (N : ℝ) / 4 ≤ (B : ℝ) * ((N : ℝ) - 4 * (m : ℝ)) := by linarith [hBscale]
    have hNB : (N : ℝ) * (B : ℝ) - 2 * (B : ℝ) * ((N : ℝ) - 2 * (m : ℝ))
        = -((B : ℝ) * ((N : ℝ) - 4 * (m : ℝ))) := by ring
    linarith [hkey, h4, hNB]
  exact advanceClause_tightAvail (N := N) hp0 hp1 hm hN hmN B κ hc q hq hmart


/-! ## 13. No hidden strengthening of the block clauses in `C₀`

The source ledger allows any `C₀ ≥ B+T+1`, and the tightness composition of §10
is stated for every admissible `T`, hence for every `C₀` above the minimal
`B+⌈2B/κ⌉₊+3`.  Enlarging `C₀` only *shrinks* the range of starting levels
`r ≥ C₀ℓ`, so a block clause proved at a smaller `C₀` implies it at every larger
one.  Together with the analogous monotonicity of `MartJumpProfile`, this says
that the inputs consumed by §10 are exactly the paper's clauses at the minimal
constants, not strengthened versions. -/

theorem advanceClauseAt_mono_C₀ {p : ℝ} {m B T C₀ C₀' : ℕ} (hC : C₀ ≤ C₀')
    {p₁ : ℕ → ℝ≥0∞}
    (h : SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ p₁) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀' p₁ := by
  intro ℓ hℓ r hr
  exact h ℓ hℓ r (le_trans (Nat.mul_le_mul_right ℓ hC) hr)

theorem halfClauseAt_mono_C₀ {p : ℝ} {m B C₀ C₀' : ℕ} (hC : C₀ ≤ C₀')
    {p₂ : ℕ → ℝ≥0∞}
    (h : SourceTightAvail.HalfClauseAt (N := N) p m B C₀ p₂) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀' p₂ := by
  intro ℓ hℓ r hr
  exact h ℓ hℓ r (le_trans (Nat.mul_le_mul_right ℓ hC) hr)

theorem martJumpProfile_mono_C₀ {p : ℝ} {m B T C₀ C₀' : ℕ} (hC : C₀ ≤ C₀')
    (h : MartJumpProfile N p m B T C₀) : MartJumpProfile N p m B T C₀' := by
  intro ℓ hℓ r hr
  exact h ℓ hℓ r (le_trans (Nat.mul_le_mul_right ℓ hC) hr)

end M3Advance
