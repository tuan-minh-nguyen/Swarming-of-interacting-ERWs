/-
# An unconditional exponential tail for the actual canonical record clock

## The gap this file addresses

`Swarm/ExcOccupation.lean` proves

    P(stall ∩ {τ_r ≤ K}) ≤ P(defect ≥ cL/(2N)) + (K+1) N · 2 exp(-θ²/(16 T L)),   θ = c L/(2N),

and its own header says a *record-clock-tail bound is still required* to turn this into a
stall profile.  This file proves such a bound, **unconditionally and on the actual array**,
and then uses it to remove the `(K+1)` factor.

## 1. The record clock is exponentially unlikely to be late

Nothing in the model is assumed beyond `p ∈ (1/2, 1)` and `2m < N`.  Two already-proved
facts are combined:

* the deterministic excitation occupation bound `window_excOcc_sum`:
  `(N - 2m) * K ≤ Σ_i (excited steps of i before K)`;
* the two-sided Azuma bound `driftMartingale_tail` for each walker's drift martingale.

If the level-`r` record has not been reached by time `K`, then (on `ReachAll`, which is
automatic because the defaulted clock is `0` off it) every walker sits below `r`, so the
swarm's total position is `< N r`.  On the other hand the total position decomposes as
`Σ_i M^i_K + (2p-1) · Σ_i (excited steps)`, whose excitation part is at least `μ K` with
`μ = (2p-1)(N-2m)`.  Hence some walker's drift martingale is at least `ε/N` in absolute
value with `ε = μ K - N r`, and Azuma gives

    P(τ_r > K) ≤ 2 N exp(-ε²/(16 K N²)).

This is a genuine distributional tail in `K` with no invariant law, no optional stopping and
no new premise.  It is informative for `K ≳ N r / μ`, the ballistic scale of the clock; no
claim is made that the clock has a uniform-in-`r` tail, so the truncation constant is not
free — it is *paid for* by `N r / μ` steps.

## 2. The stall profile without the `(K+1)` truncation

Combining 1 with `ExcOcc.stall_measure_le_trunc` and splitting on `{τ_r ≤ K}`:

    P(stall) ≤ P(defect ≥ θ) + (K+1) · 2N · exp(-λ) + 2N · exp(-λ),      λ = θ²/(16 T L),

for **any** `K` with `2 N r ≤ K μ` and `64 N² λ ≤ K μ²` (`stall_measure_le_uncond`).
The region is nonempty as soon as `r ≤ 32 N λ / μ`, i.e. at the ballistic scale of the
record level.  There `stall_measure_le_poly` fixes `K = ⌈2Nr/μ⌉ + ⌈64N²λ/μ²⌉ + 1`, whose
prefactor is `(2 N r / μ + 64 N² λ / μ² + 4) · 2N`, polynomial in `λ` and `r`, so the stall
tail is `defect + poly · exp(-λ)`: summable in `L` exactly when the defect tail is, with no
`(K+1)` factor and no clock-tail premise.  `stall_measure_le_regime` removes `r` from the
prefactor under `r ≤ 32 N λ / μ`, and the raw jump alternative is untruncated in
`martJumpSet_measure_le_uncond`.  The defect tail at the same threshold `θ = c L/(2N)` is
left exactly where `ExcOccupation` leaves it.

## What is *not* claimed

No tightness, no `AdvanceClauseAt` instantiation, no invariant law, no ballisticity, no
removal of the defect tail, no `N = 2m` case (the clock tail needs `2m < N`), and no
axiom beyond the three standard ones.
-/
import Swarm.ExcOccupation

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open RecordDefect SwarmRecordMeas.Actual
open ExcOcc

namespace RecordClockTail

variable {N : ℕ} [Nonempty (Fin N)]

/-! ## 1. The swarm-sum drift decomposition -/

/-- Sum of the walkers' drift martingales: the drift martingale of the total position. -/
noncomputable def sumDrift (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : ℝ :=
  ∑ i : Fin N, driftMartingale p m U n i

/-- Total number of excited steps collected by the swarm before time `n`. -/
noncomputable def sumExc (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) : ℕ :=
  ∑ i : Fin N, excitedSteps p m U n i

/-- The drift martingale of a single walker vanishes at time zero. -/
theorem driftMartingale_zero (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    driftMartingale p m U 0 i = 0 := by
  have h1 : (trajectory p m U 0).pos i = 0 := ExcOcc.traj_pos_zero p m U i
  have h2 : excitedSteps p m U 0 i = 0 := rfl
  unfold driftMartingale
  rw [h1, h2]
  norm_num

/-- The total position is the swarm-sum drift martingale plus the excited drift. -/
theorem sum_pos_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    (∑ i : Fin N, ((trajectory p m U n).pos i : ℝ))
      = sumDrift p m U n + (2 * p - 1) * (sumExc p m U n : ℝ) := by
  have h1 : sumDrift p m U n
      = (∑ i : Fin N, ((trajectory p m U n).pos i : ℝ))
        - (2 * p - 1) * (sumExc p m U n : ℝ) := by
    rw [sumExc, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [driftMartingale, sumDrift]
  rw [h1]
  ring

/-- The swarm's total excitation occupation is at least `(N - 2m)` per step. -/
theorem sumExc_lower (p : ℝ) (m : ℕ) (U : Array N) (K : ℕ) :
    (N - 2 * m) * K ≤ sumExc p m U K := by
  have h := window_excOcc_sum p m U 0 K
  have hsum : (∑ i : Fin N, ExcOcc.excOcc p m U 0 K i) = sumExc p m U K := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ExcOcc.excOcc, excitedSteps, zero_add]
  rw [hsum] at h
  have h2 := Nat.sub_le_sub_right h (2 * m * K)
  rw [Nat.add_sub_cancel_left] at h2
  rw [Nat.sub_mul]
  exact h2

/-! ## 2. Positions at a late record clock -/

/-- If the level-`r` record clock has not fired by time `K`, every walker is strictly below
level `r` at time `K`. -/
theorem pos_lt_of_clock_gt {p : ℝ} {m r K : ℕ} {U : Array N}
    (hK : K < recTimeA p m U r) (i : Fin N) :
    ((trajectory p m U K).pos i : ℝ) < (r : ℝ) := by
  have hreach : U ∈ ReachAll p m := by
    by_contra hU
    rw [recTimeA_eq_zero_of_not_reach hU r] at hK
    omega
  have hrec := ExcOcc.isRecord_recTimeA_actX (N := N) hreach
  have hltZ : RecordoSupply.actX p m U i K < (r : ℤ) :=
    lt_of_le_of_lt (le_runMax (X := RecordoSupply.actX p m U) K i) ((hrec r).1 K hK)
  have hcast : ((RecordoSupply.actX p m U i K : ℤ) : ℝ) < (r : ℝ) := by exact_mod_cast hltZ
  rwa [show RecordoSupply.actX p m U i K = (trajectory p m U K).pos i from rfl] at hcast

/-! ## 2b. The deterministic ballistic time floor of the clock -/

/-- Every walker is at most at its own time. -/
theorem actX_le_time (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    RecordoSupply.actX p m U i n ≤ (n : ℤ) := by
  have h := ExcOcc.abs_pos_le p m U i n
  have hle := (abs_le.1 h).2
  exact hle

/-- The configuration maximum is at most the time. -/
theorem runMax_le_time (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) :
    runMax (RecordoSupply.actX p m U) n ≤ (n : ℤ) := by
  refine Finset.sup'_le (s := Finset.univ)
    (f := fun i => RecordoSupply.actX p m U i n) Finset.univ_nonempty (fun i _ => ?_)
  exact actX_le_time p m U i n

/-- **The record clock cannot beat the level.**  On `ReachAll` the level-`r` record needs at
least `r` steps, so a clock tail can only be informative for `K ≥ r`, i.e. for
`K ≈ N r/μ`, exactly the price paid in `recTimeA_tail`. -/
theorem le_recTimeA {p : ℝ} {m r : ℕ} {U : Array N} (hU : U ∈ ReachAll p m) :
    r ≤ recTimeA p m U r := by
  have hspec : runMax (RecordoSupply.actX p m U) (recTimeA p m U r) = (r : ℤ) :=
    (recTimeA_spec p m U r).resolve_left (fun h => h hU)
  have hle := runMax_le_time p m U (recTimeA p m U r)
  rw [hspec] at hle
  omega

/-! ## 3. The record-clock tail -/

/-- **Unconditional exponential tail of the actual canonical record clock.**
If `2m < N` and `p ∈ (1/2, 1)`, then for every `K ≥ 1` and every record level `r`,
on the actual array,

    P(τ_r > K) ≤ 2 N exp(-(μ K - N r)² / (16 K N²)),    μ = (2p-1)(N-2m),

a genuine estimate exactly when `N r < μ K`. -/
theorem recTimeA_tail {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m r K : ℕ}
    (hmN : 2 * m < N) (hK1 : 1 ≤ K)
    (hreg : (N : ℝ) * (r : ℝ) < (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))) :
    (arrayMeasure N).real {U : Array N | K < recTimeA p m U r}
      ≤ 2 * (N : ℝ) * Real.exp
          (-((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) - (N : ℝ) * (r : ℝ))
              / (N : ℝ)) ^ 2) / (16 * (K : ℝ))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ : ℝ := (2 * p - 1) * ((N : ℝ) - 2 * m) with hμ
  set ε : ℝ := (K : ℝ) * μ - (N : ℝ) * (r : ℝ) with hε
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hcpos : (0 : ℝ) < 2 * p - 1 := by linarith
  have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  have hdiff : (0 : ℝ) < (N : ℝ) - 2 * m := by linarith
  have hμpos : 0 < μ := by
    rw [hμ]
    exact mul_pos hcpos hdiff
  have hμlt : μ < (N : ℝ) := by
    have h4 : (2 * p - 1) * ((N : ℝ) - 2 * m) < 1 * ((N : ℝ) - 2 * m) :=
      mul_lt_mul_of_pos_right (by linarith) hdiff
    have h5 : (N : ℝ) - 2 * m ≤ (N : ℝ) := by linarith
    rw [hμ]
    linarith
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have hsub : {U : Array N | K < recTimeA p m U r} ⊆
      ⋃ i : Fin N, {U : Array N | ε / (N : ℝ) ≤ |driftMartingale p m U K i|} := by
    intro U hU
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    -- the total position is strictly below `N r`
    have hS : (∑ i : Fin N, ((trajectory p m U K).pos i : ℝ)) < (N : ℝ) * (r : ℝ) := by
      have hlt : ∀ i : Fin N, ((trajectory p m U K).pos i : ℝ) < (r : ℝ) :=
        fun i => pos_lt_of_clock_gt (N := N) hU i
      have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin N)))
        Finset.univ_nonempty (f := fun i => ((trajectory p m U K).pos i : ℝ))
        (g := fun _ => (r : ℝ)) (fun i _ => hlt i)
      simpa [Finset.sum_const, Finset.card_univ] using hsum
    -- the excitation part is at least `μ K`
    have hExc : μ * (K : ℝ) ≤ (2 * p - 1) * (sumExc p m U K : ℝ) := by
      have hlow := sumExc_lower p m U K
      have hcast1 : (((N - 2 * m) * K : ℕ) : ℝ) ≤ (sumExc p m U K : ℝ) := by
        exact_mod_cast hlow
      have hcast2 : (((N - 2 * m) * K : ℕ) : ℝ) = ((N : ℝ) - 2 * m) * (K : ℝ) := by
        push_cast [Nat.cast_sub (le_of_lt hmN)]
        ring
      rw [hcast2] at hcast1
      calc μ * (K : ℝ) = (2 * p - 1) * (((N : ℝ) - 2 * m) * (K : ℝ)) := by
            rw [hμ]; ring
        _ ≤ (2 * p - 1) * (sumExc p m U K : ℝ) :=
            mul_le_mul_of_nonneg_left hcast1 (le_of_lt hcpos)
    -- hence the swarm-sum martingale is strictly below `-ε`
    have hsp := sum_pos_eq p m U K
    have hD : sumDrift p m U K < -ε := by
      rw [hε]
      linarith
    -- but a sum of `N` terms each of size `< ε/N` is smaller than `ε` in absolute value
    have hsmall : |sumDrift p m U K| < ε := by
      have hrew : sumDrift p m U K = ∑ i : Fin N, driftMartingale p m U K i := rfl
      rw [hrew]
      have h1 : |∑ i : Fin N, driftMartingale p m U K i|
          ≤ ∑ i : Fin N, |driftMartingale p m U K i| := Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ i : Fin N, |driftMartingale p m U K i| < ∑ _i : Fin N, ε / (N : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
          (f := fun i => |driftMartingale p m U K i|) (g := fun _ => ε / (N : ℝ))
          (fun i _ => hcon i)
      have h3 : (∑ _i : Fin N, ε / (N : ℝ)) = ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_div_cancel₀]
        exact_mod_cast (show N ≠ 0 by omega)
      rw [h3] at h2
      linarith
    have habs : ε < |sumDrift p m U K| := by
      rw [abs_of_neg (by linarith : sumDrift p m U K < 0)]
      linarith
    linarith
  calc (arrayMeasure N).real {U : Array N | K < recTimeA p m U r}
      ≤ (arrayMeasure N).real (⋃ i : Fin N,
          {U : Array N | ε / (N : ℝ) ≤ |driftMartingale p m U K i|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i : Fin N, (arrayMeasure N).real
          {U : Array N | ε / (N : ℝ) ≤ |driftMartingale p m U K i|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin N, 2 * Real.exp (-((ε / (N : ℝ)) ^ 2) / (16 * (K : ℝ))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hεN : 0 < ε / (N : ℝ) := by positivity
        have h1 : ε ≤ (K : ℝ) * μ := by
          have hNr : (0 : ℝ) ≤ (N : ℝ) * (r : ℝ) := mul_nonneg hNpos.le hr0
          rw [hε]
          linarith
        have h2 : ε / (N : ℝ) ≤ (K : ℝ) := by
          rw [div_le_iff₀ hNpos]
          have hmul : (K : ℝ) * μ ≤ (K : ℝ) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left (le_of_lt hμlt) hKpos.le
          linarith
        have hεNK : ε / (N : ℝ) ≤ 4 * (K : ℝ) := by linarith
        have h := ExcOcc.driftMartingale_tail (N := N) hp0 hp1 m 0 K hK1 i
          (ε := ε / (N : ℝ)) hεN hεNK
        simpa only [Nat.zero_add, driftMartingale_zero, sub_zero] using h
    _ = 2 * (N : ℝ) * Real.exp (-((ε / (N : ℝ)) ^ 2) / (16 * (K : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 4. The stall threshold and exponent of `ExcOccupation` -/

/-- The stall threshold `θ = c L/(2N)` of `ExcOcc.stall_measure_le_trunc`. -/
noncomputable def stallTheta (N : ℕ) (p : ℝ) (m B T L : ℕ) : ℝ :=
  ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))

/-- The Azuma exponent `λ = θ²/(16 T L)` of the stall tail. -/
noncomputable def stallLam (N : ℕ) (p : ℝ) (m B T L : ℕ) : ℝ :=
  stallTheta N p m B T L ^ 2 / (16 * ((T * L : ℕ) : ℝ))

/-- The stall exponent is nonnegative. -/
theorem stallLam_nonneg (N : ℕ) (p : ℝ) (m B T L : ℕ) (hTL : 1 ≤ T * L) :
    0 ≤ stallLam N p m B T L := by
  have hpos : (0 : ℝ) < ((T * L : ℕ) : ℝ) := by
    have : 0 < T * L := by omega
    exact_mod_cast this
  rw [stallLam, stallTheta]
  positivity

/-- The negative exponent in the exact `Real.exp` shape used by
`ExcOcc.stall_measure_le_trunc`. -/
theorem stallLam_neg_eq (N : ℕ) (p : ℝ) (m B T L : ℕ) :
    -(stallLam N p m B T L)
      = -((ExcOcc.cCoef N p m B T * (L : ℝ) / (2 * (N : ℝ))) ^ 2)
          / (16 * ((T * L : ℕ) : ℝ)) := by
  simp only [stallLam, stallTheta]
  ring

/-- **Scalar comparison.**  Once `2 N r ≤ K μ` and `64 N² λ ≤ K μ²` with `μ = (2p-1)(N-2m)`,
the clock-tail exponent `(μ K - N r)²/(16 K N²)` dominates the stall exponent `λ`. -/
theorem stallLam_le_clockExp {p : ℝ} (hp : (1 : ℝ) / 2 < p) {m B T r L K : ℕ}
    (hmN : 2 * m < N) (hK : 0 < K)
    (hreg1 : 2 * (N : ℝ) * (r : ℝ) ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)))
    (hreg2 : 64 * (N : ℝ) ^ 2 * stallLam N p m B T L
      ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) ^ 2) :
    stallLam N p m B T L
      ≤ (((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2
          / (16 * (K : ℝ)) := by
  set μ : ℝ := (2 * p - 1) * ((N : ℝ) - 2 * m) with hμ
  set ε : ℝ := (K : ℝ) * μ - (N : ℝ) * (r : ℝ) with hε
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hcpos : (0 : ℝ) < 2 * p - 1 := by linarith
  have hμpos : 0 < μ := by
    rw [hμ]
    exact mul_pos hcpos (by linarith)
  have hεge : (K : ℝ) * μ / 2 ≤ ε := by rw [hε]; linarith
  have hKμpos : (0 : ℝ) ≤ (K : ℝ) * μ := le_of_lt (mul_pos hKpos hμpos)
  have hsq : ((K : ℝ) * μ) ^ 2 / 4 ≤ ε ^ 2 := by nlinarith [hεge, hKμpos]
  have hA : stallLam N p m B T L ≤ (K : ℝ) * μ ^ 2 / (64 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hreg2]
  have hB : (K : ℝ) * μ ^ 2 / (64 * (N : ℝ) ^ 2)
      ≤ ε ^ 2 / (16 * (N : ℝ) ^ 2 * (K : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq]
  have hC : ε ^ 2 / (16 * (N : ℝ) ^ 2 * (K : ℝ)) = (ε / (N : ℝ)) ^ 2 / (16 * (K : ℝ)) := by
    field_simp
  calc stallLam N p m B T L ≤ (K : ℝ) * μ ^ 2 / (64 * (N : ℝ) ^ 2) := hA
    _ ≤ ε ^ 2 / (16 * (N : ℝ) ^ 2 * (K : ℝ)) := hB
    _ = (ε / (N : ℝ)) ^ 2 / (16 * (K : ℝ)) := hC

/-! ## 5. The stall profile without the `(K+1)` truncation -/

/-- **The actual swarm-stall tail with no clock truncation.**
On the actual array, for `2m < N`, every `K` at the ballistic scale of the record level
(`2 N r ≤ K μ`) which is also large enough to swallow the Azuma exponent (`64 N² λ ≤ K μ²`),

    P(stall) ≤ P(defect ≥ θ) + (K+1) · 2N · exp(-λ) + 2N · exp(-λ).

The first term is the defect tail at exactly the threshold of `ExcOcc.stall_measure_le_trunc`;
the last term replaces the record-clock tail.  No optional stopping, no fibre summation and
no new hypothesis: the record-clock tail is *proved* in `recTimeA_tail`. -/
theorem stall_measure_le_uncond {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L K : ℕ} (hmN : 2 * m < N) (hW : 1 ≤ T * L)
    (hθ : 0 < stallTheta N p m B T L)
    (hθW : stallTheta N p m B T L ≤ 4 * ((T * L : ℕ) : ℝ))
    (hK1 : 1 ≤ K)
    (hreg1 : 2 * (N : ℝ) * (r : ℝ) ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)))
    (hreg2 : 64 * (N : ℝ) ^ 2 * stallLam N p m B T L
      ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) ^ 2) :
    (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
        + ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L)))
        + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hmNle : 2 * m ≤ N := le_of_lt hmN
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := by omega
  have hμpos : 0 < (2 * p - 1) * ((N : ℝ) - 2 * m) := by
    have hc : (0 : ℝ) < 2 * p - 1 := by linarith
    have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    exact mul_pos hc (by linarith)
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hreg : (N : ℝ) * (r : ℝ) < (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hKμ : 0 < (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) := mul_pos hKposR hμpos
    rcases eq_or_lt_of_le hr0 with h0 | hpos
    · rw [← h0]; simpa using hKμ
    · have hNr : (0 : ℝ) < (N : ℝ) * (r : ℝ) := by
        exact mul_pos (by exact_mod_cast (show 0 < N by omega)) hpos
      nlinarith [hreg1, hNr]
  -- split the stall set by the record clock
  have hsplit : ExcOcc.stallSet (N := N) p m B T r L ⊆
      (ExcOcc.stallSet (N := N) p m B T r L ∩ {U | recTimeA p m U r ≤ K}) ∪
        (ExcOcc.stallSet (N := N) p m B T r L ∩ {U | K < recTimeA p m U r}) := by
    intro U hU
    by_cases h : recTimeA p m U r ≤ K
    · exact Or.inl ⟨hU, h⟩
    · exact Or.inr ⟨hU, not_le.mp h⟩
  have htrunc := ExcOcc.stall_measure_le_trunc (N := N) hp0 hp1 (m := m) (B := B) (T := T)
    (r := r) (L := L) (K := K) hmNle hNpos hW hθ hθW
  have hclock := recTimeA_tail (N := N) hp0 hp1 (m := m) (r := r) (K := K) hmN hK1 hreg
  have hexp : Real.exp (-((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))
        - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2) / (16 * (K : ℝ)))
      ≤ Real.exp (-(stallLam N p m B T L)) := by
    refine Real.exp_le_exp.2 ?_
    have h := stallLam_le_clockExp (N := N) hp0 hmN hKpos hreg1 hreg2
    have heq : -((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))
          - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2) / (16 * (K : ℝ))
        = -((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))
          - (N : ℝ) * (r : ℝ)) / (N : ℝ)) ^ 2 / (16 * (K : ℝ))) := by ring
    rw [heq]
    exact neg_le_neg h
  have hclock' : (arrayMeasure N).real
        (ExcOcc.stallSet (N := N) p m B T r L ∩ {U | K < recTimeA p m U r})
      ≤ 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
    refine le_trans (measureReal_mono (Set.inter_subset_right) (measure_ne_top _ _)) ?_
    refine le_trans hclock ?_
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  calc (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real
          ((ExcOcc.stallSet (N := N) p m B T r L ∩ {U | recTimeA p m U r ≤ K}) ∪
            (ExcOcc.stallSet (N := N) p m B T r L ∩ {U | K < recTimeA p m U r})) :=
        measureReal_mono hsplit (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L ∩
            {U | recTimeA p m U r ≤ K})
          + (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L ∩
            {U | K < recTimeA p m U r}) := measureReal_union_le _ _
    _ ≤ ((arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
          + ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L))))
          + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
        refine add_le_add ?_ hclock'
        simp only [stallTheta, stallLam_neg_eq]
        exact htrunc
    _ = (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
        + ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L)))
        + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by ring

/-- **The actual record-advance failure event**, i.e. the level-`(r+BL)` record has not been
reached `T L` steps after the level-`r` record, has the same unconditional bound.  This is
the literal event of `ExcOcc.timeLag_subset_stallSet`; the `AdvanceClauseAt` profile
assembly is not performed here. -/
theorem timeLag_measure_le_uncond {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L K : ℕ} (hmN : 2 * m < N) (hW : 1 ≤ T * L)
    (hθ : 0 < stallTheta N p m B T L)
    (hθW : stallTheta N p m B T L ≤ 4 * ((T * L : ℕ) : ℝ))
    (hK1 : 1 ≤ K)
    (hreg1 : 2 * (N : ℝ) * (r : ℝ) ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)))
    (hreg2 : 64 * (N : ℝ) ^ 2 * stallLam N p m B T L
      ≤ (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) ^ 2) :
    (arrayMeasure N).real
        {U : Array N | recTimeA p m U r + T * L < recTimeA p m U (r + B * L)}
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
        + ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L)))
        + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine le_trans (measureReal_mono (ExcOcc.timeLag_subset_stallSet (N := N) p m B T r L)
    (measure_ne_top _ _)) ?_
  exact stall_measure_le_uncond (N := N) hp0 hp1 hmN hW hθ hθW hK1 hreg1 hreg2

/-- **The stall profile with a canonical clock constant.**
No free truncation constant survives: `K` is chosen as
`⌈2 N r / μ⌉ + ⌈64 N² λ / μ²⌉ + 1` with `μ = (2p-1)(N-2m)`, and the cost is stated with the
explicit polynomial prefactor `2 N r / μ + 64 N² λ / μ² + 4` in front of `exp(-λ)`.
The defect term is the same thresholded defect tail as in `ExcOcc`. -/
theorem stall_measure_le_poly {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hmN : 2 * m < N) (hW : 1 ≤ T * L)
    (hθ : 0 < stallTheta N p m B T L)
    (hθW : stallTheta N p m B T L ≤ 4 * ((T * L : ℕ) : ℝ)) :
    (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
        + (2 * (N : ℝ) * (r : ℝ) / ((2 * p - 1) * ((N : ℝ) - 2 * m))
            + 64 * (N : ℝ) ^ 2 * stallLam N p m B T L
                / ((2 * p - 1) * ((N : ℝ) - 2 * m)) ^ 2 + 4)
          * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L)))
        + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  set μ : ℝ := (2 * p - 1) * ((N : ℝ) - 2 * m) with hμ
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hμpos : 0 < μ := by
    have hc : (0 : ℝ) < 2 * p - 1 := by linarith
    have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    rw [hμ]
    exact mul_pos hc (by linarith)
  set K : ℕ := Nat.ceil (2 * (N : ℝ) * (r : ℝ) / μ)
    + Nat.ceil (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2) + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hKcast : (K : ℝ) = (Nat.ceil (2 * (N : ℝ) * (r : ℝ) / μ) : ℝ)
      + (Nat.ceil (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2) : ℝ) + 1 := by
    rw [hK]; push_cast; ring
  have hx : 2 * (N : ℝ) * (r : ℝ) / μ ≤ (K : ℝ) := by
    have h1 := Nat.le_ceil (2 * (N : ℝ) * (r : ℝ) / μ)
    have h2 : (0 : ℝ) ≤ (Nat.ceil (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2) : ℝ) :=
      Nat.cast_nonneg _
    rw [hKcast]; linarith
  have hy : 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 ≤ (K : ℝ) := by
    have h1 := Nat.le_ceil (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2)
    have h2 : (0 : ℝ) ≤ (Nat.ceil (2 * (N : ℝ) * (r : ℝ) / μ) : ℝ) := Nat.cast_nonneg _
    rw [hKcast]; linarith
  have hreg1 : 2 * (N : ℝ) * (r : ℝ) ≤ (K : ℝ) * μ := by
    rw [div_le_iff₀ hμpos] at hx
    linarith
  have hreg2 : 64 * (N : ℝ) ^ 2 * stallLam N p m B T L ≤ (K : ℝ) * μ ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < μ ^ 2)] at hy
    linarith
  have hKbound : ((K : ℝ) + 1)
      ≤ 2 * (N : ℝ) * (r : ℝ) / μ + 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4 := by
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (N : ℝ) * (r : ℝ) / μ by positivity)
    have hL0 : (0 : ℝ) ≤ stallLam N p m B T L := stallLam_nonneg N p m B T L hW
    have h2 := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 by positivity)
    rw [hKcast]; linarith
  refine le_trans (stall_measure_le_uncond (N := N) hp0 hp1 hmN hW hθ hθW hK1 hreg1 hreg2) ?_
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKbound (by positivity)) (by positivity)

/-- **The stall profile with a level-independent prefactor.**  In the regime
`r ≤ 32 N λ / μ` the canonical clock constant of `stall_measure_le_poly` costs at most
`128 N² λ / μ² + 4`, so the stall tail is

    P(stall) ≤ P(defect ≥ θ) + (128 N² λ / μ² + 4) · 2N · exp(-λ) + 2N · exp(-λ),

a bound whose prefactor involves only `N`, `p`, `m`, `B`, `T`, `L` and not the record level
`r`.  Since `λ = c² L /(64 T N²)` this is `poly(L) · exp(-c² L/(64 T N²))`. -/
theorem stall_measure_le_regime {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m B T r L : ℕ} (hmN : 2 * m < N) (hW : 1 ≤ T * L)
    (hθ : 0 < stallTheta N p m B T L)
    (hθW : stallTheta N p m B T L ≤ 4 * ((T * L : ℕ) : ℝ))
    (hregime : 2 * (N : ℝ) * (r : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))
      ≤ 64 * (N : ℝ) ^ 2 * stallLam N p m B T L) :
    (arrayMeasure N).real (ExcOcc.stallSet (N := N) p m B T r L)
      ≤ (arrayMeasure N).real (ExcOcc.defectSet (N := N) p m r (stallTheta N p m B T L))
        + (128 * (N : ℝ) ^ 2 * stallLam N p m B T L
            / ((2 * p - 1) * ((N : ℝ) - 2 * m)) ^ 2 + 4)
          * (N : ℝ) * (2 * Real.exp (-(stallLam N p m B T L)))
        + 2 * (N : ℝ) * Real.exp (-(stallLam N p m B T L)) := by
  set μ : ℝ := (2 * p - 1) * ((N : ℝ) - 2 * m) with hμ
  have hμpos : 0 < μ := by
    have hc : (0 : ℝ) < 2 * p - 1 := by linarith
    have h2mN : (2 * m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    rw [hμ]
    exact mul_pos hc (by linarith)
  have hkey : 2 * (N : ℝ) * (r : ℝ) / μ ≤ 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 := by
    rw [div_le_div_iff₀ hμpos (by positivity : (0 : ℝ) < μ ^ 2)]
    nlinarith [hregime]
  refine le_trans (stall_measure_le_poly (N := N) hp0 hp1 hmN hW hθ hθW) ?_
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
  have hstep : 2 * (N : ℝ) * (r : ℝ) / μ
        + (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4)
      ≤ 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2
        + (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4) :=
    add_le_add hkey (le_refl _)
  have hgoal : 2 * (N : ℝ) * (r : ℝ) / μ
        + 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4
      ≤ 128 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4 := by
    calc 2 * (N : ℝ) * (r : ℝ) / μ
          + 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4
        = 2 * (N : ℝ) * (r : ℝ) / μ
          + (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4) := by ring
      _ ≤ 64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2
          + (64 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4) := hstep
      _ = 128 * (N : ℝ) ^ 2 * stallLam N p m B T L / μ ^ 2 + 4 := by ring
  simpa only [hμ] using hgoal

/-- **The raw martingale-jump alternative, untruncated.**  The clock tail also removes the
truncation from `ExcOcc.martJumpSet_inter_recordTime_le` itself: no restriction on the record
clock is needed, only the (proved) tail of the clock.  The prefactor stays polynomial in `K`. -/
theorem martJumpSet_measure_le_uncond {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m r W K : ℕ} (hmN : 2 * m < N) (hW : 1 ≤ W) {θ : ℝ} (hθ : 0 < θ)
    (hθW : θ ≤ 4 * ((W : ℕ) : ℝ)) (hK1 : 1 ≤ K)
    (hreg : (N : ℝ) * (r : ℝ) < (K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m))) :
    (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r W θ)
      ≤ ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * ((W : ℕ) : ℝ))))
        + 2 * (N : ℝ) * Real.exp
            (-((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) - (N : ℝ) * (r : ℝ))
              / (N : ℝ)) ^ 2) / (16 * (K : ℝ))) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsplit : ExcOcc.martJumpSet (N := N) p m r W θ ⊆
      (ExcOcc.martJumpSet (N := N) p m r W θ ∩ {U | recTimeA p m U r ≤ K}) ∪
        {U | K < recTimeA p m U r} := by
    intro U hU
    by_cases h : recTimeA p m U r ≤ K
    · exact Or.inl ⟨hU, h⟩
    · exact Or.inr (not_le.mp h)
  have htrunc := ExcOcc.martJumpSet_inter_recordTime_le (N := N) hp0 hp1 (m := m) (r := r)
    (W := W) (K := K) hW hθ hθW
  have hclock := recTimeA_tail (N := N) hp0 hp1 (m := m) (r := r) (K := K) hmN hK1 hreg
  calc (arrayMeasure N).real (ExcOcc.martJumpSet (N := N) p m r W θ)
      ≤ (arrayMeasure N).real
          ((ExcOcc.martJumpSet (N := N) p m r W θ ∩ {U | recTimeA p m U r ≤ K}) ∪
            {U | K < recTimeA p m U r}) := measureReal_mono hsplit (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real
          (ExcOcc.martJumpSet (N := N) p m r W θ ∩ {U | recTimeA p m U r ≤ K})
        + (arrayMeasure N).real {U | K < recTimeA p m U r} := measureReal_union_le _ _
    _ ≤ ((K : ℝ) + 1) * (N : ℝ) * (2 * Real.exp (-(θ ^ 2) / (16 * ((W : ℕ) : ℝ))))
        + 2 * (N : ℝ) * Real.exp
            (-((((K : ℝ) * ((2 * p - 1) * ((N : ℝ) - 2 * m)) - (N : ℝ) * (r : ℝ))
              / (N : ℝ)) ^ 2) / (16 * (K : ℝ))) := add_le_add htrunc hclock

end RecordClockTail
