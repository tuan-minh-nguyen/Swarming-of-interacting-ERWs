/-
  **m6 / direction d11 — the down-jump and record-site halves of the above-record one-step
  conditional increment, for the actual full-history potential.**

  The above-record one-step Poisson increment of walker `i` at a site `M_n^j + G` of walker `j`
  splits, along the actual trajectory, into

      H(X_{n+1}^i) - H(X_n^i) = 1{up} h(M_n^j+G) - 1{down} h(M_n^j+G-1)

  (`PoissonStep.Hpot_traj_sub`).  The hard half is the **up** one: at `G ≥ 1` it needs the fresh
  multiplier `rhoStep p m n j (G+1)` at the *unread* site `M_n^j+G+1`, which is not
  `infoPiece p m n j G`-measurable; that is the joint-block-law link of direction A (`d1`) and is
  **not** proved here.

  This file supplies the half that needs no fresh multiplier:

  * any multiplier `f` that is bounded and `infoPiece p m n j G`-measurable pulls out of both
    jump-set conditional means at `infoPiece p m n j G` (theorems 1 and 2);
  * the **down** potential step at level `G` is exactly such an `f` — both for the
    record-restarted potential `shiftH p m n j G` (theorem 3, the object of `RecCond`) and for the
    **actual full-history** potential `shiftG (H0 p m n j) p m n j G = h_j(M_n^j + G)`
    (`ShiftedSeed.shiftG_H0`, theorem 4);
  * at the record itself (`G = 0`) even the **up** step is such an `f`: the record row is part of
    `recInfo m j 0`, so `h_j(M_n^j) = H0 p m n j` is `infoPiece p m n j 0`-measurable (theorem 5).

  Everything is at `infoPiece` (the potential step at and above the running record is *not*
  `enlFilt`-adapted, which is exactly why `PullOut.condExp_drift_of_adapted` does not apply).
-/
import Swarm.JumpRec
import Swarm.PullOut
import Swarm.ShiftedSeed
import Swarm.SeedMeas

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### The fresh left-jump law at the record-information σ-algebra -/

/-- **The fresh left-jump law at `infoPiece`.**  For distinct walkers `i ≠ j`,
`E[1{X_{n+1}^i = X_n^i - 1} | infoPiece p m n j G] = 1 - alpha_n^i`.

The left-jump companion of the compiled `condExp_stepUp_infoPiece`, obtained from the pointwise
identity `stepDownInd = 1 - stepUpInd` (`EnlDrift.stepDownInd_eq_one_sub`). -/
theorem condExp_stepDown_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (G : ℕ) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N) (stepDownInd p m n i)
      =ᵐ[arrayMeasure N] fun U => 1 - alphaFun p m n i U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : infoPiece (N := N) p m n j G ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j G
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hpt : stepDownInd p m n i = (fun _ : Array N => (1 : ℝ)) - stepUpInd p m n i := by
    funext U
    rw [Pi.sub_apply, stepDownInd_eq_one_sub]
  rw [hpt]
  have hsub := condExp_sub (μ := arrayMeasure N) (m := infoPiece (N := N) p m n j G)
    (f := fun _ : Array N => (1 : ℝ)) (g := stepUpInd p m n i)
    (integrable_const 1) (integrable_stepUpInd p m n i)
  have hc : condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun _ : Array N => (1 : ℝ))
      =ᵐ[arrayMeasure N] fun _ : Array N => (1 : ℝ) :=
    Filter.EventuallyEq.of_eq
      (condExp_const (μ := arrayMeasure N) (m := infoPiece (N := N) p m n j G) hle (1 : ℝ))
  have hup : condExp (infoPiece (N := N) p m n j G) (arrayMeasure N) (stepUpInd p m n i)
      =ᵐ[arrayMeasure N] fun U => alphaFun p m n i U :=
    condExp_stepUp_infoPiece (N := N) (m := m) (n := n) p hp0 hp1 hij G
  refine hsub.trans ?_
  filter_upwards [hc, hup] with U h1 h2
  rw [Pi.sub_apply, h1, h2]

/-! ### Bounded record-information multipliers pull out of both jump-set conditional means -/

/-- **The up-jump conditional mean with an `infoPiece`-adapted multiplier.**  For a bounded
`infoPiece p m n j G`-measurable `f`,

    E[1{up}_i · f | infoPiece p m n j G] =ᵐ alpha_n^i · f.

No freshness of `f` is used: `f` is *inside* the record information, the up/down decision is
outside it. -/
theorem condExp_stepUp_mul_of_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (G : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j G] A) {f : Array N → ℝ}
    (hf : Measurable[infoPiece (N := N) p m n j G] f) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ U, ‖f U‖ ≤ c) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepUpInd p m n i U * f U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator (fun U => alphaFun p m n i U * f U) U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : infoPiece (N := N) p m n j G ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j G
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hfmeas : Measurable[infoPiece (N := N) p m n j G]
      (fun U => A.indicator f U) := hf.indicator hA
  have hfbound : ∀ U, ‖A.indicator f U‖ ≤ c := by
    intro U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU]; exact hc U
    · rw [Set.indicator_of_notMem hU, norm_zero]; exact hc0
  have hpull := condExp_stronglyMeasurable_mul_of_bound (m := infoPiece (N := N) p m n j G) hle
    (f := fun U => A.indicator f U) (g := stepUpInd p m n i) hfmeas.stronglyMeasurable
    (integrable_stepUpInd p m n i) c (Filter.Eventually.of_forall hfbound)
  have hup : condExp (infoPiece (N := N) p m n j G) (arrayMeasure N) (stepUpInd p m n i)
      =ᵐ[arrayMeasure N] fun U => alphaFun p m n i U :=
    condExp_stepUp_infoPiece (N := N) (m := m) (n := n) p hp0 hp1 hij G
  have hfun : (fun U => A.indicator (fun U => stepUpInd p m n i U * f U) U)
      = (fun U => A.indicator f U) * stepUpInd p m n i := by
    funext U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Pi.mul_apply]
      show stepUpInd p m n i U * f U = A.indicator f U * stepUpInd p m n i U
      rw [Set.indicator_of_mem hU, mul_comm]
    · rw [Set.indicator_of_notMem hU, Pi.mul_apply]
      show (0 : ℝ) = A.indicator f U * stepUpInd p m n i U
      rw [Set.indicator_of_notMem hU, zero_mul]
  rw [hfun]
  refine hpull.trans ?_
  filter_upwards [hup] with U h3
  rw [Pi.mul_apply, h3]
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

/-- **The down-jump conditional mean with an `infoPiece`-adapted multiplier.**  For a bounded
`infoPiece p m n j G`-measurable `f`,

    E[1{down}_i · f | infoPiece p m n j G] =ᵐ (1 - alpha_n^i) · f. -/
theorem condExp_stepDown_mul_of_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (G : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j G] A) {f : Array N → ℝ}
    (hf : Measurable[infoPiece (N := N) p m n j G] f) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ U, ‖f U‖ ≤ c) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepDownInd p m n i U * f U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator (fun U => (1 - alphaFun p m n i U) * f U) U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : infoPiece (N := N) p m n j G ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j G
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hfmeas : Measurable[infoPiece (N := N) p m n j G]
      (fun U => A.indicator f U) := hf.indicator hA
  have hfbound : ∀ U, ‖A.indicator f U‖ ≤ c := by
    intro U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU]; exact hc U
    · rw [Set.indicator_of_notMem hU, norm_zero]; exact hc0
  have hpull := condExp_stronglyMeasurable_mul_of_bound (m := infoPiece (N := N) p m n j G) hle
    (f := fun U => A.indicator f U) (g := stepDownInd p m n i) hfmeas.stronglyMeasurable
    (integrable_stepDownInd p m n i) c (Filter.Eventually.of_forall hfbound)
  have hdn : condExp (infoPiece (N := N) p m n j G) (arrayMeasure N) (stepDownInd p m n i)
      =ᵐ[arrayMeasure N] fun U => 1 - alphaFun p m n i U :=
    condExp_stepDown_infoPiece (N := N) (m := m) (n := n) p hp0 hp1 hij G
  have hfun : (fun U => A.indicator (fun U => stepDownInd p m n i U * f U) U)
      = (fun U => A.indicator f U) * stepDownInd p m n i := by
    funext U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Pi.mul_apply]
      show stepDownInd p m n i U * f U = A.indicator f U * stepDownInd p m n i U
      rw [Set.indicator_of_mem hU, mul_comm]
    · rw [Set.indicator_of_notMem hU, Pi.mul_apply]
      show (0 : ℝ) = A.indicator f U * stepDownInd p m n i U
      rw [Set.indicator_of_notMem hU, zero_mul]
  rw [hfun]
  refine hpull.trans ?_
  filter_upwards [hdn] with U h3
  rw [Pi.mul_apply, h3]
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

/-- **Generic pull-out of a bounded record-information multiplier.**  For any integrable `F` and
any bounded `infoPiece p m n j G`-measurable `f`, the indicator-restricted conditional mean
factorises:

    E[1_A (F · f) | infoPiece p m n j G] =ᵐ 1_A (E[F | infoPiece p m n j G] · f).

It is the only ingredient the above-record up step needs beyond the joint block law: take
`F = stepUpInd i * rhoStep p m n j (G+1)` and `f = 1 + h_j(M_n^j+G)`, which is
`infoPiece p m n j G`-measurable and bounded (`RecSeed.measurable_shiftG`, `abs_shiftG_le`,
`ShiftedSeed.shiftG_H0`), and use the joint identity for `E[stepUpInd i * rhoStep | infoPiece]`.
The lemma itself assumes nothing about `F` beyond integrability. -/
theorem condExp_indicator_mul_of_infoPiece {p : ℝ} {m n : ℕ} {i j : Fin N} (G : ℕ)
    {A : Set (Array N)} (hA : MeasurableSet[infoPiece (N := N) p m n j G] A)
    {F : Array N → ℝ} (hF : Integrable F (arrayMeasure N)) {f : Array N → ℝ}
    (hf : Measurable[infoPiece (N := N) p m n j G] f) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ U, ‖f U‖ ≤ c) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun U => A.indicator (fun U => F U * f U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => condExp (infoPiece (N := N) p m n j G) (arrayMeasure N) F U * f U) U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : infoPiece (N := N) p m n j G ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j G
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hfmeas : Measurable[infoPiece (N := N) p m n j G] (fun U => A.indicator f U) :=
    hf.indicator hA
  have hfbound : ∀ U, ‖A.indicator f U‖ ≤ c := by
    intro U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU]; exact hc U
    · rw [Set.indicator_of_notMem hU, norm_zero]; exact hc0
  have hpull := condExp_stronglyMeasurable_mul_of_bound (m := infoPiece (N := N) p m n j G) hle
    (f := fun U => A.indicator f U) (g := F) hfmeas.stronglyMeasurable hF c
    (Filter.Eventually.of_forall hfbound)
  have hfun : (fun U => A.indicator (fun U => F U * f U) U)
      = (fun U => A.indicator f U) * F := by
    funext U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Pi.mul_apply]
      show F U * f U = A.indicator f U * F U
      rw [Set.indicator_of_mem hU, mul_comm]
    · rw [Set.indicator_of_notMem hU, Pi.mul_apply]
      show (0 : ℝ) = A.indicator f U * F U
      rw [Set.indicator_of_notMem hU, zero_mul]
  rw [hfun]
  refine hpull.trans ?_
  filter_upwards with U
  rw [Pi.mul_apply]
  by_cases hU : U ∈ A
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

/-! ### The down potential step: record-restarted and actual full-history -/

/-- **The down half above the record, record-restarted potential.**  The level-`G` potential
`shiftH p m n j G` of `RecExp`/`RecCond` is `infoPiece p m n j G`-measurable and bounded by
`2G+3`, so it pulls out of the down-jump conditional mean. -/
theorem condExp_stepDown_shiftH_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (G : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j G] A) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepDownInd p m n i U * shiftH p m n j G U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => (1 - alphaFun p m n i U) * shiftH p m n j G U) U := by
  have hpne : p ≠ 0 := by linarith
  refine condExp_stepDown_mul_of_infoPiece (N := N) p hp0 hp1 hij G hA
    (measurable_shiftH hpne m n j G) (c := 2 * ((G : ℝ)) + 3) (by positivity) ?_
  intro U
  rw [Real.norm_eq_abs]
  exact abs_shiftH_le hp0 hp1 hpne m n j G U

/-- **The down half above the record, actual full-history potential.**  By
`ShiftedSeed.shiftG_H0`, `shiftG (H0 p m n j) p m n j G = h_j(M_n^j + G)`, the paper's potential at
the absolute site `M_n^j + G`.  It is `infoPiece p m n j G`-measurable (`RecSeed.measurable_shiftG`
with the full-history seed measurability `SeedMeas.measurable_seedH`) and bounded by
`(2n+3) + 2G + 2`, so it pulls out of the down-jump conditional mean:

    E[1_A 1{down}_i h_j(M_n^j+G) | infoPiece p m n j G]
      =ᵐ 1_A (1 - alpha_n^i) h_j(M_n^j+G).

With `G = g-1` this is exactly the down step of the above-record increment at level `g ≥ 1`. -/
theorem condExp_stepDown_shiftG_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) (G : ℕ) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j G] A) :
    condExp (infoPiece (N := N) p m n j G) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepDownInd p m n i U *
          shiftG (H0 p m n j) p m n j G U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j G U) U := by
  have hpne : p ≠ 0 := by linarith
  have hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) :=
    measurable_seedH hp0.le m n j
  refine condExp_stepDown_mul_of_infoPiece (N := N) p hp0 hp1 hij G hA
    (measurable_shiftG (p := p) (h0 := H0 p m n j) (hh0 := hh0) m n j G)
    (c := 2 * (n : ℝ) + 5 + 2 * ((G : ℝ))) (by positivity) ?_
  intro U
  rw [Real.norm_eq_abs]
  have h := abs_shiftG_le hp0 hp1 (fun U => abs_H0_le hp0 hp1 hpne m n j U) m n j G U
  linarith

/-- **The level-`(g-1)` actual form** (the indexing of the above-record drift at level `g ≥ 1`):
the down step `h_j(M_n^j+g-1)` is `shiftG (H0 p m n j) p m n j (g-1)`. -/
theorem condExp_stepDown_shiftG_infoPiece_pred (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {g : ℕ} (_hg : 1 ≤ g) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j (g - 1)] A) :
    condExp (infoPiece (N := N) p m n j (g - 1)) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepDownInd p m n i U *
          shiftG (H0 p m n j) p m n j (g - 1) U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => (1 - alphaFun p m n i U) * shiftG (H0 p m n j) p m n j (g - 1) U) U :=
  condExp_stepDown_shiftG_infoPiece (N := N) (m := m) (n := n) p hp0 hp1 hij (g - 1) hA

/-- **The `hZpot` step function at an above-record site is the shifted full-history potential.**
At an integer site `x = M_n^j + G` (`G ≥ 0`, record nonnegative) the `hZpot` step function of the
actual site potential `h_j = hof p (siteMarks p m · j)` equals `shiftG (H0 p m n j) p m n j G`,
i.e. `h_j(M_n^j + G)` by `ShiftedSeed.shiftG_H0`.  This is the pointwise glue between the
`PoissonStep.Hpot_traj_sub` split and the potential-level statements above. -/
lemma hZpot_eq_shiftG_H0 {p : ℝ} (hp0 : p ≠ 0) {m n : ℕ} (j : Fin N) {G : ℕ} {U : Array N}
    (hM : 0 ≤ recVal j (prefOf p m n U)) {x : ℤ}
    (hx : x = recVal j (prefOf p m n U) + (G : ℤ)) :
    hZpot (fun k => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) x
      = shiftG (H0 p m n j) p m n j G U := by
  have hG0 : (0 : ℤ) ≤ (G : ℤ) := by exact_mod_cast Nat.zero_le G
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  rw [hZpot_of_nonneg hx0, shiftG_H0 hp0 m n j G U]
  have hidx : x.toNat = (recVal j (prefOf p m n U)).toNat + G := by
    rw [hx, Int.toNat_add hM hG0]
    simp
  rw [hidx]

/-! ### The record-site up jump -/

/-- **The record-site up term, actual full-history potential.**  At the record the multiplier is
adapted: `H0 p m n j = h_j(M_n^j)` is measurable for `enlRecMeas p m n j ⊆ infoPiece p m n j 0`
and bounded by `2n+3`.  Hence

    E[1_A 1{up}_i h_j(M_n^j) | infoPiece p m n j 0] =ᵐ 1_A alpha_n^i h_j(M_n^j)

for every `infoPiece p m n j 0`-measurable `A` — the record-boundary case of the above-record
drift, which needs no joint block law. -/
theorem condExp_stepUp_H0_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j 0] A) :
    condExp (infoPiece (N := N) p m n j 0) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepUpInd p m n i U * H0 p m n j U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => alphaFun p m n i U * H0 p m n j U) U := by
  have hpne : p ≠ 0 := by linarith
  refine condExp_stepUp_mul_of_infoPiece (N := N) p hp0 hp1 hij 0 hA ?_
    (c := 2 * (n : ℝ) + 3) (by positivity) (fun U => abs_H0_le hp0 hp1 hpne m n j U)
  exact fun s hs => enlRecMeas_le_infoPiece p m n j 0 _ (measurable_seedH hp0.le m n j hs)

/-- **The record-site up term, record-restarted potential** (`shiftH p m n j 0`, the object of
`RecExp`), for comparison with the compiled `condExp_stepUp_infoPiece`-based statements. -/
theorem condExp_stepUp_shiftH_infoPiece (p : ℝ) (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {A : Set (Array N)}
    (hA : MeasurableSet[infoPiece (N := N) p m n j 0] A) :
    condExp (infoPiece (N := N) p m n j 0) (arrayMeasure N)
        (fun U => A.indicator (fun U => stepUpInd p m n i U * shiftH p m n j 0 U) U)
      =ᵐ[arrayMeasure N] fun U => A.indicator
        (fun U => alphaFun p m n i U * shiftH p m n j 0 U) U := by
  have hpne : p ≠ 0 := by linarith
  refine condExp_stepUp_mul_of_infoPiece (N := N) p hp0 hp1 hij 0 hA
    (measurable_shiftH hpne m n j 0) (c := 3) (by norm_num) ?_
  intro U
  rw [Real.norm_eq_abs]
  have h := abs_shiftH_le hp0 hp1 hpne m n j 0 U
  rw [Nat.cast_zero, mul_zero, zero_add] at h
  exact h

end Swarming.Enl


