/-
  **Direction B: the exact shifted full-history potential and its deterministic bound.**

  `RecSeed.lean` proves the projected recursion

      `E[Φ^g h0 | enlRecMeas] =ᵐ Φ_det^g h0`

  for an *arbitrary* seed `h0` that is `enlRecMeas`-measurable, integrable and deterministically
  bounded, where `Φ^g h0` is driven by the marks at the sites `M, M+1, …` above the running record
  `M = M_n^j = recVal j (prefOf p m n U)`.  It does **not** identify `Φ^g h0` with the paper's
  full-history potential `h_j(M+g)`.

  This file closes exactly that identification, for the actual trajectory
  `Swarming.Trajectory.trajectory`, the actual `arrayMeasure N`, and the actual site-mark sequence
  `SwarmLogRatio.siteMarks p m U j` on nonnegative sites:

  * `siteMarks_eq_markB_ofNat` — the actual site mark at a natural site `x` is the `Bool` mark
    `markB` at the integer site `(x : ℤ)`; this is the only point where `decide` and
    `if … then true else false` have to be reconciled.
  * `natCast_toNat_add` — `((M.toNat + k : ℕ) : ℤ) = M + k` for `0 ≤ M` (`Int.toNat_of_nonneg`).
  * `markSeq_eq_siteMarks` — the `k`-th mark above the record in the sense of `RecExp.markSeq` is
    the actual mark at the site `M + k`.
  * `shiftG_H0` — **exact shifted identification**:
    `shiftG H0 p m n j g U = hof p (siteMarks p m U j) (M.toNat + g)` for every `g`, where
    `H0 U = hof p (siteMarks p m U j) M.toNat` is the paper's full-history seed `h_j(M)`.
  * `abs_H0_le` — the deterministic bound `|H0 U| ≤ 2 n + 3`, from
    `SwarmShiftMarks.abs_hof_le'` (`|hof| ≤ 2n+3`) and the record bound `M ≤ n`
    (`recVal_prefOf_le_time`).
  * `recSeed_hypotheses` / `condExp_H0` — with **one** explicit input, measurability of `H0` for
    `enlRecMeas`, all `RecSeed` hypotheses are discharged and the projected recursion is obtained
    for the actual full-history potential.

  There is **no** projected-law transport here: everything is pointwise algebra on the actual
  array, plus the generic conditional-expectation API of `RecSeed`.  In particular this file does
  not prove `H0` to be `enlRecMeas`-measurable (direction A's target), it records that as the
  single remaining instantiation link.  `Joint.lean` in this directory removes even that input by
  importing direction A's `SeedMeas` and applying its `measurable_seedH`.

  Negative sites do not occur: the record is nonnegative (`zero_le_recVal_prefOf`) and the index
  `M.toNat + g` is the natural-number reading of the integer site `M + g`.
-/
import Swarm.RecSeed
import Swarm.RawLogRatio
import Swarm.ShiftRecMarks

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### 1. The actual site marks and the shifted mark sequence

`RecExp.markSeq` reads `markB p m j (M + k) U`; the actual mark sequence `siteMarks` reads the
same site at a natural index.  The two agree after the `ℤ`/`ℕ` conversion of the record. -/

/-- The `Bool` mark at a fixed site is `true` exactly at a marked site. -/
lemma markB_eq_true {p : ℝ} {m : ℕ} {j : Fin N} {x : ℤ} {U : Array N} :
    markB p m j x U = true ↔ SiteMark p m U j x := by
  constructor
  · intro h
    by_contra hc
    rw [markB_neg hc] at h
    exact Bool.false_ne_true h
  · exact markB_pos

/-- **The actual mark at a natural site.**  `SwarmLogRatio.siteMarks` is `decide (SiteMark …)`; at
`x : ℕ` this is the `Bool` mark `markB` at the integer site `(x : ℤ)`. -/
lemma siteMarks_eq_markB_ofNat {p : ℝ} (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) :
    SwarmLogRatio.siteMarks p m U j x = markB p m j (x : ℤ) U := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    rw [show SwarmLogRatio.siteMarks p m U j x = true ↔ SiteMark p m U j (x : ℤ) from by
      classical
      simp only [SwarmLogRatio.siteMarks]
      exact decide_eq_true_iff] at h
    exact (markB_eq_true).mpr h
  · intro h
    rw [show SwarmLogRatio.siteMarks p m U j x = true ↔ SiteMark p m U j (x : ℤ) from by
      classical
      simp only [SwarmLogRatio.siteMarks]
      exact decide_eq_true_iff]
    exact (markB_eq_true).mp h

/-- The integer/natural conversion of a nonnegative record: `M.toNat + k` is the site `M + k`. -/
lemma natCast_toNat_add {M : ℤ} (hM : 0 ≤ M) (k : ℕ) :
    (((M.toNat + k : ℕ) : ℤ)) = M + (k : ℤ) := by
  have h : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM
  push_cast [h]
  ring

/-- **The mark alignment.**  The `k`-th mark above the running record used by `RecExp.markSeq` is
the actual site mark at the site `M_n^j + k`, indexed by the natural number `M_n^j.toNat + k`. -/
lemma markSeq_eq_siteMarks {p : ℝ} (m n : ℕ) (j : Fin N) (U : Array N) (k : ℕ) :
    markSeq p m n j U k
      = SwarmLogRatio.siteMarks p m U j ((recVal j (prefOf p m n U)).toNat + k) := by
  rw [markSeq, siteMarks_eq_markB_ofNat, natCast_toNat_add (zero_le_recVal_prefOf p m U j n)]

/-! ### 2. The exact shifted identification -/

/-- **The full-history seed at the running record**: `H0 = h_j(M_n^j)`, as a function of the
actual array and the actual site-mark sequence. -/
noncomputable def H0 (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) : ℝ :=
  SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (recVal j (prefOf p m n U)).toNat

lemma H0_def {p : ℝ} (m n : ℕ) (j : Fin N) (U : Array N) :
    H0 p m n j U =
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (recVal j (prefOf p m n U)).toNat := rfl

/-- **Exact shifted identification.**  The potential `RecSeed.shiftG` started at the full-history
seed `h_j(M)` and driven by the marks above the record is the actual `h_j(M+g)`; no conditional
expectation is involved. -/
theorem shiftG_H0 {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    shiftG (H0 p m n j) p m n j g U
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g) := by
  induction g with
  | zero => rfl
  | succ k ih =>
      have hidx : (recVal j (prefOf p m n U)).toNat + (k + 1)
          = ((recVal j (prefOf p m n U)).toNat + k) + 1 := by omega
      show 1 + rhoStep p m n j (k + 1) U
          * (1 + shiftG (H0 p m n j) p m n j k U)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + (k + 1))
      rw [hidx, SwarmMarks.hof_succ, ← ih]
      rw [rhoStep, markSeq_eq_siteMarks, hidx, SwarmMarks.hstep_eq_rho hp0]

/-! ### 3. The record never exceeds the time, hence the deterministic seed bound -/

/-- Every walker is at distance at most `t` after `t` steps, in particular at most `t` to the
right; only the right-hand bound is needed for the running record. -/
lemma pos_le_time (p : ℝ) (m : ℕ) (U : Array N) (t : ℕ) (i : Fin N) :
    (trajectory p m U t).pos i ≤ (t : ℤ) := by
  induction t with
  | zero => simp
  | succ k ih =>
      rw [trajectory_succ, nextWalkState_pos, nextPos]
      have hd : Swarming.drivenStep
          (U (i, (trajectory p m U k).pos i,
            (trajectory p m U k).ell i ((trajectory p m U k).pos i)))
          (rightProbability p m (trajectory p m U k).ell i ((trajectory p m U k).pos i)) ≤ 1 := by
        unfold Swarming.drivenStep
        split <;> omega
      push_cast
      linarith

/-- The running record is at most the current time. -/
lemma runMax_le_time (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n ≤ (n : ℤ) := by
  obtain ⟨t, ht, heq⟩ := exists_eq_runMax p m U j n
  rw [← heq]
  exact le_trans (pos_le_time p m U t j) (by exact_mod_cast ht)

/-- The record read off the prefix is at most `n`. -/
lemma recVal_prefOf_le_time (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    recVal j (prefOf p m n U) ≤ (n : ℤ) := by
  rw [← runMax_eq_recVal]
  exact runMax_le_time p m U j n

/-- The natural-number record is at most `n`. -/
lemma toNat_recVal_prefOf_le (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    (recVal j (prefOf p m n U)).toNat ≤ n := by
  have h := recVal_prefOf_le_time p m U j n
  have h' := Int.toNat_le_toNat h
  simpa using h'

/-- **The deterministic bound on the full-history seed**: `|h_j(M_n^j)| ≤ 2 n + 3`, from the
one-site bound `|hof … k| ≤ 2k + 3` at `k = M_n^j` and `M_n^j ≤ n`. -/
lemma abs_H0_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N) (U : Array N) : |H0 p m n j U| ≤ 2 * (n : ℝ) + 3 := by
  have h := SwarmShiftMarks.abs_hof_le' hp1 hp2 hp0 (SwarmLogRatio.siteMarks p m U j)
    (recVal j (prefOf p m n U)).toNat
  have hk : ((recVal j (prefOf p m n U)).toNat : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast toNat_recVal_prefOf_le p m U j n
  simp only [H0]
  linarith

/-! ### 4. The RecSeed hypotheses and the projected recursion for the actual seed -/

/-- Measurability for `enlRecMeas` implies ambient measurability, hence integrability from the
deterministic bound. -/
lemma integrable_H0 {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j)) :
    Integrable (H0 p m n j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hamb : Measurable (H0 p m n j) := fun s hs => enlRecMeas_le p m n j _ (hh0 hs)
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 3)) hamb.aestronglyMeasurable ?_
  · filter_upwards with U
    rw [Real.norm_eq_abs]
    exact abs_H0_le hp1 hp2 hp0 m n j U

/-- **All `RecSeed` hypotheses for the actual full-history seed.**  The only input is
`enlRecMeas`-measurability of `H0`; the deterministic bound and integrability are supplied here.
This is the precise shape of the remaining link to direction A. -/
theorem recSeed_hypotheses {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j)) :
    Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j) ∧
      Integrable (H0 p m n j) (arrayMeasure N) ∧
      ∀ U, |H0 p m n j U| ≤ 2 * (n : ℝ) + 3 :=
  ⟨hh0, integrable_H0 hp1 hp2 hp0 m n j hh0, abs_H0_le hp1 hp2 hp0 m n j⟩

/-- **The projected recursion for the actual full-history potential.**
`E[h_j(M_n^j + g) | enlRecMeas]` is the `g`-fold affine iteration started at the random seed
`h_j(M_n^j)`.  This is `RecSeed.condExp_shiftG` instantiated at the actual `hof`, with the shifted
identification `shiftG_H0` used to rewrite the left-hand side. -/
theorem condExp_H0 {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j)) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g))
      =ᵐ[arrayMeasure N] fun U => phiIter (aRec p m) g (H0 p m n j U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hint : Integrable (H0 p m n j) (arrayMeasure N) :=
    integrable_H0 hp1 hp2 hp0 m n j hh0
  have hmain := condExp_shiftG (p := p) hp0 hp1 hp2 m j
    (h0 := H0 p m n j) (c := 2 * (n : ℝ) + 3) (abs_H0_le hp1 hp2 hp0 m n j) hh0 hint g
  rwa [show shiftG (H0 p m n j) p m n j g
      = fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + g)
      from funext (shiftG_H0 hp0 m n j g)] at hmain

/-- **The paper's display `e_{g+1} = 1 + a (1 + e_g)` for the actual full-history potential.**
This is the recursion `(projh)` at the random record, with the seed carried along: no iteration of
a deterministic constant is assumed. -/
theorem condExp_H0_succ {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {n : ℕ} (j : Fin N)
    (hh0 : Measurable[enlRecMeas (N := N) p m n j] (H0 p m n j)) (g : ℕ) :
    condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
        (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + (g + 1)))
      =ᵐ[arrayMeasure N] fun U => 1 + aRec p m *
        (1 + condExp (enlRecMeas (N := N) p m n j) (arrayMeasure N)
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + g)) U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h1 := condExp_H0 hp0 hp1 hp2 m j hh0 (g + 1)
  have h2 := condExp_H0 hp0 hp1 hp2 m j hh0 g
  filter_upwards [h1, h2] with U h1U h2U
  rw [h1U, h2U, phiIter_succ]

end Swarming.Enl


