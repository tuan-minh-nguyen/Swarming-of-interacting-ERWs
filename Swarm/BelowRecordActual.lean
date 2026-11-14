/-
  **Direction D'' (m4): the below-record side of the actual one-step `Hpot` ledger.**

  This file connects the *actual* one-step potential increment

      `Hpot h_j(X_{n+1}^i) - Hpot h_j(X_n^i)`,     `h_j = envH p m j`,

  to the existing regional lower bounds on the region that is **strictly below** the running
  record of walker `j`,

      `B = belowRecSet p m n i j = {U | (trajectory p m U n).pos i < runMax p m U j n}`
        `= {U | (trajectory p m U n).pos i < recVal j (prefOf p m n U)}`,

  i.e. the complement of the whole above-record chain `⋃ g, abovePosSet p m n i j g`
  (`compl_belowRecSet`).

  Contents, in order:

  * `measurableSet_belowRecSet` and the finite cover `belowRecSet_eq_iUnion_singletons`
    (`B` is a finite union of the pieces on which the random site `X_n^i` is fixed);
  * `belowRec_step_up_piecewise` / `belowRec_step_down_piecewise` — the pointwise
    piecewise-constant form of the two potential steps restricted to `B`, and their
    `enlFilt`-measurability (`measurable_belowRec_indicator_hZpot_at`,
    `measurable_belowRec_indicator_hZpot_pred`), which is exactly the hypothesis of
    `PullOut.condExp_drift_of_adapted` that fails *at* and *above* the record;
  * `condExp_drift_belowRec` — the exact restricted conditional mean on `B` at `enlFilt`;
  * `belowRec_bracket_nonneg` — the deterministic bracket is `>= 0` on `B`
    (`2 alpha - 1 >= 0` below zero, `>= 1` in the interior, both from the existing
    `InteriorBound` inputs);
  * `belowRec_drift_ge_zero` and `belowRec_drift_ge_neg_bRec` — the region bound
    `0 <= E[1_B increment | enlFilt]`, resp. `1_B (-bRec) <= E[1_B increment | enlFilt]`;
  * `integrable_belowRec_increment` — integrability of the restricted increment;
  * `compl_belowRecSet` / `iUnion_abovePosSet_eq_compl` — the pointwise partition
    `Omega = B ⊔ ⋃_{g <= n} abovePosSet g` that the global assembly consumes.

  Nothing here treats the record (`g = 0`) or above-record (`g >= 1`) offsets: `B` is the
  disjoint complement of `⋃ g, abovePosSet p m n i j g`.  No tower, no `Q`, no occupation.
-/
import Swarm.InteriorBound
import Swarm.AboveRecIncrement
import Swarm.BelowRecord

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmCross

variable {N : ℕ}

/-! ### The strictly-below-record region -/

/-- The region on which walker `i` is **strictly below** the running record of walker `j`
at time `n`.  This is the complement of `⋃ g, abovePosSet p m n i j g`. -/
def belowRecSet (p : ℝ) (m n : ℕ) (i j : Fin N) : Set (Array N) :=
  {U : Array N | (trajectory p m U n).pos i < runMax p m U j n}

/-- The same region, written with the prefix record `recVal` of the record environment. -/
theorem belowRecSet_eq_recVal (p : ℝ) (m n : ℕ) (i j : Fin N) :
    belowRecSet p m n i j
      = {U : Array N | (trajectory p m U n).pos i < recVal j (prefOf p m n U)} := by
  ext U
  simp only [belowRecSet, Set.mem_ofPred_eq, runMax_eq_recVal]

/-- The deterministic positive part of the offset is bounded by the time horizon. -/
lemma offset_le_of_bounds (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N)
    (h0 : (0 : ℤ) ≤ (trajectory p m U n).pos i) :
    ((trajectory p m U n).pos i).toNat ≤ n := by
  have hpos := (pos_bounds (p := p) (m := m) U n i).2
  have hcast : (((trajectory p m U n).pos i).toNat : ℤ) = (trajectory p m U n).pos i :=
    Int.toNat_of_nonneg ‹(0 : ℤ) ≤ _›
  have hn : (((trajectory p m U n).pos i).toNat : ℤ) ≤ (n : ℤ) := by rw [hcast]; exact hpos
  exact_mod_cast hn

/-- The below-record region as the finite union of the pieces with a fixed position. -/
theorem belowRecSet_eq_iUnion_singletons (p : ℝ) (m n : ℕ) (i j : Fin N) :
    belowRecSet p m n i j
      = ({U : Array N | (trajectory p m U n).pos i < 0}
          ∪ ⋃ k ∈ Finset.range (n + 1),
            ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
              ∩ {U : Array N | (k : ℤ) < runMax p m U j n})) := by
  ext U
  simp only [belowRecSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Finset.mem_range,
    Set.mem_inter_iff]
  constructor
  · intro h
    by_cases hneg : (trajectory p m U n).pos i < 0
    · exact Or.inl hneg
    · have hnonneg : (0 : ℤ) ≤ (trajectory p m U n).pos i := not_lt.mp hneg
      have hk : ((trajectory p m U n).pos i).toNat ≤ n := offset_le_of_bounds p m U n i hnonneg
      refine Or.inr ⟨((trajectory p m U n).pos i).toNat, Nat.lt_succ_of_le hk, ?_, ?_⟩
      · exact (Int.toNat_of_nonneg hnonneg).symm
      · rw [Int.toNat_of_nonneg hnonneg]; exact h
  · rintro (hneg | ⟨k, -, hx, hk⟩)
    · exact lt_of_lt_of_le hneg (zero_le_runMax p m U j n)
    · rw [hx]; exact hk

/-- The strictly-below-record region is `enlFilt`-measurable. -/
theorem measurableSet_belowRecSet (p : ℝ) (m n : ℕ) (i j : Fin N) :
    MeasurableSet[enlFilt p m n] (belowRecSet p m n i j) := by
  classical
  rw [belowRecSet_eq_iUnion_singletons]
  refine MeasurableSet.union ?_ (Finset.measurableSet_biUnion _ fun k _ => ?_)
  · exact enl_pos_measurable p m n le_rfl i
      (measurableSet_lt measurable_id measurable_const)
  · exact (enl_pos_measurable p m n le_rfl i (measurableSet_singleton (k : ℤ))).inter
      (measurableSet_lt_runMax p m n j k)


/-! ### The two potential steps, restricted to the below-record region -/

/-- **Forward step, piecewise.**  On the below-record region the forward potential step is the
boundary value `1` at negative positions and the fixed-site value `h_j(k)` at position `k`. -/
theorem belowRec_indicator_hZpot_at_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (fun U => (belowRecSet p m n i j).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U)
      = fun U =>
          ({U : Array N | (trajectory p m U n).pos i < 0}).indicator (fun _ => (1 : ℝ)) U
          + ∑ k ∈ Finset.range (n + 1),
              ((belowRecSet p m n i j)
                ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
                (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) U := by
  funext U
  by_cases hU : U ∈ belowRecSet p m n i j
  · by_cases hneg : (trajectory p m U n).pos i < 0
    · have hsum : (∑ k ∈ Finset.range (n + 1),
          ((belowRecSet p m n i j)
            ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
            (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) U) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Set.indicator_of_notMem]
        rintro ⟨-, hx⟩
        have hx' : (trajectory p m U n).pos i = (k : ℤ) := hx
        omega
      rw [Set.indicator_of_mem hU, hZpot_of_nonpos (by omega), hsum,
        Set.indicator_of_mem (show U ∈ {U : Array N | (trajectory p m U n).pos i < 0} from hneg)]
      ring
    · have hx0 : (0 : ℤ) ≤ (trajectory p m U n).pos i := not_lt.mp hneg
      have hk : ((trajectory p m U n).pos i).toNat ≤ n := offset_le_of_bounds p m U n i hx0
      have hval : hZpot (envH p m j U) ((trajectory p m U n).pos i)
          = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((trajectory p m U n).pos i).toNat := by
        rw [hZpot_of_nonneg hx0]; rfl
      have hmemA : U ∈ ((belowRecSet p m n i j)
          ∩ {V : Array N | (trajectory p m V n).pos i
              = (((trajectory p m U n).pos i).toNat : ℤ)}) :=
        ⟨hU, (Int.toNat_of_nonneg hx0).symm⟩
      have hsingle := Finset.sum_eq_single (f := fun (k : ℕ) => ((belowRecSet p m n i j)
            ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
            (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) U)
          ((trajectory p m U n).pos i).toNat
          (fun b _ hb => by
            rw [Set.indicator_of_notMem]
            rintro ⟨-, hx⟩
            exact hb (by rw [show (trajectory p m U n).pos i = (b : ℤ) from hx,
              Int.toNat_natCast]))
          (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hmem)
      rw [Set.indicator_of_mem hU, hval, hsingle.trans (Set.indicator_of_mem hmemA _),
        Set.indicator_of_notMem (show U ∉ {U : Array N | (trajectory p m U n).pos i < 0}
          from hneg)]
      ring
  · have hsum : (∑ k ∈ Finset.range (n + 1),
        ((belowRecSet p m n i j)
          ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) U) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Set.indicator_of_notMem]
      exact fun hh => hU hh.1
    have hnotneg : U ∉ {U : Array N | (trajectory p m U n).pos i < 0} := by
      intro hh
      exact hU (lt_of_lt_of_le hh (zero_le_runMax p m U j n))
    rw [Set.indicator_of_notMem hU, hsum, Set.indicator_of_notMem hnotneg]
    ring

/-- **Backward step, piecewise.**  Same decomposition for the backward potential step. -/
theorem belowRec_indicator_hZpot_pred_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (fun U => (belowRecSet p m n i j).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U)
      = fun U =>
          ({U : Array N | (trajectory p m U n).pos i < 0}).indicator (fun _ => (1 : ℝ)) U
          + ∑ k ∈ Finset.range (n + 1),
              ((belowRecSet p m n i j)
                ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
                (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U := by
  funext U
  by_cases hU : U ∈ belowRecSet p m n i j
  · by_cases hneg : (trajectory p m U n).pos i < 0
    · have hsum : (∑ k ∈ Finset.range (n + 1),
          ((belowRecSet p m n i j)
            ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
            (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Set.indicator_of_notMem]
        rintro ⟨-, hx⟩
        have hx' : (trajectory p m U n).pos i = (k : ℤ) := hx
        omega
      rw [Set.indicator_of_mem hU, hZpot_of_nonpos (by omega), hsum,
        Set.indicator_of_mem (show U ∈ {U : Array N | (trajectory p m U n).pos i < 0} from hneg)]
      ring
    · have hx0 : (0 : ℤ) ≤ (trajectory p m U n).pos i := not_lt.mp hneg
      have hk : ((trajectory p m U n).pos i).toNat ≤ n := offset_le_of_bounds p m U n i hx0
      have hmemA : U ∈ ((belowRecSet p m n i j)
          ∩ {V : Array N | (trajectory p m V n).pos i
              = (((trajectory p m U n).pos i).toNat : ℤ)}) :=
        ⟨hU, (Int.toNat_of_nonneg hx0).symm⟩
      have hsingle := Finset.sum_eq_single (f := fun (k : ℕ) => ((belowRecSet p m n i j)
            ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
            (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U)
          ((trajectory p m U n).pos i).toNat
          (fun b _ hb => by
            rw [Set.indicator_of_notMem]
            rintro ⟨-, hx⟩
            exact hb (by rw [show (trajectory p m U n).pos i = (b : ℤ) from hx,
              Int.toNat_natCast]))
          (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hmem)
      rw [Set.indicator_of_mem hU, hsingle.trans (Set.indicator_of_mem hmemA _),
        Int.toNat_of_nonneg hx0,
        Set.indicator_of_notMem (show U ∉ {U : Array N | (trajectory p m U n).pos i < 0}
          from hneg)]
      ring
  · have hsum : (∑ k ∈ Finset.range (n + 1),
        ((belowRecSet p m n i j)
          ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}).indicator
          (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Set.indicator_of_notMem]
      exact fun hh => hU hh.1
    have hnotneg : U ∉ {U : Array N | (trajectory p m U n).pos i < 0} := by
      intro hh
      exact hU (lt_of_lt_of_le hh (zero_le_runMax p m U j n))
    rw [Set.indicator_of_notMem hU, hsum, Set.indicator_of_notMem hnotneg]
    ring


/-! ### Measurability of the restricted steps -/

/-- **The forward step restricted to the below-record region is `enlFilt`-measurable.** -/
theorem measurable_belowRec_indicator_hZpot_at (p : ℝ) (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ)
    (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U => (belowRecSet p m n i j).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  rw [belowRec_indicator_hZpot_at_eq]
  refine Measurable.add
    (Measurable.indicator measurable_const
      (enl_pos_measurable p m n le_rfl i (measurableSet_lt measurable_id measurable_const)))
    (Finset.measurable_sum _ fun k _ => ?_)
  have hA : MeasurableSet[enlFilt p m n]
      ((belowRecSet p m n i j)
        ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}) :=
    (measurableSet_belowRecSet p m n i j).inter
      (enl_pos_measurable p m n le_rfl i (measurableSet_singleton (k : ℤ)))
  refine measurable_indicator_hof_of_below (p := p) hp m n j k hA ?_
  intro U hU
  have hlt : (trajectory p m U n).pos i < runMax p m U j n := hU.1
  rwa [hU.2] at hlt

/-- **The backward step restricted to the below-record region is `enlFilt`-measurable.** -/
theorem measurable_belowRec_indicator_hZpot_pred (p : ℝ) (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ)
    (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U => (belowRecSet p m n i j).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U) := by
  rw [belowRec_indicator_hZpot_pred_eq]
  refine Measurable.add
    (Measurable.indicator measurable_const
      (enl_pos_measurable p m n le_rfl i (measurableSet_lt measurable_id measurable_const)))
    (Finset.measurable_sum _ fun k _ => ?_)
  have hA : MeasurableSet[enlFilt p m n]
      ((belowRecSet p m n i j)
        ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}) :=
    (measurableSet_belowRecSet p m n i j).inter
      (enl_pos_measurable p m n le_rfl i (measurableSet_singleton (k : ℤ)))
  have hAM : ∀ U, U ∈ ((belowRecSet p m n i j)
      ∩ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}) →
      (trajectory p m U n).pos i < runMax p m U j n := fun U hU => hU.1
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hfun : (fun U : Array N => hZpot (envH p m j U) (((0 : ℕ) : ℤ) - 1))
        = fun _ => (1 : ℝ) := by
      funext U
      exact hZpot_of_nonpos (by norm_num)
    rw [hfun]
    exact Measurable.indicator measurable_const hA
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hfun : (fun U : Array N => hZpot (envH p m j U) (((k' + 1 : ℕ) : ℤ) - 1))
        = fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k' := by
      funext U
      have hcast : (((k' + 1 : ℕ)) : ℤ) - 1 = (k' : ℤ) := by push_cast; ring
      rw [hcast, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k'), Int.toNat_natCast]
      rfl
    rw [hfun]
    refine measurable_indicator_hof_of_below (p := p) hp m n j k' hA ?_
    intro U hU
    have hlt : (((k' + 1 : ℕ)) : ℤ) < runMax p m U j n := by
      have h := hAM U hU
      rwa [hU.2] at h
    have hstep : (k' : ℤ) < (((k' + 1 : ℕ)) : ℤ) := by push_cast; omega
    exact lt_trans hstep hlt

/-! ### The deterministic bound on the potential steps -/

/-- Every potential step at a site at most `n` is bounded by `2 n + 3` (and the boundary value
`1` is below it). -/
lemma belowRec_abs_hZpot_envH_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ} (j : Fin N)
    (U : Array N) {x : ℤ} (hx : x ≤ (n : ℤ)) :
    |hZpot (envH p m j U) x| ≤ 2 * (n : ℝ) + 3 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hneg : x ≤ -1
  · rw [hZpot_of_nonpos hneg, abs_one]
    linarith
  · have hx0 : (0 : ℤ) ≤ x := by omega
    rw [hZpot_of_nonneg hx0]
    have hxn : x.toNat ≤ n := by
      have hcast : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0
      omega
    have henv : envH p m j U x.toNat
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x.toNat := rfl
    rw [henv]
    have hb := SwarmShiftMarks.abs_hof_le' hp1 hp2 (by linarith : p ≠ 0)
      (SwarmLogRatio.siteMarks p m U j) x.toNat
    have hcast : ((x.toNat : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxn
    linarith

/-- Norm bound for the restricted forward step. -/
theorem norm_belowRec_indicator_hZpot_at_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (i j : Fin N) (U : Array N) :
    ‖(belowRecSet p m n i j).indicator
      (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U‖ ≤ 2 * (n : ℝ) + 3 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hU : U ∈ belowRecSet p m n i j
  · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
    exact belowRec_abs_hZpot_envH_le hp1 hp2 j U (pos_bounds (p := p) (m := m) U n i).2
  · rw [Set.indicator_of_notMem hU]
    simp only [norm_zero]
    linarith

/-- Norm bound for the restricted backward step. -/
theorem norm_belowRec_indicator_hZpot_pred_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (i j : Fin N) (U : Array N) :
    ‖(belowRecSet p m n i j).indicator
      (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U‖ ≤ 2 * (n : ℝ) + 3 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hU : U ∈ belowRecSet p m n i j
  · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
    refine belowRec_abs_hZpot_envH_le hp1 hp2 j U ?_
    have := (pos_bounds (p := p) (m := m) U n i).2
    omega
  · rw [Set.indicator_of_notMem hU]
    simp only [norm_zero]
    linarith

/-! ### The exact one-step conditional mean on the below-record region -/

/-- **The actual one-step `Hpot` drift on the strictly-below-record region.**  On
`B = belowRecSet p m n i j` the conditional mean of the actual potential increment is the
paper's bracket, with the *actual* site-mark environment `h_j`:

    `E[1_B (H_pot(X_{n+1}^i) - H_pot(X_n^i)) | enlFilt p m n]`
      `=ᵐ 1_B (alpha_n^i h_j(X_n^i) - (1 - alpha_n^i) h^w_j(X_n^i - 1))`.

  Below the record both `h_j(X_n^i)` and `h^w_j(X_n^i - 1)` are `enlFilt`-measurable (that is what
  the two measurability inputs above supply, and what fails *at* and *above* the record), so this
  is an instance of `PullOut.condExp_drift_of_adapted` — no tower, no above-record input. -/
theorem condExp_drift_belowRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => (belowRecSet p m n i j).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U)
      =ᵐ[arrayMeasure N] fun U => (belowRecSet p m n i j).indicator
        (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
          - (1 - alphaFun p m n i U)
            * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U :=
  condExp_drift_of_adapted hp1 hp2 (envH p m j) i (measurableSet_belowRecSet p m n i j)
    (measurable_belowRec_indicator_hZpot_at p hp1.le m n i j)
    (measurable_belowRec_indicator_hZpot_pred p hp1.le m n i j)
    (2 * (n : ℝ) + 3) (by positivity)
    (norm_belowRec_indicator_hZpot_at_le hp1 hp2 i j)
    (norm_belowRec_indicator_hZpot_pred_le hp1 hp2 i j)


/-! ### The bracket is nonnegative below the record -/

/-- **The deterministic bracket is nonnegative strictly below the record.**  Below zero both
potential steps equal the boundary value `1`, so the bracket is `2 alpha - 1 >= 0`; at a natural
site `0 <= k < M_n^j` it is at least `1` by the existing interior input
`InteriorBound.interior_bracket_ge_one`. -/
theorem belowRec_bracket_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) {U : Array N} (hU : U ∈ belowRecSet p m n i j) :
    0 ≤ alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
      - (1 - alphaFun p m n i U)
        * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1) := by
  by_cases hneg : (trajectory p m U n).pos i < 0
  · have h1 : hZpot (envH p m j U) ((trajectory p m U n).pos i) = 1 :=
      hZpot_of_nonpos (by omega)
    have h2 : hZpot (envH p m j U) ((trajectory p m U n).pos i - 1) = 1 :=
      hZpot_of_nonpos (by omega)
    have hα : (1 : ℝ) / 2 ≤ alphaFun p m n i U := one_half_le_alphaFun hp1 hp2 m n i U
    rw [h1, h2]
    nlinarith
  · have hx0 : (0 : ℤ) ≤ (trajectory p m U n).pos i := not_lt.mp hneg
    have hx : (trajectory p m U n).pos i = (((trajectory p m U n).pos i).toNat : ℤ) :=
      (Int.toNat_of_nonneg hx0).symm
    have hlt : (trajectory p m U n).pos i < runMax p m U j n := hU
    have hkM : (((trajectory p m U n).pos i).toNat : ℤ) < runMax p m U j n := by
      rw [← hx]; exact hlt
    have hb := interior_bracket_ge_one hp1 hp2 hij hx hkM
    have hz : hZpot (envH p m j U) ((trajectory p m U n).pos i)
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((trajectory p m U n).pos i).toNat := by
      rw [hZpot_of_nonneg hx0]; rfl
    have harg : (trajectory p m U n).pos i - 1
        = (((trajectory p m U n).pos i).toNat : ℤ) - 1 := by omega
    rw [hz, harg]
    linarith

/-- **The below-record drift is nonnegative** in the `enlFilt` conditional mean. -/
theorem belowRec_drift_ge_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    (fun _ => (0 : ℝ)) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => (belowRecSet p m n i j).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  have hle : (fun _ : Array N => (0 : ℝ)) ≤ᵐ[arrayMeasure N]
      fun U => (belowRecSet p m n i j).indicator
        (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
          - (1 - alphaFun p m n i U)
            * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U := by
    refine Filter.Eventually.of_forall fun U => ?_
    dsimp only
    by_cases hU : U ∈ belowRecSet p m n i j
    · rw [Set.indicator_of_mem hU]
      exact belowRec_bracket_nonneg hp1 hp2 hij hU
    · rw [Set.indicator_of_notMem hU]
  exact hle.trans_eq (condExp_drift_belowRec (p := p) hp1 hp2 (m := m) (n := n) i j).symm

/-- **The below-record regional lower bound**, in the shape the global assembly consumes:
the restricted conditional mean is at least `-b_n` on the whole below-record region. -/
theorem belowRec_drift_ge_neg_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    (fun U => (belowRecSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N]
        condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => (belowRecSet p m n i j).indicator
            (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
              - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  have hle : (fun U => (belowRecSet p m n i j).indicator
        (fun U => -(bRec p m n j U)) U) ≤ᵐ[arrayMeasure N]
      fun U => (belowRecSet p m n i j).indicator
        (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
          - (1 - alphaFun p m n i U)
            * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U := by
    refine Filter.Eventually.of_forall fun U => ?_
    dsimp only
    by_cases hU : U ∈ belowRecSet p m n i j
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
      have h3 : (3 : ℝ) ≤ bRec p m n j U := three_le_bRec hp1 hp2 m n j U
      have hnn := belowRec_bracket_nonneg hp1 hp2 hij hU
      linarith
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  exact hle.trans_eq (condExp_drift_belowRec (p := p) hp1 hp2 (m := m) (n := n) i j).symm

/-- **Integrability of the restricted increment** below the record. -/
theorem integrable_belowRec_increment {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    (i j : Fin N) :
    Integrable (fun U => (belowRecSet p m n i j).indicator
      (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
        - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) (arrayMeasure N) := by
  rw [indicator_Hpot_sub_eq (envH p m j) i (A := belowRecSet p m n i j)]
  refine Integrable.sub
    (integrable_stepUpInd_mul (measurable_belowRec_indicator_hZpot_at p hp1.le m n i j)
      (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 3)
      (norm_belowRec_indicator_hZpot_at_le hp1 hp2 i j))
    (integrable_stepDownInd_mul (measurable_belowRec_indicator_hZpot_pred p hp1.le m n i j)
      (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 3)
      (norm_belowRec_indicator_hZpot_pred_le hp1 hp2 i j))


/-! ### The partition of the array space into below-record and above-record offsets -/

/-- The above-record offsets, written with the actual trajectory position. -/
theorem abovePosSet_eq_pos (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    abovePosSet p m n i j g
      = {U : Array N | (trajectory p m U n).pos i
          = recVal j (prefOf p m n U) + (g : ℤ)} := by
  ext U
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  simp only [abovePosSet, Set.mem_ofPred_eq, hpos]

/-- **The strictly-below-record region is the complement of the whole above-record chain.** -/
theorem compl_belowRecSet (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (belowRecSet p m n i j)ᶜ = ⋃ g : ℕ, abovePosSet p m n i j g := by
  ext U
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  simp only [belowRecSet, abovePosSet, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
    runMax_eq_recVal, hpos]
  constructor
  · intro h
    have hcast : (((trajectory p m U n).pos i - recVal j (prefOf p m n U)).toNat : ℤ)
        = (trajectory p m U n).pos i - recVal j (prefOf p m n U) :=
      Int.toNat_of_nonneg (by omega)
    refine ⟨((trajectory p m U n).pos i - recVal j (prefOf p m n U)).toNat, ?_⟩
    rw [hcast]
    ring
  · rintro ⟨g, hg⟩
    omega

/-- **Finite form of the complement**: only the offsets `g <= n` can occur. -/
theorem compl_belowRecSet_finite (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (belowRecSet p m n i j)ᶜ
      = ⋃ g ∈ Finset.range (n + 1), abovePosSet p m n i j g := by
  rw [compl_belowRecSet]
  ext U
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  simp only [abovePosSet, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, hpos]
  constructor
  · rintro ⟨g, hg⟩
    have hM0 : (0 : ℤ) ≤ recVal j (prefOf p m n U) := zero_le_recVal_prefOf p m U j n
    have h2 := (pos_bounds (p := p) (m := m) U n i).2
    exact ⟨g, by omega, hg⟩
  · rintro ⟨g, -, hg⟩
    exact ⟨g, hg⟩

/-- The below-record region is disjoint from every above-record offset. -/
theorem disjoint_belowRec_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) (g : ℕ) :
    Disjoint (belowRecSet p m n i j) (abovePosSet p m n i j g) := by
  rw [Set.disjoint_left]
  intro U h1 h2
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  simp only [belowRecSet, abovePosSet, Set.mem_ofPred_eq, runMax_eq_recVal, hpos] at h1 h2
  omega

/-- Distinct above-record offsets are disjoint. -/
theorem disjoint_abovePosSet (p : ℝ) (m n : ℕ) (i j : Fin N) {g g' : ℕ} (h : g ≠ g') :
    Disjoint (abovePosSet p m n i j g) (abovePosSet p m n i j g') := by
  rw [Set.disjoint_left]
  intro U h1 h2
  have hpos : ext (prefOf p m n U) n i = (trajectory p m U n).pos i := ext_prefOf U le_rfl i
  simp only [abovePosSet, Set.mem_ofPred_eq, hpos] at h1 h2
  have : (g : ℤ) = (g' : ℤ) := by omega
  exact h (by exact_mod_cast this)

/-- **The array space is the below-record region together with the finitely many above-record
offsets** — the partition the global one-step assembly consumes. -/
theorem univ_eq_belowRec_union_above (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (Set.univ : Set (Array N))
      = belowRecSet p m n i j
        ∪ ⋃ g ∈ Finset.range (n + 1), abovePosSet p m n i j g := by
  rw [← compl_belowRecSet_finite]
  exact (Set.union_compl_self _).symm


/-! ### Record-language form of the regional bound -/

/-- **The below-record regional bound in the record language**: with
`B = {U | (trajectory p m U n).pos i < recVal j (prefOf p m n U)}`, the actual restricted
one-step conditional mean is at least `-b_n` on `B`. -/
theorem recVal_belowRec_drift_ge_neg_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (fun U => ({U : Array N | (trajectory p m U n).pos i < recVal j (prefOf p m n U)}).indicator
        (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N]
        condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => ({U : Array N | (trajectory p m U n).pos i
                < recVal j (prefOf p m n U)}).indicator
            (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
              - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  have hset := belowRecSet_eq_recVal p m n i j
  have h := belowRec_drift_ge_neg_bRec (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j) hij
  rwa [hset] at h

/-! ### Axiom audit -/


end Swarming.Enl
