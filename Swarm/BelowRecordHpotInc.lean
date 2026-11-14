/-
  **Direction C (m3) — audited below-record ledger in the common `HpotInc` object.**

  This companion file adds the API the global one-step assembly (`Direction F`) and its
  integral form (`Direction G`) actually consume, without proving any new probability:

  * `belowRec_HpotInc_eq` — `HpotInc p m n i j` (the *common* increment introduced by the
    integrated `RecordTower.lean`) is **definitionally** the m4 integrand.  This is the
    normalisation that makes the below-record half and the at/above-record halves
    (`RecordTower`, `AboveActualDrift`) speak about one object;
  * `condExp_HpotInc_belowRec`, `HpotInc_belowRec_ge_zero`,
    `HpotInc_belowRec_ge_neg_bRec`, `integrable_HpotInc_belowRec` — the exact
    `enlFilt p m n` conditional mean, its bracket sign form and its ledger form
    `1_B (-bRec)`, and integrability, all at `HpotInc`;
  * `measurableSet_belowRecSet_ambient`, `integrable_belowRec_neg_bRec` — the two analytic
    side conditions of the *unconditonal* (mass) form that the m4 artifact does not supply
    (it only states the a.e. inequality);
  * `setIntegral_belowRec_HpotInc_ge` — the set-integral form
    `∫_B (-bRec) ≤ ∫_B HpotInc`, mirroring `RecordTower.setIntegral_le_setIntegral_HpotInc_zero`;
  * `indicator_partition_belowRec_above` — for an **arbitrary** `f`,
    `f = 1_B · f + Σ_{g<n+1} 1_{A_g} · f`, proved from the m4 disjointness/finite-cover
    lemmas; its two instances `HpotInc_eq_belowRec_add_sum` and
    `one_eq_indicator_belowRec_add_sum` are the pointwise partition the finite
    `condExp`-additive assembly needs.

  Everything here is a restatement/assembly of the audited below-record facts at `enlFilt`;
  no at-record or above-record tower step, no `shiftG`, no `eRec`, no `Q`, no occupation.
-/
import Swarm.BelowRecordActual
import Swarm.RecordTower

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory Swarming.StepCross SwarmCross

variable {N : ℕ}

/-! ### Normalisation to the common increment -/

/-- `RecordTower.HpotInc` is, definitionally, the integrand of the m4 below-record statements.
This is the only bridge needed: `HpotInc` unfolds to `Hpot h_j (X_{n+1}^i) - Hpot h_j (X_n^i)`
with the actual full-history environment `h_j = envH p m j`. -/
theorem belowRec_HpotInc_eq (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j
      = fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
          - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i) := rfl

/-! ### The audited below-record statements at `HpotInc` -/

/-- **Exact one-step `enlFilt` conditional mean below the record**, at the common increment.
On `B = belowRecSet p m n i j` the conditional mean of `HpotInc` is the paper's bracket with
the actual site-mark environment.  (Restatement of the audited `condExp_drift_belowRec`.) -/
theorem condExp_HpotInc_belowRec (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        ((belowRecSet p m n i j).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (belowRecSet p m n i j).indicator
        (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
          - (1 - alphaFun p m n i U)
            * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) := by
  rw [belowRec_HpotInc_eq]
  exact condExp_drift_belowRec (p := p) hp1 hp2 (m := m) (n := n) i j

/-- **The below-record drift is nonnegative**, at the common increment. -/
theorem HpotInc_belowRec_ge_zero (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    (fun _ => (0 : ℝ)) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N)
        ((belowRecSet p m n i j).indicator (HpotInc p m n i j)) := by
  rw [belowRec_HpotInc_eq]
  exact belowRec_drift_ge_zero (p := p) hp1 hp2 (m := m) (n := n) hij

/-- **The below-record regional lower bound** `1_B (-b_n)` at the common increment: the shape
the global one-step ledger sums.  (Restatement of the audited `belowRec_drift_ge_neg_bRec`.) -/
theorem HpotInc_belowRec_ge_neg_bRec (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    (fun U => (belowRecSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowRecSet p m n i j).indicator (HpotInc p m n i j)) := by
  rw [belowRec_HpotInc_eq]
  exact belowRec_drift_ge_neg_bRec (p := p) hp1 hp2 (m := m) (n := n) hij

/-- **Integrability of the restricted below-record increment**, at the common increment. -/
theorem integrable_HpotInc_belowRec (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    (i j : Fin N) :
    Integrable ((belowRecSet p m n i j).indicator (HpotInc p m n i j)) (arrayMeasure N) := by
  rw [belowRec_HpotInc_eq]
  exact integrable_belowRec_increment (p := p) hp1 hp2 (m := m) (n := n) i j

/-! ### The analytic side conditions of the mass (integral) form -/

/-- The below-record region is ambient measurable (it is `enlFilt p m n`-measurable). -/
theorem measurableSet_belowRecSet_ambient (p : ℝ) (m n : ℕ) (i j : Fin N) :
    MeasurableSet (belowRecSet p m n i j) :=
  (enlFilt p m).le n _ (measurableSet_belowRecSet p m n i j)

/-- The ledger weight `1_B (-bRec)` restricted below the record is integrable: `bRec = HprevAt + 2`
is bounded by `2 n + 5` on the whole array space. -/
theorem integrable_belowRec_neg_bRec (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (i j : Fin N) :
    Integrable (fun U => (belowRecSet p m n i j).indicator (fun U => -(bRec p m n j U)) U)
      (arrayMeasure N) := by
  have hA := measurableSet_belowRecSet_ambient (N := N) p m n i j
  have hfun : (fun U : Array N => -(bRec p m n j U))
      = fun U => -(HprevAt p m n j U + 2) := by
    funext U
    rw [bRec]
  have hmeas : Measurable (fun U : Array N =>
      (belowRecSet p m n i j).indicator (fun U => -(bRec p m n j U)) U) := by
    rw [hfun]
    exact (((measurable_HprevAt p m n j).add_const 2).neg).indicator hA
  refine Integrable.mono' (integrable_const (2 * (n : ℝ) + 5)) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  by_cases hU : U ∈ belowRecSet p m n i j
  · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
    show |-(bRec p m n j U)| ≤ 2 * (n : ℝ) + 5
    rw [abs_neg, bRec]
    have h1 : |HprevAt p m n j U| ≤ 2 * (n : ℝ) + 3 := abs_HprevAt_le hp1 hp2 m n j U
    have h2 : |HprevAt p m n j U + 2| ≤ |HprevAt p m n j U| + 2 := by
      simpa using abs_add_le (HprevAt p m n j U) (2 : ℝ)
    linarith
  · rw [Set.indicator_of_notMem hU, norm_zero]
    positivity

/-- The ledger weight `1_B (-bRec)` is already `enlFilt p m n`-measurable, so it can be pulled
out of (or compared inside) an `enlFilt` conditional expectation; the assembly uses this where a
restricted lower bound is stated against an adapted weight. -/
theorem measurable_enlFilt_belowRec_neg_bRec (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    Measurable[enlFilt p m n]
      (fun U => (belowRecSet p m n i j).indicator (fun U => -(bRec p m n j U)) U) := by
  have hfun : (fun U : Array N => -(bRec p m n j U))
      = fun U => -(HprevAt p m n j U + 2) := by
    funext U
    rw [bRec]
  rw [hfun]
  exact (((measurable_HprevAt_enlFilt hp1.le m n j).add_const 2).neg).indicator
    (measurableSet_belowRecSet p m n i j)

/-- **Mass form of the below-record bound**: the restricted conditional drift dominates `-b_n`
on `B` also after integrating,
`∫_B (-b_n) ≤ ∫_B HpotInc`.  This is the one-step contribution of the strictly-below-record
region to the paper's `(Zloss)` bookkeeping (the `g`-sum counterpart is not claimed here). -/
theorem setIntegral_belowRec_HpotInc_ge (p : ℝ) (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m n : ℕ}
    {i j : Fin N} (hij : i ≠ j) :
    ∫ U in belowRecSet p m n i j, (-(bRec p m n j U)) ∂(arrayMeasure N)
      ≤ ∫ U in belowRecSet p m n i j, HpotInc p m n i j U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hA := measurableSet_belowRecSet_ambient (N := N) p m n i j
  have hInt : Integrable ((belowRecSet p m n i j).indicator (HpotInc p m n i j)) (arrayMeasure N) :=
    integrable_HpotInc_belowRec (p := p) hp1 hp2 (m := m) (n := n) i j
  have hbound := integrable_belowRec_neg_bRec (N := N) (p := p) hp1 hp2 m n i j
  have hmono := integral_mono_ae hbound integrable_condExp
    (HpotInc_belowRec_ge_neg_bRec (p := p) hp1 hp2 (m := m) (n := n) hij)
  have hce : ∫ U, condExp (enlFilt p m n) (arrayMeasure N)
        ((belowRecSet p m n i j).indicator (HpotInc p m n i j)) U ∂(arrayMeasure N)
      = ∫ U, (belowRecSet p m n i j).indicator (HpotInc p m n i j) U ∂(arrayMeasure N) :=
    integral_condExp hle
  rw [hce, integral_indicator hA, integral_indicator hA] at hmono
  exact hmono

/-! ### The finite offset partition, pointwise and at `HpotInc` -/

/-- **Pointwise indicator decomposition of the offset partition**, for an arbitrary
`f : Array N → ℝ`:

  `f = 1_B · f + Σ_{g < n+1} 1_{A_g} · f`,

where `B = belowRecSet p m n i j` and `A_g = abovePosSet p m n i j g`.  Uses only the audited
finite cover (`univ_eq_belowRec_union_above`) and the two disjointness lemmas, so it inherits
their sign conventions; no probability, no measurability. -/
theorem indicator_partition_belowRec_above (p : ℝ) (m n : ℕ) (i j : Fin N) (f : Array N → ℝ) :
    f = fun U => (belowRecSet p m n i j).indicator f U
      + ∑ g ∈ Finset.range (n + 1), (abovePosSet p m n i j g).indicator f U := by
  funext U
  by_cases hB : U ∈ belowRecSet p m n i j
  · have hzero : (∑ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator f U) = 0 := by
      refine Finset.sum_eq_zero fun g _ => ?_
      refine Set.indicator_of_notMem (f := f) (s := abovePosSet p m n i j g) (a := U) ?_
      exact fun hmem => (Set.disjoint_left.mp (disjoint_belowRec_abovePosSet p m n i j g)) hB hmem
    rw [Set.indicator_of_mem hB, hzero, add_zero]
  · have hmem : U ∈ ⋃ g ∈ Finset.range (n + 1), abovePosSet p m n i j g := by
      have huniv : U ∈ belowRecSet p m n i j
          ∪ ⋃ g ∈ Finset.range (n + 1), abovePosSet p m n i j g := by
        rw [← univ_eq_belowRec_union_above]
        exact Set.mem_univ U
      rcases huniv with h | h
      · exact absurd h hB
      · exact h
    obtain ⟨g, hg, hUg⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using hmem
    have hsingle : (∑ g' ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g').indicator f U)
        = (abovePosSet p m n i j g).indicator f U := by
      refine Finset.sum_eq_single g ?_ ?_
      · intro b _ hne
        refine Set.indicator_of_notMem (f := f) (s := abovePosSet p m n i j b) (a := U) ?_
        exact fun hmem_b =>
          (Set.disjoint_left.mp ((disjoint_abovePosSet p m n i j hne).symm)) hUg hmem_b
      · intro hgnot
        exact absurd hg hgnot
    rw [Set.indicator_of_notMem hB, hsingle, Set.indicator_of_mem hUg, zero_add]

/-- **The pointwise partition of the actual one-step increment**:
`HpotInc = 1_B · HpotInc + Σ_{g < n+1} 1_{A_g} · HpotInc`.  Each summand is the restricted
increment of one region of the ledger; this is the decomposition the finite `condExp`-additive
global assembly applies. -/
theorem HpotInc_eq_belowRec_add_sum (p : ℝ) (m n : ℕ) (i j : Fin N) :
    HpotInc p m n i j
      = fun U => (belowRecSet p m n i j).indicator (HpotInc p m n i j) U
          + ∑ g ∈ Finset.range (n + 1),
              (abovePosSet p m n i j g).indicator (HpotInc p m n i j) U :=
  indicator_partition_belowRec_above p m n i j (HpotInc p m n i j)

/-- **The partition at the constant `1`**: `1 = 1_B + Σ_{g < n+1} 1_{A_g}` pointwise.  This is
the "`1 = Σ` of the finitely many region indicators" identity that turns a global one-step
conditional moment into the sum of the region-restricted ones. -/
theorem one_eq_indicator_belowRec_add_sum (p : ℝ) (m n : ℕ) (i j : Fin N) :
    (fun _ : Array N => (1 : ℝ))
      = fun U => (belowRecSet p m n i j).indicator (fun _ => (1 : ℝ)) U
          + ∑ g ∈ Finset.range (n + 1),
              (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ)) U :=
  indicator_partition_belowRec_above p m n i j (fun _ => (1 : ℝ))

/-! ### Smoke test at concrete constants -/

/- At `N = 2`, `p = 3/4`, `m = 2`, `n = 1`, `i = 0`, `j = 1` every hypothesis of the
below-record bundle is satisfiable, and the ledger bound, the integrability of the restricted
increment and the pointwise offset partition all instantiate together.  Nothing here is a new
claim: it is the check that the audited interface is usable at concrete numbers rather than
only vacuously. -/
section Smoke

example :
    (fun U => (belowRecSet (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)).indicator
        (fun U => -(bRec (p := (3 : ℝ) / 4) 2 1 (1 : Fin 2) U)) U)
      ≤ᵐ[arrayMeasure 2] condExp (enlFilt (p := (3 : ℝ) / 4) (m := 2) 1) (arrayMeasure 2)
        ((belowRecSet (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)).indicator
          (HpotInc (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2))) :=
  HpotInc_belowRec_ge_neg_bRec (p := (3 : ℝ) / 4) (by norm_num) (by norm_num)
    (m := 2) (n := 1) (by decide : (0 : Fin 2) ≠ 1)

example : Integrable ((belowRecSet (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)).indicator
    (HpotInc (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2))) (arrayMeasure 2) :=
  integrable_HpotInc_belowRec (p := (3 : ℝ) / 4) (by norm_num) (by norm_num)
    (m := 2) (n := 1) (0 : Fin 2) (1 : Fin 2)

example :
    HpotInc (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)
      = fun U => (belowRecSet (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)).indicator
            (HpotInc (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)) U
          + ∑ g ∈ Finset.range (1 + 1),
              (abovePosSet (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2) g).indicator
                (HpotInc (p := (3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)) U :=
  HpotInc_eq_belowRec_add_sum (N := 2) ((3 : ℝ) / 4) 2 1 (0 : Fin 2) (1 : Fin 2)

end Smoke

/-! ### Axiom audit -/


end Swarming.Enl
