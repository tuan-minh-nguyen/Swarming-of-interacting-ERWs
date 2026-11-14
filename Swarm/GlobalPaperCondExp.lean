/-
  **Direction B (m2) — `GlobalPaperCondExp.lean`: the pointwise `enlFilt` lower bound of the
  paper's one-step `(Zloss)` weight.**

  The integrated one-step *integral* budget
  (`GlobalIntegralBudget.integral_HpotInc_ge_paperWeight`, discharged in `DischargeInputs`) states

    `∫ paperWeight ≤ ∫ HpotInc`.

  This file proves the genuine a.e. **pointwise** statement behind it:

    `paperWeight p m n i j ≤ᵐ[arrayMeasure N] (arrayMeasure N)[HpotInc p m n i j | enlFilt p m n]`

  for `1/2 < p < 1`, `2 ≤ m`, `i ≠ j` and every `n`, with `paperWeight` the *sharp* paper weight
  `1{0 ≤ X_n^i ≤ M_n^j} - b_n a^{(X_n^i - M_n^j)} 1{M_n^j ≤ X_n^i}` — i.e. the sharp below-row
  `posWeight = 1{0 ≤ X_n^i}`, never the lossy `-b_n` campaign row.

  The argument is pure bookkeeping on the finite partition
  `B ∪ ⋃_{g < n+1} A_g` of `Direction G`:

  * `paperWeight` is, pointwise, the *sum of its rows*:
    `1_B · posWeight + 1_{A_0} · (1 - b_n) + Σ_{g ≥ 1} 1_{A_g} · (-b_n a^g)`
    (`paperWeight_eq_pieces`);
  * each row is dominated a.e. by the restricted `enlFilt`-conditional mean of the corresponding
    piece of the increment — the sharp below row (`DischargeInputs.belowSharp_hypothesis_discharged`,
    from the accepted exact below-record identity plus the interior/negative bracket bounds), the
    record row `g = 0` (`RecordTower.indicator_le_condExp_indicator_HpotInc_zero`) and the above
    rows `g ≥ 1` (`AboveTower.indicator_le_condExp_indicator_HpotInc_abovePosSet`);
  * the *linearity* of the conditional expectation over the finite partition,
    `E[f | enlFilt n] =ᵐ E[1_B f | enlFilt n] + Σ_g E[1_{A_g} f | enlFilt n]`
    (`condExp_eq_indicator_pieces_of_integrable`, `condExp_add` + `condExp_finsetSum`), converts the
    sum of restricted bounds into the single global conditional mean.

  Delivered here:

  * the unconditional pointwise bound (`paperWeight_le_condExp_discharged`) and its explicit-input
    form (`paperWeight_le_condExp_of_hypotheses`);
  * the **exact global projected identity**: the whole `enlFilt n`-conditional mean written as the
    below bracket plus the record row plus the above rows of `eRec`
    (`condExp_HpotInc_eq_piecewise_rows`) — no inequality, the exact projected form;
  * the weight-time aggregation `Σ_{n < N₀} paperWeight(n) ≤ᵐ Σ_{n < N₀} E[HpotInc(n) | enlFilt n]`
    (`sum_range_paperWeight_le_condExp`) together with the adaptedness of each compensator term;
  * the integral re-derivation of the accepted budget from the pointwise statement
    (`integral_paperWeight_le_of_condExp`), as a consistency check — it is the accepted
    `integral_HpotInc_ge_paperWeight_discharged`, not a substitute for it;
  * the campaign corollary `campaignWeight ≤ᵐ paperWeight` (nonnegative remainder) is recorded as
    `campaignWeight_le_paperWeight`; Direction A owns the campaign statement.

  No `sorry`, no `admit`, no custom axioms, no `native_decide`; axiom prints at the end of the file.
  Nothing here edits `results/` or any earlier artifact: it only imports the accepted modules.
-/
import Swarm.DischargeInputs

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl
namespace Budget

open Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmCross

variable {N : ℕ}

/-! ### 1. The finite partition, in multiplicative form

`indicator_belowSet_add_sum_abovePosSet` is the partition of unity
`1_B + Σ_{g < n+1} 1_{A_g} = 1`.  Multiplying by `f` gives the decomposition of `f` used by both
the weight side and the conditional-expectation side. -/

namespace Paper

/-- **The partition applied to a function**: `f = 1_B f + Σ_{g < n+1} 1_{A_g} f` pointwise. -/
theorem indicator_partition_sum_eq_self (p : ℝ) (m n : ℕ) (i j : Fin N) (f : Array N → ℝ)
    (U : Array N) :
    f U = (belowSet p m n i j).indicator f U
      + ∑ g ∈ Finset.range (n + 1), (abovePosSet p m n i j g).indicator f U := by
  classical
  have hpart := indicator_belowSet_add_sum_abovePosSet p m n i j U
  calc f U = ((belowSet p m n i j).indicator (fun _ => (1 : ℝ)) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ)) U) * f U := by
        rw [hpart, one_mul]
    _ = (belowSet p m n i j).indicator (fun _ => (1 : ℝ)) U * f U
        + (∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (fun _ => (1 : ℝ)) U) * f U := by
        rw [add_mul]
    _ = (belowSet p m n i j).indicator f U
        + ∑ g ∈ Finset.range (n + 1), (abovePosSet p m n i j g).indicator f U := by
        rw [Finset.sum_mul]
        congr 1
        · by_cases hU : U ∈ belowSet p m n i j
          · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]; ring
          · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]; ring
        · exact Finset.sum_congr rfl fun g _ => by
            by_cases hU : U ∈ abovePosSet p m n i j g
            · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]; ring
            · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]; ring

end Paper

/-! ### 2. The paper weight as the sum of its rows

The sharp below row is `posWeight = 1{0 ≤ X_n^i}`; at the record it is `1 - b_n`; at offset
`g ≥ 1` it is `-b_n a^g`.  These are exactly the `offsetWeight` pieces of the campaign ledger, so
only the below row changes relative to `campaignWeight_eq_pieces`. -/

/-- **The paper weight, decomposed onto the finite partition.**  This is
`paperWeight_eq_campaignWeight_add_below` applied to `campaignWeight_eq_pieces`: the campaign's
below row `-b_n` plus the exact remainder `1{0 ≤ x} + b_n` is the paper's below row `1{0 ≤ x}`. -/
theorem paperWeight_eq_pieces (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    paperWeight p m n i j U
      = (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U := by
  classical
  have hrem := paperWeight_eq_campaignWeight_add_below p m n i j U
  have hcamp := campaignWeight_eq_pieces p m n i j U
  rw [hrem, hcamp]
  by_cases hU : U ∈ belowSet p m n i j
  · have hzero : ∀ g ∈ Finset.range (n + 1),
        (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U = 0 := by
      intro g hg
      exact Set.indicator_of_notMem (f := offsetWeight p m n j g) (fun h =>
        (Set.disjoint_left.mp (disjoint_belowSet_abovePosSet p m n i j hg)) hU h)
    rw [Finset.sum_eq_zero hzero]
    simp only [Set.indicator_of_mem hU]
    ring
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
    ring

/-! ### 3. Finite a.e. monotonicity

A finite family of a.e. inequalities can be added.  Used to accumulate the below row and the
finitely many above rows. -/

namespace Paper

/-- **A finite sum of a.e. inequalities is an a.e. inequality.** -/
theorem eventuallyLE_finset_sum {ι : Type*} (s : Finset ι) {f g : ι → Array N → ℝ}
    (h : ∀ i ∈ s, f i ≤ᵐ[arrayMeasure N] g i) :
    (fun U => ∑ i ∈ s, f i U) ≤ᵐ[arrayMeasure N] (fun U => ∑ i ∈ s, g i U) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall (fun U => le_refl (0 : ℝ))
  | insert a s ha ih =>
      have h1 : f a ≤ᵐ[arrayMeasure N] g a := h a (Finset.mem_insert_self a s)
      have h2 : (fun U => ∑ i ∈ s, f i U) ≤ᵐ[arrayMeasure N] (fun U => ∑ i ∈ s, g i U) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      filter_upwards [h1, h2] with U h1 h2
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add h1 h2

/-- **A finite sum of a.e. equalities is an a.e. equality.** -/
theorem eventuallyEq_finset_sum {ι : Type*} (s : Finset ι) {f h : ι → Array N → ℝ}
    (hf : ∀ i ∈ s, f i =ᵐ[arrayMeasure N] h i) :
    (fun U => ∑ i ∈ s, f i U) =ᵐ[arrayMeasure N] (fun U => ∑ i ∈ s, h i U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : f a =ᵐ[arrayMeasure N] h a := hf a (Finset.mem_insert_self a s)
      have h2 : (fun U => ∑ i ∈ s, f i U) =ᵐ[arrayMeasure N] (fun U => ∑ i ∈ s, h i U) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      filter_upwards [h1, h2] with U h1 h2
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2]

end Paper

/-! ### 4. Linearity of the conditional expectation over the partition

This is the exact projected form on the increment side, and holds with no hypothesis beyond
integrability: `enlFilt n`-conditioning is linear, and the finite partition splits `f` into the
below piece and the above pieces. -/

/-- **Exact linearity over the finite partition.**
`E[f | enlFilt n] =ᵐ E[1_B f | enlFilt n] + Σ_{g < n+1} E[1_{A_g} f | enlFilt n]`.

No measurability of `B` or `A_g` with respect to `enlFilt n` is used: this is additivity
(`condExp_add`) and finite-sum additivity (`condExp_finsetSum`) applied to the pointwise
partition identity `indicator_partition_sum_eq_self`. -/
theorem condExp_eq_indicator_pieces_of_integrable (p : ℝ) (m n : ℕ) (i j : Fin N)
    {f : Array N → ℝ} (hf : Integrable f (arrayMeasure N)) :
    condExp (enlFilt p m n) (arrayMeasure N) f
      =ᵐ[arrayMeasure N] (fun U =>
        condExp (enlFilt p m n) (arrayMeasure N) ((belowSet p m n i j).indicator f) U
        + ∑ g ∈ Finset.range (n + 1),
            condExp (enlFilt p m n) (arrayMeasure N)
              ((abovePosSet p m n i j g).indicator f) U) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hB : Integrable ((belowSet p m n i j).indicator f) (arrayMeasure N) :=
    hf.indicator (measurableSet_belowSet p m n i j)
  have hA : ∀ g ∈ Finset.range (n + 1),
      Integrable ((abovePosSet p m n i j g).indicator f) (arrayMeasure N) :=
    fun g _ => hf.indicator (measurableSet_abovePosSet_w p m n i j g)
  have hsum : Integrable (fun U => ∑ g ∈ Finset.range (n + 1),
      (abovePosSet p m n i j g).indicator f U) (arrayMeasure N) :=
    integrable_finsetSum _ hA
  calc condExp (enlFilt p m n) (arrayMeasure N) f
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => (belowSet p m n i j).indicator f U
            + ∑ g ∈ Finset.range (n + 1), (abovePosSet p m n i j g).indicator f U) :=
        condExp_congr_ae (Filter.Eventually.of_forall
          fun U => Paper.indicator_partition_sum_eq_self p m n i j f U)
    _ =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
            ((belowSet p m n i j).indicator f)
          + condExp (enlFilt p m n) (arrayMeasure N)
              (fun U => ∑ g ∈ Finset.range (n + 1),
                (abovePosSet p m n i j g).indicator f U) :=
        condExp_add hB hsum (enlFilt p m n)
    _ =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
            ((belowSet p m n i j).indicator f)
          + condExp (enlFilt p m n) (arrayMeasure N)
              (∑ g ∈ Finset.range (n + 1), (abovePosSet p m n i j g).indicator f) :=
        (Filter.EventuallyEq.refl _ _).add (condExp_congr_ae
          (Filter.EventuallyEq.of_eq (funext fun U => by rw [Finset.sum_apply])))
    _ =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
            ((belowSet p m n i j).indicator f)
          + ∑ g ∈ Finset.range (n + 1),
              condExp (enlFilt p m n) (arrayMeasure N)
                ((abovePosSet p m n i j g).indicator f) :=
        (Filter.EventuallyEq.refl _ _).add (condExp_finsetSum hA (enlFilt p m n))
    _ =ᵐ[arrayMeasure N] (fun U =>
        condExp (enlFilt p m n) (arrayMeasure N) ((belowSet p m n i j).indicator f) U
        + ∑ g ∈ Finset.range (n + 1),
            condExp (enlFilt p m n) (arrayMeasure N)
              ((abovePosSet p m n i j g).indicator f) U) :=
        Filter.EventuallyEq.of_eq
          (funext fun U => by rw [Pi.add_apply, Finset.sum_apply])

/-! ### 5. The row bounds, accumulated

Each row of the paper weight is dominated a.e. by the restricted conditional mean of the matching
piece of the increment.  The pieces are `B` (sharp below row), `A_0` (record row) and `A_{g}`
for `g ≥ 1` (above rows). -/

/-- **The accumulated row inequality.**  With the sharp below-row bound and the above-row bounds as
explicit hypotheses, the whole piecewise weight is dominated a.e. by the sum of the restricted
conditional means (the below piece, the record piece `g = 0` and the above pieces `g ≥ 1`).
`hij` is a standing assumption of the ledger (it is consumed when the two row inputs are
discharged); the lemma itself only uses the two hypotheses. -/
theorem pieces_le_pieces_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelowSharp : (fun U => (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    (fun U => (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
      ≤ᵐ[arrayMeasure N] (fun U =>
        condExp (enlFilt p m n) (arrayMeasure N)
            ((belowSet p m n i j).indicator (HpotInc p m n i j)) U
        + ∑ g ∈ Finset.range (n + 1),
            condExp (enlFilt p m n) (arrayMeasure N)
              ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) U) := by
  classical
  have hA : ∀ g ∈ Finset.range (n + 1),
      (fun U => (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) := by
    intro g hg
    match g with
    | 0 =>
        have hw : offsetWeight p m n j 0 = (fun U => 1 - bRec p m n j U) := rfl
        rw [hw]
        exact indicator_le_condExp_indicator_HpotInc_zero (N := N) p hp1 hp2 m n hij
    | (k + 1) =>
        have hk : k + 1 ≤ n := by
          have := Finset.mem_range.mp hg
          omega
        have hw : offsetWeight p m n j (k + 1)
            = (fun U => -(bRec p m n j U * aRec p m ^ (k + 1))) := rfl
        rw [hw]
        exact hAbove (k + 1) (by omega) hk
  have hsum := Paper.eventuallyLE_finset_sum (s := Finset.range (n + 1))
    (f := fun g => fun U => (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U)
    (g := fun g => condExp (enlFilt p m n) (arrayMeasure N)
      ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) hA
  filter_upwards [hBelowSharp, hsum] with U h1 h2
  exact add_le_add h1 h2

/-! ### 6. The pointwise global paper bound -/

/-- **The pointwise global `enlFilt` bound for the paper weight**, with the two regional inputs as
explicit hypotheses (`hij` is again the standing distinct-walker assumption).  Composes `paperWeight_eq_pieces`, the accumulated row bounds
(`pieces_le_pieces_condExp`) and the exact linearity of the conditional expectation over the finite
partition (`condExp_eq_indicator_pieces_of_integrable`). -/
theorem paperWeight_le_condExp_of_hypotheses {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j)
    (hBelowSharp : (fun U => (belowSet p m n i j).indicator
        (fun U => posWeight p m n i U) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        ((belowSet p m n i j).indicator (HpotInc p m n i j)))
    (hAbove : ∀ g : ℕ, 1 ≤ g → g ≤ n →
      (fun U => (abovePosSet p m n i j g).indicator
          (fun U => -(bRec p m n j U * aRec p m ^ g)) U)
        ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j))) :
    paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) := by
  have hpne : p ≠ 0 := by linarith
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hle := pieces_le_pieces_condExp (N := N) (p := p) hp1 hp2 hij hBelowSharp hAbove
  have heq := condExp_eq_indicator_pieces_of_integrable (N := N) (p := p) (m := m) (n := n)
    (i := i) (j := j) hf
  have h1 : paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] (fun U =>
        (belowSet p m n i j).indicator (fun U => posWeight p m n i U) U
        + ∑ g ∈ Finset.range (n + 1),
            (abovePosSet p m n i j g).indicator (offsetWeight p m n j g) U) :=
    Filter.Eventually.of_forall (fun U => (paperWeight_eq_pieces p m n i j U).le)
  exact Filter.EventuallyLE.trans_eq (Filter.EventuallyLE.trans h1 hle) heq.symm

/-- **The pointwise global `enlFilt` bound for the paper weight, unconditionally.**

Both regional inputs are the accepted, integrated ones: the sharp below-record bound
(`DischargeInputs.belowSharp_hypothesis_discharged`, built from the exact below-record identity plus
the interior/negative bracket bounds) and the above-record towers `g ≥ 1`
(`DischargeInputs.above_hypothesis_discharged`, from `AboveTower`, `2 ≤ m`).

Conclusion, for `1/2 < p < 1`, `2 ≤ m`, `i ≠ j`, every `n`:

  `paperWeight p m n i j ≤ᵐ[arrayMeasure N] (arrayMeasure N)[HpotInc p m n i j | enlFilt p m n]`. -/
theorem paperWeight_le_condExp_discharged {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    paperWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) :=
  paperWeight_le_condExp_of_hypotheses (N := N) (p := p) hp1 hp2 hij
    (belowSharp_hypothesis_discharged (N := N) (p := p) hp1 hp2 hij)
    (above_hypothesis_discharged (N := N) (p := p) hp1 hp2 hm hij)

/-! ### 7. The campaign weight is dominated by the paper weight

The exact remainder `1_B (1{0 ≤ X_n^i} + b_n)` is nonnegative (`b_n ≥ 3`), so the campaign weight
is the paper weight minus a nonnegative function.  This is *not* the route to the bound — the
sharp bound is proved directly in §6 — but it is the exact relation between the two ledgers, and it
records that the paper-level statement is strictly stronger. -/

/-- **The campaign weight is pointwise dominated by the paper weight.** -/
theorem campaignWeight_le_paperWeight {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) (U : Array N) :
    campaignWeight p m n i j U ≤ paperWeight p m n i j U := by
  rw [paperWeight_eq_campaignWeight_add_below]
  by_cases hU : U ∈ belowSet p m n i j
  · rw [Set.indicator_of_mem hU]
    have hb := three_le_bRec (p := p) hp1 hp2 m n j U
    have hp := posWeight_nonneg (p := p) m n i U
    linarith
  · rw [Set.indicator_of_notMem hU, add_zero]

/-- **Corollary (Direction A's statement, through the sharp paper row).**  Since the paper weight
dominates the campaign weight, the campaign weight is also dominated by the global `enlFilt`
conditional mean.  Direction A owns this statement; it is recorded here only as an immediate
consequence of §6. -/
theorem campaignWeight_le_condExp_of_paper {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    campaignWeight p m n i j
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) :=
  Filter.EventuallyLE.trans
    (Filter.Eventually.of_forall fun U =>
      campaignWeight_le_paperWeight hp1 hp2 m n i j U)
    (paperWeight_le_condExp_discharged hp1 hp2 hm hij)

/-! ### 8. Consistency with the accepted integral budget

The accepted `DischargeInputs.integral_HpotInc_ge_paperWeight_discharged` is the integral of the
pointwise statement proved above.  Integrating the pointwise bound with
`GlobalIntegralBudget.integral_le_of_condExp_ge` recovers it exactly; the two agree. -/

/-- **The accepted mass budget, re-derived from the pointwise bound.**  This is a check that the
a.e. statement of §6 integrates to the accepted `∫ paperWeight ≤ ∫ HpotInc`. -/
theorem integral_paperWeight_le_of_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, paperWeight p m n i j U ∂(arrayMeasure N) ≤ ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  integral_le_of_condExp_ge (N := N) (p := p) hp1 hp2
    (integrable_paperWeight_w (p := p) hp1 hp2 m n i j)
    (paperWeight_le_condExp_discharged (N := N) (p := p) hp1 hp2 hm hij)

/-- The same statement in the orientation of the accepted input. -/
theorem integral_HpotInc_ge_paperWeight_of_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, HpotInc p m n i j U ∂(arrayMeasure N)
      ≥ ∫ U, paperWeight p m n i j U ∂(arrayMeasure N) :=
  integral_paperWeight_le_of_condExp hp1 hp2 hm hij

/-! ### 9. The exact projected identity

The global `enlFilt n`-conditional mean of the increment is, exactly, the paper's projected ledger:
the below bracket `alpha h_j(x) - (1 - alpha) h_j(x-1)`, the record row
`alpha e_0 - (1 - alpha) h_j(M-1)` and the above rows `alpha e_g - (1 - alpha) e_{g-1}`.

Each row is the accepted restricted identity of the integrated files
(`BelowRecordHpotInc.condExp_HpotInc_belowRec`, `RecordTower.condExp_indicator_HpotInc_enlFilt_zero`,
`AboveTower.condExp_indicator_HpotInc_enlFilt_abovePosSet_succ`), and the assembly is the same
finite linearity as §4 — so this is an identity, not a lossy offcut of the proof of §6. -/

/-- **The exact projected form of the paper's one-step ledger.**  For `1/2 < p < 1` and `i ≠ j`,

`E[HpotInc | enlFilt n]`
  `=ᵐ 1_B (alpha h_j(X_n^i) - (1-alpha) h_j(X_n^i - 1))`
  `  + 1_{A_0} (alpha e_0 - (1-alpha) h_j(M_n^j - 1))`
  `  + Σ_{k<n} 1_{A_{k+1}} (alpha e_{k+1} - (1-alpha) e_k)`,

with `B = {X_n^i < M_n^j}`, `A_g = {X_n^i = M_n^j + g}`.  (No `2 ≤ m` is needed: the `g ≥ 1`
identity of `AboveTower` holds at `m ≥ 1`.) -/
theorem condExp_HpotInc_eq_piecewise_rows {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)
      =ᵐ[arrayMeasure N] (fun U =>
        (belowSet p m n i j).indicator
          (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
            - (1 - alphaFun p m n i U)
              * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U
        + (abovePosSet p m n i j 0).indicator
            (fun U => alphaFun p m n i U * eRec p m n j 0 U
              - (1 - alphaFun p m n i U) * HprevAt p m n j U) U
        + ∑ k ∈ Finset.range n,
            (abovePosSet p m n i j (k + 1)).indicator
              (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
                - (1 - alphaFun p m n i U) * eRec p m n j k U) U) := by
  have hpne : p ≠ 0 := by linarith
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hdecomp := condExp_eq_indicator_pieces_of_integrable (N := N) (p := p) (m := m) (n := n)
    (i := i) (j := j) hf
  have hbelow := condExp_HpotInc_belowRec (p := p) hp1 hp2 (m := m) (n := n) (i := i) (j := j)
  rw [belowRecSet_eq_belowSet] at hbelow
  have hzero := condExp_indicator_HpotInc_enlFilt_zero (N := N) p hp1 hp2 m n hij
  have hsucc : ∀ k : ℕ, condExp (enlFilt p m n) (arrayMeasure N)
      ((abovePosSet p m n i j (k + 1)).indicator (HpotInc p m n i j))
      =ᵐ[arrayMeasure N] (abovePosSet p m n i j (k + 1)).indicator
        (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
          - (1 - alphaFun p m n i U) * eRec p m n j k U) :=
    fun k => condExp_indicator_HpotInc_enlFilt_abovePosSet_succ (p := p) hp1 hp2 m n hij k
  -- the above rows: split off `g = 0` and replace every row by its exact identity
  have hS : (fun U => ∑ g ∈ Finset.range (n + 1),
        condExp (enlFilt p m n) (arrayMeasure N)
          ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) U)
      =ᵐ[arrayMeasure N] (fun U =>
        (∑ k ∈ Finset.range n,
            (abovePosSet p m n i j (k + 1)).indicator
              (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
                - (1 - alphaFun p m n i U) * eRec p m n j k U) U)
        + (abovePosSet p m n i j 0).indicator
            (fun U => alphaFun p m n i U * eRec p m n j 0 U
              - (1 - alphaFun p m n i U) * HprevAt p m n j U) U) := by
    have hsplit : (fun U => ∑ g ∈ Finset.range (n + 1),
          condExp (enlFilt p m n) (arrayMeasure N)
            ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) U)
        = (fun U => (∑ k ∈ Finset.range n,
              condExp (enlFilt p m n) (arrayMeasure N)
                ((abovePosSet p m n i j (k + 1)).indicator (HpotInc p m n i j)) U)
            + condExp (enlFilt p m n) (arrayMeasure N)
                ((abovePosSet p m n i j 0).indicator (HpotInc p m n i j)) U) := by
      funext U
      rw [Finset.sum_range_succ']
    have hcongr : (fun U => ∑ k ∈ Finset.range n,
          condExp (enlFilt p m n) (arrayMeasure N)
            ((abovePosSet p m n i j (k + 1)).indicator (HpotInc p m n i j)) U)
        =ᵐ[arrayMeasure N] (fun U => ∑ k ∈ Finset.range n,
            (abovePosSet p m n i j (k + 1)).indicator
              (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
                - (1 - alphaFun p m n i U) * eRec p m n j k U) U) :=
      Paper.eventuallyEq_finset_sum _ (fun k _ => hsucc k)
    rw [hsplit]
    exact hcongr.add hzero
  have hmid : (fun U =>
        condExp (enlFilt p m n) (arrayMeasure N)
            ((belowSet p m n i j).indicator (HpotInc p m n i j)) U
        + ∑ g ∈ Finset.range (n + 1),
            condExp (enlFilt p m n) (arrayMeasure N)
              ((abovePosSet p m n i j g).indicator (HpotInc p m n i j)) U)
      =ᵐ[arrayMeasure N] (fun U =>
        (belowSet p m n i j).indicator
          (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
            - (1 - alphaFun p m n i U)
              * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U
        + ((∑ k ∈ Finset.range n,
            (abovePosSet p m n i j (k + 1)).indicator
              (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
                - (1 - alphaFun p m n i U) * eRec p m n j k U) U)
          + (abovePosSet p m n i j 0).indicator
            (fun U => alphaFun p m n i U * eRec p m n j 0 U
              - (1 - alphaFun p m n i U) * HprevAt p m n j U) U)) := by
    filter_upwards [hbelow, hS] with U h1 h2
    rw [h1, h2]
  refine Filter.EventuallyEq.trans hdecomp ?_
  refine Filter.EventuallyEq.trans hmid ?_
  exact Filter.Eventually.of_forall (fun U => by ring)

/-! ### 10. The compensator and the weight-time aggregation

The one-step predicted increment is `paperCompensator p m n i j = E[HpotInc | enlFilt n]`.  It is
`enlFilt n`-strongly-measurable (so the summed ledger is an adapted process at each time) and
integrable, with the same integral as the increment.  The pointwise bound of §6 then aggregates
over a finite time window. -/

/-- The one-step compensator (predicted increment) of the paper ledger at time `n`. -/
noncomputable def paperCompensator (p : ℝ) (m n : ℕ) (i j : Fin N) : Array N → ℝ :=
  condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)

/-- The paper weight is dominated by the one-step compensator (restatement of §6). -/
theorem paperWeight_le_paperCompensator {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    paperWeight p m n i j ≤ᵐ[arrayMeasure N] paperCompensator p m n i j :=
  paperWeight_le_condExp_discharged (N := N) (p := p) hp1 hp2 hm hij

/-- **The compensator is adapted**: strongly measurable for `enlFilt n`. -/
theorem stronglyMeasurable_paperCompensator (p : ℝ) (m n : ℕ) (i j : Fin N) :
    StronglyMeasurable[enlFilt p m n] (paperCompensator p m n i j) :=
  stronglyMeasurable_condExp

/-- The compensator is integrable. -/
theorem integrable_paperCompensator {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) : Integrable (paperCompensator p m n i j) (arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  have hf : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  simpa only [paperCompensator] using
    (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n) (f := HpotInc p m n i j))

/-- The compensator has the integral of the increment (no mass is created by projecting). -/
theorem integral_paperCompensator {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) (i j : Fin N) :
    ∫ U, paperCompensator p m n i j U ∂(arrayMeasure N)
      = ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  exact integral_condExp hle

/-- **The weight-time aggregation**: over any finite time window `T` the summed paper weight is
a.e. dominated by the summed one-step compensators.  (Each time step contributes its own
`enlFilt n`; the finite intersection of the a.e. statements is an a.e. statement.) -/
theorem sum_range_paperWeight_le_sum_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    (fun U => ∑ n ∈ Finset.range T, paperWeight p m n i j U)
      ≤ᵐ[arrayMeasure N] (fun U => ∑ n ∈ Finset.range T,
        condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) :=
  Paper.eventuallyLE_finset_sum (s := Finset.range T)
    (f := fun n => paperWeight p m n i j)
    (g := fun n => condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j))
    (fun n _ => paperWeight_le_condExp_discharged (N := N) (p := p) hp1 hp2 hm hij (n := n))

/-- The same aggregation in the spelling of the compensator. -/
theorem sum_range_paperWeight_le_sum_paperCompensator {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    (fun U => ∑ n ∈ Finset.range T, paperWeight p m n i j U)
      ≤ᵐ[arrayMeasure N] (fun U => ∑ n ∈ Finset.range T, paperCompensator p m n i j U) :=
  Paper.eventuallyLE_finset_sum (s := Finset.range T)
    (f := fun n => paperWeight p m n i j)
    (g := fun n => paperCompensator p m n i j)
    (fun n _ => paperWeight_le_paperCompensator (N := N) (p := p) hp1 hp2 hm hij (n := n))

/-- **The integrated weight-time aggregation**: summing the accepted one-step budgets over a
finite time window.  (Kept separate from the a.e. statement: the a.e. aggregation above does *not*
need the integral budget, and this does not need the a.e. statement.) -/
theorem sum_range_integral_paperWeight_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    ∑ n ∈ Finset.range T, ∫ U, paperWeight p m n i j U ∂(arrayMeasure N)
      ≤ ∑ n ∈ Finset.range T, ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
  Finset.sum_le_sum fun n _ =>
    integral_HpotInc_ge_paperWeight_discharged (N := N) (p := p) hp1 hp2 hm hij (n := n)

/-- **The integrated weight-time aggregation from the pointwise one**: integrating the a.e.
aggregation of §10 gives `∫ Σ_{n<T} paperWeight(n) ≤ Σ_{n<T} ∫ HpotInc(n)`.  Unlike
`sum_range_integral_paperWeight_le` below, this consumes the *pointwise* statements (through
`integral_mono_ae` and the per-time integral identity `∫ E[HpotInc | enlFilt n] = ∫ HpotInc`), so it
is a genuine consequence of §6 rather than a restatement of the accepted per-time budgets. -/
theorem integral_sum_range_paperWeight_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    ∫ U, (∑ n ∈ Finset.range T, paperWeight p m n i j U) ∂(arrayMeasure N)
      ≤ ∑ n ∈ Finset.range T, ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  have hPW : Integrable (fun U => ∑ n ∈ Finset.range T, paperWeight p m n i j U)
      (arrayMeasure N) :=
    integrable_finsetSum _ (fun n _ => integrable_paperWeight_w (p := p) hp1 hp2 m n i j)
  have hCE : Integrable (fun U => ∑ n ∈ Finset.range T,
      condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) (arrayMeasure N) :=
    integrable_finsetSum _ (fun n _ => by
      have hn : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
        integrable_HpotInc hp1 hp2 hpne m n i j
      simpa only [paperCompensator] using
        (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n) (f := HpotInc p m n i j)))
  have hmono := integral_mono_ae hPW hCE
    (sum_range_paperWeight_le_sum_condExp (N := N) (p := p) hp1 hp2 hm hij T)
  have hsumCE : ∫ U, (∑ n ∈ Finset.range T,
        condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j) U) ∂(arrayMeasure N)
      = ∑ n ∈ Finset.range T, ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
    rw [integral_finsetSum _ (fun n _ => by
      have hn : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
        integrable_HpotInc hp1 hp2 hpne m n i j
      simpa only [paperCompensator] using
        (integrable_condExp (μ := arrayMeasure N) (m := enlFilt p m n) (f := HpotInc p m n i j)))]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
    haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
    exact integral_condExp hle
  linarith [hmono, hsumCE]

/-! ### 11. The paper bracket and the projected residual

Recording the bracket of §9 as a function makes the one-step ledger explicit:

  `HpotInc n = paperBracket n + paperResidual n`   (pointwise, exact),

and the residual has the exact projection

  `E[paperResidual n | enlFilt n] =ᵐ paperBracket n - E[paperBracket n | enlFilt n]`

— *the projection defect of the bracket*.  So the residual is centred exactly when the bracket is
`enlFilt n`-adapted; that adaptedness is carried as an **explicit premise**
(`condExp_paperResidual_eq_zero_of_stronglyMeasurable`), never as an axiom and never as a
martingale claim.  What holds *unconditionally* is the zero total integral
(`integral_paperResidual_eq_zero`) and, over a finite horizon, the exact compensation algebra
(`sum_range_paperResidual_eq`, `integral_sum_range_paperResidual_eq_zero`). -/

/-- **The paper's projected one-step bracket**: the below bracket, the record row and the above
rows — the right-hand side of the exact identity of §9. -/
noncomputable def paperBracket (p : ℝ) (m n : ℕ) (i j : Fin N) : Array N → ℝ :=
  fun U =>
    (belowSet p m n i j).indicator
      (fun U => alphaFun p m n i U * hZpot (envH p m j U) ((trajectory p m U n).pos i)
        - (1 - alphaFun p m n i U)
          * hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U
    + (abovePosSet p m n i j 0).indicator
        (fun U => alphaFun p m n i U * eRec p m n j 0 U
          - (1 - alphaFun p m n i U) * HprevAt p m n j U) U
    + ∑ k ∈ Finset.range n,
        (abovePosSet p m n i j (k + 1)).indicator
          (fun U => alphaFun p m n i U * eRec p m n j (k + 1) U
            - (1 - alphaFun p m n i U) * eRec p m n j k U) U

/-- **The exact identity of §9 in bracket form**: `E[HpotInc | enlFilt n] =ᵐ paperBracket`. -/
theorem condExp_HpotInc_eq_paperBracket {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)
      =ᵐ[arrayMeasure N] paperBracket p m n i j :=
  condExp_HpotInc_eq_piecewise_rows (N := N) hp1 hp2 m n hij

/-- The bracket is integrable (it is a version of the conditional mean). -/
theorem integrable_paperBracket {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) : Integrable (paperBracket p m n i j) (arrayMeasure N) :=
  (integrable_paperCompensator (N := N) (p := p) hp1 hp2 m n i j).congr
    (condExp_HpotInc_eq_paperBracket (N := N) (p := p) hp1 hp2 m n hij)

/-- The bracket has the integral of the increment. -/
theorem integral_paperBracket {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, paperBracket p m n i j U ∂(arrayMeasure N)
      = ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) := by
  rw [← integral_paperCompensator (N := N) (p := p) hp1 hp2 m n i j]
  exact integral_congr_ae (condExp_HpotInc_eq_paperBracket (N := N) (p := p) hp1 hp2 m n hij).symm

/-- **The sharp global bound in bracket form**: `paperWeight ≤ᵐ paperBracket`. -/
theorem paperWeight_le_paperBracket {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (hm : 2 ≤ m) {i j : Fin N} (hij : i ≠ j) :
    paperWeight p m n i j ≤ᵐ[arrayMeasure N] paperBracket p m n i j :=
  Filter.EventuallyLE.trans_eq (paperWeight_le_paperCompensator (N := N) (p := p) hp1 hp2 hm hij)
    (condExp_HpotInc_eq_paperBracket (N := N) (p := p) hp1 hp2 m n hij)

/-- **The paper residual**: the increment minus the projected bracket. -/
noncomputable def paperResidual (p : ℝ) (m n : ℕ) (i j : Fin N) : Array N → ℝ :=
  fun U => HpotInc p m n i j U - paperBracket p m n i j U

/-- **The one-step ledger, exactly**: increment = bracket + residual. -/
theorem HpotInc_eq_paperBracket_add_paperResidual (p : ℝ) (m n : ℕ) (i j : Fin N) (U : Array N) :
    HpotInc p m n i j U
      = paperBracket p m n i j U + paperResidual p m n i j U := by
  simp only [paperResidual]
  ring

/-- The residual is integrable. -/
theorem integrable_paperResidual {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) : Integrable (paperResidual p m n i j) (arrayMeasure N) := by
  have hpne : p ≠ 0 := by linarith
  exact (integrable_HpotInc hp1 hp2 hpne m n i j).sub
    (integrable_paperBracket (N := N) (p := p) hp1 hp2 m n hij)

/-- **The exact projection of the residual**: the projection defect of the bracket.  No
adaptedness is assumed; this is an identity. -/
theorem condExp_paperResidual_eq {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    condExp (enlFilt p m n) (arrayMeasure N) (paperResidual p m n i j)
      =ᵐ[arrayMeasure N] (fun U => paperBracket p m n i j U
        - condExp (enlFilt p m n) (arrayMeasure N) (paperBracket p m n i j) U) := by
  have hpne : p ≠ 0 := by linarith
  have hinc : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hbr : Integrable (paperBracket p m n i j) (arrayMeasure N) :=
    integrable_paperBracket (N := N) (p := p) hp1 hp2 m n hij
  have hsub : condExp (enlFilt p m n) (arrayMeasure N) (paperResidual p m n i j)
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N) (HpotInc p m n i j)
        - condExp (enlFilt p m n) (arrayMeasure N) (paperBracket p m n i j) := by
    have hrw : paperResidual p m n i j = HpotInc p m n i j - paperBracket p m n i j := rfl
    rw [hrw]
    exact condExp_sub hinc hbr (enlFilt p m n)
  refine Filter.EventuallyEq.trans hsub ?_
  exact (condExp_HpotInc_eq_paperBracket (N := N) (p := p) hp1 hp2 m n hij).sub
    (Filter.EventuallyEq.refl _ _)

/-- **The residual is centred, given the bracket's adaptedness as an explicit premise.**  This is
the adaptedness gap stated honestly: it is not proved here for the model's bracket, and it is not
assumed silently. -/
theorem condExp_paperResidual_eq_zero_of_stronglyMeasurable {p : ℝ} (hp1 : (1 : ℝ) / 2 < p)
    (hp2 : p < 1) (m n : ℕ) {i j : Fin N} (hij : i ≠ j)
    (hbr : StronglyMeasurable[enlFilt p m n] (paperBracket p m n i j)) :
    condExp (enlFilt p m n) (arrayMeasure N) (paperResidual p m n i j) =ᵐ[arrayMeasure N] 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  haveI : SigmaFinite ((arrayMeasure N).trim hle) := inferInstance
  have hfix : condExp (enlFilt p m n) (arrayMeasure N) (paperBracket p m n i j)
      =ᵐ[arrayMeasure N] paperBracket p m n i j :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hle hbr
      (integrable_paperBracket (N := N) (p := p) hp1 hp2 m n hij))
  refine Filter.EventuallyEq.trans (condExp_paperResidual_eq (N := N) (p := p) hp1 hp2 m n hij) ?_
  filter_upwards [hfix] with U hU
  rw [hU, sub_self]
  rfl

/-- **The residual has zero total integral**, unconditionally. -/
theorem integral_paperResidual_eq_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m n : ℕ) {i j : Fin N} (hij : i ≠ j) :
    ∫ U, paperResidual p m n i j U ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hpne : p ≠ 0 := by linarith
  have hinc : Integrable (HpotInc p m n i j) (arrayMeasure N) :=
    integrable_HpotInc hp1 hp2 hpne m n i j
  have hbr : Integrable (paperBracket p m n i j) (arrayMeasure N) :=
    integrable_paperBracket (N := N) (p := p) hp1 hp2 m n hij
  have hbrint : ∫ U, paperBracket p m n i j U ∂(arrayMeasure N)
      = ∫ U, HpotInc p m n i j U ∂(arrayMeasure N) :=
    integral_paperBracket (N := N) (p := p) hp1 hp2 m n hij
  have hfun : paperResidual p m n i j
      = fun U => HpotInc p m n i j U - paperBracket p m n i j U := rfl
  rw [hfun, integral_sub hinc hbr, hbrint, sub_self]

/-- **The finite-horizon compensation ledger, exact algebra**:
`Σ residual = Σ increment - Σ bracket` pointwise. -/
theorem sum_range_paperResidual_eq (p : ℝ) (m : ℕ) (i j : Fin N) (T : ℕ) (U : Array N) :
    ∑ k ∈ Finset.range T, paperResidual p m k i j U
      = (∑ k ∈ Finset.range T, HpotInc p m k i j U)
        - ∑ k ∈ Finset.range T, paperBracket p m k i j U := by
  simp only [paperResidual, Finset.sum_sub_distrib]

/-- **The time-summed residual has zero total integral** over any finite horizon. -/
theorem integral_sum_range_paperResidual_eq_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {i j : Fin N} (hij : i ≠ j) (T : ℕ) :
    ∫ U, (∑ k ∈ Finset.range T, paperResidual p m k i j U) ∂(arrayMeasure N) = 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  rw [integral_finsetSum _ (fun k _ =>
    integrable_paperResidual (N := N) (p := p) hp1 hp2 m k hij)]
  exact Finset.sum_eq_zero fun k _ =>
    integral_paperResidual_eq_zero (N := N) (p := p) hp1 hp2 m k hij

/-- **The compensator aggregated over a finite horizon is adapted at the horizon**: the sum of the
one-step `enlFilt n`-compensators, `n < T`, is `enlFilt T`-strongly-measurable (nestedness of the
enlarged filtration). -/
theorem stronglyMeasurable_sum_range_paperCompensator (p : ℝ) (m : ℕ) (i j : Fin N) (T : ℕ) :
    StronglyMeasurable[enlFilt p m T]
      (∑ n ∈ Finset.range T, paperCompensator p m n i j) :=
  Finset.stronglyMeasurable_sum _ fun n hn =>
    StronglyMeasurable.mono (stronglyMeasurable_paperCompensator p m n i j)
      (Filtration.mono (enlFilt p m) (Nat.le_of_lt (Finset.mem_range.mp hn)))

/-! ### 12. Instantiation check

`N = 2`, `p = 3/4`, `m = 2`, `n = 1`, distinct walkers: every constant of §6 and §10
instantiates, with `n = 1` giving the below row, the record row `A_0` and the single above row
`g = 1`. -/

example (i j : Fin 2) (hij : i ≠ j) :
    paperWeight (3 / 4) 2 1 i j
      ≤ᵐ[arrayMeasure 2] condExp (enlFilt (3 / 4) 2 1) (arrayMeasure 2)
        (HpotInc (3 / 4) 2 1 i j) :=
  paperWeight_le_condExp_discharged (p := 3 / 4) (by norm_num) (by norm_num)
    (m := 2) (n := 1) (by norm_num) hij

example (i j : Fin 2) (hij : i ≠ j) :
    (fun U => ∑ n ∈ Finset.range 2, paperWeight (3 / 4) 2 n i j U)
      ≤ᵐ[arrayMeasure 2] (fun U => ∑ n ∈ Finset.range 2,
        condExp (enlFilt (3 / 4) 2 n) (arrayMeasure 2) (HpotInc (3 / 4) 2 n i j) U) :=
  sum_range_paperWeight_le_sum_condExp (p := 3 / 4) (by norm_num) (by norm_num)
    (m := 2) (by norm_num) hij 2

/-! ### 13. Axiom audit -/


