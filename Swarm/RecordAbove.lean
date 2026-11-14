/-
  **Direction C — above-record conditional-mean algebra for the actual random record.**

  The integrated module `Swarm/EnlProjection.lean` proves, for the actual trajectory
  `Swarming.Trajectory.trajectory` and the actual `arrayMeasure N`,

      `E[h_j(M_n^j + g) | enlFilt n] =ᵐ Φ^g (E[h_j(M_n^j) | enlFilt n])`,

  where `Φ(h) = 1 + a (1 + h)` and the seed is a genuine conditional mean.  This file

  * defines the paper's random record sequence `e_g`, as that conditional mean;
  * proves the paper's `(projh)` closed form `e_g = L + a^g (e_0 - L)`, `L = (1+a)/(1-a)`;
  * proves `e_g >= 1` (hence `e_g >= 0`) for every `g`;
  * defines the paper's `b_n = h_j(M_n^j - 1) + 2` from the actual site marks and proves
    `e_0 <= E[b_n | enlFilt]` **unconditionally**, and `e_0 <= b_n` given the below-record
    `enlFilt`-measurability of `h_j(M_n^j - 1)` (the single missing information statement,
    named explicitly, not claimed here);
  * proves the paper's above-record drift inequality
    `-b a^{g} <= α e_g - (1-α) e_{g-1}` for `m >= 2` and `α >= 1/2`, and the sharper form
    `α e_{g} - (1-α) e_{g-1} >= ((1-a) a^{g-1}/2) (L - e_0)`.

  Nothing here sums the drift, constructs `Q`, or claims a regeneration/occupation theorem.
-/
import Swarm.EnlProjection
import Swarm.Zdrift

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The actual random record sequence `e_g` -/

/-- The paper's above-record conditional mean at a random record:
`e_g = Φ^g (E[h_j(M_n^j) | F_n])` where `F_n = enlFilt p m n` and `Φ(h) = 1 + a (1 + h)`.

The seed `e_0` is the conditional mean of the full-history potential `h_j(M_n^j)`, **not** the
possibly unread record value `h_j(M_n^j)` itself and **not** a restart seed: by
`condExp_hof_record_enlFilt`, `e_g` is the conditional mean of `h_j(M_n^j + g)`. -/
noncomputable def eRec (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) : ℝ :=
  phiIter (aRec p m) g (condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j) U)

/-- The seed: `e_0` is exactly the `enlFilt`-conditional mean of `h_j(M_n^j)`. -/
theorem eRec_zero (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) :
    eRec p m n j 0 U
      = condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j) U := rfl

/-- The one-step recursion `e_{g+1} = 1 + a (1 + e_g)`, pointwise. -/
theorem eRec_succ (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    eRec p m n j (g + 1) U = 1 + aRec p m * (1 + eRec p m n j g U) := rfl

/-- **`e_g` is the actual conditional mean of the full-history potential** `h_j(M_n^j + g)`
given the paper's enlarged filtration.  This is the integrated
`condExp_hof_record_enlFilt`, read through the definition of `eRec`. -/
theorem eRec_eq_condExp {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (g : ℕ) :
    eRec p m n j g =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
      (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((recVal j (prefOf p m n U)).toNat + g)) :=
  (condExp_hof_record_enlFilt hp1 hp2 m j g).symm

/-! ### The paper's `(projh)` closed form -/

/-- **`(projh)`**: `e_g = L + a^g (e_0 - L)` with `L = (1+a)/(1-a)`, for the actual random
record, pointwise on the array. -/
theorem eRec_closed_form (p : ℝ) (m n : ℕ) (j : Fin N) (ha : aRec p m ≠ 1) (g : ℕ)
    (U : Array N) :
    eRec p m n j g U
      = (1 + aRec p m) / (1 - aRec p m)
        + aRec p m ^ g * (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m)) := by
  refine SwarmOcc.proj_closed_form ha (fun g => eRec p m n j g U) (fun g => ?_) g
  rw [eRec_succ]
  ring

/-- The **increment form** of `(projh)`: `e_{g+1} - e_g = (1-a) a^g (L - e_0)`. -/
theorem eRec_step_sub (p : ℝ) (m n : ℕ) (j : Fin N) (ha : aRec p m ≠ 1) (g : ℕ)
    (U : Array N) :
    eRec p m n j (g + 1) U - eRec p m n j g U
      = (1 - aRec p m) * aRec p m ^ g
        * ((1 + aRec p m) / (1 - aRec p m) - eRec p m n j 0 U) := by
  refine SwarmOcc.proj_step_sub ha (fun g => eRec p m n j g U) (fun g => ?_) g
  rw [eRec_succ]
  ring

/-- **`(projH)` summed at the random record**: the partial sums of the projected sequence,
`sum_{j<g} e_j = g L + (e_0 - L)(1-a^g)/(1-a)`. -/
theorem eRec_partial_sum (p : ℝ) (m n : ℕ) (j : Fin N) (ha : aRec p m ≠ 1) (g : ℕ)
    (U : Array N) :
    ∑ k ∈ Finset.range g, eRec p m n j k U
      = g * ((1 + aRec p m) / (1 - aRec p m))
        + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
          * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  refine SwarmOcc.proj_partial_sum ha (fun g => eRec p m n j g U) (fun g => ?_) g
  rw [eRec_succ]
  ring

/-! ### Deterministic bounds on the multiplier `a` -/

/-- `a >= 0` for every `m` (the paper's `a >= 1 - (1-p)^{m-1}`). -/
theorem zero_le_aRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    0 ≤ aRec p m := by
  have h := one_sub_le_aRec hp1 hp2 m
  have hq : (1 - p) ^ (m - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  linarith

/-- **`1/2 < a < 1` for `m >= 2`** (the paper's remark before `(projh)`). -/
theorem aRec_bounds {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    1 / 2 < aRec p m ∧ aRec p m < 1 := by
  have hq0 : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hb := ExcitedEnv.aConst_bounds hp1 hp2 hq0 (ExcitedEnv.q_le_half hp1 hp2 hm)
  exact ⟨hb.1, hb.2.1⟩

/-! ### Positivity of the projected sequence -/

/-- **`1 <= e_0`**: the seed is a conditional mean of a potential whose pointwise value is at
least one. -/
theorem one_le_eRec_zero {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) :
    1 ≤ᵐ[arrayMeasure N] eRec p m n j 0 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : (fun _ : Array N => (1 : ℝ)) ≤ᵐ[arrayMeasure N] H0 p m n j :=
    Filter.Eventually.of_forall fun U =>
      SwarmMarks.one_le_hof hp1.le hp2 (SwarmLogRatio.siteMarks p m U j)
        (recVal j (prefOf p m n U)).toNat
  have hmono := condExp_mono (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := fun _ : Array N => (1 : ℝ)) (g := H0 p m n j)
    (integrable_const 1) ((recSeed_hypotheses_complete hp1 hp2 m n j).2.1) hle
  have hc : condExp (enlFilt p m n) (arrayMeasure N) (fun _ : Array N => (1 : ℝ))
      = fun _ => 1 :=
    condExp_const (μ := arrayMeasure N) (m := enlFilt p m n) ((enlFilt p m).le n) (1 : ℝ)
  rw [hc] at hmono
  filter_upwards [hmono] with U hU
  simpa only [Pi.one_apply, eRec_zero] using hU

/-- **`1 <= e_g` for every `g`**, hence `0 <= e_g`. -/
theorem one_le_eRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (g : ℕ) :
    1 ≤ᵐ[arrayMeasure N] eRec p m n j g := by
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  induction g with
  | zero => simpa only [eRec_zero] using one_le_eRec_zero hp1 hp2 m (n := n) j
  | succ k ih =>
      filter_upwards [ih] with U hU
      rw [eRec_succ]
      simp only [Pi.one_apply] at hU ⊢
      nlinarith

/-- **`0 <= e_g` for every `g`.** -/
theorem zero_le_eRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (g : ℕ) :
    0 ≤ᵐ[arrayMeasure N] eRec p m n j g :=
  (one_le_eRec hp1 hp2 m j g).mono fun U hU => le_trans zero_le_one hU


/-! ### The paper's `b_n = h_j(M_n^j - 1) + 2` from the actual site marks -/

/-- `h_j(M_n^j - 1)` for the actual site marks, with the paper's boundary value `h_j(-1) = 1`
(so at record `0` this is `1`, not `h_j(0)`). -/
noncomputable def HprevAt (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) : ℝ :=
  if (recVal j (prefOf p m n U)).toNat = 0 then 1
  else SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
    ((recVal j (prefOf p m n U)).toNat - 1)

/-- The paper's `b_n = h_j(M_n^j - 1) + 2`. -/
noncomputable def bRec (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) : ℝ :=
  HprevAt p m n j U + 2

theorem HprevAt_of_zero (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N)
    (h : (recVal j (prefOf p m n U)).toNat = 0) :
    HprevAt p m n j U = 1 := by
  rw [HprevAt, if_pos h]

theorem HprevAt_of_succ (p : ℝ) (m n : ℕ) (j : Fin N) (U : Array N) (k : ℕ)
    (h : (recVal j (prefOf p m n U)).toNat = k + 1) :
    HprevAt p m n j U = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k := by
  rw [HprevAt, if_neg (by omega), h]
  simp

/-- `1 <= h_j(M_n^j - 1)`: both branches are at least one. -/
theorem one_le_HprevAt {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : 1 ≤ HprevAt p m n j U := by
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m n U)).toNat) with h0 | hpos
  · rw [HprevAt_of_zero p m n j U h0]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m n U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m n j U k hk]
    exact SwarmMarks.one_le_hof hp1.le hp2 (SwarmLogRatio.siteMarks p m U j) k

/-- **`h_j(M) <= h_j(M-1) + 2`** for the actual site marks and the actual record, including the
record-`0` boundary case.  This is the paper's "both branches of `(hrec)` give
`1 <= h_j(x) <= h_j(x-1) + 2`" at the random record. -/
theorem H0_le_HprevAt_add_two {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (U : Array N) : H0 p m n j U ≤ HprevAt p m n j U + 2 := by
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m n U)).toNat) with h0 | hpos
  · rw [HprevAt_of_zero p m n j U h0, H0_def, h0]
    have h3 := SwarmMarks.hof_zero_le_three hp1.le hp2 (SwarmLogRatio.siteMarks p m U j)
    linarith
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m n U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m n j U k hk, H0_def, hk, SwarmMarks.hof_succ]
    have h1 : 1 ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k :=
      SwarmMarks.one_le_hof hp1.le hp2 (SwarmLogRatio.siteMarks p m U j) k
    have h2 := SwarmMarks.hstep_le_add_two (p := p) hp1.le hp2
      (b := SwarmLogRatio.siteMarks p m U j (k + 1))
      (h := SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) h1
    linarith

/-- The deterministic bound `|h_j(M_n^j - 1)| <= 2n + 3`. -/
theorem abs_HprevAt_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : |HprevAt p m n j U| ≤ 2 * (n : ℝ) + 3 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos ((recVal j (prefOf p m n U)).toNat) with h0 | hpos
  · rw [HprevAt_of_zero p m n j U h0, abs_one]
    linarith
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (recVal j (prefOf p m n U)).toNat ≠ 0)
    rw [HprevAt_of_succ p m n j U k hk]
    have hb := SwarmShiftMarks.abs_hof_le' hp1 hp2 (by linarith) (SwarmLogRatio.siteMarks p m U j) k
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      have := toNat_recVal_prefOf_le p m U j n
      rw [hk] at this
      exact_mod_cast Nat.le_of_succ_le this
    linarith

/-! ### Ambient measurability and integrability of `h_j(M_n^j - 1)` -/

/-- The mark sequence of walker `j` is an ambient measurable function into `ℕ → Bool`. -/
theorem measurable_siteMarks (p : ℝ) (m : ℕ) (j : Fin N) :
    Measurable fun U : Array N => SwarmLogRatio.siteMarks p m U j := by
  classical
  refine measurable_pi_iff.mpr fun x => ?_
  refine measurable_to_bool ?_
  have hset : {U : Array N | SwarmLogRatio.siteMarks p m U j x = true}
      = {U : Array N | SiteMark p m U j (x : ℤ)} := by
    ext U
    simp only [Set.mem_ofPred_eq, SwarmLogRatio.siteMarks]
    exact decide_eq_true_iff
  rw [hset]
  exact measurableSet_siteMark_array p m j (x : ℤ)

/-- `h_j(k)` at a fixed site `k` is ambient measurable, as a function of the actual site marks. -/
theorem measurable_hof_siteMarks (p : ℝ) (m : ℕ) (j : Fin N) (k : ℕ) :
    Measurable fun U : Array N =>
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k :=
  (measurable_hof_any p k).comp (measurable_siteMarks p m j)

/-- `h_j(M_n^j - 1)` is ambient measurable: on the record fibre `{M_n^j = y}` it is the
fixed-index potential, and the fibres are measurable. -/
theorem measurable_HprevAt (p : ℝ) (m n : ℕ) (j : Fin N) :
    Measurable (HprevAt p m n j) := by
  classical
  have hU : ∀ y : ℤ, Measurable fun U : Array N =>
      if y.toNat = 0 then (1 : ℝ)
      else SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (y.toNat - 1) := by
    intro y
    by_cases hy : y.toNat = 0
    · simpa [hy] using
        (measurable_const (a := (1 : ℝ)) : Measurable fun _ : Array N => (1 : ℝ))
    · simpa [hy] using measurable_hof_siteMarks p m j (y.toNat - 1)
  have hpiece := SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℤ)
    (U := fun y : ℤ => fun U : Array N =>
      if y.toNat = 0 then (1 : ℝ)
      else SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (y.toNat - 1))
    hU (fun U => recVal j (prefOf p m n U))
    (fun y => measurableSet_recVal_eq_ambient p m n j y)
  have hfun : (fun U : Array N =>
      (fun y : ℤ => fun U' : Array N =>
        if y.toNat = 0 then (1 : ℝ)
        else SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U' j) (y.toNat - 1))
        (recVal j (prefOf p m n U)) U) = HprevAt p m n j := rfl
  rw [← hfun]
  exact hpiece

/-- `h_j(M_n^j - 1)` is integrable for the actual array measure. -/
theorem integrable_HprevAt {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) : Integrable (HprevAt p m n j) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound (measurable_HprevAt p m n j).aestronglyMeasurable (2 * (n : ℝ) + 3)
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_HprevAt_le hp1 hp2 m n j U

/-! ### The seed upper bound -/

/-- The conditional mean of a function plus a constant, in the form used below. -/
theorem condExp_add_const {p : ℝ} (m n : ℕ) {f : Array N → ℝ}
    (hint : Integrable f (arrayMeasure N)) (c : ℝ) :
    condExp (enlFilt p m n) (arrayMeasure N) (f + fun _ : Array N => c)
      =ᵐ[arrayMeasure N] (condExp (enlFilt p m n) (arrayMeasure N) f + fun _ => c) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hc : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have h1 := condExp_add (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := f) (g := fun _ : Array N => c) hint (integrable_const c)
  have hc' := condExp_const (μ := arrayMeasure N) (m := enlFilt p m n) hc c
  refine h1.trans ?_
  filter_upwards [Filter.EventuallyEq.of_eq hc'] with U hcU
  simp only [Pi.add_apply, hcU]

/-- **`e_0 <= E[h_j(M_n^j - 1) + 2 | F_n]`**, unconditionally: the conditional mean of
`h_j(M_n^j)` is at most the conditional mean of the pointwise upper bound
`h_j(M_n^j - 1) + 2`.  No below-record measurability is used here. -/
theorem eRec_zero_le_condExp_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) :
    eRec p m n j 0 ≤ᵐ[arrayMeasure N] fun U =>
      condExp (enlFilt p m n) (arrayMeasure N) (HprevAt p m n j) U + 2 := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hint0 : Integrable (H0 p m n j) (arrayMeasure N) :=
    (recSeed_hypotheses_complete hp1 hp2 m n j).2.1
  have hint : Integrable (bRec p m n j) (arrayMeasure N) :=
    (integrable_HprevAt hp1 hp2 m n j).add (integrable_const 2)
  have hmono := condExp_mono (μ := arrayMeasure N) (m := enlFilt p m n)
    (f := H0 p m n j) (g := bRec p m n j) hint0 hint
    (Filter.Eventually.of_forall fun U => H0_le_HprevAt_add_two hp1 hp2 m n j U)
  have hadd := condExp_add_const (p := p) m n (f := HprevAt p m n j)
    (integrable_HprevAt hp1 hp2 m n j) 2
  have key : condExp (enlFilt p m n) (arrayMeasure N) (H0 p m n j)
      ≤ᵐ[arrayMeasure N] fun U =>
        condExp (enlFilt p m n) (arrayMeasure N) (HprevAt p m n j) U + 2 :=
    hmono.trans_eq hadd
  exact key

/-- **`e_0 <= b_n`** (the paper's `E[h_j(r_n) | F_n] <= h_j(r_n-1) + 2`), given the one missing
information statement: `h_j(M_n^j - 1)` must be `F_n = enlFilt p m n`-measurable.  That
below-record measurability is **not** proved here (it is the direction-A target); it is the
explicit hypothesis `hmeas`. -/
theorem eRec_zero_le_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (hmeas : Measurable[enlFilt p m n] (HprevAt p m n j)) :
    eRec p m n j 0 ≤ᵐ[arrayMeasure N] bRec p m n j := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hle : enlFilt p m n ≤ (inferInstance : MeasurableSpace (Array N)) := (enlFilt p m).le n
  have hconst : condExp (enlFilt p m n) (arrayMeasure N) (HprevAt p m n j)
      = HprevAt p m n j :=
    condExp_of_stronglyMeasurable (μ := arrayMeasure N) (m := enlFilt p m n) hle
      hmeas.stronglyMeasurable (integrable_HprevAt hp1 hp2 m n j)
  have hkey := eRec_zero_le_condExp_bRec hp1 hp2 m (n := n) j
  rw [hconst] at hkey
  exact hkey

/-- The two seed bounds together: `1 <= e_0 <= b_n`, the second under the same scoped
measurability input. -/
theorem eRec_zero_bounds {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (hmeas : Measurable[enlFilt p m n] (HprevAt p m n j)) :
    (1 ≤ᵐ[arrayMeasure N] eRec p m n j 0) ∧
      (eRec p m n j 0 ≤ᵐ[arrayMeasure N] bRec p m n j) :=
  ⟨one_le_eRec_zero hp1 hp2 m j, eRec_zero_le_bRec hp1 hp2 m (n := n) j hmeas⟩

/-- `b_n >= 0` (indeed `b_n >= 3`). -/
theorem three_le_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (U : Array N) : 3 ≤ bRec p m n j U := by
  have := one_le_HprevAt hp1 hp2 m n j U
  simp only [bRec]
  linarith


/-! ### `a < 1` for every `m`, and `a > 1/2` for `m >= 2` -/

theorem aRec_lt_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    aRec p m < 1 := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have h2p : 0 < 2 * p - 1 := by linarith
  have hpos : 0 < (2 * p - 1) * (1 - p) ^ (m - 1) / p := div_pos (mul_pos h2p hq) hp0
  unfold aRec ExcitedEnv.aConst
  linarith

theorem aRec_ne_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    aRec p m ≠ 1 :=
  ne_of_lt (aRec_lt_one hp1 hp2 m)

/-! ### The above-record drift inequalities -/

/-- **The paper's sharper above-record bound.**  For `α >= 1/2` and every `g`,

    `α e_{g+1} - (1-α) e_g >= ((1-a) a^g / 2) (L - e_0)`,

  `L = (1+a)/(1-a)`.  This is the paper's display
  `≥ ((1-a)a^{g-1}/2) ((1+a)/(1-a) - E[h_j(r_n) | F_n])` at `g = k+1`; unlike the coarser
  `-b_n a^{g+1}` bound it does not use `a >= 1/3`. -/
theorem eRec_drift_ge {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℕ) :
    (fun U => ((1 - aRec p m) * aRec p m ^ g / 2)
        * ((1 + aRec p m) / (1 - aRec p m) - eRec p m n j 0 U))
      ≤ᵐ[arrayMeasure N]
        fun U => α * eRec p m n j (g + 1) U - (1 - α) * eRec p m n j g U := by
  have hane : aRec p m ≠ 1 := aRec_ne_one hp1 hp2 m
  filter_upwards [one_le_eRec hp1 hp2 m (n := n) j (g + 1), one_le_eRec hp1 hp2 m (n := n) j g]
    with U h1 h2
  simp only [Pi.one_apply] at h1 h2
  have hstep := eRec_step_sub p m n j hane g U
  have hsplit : α * eRec p m n j (g + 1) U - (1 - α) * eRec p m n j g U
      = (1 / 2) * (eRec p m n j (g + 1) U - eRec p m n j g U)
        + (α - 1 / 2) * (eRec p m n j (g + 1) U + eRec p m n j g U) := by
    ring
  have hnn : 0 ≤ (α - 1 / 2) * (eRec p m n j (g + 1) U + eRec p m n j g U) := by
    have : (0 : ℝ) ≤ α - 1 / 2 := by linarith
    have : 0 ≤ eRec p m n j (g + 1) U + eRec p m n j g U := by linarith
    exact mul_nonneg ‹(0 : ℝ) ≤ α - 1 / 2› this
  rw [hsplit, hstep]
  linarith

/-- **The above-record drift bound `(Zloss)` above the record, `m >= 2`**, for a random `b`
with `0 <= b` and `e_0 <= b` almost surely: for every `k`,

    `-b a^{k+1} <= α e_{k+1} - (1-α) e_k`.

  This is `SwarmOcc.zdrift_above` instantiated at the actual random-record sequence. -/
theorem eRec_zdrift_above {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (hm : 2 ≤ m) {α : ℝ} (hα : 1 / 2 ≤ α) {b : Array N → ℝ}
    (hb : 0 ≤ᵐ[arrayMeasure N] b) (he0 : eRec p m n j 0 ≤ᵐ[arrayMeasure N] b) (k : ℕ) :
    (-b * fun _ : Array N => aRec p m ^ (k + 1))
      ≤ᵐ[arrayMeasure N]
        fun U => α * eRec p m n j (k + 1) U - (1 - α) * eRec p m n j k U := by
  have hab := aRec_bounds hp1 hp2 hm
  have ha0 : 0 ≤ aRec p m := zero_le_aRec hp1 hp2 m
  have ha1 : aRec p m < 1 := hab.2
  have ha13 : 1 / 3 ≤ aRec p m := by linarith [hab.1]
  have hne : ∀ᵐ U ∂(arrayMeasure N), ∀ g : ℕ, 0 ≤ eRec p m n j g U :=
    MeasureTheory.ae_all_iff.mpr (fun g => zero_le_eRec hp1 hp2 m j g)
  filter_upwards [hb, he0, hne] with U hbU he0U hneU
  exact SwarmOcc.zdrift_above ha0 ha1 ha13 hbU hα (fun g => eRec p m n j g U)
    (fun g => by rw [eRec_succ]; ring) he0U (fun g => hneU g) k

/-- **The above-record drift bound with the paper's `b_n = h_j(M_n^j - 1) + 2`.**
The only input beyond `m >= 2` and `α >= 1/2` is the below-record `enlFilt`-measurability of
`h_j(M_n^j - 1)` (`hmeas`), which is not proved here. -/
theorem zdrift_above_eRec_bRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (hm : 2 ≤ m)
    (hmeas : Measurable[enlFilt p m n] (HprevAt p m n j)) {α : ℝ} (hα : 1 / 2 ≤ α) (k : ℕ) :
    (-bRec p m n j * fun _ : Array N => aRec p m ^ (k + 1))
      ≤ᵐ[arrayMeasure N]
        fun U => α * eRec p m n j (k + 1) U - (1 - α) * eRec p m n j k U := by
  have hb : (0 : Array N → ℝ) ≤ᵐ[arrayMeasure N] bRec p m n j :=
    Filter.Eventually.of_forall fun U => by
      have h := three_le_bRec hp1 hp2 m n j U
      have h' : (0 : ℝ) ≤ bRec p m n j U := by linarith
      simpa only [Pi.zero_apply] using h'
  exact eRec_zdrift_above hp1 hp2 m (n := n) j hm hα hb
    (eRec_zero_le_bRec hp1 hp2 m (n := n) j hmeas) k

/-! ### The projected cumulative potential above the record -/

theorem measurable_hof_siteMarks_add (p : ℝ) (m n : ℕ) (j : Fin N) (k : ℕ) :
    Measurable fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat + k) := by
  classical
  have hU : ∀ y : ℤ, Measurable fun U : Array N =>
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (y.toNat + k) :=
    fun y => measurable_hof_siteMarks p m j _
  have hpiece := SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℤ)
    (U := fun y : ℤ => fun U : Array N =>
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) (y.toNat + k))
    hU (fun U => recVal j (prefOf p m n U))
    (fun y => measurableSet_recVal_eq_ambient p m n j y)
  exact hpiece

/-- The potential at the shifted site `M_n^j + k` is integrable, from the deterministic bound
`|h_j(M+k)| <= 2(M+k) + 3 <= 2(n+k) + 3`. -/
theorem integrable_hof_siteMarks_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (k : ℕ) :
    Integrable (fun U : Array N => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat + k)) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound (measurable_hof_siteMarks_add p m n j k).aestronglyMeasurable
    (2 * ((n : ℝ) + (k : ℝ)) + 3) (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  have hb := SwarmShiftMarks.abs_hof_le' hp1 hp2 (by linarith)
    (SwarmLogRatio.siteMarks p m U j) ((recVal j (prefOf p m n U)).toNat + k)
  have hkn : (((recVal j (prefOf p m n U)).toNat + k : ℕ) : ℝ) ≤ (n : ℝ) + (k : ℝ) := by
    have h1 : (recVal j (prefOf p m n U)).toNat ≤ n := toNat_recVal_prefOf_le p m U j n
    have h2 : (((recVal j (prefOf p m n U)).toNat + k : ℕ) : ℝ)
        = ((recVal j (prefOf p m n U)).toNat : ℝ) + (k : ℝ) := by push_cast; ring
    have h3 : ((recVal j (prefOf p m n U)).toNat : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    rw [h2]
    linarith
  linarith

/-- **The conditional mean of the above-record potential block.**  For the actual trajectory and
the actual `arrayMeasure N`, the `enlFilt`-conditional mean of
`sum_{k<g} h_j(M_n^j + k)` is the sum of the projected terms `e_k`. -/
theorem condExp_sum_hof_record {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (g : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + k))
      =ᵐ[arrayMeasure N] fun U => ∑ k ∈ Finset.range g, eRec p m n j k U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hsum := condExp_finsetSum (μ := arrayMeasure N)
    (s := Finset.range g)
    (f := fun k (U : Array N) => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
      ((recVal j (prefOf p m n U)).toNat + k))
    (fun k _ => integrable_hof_siteMarks_add hp1 hp2 m n j k) (enlFilt p m n)
  have hL : (fun U : Array N => ∑ k ∈ Finset.range g,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + k))
      = (∑ k ∈ Finset.range g, fun U : Array N =>
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + k)) := by
    funext U
    rw [Finset.sum_apply]
  rw [hL]
  refine hsum.trans ?_
  have hall : ∀ᵐ U ∂(arrayMeasure N), ∀ k : ℕ,
      eRec p m n j k U
        = condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + k)) U :=
    MeasureTheory.ae_all_iff.mpr (fun k => eRec_eq_condExp hp1 hp2 m (n := n) j k)
  filter_upwards [hall] with U hU
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => (hU k).symm

/-- **`(projH)` above the record, for the actual model**: the conditional mean of the
above-record block of the cumulative potential is

    `g L + (e_0 - L) (1 - a^g)/(1-a)`,   `L = (1+a)/(1-a)`.

Together with `Hpot_add_nat` this is exactly the paper's `(projH)` minus its replacement of
`E[H_j(r_n) | F_n]` by the unread value `H_j(r_n)` — that last identification is precisely the
below-record measurability statement, not claimed here. -/
theorem condExp_sum_hof_record_closed {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
          ((recVal j (prefOf p m n U)).toNat + k))
      =ᵐ[arrayMeasure N] fun U =>
        (g : ℝ) * ((1 + aRec p m) / (1 - aRec p m))
          + (eRec p m n j 0 U - (1 + aRec p m) / (1 - aRec p m))
            * ((1 - aRec p m ^ g) / (1 - aRec p m)) := by
  refine (condExp_sum_hof_record hp1 hp2 m (n := n) j g).trans ?_
  filter_upwards with U
  exact eRec_partial_sum p m n j (aRec_ne_one hp1 hp2 m) g U

/-! ### The cumulative potential `H^w` at the random record -/

/-- `H^w` at a fixed site `y`, driven by the actual site marks, is ambient measurable. -/
theorem measurable_Hpot_fixed (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) :
    Measurable fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u) y := by
  have heq : (fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u) y)
      = fun U => if y ≤ 0 then (y : ℝ)
        else ∑ u ∈ Finset.range y.toNat, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u :=
    rfl
  rw [heq]
  by_cases hy : y ≤ 0
  · simp only [if_pos hy]; exact measurable_const
  · simp only [if_neg hy]
    exact Finset.measurable_sum _ fun u _ => measurable_hof_siteMarks p m j u

/-- The cumulative potential at the actual record is ambient measurable. -/
theorem measurable_Hpot_record (p : ℝ) (m n : ℕ) (j : Fin N) :
    Measurable fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
        (recVal j (prefOf p m n U)) := by
  classical
  have hpiece := SwarmIID.measurable_of_countable_pieces (Ω := Array N) (ι := ℤ)
    (U := fun y : ℤ => fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u) y)
    (fun y => measurable_Hpot_fixed p m j y)
    (fun U => recVal j (prefOf p m n U))
    (fun y => measurableSet_recVal_eq_ambient p m n j y)
  exact hpiece

/-- The cumulative potential at the record is bounded by `n (2n+3)`. -/
theorem abs_Hpot_record_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) (U : Array N) :
    |SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
        (recVal j (prefOf p m n U))| ≤ (n : ℝ) * (2 * (n : ℝ) + 3) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hC : (0 : ℝ) ≤ 2 * (n : ℝ) + 3 := by linarith
  have hM0 := zero_le_recVal_prefOf p m U j n
  rcases lt_or_ge 0 (recVal j (prefOf p m n U)) with hpos | hnonpos
  · rw [SwarmOcc.Hpot, if_neg (by omega)]
    have hle : |∑ u ∈ Finset.range (recVal j (prefOf p m n U)).toNat,
        SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u|
        ≤ ∑ u ∈ Finset.range (recVal j (prefOf p m n U)).toNat, (2 * (n : ℝ) + 3) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      have hu' : u ≤ n := by
        have h1 : u < (recVal j (prefOf p m n U)).toNat := Finset.mem_range.mp hu
        have h2 := toNat_recVal_prefOf_le p m U j n
        omega
      have hb := SwarmShiftMarks.abs_hof_le' hp1 hp2 (by linarith)
        (SwarmLogRatio.siteMarks p m U j) u
      have h3 : (u : ℝ) ≤ (n : ℝ) := by exact_mod_cast hu'
      linarith
    have hsum : ∑ _u ∈ Finset.range (recVal j (prefOf p m n U)).toNat, (2 * (n : ℝ) + 3)
        = ((recVal j (prefOf p m n U)).toNat : ℝ) * (2 * (n : ℝ) + 3) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum] at hle
    have hMe : ((recVal j (prefOf p m n U)).toNat : ℝ) ≤ (n : ℝ) := by
      have h2 := toNat_recVal_prefOf_le p m U j n
      exact_mod_cast h2
    calc |∑ u ∈ Finset.range (recVal j (prefOf p m n U)).toNat,
          SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u|
        ≤ ((recVal j (prefOf p m n U)).toNat : ℝ) * (2 * (n : ℝ) + 3) := hle
      _ ≤ (n : ℝ) * (2 * (n : ℝ) + 3) := by
          exact mul_le_mul_of_nonneg_right hMe hC
  · have hz : recVal j (prefOf p m n U) = 0 := le_antisymm hnonpos hM0
    rw [hz, SwarmOcc.Hpot_of_nonpos le_rfl, Int.cast_zero, abs_zero]
    positivity

theorem integrable_Hpot_record {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ)
    (j : Fin N) :
    Integrable (fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
        (recVal j (prefOf p m n U))) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.of_bound (measurable_Hpot_record p m n j).aestronglyMeasurable
    ((n : ℝ) * (2 * (n : ℝ) + 3)) (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_Hpot_record_le hp1 hp2 m n j U

/-- **`H^w(M_n^j + g) = H^w(M_n^j) + sum_{k<g} h_j(M_n^j + k)`** for the actual potential. -/
theorem Hpot_record_add (p : ℝ) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
        (recVal j (prefOf p m n U) + (g : ℤ))
      = SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
          (recVal j (prefOf p m n U))
        + ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
            ((recVal j (prefOf p m n U)).toNat + k) := by
  have hM : (((recVal j (prefOf p m n U)).toNat : ℕ) : ℤ) = recVal j (prefOf p m n U) :=
    Int.toNat_of_nonneg (zero_le_recVal_prefOf p m U j n)
  have h := SwarmOcc.Hpot_add_nat
    (h := fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
    (recVal j (prefOf p m n U)).toNat g
  rw [hM] at h
  exact h

/-- **The cumulative projected potential at the record, decomposed.**  For the actual trajectory
and the actual `arrayMeasure N`,

    `E[H^w(M_n^j + g) | F_n] = E[H^w(M_n^j) | F_n] + sum_{k<g} e_k`

  almost surely.  This is the above-record part of the paper's `H_{j,n}(r_n + g)`: the first term
  is the projected value at the record, which the paper replaces by the actual `H_j(r_n)` using
  below-record measurability — that replacement is not claimed here. -/
theorem condExp_Hpot_record_add {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {n : ℕ} (j : Fin N) (g : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
          (recVal j (prefOf p m n U) + (g : ℤ)))
      =ᵐ[arrayMeasure N] fun U =>
        condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
            (recVal j (prefOf p m n U))) U
        + ∑ k ∈ Finset.range g, eRec p m n j k U := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hH : Integrable (fun U : Array N =>
      SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
        (recVal j (prefOf p m n U))) (arrayMeasure N) := integrable_Hpot_record hp1 hp2 m n j
  have hS : Integrable (fun U : Array N => ∑ k ∈ Finset.range g,
      SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
        ((recVal j (prefOf p m n U)).toNat + k)) (arrayMeasure N) := by
    refine (integrable_finsetSum' (Finset.range g) fun k _ =>
      integrable_hof_siteMarks_add hp1 hp2 m n j k).congr ?_
    filter_upwards with U
    simp only [Finset.sum_apply]
  calc condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
          (recVal j (prefOf p m n U) + (g : ℤ)))
      =ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
              (recVal j (prefOf p m n U))
            + ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
                ((recVal j (prefOf p m n U)).toNat + k)) :=
        condExp_congr_ae (Filter.Eventually.of_forall fun U => Hpot_record_add p m n j g U)
    _ =ᵐ[arrayMeasure N] (condExp (enlFilt p m n) (arrayMeasure N)
            (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
              (recVal j (prefOf p m n U)))
          + condExp (enlFilt p m n) (arrayMeasure N)
            (fun U => ∑ k ∈ Finset.range g, SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((recVal j (prefOf p m n U)).toNat + k))) := by
        have h := condExp_add (μ := arrayMeasure N) (m := enlFilt p m n)
          (f := fun U => SwarmOcc.Hpot
            (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
            (recVal j (prefOf p m n U)))
          (g := fun U => ∑ k ∈ Finset.range g,
            SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j)
              ((recVal j (prefOf p m n U)).toNat + k)) hH hS
        filter_upwards [h] with U hU
        exact hU
    _ =ᵐ[arrayMeasure N] fun U =>
        condExp (enlFilt p m n) (arrayMeasure N)
          (fun U => SwarmOcc.Hpot (fun u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u)
            (recVal j (prefOf p m n U))) U
        + ∑ k ∈ Finset.range g, eRec p m n j k U := by
        have h := condExp_sum_hof_record hp1 hp2 m (n := n) j g
        filter_upwards [h] with U hU
        simp only [Pi.add_apply, hU]


/-- **The record case of `(Zloss)` with the actual objects**, `x = r_n`: for `α >= 1/2`,

    `1 - b_n <= α e_0 - (1-α) h_j(M_n^j - 1)`.

  The only input is `1 <= e_0` (proved unconditionally) and `e_0 <= b_n` (which uses `hmeas`). -/
theorem zdrift_at_eRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) {n : ℕ}
    (j : Fin N) (hmeas : Measurable[enlFilt p m n] (HprevAt p m n j)) {α : ℝ}
    (hα : 1 / 2 ≤ α) :
    (fun U => 1 - bRec p m n j U)
      ≤ᵐ[arrayMeasure N] fun U => α * eRec p m n j 0 U - (1 - α) * HprevAt p m n j U := by
  filter_upwards [one_le_eRec_zero hp1 hp2 m (n := n) j,
    eRec_zero_le_bRec hp1 hp2 m (n := n) j hmeas] with U h1 hb
  simp only [Pi.one_apply] at h1
  have hprev : 0 ≤ HprevAt p m n j U := by
    have := one_le_HprevAt hp1 hp2 m n j U
    linarith
  have hsum : 0 ≤ eRec p m n j 0 U + HprevAt p m n j U := by linarith
  have hres := SwarmOcc.zdrift_at (α := α) (e := eRec p m n j 0 U)
    (hprev := HprevAt p m n j U) (b := HprevAt p m n j U + 2) hα h1 hsum hprev rfl
  simpa only [bRec] using hres


end Swarming.Enl
