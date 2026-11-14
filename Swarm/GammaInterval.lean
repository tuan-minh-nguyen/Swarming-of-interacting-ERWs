/-
  **The finite-interval, residue-class probability accounting of `(locsum)`.**

  `GammaTailExp.lean` proves a stopped count tail for one residue class of the group record:
  with `y_i = y0 + 2 m i`,

  `P(# {i < K : Γ_{y_i}} ≤ j) ≤ exp (-(K c - j)² / K)`,  `c = (1-p)^((2m-1)|A|)`,

  on finite records.  `GammaClass.lean` splits `[a0,b0]` into the `2m` residue classes
  (class `j` starts at `clsY0 a0 j = a0 + j`) and counts levels exactly.

  This file joins the two:

  * `gamma_class_tail` : for one class, the count of successful trials drops below
    `c * clsK - t` only with probability at most `exp (-t²/clsK)` — the deviation `t`
    is compared directly with `c * clsK` (no floor is introduced in the *bound*, only
    inside the probability estimate, where it can only help);
  * `gamma_interval_count_lower` : the union over the finitely many classes,
    `P(#{y ∈ [a0,b0] : Γ_y} < c (b0-a0+1) - 2 m t) ≤ 2 m · exp (-t²/K̄)` with
    `K̄ = ⌊L/2m⌋+1`, together with the exact complement statement: outside that
    event the count over the *whole* interval is at least `c (b0-a0+1) - 2 m t`;
  * `paper_deviation_exponent` : with the paper's deviation `t = 2 L^{3/4}` and
    `K̄ ≤ C_T L`, the exponent is exactly `4 √L / C_T`, i.e. of the form
    `c_T L^{1/2}`; and `two_mul_pow_three_quarters_sq` records `(2L^{3/4})² = 4L√L`.

  The optimisation range of `gamma_count_tail_exp_finite_records` follows from
  `c ≤ 1/2` (`gammaC_le_half`), so no extra size hypothesis is needed. The nonpositive
  threshold and empty-class cases are handled separately; `gamma_interval_count_lower_short`
  records the degenerate total threshold `c (b0-a0+1) - 2 m t ≤ 0` with no probability cost.

  **No `Γ` event with `σ_y^A = ⊤` is counted as a success.**  `Γ_y` itself is contained
  in `{σ_y ≠ ⊤}` (`GammaSet_subset_sigmaA_ne_top`), and the count is a count of `Γ_y`
  only.  Turning the counted trials into drift contributions at the times `σ_y + 2m - 1`
  (their distinctness and their containment in `(s,t]`) is *not* done here: that is the
  separate passage-time direction.
-/
import Swarm.GammaClass
import Swarm.GammaEndpoint

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Enl

variable {N : ℕ}

/-! ## §1. The class count and its measurability -/

/-- The number of successful trials among the first `K` levels `y0 + 2 m i` of a residue
class starting at `y0`. -/
noncomputable def clsCount (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y0 : ℤ) (K : ℕ) (U : Array N) : ℕ :=
  ((Finset.range K).filter (fun i => U ∈ GammaSet p m hA (lvl y0 m i))).card

/-- The class count is a sum of indicators. -/
lemma clsCount_eq_sum (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y0 : ℤ) (K : ℕ) (U : Array N) :
    (clsCount p m hA y0 K U : ℝ) =
      ∑ i ∈ Finset.range K, if U ∈ GammaSet p m hA (lvl y0 m i) then (1 : ℝ) else 0 := by
  simp only [clsCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma measurable_clsCount (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y0 : ℤ) (K : ℕ) :
    Measurable (fun U : Array N => (clsCount p m hA y0 K U : ℝ)) := by
  have h : (fun U : Array N => (clsCount p m hA y0 K U : ℝ)) =
      fun U => ∑ i ∈ Finset.range K,
        if U ∈ GammaSet p m hA (lvl y0 m i) then (1 : ℝ) else 0 := by
    funext U
    exact clsCount_eq_sum p m hA y0 K U
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_GammaSet m A hA (lvl y0 m i)) measurable_const
    measurable_const

/-- A trial is only nonempty when the pass time is finite: `Γ_y ⊆ {σ_y ≠ ⊤}`. -/
theorem GammaSet_subset_sigmaA_ne_top (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (y : ℤ) : GammaSet p m hA y ⊆ {U : Array N | sigmaA p m U hA y ≠ ⊤} := by
  intro U hU
  simp only [GammaSet, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_inter_iff] at hU
  obtain ⟨n, iy, -, ⟨⟨hAR, -⟩, -⟩⟩ := hU
  have hneq : sigmaA p m U hA y ≠ ⊤ := by
    rw [sigmaA_eq_coe_iff.mpr hAR]
    exact WithTop.coe_ne_top
  simpa only [Set.mem_ofPred_eq] using hneq

lemma clsKbar_pos {a0 b0 : ℤ} {m : ℕ} (hm : 0 < m) : 0 < clsKbar a0 b0 m := by
  simp only [clsKbar]
  exact Nat.zero_lt_succ _

/-! ## §2. The per-class tail -/

/-- `c = (1-p)^{(2m-1)|A|}` is at most `1/2` as soon as `p ≥ 1/2`, `m ≥ 1`, `A ≠ ∅`. -/
lemma gammaC_le_half (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m)
    (A : Finset (Fin N)) (hA : A.Nonempty) :
    (1 - p) ^ ((2 * m - 1) * A.card) ≤ 1 / 2 := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hcard : 0 < (2 * m - 1) * A.card := by
    have h1 : 0 < 2 * m - 1 := by omega
    exact Nat.mul_pos h1 (Finset.card_pos.mpr hA)
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  rw [hn', pow_succ]
  have hb : (1 - p) ^ n' ≤ 1 := pow_le_one₀ h0 (by linarith)
  have hb0 : (0 : ℝ) ≤ (1 - p) ^ n' := pow_nonneg h0 _
  nlinarith

/-- **The finite-interval residue-class count tail.**

Let `c = (1-p)^((2m-1)|A|)`, let `j < 2m` index a residue class of `[a0,b0]` with
`a0 ≥ 0` and `a0 ≤ b0`, and let `t ≥ 0` be the deviation.  Then the class count of
successful trials `Γ` falls below `c · clsK - t` only with probability at most
`exp (-t²/clsK)`.

No range restriction is needed.  Indeed `c ≤ 1/2`, so in the Chernoff range
`K c - j ≤ K/2` the optimisation hypothesis of `gamma_count_tail_exp_finite_records`
holds automatically; and where `c · clsK - t ≤ 0` the lower bound is trivial and the
bad event is empty.  The floor `j = ⌊c·clsK - t⌋` is *not* used in the bound: the
deviation `K c - j` is at least `t`, which only improves the exponent. -/
theorem gamma_class_tail (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m)
    (A : Finset (Fin N)) (hA : A.Nonempty) {a0 b0 : ℤ} (ha0 : 0 ≤ a0) (hab : a0 ≤ b0)
    {t : ℝ} (ht : 0 ≤ t) {j : ℕ} (hj : j < 2 * m) :
    arrayMeasure N {U : Array N | (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)
        < (1 - p) ^ ((2 * m - 1) * A.card) * (clsK a0 b0 m j : ℝ) - t}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (clsK a0 b0 m j : ℝ)))) := by
  classical
  set cr : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hcr
  set K : ℕ := clsK a0 b0 m j with hKdef
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcr0 : 0 ≤ cr := pow_nonneg h1mp _
  have hcrhalf : cr ≤ 1 / 2 := gammaC_le_half p hp0 hp1 m hm A hA
  set x : ℝ := cr * (K : ℝ) - t with hx
  by_cases hxc : x ≤ 0
  · -- the target lower bound is nonpositive, so the bad event is empty
    have hempty : {U : Array N | (clsCount p m hA (clsY0 a0 j) K U : ℝ) < x} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      intro U hU
      have h0 : (0 : ℝ) ≤ (clsCount p m hA (clsY0 a0 j) K U : ℝ) := Nat.cast_nonneg _
      rw [Set.mem_ofPred_eq] at hU
      linarith
    rw [hempty]
    simp only [MeasureTheory.measure_empty]
    exact zero_le
  · -- the Chernoff range: `jf = ⌊cr K - t⌋`, and `cr K - jf ≤ cr K ≤ K/2`
    have hx0 : 0 < x := not_le.mp hxc
    have hKpos : 0 < K := by
      by_contra hK
      have hK0 : K = 0 := Nat.eq_zero_of_not_pos hK
      rw [hK0] at hx
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hx
      linarith
    set jf : ℕ := Nat.floor x with hjf
    have hjf_le : (jf : ℝ) ≤ x := Nat.floor_le hx0.le
    have hjf_gt : x < (jf : ℝ) + 1 := Nat.lt_floor_add_one x
    have hjc : (jf : ℝ) ≤ (K : ℝ) * cr := by rw [hx] at hjf_le; linarith
    have hjc' : (jf : ℝ) ≤ (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) := by
      rw [← hcr]; linarith
    have hthalf : (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) - (jf : ℝ) ≤ (K : ℝ) / 2 := by
      have h1 : cr * (K : ℝ) - (jf : ℝ) ≤ cr * (K : ℝ) := by
        have h0 : (0 : ℝ) ≤ (jf : ℝ) := Nat.cast_nonneg _
        linarith
      have h2 : cr * (K : ℝ) ≤ (K : ℝ) / 2 := by
        have h0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h3 : (K : ℝ) * cr - (jf : ℝ) ≤ (K : ℝ) / 2 := by
        calc (K : ℝ) * cr - (jf : ℝ) = cr * (K : ℝ) - (jf : ℝ) := by ring
          _ ≤ (K : ℝ) / 2 := le_trans h1 h2
      rw [← hcr]
      exact h3
    have htail := gamma_count_tail_exp_finite_records p hp0 hp1 m A hA
      (clsY0_nonneg ha0 j) K jf hKpos hjc' hthalf
    -- the bad event is contained in the count tail event
    have hsub : {U : Array N | (clsCount p m hA (clsY0 a0 j) K U : ℝ) < x} ⊆
        {U : Array N | clsCount p m hA (clsY0 a0 j) K U ≤ jf} := by
      intro U hU
      rw [Set.mem_ofPred_eq] at hU ⊢
      exact Nat.le_floor hU.le
    refine (measure_mono hsub).trans (htail.trans ?_)
    -- the exponent improves, since the deviation is at least `t`
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.exp_le_exp]
    have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hdev : t ≤ cr * (K : ℝ) - (jf : ℝ) := by rw [hx] at hjf_le; linarith
    have hsq : t ^ 2 ≤ (cr * (K : ℝ) - (jf : ℝ)) ^ 2 := by nlinarith [ht]
    have hmono : t ^ 2 / (K : ℝ) ≤ (cr * (K : ℝ) - (jf : ℝ)) ^ 2 / (K : ℝ) := by
      gcongr
    have hstep : cr * (K : ℝ) = (K : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) := by
      rw [hcr]; ring
    rw [hstep] at hmono
    linarith

/-! ## §3. The union over the finitely many classes -/

/-- **The whole-interval count is the sum of the class counts.** -/
theorem card_filter_Icc_eq_sum_clsCount (p : ℝ) (m : ℕ) (hm : 0 < m)
    {A : Finset (Fin N)} (hA : A.Nonempty) {a0 b0 : ℤ} (hab : a0 ≤ b0) (U : Array N) :
    ((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card =
      ∑ j ∈ Finset.range (2 * m),
        clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U := by
  rw [sum_card_filter_clsLevels hm hab (fun y => U ∈ GammaSet p m hA y)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [card_filter_clsLevels hm]
  rfl

/-- **The finite-interval `(locsum)` bound, with its probability.**

Let `0 ≤ a0 ≤ b0`, `m ≥ 1` and `c = (1-p)^((2m-1)|A|)`.  Then, for every deviation `t ≥ 0`,

`P(#{y ∈ [a0,b0] : Γ_y} < c (b0-a0+1) - 2 m t) ≤ 2 m · exp (-t²/K̄)`,
`K̄ = ⌊(b0-a0)/2m⌋ + 1`.

This is the paper's `(locsum)` lower bound — the per-class deviation `t` accumulated over
the `2m` residue classes to `2 m t` (with `t = 2L^{3/4}` this is the paper's `4 m L^{3/4}`)
— outside an event whose probability is exactly the union bound over the `2m` classes.
The count on the left is a count of trials `Γ_y`; by `GammaSet_subset_sigmaA_ne_top` no
`y` with `σ_y^A = ⊤` contributes. -/
theorem gamma_interval_count_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) {a0 b0 : ℤ} (ha0 : 0 ≤ a0)
    (hab : a0 ≤ b0) {t : ℝ} (ht : 0 ≤ t) :
    arrayMeasure N {U : Array N |
        ((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card
          < (1 - p) ^ ((2 * m - 1) * A.card) * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t}
      ≤ (2 * m : ℕ) * ENNReal.ofReal (Real.exp (-(t ^ 2 / (clsKbar a0 b0 m : ℝ)))) := by
  classical
  set cr : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hcr
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcr0 : 0 ≤ cr := pow_nonneg h1mp _
  -- pointwise: if every class count is at least `cr K_j - t`, the total is at least
  -- `cr (L+1) - 2 m t`
  have hsum_eq : ∑ j ∈ Finset.range (2 * m), (cr * (clsK a0 b0 m j : ℝ) - t) =
      cr * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have h2 : ∑ j ∈ Finset.range (2 * m), (clsK a0 b0 m j : ℝ) =
        ((b0 - a0).toNat + 1 : ℝ) := by
      rw [← Nat.cast_sum, sum_clsK hm hab, Nat.cast_add, Nat.cast_one]
    rw [h2]
    push_cast
    ring
  have hpt : ∀ U : Array N,
      (∀ j ∈ Finset.range (2 * m),
        cr * (clsK a0 b0 m j : ℝ) - t ≤ (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)) →
      cr * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t ≤
        (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) := by
    intro U hU
    rw [card_filter_Icc_eq_sum_clsCount p m hm hA hab U, Nat.cast_sum]
    have hle := Finset.sum_le_sum hU
    rwa [hsum_eq] at hle
  -- the bad event is contained in the union of the class-bad events
  have hsub : {U : Array N |
        ((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card
          < cr * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t} ⊆
      ⋃ j ∈ Finset.range (2 * m),
        {U : Array N | (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)
          < cr * (clsK a0 b0 m j : ℝ) - t} := by
    intro U hU
    by_contra hcon
    have hcon' : ∀ j ∈ Finset.range (2 * m),
        cr * (clsK a0 b0 m j : ℝ) - t ≤
          (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ) := by
      intro j hj
      by_contra hlt
      exact hcon (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, not_le.mp hlt⟩⟩)
    exact absurd (hpt U hcon') (not_le.mpr hU)
  refine (measure_mono hsub).trans ?_
  refine (measure_biUnion_finset_le (Finset.range (2 * m)) _).trans ?_
  -- bound each class by the uniform exponent `t²/K̄`
  have hterm : ∀ j ∈ Finset.range (2 * m),
      arrayMeasure N {U : Array N | (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)
          < cr * (clsK a0 b0 m j : ℝ) - t}
        ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (clsKbar a0 b0 m : ℝ)))) := by
    intro j hj
    have hjlt : j < 2 * m := Finset.mem_range.mp hj
    have hKbar : (clsK a0 b0 m j : ℝ) ≤ (clsKbar a0 b0 m : ℝ) := by
      exact_mod_cast clsK_le_Kbar hm hab (j := j)
    by_cases hKj : clsK a0 b0 m j = 0
    · -- an empty class carries no trials: the bad event is empty
      have hempty : {U : Array N | (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)
            < cr * (clsK a0 b0 m j : ℝ) - t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        intro U hU
        rw [Set.mem_ofPred_eq] at hU
        rw [hKj] at hU
        simp only [Nat.cast_zero, mul_zero, zero_sub] at hU
        have h0 : (0 : ℝ) ≤ (clsCount p m hA (clsY0 a0 j) 0 U : ℝ) := Nat.cast_nonneg _
        linarith
      rw [hempty]
      simp only [MeasureTheory.measure_empty]
      exact zero_le
    · have hKpos : 0 < clsK a0 b0 m j := Nat.pos_of_ne_zero hKj
      have hK1 : (1 : ℝ) ≤ (clsK a0 b0 m j : ℝ) := by exact_mod_cast hKpos
      refine (gamma_class_tail p hp0 hp1 m hm A hA ha0 hab ht hjlt).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.exp_le_exp]
      have h0 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
      have hmono : t ^ 2 / (clsKbar a0 b0 m : ℝ) ≤ t ^ 2 / (clsK a0 b0 m j : ℝ) :=
        div_le_div_of_nonneg_left h0 (by linarith) hKbar
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The exact complement statement**: outside the union of the `2m` class-bad events,
the number of trials `Γ_y` with `y ∈ [a0,b0]` is at least `c (b0-a0+1) - 2 m t`. -/
theorem gamma_interval_lower_on_good (p : ℝ) (m : ℕ) (hm : 0 < m)
    {A : Finset (Fin N)} (hA : A.Nonempty) {a0 b0 : ℤ} (hab : a0 ≤ b0) {t : ℝ}
    {U : Array N}
    (hU : ∀ j ∈ Finset.range (2 * m),
      (1 - p) ^ ((2 * m - 1) * A.card) * (clsK a0 b0 m j : ℝ) - t ≤
        (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)) :
    (1 - p) ^ ((2 * m - 1) * A.card) * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t ≤
      (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) := by
  classical
  set cr : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hcr
  rw [card_filter_Icc_eq_sum_clsCount p m hm hA hab U, Nat.cast_sum]
  have hle := Finset.sum_le_sum hU
  have hsum_eq : ∑ j ∈ Finset.range (2 * m), (cr * (clsK a0 b0 m j : ℝ) - t) =
      cr * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have h2 : ∑ j ∈ Finset.range (2 * m), (clsK a0 b0 m j : ℝ) =
        ((b0 - a0).toNat + 1 : ℝ) := by
      rw [← Nat.cast_sum, sum_clsK hm hab, Nat.cast_add, Nat.cast_one]
    rw [h2]
    push_cast
    ring
  rw [hsum_eq] at hle
  exact hle

/-- The trivial short-interval case: if `c (b0-a0+1) - 2 m t ≤ 0` the count bound holds
with no probability cost at all. -/
theorem gamma_interval_count_lower_short (p : ℝ) (m : ℕ) {A : Finset (Fin N)}
    {a0 b0 : ℤ} {t : ℝ} (hshort :
      (1 - p) ^ ((2 * m - 1) * A.card) * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t ≤ 0)
    (U : Array N) :
    (1 - p) ^ ((2 * m - 1) * A.card) * ((b0 - a0).toNat + 1 : ℝ) - 2 * (m : ℝ) * t ≤
      (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) := by
  have h0 : (0 : ℝ) ≤ (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) :=
    Nat.cast_nonneg _
  linarith

/-! ## §4. The paper's deviation and exponent -/

/-- `(2 L^{3/4})² = 4 L √L` for `L ≥ 0`, with `L^{3/4} = √(L √L)`. -/
theorem two_mul_pow_three_quarters_sq {L : ℝ} (hL : 0 ≤ L) :
    (2 * Real.sqrt (L * Real.sqrt L)) ^ 2 = 4 * L * Real.sqrt L := by
  have h0 : 0 ≤ L * Real.sqrt L := by positivity
  rw [mul_pow, Real.sq_sqrt h0]
  ring

/-- **The exponent of the paper's deviation.**  With `t = 2L^{3/4}` and a uniform bound
`K̄ ≤ C_T L`, the Chernoff exponent of `gamma_interval_count_lower` is exactly
`4 √L / C_T`, of the paper's form `c_T L^{1/2}`. -/
theorem paper_deviation_exponent {L CT : ℝ} (hL : 0 < L) (hCT : 0 < CT) :
    (2 * Real.sqrt (L * Real.sqrt L)) ^ 2 / (CT * L) = 4 * Real.sqrt L / CT := by
  rw [two_mul_pow_three_quarters_sq hL.le]
  field_simp

/-- With `t = 2L^{3/4}`, the deviation accumulated over the `2m` classes. -/
theorem two_m_mul_paper_deviation (m : ℕ) {L : ℝ} :
    2 * (m : ℝ) * (2 * Real.sqrt (L * Real.sqrt L)) = 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L) := by
  ring

/-! ## §5. A finite family of intervals -/

/-- **Simultaneous `(locsum)` bounds on a finite family of integer intervals.**

For every interval `[a,b]` of a finite family `Is`, outside an event of probability at most
`2m · exp(-t²/K̄(a,b))`, the number of trials `Γ_y` with `y ∈ [a,b]` is at least
`c (b-a+1) - 2 m t`.  The union bound over the family is what makes the estimate
simultaneous; no constant is hidden. -/
theorem gamma_family_count_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) (Is : Finset (ℤ × ℤ)) {t : ℝ}
    (ht : 0 ≤ t) (hlo : ∀ ab ∈ Is, 0 ≤ ab.1) (hle : ∀ ab ∈ Is, ab.1 ≤ ab.2) :
    arrayMeasure N (⋃ ab ∈ Is, {U : Array N |
        ((Finset.Icc ab.1 ab.2).filter (fun y => U ∈ GammaSet p m hA y)).card
          < (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
            - 2 * (m : ℝ) * t})
      ≤ ∑ ab ∈ Is, (2 * m : ℕ) *
          ENNReal.ofReal (Real.exp (-(t ^ 2 / (clsKbar ab.1 ab.2 m : ℝ)))) := by
  refine (measure_biUnion_finset_le Is _).trans (Finset.sum_le_sum ?_)
  intro ab hab_mem
  exact gamma_interval_count_lower p hp0 hp1 m hm A hA (hlo ab hab_mem) (hle ab hab_mem) ht

/-! ## §6. The paper's window `(R_s, R_t - 2m]` and its deviation `2L^{3/4}` -/

/-- **The paper's window.**  For `0 ≤ R_s` and `R_s < R_t - 2m`, the interval
`[R_s+1, R_t-2m]` has exactly `R_t - R_s - 2m` integers, so
`gamma_interval_count_lower` gives

`P(#{y ∈ (R_s, R_t-2m] : Γ_y} < c (R_t-R_s-2m) - 2 m t) ≤ 2 m · exp (-t²/K̄)`.

Whether the *events* `Γ_y` in this window can be charged to distinct times
`σ_y + 2m - 1 ∈ (s,t]` is the separate passage-time question; this statement is only
about the count. -/
theorem gamma_window_count_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) {rs rt : ℤ}
    (hlo : 0 ≤ rs + 1) (hwin : rs + 1 ≤ rt - ((2 * m : ℕ) : ℤ)) {t : ℝ} (ht : 0 ≤ t) :
    arrayMeasure N {U : Array N |
        ((Finset.Icc (rs + 1) (rt - ((2 * m : ℕ) : ℤ))).filter
          (fun y => U ∈ GammaSet p m hA y)).card
          < (1 - p) ^ ((2 * m - 1) * A.card) * ((rt - rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
            - 2 * (m : ℝ) * t}
      ≤ (2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-(t ^ 2 / (clsKbar (rs + 1) (rt - ((2 * m : ℕ) : ℤ)) m : ℝ)))) := by
  have hidx : (((rt - ((2 * m : ℕ) : ℤ)) - (rs + 1)).toNat + 1 : ℝ) =
      ((rt - rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ) := by
    have hnat : ((rt - ((2 * m : ℕ) : ℤ)) - (rs + 1)).toNat + 1 =
        (rt - rs - ((2 * m : ℕ) : ℤ)).toNat := by
      have h1 : (0 : ℤ) ≤ rt - rs - ((2 * m : ℕ) : ℤ) := by omega
      have h5 : (((rt - ((2 * m : ℕ) : ℤ)) - (rs + 1)).toNat : ℤ) + 1 =
          (((rt - rs - ((2 * m : ℕ) : ℤ)).toNat) : ℤ) := by
        have h6 : (((rt - ((2 * m : ℕ) : ℤ)) - (rs + 1)).toNat : ℤ) =
            (rt - ((2 * m : ℕ) : ℤ)) - (rs + 1) := Int.toNat_of_nonneg (by omega)
        have h7 : (((rt - rs - ((2 * m : ℕ) : ℤ)).toNat) : ℤ) =
            rt - rs - ((2 * m : ℕ) : ℤ) := Int.toNat_of_nonneg h1
        omega
      have h6 : (((rt - ((2 * m : ℕ) : ℤ)) - (rs + 1)).toNat + 1 : ℤ) =
          (((rt - rs - ((2 * m : ℕ) : ℤ)).toNat) : ℤ) := by
        push_cast
        exact h5
      exact_mod_cast h6
    exact_mod_cast hnat
  have h := gamma_interval_count_lower p hp0 hp1 m hm A hA
    (a0 := rs + 1) (b0 := rt - ((2 * m : ℕ) : ℤ)) hlo hwin ht
  simpa only [hidx] using h

/-- **The paper's deviation `t = 2 L^{3/4}`.**  On the window `(R_s, R_t-2m]`, the count
is at least `c (R_t-R_s-2m) - 4 m L^{3/4}` — the paper's `4 m L^{3/4}`, with
`L^{3/4} = √(L√L)` — outside an event of probability at most
`2 m · exp (-(4 L√L)/K̄)`. -/
theorem gamma_window_count_lower_paper (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) {rs rt : ℤ} {L : ℝ} (hL : 0 < L)
    (hlo : 0 ≤ rs + 1) (hwin : rs + 1 ≤ rt - ((2 * m : ℕ) : ℤ)) :
    arrayMeasure N {U : Array N |
        ((Finset.Icc (rs + 1) (rt - ((2 * m : ℕ) : ℤ))).filter
          (fun y => U ∈ GammaSet p m hA y)).card
          < (1 - p) ^ ((2 * m - 1) * A.card) * ((rt - rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
            - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)}
      ≤ (2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-(4 * L * Real.sqrt L /
            (clsKbar (rs + 1) (rt - ((2 * m : ℕ) : ℤ)) m : ℝ)))) := by
  have ht : (0 : ℝ) ≤ 2 * Real.sqrt (L * Real.sqrt L) := by positivity
  have h := gamma_window_count_lower p hp0 hp1 m hm A hA hlo hwin ht
  have hthr : (1 - p) ^ ((2 * m - 1) * A.card) * ((rt - rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
        - 2 * (m : ℝ) * (2 * Real.sqrt (L * Real.sqrt L)) =
      (1 - p) ^ ((2 * m - 1) * A.card) * ((rt - rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ)
        - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L) := by ring
  have hexp : (2 * Real.sqrt (L * Real.sqrt L)) ^ 2 /
        (clsKbar (rs + 1) (rt - ((2 * m : ℕ) : ℤ)) m : ℝ) =
      4 * L * Real.sqrt L / (clsKbar (rs + 1) (rt - ((2 * m : ℕ) : ℤ)) m : ℝ) := by
    rw [two_mul_pow_three_quarters_sq hL.le]
  simpa only [hthr, hexp] using h

/-! ## §7. The paper's left-hand side as a sum of indicators -/

/-- The paper's `∑_{a0 ≤ y ≤ b0} 1_{Γ_y^A}` is exactly the class count displayed in
`gamma_interval_count_lower`, so the probability bound applies to the paper's sum
verbatim. -/
theorem sum_indicator_GammaSet (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    {a0 b0 : ℤ} (U : Array N) :
    ∑ y ∈ Finset.Icc a0 b0, (if U ∈ GammaSet p m hA y then (1 : ℝ) else 0) =
      (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) := by
  rw [Finset.sum_boole]

/-- The same count with the paper's interval `(R_s, R_t - 2m]`. -/
theorem sum_indicator_GammaSet_window (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    {rs rt : ℤ} (U : Array N) :
    ∑ y ∈ Finset.Icc (rs + 1) (rt - ((2 * m : ℕ) : ℤ)),
        (if U ∈ GammaSet p m hA y then (1 : ℝ) else 0) =
      (((Finset.Icc (rs + 1) (rt - ((2 * m : ℕ) : ℤ))).filter
        (fun y => U ∈ GammaSet p m hA y)).card : ℝ) :=
  sum_indicator_GammaSet p m hA U

end Swarming.Enl
