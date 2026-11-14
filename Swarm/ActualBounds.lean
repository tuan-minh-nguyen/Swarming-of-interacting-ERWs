/-
Transfer of the unconditional auxiliary running-maximum bound
(`SymmTransport.prob_nonhit_le_sqrt_actual`) to the **actual interacting
trajectory** `Swarming.Trajectory.trajectory` under `Swarming.Uniform.arrayMeasure`.

The pointwise coupling `symmetricWalk_le_trajectory` says the auxiliary fair walk
never exceeds the interacting walker's position (for `p ≥ 1/2`).  Hence the event
"the interacting walker stayed below `b` up to time `n`" is contained in the
corresponding event for the auxiliary walk, so it inherits the quantitative
bound `(2b+1)√2/√(n+1)`.  Complements give a lower bound on the probability that
the interacting walker reaches level `b` by time `n`, a union bound gives the
same simultaneously for all `N` walkers, and Borel–Cantelli converts the
finite-horizon estimate into almost-sure unboundedness of every walker.

No independence statement for the auxiliary increments is used (that remains a
separate task); the only inputs are the integrated pattern law via
`prob_nonhit_le_sqrt_actual` and the verified pointwise coupling.
-/
import Swarm.Bound

open MeasureTheory ProbabilityTheory Set Filter
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

namespace Swarming.Actual

variable {N : ℕ}

/-! ### Measurability of the actual-trajectory events -/

/-- The event that walker `i` stays strictly below `b` up to time `n`. -/
theorem measurableSet_nonhit (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) (b : ℤ) :
    MeasurableSet {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < b} := by
  have hset : {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < b}
      = ⋂ k ∈ Finset.range (n + 1),
          {U : Array N | (trajectory p m U k).pos i < b} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  rw [hset]
  exact Finset.measurableSet_biInter _ fun k _ =>
    measurableSet_Iio.preimage ((Swarming.Fair.measurable_trajectory p m k).1 i)

/-- The event that walker `i` reaches level `b` by time `n`. -/
theorem measurableSet_hit (p : ℝ) (m : ℕ) (i : Fin N) (n : ℕ) (b : ℤ) :
    MeasurableSet {U : Array N | ∃ k ≤ n, b ≤ (trajectory p m U k).pos i} := by
  have hset : {U : Array N | ∃ k ≤ n, b ≤ (trajectory p m U k).pos i}
      = {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < b}ᶜ := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_lt]
    constructor <;> rintro ⟨k, hk, h⟩ <;> exact ⟨k, hk, h⟩
  rw [hset]
  exact (measurableSet_nonhit p m i n b).compl

/-! ### Inheritance of the auxiliary bound -/

/-- **Non-hitting bound for the actual interacting walker.**  For `p ≥ 1/2` the
probability that walker `i` stays below level `b` up to time `n` is at most
`(2b+1)√2/√(n+1)`; the fair auxiliary walk dominates nothing, it is dominated by
the interacting one, so it bounds the interacting stay-below event from above. -/
theorem nonhit_le_sqrt {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) (n : ℕ) {b : ℕ}
    (hb : 1 ≤ b) :
    (arrayMeasure N).real {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < (b : ℤ)}
      ≤ (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (Swarming.SymmTransport.prob_nonhit_le_sqrt_actual (N := N) p m i n hb)
  intro U hU k hk
  exact lt_of_le_of_lt (symmetricWalk_le_trajectory hp m U i k) (hU k hk)

/-- **Reaching bound for the actual interacting walker.** -/
theorem hit_ge_one_sub_sqrt {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) (n : ℕ) {b : ℕ}
    (hb : 1 ≤ b) :
    1 - (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1)
      ≤ (arrayMeasure N).real {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} := by
  have hcompl : (arrayMeasure N).real {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}
      = 1 - (arrayMeasure N).real
          {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < (b : ℤ)} := by
    have hset : {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}
        = {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < (b : ℤ)}ᶜ := by
      ext U
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_lt]
      constructor <;> rintro ⟨k, hk, h⟩ <;> exact ⟨k, hk, h⟩
    rw [hset, measureReal_compl (measurableSet_nonhit p m i n (b : ℤ))]
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [hcompl]
  linarith [nonhit_le_sqrt hp m i n hb]

/-! ### Simultaneous version for all `N` walkers -/

/-- **Every walker reaches level `b` by time `n`, with probability at least
`1 - N·(2b+1)√2/√(n+1)`** — the finite-`N` union bound. -/
theorem all_walkers_hit_ge_one_sub {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (n : ℕ) {b : ℕ}
    (hb : 1 ≤ b) :
    1 - (N : ℝ) * ((2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1))
      ≤ (arrayMeasure N).real
          {U : Array N | ∀ i : Fin N, ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} := by
  classical
  set x : ℝ := (2 * (b : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) with hx
  have hAmeas : ∀ i : Fin N,
      MeasurableSet {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} :=
    fun i => measurableSet_hit p m i n (b : ℤ)
  have huniv : (arrayMeasure N).real (univ : Set (Array N)) = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hsub : (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ)ᶜ
      ⊆ {U : Array N | ∀ i : Fin N, ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} := by
    intro U hU i
    by_contra h
    exact hU (Set.mem_iUnion.2 ⟨i, h⟩)
  have hUmeas : MeasurableSet
      (⋃ i : Fin N, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ) :=
    MeasurableSet.iUnion fun i => (hAmeas i).compl
  have hcomplreal : (arrayMeasure N).real
      (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ)
      = 1 - (arrayMeasure N).real
          (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ)ᶜ := by
    rw [measureReal_compl hUmeas, huniv]
    ring
  have hunion : (arrayMeasure N).real
      (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ) ≤ (N : ℝ) * x := by
    refine le_trans (measureReal_iUnion_fintype_le
      (fun i : Fin N => {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ)) ?_
    have hterm : ∀ i : Fin N,
        (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ ≤ x := by
      intro i
      have hc : (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ
          = 1 - (arrayMeasure N).real
              {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} := by
        rw [measureReal_compl (hAmeas i), huniv]
      have := hit_ge_one_sub_sqrt (N := N) hp m i n hb
      rw [hc]
      linarith
    calc ∑ i : Fin N, (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ
        ≤ ∑ _i : Fin N, x := Finset.sum_le_sum fun i _ => hterm i
      _ = (N : ℝ) * x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc 1 - (N : ℝ) * x
      ≤ 1 - (arrayMeasure N).real
          (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ) := by
        linarith [hunion]
    _ = (arrayMeasure N).real
          (⋃ i, {U : Array N | ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i}ᶜ)ᶜ := by
        rw [hcomplreal]; ring
    _ ≤ (arrayMeasure N).real
          {U : Array N | ∀ i : Fin N, ∃ k ≤ n, (b : ℤ) ≤ (trajectory p m U k).pos i} :=
        measureReal_mono hsub (measure_ne_top _ _)

/-! ### Elementary size estimate at horizon `(b+1)^6` -/

/-- The running-maximum bound at horizon `(b+1)^6` is dominated by
`3√2/(b+1)²`, whose sum over `b` converges. -/
theorem sqrt_bound_step (b : ℕ) :
    (2 * ((b : ℝ) + 1) + 1) * Real.sqrt 2 / Real.sqrt (((b : ℝ) + 1) ^ 6 + 1)
      ≤ 3 * Real.sqrt 2 * (1 / ((b : ℝ) + 1) ^ 2) := by
  set r : ℝ := (b : ℝ) + 1 with hr
  have hr1 : (1 : ℝ) ≤ r := by
    rw [hr]
    linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hsqrt : r ^ 3 ≤ Real.sqrt (r ^ 6 + 1) := by
    apply Real.le_sqrt_of_sq_le
    have h : (r ^ 3) ^ 2 = r ^ 6 := by ring
    rw [h]
    linarith
  have hnum : (2 * r + 1) ≤ 3 * r := by linarith
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hstep1 : (2 * r + 1) * Real.sqrt 2 / Real.sqrt (r ^ 6 + 1)
      ≤ (2 * r + 1) * Real.sqrt 2 / r ^ 3 :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * r + 1) (Real.sqrt_nonneg 2))
      (pow_pos hr0 3) hsqrt
  have hstep2 : (2 * r + 1) * Real.sqrt 2 / r ^ 3 ≤ (3 * r) * Real.sqrt 2 / r ^ 3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum hsqrt2) (le_of_lt (pow_pos hr0 3))
  refine le_trans hstep1 (le_trans hstep2 ?_)
  have h3 : (3 * r) * Real.sqrt 2 / r ^ 3 = 3 * Real.sqrt 2 * (1 / r ^ 2) := by
    field_simp
  rw [h3]

/-! ### Almost-sure unboundedness of the actual walkers -/

/-- Borel–Cantelli consequence of the finite-horizon estimate: almost surely, for all
large `b`, walker `i` reaches level `b + 1` by time `(b + 1)^6`. -/
theorem ae_eventually_reaches {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ b : ℕ in atTop,
      ∃ k ≤ (b + 1) ^ 6, ((b + 1 : ℕ) : ℤ) ≤ (trajectory p m U k).pos i := by
  classical
  have hsumm : Summable (fun b : ℕ => 3 * Real.sqrt 2 * (1 / ((b : ℝ) + 1) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) :=
      (Real.summable_one_div_nat_rpow).mpr (by norm_num : (1 : ℝ) < 2)
    have hshift : Summable (fun b : ℕ => 1 / ((b : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) 1).mpr hbase
      simpa using h
    simpa [mul_assoc] using hshift.mul_left (3 * Real.sqrt 2)
  have hbound : ∀ b : ℕ, (arrayMeasure N)
      {U : Array N | ∀ k ≤ (b + 1) ^ 6, (trajectory p m U k).pos i < ((b + 1 : ℕ) : ℤ)}
      ≤ ENNReal.ofReal (3 * Real.sqrt 2 * (1 / ((b : ℝ) + 1) ^ 2)) := by
    intro b
    have hb1 : 1 ≤ b + 1 := Nat.succ_le_succ (Nat.zero_le b)
    have hreal := nonhit_le_sqrt (N := N) hp m i ((b + 1) ^ 6) hb1
    have hcast1 : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by push_cast; ring
    have hcast2 : (((b + 1) ^ 6 : ℕ) : ℝ) = ((b : ℝ) + 1) ^ 6 := by push_cast; ring
    rw [hcast1, hcast2] at hreal
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (sqrt_bound_step b))
    rw [← ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _)]
    exact ENNReal.ofReal_le_ofReal hreal
  have htsum : ∑' b : ℕ, (arrayMeasure N)
      {U : Array N | ∀ k ≤ (b + 1) ^ 6, (trajectory p m U k).pos i < ((b + 1 : ℕ) : ℤ)} ≠ ⊤ := by
    have hle := ENNReal.tsum_le_tsum hbound
    have hof : (∑' b : ℕ, ENNReal.ofReal (3 * Real.sqrt 2 * (1 / ((b : ℝ) + 1) ^ 2)))
        = ENNReal.ofReal (∑' b : ℕ, 3 * Real.sqrt 2 * (1 / ((b : ℝ) + 1) ^ 2)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun b => by positivity) hsumm]
    rw [hof] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae := MeasureTheory.ae_eventually_notMem htsum
  filter_upwards [hae] with U hU
  filter_upwards [hU] with b hb
  simp only [not_forall, not_lt] at hb
  exact ⟨hb.choose, hb.choose_spec.1, hb.choose_spec.2⟩

/-- **Almost sure unboundedness of every single interacting walker** (`p ≥ 1/2`). -/
theorem ae_unbounded_above {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ B : ℕ, ∃ k : ℕ, (B : ℤ) ≤ (trajectory p m U k).pos i := by
  filter_upwards [ae_eventually_reaches (N := N) hp m i] with U hU B
  obtain ⟨b₀, hb₀⟩ := Filter.eventually_atTop.1 hU
  obtain ⟨k, -, hle⟩ := hb₀ (max b₀ B) (le_max_left _ _)
  have h1 : (B : ℤ) ≤ ((max b₀ B + 1 : ℕ) : ℤ) := by
    have h2 : B ≤ (max b₀ B + 1) := le_trans (le_max_right b₀ B) (Nat.le_succ _)
    exact_mod_cast h2
  exact ⟨k, le_trans h1 hle⟩

/-- **Almost sure simultaneous unboundedness of all `N` walkers.** -/
theorem ae_all_unbounded_above {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ i : Fin N, ∀ B : ℕ, ∃ k : ℕ,
      (B : ℤ) ≤ (trajectory p m U k).pos i := by
  have hall := (Finset.eventually_all (Finset.univ : Finset (Fin N))
    (l := ae (arrayMeasure N))
    (p := fun i (U : Array N) => ∀ B : ℕ, ∃ k : ℕ,
      (B : ℤ) ≤ (trajectory p m U k).pos i)).mpr
    (fun i _ => ae_unbounded_above (N := N) hp m i)
  filter_upwards [hall] with U hU i
  exact hU i (Finset.mem_univ i)

/-- **The interacting walker's hitting probability dominates the exact fair-walk
reflection count**: the two-term count of the finite reflection module is a lower bound. -/
theorem hit_ge_binomial {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) (n : ℕ) {b : ℤ}
    (hb : 1 ≤ b) :
    (((Finset.univ.filter (fun ω : Fin n → Bool =>
          b ≤ SwarmReflect.psum ω n)).card : ℝ)
        + ((Finset.univ.filter (fun ω : Fin n → Bool =>
            b < SwarmReflect.psum ω n)).card : ℝ)) / 2 ^ n
      ≤ (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, b ≤ (trajectory p m U k).pos i} := by
  refine le_trans (le_of_eq (Swarming.SymmTransport.prob_hit_eq_actual (N := N) p m i n hb).symm) ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro U hU
  obtain ⟨k, hk, hle⟩ := hU
  exact ⟨k, hk, le_trans hle (symmetricWalk_le_trajectory hp m U i k)⟩

/-! ### The natural `√n` scale -/

/-- Arithmetic core of the `√n`-scale statements: with `b = ⌊√n⌋/K` the running-maximum
bound `(2b+1)√2/√(n+1)` is at most `2√2/K + √2/√n`. -/
theorem sqrt_scale_bound {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) :
    (2 * ((n.sqrt / K : ℕ) : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1)
      ≤ 2 * Real.sqrt 2 / (K : ℝ) + Real.sqrt 2 / Real.sqrt (n : ℝ) := by
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsq : ((n.sqrt : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have h := Nat.sqrt_le' n
    have hcast : (((n.sqrt ^ 2 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    simpa [pow_two] using hcast
  have hb_le : ((n.sqrt / K : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) / (K : ℝ) :=
    le_trans (Nat.cast_div_le) (by gcongr)
  have hnum : 2 * ((n.sqrt / K : ℕ) : ℝ) + 1 ≤ 2 * (Real.sqrt (n : ℝ) / (K : ℝ)) + 1 := by
    linarith
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hinv : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 1 / Real.sqrt (n : ℝ) :=
    one_div_le_one_div_of_le hs (Real.sqrt_le_sqrt (by linarith))
  calc (2 * ((n.sqrt / K : ℕ) : ℝ) + 1) * Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1)
      = ((2 * ((n.sqrt / K : ℕ) : ℝ) + 1) * Real.sqrt 2)
          * (1 / Real.sqrt ((n : ℝ) + 1)) := by ring
    _ ≤ ((2 * (Real.sqrt (n : ℝ) / (K : ℝ)) + 1) * Real.sqrt 2)
          * (1 / Real.sqrt (n : ℝ)) := by
        refine mul_le_mul ?_ hinv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hnum hsqrt2
    _ = 2 * Real.sqrt 2 / (K : ℝ) + Real.sqrt 2 / Real.sqrt (n : ℝ) := by
        field_simp

/-- **At the natural scale `√n`**: the actual interacting walker stays below level
`⌊√n/K⌋` throughout `[0, n]` with probability at most `2√2/K + √2/√n`. -/
theorem stays_below_sqrt_scale {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) {n K : ℕ}
    (hn : 1 ≤ n) (hK : 1 ≤ K) (hb : 1 ≤ n.sqrt / K) :
    (arrayMeasure N).real
        {U : Array N | ∀ k ≤ n, (trajectory p m U k).pos i < ((n.sqrt / K : ℕ) : ℤ)}
      ≤ 2 * Real.sqrt 2 / (K : ℝ) + Real.sqrt 2 / Real.sqrt (n : ℝ) :=
  le_trans (nonhit_le_sqrt (N := N) hp m i n hb) (sqrt_scale_bound hn hK)

/-- **At the natural scale `√n`**, complementary form: the walker reaches level
`⌊√n/K⌋` by time `n` with probability at least `1 - 2√2/K - √2/√n`. -/
theorem hit_sqrt_scale {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) {n K : ℕ}
    (hn : 1 ≤ n) (hK : 1 ≤ K) (hb : 1 ≤ n.sqrt / K) :
    1 - 2 * Real.sqrt 2 / (K : ℝ) - Real.sqrt 2 / Real.sqrt (n : ℝ)
      ≤ (arrayMeasure N).real
          {U : Array N | ∃ k ≤ n, ((n.sqrt / K : ℕ) : ℤ) ≤ (trajectory p m U k).pos i} := by
  have h := hit_ge_one_sub_sqrt (N := N) hp m i n hb
  linarith [sqrt_scale_bound hn hK]

end Swarming.Actual

/-! ### Axiom audit -/


