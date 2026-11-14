/-
  Direction (E): the actual drift martingale of the interacting model
  `M^i_n = X^i_n - (2p-1) #{t < n : i excited at t}` as a Mathlib `Martingale`,
  and the consequent oscillation statement `max(M^i_t) - X^i_t = o(n)`.

  The paper's `(mart)` is available in set-integral form (`Swarm.mart_increment`).
  `martingale_of_setIntegral_eq_succ` turns it into a genuine nested-filtration
  martingale; `MartingaleLimit.martingale_strong_law` plus
  `MartingaleLimit.tendsto_running_max` then give `max_{t<=n} |M^i_t| = o(n)`, and
  `SwarmHosc.hosc_pointwise` converts that into the `hosc` premise of the verified
  covering argument `SwarmSpeed.speed_lower_bound`.
-/
import Swarm.Imports
import Swarm.Hosc
import Swarm.Speed
import Swarm.Assembly.Model
import Swarm.UpperBound
import Swarm.MartingaleLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

namespace SwarmHosc

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ}
  {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ m0} {m : ℕ} {p : ℝ}

/-! ### Measurability of the excitation counter in the enlarged filtration -/

/-- The excitation set at time `t` is measured by `𝓕 t` (not merely Borel). -/
theorem measurableSet_excitedSet_filt (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (t : ℕ)
    (i : Fin N) : MeasurableSet[𝓕 t] (Swarm.excitedSet X m t i) := by
  classical
  have hXj : ∀ (s : ℕ) (j : Fin N), s ≤ t → Measurable[𝓕 t] fun ω => X s ω j :=
    fun s j hs => (hlaw.1 s j).mono (𝓕.mono hs) le_rfl
  have hsum : Measurable[𝓕 t] fun ω => ∑ j ∈ Finset.univ.erase i,
      ∑ s ∈ Finset.range (t + 1), (if X s ω j = X t ω i then (1 : ℕ) else 0) := by
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun s hs => ?_
    have hs' : s ≤ t := by
      have := Finset.mem_range.1 hs
      omega
    exact Measurable.ite (measurableSet_eq_fun (hXj s j hs') (hXj t i le_rfl))
      measurable_const measurable_const
  have hgoal : Swarm.excitedSet X m t i = {ω | m ≤ ∑ j ∈ Finset.univ.erase i,
      ∑ s ∈ Finset.range (t + 1), (if X s ω j = X t ω i then (1 : ℕ) else 0)} := by
    ext ω
    simp [Swarm.excitedSet, Swarm.Excited, Swarm.otherVisits, Swarm.localTime]
  rw [hgoal]
  exact measurableSet_le measurable_const hsum

/-- The excitation counter `excCount n` is `𝓕 n`-measurable. -/
theorem measurable_excCount_filt (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (n : ℕ)
    (i : Fin N) : Measurable[𝓕 n] fun ω => (Swarm.excCount X m n ω i : ℝ) := by
  classical
  have hrepr : (fun ω => (Swarm.excCount X m n ω i : ℝ))
      = fun ω => ∑ t ∈ Finset.range n, (if Swarm.Excited X m t ω i then (1 : ℝ) else 0) := by
    funext ω
    simp only [Swarm.excCount, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  rw [hrepr]
  refine Finset.measurable_sum _ fun t ht => ?_
  have ht' : t < n := Finset.mem_range.1 ht
  have hset : MeasurableSet[𝓕 n] (Swarm.excitedSet X m t i) :=
    (𝓕.mono (le_of_lt ht')) _ (measurableSet_excitedSet_filt hlaw t i)
  have hind : (fun ω => (if Swarm.Excited X m t ω i then (1 : ℝ) else 0))
      = Set.indicator (Swarm.excitedSet X m t i) (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : Swarm.Excited X m t ω i <;> simp [Set.indicator, Swarm.excitedSet, h]
  rw [hind]
  exact Measurable.indicator measurable_const hset

/-- The excitation counter is monotone in time. -/
lemma excCount_mono (t n : ℕ) (ht : t ≤ n) (ω : Ω) (i : Fin N) :
    Swarm.excCount X m t ω i ≤ Swarm.excCount X m n ω i := by
  classical
  unfold Swarm.excCount
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr ht) ?_
  intro k _ _
  split_ifs <;> simp

/-- The excitation counter is bounded by the time index. -/
lemma excCount_le (n : ℕ) (ω : Ω) (i : Fin N) : Swarm.excCount X m n ω i ≤ n := by
  classical
  unfold Swarm.excCount
  calc ∑ t ∈ Finset.range n, (if Swarm.Excited X m t ω i then 1 else 0)
      ≤ ∑ _t ∈ Finset.range n, 1 := by
        refine Finset.sum_le_sum fun t _ => ?_
        split_ifs <;> simp
    _ = n := by simp

/-- The drift martingale is `𝓕 n`-measurable. -/
theorem measurable_mart_filt (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    Measurable[𝓕 n] fun ω => Swarm.mart p X m n ω i := by
  have hpos : Measurable[𝓕 n] fun ω => Swarm.pos X n i ω :=
    (Swarm.measurable_intToReal).comp (hlaw.1 n i)
  have hexc : Measurable[𝓕 n] fun ω => (Swarm.excCount X m n ω i : ℝ) :=
    measurable_excCount_filt hlaw n i
  show Measurable[𝓕 n] (fun ω => Swarm.pos X n i ω - (2 * p - 1) * (Swarm.excCount X m n ω i : ℝ))
  exact hpos.sub (hexc.const_mul (2 * p - 1))

/-! ### The drift martingale -/

/-- Integrability of the drift martingale (finite measure space, sublinear growth). -/
theorem integrable_mart_filt [IsProbabilityMeasure μ]
    (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    Integrable (fun ω => Swarm.mart p X m n ω i) μ := by
  have hpos : Integrable (fun ω => Swarm.pos X n i ω) μ := Swarm.integrable_pos hlaw n i
  have hexc : Integrable (fun ω => (Swarm.excCount X m n ω i : ℝ)) μ := by
    refine Integrable.of_bound
      ((measurable_excCount_filt hlaw n i).mono (𝓕.le n) le_rfl).aestronglyMeasurable
      (n : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast excCount_le (X := X) (m := m) n ω i
  show Integrable (fun ω => Swarm.pos X n i ω - (2 * p - 1) * (Swarm.excCount X m n ω i : ℝ)) μ
  exact hpos.sub (hexc.const_mul (2 * p - 1))

/-- The one-step difference of the drift martingale, in explicit form. -/
theorem mart_succ_sub (n : ℕ) (i : Fin N) (ω : Ω) :
    Swarm.mart p X m (n + 1) ω i - Swarm.mart p X m n ω i
      = ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
        - (2 * p - 1) * Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω := by
  classical
  have hE1 : ((Swarm.excCount X m (n + 1) ω i : ℕ) : ℝ)
      = (Swarm.excCount X m n ω i : ℝ) + (if Swarm.Excited X m n ω i then (1 : ℝ) else 0) := by
    rw [Swarm.excCount_succ]
    push_cast
    ring
  have hP' : Swarm.pos X (n + 1) i ω
      = Swarm.pos X n i ω + ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) := by
    simp only [Swarm.pos]
    push_cast
    ring
  have hI : Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω
      = (if Swarm.Excited X m n ω i then (1 : ℝ) else 0) := by
    by_cases h : Swarm.Excited X m n ω i <;> simp [Set.indicator, Swarm.excitedSet, h]
  simp only [Swarm.mart]
  rw [hE1, hP', hI]
  ring

/-- The increments of the drift martingale are bounded by `2` for `p ∈ [1/2, 1]`. -/
theorem abs_mart_inc_le (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (n : ℕ) (i : Fin N) (ω : Ω) :
    |MartingaleLimit.inc (fun k ω => Swarm.mart p X m k ω i) n ω| ≤ 2 := by
  classical
  rw [MartingaleLimit.inc_apply, mart_succ_sub]
  have hstep : |((X (n + 1) ω i - X n ω i : ℤ) : ℝ)| = 1 := by
    rcases Swarm.abs_step_of_law hlaw n ω i with h | h <;> rw [h] <;> norm_num
  have hI : |Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω| ≤ 1 := by
    by_cases h : ω ∈ Swarm.excitedSet X m n i
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]; norm_num
  have hc : |2 * p - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc |((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
        - (2 * p - 1) * Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω|
      ≤ |((X (n + 1) ω i - X n ω i : ℤ) : ℝ)|
        + |(2 * p - 1) * Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω| :=
        abs_sub _ _
    _ = 1 + |2 * p - 1| * |Set.indicator (Swarm.excitedSet X m n i) (1 : Ω → ℝ) ω| := by
        rw [hstep, abs_mul]
    _ ≤ 1 + 1 * 1 := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul hc hI (abs_nonneg _) (by linarith)
    _ = 2 := by norm_num

/-- **The paper's martingale `(mart)` as a genuine nested-filtration martingale.** -/
theorem mart_martingale [IsProbabilityMeasure μ]
    (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (i : Fin N) :
    Martingale (fun n ω => Swarm.mart p X m n ω i) 𝓕 μ := by
  refine martingale_of_setIntegral_eq_succ (fun n => (measurable_mart_filt hlaw n i).stronglyMeasurable)
    (fun n => integrable_mart_filt hlaw n i) (fun n A hA => ?_)
  have h1 : IntegrableOn (fun ω => Swarm.mart p X m (n + 1) ω i) A μ :=
    (integrable_mart_filt hlaw (n + 1) i).integrableOn
  have h2 : IntegrableOn (fun ω => Swarm.mart p X m n ω i) A μ :=
    (integrable_mart_filt hlaw n i).integrableOn
  have hsub : ∫ ω in A, (Swarm.mart p X m (n + 1) ω i - Swarm.mart p X m n ω i) ∂μ
      = ∫ ω in A, Swarm.mart p X m (n + 1) ω i ∂μ
        - ∫ ω in A, Swarm.mart p X m n ω i ∂μ := integral_sub h1 h2
  have hzero := Swarm.mart_increment hlaw n i hA
  linarith [hsub.symm.trans hzero]

/-- The drift martingale starts at `0`. -/
theorem mart_zero (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (i : Fin N) (ω : Ω) :
    Swarm.mart p X m 0 ω i = 0 := by
  classical
  have hX0 : X 0 ω i = 0 := hlaw.2.1 ω i
  simp [Swarm.mart, Swarm.pos, Swarm.excCount, hX0]

/-- **`max_{t<=n} |M^i_t| = o(n)`** for the actual drift martingale. -/
theorem ae_mart_max_div [IsProbabilityMeasure μ]
    (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t ≤ n, |Swarm.mart p X m t ω i| ≤ ε * n :=
  ae_max_div_of_bounded_inc (C := 2) (mart_martingale hlaw i) (mart_zero hlaw i) (by norm_num)
    (fun n ω => abs_mart_inc_le hlaw hp1 hp2 n i ω)

/-- **Oscillation statement `max(M^i_t) - X^i_t = o(n)`** (paper `(prelim)`), i.e. the
`hosc` premise of the verified covering argument. -/
theorem hosc_of_law [IsProbabilityMeasure μ]
    (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto
      (fun n => ((SwarmSpeed.runMax (fun t => X t ω i) n : ℝ) - (X n ω i : ℝ)) / n)
      atTop (𝓝 0) := by
  classical
  have hc : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hpoint : ∀ i : Fin N, ∀ᵐ ω ∂μ, Tendsto
      (fun n => ((SwarmSpeed.runMax (fun t => X t ω i) n : ℝ) - (X n ω i : ℝ)) / n)
      atTop (𝓝 0) := by
    intro i
    exact ae_hosc_of_martingale (μ := μ) (ℱ := 𝓕)
      (u := fun t ω => X t ω i) (M := fun t ω => Swarm.mart p X m t ω i)
      (E := fun t ω => Swarm.excCount X m t ω i) (c := 2 * p - 1)
      (mart_martingale hlaw i) (mart_zero hlaw i) (by norm_num)
      (fun n ω => abs_mart_inc_le hlaw hp1 hp2 n i ω) hc
      (fun n ω => by simp only [Swarm.mart, Swarm.pos]; ring)
      (fun t n ω ht => excCount_mono t n ht ω i)
  exact ae_all_iff.mpr hpoint

end SwarmHosc
