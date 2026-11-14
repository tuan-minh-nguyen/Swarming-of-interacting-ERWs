/-
Area (h) — the upper half of the interval in the main theorem.

The paper's Theorem 1.1 asserts `v_{N,m}(p) in [kappa(m,p), 2p-1]`.  The campaign's
existing modules transfer the *lower* bound (`Renewal.le_div_of_le_ratio`); nothing
covered the upper bound `v <= 2p-1`.  The paper obtains it at the end of the proof of
Proposition `ball` from the martingale strong law applied to
`M_n^i = X_n^i - (2p-1) sum_{t<n} 1{excited}` (eq. (mart)).

The route taken here avoids the martingale strong law entirely and is elementary:

* the conditional transition rule gives the exact drift identity
  `∫ (X_{n+1}^i - X_n^i) = (2p-1) mu.real {excited at n}`;
* telescoping gives the *exact* mean identity
  `∫ X_n^i = (2p-1) sum_{t<n} P(excited at t) <= (2p-1) n`;
* `|X_n^i| <= n` makes `X_n^i/n` uniformly bounded by `1`, so dominated convergence
  turns a.s. convergence `X_n^i/n -> v` into `∫ X_n^i/n -> v`, whence `v <= 2p-1`.

In fact this proves more, `v = (2p-1) * lim_n (1/n) sum_{t<n} P(excited at t)`: the
speed is `2p-1` times the asymptotic excitation density.  That identity is the natural
"no-loss" counterpart of the paper's lower bound (which costs the factor
`a = 1 - (2p-1)(1-p)^{m-1}/p` in the marked-site comparison).
-/
import Swarm.Assembly.Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

namespace Swarm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
variable {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

/-! ### Measurability -/

lemma measurable_intToReal : Measurable fun z : ℤ => ((z : ℤ) : ℝ) := measurable_of_countable _

/-- The position of walker `i` at time `n`, as a real random variable. -/
noncomputable def pos (X : ℕ → Ω → Fin N → ℤ) (n : ℕ) (i : Fin N) : Ω → ℝ :=
  fun ω => ((X n ω i : ℤ) : ℝ)

lemma measurable_pos (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    Measurable (pos X n i) :=
  measurable_intToReal.comp ((h.1 n i).mono (𝓕.le n) le_rfl)

lemma measurable_upSet (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    MeasurableSet (upSet X n i) := by
  have h1 : Measurable fun ω => X n ω i := (h.1 n i).mono (𝓕.le n) le_rfl
  have h2 : Measurable fun ω => X (n + 1) ω i := (h.1 (n + 1) i).mono (𝓕.le (n + 1)) le_rfl
  exact measurableSet_eq_fun h2 (h1.add_const 1)

/-! ### The drift identity -/

/-- Pointwise: the integer jump equals `2 * 1{right jump} - 1`. -/
lemma step_eq_indicator (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (ω : Ω) (i : Fin N) :
    ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
      = 2 * Set.indicator (upSet X n i) (1 : Ω → ℝ) ω - 1 := by
  have hs := abs_step_of_law h n ω i
  have hmem : ω ∈ upSet X n i ↔ X (n + 1) ω i - X n ω i = 1 := by
    unfold upSet
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h' <;> omega
  rw [Set.indicator]
  by_cases h' : ω ∈ upSet X n i
  · have h1 : X (n + 1) ω i - X n ω i = 1 := hmem.1 h'
    norm_num [h', h1]
  · have h1 : X (n + 1) ω i - X n ω i = -1 := by
      rcases hs with hs | hs
      · exact absurd (hmem.2 hs) h'
      · exact hs
    norm_num [h', h1]

/-- **Drift identity.**  The mean jump of walker `i` at time `n` is
`(2p-1) P(excited at n)`; this is the unconditional form of the paper's `(mart)`. -/
theorem integral_step (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    ∫ ω, ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) ∂μ
      = (2 * p - 1) * μ.real (excitedSet X m n i) := by
  have hsm : MeasurableSet (upSet X n i) := measurable_upSet h n i
  have hstep : ∀ ω, ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
      = 2 * Set.indicator (upSet X n i) (1 : Ω → ℝ) ω - 1 :=
    fun ω => step_eq_indicator h n ω i
  rw [funext hstep]
  have hu : Integrable (fun ω => 2 * Set.indicator (upSet X n i) (1 : Ω → ℝ) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hsm).const_mul 2
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  rw [integral_sub hu h1, integral_const_mul, integral_indicator_one hsm]
  have hone : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp
  rw [hone]
  have hrule := h.2.2.2 n i Set.univ MeasurableSet.univ
  have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp
  rw [Set.univ_inter, Set.univ_inter, huniv] at hrule
  rw [hrule]
  ring

/-! ### The exact mean identity and the drift bound -/

lemma integrable_pos (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    Integrable (pos X n i) μ :=
  Integrable.of_bound (measurable_pos h n i).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by
      have hb : |((X n ω i : ℤ) : ℝ)| ≤ (n : ℝ) := by
        exact_mod_cast abs_le_time_of_law h n ω i
      simpa [pos, Real.norm_eq_abs] using hb)

lemma integrable_step (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    Integrable (fun ω => ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)) μ := by
  have hmeas : Measurable fun ω => ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) :=
    measurable_intToReal.comp
      (((h.1 (n + 1) i).mono (𝓕.le (n + 1)) le_rfl).sub ((h.1 n i).mono (𝓕.le n) le_rfl))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
  have hs := abs_step_of_law h n ω i
  have hcase : ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) = 1 ∨
      ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) = -1 := by
    rcases hs with hs | hs
    · left; rw [hs]; norm_num
    · right; rw [hs]; norm_num
  rcases hcase with h' | h' <;> rw [h', Real.norm_eq_abs] <;> norm_num

/-- **Exact mean of the position.** `∫ X_n^i = (2p-1) sum_{t<n} P(excited at t)`. -/
theorem integral_position_eq (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    ∫ ω, pos X n i ω ∂μ
      = (2 * p - 1) * ∑ t ∈ Finset.range n, μ.real (excitedSet X m t i) := by
  induction n with
  | zero =>
      have h0 : ∀ ω, pos X 0 i ω = 0 := fun ω => by simp [pos, h.2.1 ω i]
      simp only [h0, Finset.range_zero, Finset.sum_empty, mul_zero]
      simp
  | succ n ih =>
      have hsplit : ∫ ω, pos X (n + 1) i ω ∂μ
          = ∫ ω, pos X n i ω ∂μ
            + ∫ ω, ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) ∂μ := by
        rw [← integral_add (integrable_pos h n i) (integrable_step h n i)]
        congr 1
        ext ω
        simp only [pos]
        push_cast
        ring
      rw [hsplit, ih, integral_step h n i, Finset.sum_range_succ]
      ring

/-- **The mean is bounded by the drift.** -/
theorem integral_position_le (h : IsInteractingLaw 𝓕 μ X m p) (hp : 1 / 2 ≤ p) (n : ℕ)
    (i : Fin N) :
    ∫ ω, pos X n i ω ∂μ ≤ (2 * p - 1) * n := by
  rw [integral_position_eq h n i]
  have hle : ∑ t ∈ Finset.range n, μ.real (excitedSet X m t i) ≤ n := by
    calc ∑ t ∈ Finset.range n, μ.real (excitedSet X m t i) ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          exact measureReal_le_one
      _ = n := by simp
  have h2p : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  exact mul_le_mul_of_nonneg_left hle h2p

/-! ### The upper half of the interval -/

/-- `|X_n^i| <= n` turns into the uniform bound `|X_n^i / n| <= 1`. -/
lemma norm_div_le_one (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (ω : Ω) (i : Fin N) :
    ‖pos X n i ω / n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [pos, hn]
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
    have h1 : |pos X n i ω| ≤ (n : ℝ) := by
      simp only [pos]
      exact_mod_cast abs_le_time_of_law h n ω i
    rw [div_le_one (by positivity)]
    exact h1

/-- Dominated convergence for the normalised position. -/
lemma tendsto_integral_pos_div (h : IsInteractingLaw 𝓕 μ X m p) (i : Fin N) {v : ℝ}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v)) :
    Tendsto (fun n => ∫ ω, pos X n i ω / n ∂μ) atTop (𝓝 v) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) (ω : Ω) => pos X n i ω / n) (f := fun _ : Ω => v)
    (bound := fun _ : Ω => (1 : ℝ))
    (fun n => ((measurable_pos h n i).div_const (n : ℝ)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => Eventually.of_forall fun ω => norm_div_le_one h n ω i) hconv
  have hf : ∫ _ : Ω, v ∂μ = v := by simp
  rw [hf] at h
  exact h

/-- **`v <= 2p - 1`.**  The upper half of the paper's interval `[kappa(m,p), 2p-1]`.

Hypothesis `hconv` is the a.s. convergence of the normalised position of walker `i`
(proved for the actual process by the renewal argument of §3.3, i.e. by
`Renewal.renewal_strong_law` plus the concrete regeneration hypotheses); the proof below
is elementary and uses only the transition rule through `integral_position_le`. -/
theorem speed_le_two_p_sub_one (h : IsInteractingLaw 𝓕 μ X m p) (hp : 1 / 2 ≤ p) (i : Fin N)
    {v : ℝ} (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v)) :
    v ≤ 2 * p - 1 := by
  have hint := tendsto_integral_pos_div h i hconv
  have hbound : ∀ᶠ n : ℕ in atTop, ∫ ω, pos X n i ω / n ∂μ ≤ 2 * p - 1 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [integral_div]
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hle := integral_position_le h hp n i
    calc (∫ ω, pos X n i ω ∂μ) / n ≤ ((2 * p - 1) * n) / n :=
          div_le_div_of_nonneg_right hle hn'.le
      _ = 2 * p - 1 := by field_simp
  exact le_of_tendsto_of_tendsto hint tendsto_const_nhds hbound

/-- **The speed is `2p-1` times the asymptotic excitation density.**

This identifies `v_{N,m}(p)` exactly in terms of the mean excitation rate of a single
walker, and shows in particular that `v <= 2p-1`, with equality iff the walker is
excited on a set of full asymptotic density. -/
theorem speed_eq_excitation_density (h : IsInteractingLaw 𝓕 μ X m p) (i : Fin N) {v rho : ℝ}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v))
    (hrate : Tendsto (fun (n : ℕ) => (1 / (n : ℝ)) * ∑ t ∈ Finset.range n,
      μ.real (excitedSet X m t i)) atTop (𝓝 rho)) :
    v = (2 * p - 1) * rho := by
  have hint := tendsto_integral_pos_div h i hconv
  have hEq : ∀ n, ∫ ω, pos X n i ω / n ∂μ
      = (2 * p - 1) * ((1 / (n : ℝ)) * ∑ t ∈ Finset.range n,
          μ.real (excitedSet X m t i)) := by
    intro n
    rw [integral_div, integral_position_eq h n i]
    ring
  have hlim : Tendsto (fun (n : ℕ) => (2 * p - 1) * ((1 / (n : ℝ)) * ∑ t ∈ Finset.range n,
      μ.real (excitedSet X m t i))) atTop (𝓝 ((2 * p - 1) * rho)) :=
    tendsto_const_nhds.mul hrate
  rw [funext hEq] at hint
  exact tendsto_nhds_unique hint hlim

/-- **`0 <= v`.**  Companion of `speed_le_two_p_sub_one`: the limit speed is
nonnegative, and is `2p-1` times the asymptotic excitation density.  Hence the only
nontrivial half of the interval `[kappa(m,p), 2p-1]` is the positivity `v > 0`, i.e. the
ballistic lower bound of Proposition `ball`. -/
theorem speed_nonneg (h : IsInteractingLaw 𝓕 μ X m p) (hp : 1 / 2 ≤ p) (i : Fin N) {v rho : ℝ}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v))
    (hrate : Tendsto (fun (n : ℕ) => (1 / (n : ℝ)) * ∑ t ∈ Finset.range n,
      μ.real (excitedSet X m t i)) atTop (𝓝 rho)) :
    0 ≤ v := by
  have hv := speed_eq_excitation_density h i hconv hrate
  have hrho : 0 ≤ rho := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hrate (Eventually.of_forall ?_)
    intro n
    have h1 : (0 : ℝ) ≤ ∑ t ∈ Finset.range n, μ.real (excitedSet X m t i) :=
      Finset.sum_nonneg fun t _ => measureReal_nonneg
    have h2 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    exact mul_nonneg h2 h1
  rw [hv]
  exact mul_nonneg (by linarith) hrho

/-! ### Measurability of the excitation event -/

omit [IsProbabilityMeasure μ] in
lemma measurable_excitedSet (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) :
    MeasurableSet (excitedSet X m n i) := by
  have hX : ∀ (t : ℕ) (j : Fin N), Measurable fun ω => X t ω j :=
    fun t j => (h.1 t j).mono (𝓕.le t) le_rfl
  have hterm : ∀ (t : ℕ) (j : Fin N),
      Measurable fun ω => (if X t ω j = X n ω i then (1 : ℕ) else 0) := by
    intro t j
    exact Measurable.ite (measurableSet_eq_fun (hX t j) (hX n i)) measurable_const
      measurable_const
  have hsum : Measurable fun ω => ∑ j ∈ Finset.univ.erase i,
      ∑ t ∈ Finset.range (n + 1), (if X t ω j = X n ω i then (1 : ℕ) else 0) :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun t _ => hterm t j
  have hgoal : excitedSet X m n i = {ω | m ≤ ∑ j ∈ Finset.univ.erase i,
      ∑ t ∈ Finset.range (n + 1), (if X t ω j = X n ω i then (1 : ℕ) else 0)} := by
    ext ω
    simp [excitedSet, Excited, otherVisits, localTime]
  rw [hgoal]
  exact measurableSet_le measurable_const hsum

/-- The paper's martingale `M_n^i` of `\eqref{mart}`, as a real-valued process. -/
noncomputable def excCount (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω) (i : Fin N) : ℕ :=
  ∑ t ∈ Finset.range n, if Excited X m t ω i then 1 else 0

noncomputable def mart (p : ℝ) (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω) (i : Fin N) : ℝ :=
  pos X n i ω - (2 * p - 1) * (excCount X m n ω i : ℝ)

omit [IsProbabilityMeasure μ] in
lemma excCount_succ (n : ℕ) (ω : Ω) (i : Fin N) :
    excCount X m (n + 1) ω i
      = excCount X m n ω i + (if Excited X m n ω i then 1 else 0) := by
  rw [excCount, excCount, Finset.sum_range_succ]

/-- **The drift identity on a general past event** — the conditional form of `(mart)`:
`∫_A (X_{n+1}^i - X_n^i) = (2p-1) P(A ∩ {excited at n})` for every `A in F_n`. -/
theorem setIntegral_step (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) {A : Set Ω}
    (hA : MeasurableSet[𝓕 n] A) :
    ∫ ω in A, ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) ∂μ
      = (2 * p - 1) * μ.real (A ∩ excitedSet X m n i) := by
  have hsm : MeasurableSet (upSet X n i) := measurable_upSet h n i
  have hstep : ∀ ω, ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
      = 2 * Set.indicator (upSet X n i) (1 : Ω → ℝ) ω - 1 :=
    fun ω => step_eq_indicator h n ω i
  simp only [hstep]
  have hint1 : IntegrableOn (fun ω => 2 * Set.indicator (upSet X n i) (1 : Ω → ℝ) ω) A μ :=
    (((integrable_const (1 : ℝ)).indicator hsm).const_mul 2).integrableOn
  have hint2 : IntegrableOn (fun _ : Ω => (1 : ℝ)) A μ := (integrable_const 1).integrableOn
  rw [integral_sub hint1 hint2, integral_const_mul, setIntegral_one_eq_measureReal,
    setIntegral_indicator hsm]
  simp only [Pi.one_apply, setIntegral_one_eq_measureReal]
  have hrule := h.2.2.2 n i A hA
  rw [hrule]
  ring

/-- **The paper's `(mart)`: `M_n^i = X_n^i - (2p-1) sum_{t<n} 1{excited}` is a
martingale.**  Stated in the "zero mean increment over every past event" form, which is
the conditional-mean statement `E[M_{n+1}^i - M_n^i | F_n] = 0`. -/
theorem mart_increment (h : IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (i : Fin N) {A : Set Ω}
    (hA : MeasurableSet[𝓕 n] A) :
    ∫ ω in A, (mart p X m (n + 1) ω i - mart p X m n ω i) ∂μ = 0 := by
  have hexc : MeasurableSet (excitedSet X m n i) := measurable_excitedSet h n i
  classical
  have hstep : ∀ ω, mart p X m (n + 1) ω i - mart p X m n ω i
      = ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)
        - (2 * p - 1) * Set.indicator (excitedSet X m n i) (1 : Ω → ℝ) ω := by
    intro ω
    have hE1 : ((excCount X m (n + 1) ω i : ℕ) : ℝ)
        = (excCount X m n ω i : ℝ) + (if Excited X m n ω i then (1 : ℝ) else 0) := by
      rw [excCount_succ]; push_cast; ring
    have hP' : pos X (n + 1) i ω = pos X n i ω + ((X (n + 1) ω i - X n ω i : ℤ) : ℝ) := by
      simp only [pos]; push_cast; ring
    have hI : Set.indicator (excitedSet X m n i) (1 : Ω → ℝ) ω
        = (if Excited X m n ω i then (1 : ℝ) else 0) := by
      by_cases h : Excited X m n ω i <;> simp [Set.indicator, excitedSet, h]
    simp only [mart]
    rw [hE1, hP', hI]
    ring
  simp only [hstep]
  have h1 : IntegrableOn (fun ω => ((X (n + 1) ω i - X n ω i : ℤ) : ℝ)) A μ :=
    (integrable_step h n i).integrableOn
  have h2 : IntegrableOn
      (fun ω => (2 * p - 1) * Set.indicator (excitedSet X m n i) (1 : Ω → ℝ) ω) A μ :=
    (((integrable_const (1 : ℝ)).indicator hexc).const_mul (2 * p - 1)).integrableOn
  rw [integral_sub h1 h2, setIntegral_step h n i hA, integral_const_mul,
    setIntegral_indicator hexc]
  simp only [Pi.one_apply, setIntegral_one_eq_measureReal]
  ring

end Swarm
