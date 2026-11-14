/-
  The **one-step drift** at the heart of the crossing estimate (eq. (cross)) and of the
  occupation bound of *Swarming of interacting excited random walks*
  (main_1d_revised.tex, §2.2).

  Setting: a filtered probability space `(Ω, m0, μ)` with a filtration `ℱ`, an adapted
  `ℕ`-valued nearest-neighbour walker `X` confined to the window `[b0, b1+1]` and absorbed at
  the two boundary levels `b0` and `b1+1` (this is the *stopped* walker of the paper), a fixed
  weight sequence `w : ℕ → ℝ` with values in `[1/2, 1)`, and the domination hypothesis
  (paper eq. (dominate), for a *deterministic* environment)

    `w (X_n)  ≤  P(X_{n+1} = X_n + 1 | ℱ_n)`   a.s. on `{b0 < X_n ≤ b1}`.

  Conclusion: the scale function `f = sc w b0 b1` of `Scale.lean` satisfies

    `f (X_n)  ≤  E[f (X_{n+1}) | ℱ_n]`   a.s.

  i.e. `f ∘ X` is a submartingale (`submartingale_nat` then applies).  The proof is the
  paper's computation:  `E[f(X_{n+1})|ℱ_n] = f(x) + (P_n - w x)(f(x+1)-f(x-1))`, whose
  second term is nonnegative because `P_n ≥ w x` and `f` is nondecreasing, and which vanishes
  on the interior exactly because `f` solves the Poisson equation (the harmonic identity of
  `Scale.lean`).

  This isolates the `condExp` manipulation; what is *not* done here is the passage to the
  hitting probability (optional stopping with `Submartingale.expected_stoppedValue_mono` and
  the final `≤ 1 - f(b1)` bound), nor the conditional application to a random environment.
-/
import Swarm.Imports
import Swarm.Transience.Scale

open MeasureTheory Filter
open scoped Topology

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- `stepRight X n` is `1` on the event that the walker steps right at time `n`. -/
noncomputable def stepRight (X : ℕ → Ω → ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => if X (n + 1) ω = X n ω + 1 then 1 else 0

/-- `inside X b0 b1 n` is `1` on the event `{b0 < X_n ≤ b1}` (the interior of the window). -/
noncomputable def inside (X : ℕ → Ω → ℕ) (b0 b1 n : ℕ) : Ω → ℝ :=
  fun ω => if b0 < X n ω ∧ X n ω ≤ b1 then 1 else 0

/-- `f(X_n+1) - f(X_n-1)`, the coefficient of `(P_n - 1/2)` in the drift computation,
clamped to `0` outside the region where both arguments lie in `[0, b1+1]`. -/
noncomputable def scaleDelta (w : ℕ → ℝ) (b0 b1 : ℕ) (X : ℕ → Ω → ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => if X n ω ≤ b1 then sc w b0 b1 (X n ω + 1) - sc w b0 b1 (X n ω - 1) else 0

/-- `f(X_n-1) - f(X_n)`, the drift correction, clamped as in `scaleDelta`. -/
noncomputable def scaleBack (w : ℕ → ℝ) (b0 b1 : ℕ) (X : ℕ → Ω → ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => if 1 ≤ X n ω then sc w b0 b1 (X n ω - 1) - sc w b0 b1 (X n ω) else 0

section Bounds

variable {w : ℕ → ℝ} {b0 b1 : ℕ} {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℕ}

lemma measurable_of_countable_sc (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1) :
    Measurable (sc w b0 b1) := measurable_of_countable _

lemma norm_sc_le_one (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
    {z : ℕ} (hz : z ≤ b1 + 1) : ‖sc w b0 b1 z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [sc_nonneg hlo hhi hb z], sc_le_one hlo hhi hb hz⟩

lemma norm_sc_le_one' (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
    {z : ℕ} (hz : z ≤ b1 + 1) : |sc w b0 b1 z| ≤ 1 := by
  rw [← Real.norm_eq_abs]
  exact norm_sc_le_one hlo hhi hb hz

/-- Measurability of `f ∘ X_n` with respect to `ℱ n`. -/
lemma measurable_sc_comp (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
    (hX : ∀ n, Measurable[ℱ n] (X n)) (n : ℕ) :
    Measurable[ℱ n] (fun ω => sc w b0 b1 (X n ω)) :=
  (measurable_of_countable_sc hlo hhi hb).comp (hX n)

/-- Integrability of `f ∘ X_n` when the walker stays in the window. -/
lemma integrable_sc_comp [IsFiniteMeasure μ] (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1)
    (hb : b0 ≤ b1) (hX : ∀ n, Measurable[ℱ n] (X n))
    {n : ℕ} (hr : ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1) :
    Integrable (fun ω => sc w b0 b1 (X n ω)) μ := by
  have hm : Measurable (fun ω => sc w b0 b1 (X n ω)) :=
    (measurable_sc_comp hlo hhi hb hX n).mono (ℱ.le n) le_rfl
  exact Integrable.of_bound hm.aestronglyMeasurable 1
    (by filter_upwards [hr] with ω hω using norm_sc_le_one hlo hhi hb hω)

end Bounds

section Step

variable [IsProbabilityMeasure μ] {w : ℕ → ℝ} {b0 b1 : ℕ} {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℕ}

variable (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
  (hX : ∀ n, Measurable[ℱ n] (X n))
  (hrange : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1)

include hlo hhi hb hX hrange

omit hlo hhi hb hrange in
lemma measurable_stepRight (n : ℕ) : Measurable[ℱ (n + 1)] (stepRight X n) := by
  unfold stepRight
  refine Measurable.ite ?_ measurable_const measurable_const
  have h1 : Measurable[ℱ (n + 1)] (X (n + 1)) := hX (n + 1)
  have h2 : Measurable[ℱ (n + 1)] (fun ω => X n ω + 1) :=
    ((hX n).mono (ℱ.mono (Nat.le_succ n)) le_rfl).add_const 1
  have hpair : Measurable[ℱ (n + 1)] (fun ω => (X (n + 1) ω, X n ω + 1)) :=
    Measurable.prod (by simpa using h1) (by simpa using h2)
  have hc : MeasurableSet ({p : ℕ × ℕ | p.1 = p.2}) :=
    Set.Countable.measurableSet (Set.Countable.mono (Set.subset_univ _) Set.countable_univ)
  have hset : MeasurableSet[ℱ (n + 1)] {ω | X (n + 1) ω = X n ω + 1} := hpair hc
  exact hset

omit hlo hhi hb hrange in
lemma measurable_inside (n : ℕ) : Measurable[ℱ n] (inside X b0 b1 n) := by
  unfold inside
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_const (hX n)) |>.inter (measurableSet_le (hX n) measurable_const)

omit hrange in
lemma measurable_scaleDelta (n : ℕ) : Measurable[ℱ n] (scaleDelta w b0 b1 X n) := by
  unfold scaleDelta
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (hX n) measurable_const
  · exact ((measurable_of_countable_sc hlo hhi hb).comp ((hX n).add_const 1)).sub
      ((measurable_of_countable_sc hlo hhi hb).comp ((hX n).sub_const 1))

omit hrange in
lemma measurable_scaleBack (n : ℕ) : Measurable[ℱ n] (scaleBack w b0 b1 X n) := by
  unfold scaleBack
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (hX n)
  · exact ((measurable_of_countable_sc hlo hhi hb).comp ((hX n).sub_const 1)).sub
      ((measurable_of_countable_sc hlo hhi hb).comp (hX n))


/-! ### Boundedness of the pieces -/

omit hlo hhi hb hX hrange in
lemma norm_stepRight_le (n : ℕ) (ω : Ω) : ‖stepRight X n ω‖ ≤ 1 := by
  unfold stepRight
  split_ifs <;> norm_num

omit hlo hhi hb hX hrange in
lemma norm_inside_le (n : ℕ) (ω : Ω) : ‖inside X b0 b1 n ω‖ ≤ 1 := by
  unfold inside
  split_ifs <;> norm_num

omit hX hrange in
lemma norm_scaleDelta_le (n : ℕ) {ω : Ω} (hr : X n ω ≤ b1 + 1) :
    ‖scaleDelta w b0 b1 X n ω‖ ≤ 2 := by
  unfold scaleDelta
  split_ifs with h
  · have h1 : X n ω + 1 ≤ b1 + 1 := by omega
    have h2 : X n ω - 1 ≤ b1 + 1 := by omega
    have h3 := norm_sc_le_one hlo hhi hb h1
    have h4 := norm_sc_le_one hlo hhi hb h2
    calc ‖sc w b0 b1 (X n ω + 1) - sc w b0 b1 (X n ω - 1)‖
        ≤ ‖sc w b0 b1 (X n ω + 1)‖ + ‖sc w b0 b1 (X n ω - 1)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ ≤ 2 := by norm_num
  · norm_num

omit hX hrange in
lemma norm_scaleBack_le (n : ℕ) {ω : Ω} (hr : X n ω ≤ b1 + 1) :
    ‖scaleBack w b0 b1 X n ω‖ ≤ 2 := by
  unfold scaleBack
  split_ifs with h
  · have h1 : X n ω - 1 ≤ b1 + 1 := by omega
    have h2 := norm_sc_le_one hlo hhi hb h1
    have h3 := norm_sc_le_one hlo hhi hb hr
    calc ‖sc w b0 b1 (X n ω - 1) - sc w b0 b1 (X n ω)‖
        ≤ ‖sc w b0 b1 (X n ω - 1)‖ + ‖sc w b0 b1 (X n ω)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ ≤ 2 := by norm_num
  · norm_num

/-! ### The pointwise identity -/

omit hlo hhi hb hX hrange in
/-- The pointwise computation behind the drift: on the interior the scale function's increment
is `R·(f(x+1)-f(x-1)) + (f(x-1)-f(x))`, and at the absorbing boundary the walker does not
move, so both sides agree. -/
lemma sc_step_identity (n : ℕ) {ω : Ω}
    (hstep : (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω)) :
    sc w b0 b1 (X (n + 1) ω) = sc w b0 b1 (X n ω) + inside X b0 b1 n ω *
      (stepRight X n ω * scaleDelta w b0 b1 X n ω + scaleBack w b0 b1 X n ω) := by
  rcases hstep with ⟨hi1, hi2, hs⟩ | hb
  · have hin : inside X b0 b1 n ω = 1 := by
      simp only [inside]; rw [if_pos ⟨hi1, hi2⟩]
    have hdel : scaleDelta w b0 b1 X n ω
        = sc w b0 b1 (X n ω + 1) - sc w b0 b1 (X n ω - 1) := by
      simp only [scaleDelta]; rw [if_pos hi2]
    have hback : scaleBack w b0 b1 X n ω
        = sc w b0 b1 (X n ω - 1) - sc w b0 b1 (X n ω) := by
      simp only [scaleBack]; rw [if_pos (by omega : 1 ≤ X n ω)]
    rcases hs with hs | hs
    · have hsr : stepRight X n ω = 1 := by
        simp only [stepRight]; rw [if_pos hs]
      rw [hs, hin, hsr, hdel, hback]; ring
    · have hval : X (n + 1) ω = X n ω - 1 := by omega
      have hsr : stepRight X n ω = 0 := by
        simp only [stepRight]
        rw [if_neg (by omega : ¬ (X (n + 1) ω = X n ω + 1))]
      rw [hval, hin, hsr, hdel, hback]; ring
  · have hnin : inside X b0 b1 n ω = 0 := by
      simp only [inside]
      rw [if_neg]
      intro hcon
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · omega
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, hnin]; ring
    · rw [h2, hnin]; ring


/-! ### Integrability of the pieces -/

omit hlo hhi hb hrange in
lemma measurable_stepRight' (n : ℕ) : Measurable (stepRight X n) :=
  (measurable_stepRight hX n).mono (ℱ.le (n + 1)) le_rfl

omit hlo hhi hb hrange in
lemma measurable_inside' (n : ℕ) : Measurable (inside X b0 b1 n) :=
  (measurable_inside hX n).mono (ℱ.le n) le_rfl

omit hrange in
lemma measurable_scaleDelta' (n : ℕ) : Measurable (scaleDelta w b0 b1 X n) :=
  (measurable_scaleDelta hlo hhi hb hX n).mono (ℱ.le n) le_rfl

omit hrange in
lemma measurable_scaleBack' (n : ℕ) : Measurable (scaleBack w b0 b1 X n) :=
  (measurable_scaleBack hlo hhi hb hX n).mono (ℱ.le n) le_rfl

omit hlo hhi hb hrange in
lemma integrable_stepRight (n : ℕ) : Integrable (stepRight X n) μ :=
  Integrable.of_bound (measurable_stepRight' hX n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => norm_stepRight_le (X := X) n ω)

lemma integrable_scaleDelta (n : ℕ) : Integrable (scaleDelta w b0 b1 X n) μ :=
  Integrable.of_bound (measurable_scaleDelta' hlo hhi hb hX n).aestronglyMeasurable 2
    (by filter_upwards [hrange n] with ω hω using norm_scaleDelta_le hlo hhi hb n hω)

lemma integrable_scaleBack (n : ℕ) : Integrable (scaleBack w b0 b1 X n) μ :=
  Integrable.of_bound (measurable_scaleBack' hlo hhi hb hX n).aestronglyMeasurable 2
    (by filter_upwards [hrange n] with ω hω using norm_scaleBack_le hlo hhi hb n hω)

lemma integrable_stepRight_mul_delta (n : ℕ) :
    Integrable (fun ω => stepRight X n ω * scaleDelta w b0 b1 X n ω) μ :=
  Integrable.of_bound
    ((measurable_stepRight' hX n).mul (measurable_scaleDelta' hlo hhi hb hX n)).aestronglyMeasurable
    2 (by
      filter_upwards [hrange n] with ω hω
      rw [norm_mul]
      calc ‖stepRight X n ω‖ * ‖scaleDelta w b0 b1 X n ω‖ ≤ 1 * 2 := by
            apply mul_le_mul (norm_stepRight_le (X := X) n ω) (norm_scaleDelta_le hlo hhi hb n hω)
              (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num)

lemma integrable_inside_mul (n : ℕ) :
    Integrable (fun ω => inside X b0 b1 n ω *
      (stepRight X n ω * scaleDelta w b0 b1 X n ω + scaleBack w b0 b1 X n ω)) μ :=
  Integrable.of_bound
    ((measurable_inside' hX n).mul
      (((measurable_stepRight' hX n).mul (measurable_scaleDelta' hlo hhi hb hX n)).add
        (measurable_scaleBack' hlo hhi hb hX n))).aestronglyMeasurable
    4 (by
      filter_upwards [hrange n] with ω hω
      rw [norm_mul]
      have h1 : ‖inside X b0 b1 n ω‖ ≤ 1 := norm_inside_le (X := X) (b0 := b0) (b1 := b1) n ω
      have h3 : ‖stepRight X n ω * scaleDelta w b0 b1 X n ω‖ ≤ 2 := by
        rw [norm_mul]
        calc ‖stepRight X n ω‖ * ‖scaleDelta w b0 b1 X n ω‖ ≤ 1 * 2 := by
              apply mul_le_mul (norm_stepRight_le (X := X) n ω) (norm_scaleDelta_le hlo hhi hb n hω)
                (norm_nonneg _) (by norm_num)
          _ = 2 := by norm_num
      have h4 : ‖scaleBack w b0 b1 X n ω‖ ≤ 2 := norm_scaleBack_le hlo hhi hb n hω
      have h2 : ‖stepRight X n ω * scaleDelta w b0 b1 X n ω + scaleBack w b0 b1 X n ω‖
          ≤ 1 * 2 + 2 := by
        refine le_trans (norm_add_le _ _) ?_
        linarith
      calc ‖inside X b0 b1 n ω‖ *
          ‖stepRight X n ω * scaleDelta w b0 b1 X n ω + scaleBack w b0 b1 X n ω‖
          ≤ 1 * (1 * 2 + 2) := by
            apply mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num)

/-! ### The one-step drift -/

/-- **The one-step submartingale drift for the scale function** (the mechanism of both
eq. (cross) and the occupation bound): under the domination hypothesis (eq. (dominate)),
`f (X_n) ≤ E[f (X_{n+1}) | ℱ_n]`. -/
theorem condExp_sc_step
    (hstep : ∀ n, ∀ᵐ ω ∂μ,
      (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, w (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (n : ℕ) :
    ∀ᵐ ω ∂μ, sc w b0 b1 (X n ω) ≤ (μ[(fun ω => sc w b0 b1 (X (n + 1) ω)) | ℱ n]) ω := by
  classical
  -- names for the four local functions
  set I : Ω → ℝ := inside X b0 b1 n
  set R : Ω → ℝ := stepRight X n
  set D : Ω → ℝ := scaleDelta w b0 b1 X n
  set B : Ω → ℝ := scaleBack w b0 b1 X n
  have hmI : Measurable[ℱ n] I := measurable_inside hX n
  have hmD : Measurable[ℱ n] D := measurable_scaleDelta hlo hhi hb hX n
  have hmB : Measurable[ℱ n] B := measurable_scaleBack hlo hhi hb hX n
  have hIsc : Integrable (fun ω => sc w b0 b1 (X n ω)) μ :=
    integrable_sc_comp hlo hhi hb hX (hrange n)
  have hIRD : Integrable (fun ω => R ω * D ω) μ := integrable_stepRight_mul_delta hlo hhi hb hX hrange n
  have hIB : Integrable B μ := integrable_scaleBack hlo hhi hb hX hrange n
  have hIG : Integrable (fun ω => I ω * (R ω * D ω + B ω)) μ :=
    integrable_inside_mul hlo hhi hb hX hrange n
  have hIR : Integrable R μ := integrable_stepRight hX n
  have hIRD' : Integrable (fun ω => R ω * D ω + B ω) μ := hIRD.add hIB
  -- (1) the pointwise identity gives an a.e. equality of random variables
  have hpt : (fun ω => sc w b0 b1 (X (n + 1) ω)) =ᵐ[μ]
      (fun ω => sc w b0 b1 (X n ω) + I ω * (R ω * D ω + B ω)) := by
    filter_upwards [hstep n] with ω hω
    exact sc_step_identity (X := X) (w := w) (b0 := b0) (b1 := b1) n hω
  -- (2) the conditional-expectation identities, pointwise
  have e1 : ∀ᵐ ω ∂μ, (μ[(fun ω => sc w b0 b1 (X (n + 1) ω)) | ℱ n]) ω
      = (μ[(fun ω => sc w b0 b1 (X n ω) + I ω * (R ω * D ω + B ω)) | ℱ n]) ω :=
    condExp_congr_ae hpt
  have e2 : ∀ᵐ ω ∂μ, (μ[(fun ω => sc w b0 b1 (X n ω) + I ω * (R ω * D ω + B ω)) | ℱ n]) ω
      = (μ[(fun ω => sc w b0 b1 (X n ω)) | ℱ n]) ω
        + (μ[(fun ω => I ω * (R ω * D ω + B ω)) | ℱ n]) ω := by
    filter_upwards [condExp_add hIsc hIG (ℱ n)] with ω h
    exact h
  have e3 : ∀ᵐ ω ∂μ, (μ[(fun ω => I ω * (R ω * D ω + B ω)) | ℱ n]) ω
      = I ω * (μ[(fun ω => R ω * D ω + B ω) | ℱ n]) ω := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (m := ℱ n) hmI.stronglyMeasurable hIG
      hIRD'] with ω h
    exact h
  have e4a : ∀ᵐ ω ∂μ, (μ[R * D | ℱ n]) ω = (μ[R | ℱ n] * D) ω :=
    condExp_mul_of_stronglyMeasurable_right (m := ℱ n) hmD.stronglyMeasurable hIRD hIR
  have e4b : ∀ᵐ ω ∂μ, (μ[B | ℱ n]) ω = B ω := by
    filter_upwards [Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (m := ℱ n) (ℱ.le n) hmB.stronglyMeasurable hIB)] with ω h
    exact h
  have e4 : ∀ᵐ ω ∂μ, (μ[(fun ω => R ω * D ω + B ω) | ℱ n]) ω
      = (μ[R * D | ℱ n]) ω + (μ[B | ℱ n]) ω := by
    filter_upwards [condExp_add hIRD hIB (ℱ n)] with ω h
    exact h
  have e0 : ∀ᵐ ω ∂μ, (μ[(fun ω => sc w b0 b1 (X n ω)) | ℱ n]) ω = sc w b0 b1 (X n ω) := by
    filter_upwards [Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (m := ℱ n) (ℱ.le n)
        (Measurable.stronglyMeasurable (measurable_sc_comp hlo hhi hb hX n)) hIsc)] with ω h
    exact h
  have key : ∀ᵐ ω ∂μ, (μ[(fun ω => sc w b0 b1 (X (n + 1) ω)) | ℱ n]) ω
      = sc w b0 b1 (X n ω) + I ω * ((μ[R | ℱ n]) ω * D ω + B ω) := by
    filter_upwards [e1, e2, e3, e4, e4a, e4b, e0] with ω h1 h2 h3 h4 h4a h4b h0
    rw [h1, h2, h3, h4, h4a, h4b, h0]
    simp only [Pi.mul_apply]
  -- (3) nonnegativity of the correction
  have hnn : 0 ≤ᵐ[μ] (fun ω => I ω * ((μ[R | ℱ n]) ω * D ω + B ω)) := by
    filter_upwards [hstep n, hdom n] with ω hs hd
    rcases hs with ⟨hi1, hi2, -⟩ | ⟨hle, -⟩ | ⟨heq, -⟩
    · have hin : I ω = 1 := by
        simp only [I, inside]; rw [if_pos ⟨hi1, hi2⟩]
      have hdel : D ω = sc w b0 b1 (X n ω + 1) - sc w b0 b1 (X n ω - 1) := by
        simp only [D, scaleDelta]; rw [if_pos hi2]
      have hback : B ω = sc w b0 b1 (X n ω - 1) - sc w b0 b1 (X n ω) := by
        simp only [B, scaleBack]; rw [if_pos (by omega : 1 ≤ X n ω)]
      have hDnn : 0 ≤ D ω := by
        rw [hdel]
        exact sub_nonneg.mpr (sc_monotone hlo hhi hb (by omega))
      have hkey : w (X n ω) * D ω + B ω = 0 := by
        rw [hdel, hback]
        have hdr := sc_drift hlo hhi hb hi1 hi2 (w (X n ω))
        have hzero : (w (X n ω) - w (X n ω)) *
            (sc w b0 b1 (X n ω + 1) - sc w b0 b1 (X n ω - 1)) = 0 := by ring
        linarith [hdr, hzero]
      have hPD : w (X n ω) * D ω ≤ (μ[R | ℱ n]) ω * D ω :=
        mul_le_mul_of_nonneg_right hd hDnn
      simp only [Pi.zero_apply] at *
      rw [hin, one_mul]
      linarith [hPD, hkey]
    · have hin : I ω = 0 := by
        simp only [I, inside]; rw [if_neg]; intro hcon; omega
      simp only [Pi.zero_apply] at *
      rw [hin, zero_mul]
    · have hin : I ω = 0 := by
        simp only [I, inside]; rw [if_neg]; intro hcon; omega
      simp only [Pi.zero_apply] at *
      rw [hin, zero_mul]
  -- (4) conclude
  filter_upwards [key, hnn] with ω hk hn
  simp only [Pi.zero_apply] at hn
  rw [hk]
  linarith

/-- **`f ∘ X` is a submartingale.**  Immediate from the one-step drift and Mathlib's
`submartingale_nat`; optional stopping (`Submartingale.expected_stoppedValue_mono`) can now
be applied to it, which is the remaining step towards the crossing estimate eq. (cross). -/
theorem submartingale_sc
    (hstep : ∀ n, ∀ᵐ ω ∂μ,
      (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, w (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω) :
    Submartingale (fun n ω => sc w b0 b1 (X n ω)) ℱ μ :=
  submartingale_nat (fun n => (measurable_sc_comp hlo hhi hb hX n).stronglyMeasurable)
    (fun n => integrable_sc_comp hlo hhi hb hX (hrange n))
    (fun n => condExp_sc_step hlo hhi hb hX hrange hstep hdom n)


end Step

end SwarmSpeed
