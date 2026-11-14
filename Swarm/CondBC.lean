/-
# The conditional Borel–Cantelli passage of the initial-regeneration construction

Source: `attachments/improving-and-polishing-the-wcjf/main_1d.tex`, §"Regeneration and the
collective speed", end of the proof of Proposition `regen`
("It remains to construct an initial regeneration under `P`"):

* tightness gives `P(d_r → ∞) = 0` (`(tightlaw)`), hence almost surely some even `K ≥ 2` has
  `d_r ≤ K` for infinitely many record indices `r`;
* the force estimate `(force)` gives, on `{d_r ≤ K}`,
  `P(d_r ≤ K, Y_{r+1} ∈ F ∣ ℱ_{τ_r}) ≥ (1-p)^{N(K+1)}`;
* the joint event `{d_r ≤ K, Y_{r+1} ∈ F}` lies in `ℱ_{τ_{r+1}}`, so the conditional
  Borel–Cantelli lemma for the filtration `(ℱ_{τ_r})` yields infinitely many visits to `F`,
  and, taking the countable union over even `K`, infinitely many simultaneous record times
  almost surely.

This file formalises that passage exactly, at the level of an abstract filtration indexed by the
record index.  The two genuine stochastic inputs are *explicit hypotheses* and are **not** proved
here:
`hforce` (the paper's conditional force bound) and `hT` (the paper's tightness output).

Nothing here claims to be a proof of regeneration, of invariance, or of the common speed: it is
the frequency step only.  No `sorry`, no custom axioms.
-/
import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.Probability.Kernel.Basic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WCJF

namespace RegenBC

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Counting visits: divergence of the visit-count sums -/

/-- If `ω` lies in infinitely many of the sets `E n`, then the partial sums of the indicators of
`E` diverge to `+∞` at `ω`.

This is Mathlib's `Set.limsup_eq_tendsto_sum_indicator_atTop` combined with the description of
`limsup` as "frequently". -/
theorem tendsto_sum_indicator_atTop_of_frequently {E : ℕ → Set Ω} {ω : Ω}
    (h : ∃ᶠ n in atTop, ω ∈ E n) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (E k).indicator (fun _ => (1 : ℝ)) ω)
      atTop atTop := by
  have hmem : ω ∈ limsup E atTop := mem_limsup_iff_frequently_mem.mpr h
  have hset := Set.limsup_eq_tendsto_sum_indicator_atTop (α := Ω) (R := ℝ) zero_lt_one E
  rw [hset] at hmem
  exact hmem

/-! ### Conditional Borel–Cantelli in the shape of the paper's force bound -/

/-- **Conditional Borel–Cantelli lemma, quantitative form.**
Let `s` be a sequence of events with `s n` measurable at time `n`, and suppose that for some
`c > 0` the conditional probability of `s (n+1)` given time `n` dominates `c` on a family of
sets `E n`.  Then on the event that `E n` happens infinitely often, `s n` happens infinitely
often.

In the paper `s n = {Y_n ∈ F}`, `E n = {d_n ≤ K}`, and the bound on the *joint* event supplied
by `(force)` implies the hypothesis used here, since a conditional probability of a smaller
event is dominated by that of a larger one. -/
theorem ae_frequently_of_condExp_ge_indicator [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {s E : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) {c : ℝ} (hc : 0 < c)
    (hforce : ∀ᵐ ω ∂μ, ∀ n, c * (E n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[(s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω) :
    ∀ᵐ ω ∂μ, (∃ᶠ n in atTop, ω ∈ E n) → ∃ᶠ n in atTop, ω ∈ s n := by
  have hbc := ae_mem_limsup_atTop_iff (ℱ := ℱ) (s := s) μ hs
  filter_upwards [hbc, hforce] with ω hbcω hf hEω
  have hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n,
      (E k).indicator (fun _ => (1 : ℝ)) ω) atTop atTop :=
    tendsto_sum_indicator_atTop_of_frequently hEω
  have hcmp : ∀ n, c * (∑ k ∈ Finset.range n, (E k).indicator (fun _ => (1 : ℝ)) ω) ≤
      ∑ k ∈ Finset.range n, (μ[(s (k + 1)).indicator (fun _ => (1 : ℝ)) | ℱ k]) ω := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hf k
  have hdiv2 : Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (fun _ => (1 : ℝ)) | ℱ k]) ω) atTop atTop := by
    rw [tendsto_atTop_atTop] at hdiv ⊢
    intro b
    obtain ⟨i, hi⟩ := hdiv (b / c)
    refine ⟨i, fun a ha => ?_⟩
    have h1 : c * (b / c) ≤ c * (∑ k ∈ Finset.range a, (E k).indicator (fun _ => (1 : ℝ)) ω) :=
      mul_le_mul_of_nonneg_left (hi a ha) (le_of_lt hc)
    have h2 := hcmp a
    have h3 : c * (b / c) = b := by field_simp
    linarith
  exact mem_limsup_iff_frequently_mem.mp (hbcω.mpr hdiv2)

/-- The same statement with the countable union over the level `K` carried out; this is the
paper's "taking the countable union over even `K`". -/
theorem ae_frequently_of_force_and_bounded [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n))
    {lvl : ℕ → ℕ → Set Ω} {c : ℕ → ℝ} (hc : ∀ K, 0 < c K)
    (hforce : ∀ᵐ ω ∂μ, ∀ K n, c K * (lvl K n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[(s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω)
    (hbound : ∀ᵐ ω ∂μ, ∃ K, ∃ᶠ n in atTop, ω ∈ lvl K n) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ s n := by
  have hall : ∀ K, ∀ᵐ ω ∂μ, (∃ᶠ n in atTop, ω ∈ lvl K n) → ∃ᶠ n in atTop, ω ∈ s n :=
    fun K => ae_frequently_of_condExp_ge_indicator (μ := μ) (ℱ := ℱ) (E := lvl K) hs (hc K)
      (hforce.mono fun ω hω n => hω K n)
  filter_upwards [MeasureTheory.ae_all_iff.2 hall, hbound] with ω hω hb
  obtain ⟨K, hK⟩ := hb
  exact hω K hK

/-! ### From the paper's tightness output to an infinitely often bounded level -/

/-- A sequence of levels that does not tend to infinity is infinitely often bounded.  This is the
order-theoretic content of "`P(d_r → ∞) = 0` implies that, almost surely, some `K` has
`d_r ≤ K` infinitely often". -/
theorem exists_frequently_le_of_not_tendsto {u : ℕ → ℕ} (h : ¬ Tendsto u atTop atTop) :
    ∃ K, ∃ᶠ n in atTop, u n ≤ K := by
  rw [tendsto_atTop_atTop] at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [frequently_atTop]
  intro i
  obtain ⟨a, hai, hlt⟩ := hb i
  exact ⟨a, hai, by omega⟩

/-- The even-level form used in the paper (`K` even, `K ≥ 2`). -/
theorem exists_even_frequently_le_of_not_tendsto {u : ℕ → ℕ}
    (h : ¬ Tendsto u atTop atTop) :
    ∃ K, Even K ∧ 2 ≤ K ∧ ∃ᶠ n in atTop, u n ≤ K := by
  obtain ⟨K, hK⟩ := exists_frequently_le_of_not_tendsto h
  refine ⟨2 * max K 1, even_two_mul _, by omega, hK.mono ?_⟩
  intro n hn
  omega

/-- **The paper's initial step, assembled.**  Assume

* `hT` : the record depth does not tend to infinity almost surely — the paper's tightness output
  `P(d_r → ∞) = 0`;
* `hforce` : the conditional force bound `c_K · 1_{d_r ≤ K} ≤ P(Y_{r+1} ∈ F ∣ ℱ_r)` for every
  record index `r`.

Then `F` is visited infinitely often almost surely. -/
theorem ae_frequently_of_force_of_tight [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {d : ℕ → Ω → ℕ} {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) {c : ℕ → ℝ} (hc : ∀ K, 0 < c K)
    (hforce : ∀ᵐ ω ∂μ, ∀ K n, c K * (if d n ω ≤ K then (1 : ℝ) else 0) ≤
      (μ[(s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω)
    (hT : ∀ᵐ ω ∂μ, ¬ Tendsto (fun n => d n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ s n := by
  refine ae_frequently_of_force_and_bounded (μ := μ) (lvl := fun K n => {ω | d n ω ≤ K})
    hs hc ?_ ?_
  · filter_upwards [hforce] with ω hω K n
    have hω' := hω K n
    by_cases h : d n ω ≤ K
    · rw [if_pos h, mul_one] at hω'
      rw [Set.indicator_of_mem (show ω ∈ {ω : Ω | d n ω ≤ K} from h), mul_one]
      exact hω'
    · rw [if_neg h, mul_zero] at hω'
      rw [Set.indicator_of_notMem (show ω ∉ {ω : Ω | d n ω ≤ K} from h), mul_zero]
      exact hω'
  · filter_upwards [hT] with ω hω
    obtain ⟨K, hK⟩ := exists_frequently_le_of_not_tendsto hω
    exact ⟨K, hK⟩


/-! ### Monotonicity: the paper's joint-event bound implies the hypothesis -/

/-- Conditional probabilities of indicators are monotone in the event.  This is what converts the
paper's bound on the *joint* event `{d_r ≤ K, Y_{r+1} ∈ F}` into a bound on `{Y_{r+1} ∈ F}`. -/
theorem condExp_indicator_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {n : ℕ} {t s : Set Ω}
    (ht : MeasurableSet t) (hs : MeasurableSet s) (h : t ⊆ s) :
    μ[t.indicator (fun _ => (1 : ℝ)) | ℱ n] ≤ᵐ[μ]
      μ[s.indicator (fun _ => (1 : ℝ)) | ℱ n] := by
  refine condExp_mono ?_ ?_ (Eventually.of_forall fun ω => ?_)
  · exact (integrable_const (1 : ℝ)).indicator ht
  · exact (integrable_const (1 : ℝ)).indicator hs
  · by_cases h1 : ω ∈ t
    · have h2 : ω ∈ s := h h1
      simp [Set.indicator, h1, h2]
    · have e1 : t.indicator (fun _ => (1 : ℝ)) ω = 0 := by simp [Set.indicator, h1]
      rw [e1]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω

/-- **Paper form of the force hypothesis.**  If for every record index `n` the conditional
probability of the *joint* event `lvl K n ∩ {Y_{n+1} ∈ F}` dominates `c K` on `lvl K n`, then the
hypothesis of `ae_frequently_of_force_and_bounded` holds. -/
theorem force_of_joint_force [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n))
    {lvl : ℕ → ℕ → Set Ω} (hlvl : ∀ K n, MeasurableSet[ℱ n] (lvl K n)) {c : ℕ → ℝ}
    (h : ∀ᵐ ω ∂μ, ∀ K n, c K * (lvl K n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[(lvl K n ∩ s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω) :
    ∀ᵐ ω ∂μ, ∀ K n, c K * (lvl K n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[(s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω := by
  have hmono : ∀ K n, μ[(lvl K n ∩ s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n] ≤ᵐ[μ]
      μ[(s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n] := by
    intro K n
    have h1 : MeasurableSet (lvl K n) := ℱ.le n (lvl K n) (hlvl K n)
    have h2 : MeasurableSet (s (n + 1)) := ℱ.le (n + 1) (s (n + 1)) (hs (n + 1))
    exact condExp_indicator_le (ℱ := ℱ) (n := n) (h1.inter h2) h2 Set.inter_subset_right
  filter_upwards [h, MeasureTheory.ae_all_iff.2 fun K => MeasureTheory.ae_all_iff.2 fun n =>
    hmono K n] with ω hω hmon
  intro K n
  exact (hω K n).trans (hmon K n)

/-- **The paper's initial step with the joint-event force bound**, in the exact shape of
`(force)`: on `{d_r ≤ K}`, the conditional probability of `{d_r ≤ K, Y_{r+1} ∈ F}` is at least
`c K`.  With the tightness output `hT` (`P(d_r → ∞) = 0`) this yields infinitely many visits to
`F` almost surely. -/
theorem ae_frequently_of_joint_force_of_bounded [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n))
    {lvl : ℕ → ℕ → Set Ω} (hlvl : ∀ K n, MeasurableSet[ℱ n] (lvl K n)) {c : ℕ → ℝ}
    (hc : ∀ K, 0 < c K)
    (hforce : ∀ᵐ ω ∂μ, ∀ K n, c K * (lvl K n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[(lvl K n ∩ s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω)
    (hbound : ∀ᵐ ω ∂μ, ∃ K, ∃ᶠ n in atTop, ω ∈ lvl K n) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ s n :=
  ae_frequently_of_force_and_bounded hs hc (force_of_joint_force hs hlvl hforce) hbound

/-- The joint-force version with the depth functional `d` and with the tightness output as the
only level hypothesis: this is literally the paper's passage from `(tightlaw)` and `(force)` to
"almost surely there are infinitely many simultaneous record times". -/
theorem ae_frequently_of_joint_force_of_tight [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {d : ℕ → Ω → ℕ} (hd : ∀ n, Measurable[ℱ n] (d n))
    {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n)) {c : ℕ → ℝ}
    (hc : ∀ K, 0 < c K)
    (hforce : ∀ᵐ ω ∂μ, ∀ K n, c K * (if d n ω ≤ K then (1 : ℝ) else 0) ≤
      (μ[({ω | d n ω ≤ K} ∩ s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω)
    (hT : ∀ᵐ ω ∂μ, ¬ Tendsto (fun n => d n ω) atTop atTop) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ s n := by
  refine ae_frequently_of_joint_force_of_bounded (μ := μ) (ℱ := ℱ) (c := c)
    (lvl := fun K n => {ω : Ω | d n ω ≤ K}) hs (fun K n => hd n measurableSet_Iic) hc ?_ ?_
  · filter_upwards [hforce] with ω hω K n
    have h := hω K n
    by_cases hdK : d n ω ≤ K
    · rw [if_pos hdK, mul_one] at h
      rw [Set.indicator_of_mem (show ω ∈ {ω : Ω | d n ω ≤ K} from hdK), mul_one]
      exact h
    · rw [if_neg hdK, mul_zero] at h
      rw [Set.indicator_of_notMem (show ω ∉ {ω : Ω | d n ω ≤ K} from hdK), mul_zero]
      exact h
  · filter_upwards [hT] with ω hω
    obtain ⟨K, hK⟩ := exists_frequently_le_of_not_tendsto hω
    exact ⟨K, hK⟩


/-! ### Kernel interface: from a kernel force estimate to the force hypothesis

The paper's `(force)` is a statement about the *transition kernel* `P` of the record chain.  The
repository proves exactly that kernel form for the stopped record kernel `hitKKernel`, with the
paper's constant `(1-p)^{N(2K+1)}` (`SimJump.RecKernel.hitKInf_srSet_ge`, used by
`InvariantPositivity.step_iterate_srSet_ge`).  What the paper's Borel–Cantelli step consumes is
the *conditional-along-the-chain* form.  The following interface lemma states that the kernel
form suffices as soon as the one-step Markov identity
`P(Y_{n+1} ∈ F ∣ ℱ_n) = κ (Y_n) F` is available for the path law; for the actual record chain
that identity is the `(recmark)` Markov property of the Ionescu–Tulcea path law
(`Mathlib`'s `ProbabilityTheory.Kernel.condDistrib_trajMeasure`), not an extra probabilistic
input. -/

/-- **Kernel force estimate + one-step Markov identity give the paper's frequency step.** -/
theorem ae_frequently_mem_of_kernel_force [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α] {ℱ : Filtration ℕ m0}
    {Y : ℕ → Ω → α} (hY : ∀ n, Measurable[ℱ n] (Y n))
    {F : Set α} (hF : MeasurableSet F) {κ : Kernel α α} [IsMarkovKernel κ]
    {Kset : ℕ → Set α} {c : ℕ → ℝ≥0∞}
    (hforce : ∀ K y, y ∈ Kset K → c K ≤ κ y F)
    (hstep : ∀ n, μ[Set.indicator {ω : Ω | Y (n + 1) ω ∈ F} (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      (fun ω => (κ (Y n ω) F).toReal))
    (hc : ∀ K, 0 < (c K).toReal)
    {lvl : ℕ → ℕ → Set Ω} (hlvl : ∀ K n, lvl K n ⊆ {ω | Y n ω ∈ Kset K})
    (hbound : ∀ᵐ ω ∂μ, ∃ K, ∃ᶠ n in atTop, ω ∈ lvl K n) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, Y n ω ∈ F := by
  have hs : ∀ n, MeasurableSet[ℱ n] {ω | Y n ω ∈ F} := fun n => hY n hF
  have hcond : ∀ᵐ ω ∂μ, ∀ K n, (c K).toReal * (lvl K n).indicator (fun _ => (1 : ℝ)) ω ≤
      (μ[Set.indicator {ω' : Ω | Y (n + 1) ω' ∈ F} (fun _ => (1 : ℝ)) | ℱ n]) ω := by
    filter_upwards [MeasureTheory.ae_all_iff.2 hstep] with ω hω
    intro K n
    rw [hω n]
    by_cases hK : ω ∈ lvl K n
    · have hy : Y n ω ∈ Kset K := hlvl K n hK
      have h1 : (c K).toReal ≤ (κ (Y n ω) F).toReal :=
        ENNReal.toReal_mono (measure_ne_top (κ (Y n ω)) F) (hforce K (Y n ω) hy)
      rw [Set.indicator_of_mem hK, mul_one]
      exact h1
    · have e : (lvl K n).indicator (fun _ => (1 : ℝ)) ω = 0 := by simp [Set.indicator, hK]
      rw [e, mul_zero]
      positivity
  have := ae_frequently_of_force_and_bounded (μ := μ) (ℱ := ℱ)
    (s := fun n => {ω | Y n ω ∈ F}) (lvl := lvl) (c := fun K => (c K).toReal) hs hc hcond hbound
  simpa using this


/-! ### From the paper's tightness interface to "the depth does not tend to infinity" -/

/-- **Uniform tail bound implies that the depth does not tend to infinity.**  The hypothesis is the
exact content of the paper's use of `(tightlaw)`:
`P(d_r → ∞) ≤ liminf_r P(d_r > K) ≤ sup_r P(d_r > K)`, and the supremum tends to `0` as `K → ∞`
uniformly in `r`.  In the repository this is the path-law form of `htight`
(`SimJump.RecKernel.recordTraj_tail`, `htight_iff_pathlaw`), whose right-hand side is literally
`recordTraj … {ω | K < dmax (ω r)}`.

This removes `hT` of the theorems above from the list of inputs: it is *derived* here from the
tightness interface. -/
theorem ae_not_tendsto_atTop_of_uniform_tail [IsFiniteMeasure μ] {d : ℕ → Ω → ℕ}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ, μ {ω | K ≤ d r ω} ≤ ε) :
    ∀ᵐ ω ∂μ, ¬ Tendsto (fun r => d r ω) atTop atTop := by
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  by_contra hne
  have hpos : 0 < μ {ω | Tendsto (fun r => d r ω) atTop atTop} := pos_iff_ne_zero.mpr hne
  obtain ⟨K, hK⟩ := h (μ {ω | Tendsto (fun r => d r ω) atTop atTop} / 2)
    (ENNReal.half_pos hpos.ne')
  have hsub : {ω | Tendsto (fun r => d r ω) atTop atTop} ⊆
      ⋃ N, ⋂ r ∈ Set.Ici N, {ω | K ≤ d r ω} := by
    intro ω hω
    obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp hω K
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iInter₂.mpr fun r hr => hi r (Set.mem_Ici.mp hr)⟩
  have hmono : Monotone (fun N => ⋂ r ∈ Set.Ici N, {ω : Ω | K ≤ d r ω}) := by
    intro a b hab ω hω
    exact Set.mem_iInter₂.mpr fun r hr =>
      Set.mem_iInter₂.mp hω r (Set.mem_Ici.mpr (le_trans hab (Set.mem_Ici.mp hr)))
  have hle : μ {ω | Tendsto (fun r => d r ω) atTop atTop} ≤
      μ {ω | Tendsto (fun r => d r ω) atTop atTop} / 2 := by
    calc μ {ω | Tendsto (fun r => d r ω) atTop atTop}
        ≤ μ (⋃ N, ⋂ r ∈ Set.Ici N, {ω | K ≤ d r ω}) := measure_mono hsub
      _ = ⨆ N, μ (⋂ r ∈ Set.Ici N, {ω | K ≤ d r ω}) := hmono.measure_iUnion
      _ ≤ μ {ω | Tendsto (fun r => d r ω) atTop atTop} / 2 := by
          refine iSup_le fun N => ?_
          refine (measure_mono ?_).trans (hK N)
          exact Set.biInter_subset_of_mem (Set.mem_Ici.mpr le_rfl)
  exact absurd hle (not_le.mpr (ENNReal.half_lt_self hne (measure_ne_top μ _)))

/-- **The paper's initial frequency step from its two actual inputs**: the uniform tail
(tightness) bound on the depth and the joint-event force bound. -/
theorem ae_frequently_of_joint_force_of_uniform_tail [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {d : ℕ → Ω → ℕ} (hd : ∀ n, Measurable[ℱ n] (d n))
    {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n)) {c : ℕ → ℝ}
    (hc : ∀ K, 0 < c K)
    (hforce : ∀ᵐ ω ∂μ, ∀ K n, c K * (if d n ω ≤ K then (1 : ℝ) else 0) ≤
      (μ[({ω | d n ω ≤ K} ∩ s (n + 1)).indicator (fun _ => (1 : ℝ)) | ℱ n]) ω)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ, μ {ω | K ≤ d r ω} ≤ ε) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ω ∈ s n :=
  ae_frequently_of_joint_force_of_tight hd hs hc hforce
    (ae_not_tendsto_atTop_of_uniform_tail htail)


/-! ### Capstone: the paper's initial frequency step from the three repository-available inputs -/

/-- **Initial-regeneration frequency step, fully assembled.**  The three inputs are precisely the
objects the repository / Mathlib supply:

* `hforce` — the force estimate of the stopped record kernel, in kernel form.  Instance in the
  repository: `SimJump.RecKernel.hitKInf_srSet_ge` with `Kset = exh N m`, `F = srSet N m`,
  `c K = ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))`.
* `hstep` — the one-step Markov identity of the path law,
  `P(Y_{n+1} ∈ F ∣ ℱ_n) = κ (Y_n) F`.  For the repository's record chain the path law is the
  Ionescu–Tulcea law `SimJump.RecKernel.recordTraj`; the identity is the `(recmark)` Markov
  property (`(recmark)` in the source), for which Mathlib provides
  `ProbabilityTheory.Kernel.condDistrib_trajMeasure`.  *This identification is not formalised
  here*: it is the one remaining path-law bridge.
* `htail` — the uniform tail bound of `(tightlaw)` in level form.  Instance in the repository:
  `SimJump.RecKernel.htight_iff_pathlaw` together with `recordTraj_tail`.

Conclusion: `F` is visited infinitely often almost surely, i.e. (with the instances above)
almost surely there are infinitely many simultaneous record times — the first half of the paper's
construction of an initial regeneration under `P`. -/
theorem ae_frequently_mem_of_kernel_force_of_uniform_tail [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α] {ℱ : Filtration ℕ m0}
    {Y : ℕ → Ω → α} (hY : ∀ n, Measurable[ℱ n] (Y n))
    {F : Set α} (hF : MeasurableSet F) {κ : Kernel α α} [IsMarkovKernel κ]
    {Kset : ℕ → Set α} {c : ℕ → ℝ≥0∞}
    (hforce : ∀ K y, y ∈ Kset K → c K ≤ κ y F)
    (hstep : ∀ n, μ[Set.indicator {ω : Ω | Y (n + 1) ω ∈ F} (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      (fun ω => (κ (Y n ω) F).toReal))
    (hc : ∀ K, 0 < (c K).toReal)
    {dep : α → ℕ}
    (hKset : ∀ K, Kset K = {y : α | dep y ≤ K})
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ, μ {ω | K ≤ dep (Y r ω)} ≤ ε) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, Y n ω ∈ F := by
  have hT : ∀ᵐ ω ∂μ, ¬ Tendsto (fun n => dep (Y n ω)) atTop atTop :=
    ae_not_tendsto_atTop_of_uniform_tail htail
  have hbound : ∀ᵐ ω ∂μ, ∃ K, ∃ᶠ n in atTop, ω ∈ {ω : Ω | dep (Y n ω) ≤ K} := by
    filter_upwards [hT] with ω hω
    obtain ⟨K, hK⟩ := exists_frequently_le_of_not_tendsto hω
    exact ⟨K, hK⟩
  refine ae_frequently_mem_of_kernel_force (lvl := fun K n => {ω : Ω | dep (Y n ω) ≤ K})
    hY hF hforce hstep hc ?_ hbound
  intro K n ω hω
  rw [hKset K]
  exact hω


/-- The paper's force constant `(1-p)^{N(2K+1)}` (as used in `(force)`, with `N` walkers and the
record level `K`) is strictly positive in the paper's regime `p < 1`.  This is the constant of
`SimJump.RecKernel.hitKInf_srSet_ge`, whose exponent is `N * (2 * K + 1)`. -/
theorem paper_constant_pos {p : ℝ} (hp : p < 1) (N K : ℕ) :
    0 < (ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))).toReal := by
  have h1 : 0 < 1 - p := by linarith
  rw [ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- **The paper's initial step with the literal tightness interface**: `htight` is stated as a
bound on the complements of the exhaustion sets,
`∀ ε > 0, ∃ K, ∀ r, μ {ω | Y_r ∉ Kset K} ≤ ε`, which is the shape of
`SimJump.RecKernel.htight_iff_pathlaw` / `recordTraj_tail` with `Kset K = exh N m K`. -/
theorem ae_frequently_mem_of_kernel_force_of_tight [IsFiniteMeasure μ]
    {α : Type*} [MeasurableSpace α] {ℱ : Filtration ℕ m0}
    {Y : ℕ → Ω → α} (hY : ∀ n, Measurable[ℱ n] (Y n))
    {F : Set α} (hF : MeasurableSet F) {κ : Kernel α α} [IsMarkovKernel κ]
    {Kset : ℕ → Set α} {c : ℕ → ℝ≥0∞}
    (hforce : ∀ K y, y ∈ Kset K → c K ≤ κ y F)
    (hstep : ∀ n, μ[Set.indicator {ω : Ω | Y (n + 1) ω ∈ F} (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      (fun ω => (κ (Y n ω) F).toReal))
    (hc : ∀ K, 0 < (c K).toReal)
    {dep : α → ℕ}
    (hKset : ∀ K, Kset K = {y : α | dep y ≤ K})
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ, μ {ω | Y r ω ∉ Kset K} ≤ ε) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, Y n ω ∈ F := by
  refine ae_frequently_mem_of_kernel_force_of_uniform_tail hY hF hforce hstep hc hKset ?_
  intro ε hε
  obtain ⟨K, hK⟩ := htight ε hε
  refine ⟨K + 1, fun r => ?_⟩
  have hset : {ω : Ω | K + 1 ≤ dep (Y r ω)} = {ω | Y r ω ∉ Kset K} := by
    ext ω
    rw [hKset K]
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hset]
  exact hK r

end RegenBC

end WCJF
