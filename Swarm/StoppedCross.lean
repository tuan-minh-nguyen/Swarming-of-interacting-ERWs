/-
  **The stopped crossing estimate** (eq. (cross) of
  *Swarming of interacting excited random walks*, `main_1d_revised.tex` §2.2),
  the part of the proof of Lemma `transience` that `CrossStep.lean` isolated.

  `CrossStep.lean` proves the one-step drift `f (X_n) ≤ E[f (X_{n+1}) | ℱ_n]` and hence that
  `f ∘ X` is a submartingale.  Here we finish the argument:

  * `exitTime X b0 b1` is the genuine first exit time of the window `[b0, b1+1]`, built from
    Mathlib's `MeasureTheory.hittingAfter`; it is a `IsStoppingTime` for the filtration
    (`isStoppingTime_exitTime`), and it is **not** assumed finite.
  * `Submartingale.stoppedProcess` applied to `f ∘ X` gives the bounded optional-sampling
    value inequality `f(X_0) ≤ E[f(X_{τ∧N})]` for every `N` (`integral_sc_le_integral_sc_stopped`).
  * On `{τ ≤ N}` the value `f(X_{τ∧N})` is `0` when the walker exits at the bottom `b0` and `1`
    when it exits at the top `b1+1`; on `{τ > N}` it is at most `1`.  Hence
    `P(exit at b0 by time N) ≤ 1 - E[f(X_0)]` (`cross_stopped_bound`).
  * Monotone convergence in `N` and `one_sub_sc_le` turn this into the paper's bound
    `P(T_{b0} < T_{b1+1}) = P(exit at b0) ≤ R(b1) = ∏_{x=b0+1}^{b1} (1-ω(x))/ω(x)`
    for a walker started at `b1` (`cross_prob_le`).

  No finiteness of `τ` is used or claimed: the submartingale bound is taken at the bounded
  stopping time `τ ∧ N` and the final probability is obtained by continuity from below.
  The weights `w` are a fixed deterministic sequence, exactly as in `CrossStep.lean`; the
  passage to a random environment (the paper's `ω_j` revealed at time `s`) is *not* done here.
-/
import Swarm.Imports
import Swarm.CrossStepInt

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SwarmSpeed

set_option linter.unusedSectionVars false

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### The exit time of the window `[b0, b1+1]` as a genuine stopping time -/

/-- The set of levels outside the closed window `[b0, b1+1]`: the walker is absorbed as soon as
it reaches one of them. -/
def outside (b0 b1 : ℕ) : Set ℕ := {x | x ≤ b0 ∨ b1 + 1 ≤ x}

lemma measurableSet_outside (b0 b1 : ℕ) : MeasurableSet (outside b0 b1) := trivial

lemma mem_outside_iff {b0 b1 x : ℕ} : x ∈ outside b0 b1 ↔ x ≤ b0 ∨ b1 + 1 ≤ x := Iff.rfl

/-- `exitTime X b0 b1` is the first time the walker `X` is outside the closed window
`[b0, b1+1]`, and `⊤` if it never leaves it. -/
noncomputable def exitTime (X : ℕ → Ω → ℕ) (b0 b1 : ℕ) : Ω → WithTop ℕ :=
  hittingAfter X (outside b0 b1) 0

/-- **The exit time is a stopping time.**  No integrability or boundedness of `X` beyond
adaptedness is needed. -/
theorem isStoppingTime_exitTime {X : ℕ → Ω → ℕ} (hX : ∀ n, Measurable[ℱ n] (X n)) (b0 b1 : ℕ) :
    IsStoppingTime ℱ (exitTime X b0 b1) :=
  Adapted.isStoppingTime_hittingAfter hX (measurableSet_outside b0 b1)

lemma exitTime_le_iff {X : ℕ → Ω → ℕ} {b0 b1 n : ℕ} {ω : Ω} :
    exitTime X b0 b1 ω ≤ ↑n ↔ ∃ k : ℕ, k ≤ n ∧ X k ω ∈ outside b0 b1 :=
  hittingAfter_bot_le_iff

/-- If the walker has exited, the level at the exit time is outside the window. -/
lemma exitTime_mem {X : ℕ → Ω → ℕ} {b0 b1 : ℕ} {ω : Ω}
    (h : exitTime X b0 b1 ω ≠ ⊤) :
    X (exitTime X b0 b1 ω).untopA ω ∈ outside b0 b1 :=
  hittingAfter_mem_set_of_ne_top h

/-- A finite exit time is a natural number. -/
lemma exists_exitTime_eq_coe {X : ℕ → Ω → ℕ} {b0 b1 : ℕ} {ω : Ω}
    (h : exitTime X b0 b1 ω ≠ ⊤) : ∃ n : ℕ, exitTime X b0 b1 ω = ↑n :=
  (WithTop.ne_top_iff_exists.mp h).imp fun _a ha => ha.symm

/-- Before the exit time the walker is inside the window. -/
lemma inside_of_lt_exitTime {X : ℕ → Ω → ℕ} {b0 b1 k : ℕ} {ω : Ω}
    (hk : (k : WithTop ℕ) < exitTime X b0 b1 ω) : X k ω ∉ outside b0 b1 :=
  notMem_of_lt_hittingAfter hk (Nat.zero_le k)

/-- If the walker never exits, it never leaves the window. -/
lemma inside_of_exitTime_top {X : ℕ → Ω → ℕ} {b0 b1 : ℕ} {ω : Ω}
    (h : exitTime X b0 b1 ω = ⊤) {k : ℕ} : X k ω ∉ outside b0 b1 :=
  hittingAfter_eq_top_iff.mp h k (Nat.zero_le k)

/-! ### Confinement of the walker to the window

The structural hypothesis `hstep` of `CrossStep.lean` (nearest-neighbour steps in the interior,
absorption at `b0` and `b1+1`) plus `X_0 ≥ b0` forces `b0 ≤ X_n` for every `n`; the upper bound
`X_n ≤ b1+1` is a hypothesis there (`hrange`).  Both are needed at once, on a single
almost-sure event, for the stopped process. -/

section Confinement

variable {X : ℕ → Ω → ℕ} {b0 b1 : ℕ}

/-- The structural hypothesis of `CrossStep.lean`, as a single almost-sure statement. -/
def StepHyp (μ : Measure Ω) (X : ℕ → Ω → ℕ) (b0 b1 : ℕ) : Prop :=
  ∀ n, ∀ᵐ ω ∂μ,
    (b0 < X n ω ∧ X n ω ≤ b1 ∧
        (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω)

lemma ae_forall_of_stepHyp (hstep : StepHyp μ X b0 b1) :
    ∀ᵐ ω ∂μ, ∀ n,
      (b0 < X n ω ∧ X n ω ≤ b1 ∧
          (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
        ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω) := by
  rw [MeasureTheory.ae_all_iff]
  exact hstep

lemma ae_forall_upper (hrange : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1) :
    ∀ᵐ ω ∂μ, ∀ n, X n ω ≤ b1 + 1 := by
  rw [MeasureTheory.ae_all_iff]
  exact hrange

/-- **Confinement.**  If the walker starts at a level `≥ b0`, satisfies the nearest-neighbour /
absorption structure and never exceeds `b1+1`, then almost surely it stays in `[b0, b1+1]` at
all times. -/
theorem ae_confined (hstep : StepHyp μ X b0 b1)
    (hrange : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1)
    (hX0 : ∀ᵐ ω ∂μ, b0 ≤ X 0 ω) :
    ∀ᵐ ω ∂μ, ∀ n, b0 ≤ X n ω ∧ X n ω ≤ b1 + 1 := by
  have hU := ae_forall_upper (μ := μ) (X := X) (b1 := b1) hrange
  have hS := ae_forall_of_stepHyp (μ := μ) (X := X) (b0 := b0) (b1 := b1) hstep
  filter_upwards [hU, hS, hX0] with ω hUω hSω h0
  intro n
  refine ⟨?_, hUω n⟩
  induction n with
  | zero => exact h0
  | succ k ih =>
    rcases hSω k with ⟨h1, -, h3 | h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
    · omega
    · omega
    · omega
    · omega

end Confinement

/-! ### The event "the walker exits at the bottom level by time `N`" -/

/-- `exitBottomBy X b0 b1 N` is the event that the walker has left the window by time `N` and
that it left it at the *bottom* level `b0`.  This is the complement, inside the exit event, of
the crossing-up event that eq. (cross) bounds. -/
def exitBottomBy (X : ℕ → Ω → ℕ) (b0 b1 N : ℕ) : Set Ω :=
  {ω | exitTime X b0 b1 ω ≤ ↑N ∧ X (exitTime X b0 b1 ω).untopA ω = b0}

/-- `hitsBefore X z w` is the event that the walker visits `z` at some time before it ever visits
`w` — the paper's event `{T_z < T_w}`. -/
def hitsBefore (X : ℕ → Ω → ℕ) (z w : ℕ) : Set Ω :=
  {ω | ∃ n, X n ω = z ∧ ∀ k < n, X k ω ≠ w}

/-- **`{T_{b0} < T_{b1+1}}` is the bottom-exit event.**  For a walker confined to the window
`[b0, b1+1]`, leaving the window at the bottom level `b0` is the same thing as visiting `b0`
before ever visiting `b1+1`.  Neither direction needs the nearest-neighbour/absorption structure,
only the confinement `b0 ≤ X_n ≤ b1+1` and `b0 ≠ b1+1`. -/
theorem exitBottom_iff_hitsBefore {X : ℕ → Ω → ℕ} {b0 b1 : ℕ} {ω : Ω} (hb : b0 ≤ b1)
    (hconf : ∀ n, b0 ≤ X n ω ∧ X n ω ≤ b1 + 1) :
    (exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0)
      ↔ ω ∈ hitsBefore X b0 (b1 + 1) := by
  have hne : b0 ≠ b1 + 1 := by omega
  constructor
  · rintro ⟨hne_top, hb0⟩
    refine ⟨(exitTime X b0 b1 ω).untopA, hb0, ?_⟩
    intro k hk hcontra
    have hmem : X k ω ∈ outside b0 b1 :=
      mem_outside_iff.mpr (Or.inr (le_of_eq hcontra.symm))
    have hle : exitTime X b0 b1 ω ≤ (k : WithTop ℕ) :=
      hittingAfter_le_of_mem (Nat.zero_le k) hmem
    have hk_le : (exitTime X b0 b1 ω).untopA ≤ k := WithTop.untopA_le hle
    omega
  · rintro ⟨n, hn, hw⟩
    have hmem : X n ω ∈ outside b0 b1 := mem_outside_iff.mpr (Or.inl (le_of_eq hn))
    have hτn : exitTime X b0 b1 ω ≤ (n : WithTop ℕ) :=
      hittingAfter_le_of_mem (Nat.zero_le n) hmem
    have hne_top : exitTime X b0 b1 ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτn
    refine ⟨hne_top, ?_⟩
    have hm : (exitTime X b0 b1 ω).untopA ≤ n := WithTop.untopA_le hτn
    rcases mem_outside_iff.mp (exitTime_mem hne_top) with h | h
    · exact le_antisymm h (hconf _).1
    · have hm1 : X (exitTime X b0 b1 ω).untopA ω = b1 + 1 := le_antisymm (hconf _).2 h
      rcases lt_or_eq_of_le hm with hlt | heq
      · exact absurd hm1 (hw _ hlt)
      · have hnm : X n ω = b1 + 1 := heq ▸ hm1
        exact absurd (hn ▸ hnm) hne

/-- The stopped walker stays inside the window whenever the walker itself does. -/
theorem ae_stoppedProcess_confined {X : ℕ → Ω → ℕ} {b0 b1 : ℕ}
    (hconf : ∀ᵐ ω ∂μ, ∀ n, b0 ≤ X n ω ∧ X n ω ≤ b1 + 1) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ,
      b0 ≤ stoppedProcess X (exitTime X b0 b1) N ω ∧
        stoppedProcess X (exitTime X b0 b1) N ω ≤ b1 + 1 := by
  filter_upwards [hconf] with ω hω N
  exact hω ((min (N : WithTop ℕ) (exitTime X b0 b1 ω)).untopA)

section StoppedMeas

variable {X : ℕ → Ω → ℕ} {b0 b1 : ℕ} (hX : ∀ n, Measurable[ℱ n] (X n))

include hX

/-- **Adaptedness of the stopped walker**: the stopped process of a strongly adapted process at
a stopping time is strongly adapted (`StronglyAdapted.stoppedProcess_of_discrete`). -/
theorem stronglyAdapted_stoppedProcess :
    StronglyAdapted ℱ (stoppedProcess X (exitTime X b0 b1)) := by
  have hu : StronglyAdapted ℱ X := fun n => (hX n).stronglyMeasurable
  exact hu.stoppedProcess_of_discrete (isStoppingTime_exitTime hX b0 b1)

theorem measurable_stoppedProcess (N : ℕ) :
    Measurable (stoppedProcess X (exitTime X b0 b1) N) :=
  ((stronglyAdapted_stoppedProcess hX N).mono (ℱ.le N)).measurable

/-- **Measurability of the bottom-exit event.**  On `{τ ≤ N}` the stopped walker *is* `X_τ`, so
the event is the intersection of the set `{τ ≤ N}` (in `ℱ N`) with `{X_{τ∧N} = b0}`. -/
theorem measurableSet_exitBottomBy (N : ℕ) : MeasurableSet (exitBottomBy X b0 b1 N) := by
  have hset : exitBottomBy X b0 b1 N
      = {ω | exitTime X b0 b1 ω ≤ (N : WithTop ℕ)}
        ∩ {ω | stoppedProcess X (exitTime X b0 b1) N ω = b0} := by
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      show stoppedProcess X (exitTime X b0 b1) N ω = b0
      exact (stoppedProcess_eq_of_ge (u := X) (τ := exitTime X b0 b1) (i := N) h1).trans h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      show X (exitTime X b0 b1 ω).untopA ω = b0
      rw [← stoppedProcess_eq_of_ge (u := X) (τ := exitTime X b0 b1) (i := N) h1]
      exact h2
  rw [hset]
  have h1 : MeasurableSet[ℱ N] {ω | exitTime X b0 b1 ω ≤ (N : WithTop ℕ)} :=
    isStoppingTime_exitTime hX b0 b1 N
  have h2 : MeasurableSet[ℱ N] {ω | stoppedProcess X (exitTime X b0 b1) N ω = b0} :=
    (stronglyAdapted_stoppedProcess hX N).measurable (measurableSet_singleton b0)
  exact (ℱ.le N) _ (h1.inter h2)

end StoppedMeas

/-! ### The stopped crossing bound -/

section Cross

variable [IsProbabilityMeasure μ]
  {w : ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}
  (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
  (hX : ∀ n, Measurable[ℱ n] (X n))
  (hstep : StepHyp μ X b0 b1)
  (hdom : ∀ n, ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
    w (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
  (hrange : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1)
  (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X 0 ω)

include hlo hhi hb hX hstep hdom hrange hX0b

/-- **Integrability of the stopped scale value**: it is bounded by `1` in absolute value because
the stopped walker never leaves the window. -/
theorem integrable_sc_stoppedProcess (N : ℕ) :
    Integrable (fun ω => sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω)) μ := by
  have hm : Measurable
      (fun ω => sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω)) :=
    (measurable_of_countable_sc hlo hhi hb).comp (measurable_stoppedProcess hX N)
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards [ae_stoppedProcess_confined (X := X) (b0 := b0) (b1 := b1)
    (ae_confined hstep hrange hX0b)] with ω hω
  exact norm_sc_le_one hlo hhi hb (hω N).2

/-- **The stopped scale process is a submartingale**:
`Submartingale.stoppedProcess` applied to the submartingale `f ∘ X` proved in
`CrossStep.lean`. -/
theorem submartingale_stoppedSc :
    Submartingale (fun n ω => sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) n ω)) ℱ μ := by
  have hbase : Submartingale (fun n ω => sc w b0 b1 (X n ω)) ℱ μ :=
    submartingale_sc_int hlo hhi hb hX hrange hstep hdom
  have h1 := hbase.stoppedProcess (isStoppingTime_exitTime hX b0 b1)
  rwa [stoppedProcess_comp (fun z => sc w b0 b1 z)] at h1

/-- **Bounded optional sampling for the scale function**:
`f(X_0) ≤ E[f(X_{τ∧N})]` for every `N`, with no assumption that `τ` is finite. -/
theorem integral_sc_le_integral_sc_stopped (N : ℕ) :
    ∫ ω, sc w b0 b1 (X 0 ω) ∂μ
      ≤ ∫ ω, sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω) ∂μ := by
  have h := (submartingale_stoppedSc hlo hhi hb hX hstep hdom hrange hX0b).setIntegral_le
    (Nat.zero_le N) MeasurableSet.univ
  simpa [stoppedProcess] using h

/-- **The pointwise comparison** behind eq. (cross): on the event that the walker exits at the
bottom level, `1 - f(X_{τ∧N}) = 1`; everywhere else `1 - f(X_{τ∧N}) ≥ 0`. -/
theorem indicator_exitBottomBy_le (N : ℕ) :
    ∀ᵐ ω ∂μ,
      (exitBottomBy X b0 b1 N).indicator (1 : Ω → ℝ) ω
        ≤ 1 - sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω) := by
  filter_upwards [ae_confined (μ := μ) hstep hrange hX0b] with ω hω
  by_cases hN : exitTime X b0 b1 ω ≤ (N : WithTop ℕ)
  · rw [stoppedProcess_eq_of_ge (u := X) (τ := exitTime X b0 b1) (i := N) hN]
    by_cases hb0 : X (exitTime X b0 b1 ω).untopA ω = b0
    · rw [Set.indicator_of_mem (show ω ∈ exitBottomBy X b0 b1 N from ⟨hN, hb0⟩), hb0,
        sc_b0 (w := w) (b0 := b0) (b1 := b1)]
      norm_num
    · have hne : exitTime X b0 b1 ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hN
      have hout : X (exitTime X b0 b1 ω).untopA ω ≤ b0
          ∨ b1 + 1 ≤ X (exitTime X b0 b1 ω).untopA ω :=
        mem_outside_iff.mp (exitTime_mem hne)
      have htop : X (exitTime X b0 b1 ω).untopA ω = b1 + 1 := by
        rcases hout with h | h
        · exact absurd (le_antisymm h ((hω ((exitTime X b0 b1 ω).untopA)).1)) hb0
        · exact le_antisymm ((hω ((exitTime X b0 b1 ω).untopA)).2) h
      rw [Set.indicator_of_notMem (fun hc => hb0 hc.2), htop, sc_top hlo hhi hb]
      norm_num
  · have hNM : (N : WithTop ℕ) ≤ exitTime X b0 b1 ω := le_of_lt (not_le.mp hN)
    rw [stoppedProcess_eq_of_le (u := X) (τ := exitTime X b0 b1) (i := N) hNM,
      Set.indicator_of_notMem (fun hc => hN hc.1)]
    have hle : sc w b0 b1 (X N ω) ≤ 1 := sc_le_one hlo hhi hb (hω N).2
    have hnn : 0 ≤ sc w b0 b1 (X N ω) := sc_nonneg hlo hhi hb _
    linarith

/-- **The stopped crossing bound**: for every `N`,
`P(exit at the bottom level b0 by time N) ≤ 1 - E[f(X_0)]`. -/
theorem cross_stopped_bound (N : ℕ) :
    μ.real (exitBottomBy X b0 b1 N) ≤ 1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ := by
  have hT : MeasurableSet (exitBottomBy X b0 b1 N) := measurableSet_exitBottomBy hX N
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have hind : Integrable ((exitBottomBy X b0 b1 N).indicator (1 : Ω → ℝ)) μ :=
    h1.indicator hT
  have hg := integrable_sc_stoppedProcess hlo hhi hb hX hstep hdom hrange hX0b N
  have hsub : Integrable
      (fun ω => 1 - sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω)) μ := h1.sub hg
  have hmono : ∫ ω, (exitBottomBy X b0 b1 N).indicator (1 : Ω → ℝ) ω ∂μ
      ≤ ∫ ω, (1 - sc w b0 b1 (stoppedProcess X (exitTime X b0 b1) N ω)) ∂μ :=
    integral_mono_ae hind hsub (indicator_exitBottomBy_le hlo hhi hb hX hstep hdom hrange hX0b N)
  have hI : ∫ ω, (exitBottomBy X b0 b1 N).indicator (1 : Ω → ℝ) ω ∂μ
      = μ.real (exitBottomBy X b0 b1 N) := by
    simpa [Pi.one_apply] using integral_indicator_one (μ := μ) hT
  rw [hI, integral_sub h1 hg, integral_const] at hmono
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hmono
  have hsm := integral_sc_le_integral_sc_stopped hlo hhi hb hX hstep hdom hrange hX0b N
  rw [Measure.real]
  linarith

/-- `E[f(X_0)] ≤ 1` because the walker starts inside the window. -/
theorem integral_sc_le_one :
    ∫ ω, sc w b0 b1 (X 0 ω) ∂μ ≤ 1 := by
  have hint : Integrable (fun ω => sc w b0 b1 (X 0 ω)) μ :=
    integrable_sc_comp hlo hhi hb hX (hrange 0)
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have h := integral_mono_ae hint h1
    (by filter_upwards [hrange 0] with ω hω using sc_le_one hlo hhi hb hω)
  simpa using h

/-- **The crossing bound for the whole exit event** (continuity from below in `N`):
`P(the walker ever exits at the bottom level) ≤ 1 - E[f(X_0)]`,
with no finiteness assumption on the exit time. -/
theorem cross_limit_bound :
    μ.real {ω | exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0}
      ≤ 1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ := by
  have hmono : Monotone (exitBottomBy X b0 b1) := by
    intro N M hNM ω hω
    exact ⟨le_trans hω.1 (by exact_mod_cast hNM), hω.2⟩
  have hUnion : (⋃ N, exitBottomBy X b0 b1 N)
      = {ω | exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0} := by
    ext ω
    rw [Set.mem_iUnion]
    show (∃ N : ℕ, exitTime X b0 b1 ω ≤ (N : WithTop ℕ)
        ∧ X (exitTime X b0 b1 ω).untopA ω = b0) ↔ _
    constructor
    · rintro ⟨N, hN, hb0⟩
      exact ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hN, hb0⟩
    · rintro ⟨hne, hb0⟩
      obtain ⟨n, hn⟩ := exists_exitTime_eq_coe hne
      exact ⟨n, by rw [hn], by simpa [hn] using hb0⟩
  have hbound : ∀ N, μ (exitBottomBy X b0 b1 N)
      ≤ ENNReal.ofReal (1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ) := by
    intro N
    have h := cross_stopped_bound hlo hhi hb hX hstep hdom hrange hX0b N
    have hfin : μ (exitBottomBy X b0 b1 N) ≠ ⊤ := measure_ne_top _ _
    rw [Measure.real] at h
    refine (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mp ?_
    rwa [ENNReal.toReal_ofReal (by linarith [integral_sc_le_one hlo hhi hb hX hstep hdom hrange hX0b])]
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hU : μ (⋃ N, exitBottomBy X b0 b1 N)
      ≤ ENNReal.ofReal (1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ) := le_of_tendsto' htend hbound
  rw [← hUnion, Measure.real]
  calc (μ (⋃ N, exitBottomBy X b0 b1 N)).toReal
      ≤ (ENNReal.ofReal (1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
    _ = 1 - ∫ ω, sc w b0 b1 (X 0 ω) ∂μ :=
        ENNReal.toReal_ofReal
          (by linarith [integral_sc_le_one hlo hhi hb hX hstep hdom hrange hX0b])

/-- The scale value at time `0` for a walker started at the top level `b1`. -/
theorem integral_sc_start (hstart : X 0 =ᵐ[μ] fun _ => b1) :
    ∫ ω, sc w b0 b1 (X 0 ω) ∂μ = sc w b0 b1 b1 := by
  have heq : (fun ω => sc w b0 b1 (X 0 ω)) =ᵐ[μ] (fun _ => sc w b0 b1 b1) := by
    filter_upwards [hstart] with ω hω
    rw [hω]
  rw [integral_congr_ae heq, integral_const]
  simp [Measure.real, measure_univ]

/-- **Eq. (cross) of the paper, sharp form**: for a walker started at the top level `b1` of the
window, the probability of exiting at the bottom level is at most
`1 - f(b1) = R(b1)/Z`, i.e. the exact right-hand side of eq. (cross). -/
theorem cross_prob_le_sharp (hstart : X 0 =ᵐ[μ] fun _ => b1) :
    μ.real {ω | exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0}
      ≤ 1 - sc w b0 b1 b1 := by
  have h := cross_limit_bound hlo hhi hb hX hstep hdom hrange hX0b
  rwa [integral_sc_start hlo hhi hb hX hstep hdom hrange hX0b hstart] at h

/-- **Eq. (cross) of the paper, unconditional form.**  For a walker started at the top level `b1`
of the window, the probability of exiting at the bottom level `b0` is at most the potential
`R(b1) = ∏_{x=b0+1}^{b1} (1-ω(x))/ω(x))`.  No finiteness of the exit time and no additional
hypothesis on a random environment is used. -/
theorem cross_prob_le (hstart : X 0 =ᵐ[μ] fun _ => b1) :
    μ.real {ω | exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0}
      ≤ R w b0 b1 :=
  (cross_prob_le_sharp hlo hhi hb hX hstep hdom hrange hX0b hstart).trans
    (one_sub_sc_le hlo hhi hb)

/-- **Eq. (cross) in the paper's own notation**: `P(T_{b0} < T_{b1+1}) ≤ R(b1)`. -/
theorem cross_prob_le_hitsBefore (hstart : X 0 =ᵐ[μ] fun _ => b1) :
    μ.real (hitsBefore X b0 (b1 + 1)) ≤ R w b0 b1 := by
  have hEq : {ω | exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0}
      =ᵐ[μ] hitsBefore X b0 (b1 + 1) := by
    filter_upwards [ae_confined hstep hrange hX0b] with ω hω
    exact propext (show (exitTime X b0 b1 ω ≠ ⊤ ∧ X (exitTime X b0 b1 ω).untopA ω = b0)
      ↔ ω ∈ hitsBefore X b0 (b1 + 1) from exitBottom_iff_hitsBefore hb hω)
  rw [Measure.real, ← measure_congr hEq, ← Measure.real]
  exact cross_prob_le hlo hhi hb hX hstep hdom hrange hX0b hstart

end Cross

end SwarmSpeed
