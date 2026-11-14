/-
# two-sided finite-horizon maximal oscillation of the actual `Qpl`

  `Qpl p m eps i j T U = sum_{t<T} projInc p m eps i j t U`

of the *optional projection* `Zproj = E[Zpot | F_t]` is a genuine martingale for the enlarged
filtration `enlFilt p m`, with `F_{t+1}`-strongly-measurable increments `projInc t` that have
vanishing `F_t`-conditional mean (`ProjOptionalLedger.martingale_Qpl`).  It also provides the
*two-sided maximal* Azuma--Hoeffding bound (`Azuma.measure_max_abs_psum_ge_le`) for an abstract
bounded-increment martingale-difference sequence.  What is missing --- and what this file supplies
--- is the composition: a two-sided finite-horizon bound on `max_{k <= n} |Qpl_k|` on the actual
array, with the truncation that makes the Azuma exponent usable made explicit.

`projInc t` is *not* deterministically small: it contains the potential increment of `Zproj`,
whose only available envelope is the polynomial `abs_Zpot_le`.  The paper therefore truncates
before centring.  Two forms are proved here, both stated for an abstract increment sequence and
then instantiated at the actual `Qpl`:

* `measure_max_abs_psum_le_of_ptrunc` --- **predictable indicator truncation.**  For a family
  `G : ℕ → Set Ω` with `MeasurableSet[ℱ k] (G k)` (so the truncation is *predictable*: it is
  decided by `F_k`-information) and `|ξ_k| ≤ C` on `G_k`, the truncated sequence
  `k ↦ 1_{G_k} • ξ_k` is again a martingale-difference sequence with the *same* filtration
  (pull-out of a predictable indicator) and has envelope `C`.  Hence

    `μ.real {max_{k<=n} |psum ξ k| >= ε} <= 2 (n+1) exp (-ε²/(4 n C²)) + μ.real {∃ k < n, ω ∉ G_k}`,

  the second term being *exactly* the residual event on which the truncation is active.  No
  centring is needed in this form: the truncation preserves the martingale property, so the
  residual is a support event, not a bias.

* `measure_max_abs_psum_le_of_clip` --- **clipping with predictable centring.**  Here the
  truncation is `x ↦ clip C x`, which destroys measurability *into* `F_t` but needs no geometric
  input at all.  The martingale property is restored by subtracting the *predictable* centre
  `y_k = clip C (E[clip C (ξ_k) | ℱ k])`.  The exact defect
  `D_n = sum_{k<n} (|ξ_k| - C)_+` and the exact centre bound `|sum_{k<n} y_k| <= n C` give

    `μ.real {max_{k<=n} |psum ξ k| >= ε} <= 2 (n+1) exp (-(ε - n C - δ)²/(16 n C²)) + μ.real {D_n >= δ}`

  for every `δ` with `n C + δ < ε`.  Nothing is assumed about the increments beyond
  integrability.

Instantiated at `ξ = projInc` both give theorems about the actual `arrayMeasure` process
`Qpl p m eps i j`, with no extra hypothesis on `p`, `m`, `i ≠ j`, `eps` beyond the ones under
which `Qpl` is already known to be a martingale.

Remaining inputs are stated, not hidden: the paper's `(locmart)` for `Qpl` needs (i) a
predictable truncation family `G` with a *small* envelope `C ≪ n` and (ii) a bound on the exact
bad event `{∃ t < n, U ∉ G t}` (resp. the clip defect `{D_n ≥ δ}`).  Neither is claimed here; the
polynomial `abs_Zpot_le` envelope suffices for neither at the paper's scale `n = T L`,
`ε = L^{3/4}`, and that is the honest quantitative content of this file.

No `sorry`, no `axiom`, no `native_decide`.  No declaration is copied from the read-only
`Lattice-Probability` checkout; the only external inputs are the integrated area modules.
-/
import Swarm.Azuma
import Swarm.LocOccLedger
import Swarm.QProjVarianceHonest
import Swarm.ZBudgetActual
import Swarm.CommonIncrement
import Swarm.InteriorBound

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace QplOsc

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### 1. Elementary manipulations of partial sums -/

/-- Partial sums are unchanged if the summands agree on a prefix. -/
theorem psum_congr_lt {ξ η : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : ∀ k < n, ξ k ω = η k ω) : LocMart.psum ξ n ω = LocMart.psum η n ω := by
  simp only [LocMart.psum]
  exact Finset.sum_congr rfl fun k hk => h k (Finset.mem_range.1 hk)

theorem psum_add (ξ η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    LocMart.psum (fun k => ξ k + η k) n ω = LocMart.psum ξ n ω + LocMart.psum η n ω := by
  simp only [LocMart.psum, Pi.add_apply, Finset.sum_add_distrib]

theorem psum_sub (ξ η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    LocMart.psum (fun k => ξ k - η k) n ω = LocMart.psum ξ n ω - LocMart.psum η n ω := by
  simp only [LocMart.psum, Pi.sub_apply, Finset.sum_sub_distrib]

theorem psum_eq_zero (ξ : ℕ → Ω → ℝ) : LocMart.psum ξ 0 = fun _ => 0 :=
  LocMart.psum_zero ξ

/-- A partial sum of an increment sequence that vanishes on a prefix vanishes. -/
theorem psum_eq_zero_of_forall {ξ : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : ∀ k < n, ξ k ω = 0) : LocMart.psum ξ n ω = 0 := by
  simp only [LocMart.psum]
  exact Finset.sum_eq_zero fun k hk => h k (Finset.mem_range.1 hk)

/-- Deterministic envelope of a partial sum. -/
theorem abs_psum_le_of_envelope {ξ : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ k ω, |ξ k ω| ≤ C) (n : ℕ) (ω : Ω) :
    |LocMart.psum ξ n ω| ≤ (n : ℝ) * C := by
  have := LocMart.abs_psum_le (ξ := ξ) (C := C) hbdd hC n ω
  simpa using this

/-- `LocMart.psum` of the projected increments is the paper's compensator `Qpl`.  Definitional. -/
theorem psum_projInc_eq_Qpl {N : ℕ} (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) (n : ℕ)
    (U : Swarming.Uniform.Array N) :
    LocMart.psum (fun t (U : Swarming.Uniform.Array N) =>
        Swarming.Enl.ProjLedger.projInc p m eps i j t U) n U
      = Swarming.Enl.ProjLedger.Qpl p m eps i j n U := rfl

/-! ### 2. Predictable indicator truncation -/

/-- The predictable truncation of an increment: keep `ξ k` on the predictable set `G k`, and
replace it by `0` off that set.  Because `G k` is `ℱ k`-measurable the truncated sequence is
still adapted to the same one-step lag and keeps the vanishing conditional mean; this is the
content of `condExp_ptrunc_eq_zero` below. -/
noncomputable def ptrunc (G : ℕ → Set Ω) (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  (G k).indicator (ξ k)

/-- The residual (complementary) part of the increment. -/
noncomputable def presid (G : ℕ → Set Ω) (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  (G k)ᶜ.indicator (ξ k)

/-- On the truncation set the truncated increment is the original one. -/
theorem ptrunc_eq_of_mem {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {k : ℕ} {ω : Ω} (h : ω ∈ G k) :
    ptrunc G ξ k ω = ξ k ω :=
  Set.indicator_of_mem h (ξ k)

/-- Off the truncation set the truncated increment vanishes. -/
theorem ptrunc_eq_zero_of_not_mem {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {k : ℕ} {ω : Ω}
    (h : ω ∉ G k) : ptrunc G ξ k ω = 0 :=
  Set.indicator_of_notMem h (ξ k)

theorem ptrunc_add_presid (G : ℕ → Set Ω) (ξ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    ptrunc G ξ k ω + presid G ξ k ω = ξ k ω := by
  classical
  simp only [ptrunc, presid]
  by_cases h : ω ∈ G k <;> simp [h]

theorem stronglyMeasurable_ptrunc {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k)) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (ptrunc G ξ k) := by
  have hle : (ℱ k : MeasurableSpace Ω) ≤ ℱ (k + 1) := ℱ.mono (Nat.le_succ k)
  have hs : MeasurableSet[ℱ (k + 1)] (G k) := MeasurableSpace.le_def.1 hle (G k) (hG k)
  exact (hξm k).indicator hs

theorem integrable_ptrunc {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ} (hξi : ∀ k, Integrable (ξ k) μ) (k : ℕ) :
    Integrable (ptrunc G ξ k) μ := by
  have hs : MeasurableSet (G k) := MeasurableSpace.le_def.1 (ℱ.le k) (G k) (hG k)
  exact (hξi k).indicator hs

/-- **The truncated increment keeps the vanishing conditional mean.**  This is where
predictability of `G` is used: the indicator can be pulled out of the conditional expectation. -/
theorem condExp_ptrunc_eq_zero {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ} (hξi : ∀ k, Integrable (ξ k) μ)
    (hξ0 : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0) (k : ℕ) :
    μ[ptrunc G ξ k | ℱ k] =ᵐ[μ] 0 := by
  have h := MeasureTheory.condExp_indicator (m := ℱ k) (μ := μ) (f := ξ k) (s := G k)
    (hξi k) (hG k)
  refine h.trans ?_
  filter_upwards [hξ0 k] with ω hω
  classical
  by_cases hmem : ω ∈ G k
  · rw [Set.indicator_of_mem hmem]; exact hω
  · rw [Set.indicator_of_notMem hmem]; simp

/-- Pointwise envelope of the truncated increment, on the truncation set only. -/
theorem abs_ptrunc_le {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ k ω, ω ∈ G k → |ξ k ω| ≤ C) (k : ℕ) (ω : Ω) :
    |ptrunc G ξ k ω| ≤ C := by
  by_cases h : ω ∈ G k
  · rw [ptrunc_eq_of_mem h]; exact hbdd k ω h
  · rw [ptrunc_eq_zero_of_not_mem h, abs_zero]; exact hC

/-- Splitting a partial sum along the truncation and its complement. -/
theorem psum_split (G : ℕ → Set Ω) (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    LocMart.psum ξ n ω
      = LocMart.psum (ptrunc G ξ) n ω + LocMart.psum (presid G ξ) n ω := by
  simp only [LocMart.psum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (ptrunc_add_presid G ξ k ω).symm

/-- Inside the good set the truncation is invisible. -/
theorem psum_ptrunc_eq_of_mem {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : ∀ k < n, ω ∈ G k) :
    LocMart.psum (ptrunc G ξ) n ω = LocMart.psum ξ n ω :=
  psum_congr_lt fun k hk => ptrunc_eq_of_mem (h k hk)

/-- **Predictable truncation: two-sided finite-horizon maximal bound.**  The residual is exactly
the event `{∃ k < n, ω ∉ G_k}` on which the truncation is active. -/
theorem measure_max_abs_psum_le_of_ptrunc [IsProbabilityMeasure μ]
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ)
    (hξ0 : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k ω, ω ∈ G k → |ξ k ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + μ.real {ω | ∃ k < n, ω ∉ G k} := by
  let _ : MeasurableSpace Ω := m0
  set ξ' : ℕ → Ω → ℝ := ptrunc G ξ with hξ'def
  have hsub : {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|} ⊆
      {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|} ∪ {ω | ∃ k < n, ω ∉ G k} := by
    intro ω hω
    obtain ⟨k, hk, hdev⟩ := hω
    by_cases hb : ∀ j < k, ω ∈ G j
    · refine Or.inl ⟨k, hk, ?_⟩
      have heq : LocMart.psum ξ' k ω = LocMart.psum ξ k ω := psum_ptrunc_eq_of_mem hb
      rwa [heq]
    · push Not at hb
      obtain ⟨j, hj, hjb⟩ := hb
      exact Or.inr ⟨j, lt_of_lt_of_le hj hk, hjb⟩
  have hAz := LocMart.measure_max_abs_psum_ge_le (μ := μ) (ℱ := ℱ) (ξ := ξ')
    (stronglyMeasurable_ptrunc hG hξm) hC (abs_ptrunc_le hC.le hbdd)
    (condExp_ptrunc_eq_zero hG hξi hξ0) hn hε
  calc μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ μ.real ({ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|} ∪ {ω | ∃ k < n, ω ∉ G k}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|} + μ.real {ω | ∃ k < n, ω ∉ G k} :=
        measureReal_union_le _ _
    _ ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
          + μ.real {ω | ∃ k < n, ω ∉ G k} :=
        add_le_add hAz le_rfl

/-- The same bound with the bad-event probability replaced by an explicit budget `δ`. -/
theorem measure_max_abs_psum_le_of_ptrunc_budget [IsProbabilityMeasure μ]
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ)
    (hξ0 : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {C δ : ℝ} (hC : 0 < C)
    (hbdd : ∀ k ω, ω ∈ G k → |ξ k ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hδ : μ.real {ω | ∃ k < n, ω ∉ G k} ≤ δ) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) + δ := by
  refine le_trans (measure_max_abs_psum_le_of_ptrunc hG hξm hξi hξ0 hC hbdd hn hε) ?_
  exact add_le_add le_rfl hδ

/-! ### 2b. Clipping with predictable centring -/

/-- Clipping at level `C`. -/
noncomputable def clip (C x : ℝ) : ℝ := max (-C) (min C x)

theorem le_clip (C x : ℝ) : -C ≤ clip C x := le_max_left _ _

theorem clip_le {C x : ℝ} (hC : 0 ≤ C) : clip C x ≤ C :=
  max_le (by linarith) (min_le_left _ _)

theorem abs_clip_le {C x : ℝ} (hC : 0 ≤ C) : |clip C x| ≤ C :=
  abs_le.2 ⟨le_clip C x, clip_le hC⟩

theorem clip_eq_self {C x : ℝ} (h : |x| ≤ C) : clip C x = x := by
  have h1 : -C ≤ x := (abs_le.1 h).1
  have h2 : x ≤ C := (abs_le.1 h).2
  simp only [clip, min_eq_right h2, max_eq_right h1]

theorem clip_of_ge {C x : ℝ} (hC : 0 ≤ C) (h : C ≤ x) : clip C x = C := by
  have h1 : min C x = C := min_eq_left h
  have h2 : -C ≤ C := by linarith
  simp only [clip, h1, max_eq_right h2]

theorem clip_of_le_neg {C x : ℝ} (hC : 0 ≤ C) (h : x ≤ -C) : clip C x = -C := by
  have h1 : x ≤ C := h.trans (by linarith)
  have h2 : min C x = x := min_eq_right h1
  simp only [clip, h2, max_eq_left h]

theorem continuous_clip (C : ℝ) : Continuous (clip C) :=
  continuous_const.max (continuous_const.min continuous_id')

/-- **The clipping defect.**  The amount removed by clipping is exactly `max 0 (|x| - C)`. -/
theorem abs_sub_clip {C : ℝ} (hC : 0 ≤ C) (x : ℝ) :
    |x - clip C x| = max 0 (|x| - C) := by
  rcases le_or_gt |x| C with h | h
  · rw [clip_eq_self h, sub_self, abs_zero, max_eq_left (by linarith)]
  · rcases abs_cases x with ⟨hx, hx0⟩ | ⟨hx, hx0⟩
    · have hx' : C ≤ x := by rw [hx] at h; exact h.le
      rw [hx, clip_of_ge hC hx', abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    · have hx' : x ≤ -C := by rw [hx] at h; linarith
      rw [hx, clip_of_le_neg hC hx', abs_of_nonpos (by linarith), max_eq_right (by linarith)]
      ring

/-- The clipped increment. -/
noncomputable def cclip (C : ℝ) (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => clip C (ξ k ω)

/-- The **predictable centre**: the conditional expectation of the clipped increment, clipped
*again* so that it is pointwise bounded by `C`. -/
noncomputable def trcenter (μ : Measure Ω) (ℱ : Filtration ℕ m0) (C : ℝ) (ξ : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → ℝ :=
  fun ω => clip C (μ[cclip C ξ k | ℱ k] ω)

/-- The centred, clipped increment. -/
noncomputable def trimc (μ : Measure Ω) (ℱ : Filtration ℕ m0) (C : ℝ) (ξ : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → ℝ :=
  fun ω => cclip C ξ k ω - trcenter μ ℱ C ξ k ω

/-- The clipping-defect increment. -/
noncomputable def cdefect (C : ℝ) (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => ξ k ω - cclip C ξ k ω

theorem stronglyMeasurable_cclip {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (C : ℝ) (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] (cclip C ξ k) :=
  (continuous_clip C).comp_stronglyMeasurable (hξm k)

theorem integrable_cclip [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : Integrable (cclip C ξ k) μ :=
  Integrable.of_bound
    ((stronglyMeasurable_cclip hξm C k).mono (ℱ.le (k + 1))).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_clip_le hC)

theorem stronglyMeasurable_trcenter (μ : Measure Ω) (ℱ : Filtration ℕ m0) {ξ : ℕ → Ω → ℝ}
    (C : ℝ) (k : ℕ) : StronglyMeasurable[ℱ k] (trcenter μ ℱ C ξ k) :=
  (continuous_clip C).comp_stronglyMeasurable stronglyMeasurable_condExp

theorem abs_trcenter_le (μ : Measure Ω) (ℱ : Filtration ℕ m0) (C : ℝ) (hC : 0 ≤ C)
    (ξ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : |trcenter μ ℱ C ξ k ω| ≤ C :=
  abs_clip_le hC

theorem integrable_trcenter (μ : Measure Ω) (ℱ : Filtration ℕ m0) {ξ : ℕ → Ω → ℝ}
    [IsFiniteMeasure μ] {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : Integrable (trcenter μ ℱ C ξ k) μ :=
  Integrable.of_bound
    ((stronglyMeasurable_trcenter μ ℱ (ξ := ξ) C k).mono (ℱ.le k)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_trcenter_le μ ℱ C hC ξ k ω)

theorem stronglyMeasurable_trimc {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (C : ℝ) (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] (trimc μ ℱ C ξ k) := by
  have h1 : StronglyMeasurable[ℱ (k + 1)] (cclip C ξ k) := stronglyMeasurable_cclip hξm C k
  have h2 : StronglyMeasurable[ℱ (k + 1)] (trcenter μ ℱ C ξ k) :=
    (stronglyMeasurable_trcenter μ ℱ (ξ := ξ) C k).mono (ℱ.mono (Nat.le_succ k))
  exact h1.sub h2

theorem abs_trimc_le {ξ : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (ω : Ω) :
    |trimc μ ℱ C ξ k ω| ≤ 2 * C := by
  have h1 : |cclip C ξ k ω| ≤ C := abs_clip_le hC
  have h2 : |trcenter μ ℱ C ξ k ω| ≤ C := abs_trcenter_le μ ℱ C hC ξ k ω
  show |cclip C ξ k ω - trcenter μ ℱ C ξ k ω| ≤ 2 * C
  calc |cclip C ξ k ω - trcenter μ ℱ C ξ k ω|
      ≤ |cclip C ξ k ω| + |trcenter μ ℱ C ξ k ω| := abs_sub _ _
    _ ≤ C + C := add_le_add h1 h2
    _ = 2 * C := by ring

theorem integrable_cdefect [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    Integrable (cdefect C ξ k) μ :=
  (hξi k).sub (integrable_cclip hξm hC k)

/-- The clipped centre *is* the conditional expectation of the clipped increment, a.e. -/
theorem ae_trcenter_eq_condExp [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    trcenter μ ℱ C ξ k =ᵐ[μ] μ[cclip C ξ k | ℱ k] := by
  have h1 : μ[cclip C ξ k | ℱ k] ≤ᵐ[μ] fun _ => C := by
    have h := MeasureTheory.condExp_mono (m := ℱ k) (μ := μ) (integrable_cclip hξm hC k)
      (integrable_const C) (Filter.Eventually.of_forall fun ω => clip_le hC)
    simpa only [MeasureTheory.condExp_const (ℱ.le k)] using h
  have h2 : (fun _ => -C) ≤ᵐ[μ] μ[cclip C ξ k | ℱ k] := by
    have h := MeasureTheory.condExp_mono (m := ℱ k) (μ := μ) (integrable_const (-C))
      (integrable_cclip hξm hC k) (Filter.Eventually.of_forall fun ω => le_clip C (ξ k ω))
    simpa only [MeasureTheory.condExp_const (ℱ.le k)] using h
  filter_upwards [h1, h2] with ω h1' h2'
  show clip C (μ[cclip C ξ k | ℱ k] ω) = μ[cclip C ξ k | ℱ k] ω
  rw [clip_eq_self (abs_le.2 ⟨h2', h1'⟩)]

/-- **The centred clipped increment has vanishing conditional mean.**  No hypothesis on `ξ` is
used beyond measurability and integrability: the centre is *defined* to be the conditional
expectation of the clipped increment. -/
theorem condExp_trimc_eq_zero [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k)) {C : ℝ} (hC : 0 < C) (k : ℕ) :
    μ[trimc μ ℱ C ξ k | ℱ k] =ᵐ[μ] 0 := by
  have h1 : Integrable (cclip C ξ k) μ := integrable_cclip hξm hC.le k
  have h2 : Integrable (trcenter μ ℱ C ξ k) μ := integrable_trcenter μ ℱ hC.le k
  have hte : μ[trcenter μ ℱ C ξ k | ℱ k] =ᵐ[μ] trcenter μ ℱ C ξ k :=
    Filter.EventuallyEq.of_eq (MeasureTheory.condExp_of_stronglyMeasurable (ℱ.le k)
      (stronglyMeasurable_trcenter μ ℱ (ξ := ξ) C k) h2)
  have h3 : μ[trimc μ ℱ C ξ k | ℱ k]
      =ᵐ[μ] μ[cclip C ξ k | ℱ k] - trcenter μ ℱ C ξ k := by
    have h := MeasureTheory.condExp_sub (m := ℱ k) h1 h2
    have hfun : trimc μ ℱ C ξ k
        = cclip C ξ k - trcenter μ ℱ C ξ k := rfl
    rw [hfun]
    filter_upwards [h, hte] with ω hω hω'
    simp only [Pi.sub_apply] at hω hω' ⊢
    rw [hω, hω']
  refine h3.trans ?_
  filter_upwards [ae_trcenter_eq_condExp (ξ := ξ) hξm hC.le k] with ω hω
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hω, sub_self]

/-- **Clipping with predictable centring: two-sided finite-horizon maximal bound.**  With the
centre and the defect as defined above, the maximal oscillation of the partial sums is bounded by
the maximal Azuma--Hoeffding tail of the centred clipped sequence (envelope `2C`) plus the
probability of the exact defect event `{δ ≤ sum_{t<n} (|ξ_t| - C)_+}`. -/
theorem measure_max_abs_psum_le_of_clip [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hε : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)} := by
  classical
  -- the three pieces
  set ζ : ℕ → Ω → ℝ := trimc μ ℱ C ξ with hζ
  set Y : ℕ → Ω → ℝ := trcenter μ ℱ C ξ with hY
  set D : ℕ → Ω → ℝ := cdefect C ξ with hD
  have hdec : ∀ k ω, LocMart.psum ξ k ω
      = LocMart.psum ζ k ω + LocMart.psum Y k ω + LocMart.psum D k ω := by
    intro k ω
    simp only [LocMart.psum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ξ j ω = (cclip C ξ j ω - trcenter μ ℱ C ξ j ω) + trcenter μ ℱ C ξ j ω
      + (ξ j ω - cclip C ξ j ω)
    ring
  have hYle : ∀ k ≤ n, ∀ ω, |LocMart.psum Y k ω| ≤ (n : ℝ) * C := by
    intro k hk ω
    have h1 : |LocMart.psum Y k ω| ≤ (k : ℝ) * C :=
      abs_psum_le_of_envelope hC.le (fun j ω => by
        have := abs_trcenter_le μ ℱ C hC.le ξ j ω
        simpa only [hY] using this) k ω
    have h2 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    calc |LocMart.psum Y k ω| ≤ (k : ℝ) * C := h1
      _ ≤ (n : ℝ) * C := by nlinarith [hC.le]
  have hDle : ∀ k ≤ n, ∀ ω, |LocMart.psum D k ω|
      ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C) := by
    intro k hk ω
    have h1 : |LocMart.psum D k ω| ≤ ∑ t ∈ Finset.range k, |cdefect C ξ t ω| := by
      simp only [LocMart.psum, hD]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ t, |cdefect C ξ t ω| = max 0 (|ξ t ω| - C) := by
      intro t
      simp only [cdefect]
      exact abs_sub_clip hC.le (ξ t ω)
    rw [Finset.sum_congr rfl (fun t _ => h2 t)] at h1
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun t _ _ => le_max_left _ _)
  -- the set inclusion with the split budget
  have hsub : {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|} ⊆
      {ω | ∃ k ≤ n, ε - (n : ℝ) * C - δ ≤ |LocMart.psum ζ k ω|}
        ∪ {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)} := by
    intro ω hω
    obtain ⟨k, hk, hdev⟩ := hω
    by_cases hb : δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)
    · exact Or.inr hb
    · push Not at hb
      refine Or.inl ⟨k, hk, ?_⟩
      have h1 : |LocMart.psum ξ k ω| ≤ |LocMart.psum ζ k ω| + |LocMart.psum Y k ω|
          + |LocMart.psum D k ω| := by
        rw [hdec k ω]
        exact (abs_add_three _ _ _)
      have h2 := hYle k hk ω
      have h3 := hDle k hk ω
      linarith
  -- maximal Azuma for the centred clipped sequence
  have hAz := LocMart.measure_max_abs_psum_ge_le (μ := μ) (ℱ := ℱ) (ξ := ζ)
    (C := 2 * C) (ε := ε - (n : ℝ) * C - δ)
    (fun k => stronglyMeasurable_trimc hξm C k)
    (by linarith)
    (fun k ω => by
      have := abs_trimc_le (μ := μ) (ℱ := ℱ) (ξ := ξ) hC.le k ω
      simpa only [hζ] using this)
    (fun k => condExp_trimc_eq_zero (ξ := ξ) hξm hC k)
    hn (by linarith)
  have hexp : (4 : ℝ) * (n : ℝ) * (2 * C) ^ 2 = 16 * (n : ℝ) * C ^ 2 := by ring
  calc μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ μ.real ({ω | ∃ k ≤ n, ε - (n : ℝ) * C - δ ≤ |LocMart.psum ζ k ω|}
          ∪ {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ∃ k ≤ n, ε - (n : ℝ) * C - δ ≤ |LocMart.psum ζ k ω|}
          + μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)} :=
        measureReal_union_le _ _
    _ ≤ _ := by
        rw [hexp] at hAz
        exact add_le_add hAz le_rfl

/-- **Markov control of the clipping defect.**  The defect event of
`measure_max_abs_psum_le_of_clip` costs at most the mean of the removed mass divided by `δ`. -/
theorem measure_defect_ge_le [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ) {C : ℝ} (hC : 0 ≤ C) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}
      ≤ (1 / δ) * ∑ t ∈ Finset.range n, ∫ ω, max 0 (|ξ t ω| - C) ∂μ := by
  classical
  have hint : ∀ t, Integrable (fun ω => max 0 (|ξ t ω| - C)) μ := by
    intro t
    have hcont : Continuous (fun x : ℝ => max 0 (|x| - C)) :=
      continuous_const.max ((continuous_abs.comp continuous_id).sub continuous_const)
    have hmeas : AEStronglyMeasurable (fun ω => max 0 (|ξ t ω| - C)) μ :=
      hcont.comp_aestronglyMeasurable
        (((hξm t).mono (ℱ.le (t + 1))).aestronglyMeasurable)
    refine Integrable.mono' (hξi t).norm hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg _) (by linarith [abs_nonneg (ξ t ω)])
  have hsum : Integrable (fun ω => ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)) μ :=
    integrable_finsetSum _ (fun t _ => hint t)
  have hnonneg : 0 ≤ᵐ[μ] fun ω => ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C) :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun t _ => le_max_left _ _
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hsum δ
  rw [integral_finsetSum _ (fun t _ => hint t)] at hmark
  have h2 : μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}
      ≤ (∑ t ∈ Finset.range n, ∫ ω, max 0 (|ξ t ω| - C) ∂μ) / δ := by
    rw [le_div_iff₀ hδ]
    linarith [hmark]
  rwa [div_eq_mul_one_div, mul_comm] at h2

/-- **Clipping with predictable centring for the actual `Qpl`, unconditionally.**  For every clip
level `C > 0`, defect budget `δ` and threshold `ε > n C + δ`, the maximal oscillation of the actual
compensator is bounded by the maximal Azuma--Hoeffding tail of the centred clipped process plus the
explicit defect event.  No martingale, adaptation or boundedness hypothesis is used: the centring
*defines* the martingale-difference structure. -/
theorem qpl_measure_max_abs_le_of_clip {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hεpos : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + (Swarming.Uniform.arrayMeasure N).real
            {U | δ ≤ ∑ t ∈ Finset.range n,
              max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)} := by
  have h := measure_max_abs_psum_le_of_clip (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    (fun t => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m t eps i j)
    hC hn hεpos hgap
  simpa only [psum_projInc_eq_Qpl] using h

/-- The same, with the defect probability replaced by its Markov bound: the only remaining datum
is the explicit integral of the removed mass. -/
theorem qpl_measure_max_abs_le_of_clip_integral {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hεpos : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) (hδ : 0 < δ) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + (1 / δ) * ∑ t ∈ Finset.range n,
            ∫ U, max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)
              ∂(Swarming.Uniform.arrayMeasure N) := by
  refine le_trans (qpl_measure_max_abs_le_of_clip hp0 hp1 hij hε hC hn hεpos hgap) ?_
  refine add_le_add le_rfl ?_
  exact measure_defect_ge_le (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    (fun t => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m t eps i j)
    (fun t => Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m t i j hε) hC.le hδ n

/-! ### 3. The actual process: two-sided finite-horizon maximal oscillation of `Qpl` -/

/-- **Two-sided finite-horizon maximal oscillation of the actual `Qpl`, with predictable
truncation.**  `G` is a *predictable* truncation family (`G t` is `enlFilt p m t`-measurable) on
which the projected increment is bounded by `C`.  Then the maximal oscillation up to `n` has the
maximal Azuma--Hoeffding tail with envelope `C`, up to the probability of the *exact* residual
event on which the truncation is active.  No other hypothesis is used. -/
theorem qpl_measure_max_abs_le_of_predictable_trunc {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {G : ℕ → Set (Swarming.Uniform.Array N)}
    (hG : ∀ t, MeasurableSet[Swarming.Enl.enlFilt p m t] (G t))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ t U, U ∈ G t → |Swarming.Enl.ProjLedger.projInc p m eps i j t U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + (Swarming.Uniform.arrayMeasure N).real {U | ∃ t < n, U ∉ G t} := by
  have h := measure_max_abs_psum_le_of_ptrunc (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m) (G := G)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    hG (fun t => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m t eps i j)
    (fun t => Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m t i j hε)
    (fun t => Swarming.Enl.ProjLedger.condExp_projInc_eq_zero hp0 hp1 m t i j hε)
    hC hbdd hn hεpos
  simpa only [psum_projInc_eq_Qpl] using h

/-- The same bound with an explicit budget `δ` for the exact residual event. -/
theorem qpl_measure_max_abs_le_of_predictable_trunc_budget {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j)
    {eps : ℝ} (hε : 0 < eps)
    {G : ℕ → Set (Swarming.Uniform.Array N)}
    (hG : ∀ t, MeasurableSet[Swarming.Enl.enlFilt p m t] (G t))
    {C δ : ℝ} (hC : 0 < C)
    (hbdd : ∀ t U, U ∈ G t → |Swarming.Enl.ProjLedger.projInc p m eps i j t U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε)
    (hδ : (Swarming.Uniform.arrayMeasure N).real {U | ∃ t < n, U ∉ G t} ≤ δ) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) + δ :=
  le_trans (qpl_measure_max_abs_le_of_predictable_trunc hp0 hp1 hij hε hG hC hbdd hn hεpos)
    (add_le_add le_rfl hδ)

/-- **The defect event is a finite union of one-step large-increment events.**  If the clipping
defect up to horizon `n` is at least `δ`, then some single increment is at least `C + δ/n` in
modulus.  This is the exact combinatorial content that turns the defect term of
`measure_max_abs_psum_le_of_clip` into `n` per-time events, each of which is the kind of event
that a per-site or per-record large-deviation estimate controls. -/
theorem exists_large_of_defect_ge {ξ : ℕ → Ω → ℝ} {C δ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hδ : 0 < δ) {ω : Ω} (h : δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)) :
    ∃ t < n, C + δ / (n : ℝ) ≤ |ξ t ω| := by
  classical
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C) < ∑ _t ∈ Finset.range n, δ / (n : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun t ht => ?_
    · exact ⟨0, Finset.mem_range.2 (by omega)⟩
    · have hlt : t < n := Finset.mem_range.1 ht
      have h1 : |ξ t ω| < C + δ / (n : ℝ) := hcon t hlt
      exact max_lt (by positivity) (by linarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  have h2 : ((n : ℝ)) * (δ / (n : ℝ)) = δ := by field_simp
  rw [h2] at hle
  linarith

/-- Union-bound form of the clipping residual: the defect probability is at most the sum of the
per-time probabilities of an increment exceeding `C + δ/n`. -/
theorem measure_defect_ge_le_union [IsFiniteMeasure μ] {ξ : ℕ → Ω → ℝ} {C δ : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hδ : 0 < δ) :
    μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}
      ≤ ∑ t ∈ Finset.range n, μ.real {ω | C + δ / (n : ℝ) ≤ |ξ t ω|} := by
  have hsub : {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}
      ⊆ ⋃ t ∈ Finset.range n, {ω | C + δ / (n : ℝ) ≤ |ξ t ω|} := by
    intro ω hω
    obtain ⟨t, ht, hdev⟩ := exists_large_of_defect_ge hn hδ hω
    exact Set.mem_biUnion (Finset.mem_range.2 ht) hdev
  calc μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ t ω| - C)}
      ≤ μ.real (⋃ t ∈ Finset.range n, {ω | C + δ / (n : ℝ) ≤ |ξ t ω|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ Finset.range n, μ.real {ω | C + δ / (n : ℝ) ≤ |ξ t ω|} :=
        measureReal_biUnion_finset_le _ _

/-- The clipping residual of the actual `Qpl` as a finite union of one-step events. -/
theorem qpl_defect_ge_le_union {N : ℕ} {C δ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hδ : 0 < δ)
    (p : ℝ) (m : ℕ) (eps : ℝ) (i j : Fin N) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | δ ≤ ∑ t ∈ Finset.range n,
          max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)}
      ≤ ∑ t ∈ Finset.range n, (Swarming.Uniform.arrayMeasure N).real
          {U | C + δ / (n : ℝ) ≤ |Swarming.Enl.ProjLedger.projInc p m eps i j t U|} :=
  measure_defect_ge_le_union (μ := Swarming.Uniform.arrayMeasure N) hn hδ

/-- **The sharpest form of the clipping bound on the actual `Qpl`.**  The residual is an explicit
finite sum of one-step tail probabilities `μ{U | C + δ/n ≤ |projInc_t U|}`; no other event, no
geometric hypothesis, and no martingale assumption enters. -/
theorem qpl_measure_max_abs_le_of_clip_union {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hεpos : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) (hδ : 0 < δ) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + ∑ t ∈ Finset.range n, (Swarming.Uniform.arrayMeasure N).real
            {U | C + δ / (n : ℝ) ≤ |Swarming.Enl.ProjLedger.projInc p m eps i j t U|} := by
  refine le_trans (qpl_measure_max_abs_le_of_clip hp0 hp1 hij hε hC hn hεpos hgap) ?_
  exact add_le_add le_rfl (qpl_defect_ge_le_union hn hδ p m eps i j)

/-! ### 4. The unconditional deterministic envelope of the projected increment

The only ingredients are the integrated polynomial bounds `abs_Hpot_envH_le` (site potential) and
`abs_Fcorr_bRec_le` (record correction).  They give a *deterministic, time-dependent* envelope
`Denv` for `projInc t`, hence an unconditional two-sided finite-horizon maximal bound with no
residual event at all.  The price is quantitative: at the paper's scale `n = T L` the envelope is
`≍ n² / eps`, so the exponent is far from what `(locmart)` needs.  The value of the statement is
that it makes the truncation theorems above non-vacuous and pins the missing input exactly: a
predictable envelope `C ≪ n` together with a bound on the truncation-active event. -/

/-- Envelope of the site potential at time `t` (`abs_Hpot_envH_le`). -/
noncomputable def Henv (t : ℕ) : ℝ := (t : ℝ) * (2 * (t : ℝ) + 3)

/-- Envelope of the record correction at time `t` (`abs_Fcorr_bRec_le`). -/
noncomputable def Fenv (p : ℝ) (m : ℕ) (eps : ℝ) (t : ℕ) : ℝ :=
  (2 * (t : ℝ) + 5) ^ 2 / (eps * (1 - Swarming.Enl.aRec p m) ^ 2)

/-- Envelope of the projected increment at time `t`. -/
noncomputable def Denv (p : ℝ) (m : ℕ) (eps : ℝ) (t : ℕ) : ℝ :=
  2 * Henv (t + 1) + 2 * Henv t + 2 * Fenv p m eps (t + 1) + 4 * Fenv p m eps t

theorem Henv_nonneg (t : ℕ) : 0 ≤ Henv t := by
  simp only [Henv]; positivity

theorem Henv_mono : Monotone Henv := by
  intro a b hab
  have ha : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  simp only [Henv]
  nlinarith

theorem one_sub_aRec_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) :
    0 < 1 - Swarming.Enl.aRec p m := by
  have h := Swarming.Enl.aRec_lt_one hp0 hp1 m
  linarith

theorem Fenv_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {eps : ℝ}
    (hε : 0 < eps) (t : ℕ) : 0 < Fenv p m eps t := by
  have h := one_sub_aRec_pos hp0 hp1 m
  simp only [Fenv]
  positivity

theorem Fenv_nonneg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {eps : ℝ}
    (hε : 0 < eps) (t : ℕ) : 0 ≤ Fenv p m eps t :=
  (Fenv_pos hp0 hp1 m hε t).le

theorem Fenv_mono {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {eps : ℝ}
    (hε : 0 < eps) : Monotone (Fenv p m eps) := by
  intro a b hab
  have ha : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hden : 0 < eps * (1 - Swarming.Enl.aRec p m) ^ 2 := by
    have h := one_sub_aRec_pos hp0 hp1 m
    positivity
  have hnum : (2 * (a : ℝ) + 5) ^ 2 ≤ (2 * (b : ℝ) + 5) ^ 2 := by nlinarith
  simp only [Fenv]
  exact div_le_div_of_nonneg_right hnum hden.le

theorem Denv_pos {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {eps : ℝ}
    (hε : 0 < eps) (t : ℕ) : 0 < Denv p m eps t := by
  have h := Fenv_pos hp0 hp1 m hε t
  have h1 := Henv_nonneg (t + 1)
  have h2 := Henv_nonneg t
  have h3 := Fenv_pos hp0 hp1 m hε (t + 1)
  simp only [Denv]
  nlinarith

theorem Denv_mono {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ) {eps : ℝ}
    (hε : 0 < eps) : Monotone (Denv p m eps) := by
  intro a b hab
  have h1 := Henv_mono (Nat.le_succ a)
  have h2 := Henv_mono hab
  have h3 := Henv_mono (show a + 1 ≤ b + 1 from Nat.succ_le_succ hab)
  have h4 := Fenv_mono hp0 hp1 m hε (Nat.le_succ a)
  have h5 := Fenv_mono hp0 hp1 m hε hab
  have h6 := Fenv_mono hp0 hp1 m hε (show a + 1 ≤ b + 1 from Nat.succ_le_succ hab)
  simp only [Denv]
  nlinarith

/-- `abs_Zpot_le` in the notation of the envelopes. -/
theorem abs_Zpot_le_env {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) (U : Swarming.Uniform.Array N) :
    |Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t| ≤ Henv t + Fenv p m eps t := by
  have h := Swarming.Enl.ProjHonest.abs_Zpot_le hp0 hp1 m i j hε t U
  simpa only [Henv, Fenv] using h

/-- **The projected potential has the polynomial envelope a.e.**  This is where the option
projection enters: the bound is only available almost surely, since `Zproj t` is a conditional
expectation. -/
theorem ae_abs_Zproj_le_env {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      |Swarming.Enl.ProjLedger.Zproj p m eps i j t U| ≤ Henv t + Fenv p m eps t := by
  haveI : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  set B : ℝ := Henv t + Fenv p m eps t with hB
  have hint : Integrable
      (fun U => Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t)
      (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Enl.VdriftAssembly.integrable_Zpot hp0 hp1 m i j hε t
  have hpt : ∀ U, |Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t| ≤ B := by
    intro U; rw [hB]; exact abs_Zpot_le_env hp0 hp1 m i j hε t U
  have h1 : (Swarming.Uniform.arrayMeasure N)[
        fun U => Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t |
        Swarming.Enl.enlFilt p m t] ≤ᵐ[Swarming.Uniform.arrayMeasure N] fun _ => B := by
    have h := MeasureTheory.condExp_mono (m := Swarming.Enl.enlFilt p m t)
      (μ := Swarming.Uniform.arrayMeasure N) hint (integrable_const B)
      (Filter.Eventually.of_forall fun U => (abs_le.1 (hpt U)).2)
    simpa only [MeasureTheory.condExp_const ((Swarming.Enl.enlFilt p m).le t)] using h
  have h2 : (fun _ => -B) ≤ᵐ[Swarming.Uniform.arrayMeasure N]
      (Swarming.Uniform.arrayMeasure N)[
        fun U => Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t |
        Swarming.Enl.enlFilt p m t] := by
    have h := MeasureTheory.condExp_mono (m := Swarming.Enl.enlFilt p m t)
      (μ := Swarming.Uniform.arrayMeasure N) (integrable_const (-B)) hint
      (Filter.Eventually.of_forall fun U => (abs_le.1 (hpt U)).1)
    simpa only [MeasureTheory.condExp_const ((Swarming.Enl.enlFilt p m).le t)] using h
  filter_upwards [h1, h2] with U h1' h2'
  show |(Swarming.Uniform.arrayMeasure N)[
      fun U => Swarming.Enl.VdriftAssembly.Zpot p m eps i j U t |
      Swarming.Enl.enlFilt p m t] U| ≤ B
  exact abs_le.2 ⟨h2', h1'⟩

/-- The record-cost increment is bounded by two record envelopes, pointwise. -/
theorem abs_Jcorr_le_env {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) (U : Swarming.Uniform.Array N) :
    |Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t|
      ≤ Fenv p m eps (t + 1) + Fenv p m eps t := by
  have h1 := Swarming.Enl.VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m (t + 1) j hε U
    ((Swarming.Trajectory.trajectory p m U (t + 1)).pos i
      - Swarming.Trajectory.runMax p m U j (t + 1))
  have h2 := Swarming.Enl.VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m t j hε U
    ((Swarming.Trajectory.trajectory p m U (t + 1)).pos i
      - Swarming.Trajectory.runMax p m U j t)
  simp only [Swarming.Enl.VdriftAssembly.Jcorr, Fenv]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- The one-step potential increment is bounded by two potential envelopes, pointwise. -/
theorem abs_HpotInc_le_env {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (m : ℕ)
    (i j : Fin N) (t : ℕ) (U : Swarming.Uniform.Array N) :
    |Swarming.Enl.HpotInc p m t i j U| ≤ Henv (t + 1) + Henv t := by
  have hx1 : |((Swarming.Trajectory.trajectory p m U (t + 1)).pos i)| ≤ ((t + 1 : ℕ) : ℤ) :=
    Swarming.Enl.ZBudget.abs_pos_le_time p m U i (t + 1)
  have hx0 : |((Swarming.Trajectory.trajectory p m U t).pos i)| ≤ ((t : ℕ) : ℤ) :=
    Swarming.Enl.ZBudget.abs_pos_le_time p m U i t
  have h1 := Swarming.Enl.ProjHonest.abs_Hpot_envH_le hp0 hp1 m (t + 1) j U hx1
  have h2 := Swarming.Enl.ProjHonest.abs_Hpot_envH_le hp0 hp1 m t j U hx0
  simp only [Swarming.Enl.HpotInc, Henv]
  push_cast at h1 h2 ⊢
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- The correction drift is bounded by twice the record envelope. -/
theorem abs_corrDrift_le {a eps α b : ℝ} {g : ℤ} {F : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hF : ∀ y, |SwarmOcc.Fcorr a eps b y| ≤ F) :
    |Swarming.Enl.VdriftAssembly.corrDrift a eps α b g| ≤ 2 * F := by
  have h1 := hF (g + 1)
  have h2 := hF (g - 1)
  have h3 := hF g
  have hFnn : 0 ≤ F := (abs_nonneg _).trans h1
  have h1m : α * |SwarmOcc.Fcorr a eps b (g + 1)| ≤ α * F :=
    mul_le_mul_of_nonneg_left h1 hα0
  have h1' : |α * SwarmOcc.Fcorr a eps b (g + 1)| ≤ α * F := by
    rw [abs_mul, abs_of_nonneg hα0]; exact h1m
  have h2' : |(1 - α) * SwarmOcc.Fcorr a eps b (g - 1)| ≤ (1 - α) * F := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have hnn : 0 ≤ 1 - α := by linarith
  calc |Swarming.Enl.VdriftAssembly.corrDrift a eps α b g|
      = |α * SwarmOcc.Fcorr a eps b (g + 1) + (1 - α) * SwarmOcc.Fcorr a eps b (g - 1)
          - SwarmOcc.Fcorr a eps b g| := by
        simp only [Swarming.Enl.VdriftAssembly.corrDrift]
    _ ≤ |α * SwarmOcc.Fcorr a eps b (g + 1) + (1 - α) * SwarmOcc.Fcorr a eps b (g - 1)|
          + |SwarmOcc.Fcorr a eps b g| := abs_sub _ _
    _ ≤ (|α * SwarmOcc.Fcorr a eps b (g + 1)| + |(1 - α) * SwarmOcc.Fcorr a eps b (g - 1)|)
          + |SwarmOcc.Fcorr a eps b g| := by
        have := abs_add_le (α * SwarmOcc.Fcorr a eps b (g + 1))
          ((1 - α) * SwarmOcc.Fcorr a eps b (g - 1))
        linarith
    _ ≤ (α * F + (1 - α) * F) + F := by linarith
    _ = 2 * F := by ring

/-- The `Edrift` term has the envelope `H(t+1) + H t + 2 F t`, a.e. -/
theorem ae_abs_Edrift_le_env {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      |Swarming.Enl.VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t|
        ≤ Henv (t + 1) + Henv t + 2 * Fenv p m eps t := by
  classical
  haveI : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure N
  set B : ℝ := Henv (t + 1) + Henv t with hB
  have hint : Integrable (fun U => Swarming.Enl.HpotInc p m t i j U)
      (Swarming.Uniform.arrayMeasure N) :=
    Swarming.Enl.integrable_HpotInc hp0 hp1 (by linarith : p ≠ 0) m t i j
  have hpt : ∀ U, |Swarming.Enl.HpotInc p m t i j U| ≤ B := by
    intro U; rw [hB]; exact abs_HpotInc_le_env hp0 hp1 m i j t U
  have h1 : (Swarming.Uniform.arrayMeasure N)[fun U => Swarming.Enl.HpotInc p m t i j U |
        Swarming.Enl.enlFilt p m t] ≤ᵐ[Swarming.Uniform.arrayMeasure N] fun _ => B := by
    have h := MeasureTheory.condExp_mono (m := Swarming.Enl.enlFilt p m t)
      (μ := Swarming.Uniform.arrayMeasure N) hint (integrable_const B)
      (Filter.Eventually.of_forall fun U => (abs_le.1 (hpt U)).2)
    simpa only [MeasureTheory.condExp_const ((Swarming.Enl.enlFilt p m).le t)] using h
  have h2 : (fun _ => -B) ≤ᵐ[Swarming.Uniform.arrayMeasure N]
      (Swarming.Uniform.arrayMeasure N)[fun U => Swarming.Enl.HpotInc p m t i j U |
        Swarming.Enl.enlFilt p m t] := by
    have h := MeasureTheory.condExp_mono (m := Swarming.Enl.enlFilt p m t)
      (μ := Swarming.Uniform.arrayMeasure N) (integrable_const (-B)) hint
      (Filter.Eventually.of_forall fun U => (abs_le.1 (hpt U)).1)
    simpa only [MeasureTheory.condExp_const ((Swarming.Enl.enlFilt p m).le t)] using h
  filter_upwards [h1, h2] with U h1' h2'
  have hcd : |Swarming.Enl.VdriftAssembly.corrDrift (Swarming.Enl.aRec p m) eps
      (SwarmCross.alphaFun p m t i U) (Swarming.Enl.bRec p m t j U)
      ((Swarming.Trajectory.trajectory p m U t).pos i
        - Swarming.Trajectory.runMax p m U j t)| ≤ 2 * Fenv p m eps t := by
    refine abs_corrDrift_le ?_ ?_ (fun y => ?_)
    · exact (Swarming.Enl.one_half_le_alphaFun hp0 hp1 m t i U).trans' (by norm_num)
    · exact (Swarming.Transition.currentAlpha_lt_one hp0 hp1 m U t i).le
    · exact Swarming.Enl.VdriftAssembly.abs_Fcorr_bRec_le hp0 hp1 m t j hε U y
  have hcond : |(Swarming.Uniform.arrayMeasure N)[fun U => Swarming.Enl.HpotInc p m t i j U |
      Swarming.Enl.enlFilt p m t] U| ≤ B := abs_le.2 ⟨h2', h1'⟩
  simp only [Swarming.Enl.VdriftAssembly.Edrift]
  calc |(Swarming.Uniform.arrayMeasure N)[fun U => Swarming.Enl.HpotInc p m t i j U |
        Swarming.Enl.enlFilt p m t] U
      - Swarming.Enl.VdriftAssembly.corrDrift (Swarming.Enl.aRec p m) eps
        (SwarmCross.alphaFun p m t i U) (Swarming.Enl.bRec p m t j U)
        ((Swarming.Trajectory.trajectory p m U t).pos i
          - Swarming.Trajectory.runMax p m U j t)|
      ≤ |(Swarming.Uniform.arrayMeasure N)[fun U => Swarming.Enl.HpotInc p m t i j U |
            Swarming.Enl.enlFilt p m t] U| + 2 * Fenv p m eps t := by
        exact (abs_sub _ _).trans (add_le_add le_rfl hcd)
    _ ≤ B + 2 * Fenv p m eps t := by linarith
    _ = Henv (t + 1) + Henv t + 2 * Fenv p m eps t := by rw [hB]

/-- **The unconditional deterministic envelope of the projected increment.** -/
theorem ae_abs_projInc_le_env {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (i j : Fin N) {eps : ℝ} (hε : 0 < eps) (t : ℕ) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      |Swarming.Enl.ProjLedger.projInc p m eps i j t U| ≤ Denv p m eps t := by
  filter_upwards [ae_abs_Zproj_le_env (N := N) hp0 hp1 (m := m) i j hε (t + 1),
    ae_abs_Zproj_le_env (N := N) hp0 hp1 (m := m) i j hε t,
    ae_abs_Edrift_le_env (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t] with U h1 h2 h3
  have h4 := abs_Jcorr_le_env (N := N) hp0 hp1 m i j hε t U
  simp only [Swarming.Enl.ProjLedger.projInc, Denv]
  have hA : |(Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
        - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      + Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t
      - Swarming.Enl.VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t|
      ≤ |(Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
        - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      + Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t|
      + |Swarming.Enl.VdriftAssembly.Edrift p m eps
          (fun r => SwarmCross.alphaFun p m r i) i j U t| := by
    have h := abs_add_le ((Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
        - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      + Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t)
      (- Swarming.Enl.VdriftAssembly.Edrift p m eps
        (fun r => SwarmCross.alphaFun p m r i) i j U t)
    rw [abs_neg] at h
    rwa [sub_eq_add_neg]
  have hB : |(Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
        - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      + Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t|
      ≤ |Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U|
        + |Swarming.Enl.ProjLedger.Zproj p m eps i j t U|
        + |Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t| := by
    have h := abs_add_le (Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
      - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      (Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t)
    have h' := abs_sub (Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U)
      (Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
    linarith
  calc |(Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U
        - Swarming.Enl.ProjLedger.Zproj p m eps i j t U)
      + Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t
      - Swarming.Enl.VdriftAssembly.Edrift p m eps (fun r => SwarmCross.alphaFun p m r i) i j U t|
      ≤ |Swarming.Enl.ProjLedger.Zproj p m eps i j (t + 1) U|
        + |Swarming.Enl.ProjLedger.Zproj p m eps i j t U|
        + |Swarming.Enl.VdriftAssembly.Jcorr p m eps i j U t|
        + |Swarming.Enl.VdriftAssembly.Edrift p m eps
            (fun r => SwarmCross.alphaFun p m r i) i j U t| := by linarith
    _ ≤ 2 * Henv (t + 1) + 2 * Henv t + 2 * Fenv p m eps (t + 1) + 4 * Fenv p m eps t := by
        linarith

/-- **Unconditional two-sided finite-horizon maximal oscillation of the actual `Qpl`.**  With
`C = Denv p m eps n` the clip level dominates every increment up to the horizon a.e., so the defect
event of `qpl_measure_max_abs_le_of_clip` is null and disappears.  No hypothesis beyond
`1/2 < p < 1`, `0 < eps`, `i ≠ j` is used. -/
theorem qpl_measure_max_abs_le_uncond {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε)
    (hlarge : (n : ℝ) * Denv p m eps n < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-(((ε - (n : ℝ) * Denv p m eps n) / 2) ^ 2)
              / (16 * (n : ℝ) * (Denv p m eps n) ^ 2)) := by
  set C : ℝ := Denv p m eps n with hCdef
  have hC : 0 < C := Denv_pos hp0 hp1 m hε n
  set δ : ℝ := (ε - (n : ℝ) * C) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hgap : (n : ℝ) * C + δ < ε := by rw [hδdef]; linarith
  have hbound : ∀ t, t < n → ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      |Swarming.Enl.ProjLedger.projInc p m eps i j t U| ≤ C := by
    intro t ht
    filter_upwards [ae_abs_projInc_le_env (N := N) hp0 hp1 (m := m) (i := i) (j := j) hε t]
      with U hU
    have hmono : Denv p m eps t ≤ Denv p m eps n := Denv_mono hp0 hp1 m hε ht.le
    rw [hCdef]
    linarith
  have hnull : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∑ t ∈ Finset.range n,
        max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C) = 0 := by
    have hall : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
        ∀ t ∈ Finset.range n,
          max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C) = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro t
      by_cases ht : t ∈ Finset.range n
      · filter_upwards [hbound t (Finset.mem_range.1 ht)] with U hU
        intro _
        have hle : |Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C ≤ 0 := by linarith
        rw [max_eq_left hle]
      · filter_upwards with U
        intro hmem
        exact absurd hmem ht
    filter_upwards [hall] with U hU
    exact Finset.sum_eq_zero hU
  have hzero : (Swarming.Uniform.arrayMeasure N).real
      {U | δ ≤ ∑ t ∈ Finset.range n,
        max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)} = 0 := by
    have h0 : (Swarming.Uniform.arrayMeasure N)
        {U | ¬ (∑ t ∈ Finset.range n,
          max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C) = 0)} = 0 :=
      MeasureTheory.ae_iff.1 hnull
    have hsub : {U | δ ≤ ∑ t ∈ Finset.range n,
          max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)}
        ⊆ {U | ¬ (∑ t ∈ Finset.range n,
          max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C) = 0)} := by
      intro U hU
      simp only [Set.mem_ofPred_eq] at hU ⊢
      intro hz
      rw [hz] at hU
      linarith
    refine le_antisymm ?_ (by positivity)
    calc (Swarming.Uniform.arrayMeasure N).real
          {U | δ ≤ ∑ t ∈ Finset.range n,
            max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C)}
        ≤ (Swarming.Uniform.arrayMeasure N).real
            {U | ¬ (∑ t ∈ Finset.range n,
              max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j t U| - C) = 0)} :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ = 0 := by rw [measureReal_def, h0]; simp
  have hmain := qpl_measure_max_abs_le_of_clip (m := m) hp0 hp1 hij hε hC hn hεpos hgap
  rw [hzero, add_zero] at hmain
  refine hmain.trans_eq ?_
  congr 1
  rw [hδdef]
  ring_nf

/-! ### 5. Deterministic starts: the window `[s, s+n]`

The paper's `(locmart)` is a statement about `max_{t in [s,t] ⊂ [s, s+n]} |Q_t - Q_s|` for a
*deterministic* start `s` (random record starts are handled elsewhere, by a union over starts).
The abstract bounds above are stated for an arbitrary filtration, so they apply verbatim to the
shifted filtration; the only new ingredient is the telescoping identity
`psum (ξ_{s+·}) n = psum ξ (s+n) - psum ξ s`. -/

/-- Translation of a filtration by a deterministic time. -/
def fshift (ℱ : Filtration ℕ m0) (s : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (s + k)
  mono' _ _ hab := ℱ.mono (Nat.add_le_add_left hab s)
  le' k := ℱ.le (s + k)

/-- Telescoping: partial sums of the shifted increments are differences of partial sums. -/
theorem psum_shift (ξ : ℕ → Ω → ℝ) (s n : ℕ) (ω : Ω) :
    LocMart.psum (fun k => ξ (s + k)) n ω
      = LocMart.psum ξ (s + n) ω - LocMart.psum ξ s ω := by
  induction n with
  | zero => simp only [Nat.add_zero, LocMart.psum_zero, sub_self]
  | succ n ih =>
      have h : s + (n + 1) = (s + n) + 1 := by omega
      rw [LocMart.psum_succ, ih, h, LocMart.psum_succ]
      ring

/-- **Predictable truncation at a deterministic start `s`.**  Same bound as
`measure_max_abs_psum_le_of_ptrunc`, for the two-sided oscillation of the window `[s, s+n]`. -/
theorem measure_max_abs_psum_shift_le_of_ptrunc [IsProbabilityMeasure μ]
    {s : ℕ} {G : ℕ → Set Ω}
    (hG : ∀ k, MeasurableSet[ℱ (s + k)] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)] (ξ (s + k)))
    (hξi : ∀ k, Integrable (ξ (s + k)) μ)
    (hξ0 : ∀ k, μ[ξ (s + k) | ℱ (s + k)] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k ω, ω ∈ G k → |ξ (s + k) ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + μ.real {ω | ∃ k < n, ω ∉ G k} := by
  have h := measure_max_abs_psum_le_of_ptrunc (μ := μ) (ℱ := fshift ℱ s)
    (G := G) (ξ := fun k => ξ (s + k))
    (fun k => hG k) (fun k => hξm k) (fun k => hξi k) (fun k => hξ0 k) hC hbdd hn hε
  simpa only [psum_shift, fshift] using h

/-- **Predictable truncation at a deterministic start `s`, for the actual `Qpl`.** -/
theorem qpl_measure_max_abs_shift_le_of_predictable_trunc {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j)
    {eps : ℝ} (hε : 0 < eps) (s : ℕ)
    {G : ℕ → Set (Swarming.Uniform.Array N)}
    (hG : ∀ k, MeasurableSet[Swarming.Enl.enlFilt p m (s + k)] (G k))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k U, U ∈ G k →
      |Swarming.Enl.ProjLedger.projInc p m eps i j (s + k) U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U
          - Swarming.Enl.ProjLedger.Qpl p m eps i j s U|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + (Swarming.Uniform.arrayMeasure N).real {U | ∃ k < n, U ∉ G k} := by
  have h := measure_max_abs_psum_shift_le_of_ptrunc (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m) (s := s) (G := G)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    hG (fun k => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m (s + k) eps i j)
    (fun k => Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m (s + k) i j hε)
    (fun k => Swarming.Enl.ProjLedger.condExp_projInc_eq_zero hp0 hp1 m (s + k) i j hε)
    hC hbdd hn hεpos
  simpa only [psum_projInc_eq_Qpl] using h

/-- **Clipping with predictable centring at a deterministic start `s`.** -/
theorem measure_max_abs_psum_shift_le_of_clip [IsProbabilityMeasure μ]
    {s : ℕ} {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)] (ξ (s + k)))
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hε : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + μ.real {ω | δ ≤ ∑ t ∈ Finset.range n, max 0 (|ξ (s + t) ω| - C)} := by
  have h := measure_max_abs_psum_le_of_clip (μ := μ) (ℱ := fshift ℱ s)
    (ξ := fun k => ξ (s + k)) (fun k => hξm k) hC hn hε hgap
  simpa only [psum_shift, fshift] using h

/-- **Clipping with predictable centring at a deterministic start `s`, for the actual `Qpl`.** -/
theorem qpl_measure_max_abs_shift_le_of_clip {N : ℕ} {p : ℝ} (hp0 : (1 : ℝ) / 2 < p)
    (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j) {eps : ℝ} (hε : 0 < eps) (s : ℕ)
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) {ε δ : ℝ} (hεpos : 0 < ε)
    (hgap : (n : ℝ) * C + δ < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j (s + k) U
          - Swarming.Enl.ProjLedger.Qpl p m eps i j s U|}
      ≤ 2 * ((n : ℝ) + 1)
          * Real.exp (-((ε - (n : ℝ) * C - δ) ^ 2) / (16 * (n : ℝ) * C ^ 2))
        + (Swarming.Uniform.arrayMeasure N).real
            {U | δ ≤ ∑ t ∈ Finset.range n,
              max 0 (|Swarming.Enl.ProjLedger.projInc p m eps i j (s + t) U| - C)} := by
  have h := measure_max_abs_psum_shift_le_of_clip (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m) (s := s)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    (fun k => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m (s + k) eps i j)
    hC hn hεpos hgap
  simpa only [psum_projInc_eq_Qpl] using h

/-- **Predictable truncation with an almost-sure envelope.**  The hypothesis `|ξ k| ≤ C` on
`G k` is only required almost surely, which is what a potential/record envelope delivered through
conditional expectations gives.  The truncation set is intersected with the (measurable, but not
predictable) event `{|ξ k| ≤ C}`; the intersection differs from the predictable truncation only on
a null set, so the vanishing conditional mean survives, while the pointwise envelope `C` becomes
available for maximal Azuma. -/
noncomputable def ptruncAe (G : ℕ → Set Ω) (C : ℝ) (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  ((G k) ∩ {ω | |ξ k ω| ≤ C}).indicator (ξ k)

theorem measurableSet_abs_le {ξ : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0} {k : ℕ} {C : ℝ}
    (hξm : StronglyMeasurable[ℱ (k + 1)] (ξ k)) :
    MeasurableSet[ℱ (k + 1)] {ω | |ξ k ω| ≤ C} := by
  have h := StronglyMeasurable.measurableSet_le (m := ℱ (k + 1)) (f := fun ω => ‖ξ k ω‖)
    (g := fun _ => C) hξm.norm stronglyMeasurable_const
  simpa only [Real.norm_eq_abs] using h

theorem stronglyMeasurable_ptruncAe {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k)) {C : ℝ} (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (ptruncAe G C ξ k) := by
  have h1 : MeasurableSet[ℱ (k + 1)] (G k) :=
    MeasurableSpace.le_def.1 (ℱ.mono (Nat.le_succ k)) (G k) (hG k)
  have h2 : MeasurableSet[ℱ (k + 1)] {ω | |ξ k ω| ≤ C} := measurableSet_abs_le (hξm k)
  exact (hξm k).indicator (h1.inter h2)

theorem integrable_ptruncAe {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ} (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ) {C : ℝ} (k : ℕ) :
    Integrable (ptruncAe G C ξ k) μ := by
  have h1 : MeasurableSet (G k) := MeasurableSpace.le_def.1 (ℱ.le k) (G k) (hG k)
  have h2 : MeasurableSet {ω | |ξ k ω| ≤ C} :=
    isClosed_Iic.measurableSet.preimage (((hξm k).mono (ℱ.le (k + 1))).measurable.norm)
  exact (hξi k).indicator (h1.inter h2)

theorem abs_ptruncAe_le {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (ω : Ω) :
    |ptruncAe G C ξ k ω| ≤ C := by
  classical
  by_cases h : ω ∈ (G k) ∩ {ω | |ξ k ω| ≤ C}
  · rw [ptruncAe, Set.indicator_of_mem h]
    exact h.2
  · rw [ptruncAe, Set.indicator_of_notMem h, abs_zero]
    exact hC

theorem ae_ptruncAe_eq_ptrunc {G : ℕ → Set Ω} {ξ : ℕ → Ω → ℝ} {C : ℝ} {k : ℕ}
    (hae : ∀ᵐ ω ∂μ, ω ∈ G k → |ξ k ω| ≤ C) :
    ptruncAe G C ξ k =ᵐ[μ] ptrunc G ξ k := by
  classical
  filter_upwards [hae] with ω hω
  by_cases hmem : ω ∈ G k
  · have h1 : ω ∈ (G k) ∩ {ω | |ξ k ω| ≤ C} := ⟨hmem, hω hmem⟩
    rw [ptruncAe, Set.indicator_of_mem h1, ptrunc_eq_of_mem hmem]
  · have h1 : ω ∉ (G k) ∩ {ω | |ξ k ω| ≤ C} := fun h => hmem h.1
    rw [ptruncAe, Set.indicator_of_notMem h1, ptrunc_eq_zero_of_not_mem hmem]

/-- **Predictable truncation, almost-sure envelope version.** -/
theorem measure_max_abs_psum_le_of_ptrunc_ae [IsProbabilityMeasure μ]
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ξ k))
    (hξi : ∀ k, Integrable (ξ k) μ)
    (hξ0 : ∀ k, μ[ξ k | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → |ξ k ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + μ.real {ω | ∃ k < n, ω ∉ G k} := by
  classical
  let _ : MeasurableSpace Ω := m0
  set ξ' : ℕ → Ω → ℝ := ptruncAe G C ξ with hξ'def
  set N : Set Ω := ⋃ k, (G k ∩ {ω | C < |ξ k ω|}) with hNdef
  have hNnull : μ N = 0 := by
    rw [hNdef]
    refine measure_iUnion_null fun k => ?_
    have hk : μ {ω | ¬ (ω ∈ G k → |ξ k ω| ≤ C)} = 0 := MeasureTheory.ae_iff.1 (hbdd k)
    refine measure_mono_null ?_ hk
    intro ω hω
    exact fun hcon => absurd (hcon hω.1) (not_le.2 hω.2)
  have hξ'0 : ∀ k, μ[ξ' k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    have h1 : μ[ξ' k | ℱ k] =ᵐ[μ] μ[ptrunc G ξ k | ℱ k] :=
      MeasureTheory.condExp_congr_ae (ae_ptruncAe_eq_ptrunc (hbdd k))
    exact h1.trans (condExp_ptrunc_eq_zero hG hξi hξ0 k)
  have hsub : {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|} ⊆
      {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|} ∪ {ω | ∃ k < n, ω ∉ G k} ∪ N := by
    intro ω hω
    by_contra hcon
    have hS' : ω ∉ {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|} :=
      fun h => hcon (Or.inl (Or.inl h))
    have hBad : ω ∉ {ω | ∃ k < n, ω ∉ G k} := fun h => hcon (Or.inl (Or.inr h))
    have hN : ω ∉ N := fun h => hcon (Or.inr h)
    obtain ⟨k, hk, hdev⟩ := hω
    have hgood : ∀ j < n, ω ∈ G j := by
      intro j hj
      by_contra hjg
      exact hBad ⟨j, hj, hjg⟩
    have henv : ∀ j < n, |ξ j ω| ≤ C := by
      intro j hj
      by_contra hCj
      exact hN (Set.mem_iUnion.2 ⟨j, ⟨hgood j hj, not_le.1 hCj⟩⟩)
    have heq : LocMart.psum ξ' k ω = LocMart.psum ξ k ω := by
      refine psum_congr_lt fun j hj => ?_
      have hjn : j < n := lt_of_lt_of_le hj hk
      have hmem : ω ∈ (G j) ∩ {ω | |ξ j ω| ≤ C} := ⟨hgood j hjn, henv j hjn⟩
      show ptruncAe G C ξ j ω = ξ j ω
      rw [ptruncAe, Set.indicator_of_mem hmem]
    exact hS' ⟨k, hk, by rwa [heq]⟩
  have hAz := LocMart.measure_max_abs_psum_ge_le (μ := μ) (ℱ := ℱ) (ξ := ξ')
    (fun k => stronglyMeasurable_ptruncAe hG hξm (C := C) k) hC
    (abs_ptruncAe_le hC.le) hξ'0 hn hε
  have hNreal : μ.real N = 0 := by rw [measureReal_def, hNnull]; simp
  calc μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ k ω|}
      ≤ μ.real ({ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|}
          ∪ {ω | ∃ k < n, ω ∉ G k} ∪ N) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real ({ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|}
          ∪ {ω | ∃ k < n, ω ∉ G k}) + μ.real N :=
        measureReal_union_le _ _
    _ = μ.real ({ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|}
          ∪ {ω | ∃ k < n, ω ∉ G k}) := by rw [hNreal, add_zero]
    _ ≤ μ.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum ξ' k ω|}
          + μ.real {ω | ∃ k < n, ω ∉ G k} := measureReal_union_le _ _
    _ ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
          + μ.real {ω | ∃ k < n, ω ∉ G k} := add_le_add hAz le_rfl

/-- The almost-sure-envelope form for the actual `Qpl`. -/
theorem qpl_measure_max_abs_le_of_predictable_trunc_ae {N : ℕ} {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} {i j : Fin N} (hij : i ≠ j)
    {eps : ℝ} (hε : 0 < eps)
    {G : ℕ → Set (Swarming.Uniform.Array N)}
    (hG : ∀ t, MeasurableSet[Swarming.Enl.enlFilt p m t] (G t))
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ t, ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      U ∈ G t → |Swarming.Enl.ProjLedger.projInc p m eps i j t U| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hεpos : 0 < ε) :
    (Swarming.Uniform.arrayMeasure N).real
        {U | ∃ k ≤ n, ε ≤ |Swarming.Enl.ProjLedger.Qpl p m eps i j k U|}
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))
        + (Swarming.Uniform.arrayMeasure N).real {U | ∃ t < n, U ∉ G t} := by
  have h := measure_max_abs_psum_le_of_ptrunc_ae (μ := Swarming.Uniform.arrayMeasure N)
    (ℱ := Swarming.Enl.enlFilt p m) (G := G)
    (ξ := fun t (U : Swarming.Uniform.Array N) =>
      Swarming.Enl.ProjLedger.projInc p m eps i j t U)
    hG (fun t => Swarming.Enl.ProjLedger.stronglyMeasurable_projInc hp0.le m t eps i j)
    (fun t => Swarming.Enl.ProjLedger.integrable_projInc hp0 hp1 m t i j hε)
    (fun t => Swarming.Enl.ProjLedger.condExp_projInc_eq_zero hp0 hp1 m t i j hε)
    hC hbdd hn hεpos
  simpa only [psum_projInc_eq_Qpl] using h

end QplOsc
