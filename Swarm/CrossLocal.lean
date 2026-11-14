/-
  **Localized (event-conditional) forms of `Swarm/Cross.lean`.**

  The integrated crossing layer requires the walker to sit at the top `b1` of the window at the
  reveal time `s` **almost everywhere**: `hstart : ∀ᵐ ω, X s ω = b1`.  At the actual model that
  holds only on the bad-time event.  The three theorems are therefore restated with the `b1`
  hypothesis localized to an `ℱ s`-measurable event `A`: the global hypothesis becomes
  `b0 ≤ X s` (true everywhere for the frozen process) plus `X s = b1` **on `A`**.  The
  conclusions are already of the form `μ.real (… ∩ A) ≤ ∫_A …`, so they are unchanged.

  The proofs are the verified ones of `Cross.lean`; the only edits are the two places where
  `hstart` is consumed.  Everything is stated for a finite measure, so the layer can also be
  applied after conditioning on an event.  Names are placed in a separate namespace so that
  both the original and the localized forms are available.
-/
import Swarm.Cross
import Swarm.Diag
import Swarm.Step
import Swarm.Step2
import Swarm.SubSigma

open MeasureTheory Filter
open scoped Topology BigOperators

namespace SwarmSpeedLoc

open SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}

section Bound

variable [IsProbabilityMeasure μ] (hb : b0 ≤ b1) (hX : ∀ n, Measurable[ℱ n] (X n))

include hb hX

/-- **Finite-horizon conditional crossing bound in the revealed environment.**

For every `ℱ_s`-measurable `A`, the probability (under `μ`) that the run started at the top
level `b1` at time `s` exits the window `[b0, b1+1]` at the bottom level `b0` before time
`s+N` is at most `∫_A (1 - f(b1))`, where `f` is the scale function of the *revealed* weights
`ω ↦ wf ω`.  This is the conditional form of eq. (cross): no independence of the environment
from the future is used, only `ℱ_s`-measurability of the revealed weights. -/
theorem cross_prob_shift_le_N_local {s N : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω)
    (hstartA : ∀ᵐ ω ∂μ, ω ∈ A → X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (crossEvent X b0 b1 s N ∩ A)
      ≤ ∫ x in A, (1 - scDiag wf b0 b1 (fun _ => b1) x) ∂μ := by
  classical
  have hconf : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → b0 ≤ X n ω ∧ X n ω ≤ b1 + 1 :=
    ae_confined_shift (s := s) hstep hrange hX0b
  have hsub := submartingale_scD_shift (s := s) hb hX hw hloh hhih hrange hstep hdom
  set F : ℕ → Ω → ℝ := fun k ω => scDiag wf b0 b1 (fun ω' => X (s + k) ω') ω with hF
  have hsubF : Submartingale F (shiftF ℱ s) μ := hsub
  have hτ : IsStoppingTime (shiftF ℱ s) (shiftExit X b0 b1 s) := isStoppingTime_shiftExit hX s
  have hstop : Submartingale (stoppedProcess F (shiftExit X b0 b1 s)) (shiftF ℱ s) μ :=
    hsubF.stoppedProcess hτ
  have hA' : MeasurableSet[(shiftF ℱ s) 0] A := hA
  have hsetint := hstop.setIntegral_le (Nat.zero_le N) hA'
  -- the time-zero value is `f(b1)` on `A`
  have h0val : ∀ᵐ ω ∂μ, (stoppedProcess F (shiftExit X b0 b1 s)) 0 ω = F 0 ω := by
    filter_upwards with ω
    exact stoppedProcess_eq_of_le (u := F) (τ := shiftExit X b0 b1 s) (i := 0) (zero_le)
  have hF0A : ∀ᵐ x ∂μ, x ∈ A → F 0 x = scDiag wf b0 b1 (fun _ => b1) x := by
    filter_upwards [hstartA] with ω hω hA
    rw [hF]
    refine scDiag_congr ?_
    show X (s + 0) ω = b1
    simpa using hω hA
  have h0eq : ∫ x in A, (stoppedProcess F (shiftExit X b0 b1 s)) 0 x ∂μ
      = ∫ x in A, scDiag wf b0 b1 (fun _ => b1) x ∂μ := by
    refine setIntegral_congr_ae ((ℱ.le s) A hA) ?_
    filter_upwards [h0val, hF0A] with ω h1 h2 hmem
    rw [h1]
    exact h2 hmem
  have hstep1 : ∫ x in A, scDiag wf b0 b1 (fun _ => b1) x ∂μ
      ≤ ∫ x in A, (stoppedProcess F (shiftExit X b0 b1 s)) N x ∂μ := by
    rw [← h0eq]
    exact hsetint
  -- pointwise comparison of the bottom-exit event with the stopped scale value
  have hintF : ∀ᵐ ω ∂μ, ∀ k, ‖F k ω‖ ≤ 1 := by
    filter_upwards [hloh, hhih, hconf] with ω h1 h2 h3 k
    rw [hF]
    exact norm_scDiag_le_one h1 h2 hb (h3 (s + k) (by omega)).2
  have hind : ∀ᵐ ω ∂μ, (crossEvent X b0 b1 s N ∩ A).indicator (1 : Ω → ℝ) ω
      ≤ 1 - (stoppedProcess F (shiftExit X b0 b1 s)) N ω := by
    filter_upwards [hconf, hintF] with ω hc hF1
    by_cases hN : shiftExit X b0 b1 s ω ≤ (N : ℕ∞)
    · rw [stoppedProcess_eq_of_ge (u := F) (τ := shiftExit X b0 b1 s) (i := N) hN]
      by_cases hmem : ω ∈ crossEvent X b0 b1 s N ∩ A
      · have hb0 : X (s + (shiftExit X b0 b1 s ω).untopA) ω = b0 := hmem.1.2
        rw [Set.indicator_of_mem hmem]
        show (1 : ℝ) ≤ 1 - scDiag wf b0 b1
          (fun ω' => X (s + (shiftExit X b0 b1 s ω).untopA) ω') ω
        rw [scDiag_congr (g := fun ω' => X (s + (shiftExit X b0 b1 s ω).untopA) ω')
            (h := fun _ => b0) hb0,
          scDiag_apply (wf := wf) (g := fun _ => b0) (ω := ω) (by show b0 ≤ b1 + 1; omega),
          sc_b0]
        norm_num
      · rw [Set.indicator_of_notMem hmem]
        have hle : F (shiftExit X b0 b1 s ω).untopA ω ≤ 1 := by
          have h := hF1 (shiftExit X b0 b1 s ω).untopA
          rw [Real.norm_eq_abs] at h
          exact (abs_le.mp h).2
        linarith
    · have hnotmem : ω ∉ crossEvent X b0 b1 s N ∩ A := fun hc => hN hc.1.1
      rw [Set.indicator_of_notMem hnotmem,
        stoppedProcess_eq_of_le (u := F) (τ := shiftExit X b0 b1 s) (i := N) (le_of_lt (not_le.mp hN))]
      have hle : F N ω ≤ 1 := by
        have h := hF1 N
        rw [Real.norm_eq_abs] at h
        exact (abs_le.mp h).2
      linarith
  -- integrate the pointwise comparison
  have hEmeas : MeasurableSet (crossEvent X b0 b1 s N ∩ A) := by
    have h1 : MeasurableSet[(shiftF ℱ s) N] {ω | shiftExit X b0 b1 s ω ≤ (N : ℕ∞)} := hτ N
    have h2 : MeasurableSet[(shiftF ℱ s) N]
        {ω | stoppedProcess (shiftX X s) (shiftExit X b0 b1 s) N ω = b0} := by
      have hsa : StronglyAdapted (shiftF ℱ s) (shiftX X s) := fun k => (hX (s + k)).stronglyMeasurable
      exact (hsa.stoppedProcess_of_discrete hτ N).measurable (measurableSet_singleton b0)
    have h3 : MeasurableSet[(shiftF ℱ s) N] (crossEvent X b0 b1 s N) := by
      rw [crossEvent_eq]
      exact h1.inter h2
    have hA'N : MeasurableSet[(shiftF ℱ s) N] A := ((shiftF ℱ s).mono (Nat.zero_le N)) A hA'
    exact (shiftF ℱ s).le N _ (h3.inter hA'N)
  have hI1 : IntegrableOn ((crossEvent X b0 b1 s N ∩ A).indicator (1 : Ω → ℝ)) A μ :=
    ((integrable_const (1 : ℝ)).indicator hEmeas).integrableOn
  have hI2 : IntegrableOn
      (fun ω => 1 - (stoppedProcess F (shiftExit X b0 b1 s)) N ω) A μ :=
    ((integrable_const (1 : ℝ)).sub (hstop.integrable N)).integrableOn
  have hmono : ∫ x in A, (crossEvent X b0 b1 s N ∩ A).indicator (1 : Ω → ℝ) x ∂μ
      ≤ ∫ x in A, (1 - (stoppedProcess F (shiftExit X b0 b1 s)) N x) ∂μ :=
    setIntegral_mono_ae hI1 hI2 hind
  have hconst : ∫ x in A, (1 : ℝ) ∂μ = μ.real A := by
    rw [MeasureTheory.setIntegral_const]
    simp
  have hleft : ∫ x in A, (crossEvent X b0 b1 s N ∩ A).indicator (1 : Ω → ℝ) x ∂μ
      = μ.real (crossEvent X b0 b1 s N ∩ A) := by
    have h := integral_indicator_one (μ := μ.restrict A)
      (s := crossEvent X b0 b1 s N ∩ A) hEmeas
    have h2 : (μ.restrict A).real (crossEvent X b0 b1 s N ∩ A)
        = μ.real (crossEvent X b0 b1 s N ∩ A) := by
      show ((μ.restrict A) (crossEvent X b0 b1 s N ∩ A)).toReal
        = (μ (crossEvent X b0 b1 s N ∩ A)).toReal
      rw [Measure.restrict_apply hEmeas, Set.inter_assoc, Set.inter_self]
    rw [h2] at h
    exact h
  have hright : ∫ x in A, (1 - (stoppedProcess F (shiftExit X b0 b1 s)) N x) ∂μ
      = μ.real A - ∫ x in A, (stoppedProcess F (shiftExit X b0 b1 s)) N x ∂μ := by
    have h := MeasureTheory.integral_sub (μ := μ.restrict A) (f := fun _ => (1 : ℝ))
      (g := fun x => (stoppedProcess F (shiftExit X b0 b1 s)) N x) (integrable_const 1)
      ((hstop.integrable N).integrableOn)
    simpa only [Pi.one_apply, hconst] using h
  have hsplit : ∫ x in A, (1 - scDiag wf b0 b1 (fun _ => b1) x) ∂μ
      = μ.real A - ∫ x in A, scDiag wf b0 b1 (fun _ => b1) x ∂μ := by
    have hsc : Integrable (fun x => scDiag wf b0 b1 (fun _ => b1) x) μ := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (measurable_scDiag (m := m0) (fun x => (hw x).mono (ℱ.le s) le_rfl)
          measurable_const).aestronglyMeasurable
      · filter_upwards [hloh, hhih] with ω h1 h2
        exact norm_scDiag_le_one h1 h2 hb (by omega)
    have h := MeasureTheory.integral_sub (μ := μ.restrict A) (f := fun _ => (1 : ℝ))
      (g := fun x => scDiag wf b0 b1 (fun _ => b1) x) (integrable_const 1) hsc.integrableOn
    simpa only [Pi.one_apply, hconst] using h
  rw [hleft, hright] at hmono
  rw [hsplit]
  linarith [hstep1]

/-! ### The limit over the horizon -/

/-- The event that, counted from time `s`, the walker eventually exits the window at the
bottom level `b0`, i.e. the paper's `{T_{b0}(s) < T_{b1+1}(s)}` in exit form. -/
def exitBottomShift (X : ℕ → Ω → ℕ) (b0 b1 s : ℕ) : Set Ω :=
  {ω | shiftExit X b0 b1 s ω ≠ ⊤ ∧
    shiftX X s (shiftExit X b0 b1 s ω).untopA ω = b0}

omit hb hX in
lemma mem_crossEvent {N : ℕ} {ω : Ω} :
    ω ∈ crossEvent X b0 b1 s N ↔
      (shiftExit X b0 b1 s ω ≤ (N : ℕ∞) ∧
        shiftX X s (shiftExit X b0 b1 s ω).untopA ω = b0) := Iff.rfl

include hb hX in
/-- **Conditional crossing bound, full horizon** (the conditional form of eq. (cross)). -/
theorem cross_prob_shift_le_local {s : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω)
    (hstartA : ∀ᵐ ω ∂μ, ω ∈ A → X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (exitBottomShift X b0 b1 s ∩ A)
      ≤ ∫ x in A, (1 - scDiag wf b0 b1 (fun _ => b1) x) ∂μ := by
  classical
  have hmono : Monotone (fun N => crossEvent X b0 b1 s N ∩ A) := by
    intro N M hNM ω hω
    rw [Set.mem_inter_iff] at hω ⊢
    obtain ⟨h1, h2⟩ := hω
    refine ⟨?_, h2⟩
    rw [mem_crossEvent] at h1 ⊢
    exact ⟨le_trans h1.1 (by exact_mod_cast hNM), h1.2⟩
  have hUnion : (⋃ N, crossEvent X b0 b1 s N ∩ A) = exitBottomShift X b0 b1 s ∩ A := by
    rw [← Set.iUnion_inter]
    congr 1
    ext ω
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hN, hb0⟩
      exact ⟨ne_top_of_le_ne_top (by exact_mod_cast WithTop.coe_ne_top) hN, hb0⟩
    · rintro ⟨hne, hb0⟩
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      exact ⟨n, le_of_eq hn.symm, hb0⟩
  have htend : Tendsto (fun N => μ (crossEvent X b0 b1 s N ∩ A)) atTop
      (nhds (μ (exitBottomShift X b0 b1 s ∩ A))) := by
    rw [← hUnion]
    exact tendsto_measure_iUnion_atTop hmono
  have hfin : μ (exitBottomShift X b0 b1 s ∩ A) ≠ ⊤ := measure_ne_top μ _
  have htendreal : Tendsto (fun N => μ.real (crossEvent X b0 b1 s N ∩ A)) atTop
      (nhds (μ.real (exitBottomShift X b0 b1 s ∩ A))) := by
    have h := (ENNReal.tendsto_toReal hfin).comp htend
    simpa [Measure.real, Function.comp_def] using h
  exact le_of_tendsto' htendreal
    (fun N => cross_prob_shift_le_N_local hb hX hw hloh hhih hrange hstep hdom hX0b hstartA hA)

include hb hX in
/-- **The paper's right-hand side**: the revealed potential `R = ∏_{x=b0+1}^{b1} r(ω_j(x))`. -/
theorem cross_prob_shift_le_R_local {s : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω)
    (hstartA : ∀ᵐ ω ∂μ, ω ∈ A → X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (exitBottomShift X b0 b1 s ∩ A) ≤ ∫ x in A, R (wf x) b0 b1 ∂μ := by
  classical
  refine (cross_prob_shift_le_local hb hX hw hloh hhih hrange hstep hdom hX0b hstartA hA).trans ?_
  have hscm : Measurable (fun x => (1 : ℝ) - scDiag wf b0 b1 (fun _ => b1) x) :=
    measurable_const.sub (measurable_scDiag (m := m0) (fun x => (hw x).mono (ℱ.le s) le_rfl)
      measurable_const)
  have hRm : Measurable (fun x => R (wf x) b0 b1) :=
    measurable_R_diag (m := m0) (fun x => (hw x).mono (ℱ.le s) le_rfl) b0 b1
  refine setIntegral_mono_ae ?_ ?_ ?_
  · refine Integrable.integrableOn (Integrable.of_bound hscm.aestronglyMeasurable 1 ?_)
    filter_upwards [hloh, hhih] with ω h1 h2
    have hsc : scDiag wf b0 b1 (fun _ => b1) ω = sc (wf ω) b0 b1 b1 :=
      scDiag_apply (by omega)
    have h0 : 0 ≤ sc (wf ω) b0 b1 b1 := sc_nonneg h1 h2 hb b1
    have h3 : sc (wf ω) b0 b1 b1 ≤ 1 := sc_le_one h1 h2 hb (show b1 ≤ b1 + 1 by omega)
    rw [Real.norm_eq_abs, abs_le, hsc]
    constructor <;> linarith
  · refine Integrable.integrableOn (Integrable.of_bound hRm.aestronglyMeasurable 1 ?_)
    filter_upwards [hloh, hhih] with ω h1 h2
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [R_nonneg h1 h2 (b0 := b0) (y := b1)],
      R_le_one h1 h2 (b0 := b0) (y := b1)⟩
  · filter_upwards [hloh, hhih] with ω h1 h2
    have hsc : scDiag wf b0 b1 (fun _ => b1) ω = sc (wf ω) b0 b1 b1 :=
      scDiag_apply (by omega)
    rw [hsc]
    exact one_sub_sc_le h1 h2 hb

include hb hX in
/-- **The conditional crossing estimate in the paper's own notation**:
on any `ℱ_s`-measurable event `A`, `P(T_{b0}(s) < T_{b1+1}(s) ; A) ≤ ∫_A ∏_{x=b0+1}^{b1} r(ω_j(x))`. -/
theorem cross_prob_shift_hitsBefore {s : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω)
    (hstartA : ∀ᵐ ω ∂μ, ω ∈ A → X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (hitsBefore (shiftX X s) b0 (b1 + 1) ∩ A) ≤ ∫ x in A, R (wf x) b0 b1 ∂μ := by
  classical
  have hconf : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → b0 ≤ X n ω ∧ X n ω ≤ b1 + 1 :=
    ae_confined_shift (s := s) hstep hrange hX0b
  have hreal : μ.real (hitsBefore (shiftX X s) b0 (b1 + 1) ∩ A)
      = μ.real (exitBottomShift X b0 b1 s ∩ A) := by
    show (μ (hitsBefore (shiftX X s) b0 (b1 + 1) ∩ A)).toReal
      = (μ (exitBottomShift X b0 b1 s ∩ A)).toReal
    congr 1
    refine measure_congr ?_
    filter_upwards [hconf] with ω hω
    have hiff : (shiftExit X b0 b1 s ω ≠ ⊤ ∧
        shiftX X s (shiftExit X b0 b1 s ω).untopA ω = b0)
        ↔ ω ∈ hitsBefore (shiftX X s) b0 (b1 + 1) :=
      exitBottom_iff_hitsBefore (X := shiftX X s) hb
        (fun n => hω (s + n) (Nat.le_add_right s n))
    refine propext (show (ω ∈ hitsBefore (shiftX X s) b0 (b1 + 1) ∧ ω ∈ A)
        ↔ (ω ∈ exitBottomShift X b0 b1 s ∧ ω ∈ A) from ⟨?_, ?_⟩)
    · rintro ⟨h1, h2⟩
      exact ⟨hiff.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hiff.mp h1, h2⟩
  rw [hreal]
  exact cross_prob_shift_le_R_local hb hX hw hloh hhih hrange hstep hdom hX0b hstartA hA

omit hb hX in
/-- Each finite-horizon crossing event is measurable. -/
lemma measurableSet_crossEvent {s N : ℕ} (hX : ∀ n, Measurable[ℱ n] (X n)) :
    MeasurableSet (crossEvent X b0 b1 s N) := by
  have hτ : IsStoppingTime (shiftF ℱ s) (shiftExit X b0 b1 s) := isStoppingTime_shiftExit hX s
  have h1 : MeasurableSet[(shiftF ℱ s) N] {ω | shiftExit X b0 b1 s ω ≤ (N : ℕ∞)} := hτ N
  have h2 : MeasurableSet[(shiftF ℱ s) N]
      {ω | stoppedProcess (shiftX X s) (shiftExit X b0 b1 s) N ω = b0} := by
    have hsa : StronglyAdapted (shiftF ℱ s) (shiftX X s) := fun k => (hX (s + k)).stronglyMeasurable
    exact (hsa.stoppedProcess_of_discrete hτ N).measurable (measurableSet_singleton b0)
  rw [crossEvent_eq]
  exact (shiftF ℱ s).le N _ (h1.inter h2)

omit hb hX in
/-- The full-horizon bottom-exit event is measurable. -/
lemma measurableSet_exitBottomShift {s : ℕ} (hX : ∀ n, Measurable[ℱ n] (X n)) :
    MeasurableSet (exitBottomShift X b0 b1 s) := by
  have hunion : exitBottomShift X b0 b1 s = ⋃ N, crossEvent X b0 b1 s N := by
    ext ω
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨hne, hb0⟩
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      exact ⟨n, le_of_eq hn.symm, hb0⟩
    · rintro ⟨N, hN, hb0⟩
      exact ⟨ne_top_of_le_ne_top (by exact_mod_cast WithTop.coe_ne_top) hN, hb0⟩
  rw [hunion]
  exact MeasurableSet.iUnion (fun N => measurableSet_crossEvent hX)

end Bound

end SwarmSpeedLoc
