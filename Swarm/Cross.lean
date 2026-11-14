/-
  **The conditional (revealed-environment) stopped crossing estimate.**

  This file takes the paper's fixed-environment stopped crossing estimate
  (`StoppedCross.cross_prob_le_hitsBefore`) and the revealed-weight one-step drift
  (`Step2.condExp_scD_step`) and assembles the *conditional on `ℱ_s`* form:
  for every `ℱ_s`-measurable set `A` on which the walker sits at `b1` at time `s`,
  the `ℱ_s`-conditional probability of crossing down to `b0` before `b1+1` is bounded
  by the revealed potential `R = ∏_{x=b0+1}^{b1} (1-ω_j(x))/ω_j(x)`.
-/
import Swarm.Imports
import Swarm.StoppedCross
import Swarm.Diag
import Swarm.Step
import Swarm.Step2
import Swarm.SubSigma

open MeasureTheory Filter
open scoped Topology BigOperators

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {wf : Ω → ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}

/-- The walker viewed from time `s`. -/
def shiftX (X : ℕ → Ω → ℕ) (s : ℕ) : ℕ → Ω → ℕ := fun k ω => X (s + k) ω

/-- The filtration viewed from time `s`. -/
def shiftF (ℱ : Filtration ℕ m0) (s : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (s + k)
  mono' := fun i j hij => ℱ.mono (by omega)
  le' := fun i => ℱ.le (s + i)

@[simp] lemma shiftF_apply {s k : ℕ} : (shiftF ℱ s) k = ℱ (s + k) := rfl
@[simp] lemma shiftX_apply {s k : ℕ} {ω : Ω} : shiftX X s k ω = X (s + k) ω := rfl

theorem adapted_shiftX (hX : ∀ n, Measurable[ℱ n] (X n)) (s : ℕ) :
    Adapted (shiftF ℱ s) (shiftX X s) := fun k => hX (s + k)

/-- The first exit time of the window `[b0, b1+1]` counted from time `s`. -/
noncomputable def shiftExit (X : ℕ → Ω → ℕ) (b0 b1 s : ℕ) : Ω → ℕ∞ :=
  hittingAfter (shiftX X s) (outside b0 b1) 0

theorem isStoppingTime_shiftExit (hX : ∀ n, Measurable[ℱ n] (X n)) (s : ℕ) :
    IsStoppingTime (shiftF ℱ s) (shiftExit X b0 b1 s) :=
  Adapted.isStoppingTime_hittingAfter (adapted_shiftX hX s) (measurableSet_outside b0 b1)

/-- `scDiag` only depends on the value of the level map at the point. -/
lemma scDiag_congr {g h : Ω → ℕ} {ω : Ω} (hh : g ω = h ω) :
    scDiag wf b0 b1 g ω = scDiag wf b0 b1 h ω := by
  simp only [scDiag, scNumDiag, hh]

section Sub

variable [IsProbabilityMeasure μ] (hb : b0 ≤ b1) (hX : ∀ n, Measurable[ℱ n] (X n))

include hb hX

/-- **The revealed-environment scale process is a submartingale** from the reveal time `s` on,
for the shifted filtration `k ↦ ℱ_{s+k}`. -/
theorem submartingale_scD_shift {s : ℕ} (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω) :
    Submartingale (fun k ω => scDiag wf b0 b1 (fun ω' => X (s + k) ω') ω) (shiftF ℱ s) μ := by
  have hwk : ∀ k, ∀ x, Measurable[ℱ (s + k)] (fun ω => wf ω x) :=
    fun k x => (hw x).mono (ℱ.mono (Nat.le_add_right s k)) le_rfl
  refine submartingale_nat (fun k => ?_) (fun k => ?_) (fun k => ?_)
  · exact (measurable_scDiag (hwk k) (hX (s + k))).stronglyMeasurable
  · refine Integrable.of_bound ((measurable_scDiag (hwk k) (hX (s + k))).mono
      (ℱ.le (s + k)) le_rfl).aestronglyMeasurable 1 ?_
    filter_upwards [hloh, hhih, hrange] with ω h1 h2 h3
    exact norm_scDiag_le_one h1 h2 hb (h3 (s + k) (Nat.le_add_right s k))
  · have h := condExp_scD_step (μ := μ) (ℱ := ℱ) (wf := wf) (X := X) (s := s) (n := s + k)
      hb hX hw (Nat.le_add_right s k) hloh hhih
      (hrange.mono (fun ω h => h (s + k) (Nat.le_add_right s k)))
      (hrange.mono (fun ω h => h (s + k + 1) (by omega)))
      (hstep (s + k) (Nat.le_add_right s k)) (hdom (s + k) (Nat.le_add_right s k))
    have harg : s + (k + 1) = s + k + 1 := by omega
    have hgoal : μ[(fun ω => scDiag wf b0 b1 (fun ω' => X (s + (k + 1)) ω') ω) | (shiftF ℱ s) k]
        = μ[(fun ω => scDiag wf b0 b1 (fun ω' => X (s + k + 1) ω') ω) | ℱ (s + k)] := by
      simp only [harg, shiftF_apply]
    rw [hgoal]
    exact h

omit hb [IsProbabilityMeasure μ] hX in
/-- **Confinement from the reveal time**: a walker that starts at or above `b0` at time `s` and
follows the nearest-neighbour/absorption structure never leaves `[b0, b1+1]`. -/
theorem ae_confined_shift {s : ℕ} (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω) :
    ∀ᵐ ω ∂μ, ∀ n, s ≤ n → b0 ≤ X n ω ∧ X n ω ≤ b1 + 1 := by
  have hstepall : ∀ᵐ ω ∂μ, ∀ k, StepAt X b0 b1 (s + k) ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun k => hstep (s + k) (Nat.le_add_right s k)
  filter_upwards [hstepall, hrange, hX0b] with ω hs hr h0
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact ⟨h0, hr s le_rfl⟩
  | succ k ih =>
      rw [show s + (k + 1) = s + k + 1 by omega]
      have hk := hs k
      have hup : X (s + k + 1) ω ≤ b1 + 1 := hr (s + k + 1) (by omega)
      rcases hk with ⟨hi1, hi2, hs1 | hs1⟩ | ⟨hle, heq⟩ | ⟨heq, heq2⟩
      · rw [hs1]; exact ⟨by omega, by omega⟩
      · rw [show X (s + k + 1) ω = X (s + k) ω - 1 by omega]
        omega
      · rw [heq]; exact ih (by omega)
      · rw [heq2, heq]; exact ⟨by omega, le_rfl⟩

end Sub

/-! ### The crossing event from time `s` -/

/-- `crossEvent X b0 b1 s N` is the event that, counted from time `s`, the walker leaves the
window `[b0, b1+1]` for the first time at the *bottom* level `b0` by time `s+N`. -/
noncomputable def crossEvent (X : ℕ → Ω → ℕ) (b0 b1 s N : ℕ) : Set Ω :=
  {ω | shiftExit X b0 b1 s ω ≤ (N : ℕ∞) ∧ X (s + (shiftExit X b0 b1 s ω).untopA) ω = b0}

lemma crossEvent_eq (s N : ℕ) :
    crossEvent X b0 b1 s N
      = {ω | shiftExit X b0 b1 s ω ≤ (N : ℕ∞)}
        ∩ {ω | stoppedProcess (shiftX X s) (shiftExit X b0 b1 s) N ω = b0} := by
  ext ω
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    show shiftX X s (min (N : ℕ∞) (shiftExit X b0 b1 s ω)).untopA ω = b0
    rw [min_eq_right h1]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 := stoppedProcess_eq_of_ge (u := shiftX X s) (τ := shiftExit X b0 b1 s) (i := N) h1
    show shiftX X s (shiftExit X b0 b1 s ω).untopA ω = b0
    rw [← h3]
    exact h2

section Bound

variable [IsProbabilityMeasure μ] (hb : b0 ≤ b1) (hX : ∀ n, Measurable[ℱ n] (X n))

include hb hX

/-- **Finite-horizon conditional crossing bound in the revealed environment.**

For every `ℱ_s`-measurable `A`, the probability (under `μ`) that the run started at the top
level `b1` at time `s` exits the window `[b0, b1+1]` at the bottom level `b0` before time
`s+N` is at most `∫_A (1 - f(b1))`, where `f` is the scale function of the *revealed* weights
`ω ↦ wf ω`.  This is the conditional form of eq. (cross): no independence of the environment
from the future is used, only `ℱ_s`-measurability of the revealed weights. -/
theorem cross_prob_shift_le_N {s N : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hstart : ∀ᵐ ω ∂μ, X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (crossEvent X b0 b1 s N ∩ A)
      ≤ ∫ x in A, (1 - scDiag wf b0 b1 (fun _ => b1) x) ∂μ := by
  classical
  have hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω := by
    filter_upwards [hstart] with ω hω
    rw [hω]; exact hb
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
    filter_upwards [hstart] with ω hω _
    rw [hF]
    refine scDiag_congr ?_
    show X (s + 0) ω = b1
    simpa using hω
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
theorem cross_prob_shift_le {s : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hstart : ∀ᵐ ω ∂μ, X s ω = b1)
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
    (fun N => cross_prob_shift_le_N hb hX hw hloh hhih hrange hstep hdom hstart hA)

include hb hX in
/-- **The paper's right-hand side**: the revealed potential `R = ∏_{x=b0+1}^{b1} r(ω_j(x))`. -/
theorem cross_prob_shift_le_R {s : ℕ} {A : Set Ω}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hstart : ∀ᵐ ω ∂μ, X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (exitBottomShift X b0 b1 s ∩ A) ≤ ∫ x in A, R (wf x) b0 b1 ∂μ := by
  classical
  refine (cross_prob_shift_le hb hX hw hloh hhih hrange hstep hdom hstart hA).trans ?_
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
    (hstart : ∀ᵐ ω ∂μ, X s ω = b1)
    (hA : MeasurableSet[ℱ s] A) :
    μ.real (hitsBefore (shiftX X s) b0 (b1 + 1) ∩ A) ≤ ∫ x in A, R (wf x) b0 b1 ∂μ := by
  classical
  have hX0b : ∀ᵐ ω ∂μ, b0 ≤ X s ω := by
    filter_upwards [hstart] with ω hω
    rw [hω]; exact hb
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
  exact cross_prob_shift_le_R hb hX hw hloh hhih hrange hstep hdom hstart hA

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

include hb hX in
/-- **The paper's conditional crossing estimate as an almost-everywhere conditional
probability bound.**  For a walker sitting at `b1` at the reveal time `s`, the `ℱ_s`-conditional
probability of crossing down to `b0` before `b1+1` is bounded by the revealed potential
`∏_{x=b0+1}^{b1} (1-ω_j(x))/ω_j(x)`:
`μ[1{T_{b0}(s) < T_{b1+1}(s)} | ℱ_s] ≤ R` almost surely. -/
theorem condExp_cross_prob_shift_le_R {s : ℕ}
    (hw : ∀ x, Measurable[ℱ s] (fun ω => wf ω x))
    (hloh : ∀ᵐ ω ∂μ, ∀ x, (1 : ℝ) / 2 ≤ wf ω x)
    (hhih : ∀ᵐ ω ∂μ, ∀ x, wf ω x < 1)
    (hrange : ∀ᵐ ω ∂μ, ∀ n, s ≤ n → X n ω ≤ b1 + 1)
    (hstep : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, StepAt X b0 b1 n ω)
    (hdom : ∀ n, s ≤ n → ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 →
      wf ω (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
    (hstart : ∀ᵐ ω ∂μ, X s ω = b1) :
    μ[(exitBottomShift X b0 b1 s).indicator (1 : Ω → ℝ) | ℱ s]
      ≤ᵐ[μ] fun ω => R (wf ω) b0 b1 := by
  classical
  have hEmeas : MeasurableSet (exitBottomShift X b0 b1 s) := measurableSet_exitBottomShift hX
  have hRmeas : Measurable[ℱ s] (fun ω => R (wf ω) b0 b1) := measurable_R_diag hw b0 b1
  have hRmeas0 : Measurable (fun ω => R (wf ω) b0 b1) := hRmeas.mono (ℱ.le s) le_rfl
  have hRint : Integrable (fun ω => R (wf ω) b0 b1) μ := by
    refine Integrable.of_bound hRmeas0.aestronglyMeasurable 1 ?_
    filter_upwards [hloh, hhih] with ω h1 h2
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [R_nonneg h1 h2 (b0 := b0) (y := b1)],
      R_le_one h1 h2 (b0 := b0) (y := b1)⟩
  have hindint : Integrable ((exitBottomShift X b0 b1 s).indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hEmeas
  refine condExp_le_of_forall_setIntegral_le (μ := μ) (m := ℱ s) (ℱ.le s) hindint hRint
    hRmeas ?_
  intro A hA
  have hEA : MeasurableSet (exitBottomShift X b0 b1 s ∩ A) :=
    hEmeas.inter ((ℱ.le s) A hA)
  have hind_eq : ∫ x in A, (exitBottomShift X b0 b1 s).indicator (1 : Ω → ℝ) x ∂μ
      = ∫ x in A, (exitBottomShift X b0 b1 s ∩ A).indicator (1 : Ω → ℝ) x ∂μ := by
    refine setIntegral_congr_ae ((ℱ.le s) A hA) ?_
    filter_upwards with ω hω
    by_cases hE : ω ∈ exitBottomShift X b0 b1 s
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem (Set.mem_inter hE hω)]
    · rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem (fun hc => hE hc.1)]
  have hleft : ∫ x in A, (exitBottomShift X b0 b1 s ∩ A).indicator (1 : Ω → ℝ) x ∂μ
      = μ.real (exitBottomShift X b0 b1 s ∩ A) := by
    have h := integral_indicator_one (μ := μ.restrict A)
      (s := exitBottomShift X b0 b1 s ∩ A) hEA
    have h2 : (μ.restrict A).real (exitBottomShift X b0 b1 s ∩ A)
        = μ.real (exitBottomShift X b0 b1 s ∩ A) := by
      show ((μ.restrict A) (exitBottomShift X b0 b1 s ∩ A)).toReal
        = (μ (exitBottomShift X b0 b1 s ∩ A)).toReal
      rw [Measure.restrict_apply hEA, Set.inter_assoc, Set.inter_self]
    rw [h2] at h
    exact h
  rw [hind_eq, hleft]
  exact cross_prob_shift_le_R hb hX hw hloh hhih hrange hstep hdom hstart hA

end Bound

end SwarmSpeed
