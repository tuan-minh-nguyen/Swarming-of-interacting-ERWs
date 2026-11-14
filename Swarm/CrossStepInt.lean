/-
  **Correction of the domination hypothesis of `CrossStep.lean`.**

  `CrossStep.condExp_sc_step` / `submartingale_sc` assume

    `hdom : ∀ n, ∀ᵐ ω, w (X n ω) ≤ P(X_{n+1} = X_n + 1 | ℱ_n)`

  *without* restricting to the interior of the window.  At the absorbing boundary this is
  incompatible with `1/2 ≤ w`: if `X_n = b0` (or `X_n = b1+1`) then the structural hypothesis
  forces `X_{n+1} = X_n`, so `stepRight X n = 0` and the conditional expectation is `0`, while
  `w (X n) ≥ 1/2 > 0`.  Hence the unconditional hypothesis already forces
  `P(X_n ∈ {b0, b1+1}) = 0` for every `n`, i.e. it can only hold for a walker that never reaches
  the boundary — and then the exit probability is `0` and the crossing estimate is vacuous.

  The paper's eq. (dominate) is stated on `{b0 < X_t < b1+1}` only, and the proof of the drift
  identity uses it only there (on the boundary the correction term carries the factor
  `inside X b0 b1 n`, which vanishes).  This file restates the two results with the hypothesis
  restricted to the interior; nothing else changes.
-/
import Swarm.Imports
import Swarm.CrossStep

open MeasureTheory Filter
open scoped Topology

namespace SwarmSpeed

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable [IsProbabilityMeasure μ] {w : ℕ → ℝ} {b0 b1 : ℕ} {X : ℕ → Ω → ℕ}

variable (hlo : ∀ x, 1 / 2 ≤ w x) (hhi : ∀ x, w x < 1) (hb : b0 ≤ b1)
  (hX : ∀ n, Measurable[ℱ n] (X n))
  (hrange : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b1 + 1)

include hlo hhi hb hX hrange


/-- **The one-step submartingale drift for the scale function** (the mechanism of both
eq. (cross) and the occupation bound): under the domination hypothesis (eq. (dominate)),
`f (X_n) ≤ E[f (X_{n+1}) | ℱ_n]`. -/
theorem condExp_sc_step_int
    (hstep : ∀ n, ∀ᵐ ω ∂μ,
      (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 → w (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω)
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
        mul_le_mul_of_nonneg_right (hd hi1 hi2) hDnn
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
theorem submartingale_sc_int
    (hstep : ∀ n, ∀ᵐ ω ∂μ,
      (b0 < X n ω ∧ X n ω ≤ b1 ∧ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω + 1 = X n ω))
      ∨ (X n ω ≤ b0 ∧ X (n + 1) ω = X n ω) ∨ (X n ω = b1 + 1 ∧ X (n + 1) ω = X n ω))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, b0 < X n ω → X n ω ≤ b1 → w (X n ω) ≤ (μ[stepRight X n | ℱ n]) ω) :
    Submartingale (fun n ω => sc w b0 b1 (X n ω)) ℱ μ :=
  submartingale_nat (fun n => (measurable_sc_comp hlo hhi hb hX n).stronglyMeasurable)
    (fun n => integrable_sc_comp hlo hhi hb hX (hrange n))
    (fun n => condExp_sc_step_int hlo hhi hb hX hrange hstep hdom n)


end SwarmSpeed
