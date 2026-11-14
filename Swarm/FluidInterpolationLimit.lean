/-
# Feeding the actual interpolants to fluid compactness

The finite paths are not an interface hypothesis here: `recordFamily` is the
clamped piecewise-affine construction applied to the actual record windows.
The accepted compactness entry point is then instantiated directly.  A raw
sample convergence statement is retained on `Icc 0 T`; no running-maximum
convergence or finite-L local-good estimate is supplied.
-/
import Swarm.FluidInterpolationRecord
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidInterpolation

open FluidLimit

universe u v

noncomputable section

/-- The concrete family consumed by `exists_record_rescaled_limit_subseq`. -/
def recordFamily {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n) (T : ℝ) :
    ℕ → ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ) :=
  fun n i => scaledBundle (X n) (level n) (τ n (level n)) (scale n) i (hscale n)
    (rawHorizon T (scale n)) T

lemma lipschitz_recordFamily {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n) (T : ℝ)
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1) (n : ℕ) (i : ι) :
    LipschitzWith 1 (recordFamily X τ level scale hscale T n i) := by
  apply lipschitz_scaledBundle _ _ _ _ _ (hscale n)
  intro k
  exact (hNN n i (τ n (level n) + k)).le

@[simp] lemma recordFamily_start {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n) {T : ℝ} (hT : 0 ≤ T)
    (z : Set.Icc (0 : ℝ) T) (hz : z = ⟨0, ⟨le_rfl, hT⟩⟩) (n : ℕ) (i : ι) :
    recordFamily X τ level scale hscale T n i z =
      scaledPosition (X n) (level n) (τ n (level n)) (scale n) i 0 := by
  subst z
  exact scaledInterp_at_zero (X n) (level n) (τ n (level n)) (scale n) i (hscale n) _

lemma recordFamily_rawSample_le {ι : Type v} [Fintype ι] [DecidableEq ι]
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hscale : ∀ n, 0 < scale n) {T : ℝ} (hNN : ∀ n i k,
      |X n i (k + 1) - X n i k| = 1)
    (n : ℕ) (i : ι) (t : Set.Icc (0 : ℝ) T) :
    dist (recordFamily X τ level scale hscale T n i t)
      (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
        (rawSample (scale n) (rawHorizon T (scale n)) t)) ≤ ((scale n : ℝ))⁻¹ := by
  apply dist_scaledInterp_rawSample_le _ _ _ _ _ (hscale n) _ _ t.2.1
  intro k
  exact (hNN n i (τ n (level n) + k)).le

/-- **Actual interpolated finite-L compactness package.** Every record and
scale hypothesis of the accepted entry point is preserved verbatim along the
common subsequence. In addition the literal clipped raw samples converge
uniformly to the same limit on the compact fluid-time domain. -/
theorem exists_record_interpolated_limit_subseq
    {ι : Type v} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C₀ : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (level scale : ℕ → ℕ)
    (hτ : ∀ n, RecordDefect.IsRecord (X n) (τ n))
    (hlarge : ∀ n, C₀ * scale n ≤ level n)
    (hscaleTop : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hd : ∀ n, RecordDefect.defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (z : Set.Icc (0 : ℝ) T) (hz : z = ⟨0, ⟨le_rfl, hT⟩⟩)
    (hNN : ∀ n i k, |X n i (k + 1) - X n i k| = 1) :
    ∃ (x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, LipschitzWith 1 (x i)) ∧
      (∀ i t, x i t ∈ Set.Icc (-1 - T) T) ∧
      (∀ i, TendstoUniformly (fun n => recordFamily X τ level scale hscale T (φ n) i)
        (x i) atTop) ∧
      (∀ i, x i z ∈ Set.Icc (-1) 0) ∧
      (∀ n, C₀ * scale (φ n) ≤ level (φ n)) ∧
      Tendsto (fun n => scale (φ n)) atTop atTop ∧
      (∀ n, RecordDefect.defect (X (φ n)) (τ (φ n)) (level (φ n)) ≤
        (scale (φ n) : ℤ)) ∧
      (∀ i, TendstoUniformly
        (fun n (t : Set.Icc (0 : ℝ) T) => scaledPosition (X (φ n)) (level (φ n))
          (τ (φ n) (level (φ n))) (scale (φ n)) i
          (rawSample (scale (φ n)) (rawHorizon T (scale (φ n))) t))
        (fun t => x i t) atTop) := by
  obtain ⟨x, φ, hφ, hxlip, hxbound, hx, hxstart, hlargeφ, hscaleφ, hdφ⟩ :=
    exists_record_rescaled_limit_subseq C₀ T hT X τ level scale
      (recordFamily X τ level scale hscale T) hτ hlarge hscaleTop hscale hd z hz
      (lipschitz_recordFamily X τ level scale hscale T hNN)
      (recordFamily_start X τ level scale hscale hT z hz)
  refine ⟨x, φ, hφ, hxlip, hxbound, hx, hxstart, hlargeφ, hscaleφ, hdφ, ?_⟩
  intro i
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hcast : Tendsto (fun n => (scale (φ n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscaleφ
  have hinv : Tendsto (fun n => ((scale (φ n) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hsmall : ∀ᶠ n in atTop, ((scale (φ n) : ℝ))⁻¹ < ε / 2 :=
    (tendsto_order.1 hinv).2 _ (half_pos hε)
  filter_upwards [hsmall, Metric.tendstoUniformly_iff.mp (hx i) (ε / 2) (half_pos hε)]
    with n hn hxn
  intro t
  have hsample := recordFamily_rawSample_le X τ level scale hscale hNN (φ n) i t
  have htri := dist_triangle (x i t) (recordFamily X τ level scale hscale T (φ n) i t)
    (scaledPosition (X (φ n)) (level (φ n)) (τ (φ n) (level (φ n))) (scale (φ n)) i
      (rawSample (scale (φ n)) (rawHorizon T (scale (φ n))) t))
  have hxn' := hxn t
  linarith

end
end FluidInterpolation
