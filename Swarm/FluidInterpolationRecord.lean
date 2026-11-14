/-
# Actual nearest-neighbour paths interpolated from a record window

`scaledInterp` is the construction from `FluidInterpolation`, with node values
exactly `FluidLimit.scaledPosition` and grid spacing `1 / scale`.  The raw
sample is clipped by `rawHorizon T scale = floor (T * scale)`.  On `[0,T]`
the clip is redundant, and the resulting sampled raw time is bounded by the
explicit horizon needed by `atRecordsOn_of_scaled_discrete_lag`.
-/
import Swarm.FluidLimitLight
import Swarm.FluidInterpolation
import Mathlib.Algebra.Order.Floor.Semiring

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidInterpolation

open FluidLimit

noncomputable section

/-- The actual piecewise-affine path on a shifted nearest-neighbour window. -/
def scaledInterp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (N : ℕ) (t : ℝ) : ℝ :=
  interp (fun k => scaledPosition X level start scale i k) ((scale : ℝ)⁻¹) N t

lemma scale_spacing_pos {scale : ℕ} (hscale : 0 < scale) : 0 < (scale : ℝ)⁻¹ := by
  have hR : (0 : ℝ) < scale := by exact_mod_cast hscale
  positivity

lemma scaledPosition_step_dist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (k : ℕ)
    (hscale : 0 < scale)
    (hstep : |X i ((start + k) + 1) - X i (start + k)| ≤ 1) :
    dist (scaledPosition X level start scale i (k + 1))
      (scaledPosition X level start scale i k) ≤ (scale : ℝ)⁻¹ := by
  have hscaleR : (0 : ℝ) < scale := by exact_mod_cast hscale
  have htime : start + (k + 1) = (start + k) + 1 := by omega
  rw [scaledPosition, scaledPosition, htime, Real.dist_eq, div_sub_div_same,
    abs_div, abs_of_pos hscaleR]
  have hstepR : |(X i ((start + k) + 1) : ℝ) - (X i (start + k) : ℝ)| ≤ 1 := by
    exact_mod_cast hstep
  have heq : (X i ((start + k) + 1) : ℝ) - (level : ℝ) -
      ((X i (start + k) : ℝ) - (level : ℝ)) =
      (X i ((start + k) + 1) : ℝ) - (X i (start + k) : ℝ) := by ring
  rw [heq]
  simpa only [one_div] using div_le_div_of_nonneg_right hstepR hscaleR.le

lemma continuous_scaledInterp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale) (N : ℕ) :
    Continuous (scaledInterp X level start scale i N) := by
  exact continuous_interp _ _ (scale_spacing_pos hscale) N

lemma lipschitz_scaledInterp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    (hNN : ∀ k, |X i ((start + k) + 1) - X i (start + k)| ≤ 1) (N : ℕ) :
    LipschitzWith 1 (scaledInterp X level start scale i N) := by
  apply lipschitz_interp _ (scale_spacing_pos hscale)
  intro k
  exact scaledPosition_step_dist X level start scale i k hscale (hNN k)

lemma scaledInterp_at_knot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    {N k : ℕ} (hk : k ≤ N) :
    scaledInterp X level start scale i N ((k : ℝ) / (scale : ℝ)) =
      scaledPosition X level start scale i k := by
  simpa only [scaledInterp, div_eq_mul_inv] using
    interp_at_knot (fun k => scaledPosition X level start scale i k)
      (scale_spacing_pos hscale) hk

@[simp] lemma scaledInterp_at_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale) (N : ℕ) :
    scaledInterp X level start scale i N 0 = scaledPosition X level start scale i 0 := by
  exact interp_at_zero _ (scale_spacing_pos hscale) N

lemma scaledInterp_eq_last {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    {N : ℕ} {t : ℝ} (ht : (N : ℝ) / (scale : ℝ) ≤ t) :
    scaledInterp X level start scale i N t = scaledPosition X level start scale i N := by
  exact interp_eq_right_of_le _ (scale_spacing_pos hscale) (by simpa [div_eq_mul_inv] using ht)

/-- Bounded continuous restriction of the actual path to compact fluid time. -/
def scaledBundle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    (N : ℕ) (T : ℝ) : Set.Icc (0 : ℝ) T →ᵇ ℝ :=
  bundle N (continuous_scaledInterp X level start scale i hscale N)

@[simp] lemma scaledBundle_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    (N : ℕ) (T : ℝ) (t : Set.Icc (0 : ℝ) T) :
    scaledBundle X level start scale i hscale N T t =
      scaledInterp X level start scale i N t := rfl

lemma lipschitz_scaledBundle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    (hNN : ∀ k, |X i ((start + k) + 1) - X i (start + k)| ≤ 1)
    (N : ℕ) (T : ℝ) : LipschitzWith 1 (scaledBundle X level start scale i hscale N T) := by
  exact lipschitz_bundle N _ (lipschitz_scaledInterp X level start scale i hscale hNN N)

/-- Raw integer horizon `floor (T * scale)` used by the paper. -/
def rawHorizon (T : ℝ) (scale : ℕ) : ℕ := ⌊T * (scale : ℝ)⌋₊

/-- Nearest raw sample, held fixed after the last raw knot. -/
def rawSample (scale N : ℕ) (t : ℝ) : ℕ := min ⌊(scale : ℝ) * t⌋₊ N

lemma rawSample_le (scale N : ℕ) (t : ℝ) : rawSample scale N t ≤ N := min_le_right _ _

lemma rawHorizon_time_le {T : ℝ} (hT : 0 ≤ T) {scale : ℕ} (hscale : 0 < scale) :
    (rawHorizon T scale : ℝ) / (scale : ℝ) ≤ T := by
  have hscaleR : (0 : ℝ) < scale := by exact_mod_cast hscale
  apply (div_le_iff₀ hscaleR).2
  exact Nat.floor_le (mul_nonneg hT hscaleR.le)

lemma rawSample_eq_floor {T : ℝ} {scale : ℕ} {t : ℝ} (htT : t ≤ T) :
    rawSample scale (rawHorizon T scale) t = ⌊(scale : ℝ) * t⌋₊ := by
  apply min_eq_left
  apply Nat.floor_le_floor
  have hscaleR : (0 : ℝ) ≤ scale := by exact_mod_cast (Nat.zero_le scale)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left htT hscaleR

/-- Comparison with the literal discrete sample at raw index `floor (scale*t)`.
The only exceptional case is the constant exterior extension after the last
raw knot; there the clipped sample is exactly the constant value. -/
lemma dist_scaledInterp_rawSample_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι) (hscale : 0 < scale)
    (hNN : ∀ k, |X i ((start + k) + 1) - X i (start + k)| ≤ 1)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    dist (scaledInterp X level start scale i N t)
      (scaledPosition X level start scale i (rawSample scale N t)) ≤ (scale : ℝ)⁻¹ := by
  have hscaleR : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hfloor : (⌊(scale : ℝ) * t⌋₊ : ℝ) ≤ (scale : ℝ) * t :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg scale) ht)
  by_cases hk : ⌊(scale : ℝ) * t⌋₊ < N
  · let k := ⌊(scale : ℝ) * t⌋₊
    have hkt : (k : ℝ) / (scale : ℝ) ≤ t := by
      apply (div_le_iff₀ hscaleR).2
      simpa only [k, mul_comm] using hfloor
    have hupper : t ≤ ((k + 1 : ℕ) : ℝ) / (scale : ℝ) := by
      apply le_of_lt ((lt_div_iff₀ hscaleR).2 ?_)
      have hu := Nat.lt_floor_add_one ((scale : ℝ) * t)
      simpa only [k, Nat.cast_add, Nat.cast_one, mul_comm] using hu
    have hnear : dist t ((k : ℝ) / (scale : ℝ)) ≤ (scale : ℝ)⁻¹ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hkt)]
      rw [div_eq_mul_inv] at hupper ⊢
      push_cast at hupper
      nlinarith
    rw [rawSample, min_eq_left hk.le]
    calc
      dist (scaledInterp X level start scale i N t)
          (scaledPosition X level start scale i k) =
          dist (scaledInterp X level start scale i N t)
            (scaledInterp X level start scale i N ((k : ℝ) / (scale : ℝ))) := by
        rw [scaledInterp_at_knot X level start scale i hscale hk.le]
      _ ≤ dist t ((k : ℝ) / (scale : ℝ)) := by
        simpa only [NNReal.coe_one, one_mul] using
          (lipschitz_scaledInterp X level start scale i hscale hNN N).dist_le_mul
            t ((k : ℝ) / (scale : ℝ))
      _ ≤ (scale : ℝ)⁻¹ := hnear
  · have hNk : N ≤ ⌊(scale : ℝ) * t⌋₊ := Nat.le_of_not_gt hk
    have hNt : (N : ℝ) / (scale : ℝ) ≤ t := by
      apply (div_le_iff₀ hscaleR).2
      calc
        (N : ℝ) ≤ (⌊(scale : ℝ) * t⌋₊ : ℝ) := by exact_mod_cast hNk
        _ ≤ (scale : ℝ) * t := hfloor
        _ = t * (scale : ℝ) := by ring
    rw [rawSample, min_eq_right hNk, scaledInterp_eq_last X level start scale i hscale hNt,
      dist_self]
    exact inv_nonneg.mpr hscaleR.le

/-- On the actual fluid window the comparison is against the unclipped
`floor (scale * t)` sample, while its value remains below `rawHorizon`. -/
lemma dist_scaledInterp_floor_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ℝ} (X : ι → ℕ → ℤ) (level start scale : ℕ) (i : ι)
    (hscale : 0 < scale) (hNN : ∀ k, |X i ((start + k) + 1) - X i (start + k)| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    dist (scaledInterp X level start scale i (rawHorizon T scale) t)
      (scaledPosition X level start scale i ⌊(scale : ℝ) * t⌋₊) ≤ (scale : ℝ)⁻¹ := by
  rw [← rawSample_eq_floor htT]
  exact dist_scaledInterp_rawSample_le X level start scale i hscale hNN _ ht

end
end FluidInterpolation
