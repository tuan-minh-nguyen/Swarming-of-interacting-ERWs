import Swarm.ClockLocMove
import Swarm.RecordClockLocal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open Finset Filter MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmRecordMeas.Actual
open scoped Topology

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ} [Nonempty (Fin N)]

/-- A sum of the walkers' compensated steps with predictable coefficients. -/
noncomputable def weightedJump (p : ℝ) (m : ℕ) (f : ℕ → Fin N → Array N → ℝ)
    (n : ℕ) (U : Array N) : ℝ :=
  ∑ i, f n i U * ExcOcc.martIncr p m n i U

/-- Exponential concentration of the weighted sum on every subinterval
of a record block. The rate is uniform over the predictable coefficients
with the prescribed absolute bound. -/
theorem record_weighted_jump_failure_le_exp
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m T : ℕ) (hT : 1 ≤ T)
    {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ (r : ℕ) (f : ℕ → Fin N → Array N → ℝ),
      (∀ n i, Measurable[Swarming.Enl.enlFilt p m n] (f n i)) →
      (∀ n i U, |f n i U| ≤ B) →
      (arrayMeasure N).real (RecClockLG.recordCarrier (N := N) p m r L ∩ {U |
        ∃ s t : ℕ, recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + T * L ∧
          ε * (L : ℝ) ≤ |∑ u ∈ Finset.Ico s t, weightedJump p m f u U|})
        ≤ Real.exp (-c * (L : ℝ)) := by
  let P := arrayMeasure N
  let F := Swarming.Enl.enlFilt (N := N) p m
  let A := 2 * (N : ℝ) * B
  have hN : (0 : ℝ) < N := by
    simpa only [Fintype.card_fin] using (show (0 : ℝ) < Fintype.card (Fin N) by
      exact_mod_cast Fintype.card_pos (α := Fin N))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let d := ε ^ 2 / (4 * (T : ℝ) * A ^ 2)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpoly := LocSumR1.eventually_poly_mul_exp_le
    (C := 2 * ((T : ℝ) + 1) ^ 2) (by positivity) hd 2
  have htop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), htop.eventually hpoly] with L hL hLp
  intro r f hf hm
  let Z := weightedJump p m f
  let Q (n : ℕ) (U : Array N) := ∑ u ∈ Finset.range n, Z u U
  have hterm (n : ℕ) (i : Fin N) :
      Measurable[F (n + 1)] (fun U => f n i U * ExcOcc.martIncr p m n i U) :=
    ((hf n i).mono (F.mono (Nat.le_succ n)) le_rfl).mul
      (ExcOcc.stronglyMeasurable_martIncr p m n i).measurable
  have habs (n : ℕ) (i : Fin N) (U : Array N) :
      |f n i U * ExcOcc.martIncr p m n i U| ≤ B * 2 := by
    rw [abs_mul]
    exact mul_le_mul (hm n i U) (ExcOcc.martIncr_abs_le hp₀ hp₁ m n i U) (abs_nonneg _) hB.le
  have hIterm (n : ℕ) (i : Fin N) :
      Integrable (fun U => f n i U * ExcOcc.martIncr p m n i U) P :=
    Integrable.of_bound ((hterm n i).mono (F.le _) le_rfl).aestronglyMeasurable (B * 2)
      (Filter.Eventually.of_forall (fun U => by simpa only [Real.norm_eq_abs] using habs n i U))
  have hM (n : ℕ) : Measurable[F (n + 1)] (Z n) :=
    Finset.measurable_sum _ (fun i _ => hterm n i)
  have hI (n : ℕ) : Integrable (Z n) P :=
    integrable_finsetSum _ (fun i _ => hIterm n i)
  have hzero (n : ℕ) : P[Z n | F n] =ᵐ[P] 0 := by
    have hh (i : Fin N) : P[(fun U => f n i U * ExcOcc.martIncr p m n i U) | F n] =ᵐ[P] 0 := by
      have hi : Integrable (ExcOcc.martIncr p m n i) P :=
        Integrable.of_bound (((ExcOcc.stronglyMeasurable_martIncr p m n i).measurable).mono
          (F.le _) le_rfl).aestronglyMeasurable 2
          (Filter.Eventually.of_forall (fun U => by
            simpa only [Real.norm_eq_abs] using ExcOcc.martIncr_abs_le hp₀ hp₁ m n i U))
      have he := condExp_mul_of_stronglyMeasurable_left (hf n i).stronglyMeasurable
        (hIterm n i) hi
      filter_upwards [he, ExcOcc.condExp_martIncr hp₀ hp₁ m n i] with U hU hV
      change P[f n i * ExcOcc.martIncr p m n i | Swarming.Enl.enlFilt p m n] U = 0
      rw [hU, Pi.mul_apply, hV, Pi.zero_apply, mul_zero]
    have he := condExp_finsetSum (m := F n) (μ := P) (s := (Finset.univ : Finset (Fin N)))
      (fun i _ => hIterm n i)
    rw [show Z n = ∑ i, (fun U => f n i U * ExcOcc.martIncr p m n i U) by
      ext U
      simp only [Z, weightedJump, Finset.sum_apply]]
    refine he.trans ?_
    filter_upwards [ae_all_iff.2 hh] with U hU
    simp only [Finset.sum_apply, hU, Pi.zero_apply, Finset.sum_const_zero]
  have hQm (n : ℕ) : StronglyMeasurable[F n] (Q n) :=
    (Finset.measurable_sum _ fun t ht => (hM t).mono
      (F.mono (Nat.lt_iff_add_one_le.mp (Finset.mem_range.mp ht))) le_rfl).stronglyMeasurable
  have hQi (n : ℕ) : Integrable (Q n) P := integrable_finsetSum _ (fun t _ => hI t)
  have hincr (n : ℕ) : StoppedWindow.increments Q n = Z n := by
    ext U
    simp [StoppedWindow.increments_apply, Q, Finset.sum_range_succ]
  have hbound (n : ℕ) (U : Array N) : |Q (n + 1) U - Q n U| ≤ A := by
    change |StoppedWindow.increments Q n U| ≤ A
    rw [hincr]
    calc
      _ ≤ ∑ i : Fin N, |f n i U * ExcOcc.martIncr p m n i U| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B * 2 := Finset.sum_le_sum fun i _ => habs n i U
      _ = _ := by simp [A, mul_comm, mul_left_comm]
  have hL₀ : (0 : ℝ) < L := by exact_mod_cast hL
  have hstp := StoppedWindow.measureReal_band_stoppedWindow_le
    (μ := P) (ℱ := F) (Q := Q) (σ := fun U => recTimeA p m U r)
    (B := fun a => RecClockLG.recordBand (N := N) p m r L a)
    (G := RecClockLG.recordCarrier (N := N) p m r L)
    hQm hQi (fun n => by rw [hincr]; exact hzero n) hA hbound
    (fun a => (Swarming.Enl.posFilt_le_enlFilt p m a) _ (RecClockLG.measurableSet_recordBand p m r L a))
    (fun a b hab => RecClockLG.disjoint_recordBand hab)
    (RecClockLG.subset_iUnion_recordBand p m r L)
    (fun a => RecClockLG.carrier_inter_band_subset_clock_eq p m r L a)
    (Nat.mul_le_mul hT hL) (mul_pos hε hL₀)
  refine (measureReal_mono ?_).trans (hstp.trans ?_)
  · rintro U ⟨hU, s, t, hs, hst, ht, hb⟩
    refine ⟨hU, ClockLocMove.mem_stoppedWindow_of_pair (Q := Q) hs hst ht ?_⟩
    simpa only [Q, Finset.sum_Ico_eq_sub _ hst] using hb
  · have he : (ε * (L : ℝ)) ^ 2 / (4 * ((T * L : ℕ) : ℝ) * A ^ 2) = d * (L : ℝ) := by
      push_cast
      dsimp only [d]
      field_simp
    have hlen : ((T * L : ℕ) : ℝ) + 1 ≤ ((T : ℝ) + 1) * L := by
      push_cast
      have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
      linarith
    calc
      _ ≤ 2 * (((T : ℝ) + 1) * L) ^ 2 * Real.exp (-d * (L : ℝ)) := by
        rw [neg_div, he, neg_mul]
        gcongr
      _ = 2 * ((T : ℝ) + 1) ^ 2 * (L : ℝ) ^ 2 * Real.exp (-d * (L : ℝ)) := by ring
      _ ≤ _ := hLp

end Swarming.Diameter
