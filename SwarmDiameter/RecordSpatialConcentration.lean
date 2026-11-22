import SwarmDiameter.RecordBoundedGroup

open Finset Filter MeasureTheory Set
open Swarming.Uniform
open SwarmLogRatio LocSum LocSumAct

namespace Swarming.Diameter

set_option autoImplicit false

theorem recordSpatialLo_le_hi (r T L : ℕ) :
    recordSpatialLo r T L ≤ recordSpatialHi r T L :=
  (Nat.sub_le _ _).trans (Nat.le_add_right _ _)

theorem recordSpatialWidth {r T L : ℕ} (hr : (T + 3) * L ≤ r) :
    recordSpatialHi r T L - recordSpatialLo r T L = (2 * T + 4) * L := by
  have h := (Nat.mul_le_mul_right L (show T + 2 ≤ T + 3 by omega)).trans hr
  have he : (2 * T + 4) * L = 2 * ((T + 2) * L) := by ring
  unfold recordSpatialHi recordSpatialLo
  rw [he]
  omega

theorem recordSpatialLo_ge {r T L : ℕ} (hr : (T + 3) * L ≤ r) : L ≤ recordSpatialLo r T L := by
  have he : (T + 3) * L = (T + 2) * L + L := by ring
  rw [he] at hr
  unfold recordSpatialLo
  omega

/-- Spatial sums needed for the bounded comparison on a record interval. -/
structure RecordSpatialBounds {N : ℕ} (p : ℝ) (m k r T L : ℕ) (U : Array N) (ε η : ℝ) : Prop where
  slope : ∀ (i : Fin N) (a b : ℕ), recordSpatialLo r T L ≤ a → a ≤ b → b ≤ recordSpatialHi r T L →
    (∑ x ∈ Finset.Ico a b, Q p k x (siteMarks p m U i)) ≤ Lb p (qOf p m) * ((b : ℝ) - a) + ε * (L : ℝ)
  product : ∀ i : Fin N,
    (∑ x ∈ Finset.Ico (recordSpatialLo r T L) (recordSpatialHi r T L),
      (Pz p x k (siteMarks p m U i)) ^ 2) ≤
        (bC p (qOf p m)) ^ k * ((2 * T + 4 : ℕ) : ℝ) * (L : ℝ) + η * (L : ℝ)

theorem record_spatial_bounds_failure_le_exp {N : ℕ} {p : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (T : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r : ℕ, (T + 3) * L ≤ r →
      (arrayMeasure N).real {U | ¬ RecordSpatialBounds p m k r T L U ε η} ≤
        2 * (N : ℝ) * Real.exp (-c * (L : ℝ)) := by
  let Ulen := 2 * T + 4
  obtain ⟨c₁, hc₁, hQ⟩ := arrayMeasure_Q_intervals_gt hp₀ hp₁ m hk Ulen hε
  obtain ⟨c₂, hc₂, hP⟩ := arrayMeasure_Pz_sq_intervals_gt hp₀ hp₁ m hk Ulen hη
  let c := min c₁ c₂
  refine ⟨c, lt_min hc₁ hc₂, ?_⟩
  filter_upwards [eventually_ge_atTop k, hQ, hP] with L hL hQL hPL
  intro r hr
  let a₀ := recordSpatialLo r T L
  let b₀ := recordSpatialHi r T L
  have ha₀ := hL.trans (recordSpatialLo_ge hr)
  let E₁ (i : Fin N) : Set (Array N) := {U | ∃ j ≤ Ulen * L, ∃ n ≤ Ulen * L,
    Lb p (qOf p m) * (n : ℝ) + ε * (L : ℝ) <
      ∑ x ∈ Finset.Ico (a₀ + j) (a₀ + j + n), Q p k x (siteMarks p m U i)}
  let E₂ (i : Fin N) : Set (Array N) := {U | ∃ j ≤ Ulen * L, ∃ n ≤ Ulen * L,
    (bC p (qOf p m)) ^ k * (n : ℝ) + η * (L : ℝ) <
      ∑ x ∈ Finset.Ico (a₀ + j) (a₀ + j + n), (Pz p x k (siteMarks p m U i)) ^ 2}
  have hwidth : b₀ - a₀ = Ulen * L := recordSpatialWidth hr
  have hsub : {U : Array N | ¬ RecordSpatialBounds p m k r T L U ε η} ⊆
      (⋃ i, E₁ i) ∪ (⋃ i, E₂ i) := by
    intro U hU
    by_contra hbad
    apply hU
    constructor
    · intro i a b ha hab hb
      by_contra! hh
      have ha₁ : a₀ + (a - a₀) = a := Nat.add_sub_of_le ha
      have hb₁ : a + (b - a) = b := Nat.add_sub_of_le hab
      have hj := (Nat.sub_le_sub_right (hab.trans hb) a₀).trans_eq hwidth
      have hn := (Nat.sub_le_sub_right hb a).trans ((Nat.sub_le_sub_left ha b₀).trans_eq hwidth)
      apply hbad
      refine Or.inl (Set.mem_iUnion.mpr ⟨i, a - a₀, hj, b - a, hn, ?_⟩)
      simpa only [ha₁, hb₁, Nat.cast_sub hab] using hh
    · intro i
      by_contra! hh
      have he : a₀ + Ulen * L = b₀ := by rw [← hwidth, Nat.add_sub_of_le (recordSpatialLo_le_hi r T L)]
      apply hbad
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, 0, Nat.zero_le _, Ulen * L, le_rfl, ?_⟩)
      simpa only [Nat.add_zero, he, Nat.cast_mul, mul_assoc] using hh
  have hrate (d : ℝ) (hd : c ≤ d) : Real.exp (-d * (L : ℝ)) ≤ Real.exp (-c * (L : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hd) (Nat.cast_nonneg _))
  have hE₁ (i : Fin N) : (arrayMeasure N).real (E₁ i) ≤ Real.exp (-c * (L : ℝ)) :=
    (hQL a₀ N ha₀ i).trans (hrate c₁ (min_le_left _ _))
  have hE₂ (i : Fin N) : (arrayMeasure N).real (E₂ i) ≤ Real.exp (-c * (L : ℝ)) :=
    (hPL a₀ N ha₀ i).trans (hrate c₂ (min_le_right _ _))
  refine (measureReal_mono hsub).trans (measureReal_union_le _ _ |>.trans ?_)
  have hu (E : Fin N → Set (Array N))
      (hE : ∀ i, (arrayMeasure N).real (E i) ≤ Real.exp (-c * (L : ℝ))) :
      (arrayMeasure N).real (⋃ i, E i) ≤ (N : ℝ) * Real.exp (-c * (L : ℝ)) :=
    (measureReal_iUnion_fintype_le _).trans (by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) fun i _ => hE i))
  linarith only [hu E₁ hE₁, hu E₂ hE₂]

end Swarming.Diameter
