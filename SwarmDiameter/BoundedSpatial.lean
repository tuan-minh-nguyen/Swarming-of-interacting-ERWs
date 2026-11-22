import SwarmDiameter.MarkBlockConcentration
import SwarmDiameter.BoundedSlopeWindow
import Swarm.R1ProductMoments

open Finset Filter MeasureTheory Set
open SwarmMarks SwarmLogRatio LocSum LocSumAct
open Swarming.Uniform
open scoped NNReal Topology

namespace Swarming.Diameter

set_option autoImplicit false

private theorem exists_markBlock (k : ℕ) (v : Fin k → Bool) :
    ∃ ω : ℕ → Bool, (fun u : Fin k => ω (k - u.1)) = v := by
  refine ⟨fun n => extFin k v (k - n), ?_⟩
  funext u
  change extFin k v (k - (k - u.1)) = v u
  rw [show k - (k - u.1) = u.1 by have := u.isLt; omega, extFin_eq u.isLt]

private noncomputable def ratioProductSq (p : ℝ) {k : ℕ} (v : Fin k → Bool) : ℝ :=
  (∏ u : Fin k, rat p (extFin k v) u.1) ^ 2

private theorem markBlockValue_ratioProductSq (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    markBlockValue (ratioProductSq p (k := k)) x ω = (Pz p x k ω) ^ 2 := by
  unfold markBlockValue ratioProductSq Pz
  congr 1
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  simp only [dif_pos hu', rat, extFin_eq hu']

private theorem measureReal_markBlock_intervals_actual {p : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m : ℕ)
    {k : ℕ} (hk : 1 ≤ k) {B : ℝ≥0} (hB : 0 < B) (f : (Fin k → Bool) → ℝ)
    (hf : ∀ v, f v ∈ Set.Icc 0 (B : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ x : ℕ, k ≤ x →
      ∫ ω, markBlockValue f x ω ∂markMeasure (boolMeasure (qOf p m)) ≤ C)
    (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ (a N : ℕ), k ≤ a → ∀ i : Fin N,
      (arrayMeasure N).real {U | ∃ j ≤ T * L, ∃ n ≤ T * L,
        C * (n : ℝ) + ε * (L : ℝ) <
          ∑ x ∈ Finset.Ico (a + j) (a + j + n), markBlockValue f x (siteMarks p m U i)}
        ≤ Real.exp (-c * (L : ℝ)) := by
  have hp : 0 < p := by linarith
  have hq₀ : 0 ≤ qOf p m := by unfold qOf; positivity
  have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  obtain ⟨c, hc, h⟩ := measureReal_markBlock_intervals_gt hq₀ hq₁ hk hB f hf hC hmean T hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with L hL
  intro a N ha i
  let E : Set (ℕ → Bool) := {ω | ∃ j ≤ T * L, ∃ n ≤ T * L,
    C * (n : ℝ) + ε * (L : ℝ) <
      ∑ x ∈ Finset.Ico (a + j) (a + j + n), markBlockValue f x ω}
  have hmE : MeasurableSet E := by
    have hconst (R : Prop) : MeasurableSet ({ω | R} : Set (ℕ → Bool)) := by
      by_cases h : R <;> simp [h]
    dsimp only [E]
    simp only [Set.ofPred_exists, Set.ofPred_and]
    refine MeasurableSet.iUnion fun j => (hconst _).inter
      (MeasurableSet.iUnion fun n => (hconst _).inter ?_)
    exact measurableSet_lt measurable_const
      (Finset.measurable_sum _ (fun x _ => measurable_markBlockValue f x))
  have hpres := measurePreserving_siteMarks hp hp₁ m i
  change (arrayMeasure N).real ((fun U => siteMarks p m U i) ⁻¹' E) ≤ _
  rw [Measure.real_def, ← Measure.map_apply hpres.measurable hmE, hpres.map_eq]
  exact hL a ha

/-- Exponential spatial sum estimate for the truncated comparison function
with boundary value one. Its mean bound is independent of the number of sites
used in the truncation. -/
theorem arrayMeasure_Q_intervals_gt {p : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ (a N : ℕ), k ≤ a → ∀ i : Fin N,
      (arrayMeasure N).real {U | ∃ j ≤ T * L, ∃ n ≤ T * L,
        Lb p (qOf p m) * (n : ℝ) + ε * (L : ℝ) <
          ∑ x ∈ Finset.Ico (a + j) (a + j + n), Q p k x (siteMarks p m U i)}
        ≤ Real.exp (-c * (L : ℝ)) := by
  have hq₀ : 0 ≤ qOf p m := by unfold qOf; positivity
  have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hq : 0 < qOf p m := pow_pos (by linarith) _
  have he (x : ℕ) (ω : ℕ → Bool) : markBlockValue (Qrel p k) x ω = Q p k x ω :=
    (Q_eq_Qrel p k x ω).symm
  have hf (v : Fin k → Bool) : Qrel p k v ∈ Set.Icc 0 (((2 * (k : ℝ≥0) + 1) : ℝ≥0) : ℝ) := by
    obtain ⟨ω, hω⟩ := exists_markBlock k v
    rw [← hω]
    change markBlockValue (Qrel p k) k ω ∈ Set.Icc 0 _
    rw [he]
    have hi := Q_le hp₀ hp₁ k k ω
    exact ⟨Q_nonneg hp₀ hp₁ k k hk ω, by push_cast; linarith only [hi]⟩
  simpa only [he] using
    (measureReal_markBlock_intervals_actual hp₀ hp₁ m hk (by positivity) (Qrel p k) hf
      (zero_le_one.trans (one_le_Lb hp₀ hp₁ hq hq₁))
      (fun x hx => by simpa only [he] using integral_Q_le hq₀ hq₁ hp₀ hp₁ hq k x hx) T hε)

/-- Exponential spatial sum estimate for the squared product of the last
`k` ratios. Its mean is the `k`-th power of the single-site second moment. -/
theorem arrayMeasure_Pz_sq_intervals_gt {p : ℝ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (m : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (T : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ (a N : ℕ), k ≤ a → ∀ i : Fin N,
      (arrayMeasure N).real {U | ∃ j ≤ T * L, ∃ n ≤ T * L,
        (bC p (qOf p m)) ^ k * (n : ℝ) + ε * (L : ℝ) <
          ∑ x ∈ Finset.Ico (a + j) (a + j + n), (Pz p x k (siteMarks p m U i)) ^ 2}
        ≤ Real.exp (-c * (L : ℝ)) := by
  have hq₀ : 0 ≤ qOf p m := by unfold qOf; positivity
  have hq₁ : qOf p m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hf (v : Fin k → Bool) : ratioProductSq p v ∈ Set.Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) := by
    obtain ⟨ω, hω⟩ := exists_markBlock k v
    rw [← hω]
    change markBlockValue (ratioProductSq p (k := k)) k ω ∈ Set.Icc 0 _
    rw [markBlockValue_ratioProductSq]
    exact ⟨sq_nonneg _, pow_le_one₀ (Pz_nonneg hp₀ hp₁ k k ω) (Pz_le_one hp₀ hp₁ k k ω)⟩
  simpa only [markBlockValue_ratioProductSq] using
    (measureReal_markBlock_intervals_actual hp₀ hp₁ m hk (by norm_num) (ratioProductSq p (k := k)) hf
      (pow_nonneg (bC_nonneg hp₀ hp₁ hq₀ hq₁) _)
      (fun x hx => by simp only [markBlockValue_ratioProductSq, LocSumR1.integral_Pz_sq hq₀ hq₁ hp₀ hp₁ x k hx,
        le_refl]) T hε)

end Swarming.Diameter
