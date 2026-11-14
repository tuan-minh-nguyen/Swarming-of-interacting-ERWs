/-
Weighted deterministic-start cells for bounded martingale differences.

The proof conditions the *measure* on a cell which is measurable for the current
filtration. It does not assert a restart law or independence of the future.
The only external interfaces are the campaign's `Azuma` and `ShiftedOsc`, and
Mathlib's `condExp_restrict_ae_eq_restrict` / conditional probability API.
-/
import Swarm.Azuma
import Swarm.ShiftedOsc

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators ENNReal

namespace ShiftedAdvance

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditioning preserves a vanishing conditional mean when the conditioning
set is measurable for the conditioning σ-algebra. This is a change of measure,
not a fresh-process or independence assertion. -/
theorem condExp_eq_zero_cond_of_measurableSet
    [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0) {A : Set Ω}
    (hA : MeasurableSet[m] A) {f : Ω → ℝ}
    (hf : Integrable f μ) (hf0 : μ[f | m] =ᵐ[μ] 0) (hA0 : μ A ≠ 0) :
    μ[|A][f | m] =ᵐ[μ[|A]] 0 := by
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hA0
  have hfρ : Integrable f (μ.restrict A) := hf.restrict
  have hfν : Integrable f μ[|A] := by
    change Integrable f ((μ A)⁻¹ • μ.restrict A)
    exact hfρ.smul_measure (ENNReal.inv_ne_top.2 hA0)
  have hρ : (μ.restrict A)[f | m] =ᵐ[μ.restrict A] 0 :=
    (condExp_restrict_ae_eq_restrict hm hA hf).trans (ae_restrict_of_ae hf0)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ[|A]) (m := m)
    (f := f) (g := fun _ => 0) hm hfν ?_ ?_ ?_).symm
  · intro s hs hμs
    exact integrable_zero _ _ _
  · intro s hs hμs
    have hzρ : ∫ x in s, f x ∂(μ.restrict A) = 0 := by
      calc
        ∫ x in s, f x ∂(μ.restrict A) =
            ∫ x in s, (μ.restrict A)[f | m] x ∂(μ.restrict A) :=
          (setIntegral_condExp hm hfρ hs).symm
        _ = ∫ _x in s, (0 : ℝ) ∂(μ.restrict A) :=
          integral_congr_ae (ae_restrict_of_ae hρ)
        _ = 0 := by simp
    simp only [integral_zero]
    change (0 : ℝ) = ∫ x in s, f x ∂((μ A)⁻¹ • μ.restrict A)
    rw [Measure.restrict_smul, integral_smul_measure, hzρ, smul_zero]
  · exact stronglyMeasurable_zero.aestronglyMeasurable

/-- Exact real-mass formula for normalized restriction. No measurability of the
second set is needed because the conditioning set is measurable. -/
theorem measureReal_cond_apply {A S : Set Ω} (hA : MeasurableSet A) :
    (μ[|A]).real S = (μ.real A)⁻¹ * μ.real (A ∩ S) := by
  rw [Measure.real_def, cond_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rfl

/-- Shift a discrete filtration by a deterministic start. -/
def cellShiftFilt (ℱ : Filtration ℕ m0) (s : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (s + k)
  mono' _ _ hab := ℱ.mono (Nat.add_le_add_left hab s)
  le' k := ℱ.le (s + k)

/-- Partial sums telescope over a deterministic shift. -/
theorem psum_shift_eq_sub {ξ : ℕ → Ω → ℝ} (s n : ℕ) (ω : Ω) :
    LocMart.psum (fun k => ξ (s + k)) n ω =
      LocMart.psum ξ (s + n) ω - LocMart.psum ξ s ω := by
  induction n with
  | zero => simp [LocMart.psum_zero]
  | succ n ih =>
      have h : s + (n + 1) = (s + n) + 1 := by omega
      rw [LocMart.psum_succ, ih, h, LocMart.psum_succ]
      ring

/-- Consecutive differences have the expected partial sum, with no telescoping
hypothesis left implicit. -/
theorem psum_succ_sub (Q : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) n ω = Q n ω - Q 0 ω := by
  induction n with
  | zero => simp [LocMart.psum_zero]
  | succ n ih => rw [LocMart.psum_succ, ih]; ring

theorem inter_self_inter (A B : Set Ω) : A ∩ (A ∩ B) = A ∩ B := by
  ext ω
  simp only [Set.mem_inter_iff]
  aesop

/-- Weighted predictable-truncation bound on a deterministic-start window.
The right side is the cell mass times the shifted maximal Azuma profile, plus
only the part of the predictable carrier complement lying in the same cell. -/
theorem measureReal_cell_max_abs_shift_le_of_ptrunc
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {s : ℕ} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ (s + k)] (G k))
    {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)] (ξ (s + k)))
    (hξi : ∀ k, Integrable (ξ (s + k)) μ)
    (hξ0 : ∀ k, μ[ξ (s + k) | ℱ (s + k)] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k ω, ω ∈ G k → |ξ (s + k) ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (A ∩ {ω | ∃ k ≤ n,
        ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}) ≤
      μ.real A * (2 * ((n : ℝ) + 1) *
        Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      μ.real (A ∩ {ω | ∃ k < n, ω ∉ G k}) := by
  let E : Set Ω := {ω | ∃ k ≤ n,
    ε ≤ |LocMart.psum ξ (s + k) ω - LocMart.psum ξ s ω|}
  let R : Set Ω := {ω | ∃ k < n, ω ∉ G k}
  by_cases hA0 : μ A = 0
  · have hz : μ.real (A ∩ E) = 0 := by
      rw [Measure.real_def, measure_mono_null Set.inter_subset_left hA0, ENNReal.toReal_zero]
    have hAz : μ.real A = 0 := (measureReal_eq_zero_iff (measure_ne_top μ A)).2 hA0
    change μ.real (A ∩ E) ≤ _
    rw [hz, hAz, zero_mul, zero_add]
    exact measureReal_nonneg
  · let ν : Measure Ω := μ[|A]
    letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hA0
    let F : Filtration ℕ m0 := cellShiftFilt ℱ s
    let ζ : ℕ → Ω → ℝ := fun k => ξ (s + k)
    let H : ℕ → Set Ω := fun k => A ∩ G k
    let η : ℕ → Ω → ℝ := fun k => (H k).indicator (ζ k)
    have hA0m : MeasurableSet A := MeasurableSpace.le_def.1 (ℱ.le s) A hA
    have hHa : ∀ k, MeasurableSet[ℱ (s + k)] (H k) := by
      intro k
      have hAk : MeasurableSet[ℱ (s + k)] A :=
        MeasurableSpace.le_def.1 (ℱ.mono (show s ≤ s + k by omega)) A hA
      exact hAk.inter (hG k)
    have hHm : ∀ k, StronglyMeasurable[F (k + 1)] (η k) := by
      intro k
      have hs : MeasurableSet[F (k + 1)] (H k) :=
        MeasurableSpace.le_def.1 (F.mono (Nat.le_succ k)) (H k) (hHa k)
      exact (hξm k).indicator hs
    have hζi : ∀ k, Integrable (ζ k) ν := by
      intro k
      change Integrable (ξ (s + k)) ((μ A)⁻¹ • μ.restrict A)
      exact (hξi k).restrict.smul_measure (ENNReal.inv_ne_top.2 hA0)
    have hζ0 : ∀ k, ν[ζ k | F k] =ᵐ[ν] 0 := by
      intro k
      have hAk : MeasurableSet[ℱ (s + k)] A :=
        MeasurableSpace.le_def.1 (ℱ.mono (show s ≤ s + k by omega)) A hA
      exact condExp_eq_zero_cond_of_measurableSet (ℱ.le (s + k))
        hAk (hξi k) (hξ0 k) hA0
    have hηi : ∀ k, Integrable (η k) ν := by
      intro k
      have hs : MeasurableSet (H k) :=
        MeasurableSpace.le_def.1 (F.le k) (H k) (hHa k)
      exact (hζi k).indicator hs
    have hη0 : ∀ k, ν[η k | F k] =ᵐ[ν] 0 := by
      intro k
      have hi := MeasureTheory.condExp_indicator (μ := ν) (m := F k)
        (f := ζ k) (s := H k) (hζi k) (hHa k)
      refine hi.trans ?_
      filter_upwards [hζ0 k] with ω hω
      by_cases hmem : ω ∈ H k
      · rw [Set.indicator_of_mem hmem]
        exact hω
      · simp [Set.indicator_of_notMem hmem]
    have hηbdd : ∀ k ω, |η k ω| ≤ C := by
      intro k ω
      change |(H k).indicator (ζ k) ω| ≤ C
      by_cases hmem : ω ∈ H k
      · rw [Set.indicator_of_mem hmem]
        exact hbdd k ω hmem.2
      · rw [Set.indicator_of_notMem hmem, abs_zero]
        exact hC.le
    have hAz := LocMart.measure_max_abs_psum_ge_le (μ := ν) (ℱ := F) (ξ := η)
      hHm hC hηbdd hη0 hn hε
    have hsub : A ∩ E ⊆
        {ω | ∃ k ≤ n, ε ≤ |LocMart.psum η k ω|} ∪ (A ∩ R) := by
      intro ω hω
      rcases hω with ⟨hωA, k, hk, hdev⟩
      by_cases hgood : ∀ j < k, ω ∈ G j
      · left
        refine ⟨k, hk, ?_⟩
        have heq : LocMart.psum η k ω = LocMart.psum ζ k ω := by
          simp only [LocMart.psum, η]
          refine Finset.sum_congr rfl fun j hj => ?_
          exact Set.indicator_of_mem
            (show ω ∈ H j from ⟨hωA, hgood j (Finset.mem_range.1 hj)⟩) (ζ j)
        rw [heq]
        change ε ≤ |LocMart.psum (fun j => ξ (s + j)) k ω|
        rwa [psum_shift_eq_sub]
      · right
        push Not at hgood
        obtain ⟨j, hj, hjG⟩ := hgood
        exact ⟨hωA, j, lt_of_lt_of_le hj hk, hjG⟩
    have hcond : ν.real (A ∩ E) ≤
        2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
          ν.real (A ∩ R) := by
      calc
        ν.real (A ∩ E) ≤ ν.real
            ({ω | ∃ k ≤ n, ε ≤ |LocMart.psum η k ω|} ∪ (A ∩ R)) :=
          measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ ν.real {ω | ∃ k ≤ n, ε ≤ |LocMart.psum η k ω|} + ν.real (A ∩ R) :=
          measureReal_union_le _ _
        _ ≤ _ := add_le_add hAz le_rfl
    change μ.real (A ∩ E) ≤ _
    change ν.real (A ∩ E) ≤ _ at hcond
    rw [measureReal_cond_apply hA0m, measureReal_cond_apply hA0m] at hcond
    rw [inter_self_inter, inter_self_inter] at hcond
    have hAreal : μ.real A ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top μ A)).2 hA0
    have hApos : 0 < μ.real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hAreal)
    have hmul := mul_le_mul_of_nonneg_left hcond hApos.le
    calc
      μ.real (A ∩ E) = μ.real A * ((μ.real A)⁻¹ * μ.real (A ∩ E)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hAreal, one_mul]
      _ ≤ μ.real A * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2)) +
            (μ.real A)⁻¹ * μ.real (A ∩ R)) := hmul
      _ = μ.real A * (2 * ((n : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) + μ.real (A ∩ R) := by
        have hr : μ.real A * ((μ.real A)⁻¹ * μ.real (A ∩ R)) = μ.real (A ∩ R) := by
          rw [← mul_assoc, mul_inv_cancel₀ hAreal, one_mul]
        rw [mul_add, hr]


/-- The literal `OscStartCell` weighted by an `F_s`-measurable event. The mass
multiplying the exponential is the full deterministic-start cell, and the
carrier complement remains intersected with exactly that cell. -/
theorem measureReal_inter_oscStartCell_le_of_ptrunc
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {Q : ℕ → Ω → ℝ} {τ : Ω → ℕ} {s : ℕ} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A)
    (hτ : MeasurableSet[ℱ s] {ω | τ ω = s})
    {G : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ (s + k)] (G k))
    (hQm : ∀ k, StronglyMeasurable[ℱ (s + k + 1)]
      (fun ω => Q (s + k + 1) ω - Q (s + k) ω))
    (hQi : ∀ k, Integrable (fun ω => Q (s + k + 1) ω - Q (s + k) ω) μ)
    (hQ0 : ∀ k, μ[fun ω => Q (s + k + 1) ω - Q (s + k) ω |
      ℱ (s + k)] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 < C)
    (hbdd : ∀ k ω, ω ∈ G k → |Q (s + k + 1) ω - Q (s + k) ω| ≤ C)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real (A ∩ OscStartCell Q τ n ε s) ≤
      μ.real (A ∩ {ω | τ ω = s}) * (2 * ((n : ℝ) + 1) *
        Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * C ^ 2))) +
      μ.real ((A ∩ {ω | τ ω = s}) ∩ {ω | ∃ k < n, ω ∉ G k}) := by
  let B : Set Ω := A ∩ {ω | τ ω = s}
  have hB : MeasurableSet[ℱ s] B := hA.inter hτ
  have h := measureReal_cell_max_abs_shift_le_of_ptrunc (μ := μ) (ℱ := ℱ)
    (ξ := fun k ω => Q (k + 1) ω - Q k ω) (A := B) hB hG hQm hQi hQ0 hC hbdd hn hε
  have htele : ∀ (k : ℕ) (ω : Ω),
      LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) (s + k) ω -
        LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) s ω =
          Q (s + k) ω - Q s ω := by
    intro k ω
    rw [psum_succ_sub, psum_succ_sub]
    ring
  have heq : B ∩ {ω | ∃ k ≤ n,
      ε ≤ |LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) (s + k) ω -
        LocMart.psum (fun k ω => Q (k + 1) ω - Q k ω) s ω|} =
      A ∩ OscStartCell Q τ n ε s := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, OscStartCell, B]
    constructor
    · rintro ⟨⟨hωA, hωτ⟩, k, hk, hdev⟩
      refine ⟨hωA, hωτ, k, hk, ?_⟩
      rw [htele k ω] at hdev
      exact hdev
    · rintro ⟨hωA, hωτ, k, hk, hdev⟩
      refine ⟨⟨hωA, hωτ⟩, k, hk, ?_⟩
      rw [htele k ω]
      exact hdev
  rw [heq] at h
  exact h

end ShiftedAdvance
