/-
# Carrier-local `GoodTime` bounds and the normalized-defect obstruction

`BadTime` and `BadHalf` already contain the paper's starting-defect carrier.
The existing unrestricted `noGoodTime` bound discards that carrier.  This file
retains it exactly and repackages the source-general two clauses from one
carrier-local failure profile.  No such profile is proved here.

The second part is a separate sharpness statement.  The integer sequence
`Nat.sqrt r` has normalized defect tending to zero, yet for every `C₀` and `L`
there is an index `r ≥ C₀ * L` whose base defect exceeds `L`.  Thus normalized
record convergence alone cannot produce a vanishing uniform base-tail profile.
This is a counterexample to that proposed inference, not a countermodel to the
actual WCJF array or to its main theorem.
-/
import Swarm.SourceTightAvail
import Swarm.FluidWiring

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply HblkTwo HblkFinal FluidBlock
open Swarming Swarming.Uniform SwarmRecordMeas SwarmRecordMeas.Actual

namespace BaseCarrier

variable {ι Ω : Type*} [Fintype ι] [Nonempty ι]

/-- On a genuine record sequence, a natural-number bound on `defect.toNat`
is the same integer defect bound used by `GoodTime`. -/
theorem defect_le_of_toNat_le {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}
    (hτ : IsRecord X τ) {r L : ℕ}
    (h : (defect X τ r).toNat ≤ L) : defect X τ r ≤ (L : ℤ) := by
  have h' : (((defect X τ r).toNat : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
  rwa [Int.toNat_of_nonneg (defect_nonneg hτ r)] at h'

/-- The carrier-preserving advance bound.  Unlike the unrestricted
`noGoodTime` reduction, its right event retains `defect ≤ L`. -/
theorem measure_badTime_le_restricted_of_ae [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (h0 : ∀ (ω : Ω) (i : ι), X ω i 0 = 0)
    (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω))
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    μ {ω | BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | defect (X ω) (τ ω) r ≤ (L : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} := by
  have hnull : μ {ω | ¬ IsRecord (X ω) (τ ω)} = 0 := ae_iff.mp hτ
  have hsub : {ω | BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ⊆
      {ω | defect (X ω) (τ ω) r ≤ (L : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} ∪
      {ω | ¬ IsRecord (X ω) (τ ω)} := by
    intro ω hω
    by_cases hrec : IsRecord (X ω) (τ ω)
    · apply Set.mem_union_left
      refine ⟨defect_le_of_toNat_le hrec hω.1, ?_⟩
      rintro ⟨n, hn⟩
      exact (goodTime_imp_not_bad hrec (hne ω) (h0 ω) hC₀ hn).1 hω
    · exact Set.mem_union_right _ hrec
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hnull, add_zero]

/-- The carrier-preserving halving bound, at the same source constants. -/
theorem measure_badHalf_le_restricted_of_ae [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (h0 : ∀ (ω : Ω) (i : ι), X ω i 0 = 0)
    (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω))
    {B T C₀ r L : ℕ} (hC₀ : B + T + 1 ≤ C₀) :
    μ {ω | BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | defect (X ω) (τ ω) r ≤ (L : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} := by
  have hnull : μ {ω | ¬ IsRecord (X ω) (τ ω)} = 0 := ae_iff.mp hτ
  have hsub : {ω | BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ⊆
      {ω | defect (X ω) (τ ω) r ≤ (L : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (X ω) (τ ω) B T r L n} ∪
      {ω | ¬ IsRecord (X ω) (τ ω)} := by
    intro ω hω
    by_cases hrec : IsRecord (X ω) (τ ω)
    · apply Set.mem_union_left
      refine ⟨defect_le_of_toNat_le hrec hω.1, ?_⟩
      rintro ⟨n, hn⟩
      exact (goodTime_imp_not_bad hrec (hne ω) (h0 ω) hC₀ hn).2 hω
    · exact Set.mem_union_right _ hrec
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [hnull, add_zero]

variable {N : ℕ} [Nonempty (Fin N)]

/-- One carrier-local `GoodTime` profile supplies the literal source-general
advance clause.  The profile itself remains a stochastic input. -/
theorem advanceClauseAt_of_restricted_goodTime_profile {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀) (P : ℕ → ℝ≥0∞)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U : Array N |
        defect (actX p m U) (recTimeA p m U) r ≤ (ℓ : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r ℓ n} ≤ P ℓ) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ P := by
  intro ℓ hℓ r hr
  exact le_trans
    (measure_badTime_le_restricted_of_ae (arrayMeasure N)
      (fun U => actX p m U) (fun U => recTimeA p m U)
      (fun U => actX_step p m U) (fun U => actX_zero p m U)
      (ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN) hC₀)
    (hP ℓ hℓ r hr)

/-- The same carrier-local profile supplies the literal source-general
halving clause; no unrestricted base-tail bound is added. -/
theorem halfClauseAt_of_restricted_goodTime_profile {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B T C₀ : ℕ) (hC₀ : B + T + 1 ≤ C₀) (P : ℕ → ℝ≥0∞)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U : Array N |
        defect (actX p m U) (recTimeA p m U) r ≤ (ℓ : ℤ) ∧
        ¬ ∃ n : ℕ, GoodTime (actX p m U) (recTimeA p m U) B T r ℓ n} ≤ P ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ P := by
  intro ℓ hℓ r hr
  exact le_trans
    (measure_badHalf_le_restricted_of_ae (arrayMeasure N)
      (fun U => actX p m U) (fun U => recTimeA p m U)
      (fun U => actX_step p m U) (fun U => actX_zero p m U)
      (ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN) hC₀)
    (hP ℓ hℓ r hr)

/-- The integer square-root normalized record defect tends to zero. -/
theorem tendsto_nat_sqrt_div_atTop :
    Tendsto (fun r : ℕ => ((Nat.sqrt r : ℕ) : ℝ) / (r : ℝ)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun r : ℕ => √((r : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hreal : Tendsto (fun r : ℕ => √((r : ℝ)) / (r : ℝ)) atTop (𝓝 0) := by
    have heq : (fun r : ℕ => √((r : ℝ)) / (r : ℝ)) =
        (fun r : ℕ => (√((r : ℝ)))⁻¹) := by
      funext r
      exact Real.sqrt_div_self
    rw [heq]
    exact tendsto_inv_atTop_zero.comp hsqrt
  apply squeeze_zero (fun r => by positivity) (fun r => ?_) hreal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.sqrt_le' r)

/-- There is always an index beyond every linear lower cutoff whose integer
square-root defect exceeds the prescribed level. -/
theorem exists_sqrt_base_tail (C₀ L : ℕ) :
    ∃ r : ℕ, C₀ * L ≤ r ∧ L < Nat.sqrt r := by
  refine ⟨C₀ * L + (L + 1) * (L + 1), Nat.le_add_right _ _, ?_⟩
  have hs : L + 1 ≤ Nat.sqrt (C₀ * L + (L + 1) * (L + 1)) :=
    Nat.le_sqrt.2 (Nat.le_add_left _ _)
  omega

/-- The deterministic square-root model has base-tail probability one on some
admissible index beyond every linear cutoff. -/
theorem sqrt_baseTail_dirac_eq_one (C₀ L : ℕ) :
    (Measure.dirac ()) {x : Unit | ∃ r : ℕ, C₀ * L ≤ r ∧ L < Nat.sqrt r} = 1 := by
  have hset : {x : Unit | ∃ r : ℕ, C₀ * L ≤ r ∧ L < Nat.sqrt r} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_sqrt_base_tail C₀ L
  rw [hset]
  exact Measure.dirac_apply_of_mem (Set.mem_univ ())

/-- Consequently no vanishing profile can uniformly dominate all admissible
base tails in the deterministic square-root model, even though its normalized
defect tends to zero. -/
theorem not_tendsto_sqrt_base_profile (C₀ : ℕ) (P : ℕ → ℝ≥0∞)
    (hP : ∀ L r : ℕ, C₀ * L ≤ r →
      (Measure.dirac ()) {x : Unit | L < Nat.sqrt r} ≤ P L) :
    ¬ Tendsto P atTop (𝓝 0) := by
  have hlarge : ∀ L : ℕ, 1 ≤ P L := by
    intro L
    obtain ⟨r, hr, hLr⟩ := exists_sqrt_base_tail C₀ L
    have hmem : () ∈ {x : Unit | L < Nat.sqrt r} := hLr
    have hone : (Measure.dirac ()) {x : Unit | L < Nat.sqrt r} = 1 :=
      Measure.dirac_apply_of_mem hmem
    rw [← hone]
    exact hP L r hr
  intro hlim
  have hevent : ∀ᶠ L : ℕ in atTop, P L < (1 : ℝ≥0∞) / 2 :=
    (tendsto_order.1 hlim).2 _ (by norm_num)
  obtain ⟨L, hL⟩ := hevent.exists
  exact (not_lt_of_ge (hlarge L)) (hL.trans_le (by norm_num))

end BaseCarrier
