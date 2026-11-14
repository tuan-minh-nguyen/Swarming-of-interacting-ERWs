/-
# The literal source `HalfClauseAt` from the good event of the halving clause

`HalvingResidual.measure_badHalf_le` bounds the paper's halving bad event by the advance bad
event (`BadTime`) plus the complement of `GoodHalf`.  This file

* removes the abstract `IsRecord` premise in favour of the *literal* a.e. record structure of
  the canonical array (`RecordMeas.ae_isRecord_recTimeA`), at the cost of a null set
  (`measure_badHalf_le_ae`);
* instantiates everything at the actual array — `Swarming.Uniform.arrayMeasure N`,
  `actX p m U`, `recTimeA p m U`, `HblkFinal.arrQ p m U` — and produces the literal
  `SourceTightAvail.HalfClauseAt`.

So the halving clause of the tightness engine follows from a **profile bound on
`BadTime ∪ (GoodHalf)ᶜ`** alone:
`μ{BadTime B T (arrQ p m ·) r ℓ} + μ{¬ GoodHalf (actX)(recTimeA) B T ℓ r} ≤ p₂ ℓ`.
`GoodHalf` is `HalvingResidual.GoodHalf`: the carrier `{d_r ≤ L}`, a local-good field at some
compatible constants with explicit size condition, and one coalescence time.  No stationarity,
invariance, start law, `dT` bound or `η = 0` appears.
-/
import Swarm.HalvingResidual
import Swarm.SourceTightAvail

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply HblkTwo HblkFinal FluidBlock
open Swarming Swarming.Uniform SwarmRecordMeas SwarmRecordMeas.Actual

namespace JoinStep

variable {N : ℕ} [Nonempty (Fin N)]

/-- The abstract bound with an almost-everywhere (instead of pointwise) record structure.
The null set is added explicitly and is `0` by hypothesis. -/
theorem measure_badHalf_le_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : Fin N) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (hτ : ∀ᵐ ω ∂μ, IsRecord (X ω) (τ ω)) {B T L r : ℕ} (hr : (T + 3) * L ≤ r) :
    μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} +
        μ {ω | ¬ GoodHalf (ι := Fin N) (X ω) (τ ω) B T L r} := by
  have hnull : μ {ω | ¬ IsRecord (X ω) (τ ω)} = 0 := ae_iff.mp hτ
  set A : Set Ω := {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
    with hA
  set Bh : Set Ω := {ω | ¬ IsRecord (X ω) (τ ω)} with hBh
  set C : Set Ω := {ω | ¬ GoodHalf (ι := Fin N) (X ω) (τ ω) B T L r} with hC
  have hsub : {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ⊆ (A ∪ Bh) ∪ C := by
    intro ω hω
    by_cases hb : HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L
    · exact Or.inl (Or.inl hb)
    · by_cases hrec : IsRecord (X ω) (τ ω)
      · refine Or.inr ?_
        intro hg
        exact not_badHalf_of_goodHalf (ι := Fin N) hrec (hne ω) hr hg hb hω
      · exact Or.inl (Or.inr hrec)
  calc μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L}
      ≤ μ ((A ∪ Bh) ∪ C) := measure_mono hsub
    _ ≤ μ (A ∪ Bh) + μ C := measure_union_le _ _
    _ ≤ (μ A + μ Bh) + μ C := by
        exact add_le_add (measure_union_le (μ := μ) A Bh) (le_refl (μ C))
    _ = μ A + μ C := by rw [hBh, hnull]; simp

/-- **The literal source halving clause.**  A profile bound on
`BadTime ∪ (GoodHalf)ᶜ` on the actual array, at the source-general constants
`B ≤ C₀ − T − 1`, gives `SourceTightAvail.HalfClauseAt`. -/
theorem halfClauseAt_of_goodHalf {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) (B T C₀ : ℕ) (hB : 2 ≤ B) (hC₀ : B + T + 1 ≤ C₀)
    (P : ℕ → ℝ≥0∞)
    (hP : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U : Array N | HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r ℓ}
        + (arrayMeasure N) {U : Array N |
            ¬ JoinStep.GoodHalf (ι := Fin N) (actX p m U) (recTimeA p m U) B T ℓ r} ≤ P ℓ) :
    SourceTightAvail.HalfClauseAt (N := N) p m B C₀ P := by
  intro ℓ hℓ r hr
  have hL : 1 ≤ ℓ := hℓ
  have hr3 : (T + 3) * ℓ ≤ r := by
    have h1 : T + 3 ≤ C₀ := by omega
    exact le_trans (Nat.mul_le_mul_right ℓ h1) hr
  have hmain := measure_badHalf_le_ae (N := N) (B := B) (T := T) (arrayMeasure N)
    (fun U => actX p m U) (fun U => recTimeA p m U)
    (fun U => actX_step p m U)
    (ae_isRecord_recTimeA (N := N) hp0 hp1 hm hN) hr3
  have hset : ∀ U : Array N,
      HblkTwo.BadHalf B (fun u => (defect (actX p m U) (recTimeA p m U) u).toNat,
        fun r => recTimeA p m U r) r ℓ
        = HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ := by
    intro U
    rfl
  simp only [hset] at hmain
  exact le_trans hmain (hP ℓ hL r hr)

end JoinStep

/-! ## Axiom audit (source order) -/


