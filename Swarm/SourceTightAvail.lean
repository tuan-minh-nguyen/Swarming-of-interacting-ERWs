/-
# Source-constant wrapper for the two residual block clauses

The general tightness engine accepts arbitrary `B`, `T`, `C₀`, while the
convenience interface in `TightAvail` fixes the smaller record-time constant.
This file exposes the source-compatible generality without proving either
stochastic estimate.  The record-time statement supplied by `M7Block.hterm_actual`
is enlarged using monotonicity of `GoodT`; scale arithmetic, summability,
Krylov--Bogoliubov and positivity are reused unchanged.
-/
import Swarm.TightAvail

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmRecordMeas
  SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform HblkTwo HblkScale

namespace SourceTightAvail

variable {N m : ℕ} [Nonempty (Fin N)]

/-- Enlarging the record-time allowance and the intermediate-defect allowance
preserves a good block. -/
theorem goodT_mono {B T₀ T C₀₀ C₀ r L : ℕ} {ω : ℕ → RecState N m × ℕ}
    (hT : T₀ ≤ T) (hC : C₀₀ ≤ C₀) :
    GoodT B C₀₀ T₀ ω r L → GoodT B C₀ T ω r L := by
  rintro ⟨htime, hhalf, hsup⟩
  refine ⟨?_, hhalf, ?_⟩
  · exact htime.trans (Nat.add_le_add_left (Nat.mul_le_mul_right L hT) _)
  · intro u hru hur
    exact (hsup u hru hur).trans (Nat.mul_le_mul_right L hC)

/-- The paper's record-advance estimate at arbitrary compatible constants. -/
def AdvanceClauseAt (p : ℝ) (m : ℕ) (B T C₀ : ℕ) (p₁ : ℕ → ℝ≥0∞) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
    (arrayMeasure N) {U | BadTime B T (HblkFinal.arrQ p m U) r ℓ} ≤ p₁ ℓ

/-- The paper's defect-halving estimate at arbitrary compatible constants. -/
def HalfClauseAt (p : ℝ) (m : ℕ) (B C₀ : ℕ) (p₂ : ℕ → ℝ≥0∞) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
    (arrayMeasure N) {U | BadHalf B (HblkFinal.arrQ p m U) r ℓ} ≤ p₂ ℓ

/-- Source-constant record tightness from the two remaining stochastic clauses.
The speed witness is supplied by the actual array.  Callers may use any `T`
above its proved record-time threshold and any `C₀ ≥ B+T+1`; in particular,
the larger `(BTchoice)` constants are not replaced by stronger bad events. -/
theorem record_tightness_of_block_clauses_at {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T C₀ : ℕ),
      (⌈2 * (B : ℝ) / κ⌉₊ + 2) ≤ T → B + T + 1 ≤ C₀ →
      ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      AdvanceClauseAt (N := N) p m B T C₀ p₁ → HalfClauseAt (N := N) p m B C₀ p₂ →
      ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
        (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
          {ω | K < dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, hterm₀⟩ := M7Block.hterm_actual (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun T C₀ hT hC₀ p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ ε hε => ?_⟩
  have hterm : ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
        ∃ j : ℕ, GoodT B C₀ T ω r (2 ^ j * L) := by
    intro r L hL
    filter_upwards [hterm₀ r L hL] with ω hω
    obtain ⟨j, hj⟩ := hω
    exact ⟨j, goodT_mono hT (by omega) hj⟩
  obtain ⟨k, hk, hmono, hbound, hpowy⟩ :=
    HblkScale.exists_compatible_scale C₀ (by omega)
  have hdec : ∀ ℓ : ℕ, (p₁ + p₂) ℓ ≤
      ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
    intro ℓ
    have h1 := hdec₁ ℓ
    have h2 := hdec₂ ℓ
    have hadd : ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
        + ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
        = ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    calc (p₁ + p₂) ℓ = p₁ ℓ + p₂ ℓ := rfl
      _ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)
            + ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := add_le_add h1 h2
      _ = ENNReal.ofReal ((K₁ + K₂) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := hadd
  refine HblkFinal.record_tightness_of_two (N := N) hp0 hp1 hm hN B T C₀ hB hC₀
    hterm p₁ p₂ h₁ h₂ k (HblkScale.g k) hmono hbound hpowy
    (HdefDefect.hdef_actual_hblkScale (N := N) hp0 hp1 hm hN k)
    ?_ (AuditSummable.tsum_coeff_mul_ne_top B (add_nonneg hK₁ hK₂) hdec) ε hε
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have h := Nat.one_le_two_pow (n := k + 1)
    exact_mod_cast h
  exact AuditSummable.tsum_at_scale_ne_top (g := HblkScale.g k) (D := (2 : ℝ) ^ (k + 1))
    (K := K₁ + K₂) hD (add_nonneg hK₁ hK₂)
    (fun r => AuditSummable.le_shift_mul_pow_g k r) (fun r => hdec _)

/-- Proposition `front` from source-constant forms of the two remaining
`(blkprob)` estimates.  This constructs the genuine stopped-record invariant
law conditionally on those estimates only; it is not an invariant-law proof. -/
theorem exists_invariant_of_block_clauses_at {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T C₀ : ℕ),
      (⌈2 * (B : ℝ) / κ⌉₊ + 2) ≤ T → B + T + 1 ≤ C₀ →
      ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      AdvanceClauseAt (N := N) p m B T C₀ p₁ → HalfClauseAt (N := N) p m B C₀ p₂ →
      ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
        Kernel.Invariant (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π ∧
        0 < π (srSet N m) := by
  obtain ⟨κ, hκ, H⟩ := record_tightness_of_block_clauses_at (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun T C₀ hT hC₀ p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hN0 : 0 < N := by omega
  haveI hν : IsProbabilityMeasure (TightAvail.startLaw (N := N) (m := m) hm1) :=
    TightAvail.isProbabilityMeasure_startLaw (N := N) (m := m) hm1
  have hpath := H T C₀ hT hC₀ p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂
  have hpath' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      recordTrajT p hp0.le hp1.le hm1 (TightAvail.startLaw (N := N) (m := m) hm1)
        {ω : ℕ → RecState N m × ℕ | K < dT ω r} ≤ ε := by
    intro ε hε
    simpa only [TightAvail.startLaw] using hpath ε hε
  have htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm1))^[r]
        (Measure.dirac (zeroState (N := N) (m := m) hm1)) (exh N m K)ᶜ ≤ ε := by
    have hν' := (TightAvail.iterate_tight_iff_dT_tail (N := N) (m := m) p
      hp0.le hp1.le hm1 (TightAvail.startLaw (N := N) (m := m) hm1)).mpr hpath'
    have hfst : (TightAvail.startLaw (N := N) (m := m) hm1).map Prod.fst
        = Measure.dirac (zeroState (N := N) (m := m) hm1) :=
      TightAvail.startLaw_fst hm1
    intro ε hε
    have htail := hν' ε hε
    rwa [hfst] at htail
  exact SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_of_tight (N := N) (m := m) p
    hp0.le hp1.le hp1 hm1 hN0 (Measure.dirac (zeroState (N := N) (m := m) hm1)) htight

end SourceTightAvail
