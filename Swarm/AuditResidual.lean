/-## The residual inputs of record tightness are exactly the two block clauses

This file composes the integrated pieces:

* `HblkFinal.record_tightness_of_two` (m3, coordinator-reviewed) — the two-clause reduction;
* `HblkScale.exists_compatible_scale` — the satisfiable scale arithmetic (`hmono`, `hbound`,
  `hpowy`) at the paper's constants, with the concrete scale `g r = r.log2 - k`;
* `HdefDefect.hdef_actual_hblkScale` (m1, integrated snapshot) — the eventual defect bound `hdef`,
  unconditionally, at the same scale;
* `AuditSummable.tsum_coeff_mul_ne_top`, `AuditSummable.tsum_at_scale_ne_top` — the two summability
  conditions, from cubic decay of the profiles.

and obtains: **along the canonical stopped-record path law, record tightness follows from the two
array-side block clauses `h₁`, `h₂` alone** (with any profiles of cubic-or-faster decay, e.g. the
paper's `C_T e^{-c_T ℓ^{1/16}}`).

So the residual list of the record-tightness route is `{h₁, h₂}` — the paper's `(blkprob)`, which
remains open.  Nothing here proves `h₁` or `h₂`, and nothing here proves the main theorem, the
invariant law, regeneration or `Ballistic`.

`AuditCoarse` in this directory shows that `h₂` cannot be weakened by the coarse-scale halving:
the certificate argument needs it uniformly in `r` at fine scales.
-/
import Swarm.AuditCoarse
import Swarm.AuditSummable
import Swarm.HdefDefect

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmRecordMeas
  SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform HblkTwo HblkScale

namespace AuditResidual

/-- **Record tightness from the two block clauses and cubic profile decay.**

Same conclusion as `HblkFinal.record_tightness_of_two` (and as
`HdefDefect.record_tightness_of_two_actual_hdef_free`) with the two summability hypotheses replaced
by explicit decay bounds on the profiles. -/
theorem record_tightness_of_two_actual_blocks {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U | HblkTwo.BadTime B (⌈2 * (B : ℝ) / κ⌉₊ + 2) (HblkFinal.arrQ p m U) r ℓ} ≤ p₁ ℓ) →
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U | HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ} ≤ p₂ ℓ) →
      ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
        (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
          {ω | K < dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, hterm⟩ := M7Block.hterm_actual (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ ε hε => ?_⟩
  -- the satisfiable scale arithmetic at the paper's constants
  obtain ⟨k, hk, hmono, hbound, hpowy⟩ :=
    HblkScale.exists_compatible_scale (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (by omega)
  -- the profile bound for `p₁ + p₂`
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
  refine HblkFinal.record_tightness_of_two (N := N) hp0 hp1 hm hN B
    (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) hB le_rfl hterm p₁ p₂
    h₁ h₂ k (HblkScale.g k) hmono hbound hpowy
    (HdefDefect.hdef_actual_hblkScale (N := N) hp0 hp1 hm hN k)
    ?_ (AuditSummable.tsum_coeff_mul_ne_top B (add_nonneg hK₁ hK₂) hdec) ε hε
  -- the Borel–Cantelli summability at the repaired logarithmic scale
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    have h := Nat.one_le_two_pow (n := k + 1)
    exact_mod_cast h
  exact AuditSummable.tsum_at_scale_ne_top (g := HblkScale.g k) (D := (2 : ℝ) ^ (k + 1))
    (K := K₁ + K₂) hD (add_nonneg hK₁ hK₂)
    (fun r => AuditSummable.le_shift_mul_pow_g k r) (fun r => hdec _)

end AuditResidual


