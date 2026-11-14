/-
# Instruction T: how much tightness does an invariant record law need, and what is available

## The audit, in one paragraph

The Krylov–Bogoliubov mechanism of the paper's §3 is formalised in
`Swarm/KrylovBogoliubov.lean` (`SwarmKB.exists_invariant_cluster_point` and the
exhaustion form `SwarmKB.exists_invariant_measure_pos_of_exhaustion`).  For the genuine
stopped-record kernel `hitKKernel p hm` of `Swarm/InfKernel.lean` two of the three
analytic inputs are *proved*:

* the Feller property — `SimJump.RecKernel.feller_hitKKernel` (`Swarm/FellerInf.lean`);
* the force estimate `c K ≤ κ y (srSet N m)` on the compact exhaustion
  `exh N m K = {y | ∀ i, dist2 y i ≤ K}` with `c K = ofReal ((1-p)^(N(2K+1))) > 0` —
  `SimJump.RecKernel.hitKInf_srSet_ge` (`Swarm/InfKernel.lean`).

The third input, tightness, is the only obstruction to *existence*.  `areas/tightness/KBAvgTight`
shows the exact form the cluster-point argument consumes, and `areas/tightness/ChainLink` +
`RecordChain` identify the iterates of `hitKKernel` with the first marginal of the genuine
stopped-record *path* law `recordTrajT`.  Consequently

* `iterate_tight_iff_dT_tail` below proves that the abstract premise
  `∀ ε > 0, ∃ K, ∀ r, ((step hitKKernel)^[r] μ) (exh N m K)ᶜ ≤ ε` is *exactly* tightness of the
  paper's own record distance `d_r` (`dT = 2 * dmax` in half-distance units) along the canonical
  stopped-record path law — the factor `2` and the direction of the inequality are both checked;
* `exists_invariant_of_block_clauses` composes the whole available chain
  (`AuditResidual.record_tightness_of_two_actual_blocks` → `exists_invariant_measure_pos_hitKInf_of_tight`)
  into a single statement producing an invariant probability measure `π` for `hitKKernel p hm` at
  the true model parameters `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, with `0 < π (srSet N m)`.

Everything analytic that the tree has proved is consumed: `(recordo)` (`M7Block.hterm_actual`),
the ultimate defect bound (`HdefDefect.hdef_actual_hblkScale`), the satisfiable scale arithmetic
(`HblkScale.exists_compatible_scale`), the identification of the actual array's record law with
the kernel path law (`M7Block.actual_block_law`), Feller and force.  What is *not* proved anywhere
in the tree, and is therefore the exact residual of this file, is the pair of array-side block
clauses `h₁`, `h₂` of the paper's `(blkprob)`:

* `AdvanceClause` — on `{d_r ≤ ℓ}` the record advance `τ_{r+Bℓ} - τ_r ≤ T ℓ` fails with array
  probability at most `p₁ ℓ`;
* `HalfClause` — on `{d_r ≤ ℓ}` the defect halving `d_{r+Bℓ} ≤ ℓ/2` fails with array probability
  at most `p₂ ℓ`;

both at the proved constants `T = ⌈2B/κ⌉₊ + 2`, `C₀ = B + T + 1` and with profiles of
cubic-or-faster decay (the paper's `C exp(-c ℓ^{1/16})` is allowed).  No `hdef`, no summability,
no abstract `ProbCtx`, no `ScaleBlk`, no Feller/tightness hypothesis is left.

## What is deliberately *not* claimed

No regeneration, no `KacBridge` mass identity, no `Ballistic`/`MainClaim`, and no statement about
a two-sided stationary system.  The positivity `0 < π (srSet N m)` is *not* an extra assumption:
it is produced here by the Krylov–Bogoliubov route, and `Swarm/InvariantPositivity.lean`
shows independently that *every* nonzero invariant law of `hitKKernel` charges `srSet`, so
positivity is not part of the tightness obstruction.
-/
import Swarm.AuditResidual
import Swarm.RecordChain
import Swarm.KBAvgTight
import Swarm.WeightExp

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace TightAvail

open SimJump SimJump.RecKernel SwarmRec SwarmRecordMeas
  SwarmRecordMeas.StartLaw Swarming Swarming.Uniform HblkTwo HblkFinal

variable {N m : ℕ} [Nonempty (Fin N)]

/-! ### The record-distance reading of the exhaustion tail -/

/-- The exhaustion tail of the record state is the super-level set of the paper's record distance
`d_r`.  The compact state stores half-distances, so `dT ω r = 2 * dmax (ω r).1`; the doubling is
what the level `2 * K` accounts for. -/
theorem compl_exh_eq_dT_tail (r K : ℕ) :
    {ω : ℕ → RecState N m × ℕ | (ω r).1 ∈ exh N m K}ᶜ
      = {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r} := by
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, dT]
  rw [mem_exh_iff_dmax_le]
  omega

/-- The converse inclusion at a halved level: a `dT`-super-level set at level `K` contains the
exhaustion tail at level `K / 2`.  (`dT` is even and at least `2 * (K / 2) + 2` once
`dmax ≥ K / 2 + 1`, so `dT > K` even for odd `K`.) -/
theorem exh_tail_subset_dT_tail (r K : ℕ) :
    {ω : ℕ → RecState N m × ℕ | (ω r).1 ∈ exh N m (K / 2)}ᶜ
      ⊆ {ω : ℕ → RecState N m × ℕ | K < dT ω r} := by
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, dT] at hω ⊢
  rw [mem_exh_iff_dmax_le] at hω
  omega

/-! ### The abstract tightness premise *is* the paper's record-distance tightness -/

/-- **Exactness of the tightness premise.**  For the genuine stopped-record path law
`recordTrajT p hp hp1 hm ν`, tightness of the laws of the record states `(step hitKKernel)^[r] (ν.map fst)`
on the compact exhaustion is *equivalent* to tightness of the paper's record distance `d_r = dT · r`
along that path law.  No hypothesis is lost or gained, and the level conversion is the factor `2`
of `dT = 2 * dmax` in both directions. -/
theorem iterate_tight_iff_dT_tail (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
        (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] (ν.map Prod.fst)
          (exh N m K)ᶜ ≤ ε)
      ↔ (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
        recordTrajT p hp hp1 hm ν {ω : ℕ → RecState N m × ℕ | K < dT ω r} ≤ ε) := by
  constructor
  · intro H ε hε
    obtain ⟨K, hK⟩ := H ε hε
    refine ⟨2 * K, fun r => ?_⟩
    rw [← compl_exh_eq_dT_tail r K, recordTrajT_tail p hp hp1 hm ν r K]
    exact hK r
  · intro H ε hε
    obtain ⟨K, hK⟩ := H ε hε
    refine ⟨K / 2, fun r => ?_⟩
    rw [← recordTrajT_tail p hp hp1 hm ν r (K / 2)]
    exact le_trans (measure_mono (exh_tail_subset_dT_tail r K)) (hK r)

/-- The start law of the canonical stopped-record chain: the all-at-the-record state with record
time `0` (the only start law compatible with the actual array's joint law,
`RecordStartLaw.exists_startLaw_constraint`). -/
noncomputable def startLaw (hm : 1 ≤ m) : Measure (RecState N m × ℕ) :=
  Measure.dirac (zeroState (N := N) (m := m) hm, (0 : ℕ))

theorem isProbabilityMeasure_startLaw (hm : 1 ≤ m) :
    IsProbabilityMeasure (startLaw (N := N) (m := m) hm) :=
  ⟨by rw [startLaw]; simp⟩

theorem startLaw_fst (hm : 1 ≤ m) :
    (startLaw (N := N) (m := m) hm).map Prod.fst
      = Measure.dirac (zeroState (N := N) (m := m) hm) := by
  rw [startLaw, Measure.map_dirac]

/-! ### The residual ledger: the paper's two block clauses -/

/-- **Residual clause `h₁`**: at the proved constants `B`, `T = ⌈2B/κ⌉₊ + 2`,
`C₀ = B + T + 1`, from a record index `r ≥ C₀ ℓ` the record time advances by at most `T ℓ` with
array probability at least `1 - p₁ ℓ`, whenever the current defect is at most `ℓ`. -/
def AdvanceClause (p : ℝ) (m : ℕ) (B : ℕ) (κ : ℝ)
    (p₁ : ℕ → ℝ≥0∞) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
    (arrayMeasure N) {U | BadTime B (⌈2 * (B : ℝ) / κ⌉₊ + 2) (arrQ p m U) r ℓ} ≤ p₁ ℓ

/-- **Residual clause `h₂`**: at the same constants, from a record index `r ≥ C₀ ℓ` and current
defect at most `ℓ`, the defect halves within `B ℓ` record steps with array probability at least
`1 - p₂ ℓ`. -/
def HalfClause (p : ℝ) (m : ℕ) (B : ℕ) (κ : ℝ)
    (p₂ : ℕ → ℝ≥0∞) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
    (arrayMeasure N) {U | BadHalf B (arrQ p m U) r ℓ} ≤ p₂ ℓ

/-- **Availability of an invariant record law from the two block clauses.**  At the true model
parameters `1/2 < p < 1`, `2 ≤ m`, `2 ≤ N`, for every block size `B ≥ 1` there is a ballistic
slope `κ > 0` (proved, from `(recordo)`) such that the paper's two block clauses at the proved
constants and with cubic-or-faster profile decay produce an *invariant probability measure* for
the genuine stopped-record kernel `hitKKernel p hm` that charges `srSet N m`.

Nothing else is assumed: Feller, force, `(recordo)`, the ultimate defect bound, the scale
arithmetic, the summability of the certificate series and the identification of the actual
array's record law with `recordTrajT` are all theorems of the registered tree. -/
theorem exists_invariant_of_block_clauses {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      AdvanceClause (N := N) p m B κ p₁ → HalfClause (N := N) p m B κ p₂ →
      ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
        Kernel.Invariant (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π ∧
        0 < π (srSet N m) := by
  obtain ⟨κ, hκ, H⟩ :=
    AuditResidual.record_tightness_of_two_actual_blocks (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hN0 : 0 < N := by omega
  haveI hν : IsProbabilityMeasure (startLaw (N := N) (m := m) hm1) :=
    isProbabilityMeasure_startLaw (N := N) (m := m) hm1
  -- the available record-path tightness, read on the canonical start law
  have hpath := H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂
  have hpath' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      recordTrajT p hp0.le hp1.le hm1 (startLaw (N := N) (m := m) hm1)
        {ω : ℕ → RecState N m × ℕ | K < dT ω r} ≤ ε := by
    intro ε hε
    simpa only [startLaw] using hpath ε hε
  -- the abstract tightness premise of the Krylov--Bogoliubov step, exactly
  have htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm1))^[r]
        (Measure.dirac (zeroState (N := N) (m := m) hm1)) (exh N m K)ᶜ ≤ ε := by
    have hν' := (iterate_tight_iff_dT_tail (N := N) (m := m) p hp0.le hp1.le hm1
      (startLaw (N := N) (m := m) hm1)).mpr hpath'
    have hfst : (startLaw (N := N) (m := m) hm1).map Prod.fst
        = Measure.dirac (zeroState (N := N) (m := m) hm1) := startLaw_fst hm1
    intro ε hε
    have := hν' ε hε
    rwa [hfst] at this
  exact SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_of_tight (N := N) (m := m) p
    hp0.le hp1.le hp1 hm1 hN0 (Measure.dirac (zeroState (N := N) (m := m) hm1)) htight

/-- The positivity half of the availability statement, restated as the Kac side conditions a
downstream consumer reads: the invariant record law charges `srSet N m` strictly and finitely. -/
theorem invariant_record_law_available {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      (∀ ℓ : ℕ, p₁ ℓ ≤ ENNReal.ofReal (K₁ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      (∀ ℓ : ℕ, p₂ ℓ ≤ ENNReal.ofReal (K₂ * (((ℓ : ℝ) + 1))⁻¹ ^ 3)) →
      AdvanceClause (N := N) p m B κ p₁ → HalfClause (N := N) p m B κ p₂ →
      ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
        Kernel.Invariant (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π ∧
        0 < π (srSet N m) ∧ π (srSet N m) ≠ ⊤ := by
  obtain ⟨κ, hκ, H⟩ := exists_invariant_of_block_clauses (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂ => ?_⟩
  obtain ⟨π, hprob, hinv, hpos⟩ := H p₁ p₂ K₁ K₂ hK₁ hK₂ hdec₁ hdec₂ h₁ h₂
  exact ⟨π, hprob, hinv, hpos, measure_ne_top π _⟩


/-! ### The paper's own profile `C exp (-c ℓ^(1/16))` -/

/-- The profile shape of the paper's block estimate `(blkprob)`, as an `ℝ≥0∞`-valued profile. -/
noncomputable def paperProfile (C cc : ℝ) (ℓ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16))))

/-- **The paper's profile decays cubically.**  `exp (-c ℓ^(1/16))` beats the polynomial
`(ℓ+1)⁻³`, so `paperProfile C cc` satisfies the decay hypothesis of
`exists_invariant_of_block_clauses` with the explicit constant `K = max C (8 · C · 48! / c^48)`. -/
theorem paperProfile_le_cubic {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ℓ : ℕ,
      paperProfile C cc ℓ ≤ ENNReal.ofReal (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3) := by
  refine ⟨max C (8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ))), ?_, fun ℓ => ?_⟩
  · exact le_trans hC (le_max_left _ _)
  · rw [paperProfile]
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h
      refine ENNReal.ofReal_le_ofReal ?_
      have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) := by norm_num
      have hzero : (0 : ℝ) ^ ((1 : ℝ) / 16) = 0 :=
        Real.zero_rpow (x := (1 : ℝ) / 16) (by norm_num)
      have hval : C * Real.exp (-(cc * (((0 : ℕ) : ℝ)) ^ ((1 : ℝ) / 16))) = C := by
        rw [hcast, hzero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      rw [hval]
      have hone : (((0 : ℕ) : ℝ) + 1)⁻¹ ^ 3 = (1 : ℝ) := by norm_num
      rw [hone, mul_one]
      exact le_max_left _ _
    · have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
      have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
      refine ENNReal.ofReal_le_ofReal ?_
      -- `exp` beats the cubic polynomial at the scale `ℓ^(1/16)`
      have hexp := RecordTight.exp_neg_rpow_le_fact (cc := cc) hc h
      have hstep : C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16)))
          ≤ C * ((((48 : ℕ).factorial : ℝ)) / (cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ))) :=
        mul_le_mul_of_nonneg_left hexp hC
      -- `(ℓ+1)³ ≤ 8 ℓ³`
      have hcube : ((ℓ : ℝ) + 1) ^ (3 : ℕ) ≤ 8 * (ℓ : ℝ) ^ (3 : ℕ) := by
        have h2 : (ℓ : ℝ) + 1 ≤ 2 * (ℓ : ℝ) := by linarith
        have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) + 1) h2 3
        calc ((ℓ : ℝ) + 1) ^ (3 : ℕ) ≤ (2 * (ℓ : ℝ)) ^ (3 : ℕ) := h3
          _ = 8 * (ℓ : ℝ) ^ (3 : ℕ) := by ring
      have hpos1 : (0 : ℝ) < (ℓ : ℝ) ^ (3 : ℕ) := by positivity
      have hpos2 : (0 : ℝ) < ((ℓ : ℝ) + 1) ^ (3 : ℕ) := by positivity
      have h8 : ((8 : ℝ) * (ℓ : ℝ) ^ (3 : ℕ))⁻¹ ≤ (((ℓ : ℝ) + 1) ^ (3 : ℕ))⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hpos2]
        exact hcube
      have h8' : ((8 : ℝ) * (ℓ : ℝ) ^ (3 : ℕ))⁻¹
          = (1 / 8) * (((ℓ : ℝ) ^ (3 : ℕ))⁻¹) := by
        rw [mul_inv]
        norm_num
      have hinv : (((ℓ : ℝ) ^ (3 : ℕ))⁻¹) ≤ 8 * ((((ℓ : ℝ) + 1) ^ (3 : ℕ))⁻¹) := by
        rw [h8'] at h8
        linarith
      have hfac : (0 : ℝ) ≤ C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ) := by positivity
      have hK : 8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ))
          ≤ max C (8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ))) := le_max_right _ _
      calc C * Real.exp (-(cc * (ℓ : ℝ) ^ ((1 : ℝ) / 16)))
          ≤ C * ((((48 : ℕ).factorial : ℝ)) / (cc ^ (48 : ℕ) * (ℓ : ℝ) ^ (3 : ℕ))) := hstep
        _ = (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ)) *
              (((ℓ : ℝ) ^ (3 : ℕ))⁻¹) := by
            field_simp
        _ ≤ (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ)) *
              (8 * (((ℓ : ℝ) + 1) ^ (3 : ℕ))⁻¹) := by
            exact mul_le_mul_of_nonneg_left hinv hfac
        _ = 8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ)) *
              ((((ℓ : ℝ) + 1) ^ (3 : ℕ))⁻¹) := by ring
        _ ≤ max C (8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ))) *
              ((((ℓ : ℝ) + 1) ^ (3 : ℕ))⁻¹) := by
            exact mul_le_mul_of_nonneg_right hK (by positivity)
        _ = max C (8 * (C * (((48 : ℕ).factorial : ℝ)) / cc ^ (48 : ℕ))) *
              (((ℓ : ℝ) + 1)⁻¹ ^ 3) := by
            rw [inv_pow]

/-- **Availability with the paper's own profile.**  It is enough that the two block clauses hold
with the paper's `C exp (-c ℓ^(1/16))` profile: the invariant record law with `0 < π (srSet N m)`
then exists at the true model parameters. -/
theorem exists_invariant_of_paper_profile {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) {C cc : ℝ} (hC : 0 ≤ C) (hc : 0 < cc) :
    ∃ κ : ℝ, 0 < κ ∧
      (AdvanceClause (N := N) p m B κ (paperProfile C cc) →
        HalfClause (N := N) p m B κ (paperProfile C cc) →
        ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
          Kernel.Invariant (hitKKernel (N := N) (m := m) p (by omega : 1 ≤ m)) π ∧
          0 < π (srSet N m)) := by
  obtain ⟨κ, hκ, H⟩ := exists_invariant_of_block_clauses (N := N) hp0 hp1 hm hN B hB
  obtain ⟨K, hK, hdec⟩ := paperProfile_le_cubic (C := C) (cc := cc) hC hc
  refine ⟨κ, hκ, ?_⟩
  intro h₁ h₂
  exact H (paperProfile C cc) (paperProfile C cc) K K hK hK hdec hdec h₁ h₂

end TightAvail

/-! ## Axiom audit -/


namespace TightAvail

open SimJump SimJump.RecKernel SwarmRec SwarmRecordMeas SwarmRecordMeas.StartLaw

variable {N m : ℕ} [Nonempty (Fin N)]

/-! ### The paper's `(tightlaw)` form of the premise

The paper derives tightness of the record distances as an *eventual* statement
`lim_K limsup_u P(d_u > K) = 0` (its (tightlaw)), which is weaker than a uniform bound in `r`.
The next two declarations show that this weaker form is exactly what the Krylov--Bogoliubov step
consumes (`SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_limsup`), and that it implies
the invariant record law with positive `srSet` mass at the true model parameters. -/

/-- The eventual (limsup) form of the tightness equivalence: tightness of the laws of the iterates
of `hitKKernel` on the exhaustion is equivalent to tightness of the record distance `dT` along the
canonical stopped-record path law, both in the eventual sense used by the paper's `(tightlaw)`. -/
theorem eventually_tight_iff_dT_tail (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ r : ℕ in atTop,
        (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] (ν.map Prod.fst)
          (exh N m K)ᶜ ≤ ε)
      ↔ (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ r : ℕ in atTop,
        recordTrajT p hp hp1 hm ν {ω : ℕ → RecState N m × ℕ | K < dT ω r} ≤ ε) := by
  constructor
  · intro H ε hε
    obtain ⟨K, hK⟩ := H ε hε
    refine ⟨2 * K, ?_⟩
    filter_upwards [hK] with r hr
    rw [← recordTrajT_tail p hp hp1 hm ν r K, compl_exh_eq_dT_tail r K] at hr
    exact hr
  · intro H ε hε
    obtain ⟨K, hK⟩ := H ε hε
    refine ⟨K / 2, ?_⟩
    filter_upwards [hK] with r hr
    rw [← recordTrajT_tail p hp hp1 hm ν r (K / 2)]
    exact le_trans (measure_mono (exh_tail_subset_dT_tail r K)) hr

/-- **The minimal missing premise, in the paper's own form.**  If the paper's `(tightlaw)` holds
for the canonical stopped-record path law — i.e. for every `ε > 0` there is a level `K` with
`P (d_r > K) ≤ ε` eventually in the record index `r` — then the genuine stopped-record kernel
`hitKKernel p hm` has an invariant probability measure charging `srSet N m`, for every
`1/2 ≤ p < 1` and `1 ≤ m`, `0 < N`.  No Feller property, force estimate, block estimate,
summability or `hdef` input is assumed: those are theorems (`feller_hitKKernel`,
`hitKInf_srSet_ge`, `HdefDefect`) or are consumed by `exists_invariant_of_block_clauses`. -/
theorem exists_invariant_of_dT_tight (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ r : ℕ in atTop,
      recordTrajT p hp hp1.le hm (startLaw (N := N) (m := m) hm)
        {ω : ℕ → RecState N m × ℕ | K < dT ω r} ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧ 0 < π (srSet N m) := by
  haveI := isProbabilityMeasure_startLaw (N := N) (m := m) hm
  have htight := (eventually_tight_iff_dT_tail (N := N) (m := m) p hp hp1.le hm
    (startLaw (N := N) (m := m) hm)).mpr h
  have hfst : (startLaw (N := N) (m := m) hm).map Prod.fst
      = Measure.dirac (zeroState (N := N) (m := m) hm) := startLaw_fst hm
  refine SimJump.RecKernel.exists_invariant_measure_pos_hitKInf_limsup (N := N) (m := m) p
    hp hp1.le hp1 hm hN (Measure.dirac (zeroState (N := N) (m := m) hm)) ?_
  intro ε hε
  obtain ⟨K, hK⟩ := htight ε hε
  refine ⟨K, ?_⟩
  filter_upwards [hK] with r hr
  rwa [hfst] at hr

end TightAvail


