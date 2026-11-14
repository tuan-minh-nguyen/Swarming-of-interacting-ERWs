/-
# Record-path tightness from the two remaining block clauses

This file assembles the verified pieces into one non-vacuous reduction of the record-tightness
route.

* `HblkTwo.hblk_canonical_of_two`: the paper's `(blkprob)` on the canonical stopped-record path
  law from the two array-side bad-event bounds (record advance and defect halving).  The third
  block inequality is nearest-neighbour geometry (`RecordDefect.block_defect_bound`).
* `M7Block.hterm_actual`: the paper's `(recordo)` doubling form, unconditionally at
  `T = ⌈2B/κ⌉₊ + 2`, `C₀ = B + T + 1` (supplied by the caller as `hterm`; it is a theorem, not an
  assumption).
* `HblkScale.PCtxR.of_eventual_pow` / `tightness_of_eventual_pow`: the Borel–Cantelli step
  deriving the scale fields `hscale_good` and `hstart`, with the *satisfiable* power condition
  `∀ a r, 2 ^ (a+1+k) ≤ r → a ≤ g r`.  (The original `ScaleRepairReduce` condition
  `∀ a, a ≤ g (2^(a+1))` is contradictory with the scale bound for every `C₀ ≥ 2`; see
  `HblkScale.scale_hypotheses_incompatible`.  This matters because the route fixes `C₀ = B+T+1`.)

`record_tightness_of_two` is the composite: tightness of the record defect along the canonical
stopped-record path law from

  (1) the array-side record-advance bound `p₁`,
  (2) the array-side defect-halving bound `p₂`,
  (3) the two certificate summability conditions for `p₁ + p₂`,
  (4) the almost-sure eventual defect bound `hdef` at a scale `g` satisfying the (satisfiable)
      scale arithmetic, and
  (5) the already-proved `hterm`.

Everything else — `hlaw` (via `M7Block.jointLawIdentity_actual`), `(diam)` (via
`M7Block.diam_actual_recordo`), `IsRecord`, measurability of the array statistic, `hscale_good`,
`hstart` — is either proved elsewhere or constructed here.

This is a reduction, not the main theorem: (1) and (2) are the paper's fluid block estimate in its
two genuinely open clauses.  No proof holes.
-/
import Swarm.HblkCoarse
import Swarm.HblkScale

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace HblkFinal

open RecordDefect RecordoSupply HblkTwo HblkScale SwarmM4C.FixedConst SwarmM4C.LawBridge
  SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform
  SimJump.RecKernel

/-- The array-side `(defect, record time)` statistic of the canonical actual array. -/
noncomputable def arrQ {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m : ℕ)
    (U : Swarming.Uniform.Array N) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
    fun r => recTimeA p m U r)

/-- **Record-defect tightness on the canonical stopped-record path law, from the two remaining
block clauses.**

`hterm` is the paper's `(recordo)` doubling form; `M7Block.hterm_actual` supplies it
unconditionally at `T = ⌈2B/κ⌉₊+2`, `C₀ = B+T+1`, so it is not an extra assumption of the route.
The genuinely open inputs are `h₁`, `h₂`, `hdef` and the two summability conditions. -/
theorem record_tightness_of_two {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B T C₀ : ℕ) (hB : 1 ≤ B) (hC₀ : B + T + 1 ≤ C₀)
    (hterm : ∀ r L : ℕ, 1 ≤ L →
      ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
        ∃ j : ℕ, GoodT B C₀ T ω r (2 ^ j * L))
    (p₁ p₂ : ℕ → ℝ≥0∞)
    (h₁ : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U | BadTime B T (arrQ p m U) r ℓ} ≤ p₁ ℓ)
    (h₂ : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (arrayMeasure N) {U | BadHalf B (arrQ p m U) r ℓ} ≤ p₂ ℓ)
    (k : ℕ)
    (g : ℕ → ℕ) (hmono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hpowy : ∀ a r : ℕ, 2 ^ (a + 1 + k) ≤ r → a ≤ g r)
    (hdef : ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
      ∀ᶠ r in atTop, dT ω r ≤ 2 ^ g r)
    (hsum_s : (∑' r : ℕ, (p₁ + p₂) (2 ^ g r)) ≠ ⊤)
    (hcert : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * (p₁ + p₂) ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ u : ℕ, (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
        {ω | K < dT ω u} ≤ ε := by
  classical
  -- the two-clause form of `hblk`
  have hblk' : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ (p₁ + p₂) ℓ := by
    intro ℓ hℓ r hr
    have h := hblk_canonical_of_two (N := N) hp0 hp1 hm hN B C₀ T hC₀ p₁ p₂
      (ae_isRecord_recTimeA (N := N) (m := m) hp0 hp1 hm hN)
      (fun l hl rr hrr => by simpa [arrQ] using h₁ l hl rr hrr)
      (fun l hl rr hrr => by simpa [arrQ] using h₂ l hl rr hrr) ℓ hℓ r hr
    simpa [arrQ, Pi.add_apply] using h
  -- the repaired Borel–Cantelli step
  have hS : ∀ ω r L, GoodT B C₀ T ω r L → dT ω r ≤ L →
      dT ω (r + B * L) ≤ L / 2 ∧
        ∀ u, r ≤ u → u ≤ r + B * L → dT ω u ≤ C₀ * L :=
    fun ω r L hG _ => goodT_hS (N := N) (m := m) B C₀ T ω r L hG
  exact tightness_of_eventual_pow
    (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
    B C₀ hB (by omega) (dT (N := N) (m := m)) (GoodT B C₀ T) (p₁ + p₂) g k
    measurable_dT (fun r ℓ => measurableSet_goodT B C₀ T r ℓ) hS hterm hblk'
    hmono hbound hpowy hsum_s hdef hcert ε hε

end HblkFinal


namespace HblkFinal

open RecordDefect RecordoSupply HblkTwo HblkScale SwarmM4C.FixedConst SwarmM4C.LawBridge
  SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform
  SimJump.RecKernel

/-- **The residual inputs of record-path tightness, in full.**

There is a ballistic slope `κ > 0` (from `M7Block.hterm_actual`) such that: for every pair of
profiles `p₁, p₂`, if

* `h₁`: on `{d_r ≤ ℓ}`, the record advance `τ_{r+Bℓ} - τ_r ≤ Tℓ` fails with array probability at
  most `p₁ ℓ`, and
* `h₂`: on `{d_r ≤ ℓ}`, the defect halving `d_{r+Bℓ} ≤ ℓ/2` fails with array probability at most
  `p₂ ℓ`

(both for `r ≥ C₀ ℓ`, at the paper's fixed constants `T = ⌈2B/κ⌉₊+2`, `C₀ = B+T+1`), and if the
concrete scale `g` satisfies the satisfiable arithmetic `hmono`, `hbound`, `hpowy` — for instance
`g r = r.log2 - k` with `2 C₀ ≤ 2^k`, as in `HblkScale.exists_compatible_scale` — and if the
eventual defect bound `hdef` and the two summability conditions hold, then the record defect is
tight along the canonical stopped-record path law.

The only inputs that are not theorems of the repository are `h₁`, `h₂`, `hdef` and the two
summability conditions. -/
theorem record_tightness_of_two_actual {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞),
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (arrayMeasure N) {U | BadTime B (⌈2 * (B : ℝ) / κ⌉₊ + 2) (arrQ p m U) r ℓ} ≤ p₁ ℓ) →
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (arrayMeasure N) {U | BadHalf B (arrQ p m U) r ℓ} ≤ p₂ ℓ) →
      ∀ (k : ℕ) (g : ℕ → ℕ),
        (∀ r r', r ≤ r' → g r ≤ g r') →
        (∀ r, 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ r →
          2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * 2 ^ g r ≤ r) →
        (∀ a r : ℕ, 2 ^ (a + 1 + k) ≤ r → a ≤ g r) →
        (∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
          ∀ᶠ r in atTop, dT ω r ≤ 2 ^ g r) →
        (∑' r : ℕ, (p₁ + p₂) (2 ^ g r)) ≠ ⊤ →
        (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * (p₁ + p₂) ℓ) ≠ ⊤ →
        ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
          (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
            (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
            {ω | K < dT ω u} ≤ ε := by
  classical
  obtain ⟨κ, hκ, hterm⟩ := M7Block.hterm_actual (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ h₁ h₂ k g hmono hbound hpowy hdef hsum_s hcert ε hε => ?_⟩
  exact record_tightness_of_two (N := N) hp0 hp1 hm hN B
    (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) hB le_rfl
    hterm p₁ p₂ h₁ h₂ k g hmono hbound hpowy hdef hsum_s hcert ε hε

end HblkFinal

