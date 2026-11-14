/-
# `hdef`: the eventual defect bound at the repaired logarithmic scale

`HblkFinal.record_tightness_of_two` (m3, coordinator-reviewed) needs four residual inputs, one of
which is

  `hdef : ∀ᵐ ω ∂(recordTrajT …), ∀ᶠ r, dT ω r ≤ 2 ^ (g r)`

for a dyadic scale `g` satisfying the *satisfiable* arithmetic `hmono`, `hbound`, `hpowy`
(`HblkScale`).  This file **proves `hdef`** at the concrete repaired scale
`g r = r.log2 - k`, i.e. it reduces `HblkScale.PCtxR.of_eventual_pow`'s last analytic input to
nothing.

The argument is the paper's: `(recordo)` says `d_r / r → 0`, and `2 ^ (r.log2 - k) ≥ r / 2 ^ (k+1)`,
so `d_r ≤ 2 ^ (r.log2 - k)` eventually.  Both halves are transported:

* **array side** — `RecordoSupply.recordo_actual` (the proved `(recordo)` with the ballistic
  constant) turns `(diam)` (`M7Block.diam_actual_recordo`) plus `IsRecord`
  (`SwarmRecordMeas.Actual.ae_isRecord_recTimeA`) into `d_r / r → 0` almost surely, and the scale
  arithmetic turns that into `d_r ≤ 2 ^ (g r)` eventually;
* **path side** — `M7Block.jointLawIdentity_actual` identifies the law of `(dT, τ)` under the
  canonical stopped-record path law with the law of the array's own `(defect, recTimeA)`, and the
  eventual bound is a *measurable* event of that pair, so it transfers (`hdef_of_jointLaw`).

Note that no identification of `dT` with the array defect is needed — nor assumed: the transport is
purely event-level, which is why the factor `2` in `dT = 2 * dmax` (the compact record state stores
half-distances) never has to be reconciled with the raw integer defect.

Main declarations:

* `lt_pow_log2_succ`, `le_pow_mul_g` — `r ≤ 2 ^ (k+1) * 2 ^ (r.log2 - k)`, the scale arithmetic.
* `array_defect_div_tendsto`, `array_eventually_toNat_le` — the array side.
* `measurableSet_eventually_coord_le`, `hdef_of_jointLaw` — the transfer.
* `hdef_actual_pow` — **`hdef` at `g r = r.log2 - k`, unconditionally.**
* `record_tightness_of_two_actual_hdef_free` — `HblkFinal.record_tightness_of_two_actual` with
  `hdef` discharged: the remaining inputs are only the two block clauses `h₁`, `h₂` and the two
  summability conditions.

No proof holes, no new axioms: only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Swarm.HblkFinal

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace HdefDefect

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec
  SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw

/-! ### The repaired logarithmic scale `g r = r.log2 - k` -/

/-- The repaired logarithmic scale of the coordinator's target: `g r = r.log2 - k`, i.e. the
exponent of the largest power of two not exceeding `r / 2 ^ k`. -/
def g (k r : ℕ) : ℕ := r.log2 - k

/-- `HdefDefect.g` is the `HblkScale` scale of the same name. -/
theorem g_eq_hblkScale (k r : ℕ) : g k r = HblkScale.g k r := rfl

/-- **`r < 2 ^ (r.log2 + 1)`.**  `Nat.le_log2` twice: `r.log2 + 1 ≤ r.log2` would force
`2 ^ (r.log2 + 1) ≤ r`. -/
theorem lt_pow_log2_succ (r : ℕ) : r < 2 ^ (r.log2 + 1) := by
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    norm_num
  · by_contra hcon
    have h1 : 2 ^ (r.log2 + 1) ≤ r := by omega
    have h2 := (Nat.le_log2 (n := r) (k := r.log2 + 1) (by omega : r ≠ 0)).mpr h1
    omega

/-- **The scale arithmetic**: `r ≤ 2 ^ (k+1) * 2 ^ (r.log2 - k)`, i.e.
`2 ^ (g r) ≥ r / 2 ^ (k+1)`. -/
theorem le_pow_mul_g (k r : ℕ) : r ≤ 2 ^ (k + 1) * 2 ^ g k r := by
  have hlt := lt_pow_log2_succ r
  rcases Nat.lt_or_ge r.log2 k with hk | hk
  · have hg : g k r = 0 := by
      rw [g, Nat.sub_eq_zero_of_le (le_of_lt hk)]
    rw [hg, pow_zero, Nat.mul_one]
    exact le_trans (le_of_lt hlt) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have hg : g k r = r.log2 - k := rfl
    rw [hg, ← pow_add]
    have hidx : k + 1 + (r.log2 - k) = r.log2 + 1 := by omega
    rw [hidx]
    exact le_of_lt hlt

section Array

variable {N : ℕ} [Nonempty (Fin N)]

/-- **`(recordo)` for the canonical array, almost surely.**  The proved `(diam)`
(`M7Block.diam_actual_recordo`), the canonical record times
(`SwarmRecordMeas.Actual.ae_isRecord_recTimeA`) and the proved `(recordo)` with its ballistic
constant (`RecordoSupply.recordo_actual`) give `d_r / r → 0` along `recTimeA` at the canonical
array law. -/
theorem array_defect_div_tendsto {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun r : ℕ => (defect (actX p m U) (recTimeA p m U) r : ℝ) / (r : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨κ, hκ, h⟩ := RecordoSupply.recordo_actual (p := p) hp0 hp1 (m := m) hm
  filter_upwards [h N hN, ae_isRecord_recTimeA (N := N) (p := p) (m := m) hp0 hp1 hm hN,
    M7Block.diam_actual_recordo (N := N) hp0 hp1 hm hN] with U hU hrec hsp
  exact hU (recTimeA p m U) hrec hsp

/-- **The array-side eventual defect bound at the repaired scale.**  From `d_r / r → 0` with the
explicit `ε = 2 ^ (-(k+1))` and the scale arithmetic `r ≤ 2 ^ (k+1) * 2 ^ (g r)`. -/
theorem array_eventually_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (k : ℕ) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∀ᶠ r : ℕ in atTop,
        defect (actX p m U) (recTimeA p m U) r ≤ ((2 ^ g k r : ℕ) : ℤ) := by
  filter_upwards [array_defect_div_tendsto (N := N) hp0 hp1 hm hN] with U hlim
  have hε : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hlim (1 / 2 ^ (k + 1)) hε
  filter_upwards [eventually_ge_atTop (max R 1)] with r hr
  set d : ℤ := defect (actX p m U) (recTimeA p m U) r with hd
  have hRr : R ≤ r := le_trans (le_max_left _ _) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hdist := hR r hRr
  rw [Real.dist_eq, sub_zero] at hdist
  have habs : (d : ℝ) / (r : ℝ) < 1 / 2 ^ (k + 1) := (abs_lt.1 hdist).2
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  rw [div_lt_iff₀ hrpos] at habs
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hstep : (d : ℝ) * 2 ^ (k + 1) < (1 / (2 : ℝ) ^ (k + 1) * (r : ℝ)) * 2 ^ (k + 1) :=
    mul_lt_mul_of_pos_right habs hp2
  have hcancel : (1 / (2 : ℝ) ^ (k + 1) * (r : ℝ)) * 2 ^ (k + 1) = (r : ℝ) := by
    field_simp
  rw [hcancel] at hstep
  have hZ : d * (2 : ℤ) ^ (k + 1) ≤ (r : ℤ) := by
    have h' : ((d * (2 : ℤ) ^ (k + 1) : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hleZ : (r : ℤ) ≤ (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ g k r := by
    have h' : ((r : ℕ) : ℤ) ≤ ((2 ^ (k + 1) * 2 ^ g k r : ℕ) : ℤ) := by
      exact_mod_cast le_pow_mul_g k r
    push_cast at h' ⊢
    exact h'
  have hc : (0 : ℤ) < (2 : ℤ) ^ (k + 1) := by positivity
  have hfin : (2 : ℤ) ^ (k + 1) * d ≤ (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ g k r := by
    calc (2 : ℤ) ^ (k + 1) * d = d * (2 : ℤ) ^ (k + 1) := by ring
      _ ≤ (r : ℤ) := hZ
      _ ≤ (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ g k r := hleZ
  exact le_of_mul_le_mul_left hfin hc

/-- The same bound in the `Nat.toNat` form used by the joint-law statistic. -/
theorem array_eventually_toNat_le {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (k : ℕ) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      ∀ᶠ r : ℕ in atTop,
        (defect (actX p m U) (recTimeA p m U) r).toNat ≤ 2 ^ g k r := by
  filter_upwards [array_eventually_le (N := N) hp0 hp1 hm hN k,
    ae_isRecord_recTimeA (N := N) (p := p) (m := m) hp0 hp1 hm hN] with U hle hrec
  filter_upwards [hle] with r hr
  have h1 : (((defect (actX p m U) (recTimeA p m U) r).toNat : ℕ) : ℤ) ≤ ((2 ^ g k r : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (defect_nonneg hrec r)]
    exact hr
  exact_mod_cast h1

end Array

section Transfer

/-- **The eventual coordinate bound is a measurable event of the `(defect, record time)`
sequence.**  `∀ᶠ r, Q.1 r ≤ F r` is the countable union over `R` of the countable intersections
over `r ≥ R`. -/
theorem measurableSet_eventually_coord_le (F : ℕ → ℕ) :
    MeasurableSet {Q : (ℕ → ℕ) × (ℕ → ℕ) | ∀ᶠ r : ℕ in atTop, Q.1 r ≤ F r} := by
  have hcoord : ∀ r : ℕ, Measurable fun Q : (ℕ → ℕ) × (ℕ → ℕ) => Q.1 r :=
    fun r => (measurable_pi_apply r).comp measurable_fst
  have heq : {Q : (ℕ → ℕ) × (ℕ → ℕ) | ∀ᶠ r : ℕ in atTop, Q.1 r ≤ F r}
      = ⋃ R : ℕ, ⋂ r : ℕ, ⋂ (_ : R ≤ r), {Q : (ℕ → ℕ) × (ℕ → ℕ) | Q.1 r ≤ F r} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Filter.eventually_atTop, Set.mem_iUnion, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iUnion fun R => MeasurableSet.iInter fun r =>
    MeasurableSet.iInter fun _ => measurableSet_le (hcoord r) measurable_const

/-- **Event-level transfer of an eventual coordinate bound along an identity of laws.**  If the
sequences `q` (on `α`) and `s` (on `β`) have the same law, then an almost-sure eventual bound for
the first coordinate of `q` transfers to `s`. -/
theorem eventually_coord_le_of_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {s : β → (ℕ → ℕ) × (ℕ → ℕ)}
    {q : α → (ℕ → ℕ) × (ℕ → ℕ)} (hs : Measurable s) (hq : Measurable q)
    (hlaw : ν.map s = μ.map q) (F : ℕ → ℕ)
    (h : ∀ᵐ a ∂μ, ∀ᶠ r : ℕ in atTop, (q a).1 r ≤ F r) :
    ∀ᵐ b ∂ν, ∀ᶠ r : ℕ in atTop, (s b).1 r ≤ F r := by
  set S : Set ((ℕ → ℕ) × (ℕ → ℕ)) := {Q | ∀ᶠ r : ℕ in atTop, Q.1 r ≤ F r} with hS
  have hSmeas : MeasurableSet S := measurableSet_eventually_coord_le F
  rw [ae_iff] at h ⊢
  have hpre : {b : β | ¬ ∀ᶠ r : ℕ in atTop, (s b).1 r ≤ F r} = s ⁻¹' Sᶜ := rfl
  rw [hpre, ← Measure.map_apply hs hSmeas.compl, hlaw, Measure.map_apply hq hSmeas.compl]
  exact h

end Transfer

section Path

variable {N : ℕ} [Nonempty (Fin N)]

/-- **`hdef` at the repaired logarithmic scale, unconditionally.**

At the canonical stopped-record path law and for every `k`, the record defect `dT` is eventually
below `2 ^ (r.log2 - k)`.  This is one of the four residual inputs of
`HblkFinal.record_tightness_of_two`; nothing is assumed here. -/
theorem hdef_actual_pow {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) (k : ℕ) :
    ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
      ∀ᶠ r : ℕ in atTop, dT ω r ≤ 2 ^ g k r := by
  have harr := array_eventually_toNat_le (N := N) hp0 hp1 hm hN k
  have hlaw := M7Block.jointLawIdentity_actual (N := N) hp0 hp1 hm hN
  exact eventually_coord_le_of_map_eq (measurable_dT.prodMk measurable_tauT)
    (measurable_recordStat (N := N) p m) hlaw (fun r => 2 ^ g k r) harr

/-- The same statement in the `HblkScale.g` spelling, ready for `HblkFinal`. -/
theorem hdef_actual_hblkScale {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (hN : 2 ≤ N) (k : ℕ) :
    ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ)))),
      ∀ᶠ r : ℕ in atTop, dT ω r ≤ 2 ^ HblkScale.g k r := by
  have h := hdef_actual_pow (N := N) hp0 hp1 hm hN k
  simpa [g_eq_hblkScale] using h

end Path


section Application

/-- **Record-path tightness with `hdef` discharged.**

This is `HblkFinal.record_tightness_of_two_actual` with the eventual defect bound `hdef` replaced
by its proof `hdef_actual_hblkScale` at the explicit repaired scale `g r = r.log2 - k`, where `k`
only has to satisfy `2 C₀ ≤ 2 ^ k` (`C₀ = B + ⌈2B/κ⌉₊ + 3`).

The remaining inputs are exactly the two block clauses `h₁`, `h₂` and the two summability
conditions; `hterm`, `hlaw` (`M7Block.jointLawIdentity_actual`), `(diam)`
(`M7Block.diam_actual_recordo`), `IsRecord`, and now `hdef`, are theorems. -/
theorem record_tightness_of_two_actual_hdef_free {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (p₁ p₂ : ℕ → ℝ≥0∞),
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U | HblkTwo.BadTime B (⌈2 * (B : ℝ) / κ⌉₊ + 2) (HblkFinal.arrQ p m U) r ℓ} ≤ p₁ ℓ) →
      (∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
        (Swarming.Uniform.arrayMeasure N)
          {U | HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ} ≤ p₂ ℓ) →
      ∀ (k : ℕ), 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ 2 ^ k →
        (∑' r : ℕ, (p₁ + p₂) (2 ^ g k r)) ≠ ⊤ →
        (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * (p₁ + p₂) ℓ) ≠ ⊤ →
        ∀ (ε : ℝ≥0∞), 0 < ε → ∃ K : ℕ, ∀ u : ℕ,
          (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
            (Measure.dirac (zeroState (N := N) (m := m) (by omega), (0 : ℕ))))
            {ω | K < dT ω u} ≤ ε := by
  obtain ⟨κ, hκ, hterm⟩ := M7Block.hterm_actual (N := N) hp0 hp1 hm hN B hB
  refine ⟨κ, hκ, fun p₁ p₂ h₁ h₂ k hk hsum_s hcert ε hε => ?_⟩
  refine HblkFinal.record_tightness_of_two (N := N) hp0 hp1 hm hN B
    (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) hB le_rfl hterm p₁ p₂
    h₁ h₂ k (HblkScale.g k) (fun r r' h => HblkScale.g_mono k h)
    ?_ (fun a r h => HblkScale.g_pow_le k h) ?_ ?_ hcert ε hε
  · intro r hr
    exact HblkScale.g_bound k _ (by omega) hk hr
  · exact hdef_actual_hblkScale (N := N) hp0 hp1 hm hN k
  · simpa [g_eq_hblkScale] using hsum_s

end Application

end HdefDefect


