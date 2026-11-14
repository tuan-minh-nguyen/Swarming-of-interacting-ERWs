/-
# `htight` for the stopped record kernel from (diam) plus the `(defect, record time)` law

`areas/tightness/ScaleRepairRecord.htight_of_blocks_R` reduces the tightness input of
`recordkernel/InfKernel.exists_invariant_measure_pos_hitKInf` to five analytic premises on the
stopped-record path law `recordTrajT`, among them the fixed-constant `hterm`

  `∀ r L, 1 ≤ L → ∀ᵐ ω, ∃ j, GoodT B C₀ T ω r (2^j L)`.

This file discharges exactly that premise:

* `ActualHterm.hterm_actual_fixed` supplies the block statement for the actual array at the fixed
  constants `T = ⌈2B/κ⌉+2`, `C₀ = B+T+1` (residual: the paper's diameter estimate `(diam)`);
* `LawBridge.hterm_pathlaw_of_array` transfers it to `recordTrajT` along the joint law of the
  `(defect, record time)` sequences.

`htight_of_blocks_R_fixed` below is the composed statement: the `hterm` premise is gone, and the
remaining premises are `hblk` (the paper's fluid block estimate `(blkprob)`), the scale
hypotheses, `hsum`/`pfun`, measurability of the array statistic and the law identification `hlaw`.

Nothing here proves `hlaw`, `hblk`, `(diam)`, tightness, invariant measures, regeneration,
ballisticity or the main theorem.
-/
import Swarm.LawBridge
import Swarm.ScaleRepairRecord

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SwarmM4C

namespace TightChain

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmM4C.FixedConst SwarmM4C.LawBridge

/-- **The tightness input of `exists_invariant_measure_pos_hitKInf`, with the fixed-constant
`hterm` discharged.**  The hypotheses are the array-side record data, the diameter estimate
`(diam)`, measurability of the array statistic, the law identification `hlaw`, and the remaining
analytic premises `hblk`, the scale hypotheses, `pfun` and `hsum`. -/
theorem htight_of_blocks_R_fixed {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) [Nonempty (Fin N)] (_hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (τf : Swarming.Uniform.Array N → ℕ → ℕ)
    (hτf : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (τf U))
    (hmeasSeq : Measurable fun U : Swarming.Uniform.Array N =>
      (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (hlaw : (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
        (μ.map (fun y : RecState N m => (y, 0)))).map (fun ω => (dT ω, tauT ω))
      = (Swarming.Uniform.arrayMeasure N).map
          (fun U => (((fun r => (defect (actX p m U) (τf U) r).toNat) : ℕ → ℕ), τf U)))
    (g : ℕ → ℕ) (R : ℕ → (ℕ → RecState N m × ℕ) → ℕ)
    (hRmeas : ∀ a, Measurable (R a))
    (hRge : ∀ a ω, 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ R a ω)
    (pfun : ℕ → ℝ≥0∞)
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (μ.map (fun y : RecState N m => (y, 0))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r ℓ}) ≤ pfun ℓ)
    (hscale_good : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (μ.map (fun y : RecState N m => (y, 0)))),
      ∀ r, R a ω ≤ r → GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
        (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ g r))
    (hstart : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (μ.map (fun y : RecState N m => (y, 0)))),
      max (2 ^ a) (dT ω (R a ω)) ≤ 2 ^ g (R a ω))
    (hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hscale_bound : ∀ r, 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ r →
      2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * 2 ^ g r ≤ r)
    (hsum : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * pfun ℓ) ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel p (by omega : 1 ≤ m)))^[r] μ (exh N m K)ᶜ ≤ ε := by
  classical
  set ν : Measure (RecState N m × ℕ) := μ.map (fun y : RecState N m => (y, 0)) with hνdef
  haveI : IsProbabilityMeasure ν := by
    rw [hνdef]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hterm : ∀ r L : ℕ, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le
      (by omega : 1 ≤ m) (μ.map (fun y : RecState N m => (y, 0)))), ∃ j : ℕ,
      GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L) := by
    have h := hterm_pathlaw_of_array hp0 hp1 hm N _hN B hB hκ hspeed τf hτf hmeasSeq hdiam
      ν hlaw
    intro r L hL
    exact h r L hL
  exact htight_of_blocks_R p hp0.le hp1.le (by omega : 1 ≤ m) μ B
    (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) hB (by omega) g R hRmeas hRge
    pfun hterm hblk hscale_good hstart hscale_mono hscale_bound hsum

end TightChain

end SwarmM4C


namespace SwarmM4C

namespace TightChain

open RecordDefect RecordoSupply SimJump.RecKernel SwarmRec SwarmM4C.FixedConst SwarmM4C.LawBridge

/-- **The measurability-free form of `htight_of_blocks_R_fixed`.**

Same conclusion, but the law identification is stated at the level of the block events only, so
no measurability of the array statistic is required.  The residual hypotheses are precisely:
the paper's diameter estimate `(diam)`, the block-event exchange rates `hlaw`, the fluid block
estimate `hblk`, the scale hypotheses, `pfun` and `hsum`. -/
theorem htight_of_blocks_R_fixed_ev {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) [Nonempty (Fin N)] (hN : 2 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    {κ : ℝ} (hκ : 0 < κ)
    (hspeed : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N, ∀ᶠ n : ℕ in atTop,
      (κ / 2) * (n : ℝ) ≤ (actX p m U i n : ℝ))
    (τf : Swarming.Uniform.Array N → ℕ → ℕ)
    (hτf : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), IsRecord (actX p m U) (τf U))
    (hdiam : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N),
      Tendsto (fun n : ℕ => spread (actX p m U) n / (n : ℝ)) atTop (𝓝 0))
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (hlaw : ∀ r L : ℕ, 1 ≤ L →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (μ.map (fun y : RecState N m => (y, 0))))
          {ω | ∃ j : ℕ, GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
            (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L)}
        = (Swarming.Uniform.arrayMeasure N)
          {U | ∃ j : ℕ, RecordoSupply.GoodBlock (defect (actX p m U) (τf U)) (τf U)
            (⌈2 * (B : ℝ) / κ⌉₊ + 2) (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L)})
    (g : ℕ → ℕ) (R : ℕ → (ℕ → RecState N m × ℕ) → ℕ)
    (hRmeas : ∀ a, Measurable (R a))
    (hRge : ∀ a ω, 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ R a ω)
    (pfun : ℕ → ℝ≥0∞)
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * ℓ ≤ r →
      (recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
          (μ.map (fun y : RecState N m => (y, 0))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
          (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r ℓ}) ≤ pfun ℓ)
    (hscale_good : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (μ.map (fun y : RecState N m => (y, 0)))),
      ∀ r, R a ω ≤ r → GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1)
        (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ g r))
    (hstart : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le (by omega : 1 ≤ m)
      (μ.map (fun y : RecState N m => (y, 0)))),
      max (2 ^ a) (dT ω (R a ω)) ≤ 2 ^ g (R a ω))
    (hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hscale_bound : ∀ r, 2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) ≤ r →
      2 * (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) * 2 ^ g r ≤ r)
    (hsum : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * pfun ℓ) ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel p (by omega : 1 ≤ m)))^[r] μ (exh N m K)ᶜ ≤ ε := by
  classical
  set ν : Measure (RecState N m × ℕ) := μ.map (fun y : RecState N m => (y, 0)) with hνdef
  haveI : IsProbabilityMeasure ν := by
    rw [hνdef]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hterm : ∀ r L : ℕ, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp0.le hp1.le
      (by omega : 1 ≤ m) (μ.map (fun y : RecState N m => (y, 0)))), ∃ j : ℕ,
      GoodT B (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) ω r (2 ^ j * L) := by
    have h := hterm_pathlaw_of_eventlaw hp0 hp1 hm N hN B hB hκ hspeed τf hτf hdiam ν hlaw
    intro r L hL
    exact h r L hL
  exact htight_of_blocks_R p hp0.le hp1.le (by omega : 1 ≤ m) μ B
    (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) (⌈2 * (B : ℝ) / κ⌉₊ + 2) hB (by omega) g R hRmeas hRge
    pfun hterm hblk hscale_good hstart hscale_mono hscale_bound hsum

end TightChain

end SwarmM4C

