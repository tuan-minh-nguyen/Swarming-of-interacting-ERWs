/-
# The repaired scale interface on the actual record path law

`Swarm/ProbCtxRecord.lean` inhabits the `ProbCtx` interface on the Ionescu–Tulcea
record path law `recordTrajT`, with the paper's three block inequalities as the explicit
relation `GoodT`, so that only `hterm`, `hR` and `hblk` remain as analytic hypotheses — and `hR`
(the all-level conclusion of Borel–Cantelli) is the one the paper does *not* get from one moving
dyadic level.

This file does the same for the repaired interface `PCtxR` of `ScaleRepair.lean`: the fields
`hd`, `hdR`, `hg`, `hS`, `hRge` are proved from the record chain, and the residual analytic
inputs become

* `hterm` (the paper's `(recordo)` existence half),
* `hblk` (the paper's `(blkprob)`),
* `hscale_good` (one good level per index, the actual Borel–Cantelli conclusion),
* `hstart` (the per-level transient),
* `hscale_mono`, `hscale_bound` (deterministic arithmetic of the chosen scale).

`hR` is not needed.  As in `ProbCtxRecord.lean`, nothing unconditional is asserted: `htight`
for the stopped record kernel follows from those path probabilities plus the summability of
`(4Bℓ+1) p ℓ`, and the initial law is arbitrary.
-/
import Swarm.ProbCtxRecord
import Swarm.ScaleRepair

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

set_option linter.style.haveILetI false

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-- **`PCtxR` on the actual record path law.**  Same construction as `probCtxT`, with the
level-dependent start `R` and the scale `g` of the repaired interface. -/
noncomputable def probCtxRT (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (B C₀ T : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (g : ℕ → ℕ) (R : ℕ → (ℕ → RecState N m × ℕ) → ℕ)
    (hRmeas : ∀ a, Measurable (R a))
    (hRge : ∀ a ω, 2 * C₀ ≤ R a ω)
    (pfun : ℕ → ℝ≥0∞)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν),
      ∃ j, GoodT B C₀ T ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp hp1 hm ν)
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ pfun ℓ)
    (hscale_good : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν),
      ∀ r, R a ω ≤ r → GoodT B C₀ T ω r (2 ^ g r))
    (hstart : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp hp1 hm ν),
      max (2 ^ a) (dT ω (R a ω)) ≤ 2 ^ g (R a ω))
    (hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hscale_bound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r) :
    SwarmM4.PCtxR (ℕ → RecState N m × ℕ) where
  μ := recordTrajT p hp hp1 hm ν
  hprob := instIsProbabilityMeasure_recordTrajT p hp hp1 hm ν
  B := B
  C₀ := C₀
  d := dT
  Good := GoodT B C₀ T
  R := R
  p := pfun
  g := g
  hB := hB
  hC₀ := hC₀
  hd := measurable_dT
  hdR := fun a => measurable_nat_eval_comp measurable_dT (hRmeas a)
  hg := fun r ℓ => measurableSet_goodT B C₀ T r ℓ
  hRmeas := hRmeas
  hRge := hRge
  hS := fun ω r L hG _ => goodT_hS B C₀ T ω r L hG
  hterm := hterm
  hblk := hblk
  hscale_mono := hscale_mono
  hscale_bound := hscale_bound
  hscale_good := hscale_good
  hstart := hstart

/-- **Conditional reduction of `htight` to the paper's analytic inputs, without the all-level
`hR`.**  The hypotheses are the path probabilities of the actual record chain; the conclusion is
the tightness input of `exists_invariant_measure_pos_hitKInf`.  This is
`ProbCtxRecord.htight_of_blocks` with `hR` replaced by the scale hypotheses. -/
theorem htight_of_blocks_R (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (B C₀ T : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (g : ℕ → ℕ) (R : ℕ → (ℕ → RecState N m × ℕ) → ℕ)
    (hRmeas : ∀ a, Measurable (R a))
    (hRge : ∀ a ω, 2 * C₀ ≤ R a ω)
    (pfun : ℕ → ℝ≥0∞)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂(recordTrajT p hp hp1 hm
      (μ.map (fun y : RecState N m => (y, 0)))), ∃ j, GoodT B C₀ T ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      (recordTrajT p hp hp1 hm (μ.map (fun y : RecState N m => (y, 0))))
        ({ω | dT ω r ≤ ℓ} ∩ {ω | ¬ GoodT B C₀ T ω r ℓ}) ≤ pfun ℓ)
    (hscale_good : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp hp1 hm
      (μ.map (fun y : RecState N m => (y, 0)))),
      ∀ r, R a ω ≤ r → GoodT B C₀ T ω r (2 ^ g r))
    (hstart : ∀ a, ∀ᵐ ω ∂(recordTrajT p hp hp1 hm
      (μ.map (fun y : RecState N m => (y, 0)))),
      max (2 ^ a) (dT ω (R a ω)) ≤ 2 ^ g (R a ω))
    (hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hscale_bound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hsum : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * pfun ℓ) ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ ≤ ε := by
  classical
  set ν : Measure (RecState N m × ℕ) := μ.map (fun y => (y, 0)) with hνdef
  haveI : IsProbabilityMeasure ν := by
    rw [hνdef]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let c := probCtxRT p hp hp1 hm ν B C₀ T hB hC₀ g R hRmeas hRge pfun hterm hblk
    hscale_good hstart hscale_mono hscale_bound
  have hfst : ν.map Prod.fst = μ := by
    rw [hνdef, Measure.map_map measurable_fst
      (by fun_prop : Measurable fun y : RecState N m => (y, (0 : ℕ)))]
    rw [show (Prod.fst ∘ (fun y : RecState N m => (y, (0 : ℕ)))) = id from rfl, Measure.map_id]
  intro ε hε
  obtain ⟨K, hK⟩ := c.tightness (by simpa [c, probCtxRT, SwarmM4.PCtxR.w] using hsum) ε hε
  refine ⟨K, fun r => ?_⟩
  have h1 : (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r}
      = (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ := by
    have hset : {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r}
        = {ω | (ω r).1 ∈ exh N m K}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, dT]
      rw [show 2 * K < 2 * dmax ((ω r).1) ↔ K < dmax ((ω r).1) by omega]
      exact dmax_lt_iff_not_mem_exh ((ω r).1) K
    rw [hset, recordTrajT_tail p hp hp1 hm ν r K, hfst]
  calc (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ
      = (recordTrajT p hp hp1 hm ν) {ω : ℕ → RecState N m × ℕ | 2 * K < dT ω r} := h1.symm
    _ = c.μ {ω | 2 * K < c.d ω r} := rfl
    _ ≤ c.μ {ω | K < c.d ω r} := measure_mono fun ω hω => by
      change K < dT ω r
      change 2 * K < dT ω r at hω
      omega
    _ ≤ ε := hK r

end RecKernel
end SimJump
