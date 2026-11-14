/-
# The actual record chain as a path law: `htight` is a path-law tail

This file applies the Ionescu–Tulcea path law of `PathLaw.lean` to the repository's stopped
record kernel.  It makes the tightness input

  `htight : ∀ ε > 0, ∃ K, ∀ r, (step hitKKernel)^[r] μ (exh N m K)ᶜ ≤ ε`

of `Swarm/InfKernel.lean` **literally** a path-probability statement:

* `recordTraj p hp hp1 hm μ : Measure (ℕ → RecState N m)` — the law of the whole record chain;
* `recordTraj_eval` — its `r`-th coordinate law is `(step hitKKernel)^[r] μ`;
* `recordTraj_tail` — `(step hitKKernel)^[r] μ (exh N m K)ᶜ = recordTraj … {ω | ω r ∉ exh N m K}`;
* `dmax` / `mem_exh_iff_dmax_le` — the paper's `d_r = max_i d_i` as a coordinate functional, so
  the same tail is `recordTraj … {ω | K < dmax (ω r)}`;
* `htight_iff_pathlaw` — the exact equivalence of the two formulations.

The time-extended chain `hitKKernelT` of `ChainLink.lean` gets the same treatment
(`recordTrajT`, `recordTrajT_tail`, `recordTrajT_fst_tail`), and `τ_r = (ω r).2 - (ω 0).2` is a
coordinate of that path space, which is what the paper's `(recordo)` block inequalities need.

No proof holes.  Imports `PathLaw`.
-/
import Swarm.PathLaw

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### The `d` functional on the record state -/

/-- The paper's `d = max_i d_i` on the compact record state (half-distances). -/
noncomputable def dmax (y : RecState N m) : ℕ :=
  Finset.univ.sup (fun i : Fin N => dist2 y i)

theorem mem_exh_iff_dmax_le (y : RecState N m) (K : ℕ) :
    y ∈ exh N m K ↔ dmax y ≤ K := by
  rw [exh, dmax, Finset.sup_le_iff]
  simp

theorem dmax_lt_iff_not_mem_exh (y : RecState N m) (K : ℕ) :
    K < dmax y ↔ y ∉ exh N m K := by
  rw [mem_exh_iff_dmax_le]
  omega

/-! ### The record chain as a path measure -/

/-- The law of the whole record chain started from `μ`. -/
noncomputable def recordTraj (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) : Measure (ℕ → RecState N m) :=
  letI : IsMarkovKernel (hitKKernel (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  homTraj (hitKKernel p hm) μ

/-- **The `r`-th record state has law `(step hitKKernel)^[r] μ`.** -/
theorem recordTraj_eval (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ] (r : ℕ) :
    (recordTraj p hp hp1 hm μ).map (fun ω : ℕ → RecState N m => ω r)
      = (SwarmKB.step (hitKKernel p hm))^[r] μ := by
  haveI : IsMarkovKernel (hitKKernel (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  exact homTraj_map_eval (hitKKernel p hm) μ r

/-- **The iterated-kernel tail is a path-law tail.** -/
theorem recordTraj_tail (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ] (r K : ℕ) :
    (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ
      = recordTraj p hp hp1 hm μ {ω : ℕ → RecState N m | ω r ∉ exh N m K} := by
  have hmeas : MeasurableSet (exh N m K)ᶜ := (measurableSet_exh N m K).compl
  rw [← recordTraj_eval p hp hp1 hm μ r, Measure.map_apply (measurable_pi_apply r) hmeas]
  rfl

/-- The same tail, written with the scalar functional `dmax`. -/
theorem recordTraj_tail_dmax (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ] (r K : ℕ) :
    (SwarmKB.step (hitKKernel p hm))^[r] μ {y | K < dmax y}
      = recordTraj p hp hp1 hm μ {ω : ℕ → RecState N m | K < dmax (ω r)} := by
  have hset : (exh N m K)ᶜ = {y : RecState N m | K < dmax y} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact (dmax_lt_iff_not_mem_exh y K).symm
  have hset2 : {ω : ℕ → RecState N m | ω r ∉ exh N m K}
      = {ω : ℕ → RecState N m | K < dmax (ω r)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact (dmax_lt_iff_not_mem_exh (ω r) K).symm
  rw [← hset, recordTraj_tail, hset2]

/-- **`htight` restated as a path-law tail condition.**  This is the same proposition as the
`htight` hypothesis of `exists_invariant_measure_pos_hitKInf`, transported to the trajectory
space of the record chain. -/
theorem htight_iff_pathlaw (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ] :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
        (SwarmKB.step (hitKKernel p hm))^[r] μ (exh N m K)ᶜ ≤ ε)
      ↔ (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
        recordTraj p hp hp1 hm μ {ω : ℕ → RecState N m | ω r ∉ exh N m K} ≤ ε) := by
  simp only [recordTraj_tail p hp hp1 hm μ]

/-! ### The time-extended chain as a path measure -/

/-- The law of the whole time-extended record chain started from `ν`. -/
noncomputable def recordTrajT (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) : Measure (ℕ → RecState N m × ℕ) :=
  letI : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT (N := N) (m := m) p hp hp1 hm
  homTraj (hitKKernelT p hm) ν

theorem recordTrajT_eval (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] (r : ℕ) :
    (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => ω r)
      = (SwarmKB.step (hitKKernelT p hm))^[r] ν := by
  haveI : IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
    isMarkovKernel_hitKKernelT (N := N) (m := m) p hp hp1 hm
  exact homTraj_map_eval (hitKKernelT p hm) ν r

/-- **The `d`-tail of the extended chain is the `d`-tail of the record chain**: extending the
state by the record time does not change the quantity `htight` bounds. -/
theorem recordTrajT_tail (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν] (r K : ℕ) :
    recordTrajT p hp hp1 hm ν {ω : ℕ → RecState N m × ℕ | (ω r).1 ∈ exh N m K}ᶜ
      = (SwarmKB.step (hitKKernel p hm))^[r] (ν.map Prod.fst) (exh N m K)ᶜ := by
  have hmeas : MeasurableSet (Prod.fst ⁻¹' (exh N m K)ᶜ : Set (RecState N m × ℕ)) :=
    (measurableSet_exh N m K).compl.preimage measurable_fst
  have hmap : recordTrajT p hp hp1 hm ν {ω : ℕ → RecState N m × ℕ | (ω r).1 ∈ exh N m K}ᶜ
      = (recordTrajT p hp hp1 hm ν).map (fun ω : ℕ → RecState N m × ℕ => ω r)
          (Prod.fst ⁻¹' (exh N m K)ᶜ) := by
    rw [Measure.map_apply (measurable_pi_apply r) hmeas]
    rfl
  rw [hmap, recordTrajT_eval p hp hp1 hm ν r, step_iterate_fst_apply p hm ν r (measurableSet_exh N m K).compl]

end RecKernel
end SimJump
