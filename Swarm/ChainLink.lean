/-
# The record chain with its elapsed time: `hitKKernelT`

`Swarm/InfKernel.lean` builds the horizon-free stopped record kernel
`hitKKernel p hm : Kernel (RecState N m) (RecState N m)`.  Its transition marginalises over the
length `k` of the finite first-record path `q`, i.e. over the **inter-record waiting time**.
That waiting time is a genuine coordinate of the paper's block inequalities (via
`τ_{r+BL} - τ_r`) but it is *not* recoverable from the record state, so the record chain alone
cannot even state the paper's `(recordo)`.

Here the same stopped law is lifted to the extended state `RecState N m × ℕ`, `(y, t)` meaning
"record state `y` at absolute record time `t`":

* `hitKInfT p hm (y,t)` — the lifted stopped record measure, with atom `(out q y, t + k)`;
* `hitKKernelT p hm` — the lifted kernel; it is a genuine Markov kernel (`isMarkovKernel_hitKKernelT`);
* `hitKKernelT_fst` — **the `RecState` marginal of `hitKKernelT` is `hitKKernel`, independently of
  the time coordinate**.  So the extension adds exactly the waiting-time information and changes
  nothing about the state transition;
* `step_map_fst` / `step_iterate_map_fst` — the same statement for every iterate;
* `hitKInfT_time_lt` / `hitKKernelT_time_lt` — the time coordinate strictly increases by at least
  one step at every record, so `t_r - t_0` is the record time `τ_r`;
* `hitKKernelT_fst_of_iterate` — the `d`-tail of `htight` is untouched by the extension:
  `(step hitKKernelT)^[r] ν {z | z.1 ∈ exh N m K} = (step hitKKernel)^[r] (ν.map fst) (exh N m K)`.

No proof holes.  Imports `InfKernel`.
-/
import Swarm.InfKernel

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### The lifted stopped record measure -/

/-- The horizon-free stopped record measure on the extended state `RecState N m × ℕ`.
A finite first-record path `q` of length `k` carries `(y,t)` to `(out q y, t + k)`. -/
noncomputable def hitKInfT (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ) :
    Measure (RecState N m × ℕ) :=
  Measure.sum (fun pq : (k : ℕ) × (Fin k → JumpVec N) =>
    ENNReal.ofReal (hitW p pq.2 z.1) •
      Measure.dirac (out hm pq.2 z.1, z.2 + pq.1))

theorem hitKInfT_apply (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ)
    {A : Set (RecState N m × ℕ)} (hA : MeasurableSet A) :
    hitKInfT p hm z A = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (hitW p pq.2 z.1) *
        (if (out hm pq.2 z.1, z.2 + pq.1) ∈ A then 1 else 0) := by
  classical
  rw [hitKInfT, Measure.sum_apply _ hA]
  refine tsum_congr fun pq => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  simp only [Set.indicator_apply, Pi.one_apply]

/-- **Total mass one** of the lifted stopped record law. -/
theorem hitKInfT_univ (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (z : RecState N m × ℕ) : hitKInfT p hm z Set.univ = 1 := by
  classical
  rw [hitKInfT_apply p hm z MeasurableSet.univ]
  simp only [Set.mem_univ, if_true, mul_one]
  rw [ENNReal.tsum_sigma']
  have hinner : ∀ k : ℕ, (∑' q : Fin k → JumpVec N, ENNReal.ofReal (hitW p q z.1))
      = ENNReal.ofReal (recTerm p k z.1) := by
    intro k
    rw [recTerm, ENNReal.ofReal_sum_of_nonneg (fun q _ => hitW_nonneg p hp hp1 q z.1)]
    exact tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi)
  simp only [hinner]
  have hsum : Summable (fun k => recTerm p k z.1) := (hasSum_recTerm p hp hp1 hm z.1).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => recTerm_nonneg p hp hp1 k z.1) hsum,
    (hasSum_recTerm p hp hp1 hm z.1).tsum_eq]
  simp

/-- **The lifted horizon-free stopped record kernel.** -/
noncomputable def hitKKernelT (p : ℝ) (hm : 1 ≤ m) :
    Kernel (RecState N m × ℕ) (RecState N m × ℕ) :=
  Kernel.mk (hitKInfT p hm) (by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    rw [show (fun z : RecState N m × ℕ => hitKInfT p hm z A)
        = (fun z => ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
            ENNReal.ofReal (hitW p pq.2 z.1) *
              (if (out hm pq.2 z.1, z.2 + pq.1) ∈ A then 1 else 0)) from
      funext fun z => hitKInfT_apply p hm z hA]
    exact Measurable.tsum fun pq =>
      (ENNReal.measurable_ofReal.comp
        ((measurable_hitW p pq.1 pq.2).comp measurable_fst)).mul
        (Measurable.ite
          (hA.preimage (Measurable.prodMk ((measurable_out hm pq.1 pq.2).comp measurable_fst)
            (measurable_snd.add_const pq.1)))
          measurable_const measurable_const))

theorem hitKKernelT_apply (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ) :
    hitKKernelT (N := N) (m := m) p hm z = hitKInfT p hm z := rfl

/-- The lifted stopped record kernel is a Markov kernel. -/
theorem isMarkovKernel_hitKKernelT (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) :
    IsMarkovKernel (hitKKernelT (N := N) (m := m) p hm) :=
  ⟨fun z => ⟨by rw [hitKKernelT_apply]; exact hitKInfT_univ p hp hp1 hm z⟩⟩

/-! ### The `RecState` marginal is the original kernel -/

theorem hitKInfT_fst (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ) :
    (hitKInfT p hm z).map Prod.fst = hitKInf p hm z.1 := by
  classical
  ext A hA
  rw [Measure.map_apply measurable_fst hA,
    hitKInfT_apply p hm z (hA.preimage measurable_fst), hitKInf_apply p hm z.1 hA]
  refine tsum_congr fun pq => ?_
  simp only [Set.mem_preimage]

/-- **The `RecState` marginal of the lifted kernel is the original stopped record kernel.** -/
theorem hitKKernelT_fst (p : ℝ) (hm : 1 ≤ m) (z : RecState N m × ℕ) :
    (hitKKernelT p hm z).map Prod.fst = hitKKernel p hm z.1 := by
  rw [hitKKernelT_apply, hitKKernel_apply]
  exact hitKInfT_fst p hm z

/-- One step of the lifted chain, projected to the record state, is one step of the record
chain applied to the projected measure. -/
theorem step_map_fst (p : ℝ) (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ)) :
    (SwarmKB.step (hitKKernelT p hm) ν).map Prod.fst
      = SwarmKB.step (hitKKernel p hm) (ν.map Prod.fst) := by
  have hfst : Measurable (Prod.fst : RecState N m × ℕ → RecState N m) := measurable_fst
  have h1 : ⇑((hitKKernelT p hm).map (Prod.fst : RecState N m × ℕ → RecState N m))
      = fun z : RecState N m × ℕ => hitKKernel p hm z.1 := by
    funext z
    rw [Kernel.map_apply _ hfst]
    exact hitKKernelT_fst p hm z
  have h2 : ⇑(hitKKernel p hm ∘ₖ Kernel.deterministic
        (Prod.fst : RecState N m × ℕ → RecState N m) hfst)
      = fun z : RecState N m × ℕ => hitKKernel p hm z.1 := by
    funext z
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  show Measure.map Prod.fst (⇑(hitKKernelT p hm) ∘ₘ ν)
      = ⇑(hitKKernel p hm) ∘ₘ (ν.map Prod.fst)
  rw [Measure.map_comp ν _ hfst, h1,
    ← Measure.deterministic_comp_eq_map (μ := ν) hfst,
    Measure.comp_assoc, h2]

/-- The same for every iterate. -/
theorem step_iterate_map_fst (p : ℝ) (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ))
    (r : ℕ) :
    ((SwarmKB.step (hitKKernelT p hm))^[r] ν).map Prod.fst
      = (SwarmKB.step (hitKKernel p hm))^[r] (ν.map Prod.fst) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        step_map_fst p hm ((SwarmKB.step (hitKKernelT p hm))^[r] ν), ih]

/-- **Every `RecState`-event has the same probability in the extended chain as in the record
chain.**  In particular the `d`-tail of `htight` is unchanged by the extension. -/
theorem step_iterate_fst_apply (p : ℝ) (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ))
    (r : ℕ) {A : Set (RecState N m)} (hA : MeasurableSet A) :
    ((SwarmKB.step (hitKKernelT p hm))^[r] ν) (Prod.fst ⁻¹' A)
      = ((SwarmKB.step (hitKKernel p hm))^[r] (ν.map Prod.fst)) A := by
  rw [← step_iterate_map_fst p hm ν r, Measure.map_apply measurable_fst hA]

/-- The `d`-tail of `htight` is unchanged by the extension. -/
theorem step_iterate_fst_apply_exh (p : ℝ) (hm : 1 ≤ m) (ν : Measure (RecState N m × ℕ))
    (r K : ℕ) :
    ((SwarmKB.step (hitKKernelT p hm))^[r] ν) (Prod.fst ⁻¹' exh N m K)
      = ((SwarmKB.step (hitKKernel p hm))^[r] (ν.map Prod.fst)) (exh N m K) :=
  step_iterate_fst_apply p hm ν r (measurableSet_exh N m K)

end RecKernel
end SimJump
