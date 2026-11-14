/-
# The horizon-free stopped record kernel is a Markov kernel

`Swarm/StoppedKernel.lean` builds the stopped record law only at finite horizon `L`
and records explicitly that "these are not Markov kernels yet: total mass one has not been
proved".  `MassOne.lean` proves that the horizon masses tend to `1`.  Here the horizon-free
object is built as the countable sum over all finite first-record paths,

  `hitKInf p hm y = ∑' (k, q), ofReal (hitW p q y) • δ_{out k q y}`,

its total mass is proved to be one, it is packaged as a `Kernel`, and the force bound
`hitK_srSet_ge` transfers to it.  So the paper's `P(y, ·)` of §3.1 is now a genuine probability
kernel, and the `hforce` input of `SwarmRec.exists_invariant_measure_pos_srSet` holds for it.
-/
import Swarm.MassOne

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### The countable-sum stopped record measure -/

/-- The horizon-free stopped record measure: the countable sum over every finite first-record
path of its weight times the Dirac mass at the normalized record state. -/
noncomputable def hitKInf (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) : Measure (RecState N m) :=
  Measure.sum (fun pq : (k : ℕ) × (Fin k → JumpVec N) =>
    ENNReal.ofReal (hitW p pq.2 y) • Measure.dirac (out hm pq.2 y))

theorem hitKInf_apply (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) {A : Set (RecState N m)}
    (hA : MeasurableSet A) :
    hitKInf p hm y A = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (hitW p pq.2 y) * (if out hm pq.2 y ∈ A then 1 else 0) := by
  classical
  rw [hitKInf, Measure.sum_apply _ hA]
  refine tsum_congr fun pq => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  simp only [Set.indicator_apply, Pi.one_apply]

/-- **Total mass one**: the horizon-free stopped record law is a probability measure. -/
theorem hitKInf_univ (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (y : RecState N m) : hitKInf p hm y Set.univ = 1 := by
  classical
  rw [hitKInf_apply p hm y MeasurableSet.univ]
  simp only [Set.mem_univ, if_true, mul_one]
  rw [ENNReal.tsum_sigma']
  have hinner : ∀ k : ℕ, (∑' q : Fin k → JumpVec N, ENNReal.ofReal (hitW p q y))
      = ENNReal.ofReal (recTerm p k y) := by
    intro k
    rw [recTerm, ENNReal.ofReal_sum_of_nonneg (fun q _ => hitW_nonneg p hp hp1 q y)]
    exact tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi)
  simp only [hinner]
  have hsum : Summable (fun k => recTerm p k y) := (hasSum_recTerm p hp hp1 hm y).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => recTerm_nonneg p hp hp1 k y) hsum,
    (hasSum_recTerm p hp hp1 hm y).tsum_eq]
  simp

/-- **The horizon-free stopped record kernel**, as a genuine `Kernel`. -/
noncomputable def hitKKernel (p : ℝ) (hm : 1 ≤ m) : Kernel (RecState N m) (RecState N m) :=
  Kernel.mk (hitKInf p hm) (by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    rw [show (fun y : RecState N m => hitKInf p hm y A)
        = (fun y => ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
            ENNReal.ofReal (hitW p pq.2 y) * (if out hm pq.2 y ∈ A then 1 else 0)) from
      funext fun y => hitKInf_apply p hm y hA]
    exact Measurable.tsum fun pq =>
      (ENNReal.measurable_ofReal.comp (measurable_hitW p pq.1 pq.2)).mul
        (Measurable.ite ((measurable_out hm pq.1 pq.2) hA) measurable_const measurable_const))

theorem hitKKernel_apply (p : ℝ) (hm : 1 ≤ m) (y : RecState N m) :
    hitKKernel (N := N) (m := m) p hm y = hitKInf p hm y := rfl

/-- The stopped record kernel is a Markov kernel. -/
theorem isMarkovKernel_hitKKernel (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) :
    IsMarkovKernel (hitKKernel (N := N) (m := m) p hm) :=
  ⟨fun y => ⟨by rw [hitKKernel_apply]; exact hitKInf_univ p hp hp1 hm y⟩⟩

/-! ### The finite horizons embed monotonically -/

theorem hitK_le_hitKInf (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m)
    {A : Set (RecState N m)} (hA : MeasurableSet A) :
    hitK p hm L y A ≤ hitKInf p hm y A := by
  classical
  rw [hitK_apply p hm L y hA, hitKInf_apply p hm y hA]
  refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum
    (s := (Finset.range (L + 1)).sigma
      (fun k => (Finset.univ : Finset (Fin k → JumpVec N))))
    (f := fun pq : (k : ℕ) × (Fin k → JumpVec N) =>
      ENNReal.ofReal (hitW p pq.2 y) * (if out hm pq.2 y ∈ A then 1 else 0)))
  rw [Finset.sum_sigma]

/-- **Eq. (force) for the genuine probability kernel**: from every record state with
`max_i d_i ≤ K`, the next record state is a simultaneous record with probability at least
`(1-p)^{N(2K+1)}`.  This is the `hforce` input of
`SwarmRec.exists_invariant_measure_pos_srSet`, now for the horizon-free kernel. -/
theorem hitKInf_srSet_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (K : ℕ) (y : RecState N m) (hy : y ∈ exh N m K) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) ≤ hitKInf p hm y (srSet N m) :=
  le_trans (hitK_srSet_ge p hp hp1 hm hN K (2 * K + 1) le_rfl y hy)
    (hitK_le_hitKInf p hm (2 * K + 1) y (measurableSet_srSet N m))

/-- **Prop. "front" for the genuine stopped record kernel, reduced to two inputs.**

The force estimate is discharged (`hitKInf_srSet_ge`), the kernel is a genuine Markov kernel, and
the only remaining hypotheses are the paper's analytic inputs: the Feller property of the record
kernel and tightness of the laws of its iterates. -/
theorem exists_invariant_measure_pos_hitKInf {N m : ℕ} (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (hF : SwarmKB.Feller (hitKKernel (N := N) (m := m) p hm))
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧ 0 < π (srSet N m) := by
  classical
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine exists_invariant_measure_pos_srSet (hitKKernel (N := N) (m := m) p hm) hF μ htight ?_
  intro K
  refine ⟨ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))), ?_, fun y hy => ?_⟩
  · rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · have h := hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy
    rwa [hitKKernel_apply]

end RecKernel
end SimJump
