/-
# Strict positivity of the simultaneous-record mass for *every* invariant record law


`Swarm/FrontThin.lean` obtains `0 < π (srSet N m)` for the stopped record
kernel `hitKKernel` from two analytic inputs: the Feller property and **tightness of the
iterates**, through the (quantitative) form of the paper's Proposition "front".

The observation recorded here is that the *positivity half* of that proposition uses neither
input.  It is a consequence of the force estimate `hitKInf_srSet_ge` and invariance alone.
For any invariant probability `π` of `hitKKernel`,

  `(1-p)^(N*(2K+1)) * π (exh N m K) ≤ π (srSet N m)`   for every `K`,

because `π (srSet) = ∫⁻ y, κ y srSet ∂π ≥ c K * π (exh K)` by the force estimate, and at least
one exhaustion level carries positive `π`-mass since the compact exhaustion covers the whole
record-state space (`dist2` is finite, so every state lies in some `exh K`).

Proved declarations (`namespace SimJump.RecKernel`):

* `exists_mem_exh`, `iUnion_exh` — the compact exhaustion covers `RecState N m`;
* `invariant_mul_Kset_le` — generic quantitative form for any invariant measure;
* `invariant_pos_of_force_ne_zero`, `invariant_pos_of_force` — generic strict positivity from
  the force estimate and the exhaustion alone (nonzero-measure and probability forms);
* `bind_mul_Kset_le` — the one-step form for an arbitrary, not necessarily invariant, start law;
* `invariant_srSet_mul_exh_le`, `invariant_srSet_pos`, `invariant_measure_srSet_pos`,
  `invariant_srSet_ne_zero`, `invariant_kac_side_conditions` — the concrete statements for the
  genuine horizon-free stopped record kernel `hitKKernel`, with the paper's explicit force
  constant `(1-p)^(N*(2K+1))`;
* `step_iterate_srSet_ge` — the iterate form `c K * P(d_r <= K) <= P(Y_{r+1} in F)`;
* `iUnion_exhT`, `hitKKernelT_srSet_ge`, `invariantT_srSet_pos`,
  `invariantT_srSet_mul_exh_le` — the same statements for the time-extended kernel
  `hitKKernelT` of `Swarm/ChainLink.lean`;
* `record_ED_of_invariant` — the composition with `KacBridge.record_ED_of_invariant_mass`:
  with the positivity derived from invariance, the paper's `(ED)` for a two-sided stationary
  system with the `(freshlaw)` factorisation needs no tightness input at all.

Because no tightness is used, these statements hold for *every* invariant law, in particular for
invariant laws produced by the non-tightness routes of the campaign (excessive measure /
moment / Lyapunov arguments in `areas/tightness/{AvgTight,MomentTight,RecordTightAvg}.lean`).
The Kac step consumes `0 < π (srSet)` as a *strict* inequality, so this removes the need to
route that side condition through the analytic tightness input.

Nothing here constructs an invariant law, and no `Swarm.Ballistic`, `Swarm.RegenAvailable`,
`Swarm.InitialRegen` or `Swarm.MainClaim` statement is made.
-/
import Swarm.ChainLink
import Swarm.InfKernel
import Swarm.KacBridge
import Swarm.RecordState

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

set_option linter.style.haveILetI false

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### The compact exhaustion covers the record-state space -/

/-- Every record state lies at some finite level of the compact exhaustion. -/
lemma exists_mem_exh (y : RecState N m) : ∃ K, y ∈ exh N m K :=
  ⟨∑ i, dist2 y i,
    fun i => Finset.single_le_sum (f := fun i => dist2 y i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

/-- The compact exhaustion of the record-state space is increasing with union the whole space. -/
lemma iUnion_exh (N m : ℕ) : (⋃ K : ℕ, exh N m K) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_exh y

/-! ### Generic forms

The two statements below isolate the measure-theoretic content of the positivity half of
Proposition "front": it is the force estimate plus invariance, with no topological input. -/

/-- **Quantitative force inequality for an invariant law.**
If `c K ≤ κ y F` for every `y` in the exhaustion set `Kset K`, then every invariant probability
`π` of `κ` satisfies `c K * π (Kset K) ≤ π F`. -/
theorem invariant_mul_Kset_le {X : Type*} [MeasurableSpace X]
    (κ : Kernel X X) [IsMarkovKernel κ]
    (Kset : ℕ → Set X) (hKmeas : ∀ K, MeasurableSet (Kset K))
    {F : Set X} (hFm : MeasurableSet F) (c : ℕ → ℝ≥0∞)
    (hforce : ∀ K (y : X), y ∈ Kset K → c K ≤ κ y F)
    (π : Measure X) (hinv : Kernel.Invariant κ π) (K : ℕ) :
    c K * π (Kset K) ≤ π F := by
  have hπF : π F = ∫⁻ y, κ y F ∂π := by
    conv_lhs => rw [← Kernel.Invariant.def hinv]
    rw [Measure.bind_apply hFm (Kernel.measurable κ).aemeasurable]
  rw [hπF, ← lintegral_indicator_const (hKmeas K) (c K)]
  refine lintegral_mono (fun y => ?_)
  by_cases hy : y ∈ Kset K
  · rw [Set.indicator_of_mem hy]
    exact hforce K y hy
  · rw [Set.indicator_of_notMem hy]
    exact zero_le

/-- **Strict positivity from the force estimate alone, for any nonzero invariant measure.**
Let `Kset` be an exhaustion of the state space (`∀ x, ∃ K, x ∈ Kset K`) with measurable levels,
and suppose the paper's force estimate holds on each level with a nonzero constant.  Then every
*nonzero* invariant measure `π` of `κ` satisfies `0 < π F`.

Neither the Feller property of `κ` nor tightness of its iterates is used, and `π` need not be
finite: this is the form produced by the excessive-measure and Krylov–Bogoliubov cluster-point
routes, where no probability invariant law is available yet. -/
theorem invariant_pos_of_force_ne_zero {X : Type*} [MeasurableSpace X]
    (κ : Kernel X X) [IsMarkovKernel κ]
    (Kset : ℕ → Set X) (hKmeas : ∀ K, MeasurableSet (Kset K))
    (hcover : ∀ x : X, ∃ K, x ∈ Kset K)
    {F : Set X} (hFm : MeasurableSet F) (c : ℕ → ℝ≥0∞) (hc : ∀ K, c K ≠ 0)
    (hforce : ∀ K (y : X), y ∈ Kset K → c K ≤ κ y F)
    (π : Measure X) (hπ : π ≠ 0) (hinv : Kernel.Invariant κ π) :
    0 < π F := by
  -- A nonzero measure loads some exhaustion level: the levels cover the space.
  obtain ⟨K, hK⟩ : ∃ K, π (Kset K) ≠ 0 := by
    by_contra h
    have hzero : ∀ K, π (Kset K) = 0 := fun K => not_not.mp (not_exists.mp h K)
    have hcover' : (⋃ K, Kset K) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact hcover x
    apply hπ
    apply Measure.measure_univ_eq_zero.mp
    rw [← hcover']
    refine le_antisymm (le_trans (measure_iUnion_le _) ?_) (zero_le)
    simp [hzero]
  exact lt_of_lt_of_le (ENNReal.mul_pos (hc K) hK)
    (invariant_mul_Kset_le κ Kset hKmeas hFm c hforce π hinv K)

/-- **Strict positivity from the force estimate alone.**  The probability form of
`invariant_pos_of_force_ne_zero`. -/
theorem invariant_pos_of_force {X : Type*} [MeasurableSpace X]
    (κ : Kernel X X) [IsMarkovKernel κ]
    (Kset : ℕ → Set X) (hKmeas : ∀ K, MeasurableSet (Kset K))
    (hcover : ∀ x : X, ∃ K, x ∈ Kset K)
    {F : Set X} (hFm : MeasurableSet F) (c : ℕ → ℝ≥0∞) (hc : ∀ K, c K ≠ 0)
    (hforce : ∀ K (y : X), y ∈ Kset K → c K ≤ κ y F)
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant κ π) :
    0 < π F := by
  refine invariant_pos_of_force_ne_zero κ Kset hKmeas hcover hFm c hc hforce π ?_ hinv
  intro h
  have h1 : π Set.univ = 1 := measure_univ
  rw [h] at h1
  simp at h1

/-! ### The genuine stopped record kernel -/

/-- **Quantitative positivity for any invariant record law.**  For every `K`, the `srSet`-mass of
an invariant probability of the horizon-free stopped record kernel is at least the paper's force
constant times the mass of the exhaustion level `exh N m K`. -/
theorem invariant_srSet_mul_exh_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (hN : 0 < N) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π) (K : ℕ) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) * π (exh N m K) ≤ π (srSet N m) := by
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine invariant_mul_Kset_le (hitKKernel (N := N) (m := m) p hm) (exh N m)
    (fun K => measurableSet_exh N m K) (measurableSet_srSet N m)
    (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))) ?_ π hinv K
  intro K y hy
  rw [hitKKernel_apply]
  exact hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy

/-- **Strict positivity of the simultaneous-record mass, with no tightness hypothesis.**  Every
invariant probability of the genuine stopped record kernel charges the simultaneous-record set
`F = srSet N m`. -/
theorem invariant_srSet_pos (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π) :
    0 < π (srSet N m) := by
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine invariant_pos_of_force (hitKKernel (N := N) (m := m) p hm) (exh N m)
    (fun K => measurableSet_exh N m K) (fun x => exists_mem_exh x)
    (measurableSet_srSet N m) (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))))
    ?_ ?_ π hinv
  · intro K
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · intro K y hy
    rw [hitKKernel_apply]
    exact hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy


/-- **Every nonzero invariant measure of the record kernel charges the simultaneous-record set.**
This is `invariant_srSet_pos` without the probability assumption, i.e. in the form produced by the
excessive-measure and cluster-point routes of `areas/tightness/{AvgTight,MomentTight}`. -/
theorem invariant_measure_srSet_pos (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (π : Measure (RecState N m)) (hπ : π ≠ 0)
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π) :
    0 < π (srSet N m) := by
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine invariant_pos_of_force_ne_zero (hitKKernel (N := N) (m := m) p hm) (exh N m)
    (fun K => measurableSet_exh N m K) (fun x => exists_mem_exh x)
    (measurableSet_srSet N m) (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))))
    ?_ ?_ π hπ hinv
  · intro K
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · intro K y hy
    rw [hitKKernel_apply]
    exact hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy

/-- The nonzero form consumed by the Kac step (`0 < pf`). -/
theorem invariant_srSet_ne_zero (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π) :
    π (srSet N m) ≠ 0 :=
  ne_of_gt (invariant_srSet_pos p hp hp1 hp_lt hm hN π hinv)

/-- **The two Kac side conditions for every invariant record law**: the `srSet`-mass is strictly
positive and finite.  This is `FrontThin.srSet_kac_side_conditions` with the Feller and
tightness hypotheses removed (they are still needed for the *existence* of `π`). -/
theorem invariant_kac_side_conditions (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π) :
    0 < π (srSet N m) ∧ π (srSet N m) < ⊤ :=
  ⟨invariant_srSet_pos p hp hp1 hp_lt hm hN π hinv, measure_lt_top _ _⟩

/-! ### The time-extended record kernel

The next-record state alone does not carry the waiting time, and the paper's block inequalities
are stated for the chain with elapsed time (`Swarm/ChainLink.lean`,
`hitKKernelT : Kernel (RecState N m × ℕ) (RecState N m × ℕ)`).  The same positivity statement
holds there: by `hitKKernelT_fst` the `RecState` marginal of each transition is `hitKKernel` at
the projected state, independently of the time coordinate, so the force estimate transfers.

This is the form a two-sided stationary version of the *time-extended* record chain needs for
its Kac factor `π(F) > 0`.
-/

/-- The lifted exhaustion `{z | z.1 ∈ exh N m K}` covers the time-extended state space. -/
lemma iUnion_exhT (N m : ℕ) :
    (⋃ K : ℕ, Prod.fst ⁻¹' exh N m K : Set (RecState N m × ℕ)) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
  exact exists_mem_exh z.1

/-- **Eq. (force) for the time-extended record kernel**, with the same constant. -/
theorem hitKKernelT_srSet_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (K : ℕ) (z : RecState N m × ℕ) (hz : z.1 ∈ exh N m K) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) ≤
      hitKKernelT (N := N) (m := m) p hm z {z' | z'.1 ∈ srSet N m} := by
  change ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) ≤
    (hitKKernelT (N := N) (m := m) p hm z) (Prod.fst ⁻¹' srSet N m)
  rw [← Measure.map_apply measurable_fst (measurableSet_srSet N m), hitKKernelT_fst,
    hitKKernel_apply]
  exact hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K z.1 hz

/-- **Every invariant law of the time-extended record kernel charges the simultaneous-record
states**, with the paper's explicit force constant and no tightness hypothesis. -/
theorem invariantT_srSet_pos (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (hitKKernelT (N := N) (m := m) p hm) ν) :
    0 < ν {z : RecState N m × ℕ | z.1 ∈ srSet N m} := by
  haveI := isMarkovKernel_hitKKernelT (N := N) (m := m) p hp hp1 hm
  refine invariant_pos_of_force (hitKKernelT (N := N) (m := m) p hm)
    (fun K => Prod.fst ⁻¹' exh N m K)
    (fun K => (measurableSet_exh N m K).preimage measurable_fst)
    (fun z => by
      obtain ⟨K, hK⟩ := exists_mem_exh z.1
      exact ⟨K, hK⟩)
    ((measurableSet_srSet N m).preimage measurable_fst)
    (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))) ?_ ?_ ν hinv
  · intro K
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · intro K z hz
    exact hitKKernelT_srSet_ge (N := N) (m := m) p hp hp1 hm hN K z hz

/-- The quantitative form for the time-extended kernel: the force constant times the mass of the
lifted exhaustion level is at most the simultaneous-record mass. -/
theorem invariantT_srSet_mul_exh_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (hN : 0 < N) (ν : Measure (RecState N m × ℕ)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (hitKKernelT (N := N) (m := m) p hm) ν) (K : ℕ) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) * ν (Prod.fst ⁻¹' exh N m K) ≤
      ν {z : RecState N m × ℕ | z.1 ∈ srSet N m} := by
  haveI := isMarkovKernel_hitKKernelT (N := N) (m := m) p hp hp1 hm
  refine invariant_mul_Kset_le (hitKKernelT (N := N) (m := m) p hm)
    (fun K => Prod.fst ⁻¹' exh N m K)
    (fun K => (measurableSet_exh N m K).preimage measurable_fst)
    ((measurableSet_srSet N m).preimage measurable_fst)
    (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1)))) ?_ ν hinv K
  intro K z hz
  exact hitKKernelT_srSet_ge (N := N) (m := m) p hp hp1 hm hN K z hz


/-! ### The bound at every iterate

Invariance was the *only* place where the Markov structure of a stationary law entered the
argument above.  Without invariance the same computation gives the one-step mass bound for an
arbitrary start law, i.e. the iterate form in which the campaign states its path-law tails
(`recordTraj_eval`, `recordTraj_tail`).
-/

/-- **One-step force bound for an arbitrary start law.** -/
theorem bind_mul_Kset_le {X : Type*} [MeasurableSpace X]
    (κ : Kernel X X) [IsMarkovKernel κ]
    (Kset : ℕ → Set X) (hKmeas : ∀ K, MeasurableSet (Kset K))
    {F : Set X} (hFm : MeasurableSet F) (c : ℕ → ℝ≥0∞)
    (hforce : ∀ K (y : X), y ∈ Kset K → c K ≤ κ y F)
    (ν : Measure X) (K : ℕ) :
    c K * ν (Kset K) ≤ ν.bind κ F := by
  rw [Measure.bind_apply hFm (Kernel.measurable κ).aemeasurable,
    ← lintegral_indicator_const (hKmeas K) (c K)]
  refine lintegral_mono (fun y => ?_)
  by_cases hy : y ∈ Kset K
  · rw [Set.indicator_of_mem hy]
    exact hforce K y hy
  · rw [Set.indicator_of_notMem hy]
    exact zero_le

/-- **The force constant times the mass of an exhaustion level bounds the *next* iterate's
simultaneous-record mass.**  This is the iterate form of the paper's `(force)`; combined with
`recordTraj_eval` it reads as a path-law statement
`c K * P(d_r ≤ K) ≤ P(Y_{r+1} ∈ F)`. -/
theorem step_iterate_srSet_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) (r K : ℕ) :
    ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))) *
        ((SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] μ) (exh N m K)
      ≤ ((SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r + 1] μ) (srSet N m) := by
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  have hstep : (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r + 1] μ
      = ((SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] μ).bind
          (hitKKernel (N := N) (m := m) p hm) := by
    rw [Function.iterate_succ_apply']
    rfl
  rw [hstep]
  exact bind_mul_Kset_le (hitKKernel (N := N) (m := m) p hm) (exh N m)
    (fun K => measurableSet_exh N m K) (measurableSet_srSet N m)
    (fun K => ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))))
    (fun K y hy => by
      rw [hitKKernel_apply]
      exact hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy) _ K


/-! ### Composition with the Kac step

`areas/recordkernel/KacBridge.record_ED_of_invariant_mass` takes the strict positivity
`0 < π (srSet)` of the invariant record law as a hypothesis and derives the paper's `(ED)` for a
two-sided stationary system with the `(freshlaw)` factorisation.  With `invariant_srSet_pos` that
hypothesis is discharged from invariance alone, so the `(ED)` step no longer depends on iterate
tightness at all: tightness remains only in the *existence* of `π`.
-/

/-- **The paper's `(ED)` with the positivity of `π (srSet)` derived from invariance**, i.e. without
the tightness hypothesis of `SwarmFront.exists_record_ED_of_tight`. -/
theorem record_ED_of_invariant {N m : ℕ} (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1)
    (hm : 1 ≤ m) (hN : 0 < N) (π : Measure (RecState N m)) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving (e : Ω → Ω) μ μ)
    {P : Type*} [MeasurableSpace P] (Φ : Ω → P) (hΦ : Measurable Φ) (ν : Measure P)
    [IsProbabilityMeasure ν] (A : Set Ω) (hA : MeasurableSet A)
    (hfac : ∀ B : Set P, MeasurableSet B → μ (A ∩ Φ ⁻¹' B) = μ A * ν B)
    (g : P → ℕ) (hg : Measurable g) (hg1 : ∀ q, 1 ≤ g q)
    (hD : ∀ ω, KacFormula.retTime (e : Ω → Ω) A ω = ((g (Φ ω) : ℕ) : ℕ∞))
    (pv : ℝ≥0∞) (hpv : 0 < pv) (hpvt : pv ≠ ⊤)
    (hmass : μ A = π (srSet N m) * pv) :
    Integrable (fun q => (g q : ℝ)) ν ∧
      1 ≤ ∫ q, (g q : ℝ) ∂ν ∧
        ∫ q, (g q : ℝ) ∂ν ≤ ((π (srSet N m) * pv)⁻¹).toReal :=
  SwarmFront.record_ED_of_invariant_mass π
    (invariant_srSet_pos p hp hp1 hp_lt hm hN π hinv)
    e he Φ hΦ ν A hA hfac g hg hg1 hD pv hpv hpvt hmass


end RecKernel
end SimJump
