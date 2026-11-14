/-
# The Krylov–Bogoliubov step needs only tightness of the Cesàro averages

`Swarm/KrylovBogoliubov.lean` proves Prop. "front" from

* the Feller property of the kernel,
* tightness of the laws of **all iterates** `(step κ)^[n] μ`,
* the force estimate on the compact exhaustion.

Reading the proof (`exists_invariant_measure_pos_of_exhaustion`), tightness of the iterates is
used twice: (i) to build `TightAverages κ μ`, and (ii) to obtain one compact set `K` with
`avg κ μ n Kᶜ ≤ 1/2` for all `n` — and in (ii) the iterate bound is immediately averaged by
`avg_compl_le_of_forall_iterate_compl_le`.  The Krylov–Bogoliubov cluster point
(`exists_invariant_cluster_point`) consumes *only* `TightAverages κ μ`.  Hence the iterate
bound is stronger than the proof needs: the sufficient hypothesis is tightness of the Cesàro
averages

  `∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, avg κ μ n Kᶜ ≤ ε`,

i.e. uniform control of the **time averages** `(n+1)⁻¹ ∑_{k≤n} (step κ)^[k] μ (Kᶜ)` rather than
of every iterate.  A bound that fails at sparse times is allowed.

This file proves that form abstractly (`exists_invariant_measure_pos_of_tightAverages`,
`exists_invariant_measure_pos_of_exhaustion_avgTight`), shows the old iterate hypothesis
implies it (`avgTight_of_iterateTight`, so nothing is lost), and instantiates it for the stopped
record kernel `hitKKernel` (`exists_invariant_measure_pos_hitKInf_avgTight`), where the weakened
premise is

  `∀ ε > 0, ∃ K, ∀ n, (n+1)⁻¹ ∑_{k≤n} (step hitKKernel)^[k] μ (exh N m K)ᶜ ≤ ε`.

Nothing here proves tightness; it identifies the weakest tightness premise the Krylov–Bogoliubov
mechanism actually consumes, so that the analytic work (block estimate, drift/Foster–Lyapunov,
or covering series) may aim at time-averaged tails.
-/
import Swarm.FellerInf

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
  [BorelSpace X]
  {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

omit [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
  [BorelSpace X] in
/-- **Nothing is lost**: tightness of every iterate implies tightness of the Cesàro averages,
for a fixed exhaustion. -/
lemma avgTight_of_iterateTight (Kset : ℕ → Set X)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, (step κ)^[n] μ (Kset K)ᶜ ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, avg κ μ n (Kset K)ᶜ ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := htight ε hε
  exact ⟨K, fun n => avg_compl_le_of_forall_iterate_compl_le hK n⟩

/-- **Prop. "front" from tight Cesàro averages.**  Same conclusion as
`exists_invariant_measure_pos`, but the tightness hypothesis is on the averages, which is what
the Krylov–Bogoliubov cluster-point argument reads. -/
theorem exists_invariant_measure_pos_of_tightAverages (hF : Feller κ) (hT : TightAverages κ μ)
    {F : Set X} (hFm : MeasurableSet F)
    (hforce : ∀ K : Set X, IsCompact K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y ∈ K, c ≤ κ y F) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧ 0 < π F := by
  obtain ⟨a, hinv, hopen⟩ := exists_invariant_cluster_point hF hT
  obtain ⟨K, hK, hKle⟩ := hT (1 / 2) (by norm_num)
  have hKopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hlim : (a : Measure X) Kᶜ ≤ 1 / 2 := hopen Kᶜ hKopen (1 / 2) hKle
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsum : (a : Measure X) K + (a : Measure X) Kᶜ = 1 := by
    rw [measure_add_measure_compl hKm, measure_univ]
  have hposK : 0 < (a : Measure X) K := by
    rw [pos_iff_ne_zero]
    intro h0
    have h1 : (a : Measure X) Kᶜ = 1 := by
      have h := hsum
      rw [h0, zero_add] at h
      simpa using h
    rw [h1] at hlim
    exact absurd hlim (by norm_num)
  obtain ⟨c, hc, hforce'⟩ := hforce K hK
  have hbound := invariant_density_lower_bound hinv hKm hFm (c := c) hforce'
  refine ⟨(a : Measure X), inferInstance, hinv, lt_of_lt_of_le ?_ hbound⟩
  exact ENNReal.mul_pos hc (ne_of_gt hposK)

/-- **Prop. "front" with an exhaustion, from time-averaged tail bounds.**  The force estimate is
only required on the exhaustion sets witnessing tightness, and the tightness input is the
Cesàro-average one. -/
theorem exists_invariant_measure_pos_of_exhaustion_avgTight (hF : Feller κ) (Kset : ℕ → Set X)
    (hcomp : ∀ K : ℕ, IsCompact (Kset K))
    (havg : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, avg κ μ n (Kset K)ᶜ ≤ ε)
    {F : Set X} (hFm : MeasurableSet F)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y ∈ Kset K, c ≤ κ y F) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧ 0 < π F := by
  have hT : TightAverages κ μ := by
    intro ε hε
    obtain ⟨K, hK⟩ := havg ε hε
    exact ⟨Kset K, hcomp K, hK⟩
  obtain ⟨a, hinv, hopen⟩ := exists_invariant_cluster_point hF hT
  obtain ⟨K₀, hKle⟩ := havg (1 / 2) (by norm_num)
  have hKc : IsCompact (Kset K₀) := hcomp K₀
  have hlim : (a : Measure X) (Kset K₀)ᶜ ≤ 1 / 2 :=
    hopen (Kset K₀)ᶜ hKc.isClosed.isOpen_compl (1 / 2) hKle
  have hKm : MeasurableSet (Kset K₀) := hKc.isClosed.measurableSet
  have hsum : (a : Measure X) (Kset K₀) + (a : Measure X) (Kset K₀)ᶜ = 1 := by
    rw [measure_add_measure_compl hKm, measure_univ]
  have hposK : 0 < (a : Measure X) (Kset K₀) := by
    rw [pos_iff_ne_zero]
    intro h0
    have h1 : (a : Measure X) (Kset K₀)ᶜ = 1 := by
      have h := hsum
      rw [h0, zero_add] at h
      simpa using h
    rw [h1] at hlim
    exact absurd hlim (by norm_num)
  obtain ⟨c, hc, hforce'⟩ := hforce K₀
  have hbound := invariant_density_lower_bound hinv hKm hFm (c := c) hforce'
  refine ⟨(a : Measure X), inferInstance, hinv, lt_of_lt_of_le ?_ hbound⟩
  exact ENNReal.mul_pos hc (ne_of_gt hposK)

omit [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
  [BorelSpace X] in
/-- **The paper's `(tightlaw)` in its literal `lim_K limsup_r` form gives the hypothesis used
above.**  `limsup_r μ_r ((Kset K)ᶜ) ≤ ε/2` gives `μ_r ((Kset K)ᶜ) ≤ ε` eventually in `r`. -/
lemma hlim_of_tendsto_limsup (Kset : ℕ → Set X)
    (h : Tendsto (fun K : ℕ => limsup (fun n : ℕ => (step κ)^[n] μ (Kset K)ᶜ) atTop)
      atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (step κ)^[n] μ (Kset K)ᶜ ≤ ε := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · subst htop
    exact ⟨0, Filter.Eventually.of_forall fun _ => le_top⟩
  have hhalf : ∀ᶠ K : ℕ in atTop,
      limsup (fun n : ℕ => (step κ)^[n] μ (Kset K)ᶜ) atTop ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.1 h (ε / 2) (ENNReal.div_pos hε.ne' (by norm_num))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hhalf
  refine ⟨K, ?_⟩
  exact (Filter.limsup_le_iff' (u := fun n : ℕ => (step κ)^[n] μ (Kset K)ᶜ) (f := atTop)
    (x := ε / 2)).1 (hK K le_rfl) ε (ENNReal.half_lt_self hε.ne' htop)

omit [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
  [BorelSpace X] in
/-- Nothing is lost: a uniform iterate bound gives the `limsup` form. -/
lemma limsup_form_of_uniform (Kset : ℕ → Set X)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, (step κ)^[n] μ (Kset K)ᶜ ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (step κ)^[n] μ (Kset K)ᶜ ≤ ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := htight ε hε
  exact ⟨K, Filter.Eventually.of_forall hK⟩

omit [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
  [BorelSpace X] in
/-- **The paper's `tightlaw` form is already enough.**  If the tails are only known to satisfy
the `limsup` bound `limsup_r μ_r ((Kset K)ᶜ) ≤ ε` (one exhaustion level per `ε`), then the
Cesàro averages obey the same bound uniformly in `n`: the eventual bound controls all terms past
`N`, and the finitely many earlier iterates are absorbed by enlarging the exhaustion level, using
continuity from above for the probability measures `(step κ)^[k] μ`. -/
lemma avgTight_of_limsup (Kset : ℕ → Set X) (hmono : Monotone Kset)
    (hmeas : ∀ K : ℕ, MeasurableSet (Kset K)) (hcover : ⋃ K, Kset K = Set.univ)
    (hlim : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (step κ)^[n] μ (Kset K)ᶜ ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, avg κ μ n (Kset K)ᶜ ≤ ε := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := hlim ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hK₀
  -- each of the finitely many earlier iterates has small tail for a large enough level
  have hex : ∀ k : ℕ, ∃ K : ℕ, (step κ)^[k] μ (Kset K)ᶜ ≤ ε := by
    intro k
    haveI := step_iterate_isProbabilityMeasure κ μ k
    have hcompl : (⋂ m : ℕ, (Kset m)ᶜ) = ∅ := by
      rw [← Set.compl_iUnion, hcover, Set.compl_univ]
    have hmono' : Antitone fun m : ℕ => (Kset m)ᶜ := fun a b hab =>
      Set.compl_subset_compl.2 (hmono hab)
    have hnull : ∀ m : ℕ, NullMeasurableSet ((Kset m)ᶜ) ((step κ)^[k] μ) := fun m =>
      (hmeas m).compl.nullMeasurableSet
    have hne : ∃ m : ℕ, (step κ)^[k] μ ((Kset m)ᶜ) ≠ ∞ := ⟨0, measure_ne_top _ _⟩
    have ht := tendsto_measure_iInter_atTop hnull hmono' hne
    rw [hcompl, measure_empty] at ht
    have hev : ∀ᶠ m : ℕ in atTop, (step κ)^[k] μ ((Kset m)ᶜ) ≤ ε :=
      ENNReal.tendsto_nhds_zero.1 ht ε hε
    obtain ⟨m, hm⟩ := eventually_atTop.1 hev
    exact ⟨m, hm m le_rfl⟩
  choose Kf hKf using hex
  refine ⟨max K₀ ((Finset.range N).sup Kf), fun n => ?_⟩
  have hmonoK : Kset K₀ ⊆ Kset ((Finset.range N).sup Kf ⊔ K₀) := by
    refine hmono ?_
    exact le_sup_right
  have hsup : K₀ ≤ max K₀ ((Finset.range N).sup Kf) := le_max_left _ _
  have hall : ∀ k : ℕ, (step κ)^[k] μ (Kset (max K₀ ((Finset.range N).sup Kf)))ᶜ ≤ ε := by
    intro k
    rcases lt_or_ge k N with hk | hk
    · have hle : Kf k ≤ max K₀ ((Finset.range N).sup Kf) :=
        le_trans (Finset.le_sup (Finset.mem_range.2 hk)) (le_max_right _ _)
      exact le_trans (measure_mono (Set.compl_subset_compl.2 (hmono hle))) (hKf k)
    · exact le_trans (measure_mono (Set.compl_subset_compl.2 (hmono hsup))) (hN k hk)
  exact avg_compl_le_of_forall_iterate_compl_le hall n

end SwarmKB

namespace SwarmRec

/-- **Prop. "front" on the record-state space, from time-averaged tail bounds.**  Same conclusion
as `exists_invariant_measure_pos_srSet`, with tightness of every iterate replaced by tightness of
the Cesàro averages of the exhaustion tails. -/
theorem exists_invariant_measure_pos_srSet_avgTight {N m : ℕ}
    (κ : ProbabilityTheory.Kernel (RecState N m) (RecState N m))
    [ProbabilityTheory.IsMarkovKernel κ]
    (hF : SwarmKB.Feller κ) (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (havg : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ,
      ∀ n, SwarmKB.avg κ μ n (exh N m K)ᶜ ≤ ε)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y : RecState N m,
      y ∈ exh N m K → c ≤ κ y (srSet N m)) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      ProbabilityTheory.Kernel.Invariant κ π ∧ 0 < π (srSet N m) :=
  SwarmKB.exists_invariant_measure_pos_of_exhaustion_avgTight (κ := κ) hF (exh N m)
    (fun K => isCompact_dist2_le N m K) havg (measurableSet_srSet N m) hforce

end SwarmRec

namespace SimJump
namespace RecKernel

/-- The iterate hypothesis of `exists_invariant_measure_pos_hitKInf_feller` implies the
time-averaged one, so the weakened premise is not a new assumption. -/
theorem avgTight_hitKKernel_of_tight {N m : ℕ} (p : ℝ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (μ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[n] μ (SwarmRec.exh N m K)ᶜ ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n : ℕ,
      SwarmKB.avg (hitKKernel (N := N) (m := m) p hm) μ n (SwarmRec.exh N m K)ᶜ ≤ ε := by
  classical
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  exact SwarmKB.avgTight_of_iterateTight (κ := hitKKernel (N := N) (m := m) p hm) (μ := μ)
    (fun K => SwarmRec.exh N m K) htight

/-- **Prop. "front" for the genuine stopped record kernel, from time-averaged tail bounds.**
The force estimate is discharged (`hitKInf_srSet_ge`), the Feller property is
`feller_hitKKernel`, and the only remaining analytic input is tightness of the Cesàro averages
of the exhaustion tails — weaker than tightness of every iterate. -/
theorem exists_invariant_measure_pos_hitKInf_avgTight {N m : ℕ} (p : ℝ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (havg : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n : ℕ,
      SwarmKB.avg (hitKKernel (N := N) (m := m) p hm) μ n (SwarmRec.exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (SwarmRec.RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (SwarmRec.srSet N m) := by
  classical
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine SwarmRec.exists_invariant_measure_pos_srSet_avgTight
    (κ := hitKKernel (N := N) (m := m) p hm) (feller_hitKKernel p hp hp1 hm) μ havg ?_
  intro K
  refine ⟨ENNReal.ofReal ((1 - p) ^ (N * (2 * K + 1))), ?_, fun y hy => ?_⟩
  · rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (by linarith) _
  · have h := hitKInf_srSet_ge (N := N) (m := m) p hp hp1 hm hN K y hy
    rwa [hitKKernel_apply]

end RecKernel
end SimJump

namespace SwarmRec

/-- The exhaustion `exh N m` is monotone in the level. -/
lemma monotone_exh (N m : ℕ) : Monotone (exh N m) := by
  intro a b hab y hy i
  exact le_trans (hy i) hab

/-- The exhaustion `exh N m` covers the record-state space. -/
lemma iUnion_exh (N m : ℕ) : (⋃ K : ℕ, exh N m K) = Set.univ := by
  ext y
  constructor
  · intro _; exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.2
      ⟨Finset.univ.sup (fun i => dist2 y i), fun i => Finset.le_sup (Finset.mem_univ i)⟩

end SwarmRec

namespace SimJump
namespace RecKernel

/-- **Prop. "front" for the stopped record kernel from the paper's `tightlaw` form**: it is
enough that for every `ε` some exhaustion level has `limsup` tail at most `ε` along the iterates,
i.e. `lim_K limsup_r P(d_r > K) = 0` in the form `∀ ε > 0, ∃ K, ∀ᶠ r, tail ≤ ε`.  No uniform
bound on every iterate is needed. -/
theorem exists_invariant_measure_pos_hitKInf_limsup {N m : ℕ} (p : ℝ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (hlim : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[n] μ (SwarmRec.exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (SwarmRec.RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (SwarmRec.srSet N m) := by
  classical
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  refine exists_invariant_measure_pos_hitKInf_avgTight p hp hp1 hp_lt hm hN μ ?_
  intro ε hε
  exact SwarmKB.avgTight_of_limsup (κ := hitKKernel (N := N) (m := m) p hm) (μ := μ)
    (fun K => SwarmRec.exh N m K) (SwarmRec.monotone_exh N m)
    (fun K => SwarmRec.measurableSet_exh N m K) (SwarmRec.iUnion_exh N m) hlim ε hε

/-- **Consistency**: the original uniform-iterate hypothesis of
`exists_invariant_measure_pos_hitKInf_feller` is recovered as a special case. -/
theorem exists_invariant_measure_pos_hitKInf_of_tight {N m : ℕ} (p : ℝ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (SwarmRec.RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] μ (SwarmRec.exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (SwarmRec.RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧
      0 < π (SwarmRec.srSet N m) :=
by
  classical
  haveI := isMarkovKernel_hitKKernel (N := N) (m := m) p hp hp1 hm
  exact exists_invariant_measure_pos_hitKInf_limsup p hp hp1 hp_lt hm hN μ
    (fun ε hε => SwarmKB.limsup_form_of_uniform (κ := hitKKernel (N := N) (m := m) p hm)
      (μ := μ) (Kset := fun K => SwarmRec.exh N m K) htight ε hε)

end RecKernel
end SimJump

/-! ## Audit -/


