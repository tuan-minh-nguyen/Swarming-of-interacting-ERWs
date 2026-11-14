/-
Krylov--Bogoliubov theorem for Feller Markov kernels, together with the `π(F) > 0`
mechanism, in the form used by `main_1d_revised.tex`
(Theorem 4.17 of Hairer's Markov process notes and Proposition "front").

Contains no proof holes; imports only Mathlib and `KBCesaro`.

Main results:
* `Feller`, `TightAverages`, `TightIterates`: the hypotheses;
* `exists_invariant_cluster_point`: **Krylov--Bogoliubov**, in the sharp form that the
  invariant measure is a weak cluster point of the Cesaro averages and therefore
  dominates every open set in the liminf sense;
* `exists_invariant_measure_of_tight`, `exists_invariant_measure_of_tight_iterates`,
  `exists_invariant_measure`: existence forms (tight averages / tight iterates /
  compact state space);
* `invariant_density_lower_bound`: `c * π A ≤ π F` from `κ y F ≥ c` on `A`;
* `exists_invariant_measure_pos`: **Proposition "front"**, abstract form -- Feller +
  tightness + the prescribed-path "force" lower bound give an invariant probability
  measure charging the simultaneous-record set `F` with positive mass.
-/
import Swarm.Imports
import Swarm.KBCesaro

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SwarmKB

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- **Feller property**, in the bounded-continuous form used below: for every test function
`f` the function `x ↦ ∫⁻ y, f y ∂(κ x)` is again a bounded continuous `ℝ≥0`-valued
function. -/
def Feller (κ : Kernel X X) : Prop :=
  ∀ f : X →ᵇ ℝ≥0, ∃ h : X →ᵇ ℝ≥0, ∀ x, (h x : ℝ≥0∞) = ∫⁻ y, (f y : ℝ≥0∞) ∂(κ x)

/-- Tightness of the laws of the Cesaro averages of the iterates of `step κ`. -/
def TightAverages (κ : Kernel X X) (μ : Measure X) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ n, avg κ μ n Kᶜ ≤ ε

/-- Tightness of the laws of the iterates themselves. -/
def TightIterates (κ : Kernel X X) (μ : Measure X) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ n, (step κ)^[n] μ Kᶜ ≤ ε

section Algebraic

variable {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Evaluating a finite sum of measures at a set. -/
lemma finset_sum_apply (s : Finset ℕ) (ν : ℕ → Measure X) (A : Set X) :
    (∑ k ∈ s, ν k) A = ∑ k ∈ s, ν k A := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, Measure.add_apply]

/-- If every iterate gives mass at most `ε` to the complement of `K`, then so does the Cesaro
average. -/
lemma avg_compl_le_of_forall_iterate_compl_le {K : Set X} {ε : ℝ≥0∞}
    (h : ∀ k, (step κ)^[k] μ Kᶜ ≤ ε) (n : ℕ) : avg κ μ n Kᶜ ≤ ε := by
  by_cases htop : ε = ⊤
  · simp [htop]
  have hsum : (∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ Kᶜ) ≤ (n + 1 : ℝ≥0∞) * ε := by
    calc (∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ Kᶜ)
        ≤ ∑ _k ∈ Finset.range (n + 1), ε := Finset.sum_le_sum fun k _ => h k
      _ = (n + 1 : ℝ≥0∞) * ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hexp : avg κ μ n Kᶜ = ((n + 1 : ℝ≥0∞))⁻¹ *
      (∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ Kᶜ) := by
    rw [avg, Measure.smul_apply, smul_eq_mul, finset_sum_apply]
  rw [hexp]
  calc ((n + 1 : ℝ≥0∞))⁻¹ * (∑ k ∈ Finset.range (n + 1), (step κ)^[k] μ Kᶜ)
      ≤ ((n + 1 : ℝ≥0∞))⁻¹ * ((n + 1 : ℝ≥0∞) * ε) := by gcongr
    _ = ε := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- Tightness of the laws of the iterates implies tightness of the Cesaro averages. -/
lemma tightAverages_of_tightIterates (h : TightIterates κ μ) : TightAverages κ μ := by
  intro ε hε
  obtain ⟨K, hK, hKle⟩ := h ε hε
  exact ⟨K, hK, fun n => avg_compl_le_of_forall_iterate_compl_le hKle n⟩

end Algebraic

section Nonvacuity

/-- **Sanity check: the Feller hypothesis is inhabited.**  The identity kernel is Feller. -/
theorem feller_id : Feller (Kernel.id : Kernel X X) := by
  intro g
  refine ⟨g, fun x => ?_⟩
  rw [Kernel.id_apply, lintegral_dirac' _ (by fun_prop : Measurable fun y => (g y : ℝ≥0∞))]

end Nonvacuity

section Tight

variable [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
  [TopologicalSpace.SeparableSpace X] [BorelSpace X]
  {κ : Kernel X X} [IsMarkovKernel κ] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Krylov--Bogoliubov theorem, sharp form.**  If `κ` is Feller and the Cesaro averages of
the iterates are tight, then some weak cluster point `a` of those averages is invariant, and
for every open set `G` the mass of `G` under `a` is at most the liminf of the masses under the
averages. -/
theorem exists_invariant_cluster_point (hF : Feller κ) (hT : TightAverages κ μ) :
    ∃ a : ProbabilityMeasure X, Kernel.Invariant κ (a : Measure X) ∧
      ∀ (G : Set X), IsOpen G → ∀ ε : ℝ≥0∞,
        (∀ n, avg κ μ n G ≤ ε) → (a : Measure X) G ≤ ε := by
  classical
  let ν : ℕ → ProbabilityMeasure X := fun n => ⟨avg κ μ n, avg_isProbabilityMeasure κ μ n⟩
  have htight : IsTightMeasureSet
      {x : Measure X | ∃ μ ∈ Set.range ν, ((μ : ProbabilityMeasure X) : Measure X) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKle⟩ := hT ε hε
    exact ⟨K, hK, fun m hm => by
      obtain ⟨μ, ⟨n, rfl⟩, rfl⟩ := hm
      exact hKle n⟩
  have hcomp : IsCompact (closure (Set.range ν)) := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have key : ∀ f : X →ᵇ ℝ≥0,
      ∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (a : Measure X)) = ∫⁻ y, (f y : ℝ≥0∞) ∂(a : Measure X) := by
    intro f
    obtain ⟨hh, hhh⟩ := hF f
    obtain ⟨C₀, hC₀⟩ := exists_pointwise_bound f
    have hC : ∀ x, (f x : ℝ≥0∞) ≤ ((C₀ : ℝ≥0) : ℝ≥0∞) := fun x => by
      exact_mod_cast hC₀ x
    have hCtop : ((C₀ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by simp
    have h1 : Tendsto (fun n => ∫⁻ y, (f y : ℝ≥0∞)
        ∂((ν (φ n) : ProbabilityMeasure X) : Measure X)) atTop
        (𝓝 (∫⁻ y, (f y : ℝ≥0∞) ∂(a : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hconv) f
    have hrew : ∀ (m : Measure X), IsProbabilityMeasure m →
        ∫⁻ y, (f y : ℝ≥0∞) ∂(step κ m) = ∫⁻ x, (hh x : ℝ≥0∞) ∂m := by
      intro m _
      have hfmeas : Measurable fun y => (f y : ℝ≥0∞) := by fun_prop
      rw [step, Measure.lintegral_bind (m := m) (μ := ⇑κ) (Kernel.aemeasurable κ)
        hfmeas.aemeasurable]
      exact lintegral_congr fun x => (hhh x).symm
    have h2 : Tendsto (fun n => ∫⁻ y, (f y : ℝ≥0∞)
        ∂(step κ ((ν (φ n) : ProbabilityMeasure X) : Measure X))) atTop
        (𝓝 (∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (a : Measure X)))) := by
      have h2' : Tendsto (fun n => ∫⁻ x, (hh x : ℝ≥0∞)
          ∂((ν (φ n) : ProbabilityMeasure X) : Measure X)) atTop
          (𝓝 (∫⁻ x, (hh x : ℝ≥0∞) ∂(a : Measure X))) :=
        (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hconv) hh
      have hfun : (fun n => ∫⁻ x, (hh x : ℝ≥0∞)
            ∂((ν (φ n) : ProbabilityMeasure X) : Measure X))
          = fun n => ∫⁻ y, (f y : ℝ≥0∞)
            ∂(step κ ((ν (φ n) : ProbabilityMeasure X) : Measure X)) := by
        funext n
        exact (hrew ((ν (φ n) : ProbabilityMeasure X) : Measure X)
          (avg_isProbabilityMeasure κ μ (φ n))).symm
      rw [hfun] at h2'
      rwa [← hrew ((a : ProbabilityMeasure X) : Measure X) inferInstance] at h2'
    have hne1 : ∀ n, ∫⁻ y, (f y : ℝ≥0∞) ∂((ν (φ n) : ProbabilityMeasure X) : Measure X) ≠ ⊤ :=
      fun n => ne_top_of_le_ne_top hCtop (lintegral_coe_le_of_bound f hC)
    have hne2 : ∀ n, ∫⁻ y, (f y : ℝ≥0∞)
        ∂(step κ ((ν (φ n) : ProbabilityMeasure X) : Measure X)) ≠ ⊤ := by
      intro n
      refine ne_top_of_le_ne_top hCtop ?_
      rw [hrew ((ν (φ n) : ProbabilityMeasure X) : Measure X)
        (avg_isProbabilityMeasure κ μ (φ n))]
      exact lintegral_coe_le_of_bound hh (fun x => by
        rw [hhh x]; exact lintegral_coe_le_of_bound f hC)
    have hnea : ∫⁻ y, (f y : ℝ≥0∞) ∂(a : Measure X) ≠ ⊤ :=
      ne_top_of_le_ne_top hCtop (lintegral_coe_le_of_bound f hC)
    have hnesa : ∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (a : Measure X)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hCtop ?_
      rw [hrew ((a : ProbabilityMeasure X) : Measure X) inferInstance]
      exact lintegral_coe_le_of_bound hh (fun x => by
        rw [hhh x]; exact lintegral_coe_le_of_bound f hC)
    have h1t := (ENNReal.tendsto_toReal_iff hne1 hnea).mpr h1
    have h2t := (ENNReal.tendsto_toReal_iff hne2 hnesa).mpr h2
    have hdt : Tendsto (fun n => ((∫⁻ y, (f y : ℝ≥0∞)
        ∂(step κ ((ν (φ n) : ProbabilityMeasure X) : Measure X))).toReal
        - (∫⁻ y, (f y : ℝ≥0∞)
        ∂((ν (φ n) : ProbabilityMeasure X) : Measure X)).toReal)) atTop (𝓝 0) :=
      (tendsto_avg_step_diff f hC hCtop).comp hφ.tendsto_atTop
    have hsub := h2t.sub h1t
    have huniq := tendsto_nhds_unique hsub hdt
    have hzero : (∫⁻ y, (f y : ℝ≥0∞) ∂(step κ (a : Measure X))).toReal
        - (∫⁻ y, (f y : ℝ≥0∞) ∂(a : Measure X)).toReal = 0 := huniq
    exact (ENNReal.toReal_eq_toReal_iff' hnesa hnea).mp (sub_eq_zero.mp hzero)
  have hinv : Kernel.Invariant κ (a : Measure X) := by
    have hprob : IsProbabilityMeasure (step κ (a : Measure X)) := step_isProbabilityMeasure κ _
    haveI := hprob
    have hfm : (⟨(a : Measure X), inferInstance⟩ : FiniteMeasure X)
        = ⟨step κ (a : Measure X),
            (inferInstance : IsFiniteMeasure (step κ (a : Measure X)))⟩ := by
      apply FiniteMeasure.ext_of_forall_lintegral_eq
      intro f
      simpa using (key f).symm
    exact (congrArg Subtype.val hfm).symm
  refine ⟨a, hinv, ?_⟩
  intro G hG ε hε
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG
  have hlim : atTop.liminf (fun n => ((ν (φ n) : ProbabilityMeasure X) : Measure X) G) ≤ ε :=
    Filter.liminf_le_of_frequently_le
      (Eventually.frequently (Eventually.of_forall (fun n => hε (φ n))))
      ⟨0, Eventually.of_forall (fun n => zero_le)⟩
  exact le_trans hport hlim

/-- **Krylov--Bogoliubov theorem.**  A Feller Markov kernel whose Cesaro averages are tight
admits an invariant probability measure. -/
theorem exists_invariant_measure_of_tight (hF : Feller κ) (hT : TightAverages κ μ) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π := by
  obtain ⟨a, hinv, -⟩ := exists_invariant_cluster_point hF hT
  exact ⟨(a : Measure X), inferInstance, hinv⟩

/-- **Krylov--Bogoliubov theorem, iterate form.** -/
theorem exists_invariant_measure_of_tight_iterates (hF : Feller κ) (hT : TightIterates κ μ) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π :=
  exists_invariant_measure_of_tight hF (tightAverages_of_tightIterates hT)

end Tight

section Compact

variable [CompactSpace X] [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
  [BorelSpace X] {κ : Kernel X X} [IsMarkovKernel κ]

/-- **Krylov--Bogoliubov theorem, compact state space.**  On a compact space every family of
probability measures is tight, so every Feller kernel has an invariant probability measure. -/
theorem exists_invariant_measure (hF : Feller κ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π := by
  refine exists_invariant_measure_of_tight (κ := κ) (μ := μ) hF ?_
  intro ε hε
  exact ⟨Set.univ, isCompact_univ, fun n => by simp⟩

/-- **Sanity check of the main theorem.**  On a compact metric space the identity kernel has an
invariant probability measure. -/
theorem exists_invariant_measure_id [Nonempty X] :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant (Kernel.id : Kernel X X) π :=
  exists_invariant_measure feller_id (Measure.dirac Classical.ofNonempty)

end Compact

section Stationary

variable {κ : Kernel X X} [IsMarkovKernel κ] {π : Measure X}

/-- **Stationarity of the iterates.**  If `π` is invariant then every iterate of the law is
`π`; this is the form in which invariance is used to build the two-sided stationary record
chain (area (g)) and to evaluate Kac's formula. -/
theorem iterate_law_of_invariant (hinv : Kernel.Invariant κ π) (n : ℕ) :
    (step κ)^[n] π = π := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; exact hinv

/-- **The Cesàro averages of an invariant law are the law itself.** -/
theorem avg_of_invariant [IsProbabilityMeasure π] (hinv : Kernel.Invariant κ π) (n : ℕ) :
    avg κ π n = π := by
  have hiter : ∀ k ∈ Finset.range (n + 1), (step κ)^[k] π = π := fun k _ =>
    iterate_law_of_invariant hinv k
  ext s hs
  rw [avg, Measure.smul_apply, smul_eq_mul, finset_sum_apply]
  rw [Finset.sum_congr rfl (fun k hk => by rw [hiter k hk])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

end Stationary

section Frontier

variable {κ : Kernel X X} [IsMarkovKernel κ] {π : Measure X} [IsProbabilityMeasure π]

/-- **The `π(F) > 0` mechanism.**  If `π` is invariant and every state in `A` reaches `F` in
one step with probability at least `c`, then `c * π A ≤ π F`. -/
theorem invariant_density_lower_bound (hinv : Kernel.Invariant κ π) {A : Set X}
    (hAm : MeasurableSet A) {F : Set X} (hFm : MeasurableSet F) {c : ℝ≥0∞}
    (h : ∀ x ∈ A, c ≤ κ x F) :
    c * π A ≤ π F := by
  have hval : π F = ∫⁻ x, κ x F ∂π := by
    conv_lhs => rw [← hinv]
    rw [Measure.bind_apply hFm (Kernel.aemeasurable κ)]
  rw [hval]
  have h1 : ∫⁻ x in A, (c : ℝ≥0∞) ∂π ≤ ∫⁻ x in A, κ x F ∂π :=
    setLIntegral_mono' hAm (fun x hx => h x hx)
  have h2 : ∫⁻ x in A, κ x F ∂π ≤ ∫⁻ x, κ x F ∂π := by
    rw [← lintegral_indicator hAm]
    exact lintegral_mono (Set.indicator_le_self A _)
  calc c * π A = ∫⁻ x in A, (c : ℝ≥0∞) ∂π := (setLIntegral_const A c).symm
    _ ≤ ∫⁻ x, κ x F ∂π := le_trans h1 h2

section Feller

variable [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
  [TopologicalSpace.SeparableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Proposition "front" (abstract form).**  Let `κ` be a Feller Markov kernel whose laws are
tight, and suppose the prescribed-path "force" estimate holds: from every compact set `K` of
states the next state lies in the simultaneous-record set `F` with probability at least some
`c_K > 0`.  Then there is an invariant probability measure `π` with `π F > 0`.

The three inputs are exactly the ones supplied in the paper by (i) the Feller property of the
record chain, (ii) Proposition "tight" (`d_r` tight), and (iii) eq. (force). -/
theorem exists_invariant_measure_pos (hF : Feller κ) (hT : TightIterates κ μ)
    {F : Set X} (hFm : MeasurableSet F)
    (hforce : ∀ K : Set X, IsCompact K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y ∈ K, c ≤ κ y F) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧ 0 < π F := by
  have hT' : TightAverages κ μ := tightAverages_of_tightIterates hT
  obtain ⟨a, hinv, hopen⟩ := exists_invariant_cluster_point hF hT'
  obtain ⟨K, hK, hKle⟩ := hT' (1 / 2) (by norm_num)
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

/-- **Proposition "front" with an exhaustion.**  The force estimate only has to be available
on the compact exhaustion sets `Kset K` that witness tightness. -/
theorem exists_invariant_measure_pos_of_exhaustion (hF : Feller κ) (Kset : ℕ → Set X)
    (hcomp : ∀ K : ℕ, IsCompact (Kset K))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ n, (step κ)^[n] μ (Kset K)ᶜ ≤ ε)
    {F : Set X} (hFm : MeasurableSet F)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y ∈ Kset K, c ≤ κ y F) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧ 0 < π F := by
  have hT' : TightIterates κ μ := fun ε hε => by
    obtain ⟨K, hK⟩ := htight ε hε
    exact ⟨Kset K, hcomp K, hK⟩
  obtain ⟨a, hinv, hopen⟩ := exists_invariant_cluster_point hF (tightAverages_of_tightIterates hT')
  obtain ⟨K₀, hK₀⟩ := htight (1 / 2) (by norm_num)
  have hKopen : IsOpen (Kset K₀)ᶜ := (hcomp K₀).isClosed.isOpen_compl
  have hlim : (a : Measure X) (Kset K₀)ᶜ ≤ 1 / 2 :=
    hopen _ hKopen (1 / 2) (fun n => avg_compl_le_of_forall_iterate_compl_le hK₀ n)
  have hKm : MeasurableSet (Kset K₀) := (hcomp K₀).isClosed.measurableSet
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

end Feller

end Frontier

end SwarmKB
