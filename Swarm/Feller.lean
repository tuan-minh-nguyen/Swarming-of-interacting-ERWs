/-
# Feller continuity of the stopped record kernel

`Swarm/StoppedKernel.lean` builds the finite-horizon stopped record kernel
`hitKernel p hm L` as a genuine Borel kernel, and both its README and
`Swarm/RecordState.lean` list the *Feller property* of the concrete record kernel as
one of the two remaining analytic inputs of the paper's Prop. "front"
(`exists_invariant_measure_pos_srSet`).

This file discharges that input, unconditionally in the parameters: `hitKernel p hm L` is Feller
for every real `p`, every horizon `L` and every truncation level `m ≥ 1`, with no hypothesis on
`p` beyond measurability of the test function structure.

The mechanism is that the kernel is an *explicit finite sum of Dirac masses* at the stopped
record states, with path weights that are continuous in the starting record state
(`PathCont.lean`).  For a bounded continuous test function `f` the integral
`∫ f d(hitKernel p hm L y)` is therefore the finite sum
`∑_{k ≤ L} ∑_{q} hitW p q y * f (out hm q y)`, a finite sum of continuous functions of `y`.
No compactness, no common-path coupling and no almost-sure finiteness of the record time is used;
in particular this holds for the finite-horizon kernel whether or not its total mass is one.

Consequences: with the (separate) mass-one and tightness inputs, the paper's Prop. "front"
holds for the stopped record kernel (`exists_invariant_measure_pos_srSet_hitKernel`).
-/
import Swarm.PathCont

open MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SimJump.RecKernel

open SimJump
open SwarmRec

variable {N m : ℕ}

/-! ### The integral against the stopped record kernel -/

theorem lintegral_finset_sum_measure {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → Measure α) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫⁻ a, g a ∂(μ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, lintegral_add_measure, ih, Finset.sum_insert ha]

/-- The integral of a measurable test function against the stopped record measure is the explicit
finite path sum.  This is the `L¹` counterpart of `hitK_apply`. -/
theorem lintegral_hitK (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m)
    {g : RecState N m → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂(hitK p hm L y) =
      ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
        ENNReal.ofReal (hitW p q y) * g (out hm q y) := by
  classical
  rw [hitK, lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hg]
  simp [smul_eq_mul]

/-! ### Feller continuity -/

theorem continuous_hitK_integral (p : ℝ) (hm : 1 ≤ m) (L : ℕ)
    (f : RecState N m →ᵇ ℝ≥0) :
    Continuous fun y : RecState N m =>
      ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
        hitW p q y * ((f (out hm q y) : ℝ≥0) : ℝ) := by
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun q _ => ?_
  refine (continuous_hitW p k q).mul ?_
  exact (NNReal.continuous_coe.comp f.continuous).comp (continuous_out hm k q)

theorem nonneg_hitK_integral (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (f : RecState N m →ᵇ ℝ≥0) (y : RecState N m) :
    0 ≤ ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
        hitW p q y * ((f (out hm q y) : ℝ≥0) : ℝ) :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (hitW_nonneg p hp hp1 q y) (by positivity)

/-- **The stopped record kernel is Feller.**  For every bounded continuous `f : X →ᵇ ℝ≥0` the
map `y ↦ ∫⁻ z, f z ∂(hitKernel p hm L y)` is again bounded continuous, being the explicit finite
path sum over continuous weights. -/
theorem feller_hitKernel (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ) :
    SwarmKB.Feller (hitKernel (N := N) (m := m) p hm L) := by
  classical
  intro f
  by_cases hne : Nonempty (RecState N m)
  swap
  · exact ⟨f, fun x => absurd ⟨x⟩ hne⟩
  obtain ⟨x₀⟩ := hne
  obtain ⟨C₀, hC₀⟩ := f.map_bounded'
  -- a uniform bound for the real-valued test function
  have hFle : ∀ z : RecState N m, ((f z : ℝ≥0) : ℝ) ≤ C₀ + ((f x₀ : ℝ≥0) : ℝ) := by
    intro z
    have h1 : dist (f z) (f x₀) ≤ C₀ := hC₀ z x₀
    rw [NNReal.dist_eq] at h1
    have h2 : ((f z : ℝ≥0) : ℝ) - ((f x₀ : ℝ≥0) : ℝ) ≤
        |((f z : ℝ≥0) : ℝ) - ((f x₀ : ℝ≥0) : ℝ)| := le_abs_self _
    linarith
  set B : ℝ := C₀ + ((f x₀ : ℝ≥0) : ℝ)
  set G : RecState N m → ℝ := fun y =>
    ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
      hitW p q y * ((f (out hm q y) : ℝ≥0) : ℝ) with hG
  have hGcont : Continuous G := continuous_hitK_integral p hm L f
  have hGnonneg : ∀ y, 0 ≤ G y := nonneg_hitK_integral p hp hp1 hm L f
  have hGle : ∀ y : RecState N m, G y ≤
      ((∑ k ∈ Finset.range (L + 1),
        (Fintype.card (Fin k → JumpVec N) : ℝ)) * B) := by
    intro y
    have hterm : ∀ k ∈ Finset.range (L + 1),
        (∑ q : Fin k → JumpVec N, hitW p q y * ((f (out hm q y) : ℝ≥0) : ℝ)) ≤
          (Fintype.card (Fin k → JumpVec N) : ℝ) * B := by
      intro k _
      calc (∑ q : Fin k → JumpVec N, hitW p q y * ((f (out hm q y) : ℝ≥0) : ℝ))
          ≤ ∑ _q : Fin k → JumpVec N, (1 * B) := by
            refine Finset.sum_le_sum fun q _ => ?_
            refine mul_le_mul (hitW_le_one p hp hp1 q y) (hFle _) (by positivity) ?_
            exact zero_le_one
        _ = (Fintype.card (Fin k → JumpVec N) : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
    calc G y ≤ ∑ k ∈ Finset.range (L + 1), (Fintype.card (Fin k → JumpVec N) : ℝ) * B :=
          Finset.sum_le_sum hterm
      _ = ((∑ k ∈ Finset.range (L + 1),
            (Fintype.card (Fin k → JumpVec N) : ℝ)) * B) := (Finset.sum_mul ..).symm
  set Kg : ℝ := (∑ k ∈ Finset.range (L + 1), (Fintype.card (Fin k → JumpVec N) : ℝ)) * B
  -- the candidate bounded continuous function
  have hGbound : ∀ x y : RecState N m, dist (G x) (G y) ≤ 2 * Kg := by
    intro x y
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hGnonneg x, hGnonneg y, hGle x, hGle y]
  set g : RecState N m →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨G, hGcont⟩ (2 * Kg) hGbound with hgdef
  refine ⟨g.comp Real.toNNReal Real.lipschitzWith_toNNReal, fun y => ?_⟩
  have hval : (((g.comp Real.toNNReal Real.lipschitzWith_toNNReal) y : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (G y) := rfl
  rw [hval]
  -- convert the real sum into the `ℝ≥0∞` sum
  have hconv : ENNReal.ofReal (G y) =
      ∑ k ∈ Finset.range (L + 1), ∑ q : Fin k → JumpVec N,
        ENNReal.ofReal (hitW p q y) * ((f (out hm q y) : ℝ≥0) : ℝ≥0∞) := by
    rw [hG]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [ENNReal.ofReal_mul (hitW_nonneg p hp hp1 q y), ENNReal.ofReal_coe_nnreal]
      · intro q _
        exact mul_nonneg (hitW_nonneg p hp hp1 q y) (by positivity)
    · intro k _
      exact Finset.sum_nonneg fun q _ =>
        mul_nonneg (hitW_nonneg p hp hp1 q y) (by positivity)
  rw [hconv]
  have hg : Measurable fun z : RecState N m => ((f z : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp f.continuous).measurable
  rw [← lintegral_hitK (N := N) (m := m) p hm L y hg]
  rfl

/-! ### Prop. "front" for the stopped record kernel, with the Feller input eliminated -/

/-- **Prop. "front" for the stopped record kernel.**  Given only the two genuinely probabilistic
inputs that remain -- the horizon-`L` stopped law is a probability law (the record time is at most
`L` almost surely) and its iterates are tight -- there is an invariant probability measure
charging the simultaneous-record set `srSet N m` with positive mass.  The Feller hypothesis of
`SwarmRec.exists_invariant_measure_pos_srSet` is discharged by `feller_hitKernel`. -/
theorem exists_invariant_measure_pos_srSet_hitKernel (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ m) (L : ℕ)
    (hmarkov : ∀ y : RecState N m, hitK p hm L y Set.univ = 1)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKernel p hm L))^[r] μ (exh N m K)ᶜ ≤ ε)
    (hforce : ∀ K : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ y : RecState N m, y ∈ exh N m K →
       hitKernel p hm L y (srSet N m) ≥ c) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      ProbabilityTheory.Kernel.Invariant (hitKernel p hm L) π ∧ 0 < π (srSet N m) := by
  haveI : IsMarkovKernel (hitKernel (N := N) (m := m) p hm L) :=
    isMarkovKernel_hitKernel_of_mass_one p hm L hmarkov
  exact exists_invariant_measure_pos_srSet (κ := hitKernel p hm L) (feller_hitKernel p hp hp1 hm L)
    μ htight hforce

end SimJump.RecKernel


