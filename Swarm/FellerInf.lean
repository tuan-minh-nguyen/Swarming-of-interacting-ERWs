/-
# Feller continuity of the horizon-free stopped record kernel

`Swarm/InfKernel.lean` builds the horizon-free stopped record law
`hitKInf p hm y` as the countable sum over all finite first-record paths and shows it is a genuine
probability kernel (`hitKKernel`, `isMarkovKernel_hitKKernel`); the only remaining inputs of
Prop. "front" for it are the Feller property and tightness of the iterates.

Here the Feller property is proved.  Ingredients, all previously verified:

* the finite-horizon kernels are Feller (`Feller.lean`), unconditionally;
* the finite-horizon stopped laws are dominated by the horizon-free one, and their total masses
  increase to one (`InfKernel.lean`);
* the *uniform* tail estimate `one_sub_hitMass_le` of `Swarm/MassOne.lean`
  (`1 - hitMass p L y ≤ 3√2/√(L+1)`, the bound being independent of the record state `y`).

For a test function bounded by `B`, the integrals against the two laws are sandwiched within
`B * 3√2/√(L+1)` uniformly in `y`, and a uniform limit of continuous functions is continuous.
Hence the horizon-free integral is continuous, i.e. `hitKKernel` is Feller.

Consequence: `exists_invariant_measure_pos_hitKInf_feller` gives the paper's Prop. "front" for the
genuine stopped record kernel with *tightness of the iterates* as the only remaining hypothesis.
-/
import Swarm.Feller
import Swarm.InfKernel

open MeasureTheory ProbabilityTheory Topology Filter
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SimJump.RecKernel

open SimJump
open SwarmRec

variable {N m : ℕ}

/-! ### Dominance of the finite-horizon laws -/

/-- The horizon-`L` stopped record law is dominated, as a measure, by the horizon-free one. -/
theorem hitK_le_hitKInf_measure (p : ℝ) (hm : 1 ≤ m) (L : ℕ) (y : RecState N m) :
    hitK p hm L y ≤ hitKInf p hm y := by
  rw [Measure.le_iff]
  intro A hA
  exact hitK_le_hitKInf p hm L y hA

/-! ### A domination estimate for integrals -/

/-- If `μ ≤ ν`, `μ` is finite and `g ≤ B`, then the integral of `g` against `ν` exceeds the
integral against `μ` by at most `B` times the excess total mass of `ν`. -/
theorem lintegral_le_add_mass_sub {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] (hμν : μ ≤ ν) {g : α → ℝ≥0∞} {B : ℝ≥0∞} (hg : ∀ x, g x ≤ B) :
    ∫⁻ x, g x ∂ν ≤ ∫⁻ x, g x ∂μ + B * (ν Set.univ - μ Set.univ) := by
  have hdec : (ν - μ) + μ = ν := Measure.sub_add_cancel_of_le hμν
  have htail : ∫⁻ x, g x ∂(ν - μ) ≤ B * (ν - μ) Set.univ := by
    calc ∫⁻ x, g x ∂(ν - μ) ≤ ∫⁻ _x, B ∂(ν - μ) := lintegral_mono hg
      _ = B * (ν - μ) Set.univ := lintegral_const B
  calc ∫⁻ x, g x ∂ν = ∫⁻ x, g x ∂((ν - μ) + μ) := by rw [hdec]
    _ = ∫⁻ x, g x ∂(ν - μ) + ∫⁻ x, g x ∂μ := lintegral_add_measure _ _ _
    _ ≤ B * (ν - μ) Set.univ + ∫⁻ x, g x ∂μ := by gcongr
    _ = B * (ν Set.univ - μ Set.univ) + ∫⁻ x, g x ∂μ := by
        rw [Measure.sub_apply MeasurableSet.univ hμν]
    _ = ∫⁻ x, g x ∂μ + B * (ν Set.univ - μ Set.univ) := by rw [add_comm]

/-- A uniform bound on a test function gives a uniform bound on its integral against the
horizon-free stopped law, which is a probability law. -/
theorem lintegral_hitKInf_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (f : RecState N m →ᵇ ℝ≥0) {B : ℝ} (hB : ∀ z, ((f z : ℝ≥0) : ℝ) ≤ B)
    (y : RecState N m) :
    ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y) ≤ ENNReal.ofReal B := by
  calc ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)
      ≤ ∫⁻ _z, ENNReal.ofReal B ∂(hitKInf p hm y) :=
        lintegral_mono fun z => by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hB z)
    _ = ENNReal.ofReal B * hitKInf p hm y Set.univ := lintegral_const _
    _ = ENNReal.ofReal B := by rw [hitKInf_univ p hp hp1 hm y, mul_one]

/-- The same bound for the finite-horizon stopped law. -/
theorem lintegral_hitK_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (f : RecState N m →ᵇ ℝ≥0) {B : ℝ} (hB : ∀ z, ((f z : ℝ≥0) : ℝ) ≤ B)
    (y : RecState N m) :
    ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) ≤ ENNReal.ofReal B := by
  calc ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)
      ≤ ∫⁻ _z, ENNReal.ofReal B ∂(hitK p hm L y) :=
        lintegral_mono fun z => by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hB z)
    _ = ENNReal.ofReal B * hitK p hm L y Set.univ := lintegral_const _
    _ = ENNReal.ofReal B * ENNReal.ofReal (hitMass p L y) := by
        rw [hitK_univ p hp hp1 hm L y]
    _ ≤ ENNReal.ofReal B * 1 := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hitMass_le_one p hp hp1 hm L y)
    _ = ENNReal.ofReal B := mul_one _

theorem hitMass_nonneg' (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (L : ℕ) (y : RecState N m) :
    0 ≤ hitMass p L y := by
  rw [hitMass]
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun q _ => hitW_nonneg p hp hp1 q y

/-! ### The uniform tail bound for integrals -/

/-- **Uniform sandwich.**  For a test function bounded by `B`, the horizon-free integral differs
from the horizon-`L` integral by at most `B * 3√2/√(L+1)`, uniformly in the starting record
state. -/
theorem hitKInf_lintegral_tail (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (f : RecState N m →ᵇ ℝ≥0) {B : ℝ} (hB : ∀ z, ((f z : ℝ≥0) : ℝ) ≤ B) (y : RecState N m) :
    ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y) ≤
      ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
        ENNReal.ofReal B *
          ENNReal.ofReal (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) := by
  haveI hfin : IsFiniteMeasure (hitK p hm L y) := ⟨hitK_univ_lt_top p hp hp1 hm L y⟩
  have hstep := lintegral_le_add_mass_sub (hitK_le_hitKInf_measure p hm L y)
    (g := fun z => ((f z : ℝ≥0) : ℝ≥0∞)) (B := ENNReal.ofReal B)
    (fun z => by simpa using ENNReal.ofReal_le_ofReal (hB z))
  have hsub0 := Measure.sub_apply (μ := hitKInf p hm y) (ν := hitK p hm L y) (s := Set.univ)
    MeasurableSet.univ (hitK_le_hitKInf_measure p hm L y)
  have hsub := hsub0
  rw [hitKInf_univ p hp hp1 hm y, hitK_univ p hp hp1 hm L y] at hsub
  have hmass : (hitKInf p hm y Set.univ - hitK p hm L y Set.univ) =
      ENNReal.ofReal (1 - hitMass p L y) := by
    rw [show hitKInf p hm y Set.univ - hitK p hm L y Set.univ
        = (hitKInf p hm y - hitK p hm L y) Set.univ from hsub0.symm, hsub,
      ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_sub 1 (hitMass_nonneg' p hp hp1 L y)).symm
  have hmono : ENNReal.ofReal (1 - hitMass p L y) ≤
      ENNReal.ofReal (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal (one_sub_hitMass_le p hp hp1 hm L y)
  calc ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)
      ≤ ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
          ENNReal.ofReal B * (hitKInf p hm y Set.univ - hitK p hm L y Set.univ) := hstep
    _ = ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
          ENNReal.ofReal B * ENNReal.ofReal (1 - hitMass p L y) := by rw [hmass]
    _ ≤ ∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
          ENNReal.ofReal B * ENNReal.ofReal (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) := by
        gcongr

/-! ### Uniform limits of continuous functions -/

/-- A function sandwiched, uniformly in the point, between a continuous family and that family
plus a vanishing sequence of errors is continuous. -/
theorem continuous_of_uniform_sandwich {X : Type*} [TopologicalSpace X] {Φ : X → ℝ}
    {h : ℕ → X → ℝ} {δ : ℕ → ℝ} (hcont : ∀ L, Continuous (h L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsand : ∀ (L : ℕ) (x : X), h L x ≤ Φ x ∧ Φ x ≤ h L x + δ L) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [show ContinuousAt Φ x₀ ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, dist (Φ x) (Φ x₀) < ε from
    Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hev : ∀ᶠ L : ℕ in atTop, δ L < ε / 3 := (tendsto_order.1 hδ).2 _ hε3
  obtain ⟨L, hL⟩ := hev.exists
  have hLcont : ∀ᶠ x in 𝓝 x₀, dist (h L x) (h L x₀) < ε / 3 :=
    Metric.tendsto_nhds.1 (hcont L).continuousAt (ε / 3) hε3
  filter_upwards [hLcont] with x hx
  have h1 : |Φ x - h L x| < ε / 3 := by
    rw [abs_of_nonneg (by linarith [(hsand L x).1])]
    linarith [(hsand L x).2, hL]
  have h1' : |Φ x₀ - h L x₀| < ε / 3 := by
    rw [abs_of_nonneg (by linarith [(hsand L x₀).1])]
    linarith [(hsand L x₀).2, hL]
  have h2 : |h L x - h L x₀| < ε / 3 := hx
  rw [Real.dist_eq]
  have htri : Φ x - Φ x₀ = (Φ x - h L x) + (h L x - h L x₀) + (h L x₀ - Φ x₀) := by ring
  rw [htri]
  calc |(Φ x - h L x) + (h L x - h L x₀) + (h L x₀ - Φ x₀)|
      ≤ |(Φ x - h L x) + (h L x - h L x₀)| + |h L x₀ - Φ x₀| := abs_add_le _ _
    _ ≤ |Φ x - h L x| + |h L x - h L x₀| + |h L x₀ - Φ x₀| := by
        have h := abs_add_le (Φ x - h L x) (h L x - h L x₀)
        linarith
    _ < ε := by
        have h3 : |h L x₀ - Φ x₀| = |Φ x₀ - h L x₀| := abs_sub_comm _ _
        rw [h3]; linarith

/-! ### Continuity of the horizon-free integral -/

theorem continuous_hitKInf_lintegral_toReal (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (f : RecState N m →ᵇ ℝ≥0) (x₀ : RecState N m)
    {B : ℝ} (hB : ∀ z, ((f z : ℝ≥0) : ℝ) ≤ B) :
    Continuous fun y : RecState N m =>
      (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal := by
  classical
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB x₀)
  -- the finite-horizon integrals as continuous functions
  have hLcont : ∀ L : ℕ, Continuous fun y : RecState N m =>
      (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal := by
    intro L
    obtain ⟨hL, hLval⟩ := feller_hitKernel (N := N) (m := m) p hp hp1 hm L f
    have hEq : (fun y : RecState N m =>
        (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal) =
        fun y => ((hL y : ℝ≥0) : ℝ) := by
      funext y
      have h1 : (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKernel p hm L y)).toReal =
          ((hL y : ℝ≥0) : ℝ) := by
        rw [← hLval y, ENNReal.coe_toReal]
      simpa [hitKernel_apply] using h1
    rw [hEq]
    exact NNReal.continuous_coe.comp hL.continuous
  -- the uniform sandwich
  have hsand : ∀ (L : ℕ) (y : RecState N m),
      (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal ≤
        (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal ∧
      (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal ≤
        (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal +
          B * (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) := by
    intro L y
    haveI hfin : IsFiniteMeasure (hitK p hm L y) := ⟨hitK_univ_lt_top p hp hp1 hm L y⟩
    have hIInf := lintegral_hitKInf_le p hp hp1 hm f hB y
    have hIL := lintegral_hitK_le p hp hp1 hm L f hB y
    have hIInftop : (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hIInf
    have hILtop : (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hIL
    constructor
    · exact ENNReal.toReal_mono hIInftop (lintegral_mono' (hitK_le_hitKInf_measure p hm L y)
        le_rfl)
    · have hb := hitKInf_lintegral_tail p hp hp1 hm L f hB y
      have hsumtop : (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
          ENNReal.ofReal B *
            ENNReal.ofReal (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1))) ≠ ⊤ :=
        (ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hIL ENNReal.ofReal_lt_top,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩).ne
      calc (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal
          ≤ (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y) +
              ENNReal.ofReal B * ENNReal.ofReal
                (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1))).toReal :=
            ENNReal.toReal_mono hsumtop hb
        _ = (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal +
              (ENNReal.ofReal B *
                ENNReal.ofReal (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1))).toReal :=
            ENNReal.toReal_add hILtop (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne
              ENNReal.ofReal_lt_top.ne)
        _ = (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal +
              B * (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal]
            positivity
  refine continuous_of_uniform_sandwich (h := fun (L : ℕ) (y : RecState N m) =>
    (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitK p hm L y)).toReal)
    (δ := fun L => B * (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1))) hLcont ?_ hsand
  have hsq : Tendsto (fun L : ℕ => Real.sqrt ((L : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun L : ℕ => (Real.sqrt ((L : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  have hrate : Tendsto (fun L : ℕ => 3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 3 * Real.sqrt 2) (f := (atTop : Filter ℕ))).mul hinv
    simpa [div_eq_mul_inv] using h
  have := (tendsto_const_nhds (x := B) (f := (atTop : Filter ℕ))).mul hrate
  simpa using this

/-! ### Feller continuity of the horizon-free stopped record kernel -/

theorem feller_hitKKernel (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) :
    SwarmKB.Feller (hitKKernel (N := N) (m := m) p hm) := by
  classical
  intro f
  by_cases hne : Nonempty (RecState N m)
  swap
  · exact ⟨f, fun x => absurd ⟨x⟩ hne⟩
  obtain ⟨x₀⟩ := hne
  obtain ⟨C₀, hC₀⟩ := f.map_bounded'
  have hble : ∀ z : RecState N m, ((f z : ℝ≥0) : ℝ) ≤ C₀ + ((f x₀ : ℝ≥0) : ℝ) := by
    intro z
    have h1 : dist (f z) (f x₀) ≤ C₀ := hC₀ z x₀
    rw [NNReal.dist_eq] at h1
    have h2 : ((f z : ℝ≥0) : ℝ) - ((f x₀ : ℝ≥0) : ℝ) ≤
        |((f z : ℝ≥0) : ℝ) - ((f x₀ : ℝ≥0) : ℝ)| := le_abs_self _
    linarith
  set B : ℝ := C₀ + ((f x₀ : ℝ≥0) : ℝ) with hBdef
  have hB : ∀ z : RecState N m, ((f z : ℝ≥0) : ℝ) ≤ B := hble
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB x₀)
  set Φ : RecState N m → ℝ := fun y =>
    (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal with hΦdef
  have hΦcont : Continuous Φ := continuous_hitKInf_lintegral_toReal p hp hp1 hm f x₀ hB
  have hΦnonneg : ∀ y, 0 ≤ Φ y := fun y => ENNReal.toReal_nonneg
  have hΦle : ∀ y, Φ y ≤ B := by
    intro y
    have h := lintegral_hitKInf_le p hp hp1 hm f hB y
    calc Φ y = (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)).toReal := rfl
      _ ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne h
      _ = B := ENNReal.toReal_ofReal hB0
  have hreal : ∀ x y : RecState N m, dist (Φ x) (Φ y) ≤ 2 * B := by
    intro x y
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hΦnonneg x, hΦnonneg y, hΦle x, hΦle y]
  refine ⟨(BoundedContinuousFunction.mkOfBound ⟨Φ, hΦcont⟩ (2 * B) hreal).comp
    Real.toNNReal Real.lipschitzWith_toNNReal, fun y => ?_⟩
  have hIInf : (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(hitKInf p hm y)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne (lintegral_hitKInf_le p hp hp1 hm f hB y)
  have hval : ((((BoundedContinuousFunction.mkOfBound ⟨Φ, hΦcont⟩ (2 * B) hreal).comp
      Real.toNNReal Real.lipschitzWith_toNNReal) y : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Φ y) := rfl
  rw [hval, ENNReal.ofReal_toReal hIInf]
  rfl

/-! ### Prop. "front" for the genuine stopped record kernel -/

/-- **Prop. "front" with the Feller input eliminated.**  For the genuine horizon-free stopped
record kernel, the force estimate and the Markov property are already proved, and the Feller
property is `feller_hitKKernel`; so tightness of the iterates is the only remaining hypothesis for
the existence of an invariant probability measure charging the simultaneous-record set. -/
theorem exists_invariant_measure_pos_hitKInf_feller (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) (hm : 1 ≤ m) (hN : 0 < N)
    (μ : Measure (RecState N m)) [IsProbabilityMeasure μ]
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ r : ℕ,
      (SwarmKB.step (hitKKernel (N := N) (m := m) p hm))^[r] μ (exh N m K)ᶜ ≤ ε) :
    ∃ π : Measure (RecState N m), IsProbabilityMeasure π ∧
      Kernel.Invariant (hitKKernel (N := N) (m := m) p hm) π ∧ 0 < π (srSet N m) :=
  exists_invariant_measure_pos_hitKInf p hp hp1 hp_lt hm hN (feller_hitKKernel p hp hp1 hm)
    μ htight

end SimJump.RecKernel


