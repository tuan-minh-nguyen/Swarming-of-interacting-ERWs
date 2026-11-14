/-
  Tail bounds and the almost-sure logarithmic growth of `h_j` (display (Kmom) of
  Proposition "spatial", `h`-part).

  From the exponential moment bound `exists_exp_moment_hof` we get, by Markov's inequality
  and a union bound over the `n+2` sites `0, …, n+1`,

      P ( max_{x <= n+1} h(x) > u ) ≤ C (n+2) e^{-θ u},

  and with `u_n = (3/θ) log (n+2)` the first Borel–Cantelli lemma gives

      max_{0 <= x <= n+1} h(x) = O (log (n+2))   almost surely.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

/-! ### Markov's inequality for the `lintegral` -/

lemma mul_measure_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (a : ℝ≥0∞) :
    a * μ {x | a ≤ f x} ≤ ∫⁻ x, f x ∂μ := by
  have hsm : MeasurableSet {x | a ≤ f x} := measurableSet_le measurable_const hf
  have h : a * μ {x | a ≤ f x} = ∫⁻ x in {x | a ≤ f x}, a ∂μ := by
    rw [setLIntegral_const]
  rw [h]
  calc ∫⁻ x in {x | a ≤ f x}, a ∂μ
      ≤ ∫⁻ x in {x | a ≤ f x}, f x ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hsm] with x hx using hx
    _ ≤ ∫⁻ x, f x ∂μ := by
        rw [← lintegral_indicator hsm]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x | a ≤ f x}
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]

/-! ### The tail of `h(x)` -/

/-- The constant `M = e^{3θ} + C/(1-γ)` of the exponential moment bound. -/
def momConst (p q θ γ : ℝ) : ℝ :=
  Real.exp (3 * θ) + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ)

/-- **Exponential tail of `h(x)`.**  For every site `x` and every `u`,
`P (u ≤ h(x)) ≤ M exp (-θ u)`. -/
theorem hof_tail_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x : ℕ) (u : ℝ) :
    markMeasure (boolMeasure q) {ω : ℕ → Bool | u ≤ hof p ω x}
      ≤ ENNReal.ofReal (momConst p q θ γ * Real.exp (-(θ * u))) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hp0 : p ≠ 0 := by linarith
  have hmeas : Measurable (fun ω : ℕ → Bool => ENNReal.ofReal (Real.exp (θ * hof p ω x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_hof hp0 x)))
  have hM := lintegral_exp_hof_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x
  -- the two events agree
  have hiff : ∀ (ω : ℕ → Bool),
      (ENNReal.ofReal (Real.exp (θ * u))
        ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))) ↔ u ≤ hof p ω x := by
    intro ω
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h hθ, fun h => mul_le_mul_of_nonneg_left h hθ.le⟩
  have hset : {ω : ℕ → Bool | u ≤ hof p ω x}
      = {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
          ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hiff]
  rw [hset]
  have hmk := mul_measure_le_lintegral (μ := markMeasure (boolMeasure q)) hmeas
    (ENNReal.ofReal (Real.exp (θ * u)))
  have hchain := le_trans hmk hM
  rw [mul_comm] at hchain
  have hfin : ENNReal.ofReal (Real.exp (θ * u)) ≠ 0 := by simp [Real.exp_pos]
  have htop : ENNReal.ofReal (Real.exp (θ * u)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : (markMeasure (boolMeasure q))
      {ω : ℕ → Bool | ENNReal.ofReal (Real.exp (θ * u))
        ≤ ENNReal.ofReal (Real.exp (θ * hof p ω x))}
      ≤ ENNReal.ofReal (momConst p q θ γ) / ENNReal.ofReal (Real.exp (θ * u)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfin) (Or.inl htop)]
    exact hchain
  refine hdiv.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), Real.exp_neg, div_eq_mul_inv]

/-! ### Union bound over the sites `0, …, n+1` -/

theorem hof_max_tail_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (n : ℕ) (u : ℝ) :
    markMeasure (boolMeasure q) {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2), u ≤ hof p ω x}
      ≤ (n + 2 : ℝ≥0∞) * ENNReal.ofReal (momConst p q θ γ * Real.exp (-(θ * u))) := by
  have hset : {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2), u ≤ hof p ω x}
      = ⋃ x ∈ Finset.range (n + 2), {ω : ℕ → Bool | u ≤ hof p ω x} := by
    ext ω
    simp
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hsingle : ∀ x ∈ Finset.range (n + 2),
      markMeasure (boolMeasure q) {ω : ℕ → Bool | u ≤ hof p ω x}
        ≤ ENNReal.ofReal (momConst p q θ γ * Real.exp (-(θ * u))) := fun x _ =>
    hof_tail_bound hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x u
  refine (Finset.sum_le_sum hsingle).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Display (Kmom), `h`-part.**  Almost surely, `h(x) = O (log (n+2))` uniformly over the
sites `0 ≤ x ≤ n+1`. -/
theorem hof_eventually_log_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ≤ n + 1, hof p ω x ≤ (3 / θ) * Real.log ((n : ℝ) + 2) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0.le hq1
  -- the majorant series is summable
  have hsumR : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) := by
    have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
      have h2 := (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ)) ^ 2) 2).mpr h0
      simpa [Nat.cast_add, Nat.cast_ofNat] using h2
    refine h1.congr fun n => ?_
    simp [one_div]
  have hMnn : 0 ≤ momConst p q θ γ := by
    unfold momConst
    have h2 : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
      have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
      have : 0 ≤ 1 - (1 - p) / p := by linarith
      positivity
    have h3 : 0 < 1 - γ := by linarith
    have h4 : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := div_nonneg h2 h3.le
    have h5 : 0 ≤ Real.exp (3 * θ) := (Real.exp_pos _).le
    linarith
  have hterm : ∀ n : ℕ,
      markMeasure (boolMeasure q) {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
        (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x}
      ≤ ENNReal.ofReal (momConst p q θ γ) * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹) := by
    intro n
    refine (hof_max_tail_bound hp1 hp2 hq0.le hq1 hθ hγpos hγ1 hγ n
      ((3 / θ) * Real.log ((n : ℝ) + 2))).trans ?_
    have hcast : ((n : ℝ≥0∞) + 2) = ENNReal.ofReal ((n : ℝ) + 2) := by
      rw [← ENNReal.ofReal_natCast (n := n), ← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ (n:ℝ)) (by norm_num : (0:ℝ) ≤ 2)]
    have hexp : Real.exp (-(θ * ((3 / θ) * Real.log ((n : ℝ) + 2))))
        = (((n : ℝ) + 2) ^ 3)⁻¹ := by
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have h1 : θ * ((3 / θ) * Real.log ((n : ℝ) + 2)) = 3 * Real.log ((n : ℝ) + 2) := by
        field_simp
      rw [h1, show (3:ℝ) * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 3) by
        rw [Real.log_pow]; push_cast; ring]
      rw [Real.exp_neg, Real.exp_log (by positivity)]
    rw [show ((n : ℝ≥0∞) + 2) = ENNReal.ofReal ((n : ℝ) + 2) from hcast, hexp,
      ← ENNReal.ofReal_mul hMnn]
    refine le_of_eq ?_
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((n : ℝ) + 2))]
    congr 1
    field_simp
  have htsum : (∑' n : ℕ, ENNReal.ofReal (momConst p q θ γ)
      * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹)) ≠ ⊤ := by
    calc (∑' n : ℕ, ENNReal.ofReal (momConst p q θ γ)
        * ENNReal.ofReal ((((n : ℝ) + 2) ^ 2)⁻¹))
        = ∑' n : ℕ, ENNReal.ofReal (momConst p q θ γ * (((n : ℝ) + 2) ^ 2)⁻¹) := by
          refine tsum_congr fun n => ?_
          rw [ENNReal.ofReal_mul hMnn]
      _ = ENNReal.ofReal (∑' n : ℕ, momConst p q θ γ * (((n : ℝ) + 2) ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsumR.mul_left _)]
      _ = ENNReal.ofReal (momConst p q θ γ * ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹) := by
          rw [tsum_mul_left]
      _ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Borel–Cantelli
  have htsumA : (∑' n : ℕ, (markMeasure (boolMeasure q))
      {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
        (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x}) ≠ ⊤ :=
    ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum hterm)
  have hbc := MeasureTheory.ae_eventually_notMem
    (μ := markMeasure (boolMeasure q))
    (s := fun n => {ω : ℕ → Bool | ∃ x ∈ Finset.range (n + 2),
      (3 / θ) * Real.log ((n : ℝ) + 2) ≤ hof p ω x}) htsumA
  filter_upwards [hbc] with ω hω
  filter_upwards [hω] with n hn x hx
  by_contra hcon
  exact hn ⟨x, Finset.mem_range.mpr (by omega), le_of_lt (not_le.mp hcon)⟩

end

end SwarmMarks
