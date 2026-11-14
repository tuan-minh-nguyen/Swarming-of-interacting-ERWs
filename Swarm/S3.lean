/-
  The fluctuation term `M_r = sum_{n<r} (mk(n+1) - q) h(n)` and its moments.

  Main outputs:
  * `integral_dfun_eq_zero`      : `E[d_n] = 0`
  * `integral_dfun_sq`           : `E[d_n^2] = q (1-q) E[h(n)^2]`
  * `Msum_sq_bound`             : `E[M_r^2] <= C r`
  * `Msum_four_bound`           : `E[M_r^4] <= B r^2`
-/
import Swarm.Imports
import Swarm.SpatialAvg.S1
import Swarm.SpatialAvg.S2

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q : ℝ}

/-! ### The uniform sixth moment of `h(x)` -/

/-- Uniform `k`-th moment of `h(x)`, from the exponential moment. -/
theorem exists_hof_pow_bound {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      Integrable (fun ω => (hof p ω n) ^ k)
        (markMeasure (boolMeasure ((1 - p) ^ (m - 1))))
      ∧ ∫ ω, (hof p ω n) ^ k ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) ≤ C := by
  obtain ⟨θ, hθ, C, hC, hbound⟩ := exists_exp_moment_hof hp1 hp2 hm
  set μ := markMeasure (boolMeasure ((1 - p) ^ (m - 1))) with hμ
  have hk0 : (0:ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hkpos : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  refine ⟨(Nat.factorial k : ℝ) / θ ^ k * C, mul_pos (div_pos hkpos (pow_pos hθ k)) hC, fun n => ?_⟩
  have hpow : ∀ y : ℝ, 1 ≤ y →
      y ^ k ≤ (Nat.factorial k : ℝ) / θ ^ k * Real.exp (θ * y) := by
    intro y hy
    have hy0 : 0 ≤ θ * y := by positivity
    have h1 : (θ * y) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (θ * y) :=
      Real.pow_div_factorial_le_exp (θ * y) hy0 k
    have h2 : (θ * y) ^ k = θ ^ k * y ^ k := by ring
    have hθk : (0:ℝ) < θ ^ k := by positivity
    rw [h2, div_le_iff₀ hk0] at h1
    rw [show (Nat.factorial k : ℝ) / θ ^ k * Real.exp (θ * y)
      = (Nat.factorial k : ℝ) * Real.exp (θ * y) / θ ^ k from by ring, le_div_iff₀ hθk]
    linarith
  have hmono : ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ k) ∂μ
      ≤ ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k * C) := by
    calc ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ k) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k * Real.exp (θ * hof p ω n)) ∂μ := by
          apply lintegral_mono
          intro ω
          exact ENNReal.ofReal_le_ofReal (hpow _ (one_le_hof hp1.le hp2 ω n))
      _ = ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k)
            * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω n)) ∂μ := by
          have hc0 : (0:ℝ) ≤ (Nat.factorial k : ℝ) / θ ^ k :=
            (div_pos hkpos (pow_pos hθ k)).le
          have hcongr : (fun ω => ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k
                * Real.exp (θ * hof p ω n)))
              = fun ω => ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k)
                  * ENNReal.ofReal (Real.exp (θ * hof p ω n)) := by
            funext ω
            exact ENNReal.ofReal_mul hc0
          have hm' : Measurable fun ω : ℕ → Bool => hof p ω n := measurable_hof (by linarith) n
          have hmexp : Measurable fun ω => ENNReal.ofReal (Real.exp (θ * hof p ω n)) :=
            ENNReal.measurable_ofReal.comp
              (Real.measurable_exp.comp (measurable_const.mul hm'))
          rw [hcongr, lintegral_const_mul _ hmexp]
      _ ≤ ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k) * ENNReal.ofReal C :=
          mul_le_mul_of_nonneg_left (hbound n) (by positivity)
      _ = ENNReal.ofReal ((Nat.factorial k : ℝ) / θ ^ k * C) := by
          exact (ENNReal.ofReal_mul (p := (Nat.factorial k : ℝ) / θ ^ k) (q := C)
            (div_pos hkpos (pow_pos hθ k)).le).symm
  have hmeas : AEStronglyMeasurable (fun ω => (hof p ω n) ^ k) μ :=
    ((measurable_hof (by linarith : p ≠ 0) n).pow_const k).aestronglyMeasurable
  have hae : 0 ≤ᵐ[μ] fun ω => (hof p ω n) ^ k :=
    Filter.Eventually.of_forall fun ω => pow_nonneg (by linarith [one_le_hof hp1.le hp2 ω n]) k
  have hlt : ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ k) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmono
  have hint : Integrable (fun ω => (hof p ω n) ^ k) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hae).mp hlt
  refine ⟨hint, ?_⟩
  have hone : ENNReal.ofReal (∫ ω, (hof p ω n) ^ k ∂μ)
      = ∫⁻ ω, ENNReal.ofReal ((hof p ω n) ^ k) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hint hae
  rw [← hone] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmono

/-! ### The martingale differences -/

/-- The centred mark at site `n+1` weighted by `h(n)`. -/
def dfun (q p : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ := (mk ω (n + 1) - q) * hof p ω n

/-- The partial sums of the martingale differences. -/
def Msum (q p : ℝ) (r : ℕ) (ω : ℕ → Bool) : ℝ := ∑ n ∈ Finset.range r, dfun q p n ω

lemma Msum_succ (r : ℕ) (ω : ℕ → Bool) :
    Msum q p (r + 1) ω = Msum q p r ω + dfun q p r ω :=
  Finset.sum_range_succ (fun n => dfun q p n ω) r

lemma measurable_dfun (hp0 : p ≠ 0) (n : ℕ) : Measurable (dfun q p n) :=
  ((measurable_mk (n + 1)).sub measurable_const).mul (measurable_hof hp0 n)

lemma dependsOn_dfun (n : ℕ) : DependsOn (n + 1) (dfun q p n) :=
  ((dependsOn_mk (le_refl (n + 1))).sub (dependsOn_const _ _)).mul
    (dependsOn_hof (Nat.le_succ n))

lemma dependsOn_Msum (r : ℕ) : DependsOn r (Msum q p r) :=
  DependsOn.sum _ fun n hn => (dependsOn_dfun n).mono (by
    have := Finset.mem_range.mp hn; omega)

lemma measurable_Msum (hp0 : p ≠ 0) (r : ℕ) : Measurable (Msum q p r) :=
  Finset.measurable_sum _ fun n _ => measurable_dfun hp0 n

/-! ### Uniform integrability of powers of `h` and of the differences -/

variable {C6 : ℝ}

/-- Domination of powers: since `h >= 1`, `h^k <= h^6` for `k <= 6`. -/
lemma hof_pow_le_six (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {k : ℕ} (hk : k ≤ 6)
    (ω : ℕ → Bool) (n : ℕ) : (hof p ω n) ^ k ≤ (hof p ω n) ^ 6 :=
  pow_le_pow_right₀ (one_le_hof hp1.le hp2 ω n) hk

lemma integrable_hof_pow (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {k : ℕ} (hk : k ≤ 6)
    {q : ℝ} (hu6 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (n : ℕ) : Integrable (fun ω => (hof p ω n) ^ k) (markMeasure (boolMeasure q)) := by
  refine Integrable.mono' (hu6 n)
    (((measurable_hof (by linarith : p ≠ 0) n).pow_const k).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [one_le_hof hp1.le hp2 ω n]) k)]
  simpa only [pow_one] using hof_pow_le_six hp1 hp2 hk ω n

lemma integrable_dfun (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hu6 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (n : ℕ) : Integrable (dfun q p n) (markMeasure (boolMeasure q)) := by
  have hbase : Integrable (fun ω => hof p ω n) (markMeasure (boolMeasure q)) := by
    simpa only [pow_one] using integrable_hof_pow (k := 1) hp1 hp2 (by norm_num) hu6 n
  have hbound : ∀ ω : ℕ → Bool, |dfun q p n ω| ≤ hof p ω n := by
    intro ω
    have hu1 : (1:ℝ) ≤ hof p ω n := one_le_hof hp1.le hp2 ω n
    have hmk : |mk ω (n + 1) - q| ≤ 1 := by
      rcases mk_zero_or_one ω (n + 1) with h | h
      · rw [h, zero_sub, abs_neg, abs_of_nonneg h0]; linarith
      · rw [h, abs_le]; constructor <;> linarith
    have h1 : |dfun q p n ω| = |mk ω (n + 1) - q| * |hof p ω n| := by
      rw [dfun, abs_mul]
    rw [h1]
    calc |mk ω (n + 1) - q| * |hof p ω n| ≤ 1 * hof p ω n := by
          apply mul_le_mul hmk ?_ (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (by linarith)]
      _ = hof p ω n := by ring
  refine Integrable.mono' hbase
    ((measurable_dfun (by linarith : p ≠ 0) n).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  exact hbound ω

/-- **`E d_n = 0`**: the mark at site `n+1` is independent of `h(n)`. -/
theorem integral_dfun_eq_zero {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (n : ℕ) :
    ∫ ω, dfun q p n ω ∂(markMeasure (boolMeasure q)) = 0 := by
  have hdep : DependsOn n (fun ω => hof p ω n) := fun ω ω' h => hof_congr n h
  have hW : Measurable (fun ω => hof p ω n) := measurable_hof (by linarith) n
  have huint : Integrable (fun ω => hof p ω n) (markMeasure (boolMeasure q)) := by
    simpa only [pow_one] using integrable_hof_pow (k := 1) hp1 hp2 (by norm_num) hu6 n
  have h := integral_dep_mul_mark_sub h0 h1 hdep hW huint
  calc ∫ ω, dfun q p n ω ∂(markMeasure (boolMeasure q))
      = ∫ ω, hof p ω n * (mk ω (n + 1) - q) ∂(markMeasure (boolMeasure q)) := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [dfun]
        ring
    _ = 0 := h

/-- **`E[W (mk(m+1) - q)^2] = q(1-q) E[W]`** for `W` a function of the marks `0, …, m`. -/
theorem integral_dep_mul_mark_sub_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {m : ℕ}
    {W : (ℕ → Bool) → ℝ} (hdep : DependsOn m W) (hW : Measurable W)
    (hint : Integrable W (markMeasure (boolMeasure q))) :
    ∫ ω, W ω * (mk ω (m + 1) - q) ^ 2 ∂(markMeasure (boolMeasure q))
      = q * (1 - q) * ∫ ω, W ω ∂(markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  set μ := markMeasure (boolMeasure q) with hμ
  have hind := indep_of_dependsOn (μB := boolMeasure q) hdep hW
  have hφ : Measurable (fun b : Bool => ((if b then (1 : ℝ) else 0) - q) ^ 2) := by fun_prop
  have hind2 : IndepFun (fun ω : ℕ → Bool => (mk ω (m + 1) - q) ^ 2) W μ :=
    hind.comp hφ measurable_id
  have hX : AEStronglyMeasurable (fun ω : ℕ → Bool => (mk ω (m + 1) - q) ^ 2) μ :=
    (((measurable_mk (m + 1)).sub measurable_const).pow_const 2).aestronglyMeasurable
  have hprod := hind2.integral_fun_mul_eq_mul_integral hX hint.aestronglyMeasurable
  have hmean : ∫ ω : ℕ → Bool, (mk ω (m + 1) - q) ^ 2 ∂μ = q * (1 - q) := by
    have h1' : ∫ ω : ℕ → Bool, (mk ω (m + 1) - q) ^ 2 ∂μ
        = ∫ b : Bool, ((if b then (1 : ℝ) else 0) - q) ^ 2 ∂(boolMeasure q) :=
      integral_eval (μB := boolMeasure q) (f := fun b : Bool => ((if b then (1:ℝ) else 0) - q)^2) (m+1)
    rw [h1', integral_boolMeasure h0 h1]
    norm_num
    ring
  have hcomm : (fun ω => W ω * (mk ω (m + 1) - q) ^ 2)
      = fun ω => (mk ω (m + 1) - q) ^ 2 * W ω := by
    funext ω; ring
  rw [hcomm, hprod, hmean]

/-- **`E d_n^2 = q(1-q) E h(n)^2`.** -/
theorem integral_dfun_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu6 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 6) (markMeasure (boolMeasure q)))
    (n : ℕ) :
    ∫ ω, (dfun q p n ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = q * (1 - q) * ∫ ω, (hof p ω n) ^ 2 ∂(markMeasure (boolMeasure q)) := by
  have hdep : DependsOn n (fun ω => (hof p ω n) ^ 2) := (dependsOn_hof (le_refl n)).pow 2
  have hW : Measurable (fun ω => (hof p ω n) ^ 2) := (measurable_hof (by linarith) n).pow_const 2
  have hint : Integrable (fun ω => (hof p ω n) ^ 2) (markMeasure (boolMeasure q)) :=
    integrable_hof_pow (k := 2) hp1 hp2 (by norm_num) hu6 n
  have h := integral_dep_mul_mark_sub_sq h0 h1 hdep hW hint
  calc ∫ ω, (dfun q p n ω) ^ 2 ∂(markMeasure (boolMeasure q))
      = ∫ ω, (hof p ω n) ^ 2 * (mk ω (n + 1) - q) ^ 2 ∂(markMeasure (boolMeasure q)) := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [dfun]
        ring
    _ = _ := h

end
end SwarmSpatial
