/-
  Direction B (quenched spatial/potential bound): the **second display of (spav)**,
  `limsup_r (1/r) ∑_{x<r} h_j(x)^2 ≤ C`, for the actual i.i.d. site marks.

  This is the quenched spatial-average input consumed by `SwarmOcc.Jsum_bound`
  (`hces : ∀ m, ∑_{x<m} g x ≤ K m` with `g x = h_j(x-1)^2`), hence the missing
  ingredient of `(Jbound)`.  It is a fixed-environment statement with a constant
  depending only on `m, p`; no conditioning and no ergodic theorem.

  Route (the quadratic analogue of the paper's telescoping identity for (spav)):
  the recursion `h(x) = 1 + ξ(x) (1 + h(x-1))`, `ξ ∈ {1, ρ}`, `ρ = (1-p)/p`, gives,
  for the functional `Φ_λ(u) = u² - λu` and every real `λ`, the exact one-step identity

      Φ_λ(h(x)) - Φ_λ(h(x-1))
        = Δ_false(h(x-1)) + mk(x) * (Δ_true - Δ_false)(h(x-1)),

  and the choice `λ = (4(1-q) + 2qρ/p)/(q(ρ-1))` makes the conditional mean equal to
  `C_F - q(1-ρ²) h(x-1)²`.  Summing telescopes `Φ` and leaves
  `q(1-ρ²) ∑_{x<r} h(x)² = C_F r - Φ(h(r)) + Φ(h(0)) + (centred fluctuation)_r`,
  with the fluctuation a genuine martingale for the finite-mark filtration, so
  `martingale_strong_law` gives it `o(r)`.  Since `h(r)/r → 0` and `h(r)²/r → 0` by
  `(Kmom)`, the average of `h²` **converges** to the explicit constant `C_F/(q(1-ρ²))`.

  Throughout `q = (1-p)^(m-1)` is the paper's mark probability, `boolMeasure q` is the
  law of a single site mark, and `hof p ω` is the paper's potential at the marks `ω`.
-/
import Swarm.Imports
import Mathlib.Probability.ConditionalExpectation
import Swarm.S11
import Swarm.RawSpatial
import Swarm.Jsum

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
open SwarmMarks
open SwarmSpatial

namespace SwarmSpatialSq

noncomputable section

variable {p q : ℝ}

/-! ### 1. The quadratic functional and the two branch differences -/

/-- `Φ_λ(u) = u² - λu`, the quadratic correction whose `λ` is tuned to cancel the linear
term of the one-step mean. -/
def Phi (lam u : ℝ) : ℝ := u ^ 2 - lam * u

/-- The excess of the marked branch over the unmarked one in the `Φ`-increment. -/
def Bfun (p lam u : ℝ) : ℝ := Phi lam (hstep p true u) - Phi lam (hstep p false u)

/-- The tuning constant `λ`: it kills the coefficient of `u` in the one-step conditional
mean of `Φ_λ(h)`. -/
def lamSq (p q : ℝ) : ℝ :=
  (4 * (1 - q) + 2 * q * ((1 - p) / p) / p) / (q * ((1 - p) / p - 1))

/-- The constant term of that conditional mean. -/
def CFSq (p q : ℝ) : ℝ := 4 * (1 - q) + q / p ^ 2 - lamSq p q * (2 * (1 - q) + q / p)

/-- The contraction factor of the second moment: `q(1-ρ²)`. -/
def aSq (p q : ℝ) : ℝ := q * (1 - ((1 - p) / p) ^ 2)

/-- The explicit spatial-average constant, `C_F/(q(1-ρ²))`. -/
def Ksq (p q : ℝ) : ℝ := CFSq p q / aSq p q

/-- **The one-step conditional mean identity, abstract form.**  For any `λ`, `C` satisfying
the two defining relations, averaging the `Φ`-increment over the site mark (`true` with
probability `q`) gives exactly `C - q(1-ρ²) u²`. -/
theorem Phi_step_mean_abstract (lam CF u : ℝ)
    (h1 : q * ((1 - p) / p - 1) * lam = 4 * (1 - q) + 2 * q * ((1 - p) / p) / p)
    (h2 : CF = 4 * (1 - q) + q / p ^ 2 - lam * (2 * (1 - q) + q / p)) :
    (1 - q) * (Phi lam (hstep p false u) - Phi lam u)
        + q * (Phi lam (hstep p true u) - Phi lam u)
      = CF - q * (1 - ((1 - p) / p) ^ 2) * u ^ 2 := by
  have hexp : (1 - q) * (Phi lam (hstep p false u) - Phi lam u)
      + q * (Phi lam (hstep p true u) - Phi lam u) - (CF - q * (1 - ((1 - p) / p) ^ 2) * u ^ 2)
      = - ((q * ((1 - p) / p - 1) * lam - (4 * (1 - q) + 2 * q * ((1 - p) / p) / p)) * u)
        - (CF - (4 * (1 - q) + q / p ^ 2 - lam * (2 * (1 - q) + q / p))) := by
    simp only [Phi, hstep_true, hstep_false]
    ring
  rw [h1, h2] at hexp
  simp only [sub_self, zero_mul, sub_zero] at hexp
  linarith

/-- The defining relation of `lamSq`. -/
theorem lamSq_spec (hp : p ≠ 0) (hp2 : p ≠ 1 / 2) (hq : q ≠ 0) :
    q * ((1 - p) / p - 1) * lamSq p q = 4 * (1 - q) + 2 * q * ((1 - p) / p) / p := by
  have hρ : (1 - p) / p - 1 ≠ 0 := by
    intro h
    apply hp2
    field_simp at h
    linarith
  have hden : q * ((1 - p) / p - 1) ≠ 0 := mul_ne_zero hq hρ
  unfold lamSq
  exact mul_div_cancel₀ _ hden

/-- **The one-step conditional mean identity.** -/
theorem Phi_step_mean (hp : p ≠ 0) (hp2 : p ≠ 1 / 2) (hq : q ≠ 0) (u : ℝ) :
    (1 - q) * (Phi (lamSq p q) (hstep p false u) - Phi (lamSq p q) u)
        + q * (Phi (lamSq p q) (hstep p true u) - Phi (lamSq p q) u)
      = CFSq p q - aSq p q * u ^ 2 := by
  have h2 : CFSq p q
      = 4 * (1 - q) + q / p ^ 2 - lamSq p q * (2 * (1 - q) + q / p) := rfl
  have h := Phi_step_mean_abstract (p := p) (q := q) (lam := lamSq p q) (CF := CFSq p q) (u := u)
    (lamSq_spec hp hp2 hq) h2
  rwa [show q * (1 - ((1 - p) / p) ^ 2) = aSq p q from rfl] at h

/-- The unmarked branch of the `Φ`-increment: `Φ(u+2) - Φ(u) = 4u + 4 - 2λ`. -/
theorem Phi_step_false (lam u : ℝ) :
    Phi lam (hstep p false u) - Phi lam u = 4 * u + 4 - 2 * lam := by
  unfold Phi
  simp only [hstep_false]
  ring

/-- **The factorization of the branch difference.**  Both branches are affine in `u` and
differ by exactly the factor `(ρ-1)(1+u)`. -/
theorem Bfun_factor (hp : p ≠ 0) (lam u : ℝ) :
    Bfun p lam u = ((1 - p) / p - 1) * (1 + u)
      * ((3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u) := by
  have h1 : (1 : ℝ) / p = 1 + (1 - p) / p := by
    field_simp
    ring
  unfold Bfun Phi
  simp only [hstep_true, hstep_false]
  rw [h1]
  ring

/-- The `Φ`-increment is affine in the mark indicator, with slope `Bfun`. -/
theorem Phi_step_mk (lam : ℝ) (ω : ℕ → Bool) (k : ℕ) :
    Phi lam (hof p ω (k + 1)) - Phi lam (hof p ω k)
      = (Phi lam (hstep p false (hof p ω k)) - Phi lam (hof p ω k))
        + SwarmSpatial.mk ω (k + 1) * Bfun p lam (hof p ω k) := by
  rw [hof_succ]
  cases h : ω (k + 1) with
  | false => simp [SwarmSpatial.mk, h]
  | true => simp only [SwarmSpatial.mk, h, if_true, Bfun, one_mul]; ring

/-- **Pointwise form of the mean identity at the actual mark and potential.** -/
theorem Phi_step_split (hp : p ≠ 0) (hp2 : p ≠ 1 / 2) (hq : q ≠ 0) (ω : ℕ → Bool) (k : ℕ) :
    Phi (lamSq p q) (hof p ω (k + 1)) - Phi (lamSq p q) (hof p ω k)
      = (CFSq p q - aSq p q * (hof p ω k) ^ 2)
        + (SwarmSpatial.mk ω (k + 1) - q) * Bfun p (lamSq p q) (hof p ω k) := by
  rw [Phi_step_mk]
  have h := Phi_step_mean (p := p) (q := q) hp hp2 hq (hof p ω k)
  have hiff : Phi (lamSq p q) (hstep p false (hof p ω k)) - Phi (lamSq p q) (hof p ω k)
      = (1 - q) * (Phi (lamSq p q) (hstep p false (hof p ω k)) - Phi (lamSq p q) (hof p ω k))
        + q * (Phi (lamSq p q) (hstep p true (hof p ω k)) - Phi (lamSq p q) (hof p ω k))
        - q * (Phi (lamSq p q) (hstep p true (hof p ω k))
            - Phi (lamSq p q) (hstep p false (hof p ω k))) := by
    ring
  rw [hiff, h]
  unfold Bfun
  ring

/-! ### 2. A quadratic bound on the branch difference -/

/-- The explicit coefficient of the quadratic bound on `Bfun`. -/
def bconst (p lam : ℝ) : ℝ :=
  2 * |(1 - p) / p - 1| * (|3 + (1 - p) / p - lam| + |1 + (1 - p) / p|)

/-- **`|Bfun|` grows at most quadratically** in `u`, for `u ≥ 1` (the range of `h`). -/
theorem Bfun_abs_le (hp : p ≠ 0) (lam : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    |Bfun p lam u| ≤ bconst p lam * u ^ 2 := by
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have hfac := Bfun_factor (p := p) hp lam u
  have htri : |(3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u|
      ≤ (|3 + (1 - p) / p - lam| + |1 + (1 - p) / p|) * u := by
    have h1 : |(3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u|
        ≤ |3 + (1 - p) / p - lam| + |1 + (1 - p) / p| * u := by
      have := abs_add_le (3 + (1 - p) / p - lam) ((1 + (1 - p) / p) * u)
      rwa [abs_mul, abs_of_nonneg hu0] at this
    have hA0 : (0 : ℝ) ≤ |3 + (1 - p) / p - lam| := abs_nonneg _
    have hA1 : |3 + (1 - p) / p - lam| ≤ |3 + (1 - p) / p - lam| * u := by
      have h := mul_le_mul_of_nonneg_left hu hA0
      simpa using h
    have hexp : (|3 + (1 - p) / p - lam| + |1 + (1 - p) / p|) * u
        = |3 + (1 - p) / p - lam| * u + |1 + (1 - p) / p| * u := by ring
    rw [hexp]
    linarith
  have hone : |1 + u| ≤ 2 * u := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + u)]
    linarith
  rw [hfac, abs_mul, abs_mul]
  have hA : (0 : ℝ) ≤ |(1 - p) / p - 1| := abs_nonneg _
  have hC : (0 : ℝ) ≤ |(3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u| := abs_nonneg _
  have step1 : |(1 - p) / p - 1| * |1 + u|
      * |(3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u|
      ≤ |(1 - p) / p - 1| * (2 * u) * ((|3 + (1 - p) / p - lam| + |1 + (1 - p) / p|) * u) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hone hA
    · exact htri
    · exact hC
    · positivity
  calc |(1 - p) / p - 1| * |1 + u| * |(3 + (1 - p) / p - lam) + (1 + (1 - p) / p) * u|
      ≤ |(1 - p) / p - 1| * (2 * u) * ((|3 + (1 - p) / p - lam| + |1 + (1 - p) / p|) * u) := step1
    _ = bconst p lam * u ^ 2 := by unfold bconst; ring

/-- The squared form used for the martingale variances. -/
theorem Bfun_sq_le (hp : p ≠ 0) (lam : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    (Bfun p lam u) ^ 2 ≤ (bconst p lam) ^ 2 * u ^ 4 := by
  have h := Bfun_abs_le (p := p) hp lam hu
  have h2 : (Bfun p lam u) ^ 2 = |Bfun p lam u| ^ 2 := (sq_abs _).symm
  rw [h2]
  have hb : (0 : ℝ) ≤ bconst p lam := by
    unfold bconst
    have h1 : (0 : ℝ) ≤ |(1 - p) / p - 1| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |3 + (1 - p) / p - lam| + |1 + (1 - p) / p| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    positivity
  have h3 : |Bfun p lam u| ≤ bconst p lam * u ^ 2 := h
  have h5 : |Bfun p lam u| * |Bfun p lam u|
      ≤ (bconst p lam * u ^ 2) * (bconst p lam * u ^ 2) :=
    mul_le_mul h3 h3 (abs_nonneg _) (by positivity)
  calc |Bfun p lam u| ^ 2 = |Bfun p lam u| * |Bfun p lam u| := by ring
    _ ≤ (bconst p lam * u ^ 2) * (bconst p lam * u ^ 2) := h5
    _ = (bconst p lam) ^ 2 * u ^ 4 := by ring


/-! ### 3. The centred quadratic fluctuation: measurability, adaptation, integrability -/

/-- `Bfun` is continuous in its third argument. -/
theorem continuous_Bfun (p lam : ℝ) : Continuous (fun u : ℝ => Bfun p lam u) := by
  unfold Bfun Phi
  simp only [hstep_true, hstep_false]
  fun_prop

/-- Composition of a `DependsOn` functional with an arbitrary function of its value. -/
theorem dependsOn_comp {m : ℕ} {W : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (g : ℝ → ℝ) :
    DependsOn m (fun ω => g (W ω)) := fun ω ω' h => congrArg g (hW ω ω' h)

/-- The centred quadratic increment. -/
def d2 (p q lam : ℝ) (k : ℕ) (ω : ℕ → Bool) : ℝ :=
  (SwarmSpatial.mk ω (k + 1) - q) * Bfun p lam (hof p ω k)

/-- The centred quadratic fluctuation `M_r = ∑_{k<r} d2_k`. -/
def M2 (p q lam : ℝ) (r : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range r, d2 p q lam k ω

lemma M2_succ (p q lam : ℝ) (r : ℕ) (ω : ℕ → Bool) :
    M2 p q lam (r + 1) ω = M2 p q lam r ω + d2 p q lam r ω := by
  simp only [M2, Finset.sum_range_succ]

lemma measurable_d2 (hp0 : p ≠ 0) (q lam : ℝ) (k : ℕ) : Measurable (d2 p q lam k) :=
  ((measurable_mk (k + 1)).sub measurable_const).mul
    ((continuous_Bfun p lam).measurable.comp (measurable_hof hp0 k))

lemma dependsOn_d2 (p q lam : ℝ) (k : ℕ) : DependsOn (k + 1) (d2 p q lam k) :=
  ((dependsOn_mk (le_refl (k + 1))).sub (dependsOn_const _ _)).mul
    (dependsOn_comp (dependsOn_hof (p := p) (Nat.le_succ k)) (Bfun p lam))

lemma dependsOn_M2 (p q lam : ℝ) (r : ℕ) : DependsOn r (M2 p q lam r) :=
  DependsOn.sum (Finset.range r) fun k hk =>
    (dependsOn_d2 p q lam k).mono (Nat.succ_le_of_lt (Finset.mem_range.mp hk))

lemma measurable_M2 (hp0 : p ≠ 0) (q lam : ℝ) (r : ℕ) : Measurable (M2 p q lam r) := by
  unfold M2
  exact Finset.measurable_sum _ fun k _ => measurable_d2 hp0 q lam k

/-- The centred mark is bounded by `1` in absolute value. -/
lemma abs_mk_sub_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (ω : ℕ → Bool) (n : ℕ) :
    |SwarmSpatial.mk ω n - q| ≤ 1 := by
  have hle1 := mk_le_one ω n
  have hnn := mk_nonneg ω n
  rw [abs_le]
  constructor <;> linarith

/-- `(Bfun (h k))²` is integrable, dominated by the fourth moment of `h k`. -/
lemma integrable_Bfun_sq (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (q lam : ℝ) (hC4 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4)
      (markMeasure (boolMeasure q)))
    (k : ℕ) :
    Integrable (fun ω => (Bfun p lam (hof p ω k)) ^ 2) (markMeasure (boolMeasure q)) := by
  set μ := markMeasure (boolMeasure q) with hμ
  refine Integrable.mono' ((hC4 k).const_mul ((bconst p lam) ^ 2))
    (((continuous_Bfun p lam).measurable.comp (measurable_hof hp0 k)).pow_const 2
      |>.aestronglyMeasurable) ?_
  filter_upwards with ω
  have h1 : 1 ≤ hof p ω k := one_le_hof hp1.le hp2 ω k
  have h2 := Bfun_sq_le (p := p) hp0 lam h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h2

/-- The increment `d2 k` is integrable. -/
lemma integrable_d2 (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (lam : ℝ)
    (hC4 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (k : ℕ) : Integrable (d2 p q lam k) (markMeasure (boolMeasure q)) := by
  set μ := markMeasure (boolMeasure q) with hμ
  refine Integrable.mono' ((hC4 k).const_mul (bconst p lam))
    ((measurable_d2 hp0 q lam k).aestronglyMeasurable) ?_
  filter_upwards with ω
  have hmk : |SwarmSpatial.mk ω (k + 1) - q| ≤ 1 := abs_mk_sub_le h0 h1 ω (k + 1)
  have hh : 1 ≤ hof p ω k := one_le_hof hp1.le hp2 ω k
  have hB := Bfun_abs_le (p := p) hp0 lam hh
  have hpow : (hof p ω k) ^ 2 ≤ (hof p ω k) ^ 4 := by
    have h2 : (1 : ℝ) ≤ (hof p ω k) ^ 2 := by nlinarith [hh]
    calc (hof p ω k) ^ 2 = (hof p ω k) ^ 2 * 1 := by ring
      _ ≤ (hof p ω k) ^ 2 * (hof p ω k) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (hof p ω k) ^ 4 := by ring
  have hb0 : (0 : ℝ) ≤ bconst p lam := by
    unfold bconst
    have h1' : (0 : ℝ) ≤ |(1 - p) / p - 1| := abs_nonneg _
    have h2' : (0 : ℝ) ≤ |3 + (1 - p) / p - lam| + |1 + (1 - p) / p| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    positivity
  simp only [d2]
  rw [Real.norm_eq_abs, abs_mul]
  calc |SwarmSpatial.mk ω (k + 1) - q| * |Bfun p lam (hof p ω k)|
      ≤ 1 * (bconst p lam * (hof p ω k) ^ 2) := by
        apply mul_le_mul hmk hB (abs_nonneg _) (by linarith)
    _ ≤ bconst p lam * (hof p ω k) ^ 4 := by
      have h2 : bconst p lam * (hof p ω k) ^ 2 ≤ bconst p lam * (hof p ω k) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow hb0
      linarith

/-- `(d2 k)²` is integrable. -/
lemma integrable_d2_sq (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (lam : ℝ)
    (hC4 : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (k : ℕ) : Integrable (fun ω => (d2 p q lam k ω) ^ 2) (markMeasure (boolMeasure q)) := by
  set μ := markMeasure (boolMeasure q) with hμ
  refine Integrable.mono' ((hC4 k).const_mul ((bconst p lam) ^ 2))
    (((measurable_d2 hp0 q lam k).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards with ω
  have hmk : |SwarmSpatial.mk ω (k + 1) - q| ≤ 1 := abs_mk_sub_le h0 h1 ω (k + 1)
  have hh : 1 ≤ hof p ω k := one_le_hof hp1.le hp2 ω k
  have hB := Bfun_sq_le (p := p) hp0 lam hh
  have hsq : (SwarmSpatial.mk ω (k + 1) - q) ^ 2 ≤ 1 := by
    have := abs_mk_sub_le h0 h1 ω (k + 1)
    nlinarith [sq_abs (SwarmSpatial.mk ω (k + 1) - q),
      abs_nonneg (SwarmSpatial.mk ω (k + 1) - q)]
  simp only [d2, mul_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (SwarmSpatial.mk ω (k + 1) - q) ^ 2 * (Bfun p lam (hof p ω k)) ^ 2
      ≤ 1 * ((bconst p lam) ^ 2 * (hof p ω k) ^ 4) := by
        apply mul_le_mul hsq hB (by positivity) (by norm_num)
    _ = (bconst p lam) ^ 2 * (hof p ω k) ^ 4 := by ring

/-! ### 4. The conditional mean vanishes: `M2` is a martingale, and `M2_r / r → 0` -/

/-- **The key conditional expectation.**  `E[d2_r | σ(ω 0, …, ω r)] = 0`, because the mark
`ω (r+1)` is independent of the past and `E mk = q`. -/
theorem condExp_d2_eq_zero {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (lam : ℝ) (r : ℕ) :
    condExp (Gfilt r) (markMeasure (boolMeasure q)) (d2 p q lam r)
      =ᵐ[markMeasure (boolMeasure q)] 0 := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  set μ := markMeasure (boolMeasure q) with hμ
  have hp0 : p ≠ 0 := by linarith
  have hXm : Measurable (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q) :=
    (measurable_mk (r + 1)).sub measurable_const
  have hYm : Measurable (fun ω : ℕ → Bool => Bfun p lam (hof p ω r)) :=
    (continuous_Bfun p lam).measurable.comp (measurable_hof hp0 r)
  have hYsm : StronglyMeasurable[Gfilt r] (fun ω : ℕ → Bool => Bfun p lam (hof p ω r)) :=
    dependsOn_stronglyMeasurable
      (dependsOn_comp (dependsOn_hof (p := p) (le_refl r)) (Bfun p lam)) hYm
  have hfun : IndepFun (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q)
      (fun ω => fun i : Fin (r + 1) => ω i) μ := by
    have hbase := indep_eval_succ (μB := boolMeasure q) r
    have hφ : Measurable (fun b : Bool => ((if b then (1 : ℝ) else 0) - q)) := by fun_prop
    have hψ : Measurable (fun v : Fin (r + 1) → Bool => v) := measurable_id
    have hc := hbase.comp hφ hψ
    simpa [SwarmSpatial.mk, Function.comp_def, hμ] using hc
  have hind : Indep (MeasurableSpace.comap
      (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q)
      (inferInstance : MeasurableSpace ℝ)) (Gfilt r) μ := hfun
  have hmeanX : ∫ ω, (SwarmSpatial.mk ω (r + 1) - q) ∂μ = 0 := by
    have h := integral_dep_mul_mark_sub (q := q) h0 h1 (m := r) (W := fun _ => (1 : ℝ))
      (dependsOn_const r 1) measurable_const (integrable_const 1)
    simpa [hμ, one_mul] using h
  have hle1 : MeasurableSpace.comap (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q)
      (inferInstance : MeasurableSpace ℝ) ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
    hXm.comap_le
  have hce : μ[(fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q) | Gfilt r]
      =ᵐ[μ] fun _ => ∫ ω, (SwarmSpatial.mk ω (r + 1) - q) ∂μ :=
    condExp_indep_eq hle1 (gfilt_le r)
      (comap_measurable (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q)).stronglyMeasurable hind
  have hXint : Integrable (fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q) μ :=
    (integrable_mk h0 h1 (r + 1)).sub (integrable_const q)
  have hXYint : Integrable (fun ω : ℕ → Bool =>
      (SwarmSpatial.mk ω (r + 1) - q) * Bfun p lam (hof p ω r)) μ := by
    have h := integrable_d2 hp1 hp2 hp0 h0 h1 lam hu4i r
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [d2]
  have hpull : μ[(fun ω : ℕ → Bool =>
        (SwarmSpatial.mk ω (r + 1) - q) * Bfun p lam (hof p ω r)) | Gfilt r]
      =ᵐ[μ] μ[(fun ω : ℕ → Bool => SwarmSpatial.mk ω (r + 1) - q) | Gfilt r]
        * fun ω => Bfun p lam (hof p ω r) :=
    condExp_mul_of_stronglyMeasurable_right hYsm hXYint hXint
  have e : d2 p q lam r = fun ω : ℕ → Bool =>
      (SwarmSpatial.mk ω (r + 1) - q) * Bfun p lam (hof p ω r) := rfl
  rw [e]
  filter_upwards [hpull, hce] with ω h1ω h2ω
  simp only [Pi.mul_apply] at h1ω
  rw [h1ω, h2ω, hmeanX, zero_mul]
  rfl

/-- `M2` is adapted to the natural finite-mark filtration. -/
theorem stronglyAdapted_M2 {p : ℝ} (hp0 : p ≠ 0) (q lam : ℝ) :
    StronglyAdapted Gfiltration (fun r (ω : ℕ → Bool) => M2 p q lam r ω) := by
  intro r
  exact dependsOn_stronglyMeasurable (dependsOn_M2 p q lam r) (measurable_M2 hp0 q lam r)

/-- `M2` is integrable at every time. -/
theorem integrable_M2 {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (lam : ℝ) (r : ℕ) : Integrable (fun ω => M2 p q lam r ω) (markMeasure (boolMeasure q)) := by
  have hp0 : p ≠ 0 := by linarith
  induction r with
  | zero =>
      simpa [M2] using
        integrable_zero (α := ℕ → Bool) (μ := markMeasure (boolMeasure q)) 0
  | succ r ih =>
      have h := ih.add (integrable_d2 hp1 hp2 hp0 h0 h1 lam hu4i r)
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]
      rw [M2_succ]

/-- The conditional expectation of one step of `M2` vanishes. -/
theorem condExp_M2_sub {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (lam : ℝ) (r : ℕ) :
    condExp (Gfilt r) (markMeasure (boolMeasure q))
        (fun ω : ℕ → Bool => M2 p q lam (r + 1) ω - M2 p q lam r ω)
      =ᵐ[markMeasure (boolMeasure q)] 0 := by
  have hfuneq : (fun ω : ℕ → Bool => M2 p q lam (r + 1) ω - M2 p q lam r ω)
      = d2 p q lam r := by
    funext ω
    rw [M2_succ]
    ring
  rw [hfuneq]
  exact condExp_d2_eq_zero h0 h1 hp1 hp2 hu4i lam r

/-- **`M2` is a genuine martingale** for the finite-mark filtration. -/
theorem martingale_M2 {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    (lam : ℝ) :
    Martingale (fun r (ω : ℕ → Bool) => M2 p q lam r ω) Gfiltration
      (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hp0 : p ≠ 0 := by linarith
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_M2 hp0 q lam)
    (fun r => integrable_M2 h0 h1 hp1 hp2 hu4i lam r) (fun r => ?_)
  exact condExp_M2_sub h0 h1 hp1 hp2 hu4i lam r

/-- The increment of `M2`. -/
lemma inc_M2 (q lam : ℝ) (r : ℕ) (ω : ℕ → Bool) :
    MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) r ω = d2 p q lam r ω := by
  simp only [MartingaleLimit.inc_apply]
  rw [M2_succ]
  ring

/-- The second moment of one increment is bounded by a constant, uniformly in time. -/
theorem integral_inc_sq_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    {C4 : ℝ} (hu4b : ∀ n, ∫ ω, (hof p ω n) ^ 4 ∂(markMeasure (boolMeasure q)) ≤ C4)
    (lam : ℝ) :
    ∀ r : ℕ, ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) r ω) ^ 2
        ∂(markMeasure (boolMeasure q)) ≤ (bconst p lam) ^ 2 * C4 := by
  intro r
  have hp0 : p ≠ 0 := by linarith
  have hcongr : (fun ω : ℕ → Bool =>
      (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) r ω) ^ 2)
      = fun ω => (d2 p q lam r ω) ^ 2 := by
    funext ω
    rw [inc_M2]
  rw [hcongr]
  set μ := markMeasure (boolMeasure q) with hμ
  have hdom : Integrable (fun ω => (bconst p lam) ^ 2 * (hof p ω r) ^ 4) μ :=
    (hu4i r).const_mul _
  have hle : (fun ω => (d2 p q lam r ω) ^ 2) ≤ᵐ[μ]
      fun ω => (bconst p lam) ^ 2 * (hof p ω r) ^ 4 := by
    filter_upwards with ω
    have hmk : |SwarmSpatial.mk ω (r + 1) - q| ≤ 1 := abs_mk_sub_le h0 h1 ω (r + 1)
    have hh : 1 ≤ hof p ω r := one_le_hof hp1.le hp2 ω r
    have hB := Bfun_sq_le (p := p) hp0 lam hh
    have hsq : (SwarmSpatial.mk ω (r + 1) - q) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (SwarmSpatial.mk ω (r + 1) - q),
        abs_nonneg (SwarmSpatial.mk ω (r + 1) - q)]
    simp only [d2, mul_pow]
    calc (SwarmSpatial.mk ω (r + 1) - q) ^ 2 * (Bfun p lam (hof p ω r)) ^ 2
        ≤ 1 * ((bconst p lam) ^ 2 * (hof p ω r) ^ 4) := by
          apply mul_le_mul hsq hB (by positivity) (by norm_num)
      _ = (bconst p lam) ^ 2 * (hof p ω r) ^ 4 := by ring
  calc ∫ ω, (d2 p q lam r ω) ^ 2 ∂μ
      ≤ ∫ ω, (bconst p lam) ^ 2 * (hof p ω r) ^ 4 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hdom hle
    _ = (bconst p lam) ^ 2 * ∫ ω, (hof p ω r) ^ 4 ∂μ := integral_const_mul _ _
    _ ≤ (bconst p lam) ^ 2 * C4 := by
        have hb0 : (0 : ℝ) ≤ (bconst p lam) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (hu4b r) hb0

/-- The weighted variance series is summable. -/
theorem summable_weighted_variance {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    {C4 : ℝ} (hu4b : ∀ n, ∫ ω, (hof p ω n) ^ 4 ∂(markMeasure (boolMeasure q)) ≤ C4)
    (lam : ℝ) :
    Summable fun k : ℕ =>
      ((k : ℝ) + 1)⁻¹ ^ 2 *
        ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) k ω) ^ 2
          ∂(markMeasure (boolMeasure q)) := by
  have hbase : Summable fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2 := by
    have h1' : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2' : Summable fun n : ℕ => (1 : ℝ) / (((n : ℕ) : ℝ) + 1) ^ 2 := by
      simpa using (summable_nat_add_iff 1).mpr h1'
    refine h2'.congr fun k => ?_
    rw [one_div, inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hbase.mul_left ((bconst p lam) ^ 2 * C4))
  have h2 : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹ ^ 2 := by positivity
  calc ((k : ℝ) + 1)⁻¹ ^ 2 *
        ∫ ω, (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) k ω) ^ 2
          ∂(markMeasure (boolMeasure q))
      ≤ ((k : ℝ) + 1)⁻¹ ^ 2 * ((bconst p lam) ^ 2 * C4) :=
        mul_le_mul_of_nonneg_left (integral_inc_sq_le h0 h1 hp1 hp2 hu4i hu4b lam k) h2
    _ = ((bconst p lam) ^ 2 * C4) * ((k : ℝ) + 1)⁻¹ ^ 2 := by ring

/-- **The second-moment martingale strong law for `M2`.** -/
theorem tendsto_M2_div {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)))
    {C4 : ℝ} (hu4b : ∀ n, ∫ ω, (hof p ω n) ^ 4 ∂(markMeasure (boolMeasure q)) ≤ C4)
    (lam : ℝ) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)),
      Tendsto (fun r : ℕ => ((r : ℝ))⁻¹ * M2 p q lam r ω) atTop (nhds 0) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hp0 : p ≠ 0 := by linarith
  have hint : ∀ k : ℕ, Integrable (fun ω : ℕ → Bool =>
      (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) k ω) ^ 2)
      (markMeasure (boolMeasure q)) := by
    intro k
    have h := integrable_d2_sq hp1 hp2 hp0 h0 h1 lam hu4i k
    have e : (fun ω : ℕ → Bool =>
        (MartingaleLimit.inc (fun r (ω : ℕ → Bool) => M2 p q lam r ω) k ω) ^ 2)
        = fun ω => (d2 p q lam k ω) ^ 2 := by
      funext ω
      rw [inc_M2]
    rw [e]
    exact h
  have hsl := MartingaleLimit.martingale_strong_law
    (μ := markMeasure (boolMeasure q)) (ℱ := Gfiltration)
    (Q := fun r (ω : ℕ → Bool) => M2 p q lam r ω)
    (martingale_M2 h0 h1 hp1 hp2 hu4i lam) hint
    (summable_weighted_variance h0 h1 hp1 hp2 hu4i hu4b lam)
  filter_upwards [hsl] with ω hω
  have e : (fun n : ℕ => (M2 p q lam n ω - M2 p q lam 0 ω) / (n : ℝ))
      = fun n : ℕ => (n : ℝ)⁻¹ * M2 p q lam n ω := by
    funext n
    have h0' : M2 p q lam 0 ω = 0 := by simp [M2]
    rw [h0', sub_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      field_simp
  rw [e] at hω
  exact hω

/-! ### 5. The telescoping identity -/

/-- Telescoping of the `Φ`-increments. -/
theorem telescope_Phi (lam : ℝ) (ω : ℕ → Bool) (r : ℕ) :
    ∑ k ∈ Finset.range r, (Phi lam (hof p ω (k + 1)) - Phi lam (hof p ω k))
      = Phi lam (hof p ω r) - Phi lam (hof p ω 0) :=
  Finset.sum_range_sub (fun k => Phi lam (hof p ω k)) r

/-- **The exact spatial identity for the second moment.**  Summing the one-step split and
telescoping `Φ` gives, for every `r`,

    q(1-ρ²) ∑_{k<r} h(k)² = C_F r - (Φ(h(r)) - Φ(h(0))) + M2_r .

This is the quadratic analogue of `(spav)`'s telescoping identity. -/
theorem spav_sq_identity (hp : p ≠ 0) (hp2 : p ≠ 1 / 2) (hq : q ≠ 0) (ω : ℕ → Bool) (r : ℕ) :
    aSq p q * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2
      = CFSq p q * r
        - (Phi (lamSq p q) (hof p ω r) - Phi (lamSq p q) (hof p ω 0))
        + M2 p q (lamSq p q) r ω := by
  induction r with
  | zero => simp [M2]
  | succ n ih =>
      have hs := Phi_step_split (p := p) (q := q) hp hp2 hq ω n
      rw [Finset.sum_range_succ, mul_add, ih, M2_succ]
      simp only [d2] at hs ⊢
      push_cast
      linarith [hs]

/-- `log²(r+c)/r → 0`. -/
theorem tendsto_log_sq_div_nat {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun r : ℕ => Real.log ((r : ℝ) + c) ^ 2 / (r : ℝ)) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
    simpa using h
  have hshift : Tendsto (fun r : ℕ => (r : ℝ) + c) atTop atTop :=
    Filter.tendsto_atTop_mono (fun r : ℕ => by push_cast; linarith)
      tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + c) ^ 2 / ((r : ℝ) + c)) atTop (nhds 0) :=
    h1.comp hshift
  have h3 : Tendsto (fun r : ℕ => ((r : ℝ) + c) / (r : ℝ)) atTop (nhds 1) := by
    have h4 : Tendsto (fun r : ℕ => c / (r : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c
    have h5 : Tendsto (fun r : ℕ => 1 + c / (r : ℝ)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h4
    refine h5.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    field_simp
  have h6 := h2.mul h3
  have h6' : Tendsto
      (fun r : ℕ => Real.log ((r : ℝ) + c) ^ 2 / ((r : ℝ) + c) * (((r : ℝ) + c) / (r : ℝ)))
      atTop (nhds 0) := by
    simpa using h6
  refine h6'.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hrc : ((r : ℝ) + c) ≠ 0 := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  field_simp

/-- `Φ(h(r))/r → 0` from the logarithmic bound `(Kmom)`. -/
theorem tendsto_Phi_div {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {c : ℝ} (hc : 0 < c) (lam : ℝ) (ω : ℕ → Bool)
    (hlog : ∀ᶠ r : ℕ in atTop, hof p ω r ≤ c * Real.log ((r : ℝ) + 2)) :
    Tendsto (fun r : ℕ => Phi lam (hof p ω r) / (r : ℝ)) atTop (nhds 0) := by
  have hlog1 : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 2) / (r : ℝ)) atTop (nhds 0) :=
    SwarmSpatial.tendsto_log_div_nat (c := 2) (by norm_num)
  have hlog2 : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 2) ^ 2 / (r : ℝ)) atTop (nhds 0) :=
    tendsto_log_sq_div_nat (c := 2) (by norm_num)
  have hlim : Tendsto (fun r : ℕ => c ^ 2 * (Real.log ((r : ℝ) + 2) ^ 2 / (r : ℝ))
      + |lam| * c * (Real.log ((r : ℝ) + 2) / (r : ℝ))) atTop (nhds 0) := by
    have h := ((hlog2.const_mul (c ^ 2)).add (hlog1.const_mul (|lam| * c)))
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hlog, Filter.eventually_gt_atTop 0] with r hr hr0
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  have h1 : 1 ≤ hof p ω r := one_le_hof hp1.le hp2 ω r
  have hnn : (0 : ℝ) ≤ hof p ω r := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log ((r : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ r := by positivity
    linarith
  have hsq : (hof p ω r) ^ 2 ≤ c ^ 2 * Real.log ((r : ℝ) + 2) ^ 2 := by
    have h2 : hof p ω r * hof p ω r
        ≤ (c * Real.log ((r : ℝ) + 2)) * (c * Real.log ((r : ℝ) + 2)) :=
      mul_le_mul hr hr hnn (by positivity)
    calc (hof p ω r) ^ 2 = hof p ω r * hof p ω r := by ring
      _ ≤ (c * Real.log ((r : ℝ) + 2)) * (c * Real.log ((r : ℝ) + 2)) := h2
      _ = c ^ 2 * Real.log ((r : ℝ) + 2) ^ 2 := by ring
  have hlin : |lam| * hof p ω r ≤ |lam| * c * Real.log ((r : ℝ) + 2) := by
    have h := mul_le_mul_of_nonneg_left hr (abs_nonneg lam)
    calc |lam| * hof p ω r ≤ |lam| * (c * Real.log ((r : ℝ) + 2)) := h
      _ = |lam| * c * Real.log ((r : ℝ) + 2) := by ring
  have hPhi : |Phi lam (hof p ω r)|
      ≤ c ^ 2 * Real.log ((r : ℝ) + 2) ^ 2 + |lam| * c * Real.log ((r : ℝ) + 2) := by
    have h2 : |Phi lam (hof p ω r)|
        ≤ (hof p ω r) ^ 2 + |lam| * hof p ω r := by
      unfold Phi
      rw [abs_le]
      constructor
      · have h4 := mul_le_mul_of_nonneg_right (le_abs_self lam) hnn
        nlinarith [sq_nonneg (hof p ω r)]
      · have h4 := mul_le_mul_of_nonneg_right (neg_le_abs lam) hnn
        nlinarith
    linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hrpos.le]
  calc |Phi lam (hof p ω r)| / (r : ℝ)
      ≤ (c ^ 2 * Real.log ((r : ℝ) + 2) ^ 2
          + |lam| * c * Real.log ((r : ℝ) + 2)) / (r : ℝ) :=
        div_le_div_of_nonneg_right hPhi hrpos.le
    _ = c ^ 2 * (Real.log ((r : ℝ) + 2) ^ 2 / (r : ℝ))
          + |lam| * c * (Real.log ((r : ℝ) + 2) / (r : ℝ)) := by
        field_simp

/-- **The second display of `(spav)`, unconditional and with an explicit constant.**  For the
actual i.i.d. Bernoulli site marks with `q = (1-p)^{m-1}`, the spatial average of `h_j²`
*converges* almost surely to `Ksq p q = C_F/(q(1-ρ²))`, a constant depending only on `m` and
`p`. -/
theorem tendsto_hof_sq_average {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))),
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2)
        atTop (nhds (Ksq p ((1 - p) ^ (m - 1)))) := by
  set q : ℝ := (1 - p) ^ (m - 1) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact qpos hp2
  have hq1 : q ≤ 1 := by rw [hqdef]; exact qle_one hp1 hp2 (by omega)
  have hp0 : p ≠ 0 := by linarith
  have hp2' : p ≠ 1 / 2 := by linarith
  obtain ⟨C4, _hC4pos, hu4⟩ := exists_hof_pow_bound (p := p) hp1 hp2 hm 4 (by norm_num)
  have hu4i : ∀ n, Integrable (fun ω => (hof p ω n) ^ 4) (markMeasure (boolMeasure q)) :=
    fun n => (hu4 n).1
  have hu4b : ∀ n, ∫ ω, (hof p ω n) ^ 4 ∂(markMeasure (boolMeasure q)) ≤ C4 :=
    fun n => (hu4 n).2
  have hM2 := tendsto_M2_div hq0.le hq1 hp1 hp2 hu4i hu4b (lamSq p q)
  obtain ⟨θ, hθ, hγ1⟩ := exists_theta (p := p) (q := q) hp1 hp2 hq0 hq1
  have hγpos : 0 < (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) := by
    positivity
  have ht := hof_eventually_log_bound (p := p) (q := q) hp1 hp2 hq0 hq1 hθ hγpos hγ1 le_rfl
  filter_upwards [hM2, ht] with ω hM2ω hlogω
  have hlogω' : ∀ᶠ r : ℕ in atTop, hof p ω r ≤ (3 / θ) * Real.log ((r : ℝ) + 2) := by
    filter_upwards [hlogω] with r hr
    exact hr r (by omega)
  have hPhi := tendsto_Phi_div (p := p) hp1 hp2 (c := 3 / θ) (by positivity) (lamSq p q) ω hlogω'
  have hPhi0 : Tendsto (fun r : ℕ => Phi (lamSq p q) (hof p ω 0) / (r : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim : Tendsto (fun r : ℕ => CFSq p q
      - ((Phi (lamSq p q) (hof p ω r) - Phi (lamSq p q) (hof p ω 0)) / (r : ℝ))
      + (r : ℝ)⁻¹ * M2 p q (lamSq p q) r ω) atTop (nhds (CFSq p q)) := by
    have h1 : Tendsto (fun r : ℕ =>
        (Phi (lamSq p q) (hof p ω r) - Phi (lamSq p q) (hof p ω 0)) / (r : ℝ))
        atTop (nhds 0) := by
      have hsub := hPhi.sub hPhi0
      simpa [sub_div] using hsub
    have h2 : Tendsto (fun r : ℕ => CFSq p q
        - ((Phi (lamSq p q) (hof p ω r) - Phi (lamSq p q) (hof p ω 0)) / (r : ℝ)))
        atTop (nhds (CFSq p q - 0)) :=
      (tendsto_const_nhds (x := CFSq p q)).sub h1
    have h3 := h2.add hM2ω
    simpa using h3
  have hidentity : ∀ᶠ r : ℕ in atTop, aSq p q * ((r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2)
      = CFSq p q
        - ((Phi (lamSq p q) (hof p ω r) - Phi (lamSq p q) (hof p ω 0)) / (r : ℝ))
        + (r : ℝ)⁻¹ * M2 p q (lamSq p q) r ω := by
    filter_upwards [Filter.eventually_gt_atTop 0] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    have hid := spav_sq_identity (p := p) (q := q) hp0 hp2' (ne_of_gt hq0) ω r
    field_simp
    linarith [hid]
  have hSeq : Tendsto (fun r : ℕ => aSq p q
      * ((r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2)) atTop (nhds (CFSq p q)) :=
    hlim.congr' (Filter.EventuallyEq.symm hidentity)
  have haSq : aSq p q ≠ 0 := by
    unfold aSq
    have hρ0 : 0 ≤ (1 - p) / p := rho_nonneg hp1 hp2
    have hρ1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
    have h1 : (0 : ℝ) < 1 - ((1 - p) / p) ^ 2 := by nlinarith
    exact ne_of_gt (mul_pos hq0 h1)
  have hfinal : Tendsto (fun r : ℕ =>
      (aSq p q)⁻¹ * (aSq p q * ((r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2)))
      atTop (nhds ((aSq p q)⁻¹ * CFSq p q)) :=
    hSeq.const_mul _
  have hfinal' : Tendsto (fun r : ℕ =>
      (r : ℝ)⁻¹ * ∑ k ∈ Finset.range r, (hof p ω k) ^ 2) atTop (nhds ((aSq p q)⁻¹ * CFSq p q)) := by
    refine hfinal.congr' ?_
    filter_upwards with r
    field_simp
  have hK : (aSq p q)⁻¹ * CFSq p q = Ksq p q := by
    unfold Ksq
    rw [div_eq_mul_inv]
    ring
  rwa [hK] at hfinal'


/-! ### 6. The actual uniform array: the quenched spatial average of `h_j²` -/

/-- **The second display of `(spav)` on the actual uniform array.**  For every walker family
`j`, the spatial average of `h_j²` along the actual site marks converges almost surely to the
explicit constant `Ksq p q`; in particular the quenched constant does not depend on `N`. -/
theorem tendsto_hof_sq_average_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ j : Fin N,
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
          ∑ x ∈ Finset.range r, (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2)
        atTop (nhds (Ksq p ((1 - p) ^ (m - 1)))) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < (1 - p) ^ (m - 1) := qpos hp2
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := qle_one hp1 hp2 (by omega)
  haveI : IsProbabilityMeasure (boolMeasure ((1 - p) ^ (m - 1))) :=
    isProbabilityMeasure_boolMeasure hq0.le hq1
  have hsingle := tendsto_hof_sq_average (p := p) hp1 hp2 hm
  have hall : ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (boolMeasure ((1 - p) ^ (m - 1)))), ∀ j : Fin N,
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
          ∑ x ∈ Finset.range r, (hof p (ω j) x) ^ 2)
        atTop (nhds (Ksq p ((1 - p) ^ (m - 1)))) :=
    (ae_all_iff (μ := SwarmMarks.markMeasureN N (boolMeasure ((1 - p) ^ (m - 1))))
      (ι := Fin N)).mpr (fun j => SwarmMarks.markMeasureN_ae N j hsingle)
  exact (SwarmLogRatio.measurePreserving_siteMarksN (N := N) hp0 hp2 m).quasiMeasurePreserving.ae
    hall

/-- **The quenched linear spatial bound in the shape consumed by `SwarmOcc.Jsum_bound`.**

There is a constant `K`, depending only on `m` and `p`, such that for almost every environment
and every walker family `j` the partial sums of `h_j²` grow at most linearly: eventually
`∑_{x<r} h_j(x)² ≤ K r`.  This is exactly the hypothesis `hces` of `Jsum_bound` (up to the
harmless index shift `x ↦ x-1`, whose difference is a single boundary term bounded by `(Kmom)`). -/
theorem exists_hof_sq_linear_bound_array {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ j : Fin N,
      ∃ R₀ : ℕ, ∀ r ≥ R₀,
        ∑ x ∈ Finset.range r, (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 ≤ K * r := by
  set KK : ℝ := |Ksq p ((1 - p) ^ (m - 1))| + 1 with hKKdef
  have hKK : Ksq p ((1 - p) ^ (m - 1)) < KK := by
    rw [hKKdef]
    have := le_abs_self (Ksq p ((1 - p) ^ (m - 1)))
    linarith
  have hpos : 0 < KK := by rw [hKKdef]; positivity
  refine ⟨KK, hpos, ?_⟩
  filter_upwards [tendsto_hof_sq_average_array (N := N) hp1 hp2 hm] with U hU
  intro j
  have hev : ∀ᶠ r : ℕ in atTop, (r : ℝ)⁻¹ *
      ∑ x ∈ Finset.range r, (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 < KK :=
    (hU j).eventually (isOpen_Iio.mem_nhds hKK)
  have hev2 : ∀ᶠ r : ℕ in atTop,
      ∑ x ∈ Finset.range r, (hof p (SwarmLogRatio.siteMarksN p m U j) x) ^ 2 ≤ KK * r := by
    filter_upwards [hev, Filter.eventually_gt_atTop 0] with r hr hr0
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hmul := mul_lt_mul_of_pos_left hr hrpos
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hrpos), one_mul] at hmul
    linarith
  exact eventually_atTop.mp hev2


/-! ### 7. Plugging the quenched bound into the record-cost summation `(Jbound)` -/

/-- **`(Jbound)` with an eventual spatial bound.**  If the record cost is dominated by
`C (g(r_t) + g(r_t+1))` at advance times (the pointwise estimate `Vdrift.J_abs_le`), and the
spatial sums of `g` are eventually at most `K m` (the quenched input, here
`exists_hof_sq_linear_bound_array`), then

    ∑_{t<n} |J_{t+1}| ≤ 2 C ( K (r_n + 2) + ∑_{x<R₀} g x ),

i.e. the paper's `C_ε ∑_{x<M} h² ≤ C M + O(1)` with the finite prefix kept explicit. -/
theorem Jsum_bound_eventual {r : ℕ → ℕ} {g : ℕ → ℝ} {C K : ℝ} {J : ℕ → ℝ} {R₀ : ℕ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hg : ∀ x, 0 ≤ g x) (hC : 0 ≤ C) (hK0 : 0 ≤ K)
    (hJ : ∀ t, |J (t + 1)|
      ≤ C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0))
    (hK : ∀ m ≥ R₀, ∑ x ∈ Finset.range m, g x ≤ K * m) (n : ℕ) :
    ∑ t ∈ Finset.range n, |J (t + 1)|
      ≤ 2 * C * (K * ((r n : ℝ) + 2) + ∑ x ∈ Finset.range R₀, g x) := by
  refine le_trans (SwarmOcc.Jsum_le hmono hg hC hJ n)
    (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have hS : (0 : ℝ) ≤ ∑ x ∈ Finset.range R₀, g x := Finset.sum_nonneg fun x _ => hg x
  rcases le_or_gt R₀ (r n + 2) with hm | hm
  · have h1 := hK (r n + 2) hm
    have hcast : K * ((r n : ℝ) + 2) = K * ↑(r n + 2) := by push_cast; ring
    rw [hcast]
    linarith
  · have hsub : Finset.range (r n + 2) ⊆ Finset.range R₀ := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have h2 : ∑ x ∈ Finset.range (r n + 2), g x ≤ ∑ x ∈ Finset.range R₀, g x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hg x
    have h3 : (0 : ℝ) ≤ K * ((r n : ℝ) + 2) := by positivity
    linarith

/-- **The `J`-slot of `OccupationPieces`, reduced to the constant condition `2CK ≤ 1`.**

Under the hypotheses of `Jsum_bound_eventual` plus `2CK ≤ 1`, the record-cost sum satisfies the
consumer's shape `∑_{t<n} |J_{t+1}| ≤ r_n + n/64` eventually, the finite prefix
`∑_{x<R₀} g x` being absorbed by the onset.  The constant condition is the only remaining
numerical input; with the verified values it is exactly where the paper's free constant
`C(m,p,ε)` enters (see the README). -/
theorem Jsum_bound_pieces {r : ℕ → ℕ} {g : ℕ → ℝ} {C K : ℝ} {J : ℕ → ℝ} {R₀ : ℕ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hg : ∀ x, 0 ≤ g x) (hC : 0 ≤ C) (hK0 : 0 ≤ K)
    (hJ : ∀ t, |J (t + 1)|
      ≤ C * (g (r t) + g (r t + 1)) * (if r (t + 1) = r t + 1 then 1 else 0))
    (hK : ∀ m ≥ R₀, ∑ x ∈ Finset.range m, g x ≤ K * m) (hCK : 2 * C * K ≤ 1) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∑ t ∈ Finset.range n, |J (t + 1)| ≤ (r n : ℝ) + (1 / 64) * n := by
  set S : ℝ := ∑ x ∈ Finset.range R₀, g x with hSdef
  have hS : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun x _ => hg x
  have hev : ∀ᶠ n : ℕ in atTop, (max 1 (64 * (4 * C * K + 2 * C * S)) : ℝ) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun n hn => ?_⟩
  have hNn := hN₀ n hn
  have hN0 : 64 * (4 * C * K + 2 * C * S) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hNn)
  have hbound : ∑ t ∈ Finset.range n, |J (t + 1)|
      ≤ 2 * C * (K * ((r n : ℝ) + 2) + ∑ x ∈ Finset.range R₀, g x) :=
    Jsum_bound_eventual (R₀ := R₀) hmono hg hC hK0 hJ hK n
  rw [← hSdef] at hbound
  have hkey : 2 * C * (K * ((r n : ℝ) + 2) + S) ≤ (r n : ℝ) + (1 / 64) * (n : ℝ) := by
    have h2CK : 2 * C * K * 2 + 2 * C * S ≤ (1 / 64) * (n : ℝ) := by nlinarith [hN0]
    have h4 : 2 * C * K * (r n : ℝ) ≤ (r n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hCK (by positivity : (0 : ℝ) ≤ (r n : ℝ))
      nlinarith [this]
    nlinarith [h2CK, h4, hS]
  linarith

end
end SwarmSpatialSq

/-! ### Audit -/


