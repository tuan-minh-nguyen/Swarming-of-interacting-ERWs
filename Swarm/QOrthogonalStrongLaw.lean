/-
# An adaptedness-free strong law for the raw compensator residual `Qcomp`

`Swarm/QIncrementAdapted.lean` proves that the raw integrand
`ZJinc p m eps i j · 0` is **not** `StronglyMeasurable` for the enlarged-prefix filtration
(`m ≥ 3`, `p ∈ (1/2,1)`, `i ≠ j`).  Hence the raw compensator residual `Qcomp` cannot be fed
to the martingale strong law (`MartingaleLimit.martingale_strong_law`) without adaptedness:      
that theorem needs an adapted martingale.

This module supplies the *weakest natural replacement*: the martingale property is used by
`martingale_strong_law` only through

* `∫ ΔQ_k = 0`              (centred increments),
* `∫ ΔQ_j · ΔQ_k = 0`       (pairwise uncorrelated increments, from the conditional-expectation
  pull-out in `MartingaleLimit.integral_mul_inc_eq_zero`),
* the summability `∑ k, (k+1)⁻² ∫ (ΔQ_k)² < ∞`.

`strong_law_of_orthogonal` below proves that these three properties alone — with **no filtration,
no adaptedness, no maximal inequality for `Q` itself** — already give `Q n / n → 0` a.s. and the
one-sided form `∀ δ > 0, eventually Q n ≥ -δ n` required by `ActualBudgetInterfaces.QResidual`
and by `BallisticInterfaceActual.InterfacesOGen`.  The price of dropping adaptedness is a
`log²`-sharpening of the variance criterion (`log²` instead of the paper's unweighted `n⁻²`); the
sharpened criterion is derived from the same `maxmom`-type second-moment input the paper uses,
and the extra factor is harmless for polylogarithmically growing second moments.

Nothing here is a proof of `hQ` at the actual model: the missing input is exactly the
uncorrelatedness hypothesis, which is *strictly weaker* than the raw adaptedness that
`QIncrementAdapted.lean` refutes (see `README.md` in this directory).

Self-contained: `import Mathlib` only.
-/
import Swarm.Imports
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace QOrth

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 1. Products of square integrable functions are integrable -/

/-- Cauchy–Schwarz at the level of integrability: the product of two `L²` functions is `L¹`. -/
theorem integrable_mul_of_sq {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) : Integrable (fun ω => f ω * g ω) μ := by
  have hmaj : Integrable (fun ω => (f ω ^ 2 + g ω ^ 2) / 2) μ := (hf2.add hg2).div_const 2
  refine Integrable.mono' hmaj (hf.mul hg) ?_
  filter_upwards with ω
  have h3 : |f ω| * |g ω| ≤ (f ω ^ 2 + g ω ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]
  rw [Real.norm_eq_abs, abs_mul]
  exact h3

/-! ## 2. Variance of a block sum -/

/-- The block sum `∑_{j < L} d (a + j)`. -/
noncomputable def blk (d : ℕ → Ω → ℝ) (a L : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range L, d (a + j) ω

/-- The partial sum process `Q n = ∑_{t < n} d t`. -/
noncomputable def Q (d : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, d t ω

theorem blk_sub (d : ℕ → Ω → ℝ) (a L : ℕ) (ω : Ω) :
    blk d a L ω = Q d (a + L) ω - Q d a ω := by
  simp only [blk, Q, Finset.sum_range_add (fun t => d t ω) a L]
  ring

/-- **Block variance identity.** For centred, pairwise uncorrelated `L²` increments the second
moment of a block sum is exactly the sum of the increments' second moments. -/
theorem integral_blk_sq (d : ℕ → Ω → ℝ)
    (hint : ∀ t, Integrable (d t) μ)
    (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0)
    (a L : ℕ) :
    ∫ ω, (blk d a L ω) ^ 2 ∂μ = ∑ j ∈ Finset.range L, ∫ ω, (d (a + j) ω) ^ 2 ∂μ := by
  have hmul : ∀ s t : ℕ, Integrable (fun ω => d s ω * d t ω) μ := by
    intro s t
    rcases eq_or_ne s t with h | h
    · subst h
      simpa only [sq] using hL2 s
    · exact integrable_mul_of_sq (hint s).aestronglyMeasurable
        (hint t).aestronglyMeasurable (hL2 s) (hL2 t)
  have hpt : ∀ ω, (blk d a L ω) ^ 2
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, d (a + i) ω * d (a + j) ω := by
    intro ω
    simp only [blk, sq, Finset.sum_mul_sum]
  calc ∫ ω, (blk d a L ω) ^ 2 ∂μ
      = ∫ ω, ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          d (a + i) ω * d (a + j) ω ∂μ := by rw [funext hpt]
    _ = ∑ i ∈ Finset.range L, ∫ ω, ∑ j ∈ Finset.range L,
          d (a + i) ω * d (a + j) ω ∂μ := by
        rw [integral_finsetSum]
        intro i _
        exact integrable_finsetSum _ (fun j _ => hmul (a + i) (a + j))
    _ = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          ∫ ω, d (a + i) ω * d (a + j) ω ∂μ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finsetSum]
        intro j _
        exact hmul (a + i) (a + j)
    _ = ∑ i ∈ Finset.range L, ∫ ω, d (a + i) ω * d (a + i) ω ∂μ := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _ hji
          exact horth (a + i) (a + j) (fun h => hji (by omega))
        · intro hi'
          exact absurd hi hi'
    _ = ∑ i ∈ Finset.range L, ∫ ω, (d (a + i) ω) ^ 2 ∂μ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [sq]

/-! ## 3. Dyadic indices -/

/-- The largest multiple of `2 ^ r` that is at most `n`. -/
def dy (n r : ℕ) : ℕ := (n / 2 ^ r) * 2 ^ r

theorem dy_zero (n : ℕ) : dy n 0 = n := by simp [dy]

theorem dy_top {n K : ℕ} (h : n < 2 ^ K) : dy n K = 0 := by
  simp [dy, Nat.div_eq_of_lt h]

theorem dy_dvd (n r : ℕ) : 2 ^ r ∣ dy n (r + 1) :=
  ⟨n / 2 ^ (r + 1) * 2, by simp only [dy, pow_succ]; ring⟩

theorem dy_step (n r : ℕ) : dy n r = dy n (r + 1) + 2 ^ r * ((n / 2 ^ r) % 2) := by
  have h1 : n / 2 ^ (r + 1) = n / 2 ^ r / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hq : n / 2 ^ r = 2 * (n / 2 ^ (r + 1)) + (n / 2 ^ r) % 2 := by
    rw [h1]
    exact (Nat.div_add_mod (n / 2 ^ r) 2).symm
  have key : (n / 2 ^ r) * 2 ^ r
      = (n / 2 ^ (r + 1)) * 2 ^ (r + 1) + 2 ^ r * ((n / 2 ^ r) % 2) := by
    conv_lhs => rw [hq]
    rw [pow_succ (2 : ℕ) r]
    ring
  simpa only [dy] using key

theorem dy_mod_two (n r : ℕ) : (n / 2 ^ r) % 2 = 0 ∨ (n / 2 ^ r) % 2 = 1 := by
  have h := Nat.mod_lt (n / 2 ^ r) (by norm_num : 0 < 2)
  omega

theorem dy_le (n r : ℕ) : dy n r ≤ n := by
  simp only [dy]
  exact Nat.div_mul_le_self n (2 ^ r)

/-- The telescoping identity behind the dyadic decomposition. -/
theorem sum_dy_telescope (S : ℕ → ℝ) (n K : ℕ) (h : n < 2 ^ K) :
    ∑ r ∈ Finset.range K, (S (dy n r) - S (dy n (r + 1))) = S n - S 0 := by
  have htel : ∑ r ∈ Finset.range K, (S (dy n (r + 1)) - S (dy n r)) = S (dy n K) - S (dy n 0) :=
    Finset.sum_range_sub (fun i => S (dy n i)) K
  calc ∑ r ∈ Finset.range K, (S (dy n r) - S (dy n (r + 1)))
      = -∑ r ∈ Finset.range K, (S (dy n (r + 1)) - S (dy n r)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun r _ => by ring)
    _ = -(S (dy n K) - S (dy n 0)) := by rw [htel]
    _ = S n - S 0 := by rw [dy_top h, dy_zero]; ring

end QOrth

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace QOrth

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 4. Pointwise dyadic bound -/

section Pointwise

variable (S : ℕ → ℝ)

/-- Each dyadic telescoping term is either zero or one aligned dyadic block. -/
theorem dy_term_le_level {n K r : ℕ} (hn : n < 2 ^ K) (hr : r < K) :
    (S (dy n r) - S (dy n (r + 1))) ^ 2
      ≤ ∑ ℓ ∈ Finset.range (2 ^ (K - r)),
          (S ((ℓ + 1) * 2 ^ r) - S (ℓ * 2 ^ r)) ^ 2 := by
  have hstep := dy_step n r
  have hmono : dy n (r + 1) ≤ n := dy_le n (r + 1)
  have hpow : (2 : ℕ) ^ K = 2 ^ r * 2 ^ (K - r) := by
    have hrK : r + (K - r) = K := by omega
    conv_lhs => rw [← hrK]
    rw [pow_add]
  rcases dy_mod_two n r with hb | hb
  · rw [hstep, hb, Nat.mul_zero, add_zero, sub_self, sq, mul_zero]
    exact Finset.sum_nonneg (fun ℓ _ => sq_nonneg _)
  · obtain ⟨ℓ, hℓ⟩ := dy_dvd n r
    have hℓ' : dy n (r + 1) = ℓ * 2 ^ r := by rw [hℓ, Nat.mul_comm]
    have hℓlt : ℓ < 2 ^ (K - r) := by
      have h2 : 2 ^ r * ℓ < 2 ^ r * 2 ^ (K - r) := by
        rw [← hpow, ← hℓ]
        exact lt_of_le_of_lt hmono hn
      exact Nat.lt_of_mul_lt_mul_left h2
    have hgoal : (S (dy n r) - S (dy n (r + 1))) ^ 2
        = (S ((ℓ + 1) * 2 ^ r) - S (ℓ * 2 ^ r)) ^ 2 := by
      rw [hstep, hb, Nat.mul_one, hℓ', ← Nat.succ_mul]
    rw [hgoal]
    exact Finset.single_le_sum (f := fun ℓ => (S ((ℓ + 1) * 2 ^ r) - S (ℓ * 2 ^ r)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr hℓlt)

/-- **Pointwise dyadic maximal bound.**  For `S` starting at `0` and `n < 2 ^ K`, the square of
`S n` is bounded by `K` times the sum of the squared dyadic block increments. -/
theorem pointwise_dyadic_bound (hS0 : S 0 = 0) {n K : ℕ} (hn : n < 2 ^ K) :
    (S n) ^ 2 ≤ (K : ℝ) * ∑ r ∈ Finset.range K,
      ∑ ℓ ∈ Finset.range (2 ^ (K - r)), (S ((ℓ + 1) * 2 ^ r) - S (ℓ * 2 ^ r)) ^ 2 := by
  have htel := sum_dy_telescope S n K hn
  have hEq : S n = ∑ r ∈ Finset.range K, (S (dy n r) - S (dy n (r + 1))) := by
    rw [htel, hS0, sub_zero]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range K)
    (f := fun r => S (dy n r) - S (dy n (r + 1)))
  have hcard : (((Finset.range K).card : ℕ) : ℝ) = (K : ℝ) := by simp
  rw [hcard] at hcs
  rw [hEq]
  refine le_trans hcs (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K))
  exact Finset.sum_le_sum (fun r hr => dy_term_le_level S hn (Finset.mem_range.mp hr))

end Pointwise

/-! ## 5. Level sums -/

/-- Reindexing: the sum over the dyadic blocks of level `r` in `[0, 2 ^ (M + r))` is the full
sum over `[0, 2 ^ (M + r))`. -/
theorem sum_levels (r M : ℕ) (f : ℕ → ℝ) :
    ∑ ℓ ∈ Finset.range (2 ^ M), ∑ j ∈ Finset.range (2 ^ r), f (ℓ * 2 ^ r + j)
      = ∑ t ∈ Finset.range (2 ^ (M + r)), f t := by
  revert f
  induction M with
  | zero => intro f; simp
  | succ M ih =>
      intro f
      have hM : (2 : ℕ) ^ (M + 1) = 2 ^ M + 2 ^ M := by
        rw [pow_succ]; ring
      have hshift : ∀ ℓ j : ℕ, (2 ^ M + ℓ) * 2 ^ r + j = 2 ^ (M + r) + (ℓ * 2 ^ r + j) := by
        intro ℓ j
        rw [add_mul, ← pow_add]
        ring
      have hih2 : ∑ ℓ ∈ Finset.range (2 ^ M), ∑ j ∈ Finset.range (2 ^ r),
            f (2 ^ (M + r) + (ℓ * 2 ^ r + j))
          = ∑ t ∈ Finset.range (2 ^ (M + r)), f (2 ^ (M + r) + t) :=
        ih (fun t => f (2 ^ (M + r) + t))
      have hlast : 2 ^ (M + r) + 2 ^ (M + r) = 2 ^ (M + 1 + r) := by
        have hidx : M + 1 + r = (M + r) + 1 := by omega
        rw [hidx, pow_succ]; ring
      rw [hM, Finset.sum_range_add, ih]
      simp only [hshift]
      rw [hih2, ← Finset.sum_range_add, hlast]

end QOrth

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace QOrth

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite pointwise sum of `AEStronglyMeasurable` functions is `AEStronglyMeasurable`. -/
theorem aestronglyMeasurable_sum_pointwise {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using aestronglyMeasurable_const (μ := μ) (b := (0 : ℝ))
  | insert a s ha ih =>
      have h1 : AEStronglyMeasurable (fun ω => f a ω) μ := h a (Finset.mem_insert_self a s)
      have h2 : AEStronglyMeasurable (fun ω => ∑ i ∈ s, f i ω) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hsum : AEStronglyMeasurable
          ((fun ω => f a ω) + fun ω => ∑ i ∈ s, f i ω) μ := h1.add h2
      have heq : ((fun ω => f a ω) + fun ω => ∑ i ∈ s, f i ω)
          = fun ω => f a ω + ∑ i ∈ s, f i ω := by
        funext ω
        rw [Pi.add_apply]
      rw [heq] at hsum
      simpa only [Finset.sum_insert ha] using hsum

/-- Squares of block sums are integrable. -/
theorem integrable_blk_sq {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (a L : ℕ) : Integrable (fun ω => (blk d a L ω) ^ 2) μ := by
  have hsum2 : Integrable (fun ω => ∑ j ∈ Finset.range L, (d (a + j) ω) ^ 2) μ :=
    integrable_finsetSum (Finset.range L) (fun j _ => hL2 _)
  have hmeas : AEStronglyMeasurable (fun ω => blk d a L ω) μ := by
    simpa only [blk] using aestronglyMeasurable_sum_pointwise (μ := μ) (Finset.range L)
      (f := fun j ω => d (a + j) ω) (fun j _ => (hint _).aestronglyMeasurable)
  refine Integrable.mono' (hsum2.const_mul ((L : ℕ) : ℝ)) (hmeas.pow 2) ?_
  filter_upwards with ω
  have h1 : (blk d a L ω) ^ 2 ≤ ((L : ℕ) : ℝ) * ∑ j ∈ Finset.range L, (d (a + j) ω) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range L)
      (f := fun j => d (a + j) ω)
    simpa only [blk, Finset.card_range] using h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h1

/-- Iterated integration over a double finset sum. -/
theorem integral_double_sum {ι κ : Type*} (s : Finset ι) (t : ι → Finset κ)
    (g : ι → κ → Ω → ℝ) (h : ∀ i ∈ s, ∀ j ∈ t i, Integrable (g i j) μ) :
    ∫ ω, ∑ i ∈ s, ∑ j ∈ t i, g i j ω ∂μ = ∑ i ∈ s, ∑ j ∈ t i, ∫ ω, g i j ω ∂μ := by
  rw [integral_finsetSum (s := s) (f := fun i ω => ∑ j ∈ t i, g i j ω)]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [integral_finsetSum (s := t i) (f := fun j ω => g i j ω)]
    exact fun j hj => h i hi j hj
  · exact fun i hi => integrable_finsetSum _ (fun j hj => h i hi j hj)

/-- The dyadic functional whose expectation the maximal bound controls. -/
noncomputable def dyaFun (d : ℕ → Ω → ℝ) (K : ℕ) : Ω → ℝ :=
  fun ω => ((K : ℝ) + 1) * ∑ r ∈ Finset.range (K + 1),
    ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
      (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2

/-- The squared level term is integrable. -/
theorem integrable_level_term {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (r ℓ : ℕ) :
    Integrable (fun ω => (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2) μ := by
  have hpt : (fun ω => (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2)
      = fun ω => (blk d (ℓ * 2 ^ r) (2 ^ r) ω) ^ 2 := by
    funext ω
    rw [blk_sub, Nat.succ_mul]
  rw [hpt]
  exact integrable_blk_sq hint hL2 (ℓ * 2 ^ r) (2 ^ r)

theorem integrable_dyaFun {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (K : ℕ) : Integrable (dyaFun d K) μ := by
  have hinner : Integrable (fun ω => ∑ r ∈ Finset.range (K + 1),
      ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
        (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2) μ := by
    refine integrable_finsetSum (Finset.range (K + 1)) (fun r _ => ?_)
    exact integrable_finsetSum (Finset.range (2 ^ (K + 1 - r)))
      (fun ℓ _ => integrable_level_term hint hL2 r ℓ)
  exact hinner.const_mul _

/-- The variance of the level-`r` block sum is the sum of the variance density. -/
theorem integral_blk_level {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0) (r ℓ : ℕ) :
    ∫ ω, (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2 ∂μ
      = ∑ j ∈ Finset.range (2 ^ r), ∫ ω, (d (ℓ * 2 ^ r + j) ω) ^ 2 ∂μ := by
  have hpt : ∀ ω, Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω
      = blk d (ℓ * 2 ^ r) (2 ^ r) ω := by
    intro ω
    rw [blk_sub]
    congr 2
    rw [Nat.succ_mul]
  simp only [hpt]
  exact integral_blk_sq d hint hL2 horth (ℓ * 2 ^ r) (2 ^ r)

/-- **The exact expectation of the dyadic functional.** -/
theorem integral_dyaFun {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0) (K : ℕ) :
    ∫ ω, dyaFun d K ω ∂μ
      = ((K : ℝ) + 1) ^ 2 * ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ := by
  have hlevel : ∀ r ∈ Finset.range (K + 1),
      ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
        ∫ ω, (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2 ∂μ
      = ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ := by
    intro r hr
    have hrK : r ≤ K + 1 := by
      have := Finset.mem_range.mp hr
      omega
    have h := sum_levels r (K + 1 - r) (fun t => ∫ ω, (d t ω) ^ 2 ∂μ)
    have hsub : K + 1 - r + r = K + 1 := Nat.sub_add_cancel hrK
    calc ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
        ∫ ω, (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2 ∂μ
        = ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
            ∑ j ∈ Finset.range (2 ^ r), ∫ ω, (d (ℓ * 2 ^ r + j) ω) ^ 2 ∂μ := by
          exact Finset.sum_congr rfl (fun ℓ _ => integral_blk_level hint hL2 horth r ℓ)
      _ = ∑ t ∈ Finset.range (2 ^ (K + 1 - r + r)), ∫ ω, (d t ω) ^ 2 ∂μ := h
      _ = ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ := by rw [hsub]
  have hInt : ∫ ω, dyaFun d K ω ∂μ
      = ((K : ℝ) + 1) * ∑ r ∈ Finset.range (K + 1),
          ∑ ℓ ∈ Finset.range (2 ^ (K + 1 - r)),
            ∫ ω, (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2 ∂μ := by
    simp only [dyaFun]
    rw [integral_const_mul]
    congr 1
    exact integral_double_sum (Finset.range (K + 1)) (fun r => Finset.range (2 ^ (K + 1 - r)))
      (fun r ℓ ω => (Q d ((ℓ + 1) * 2 ^ r) ω - Q d (ℓ * 2 ^ r) ω) ^ 2)
      (fun r _ ℓ _ => integrable_level_term hint hL2 r ℓ)
  rw [hInt, Finset.sum_congr rfl hlevel, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Maximal-type bound.** -/
theorem measure_exists_gt {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0)
    {K : ℕ} {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) ^ 2 / c ^ 2
          * ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ) := by
  have hsub : {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}
      ⊆ {ω | c ^ 2 ≤ dyaFun d K ω} := by
    rintro ω ⟨n, hn, hgt⟩
    have hpt := pointwise_dyadic_bound (fun m => Q d m ω) (by simp [Q]) hn
    have h2 : c ^ 2 < (Q d n ω) ^ 2 := by
      nlinarith [abs_nonneg (Q d n ω), abs_mul_abs_self (Q d n ω), sq_abs (Q d n ω)]
    have h3 : (Q d n ω) ^ 2 ≤ dyaFun d K ω := by
      simpa only [dyaFun, Nat.cast_add, Nat.cast_one] using hpt
    exact le_of_lt (lt_of_lt_of_le h2 h3)
  have hF := integrable_dyaFun (μ := μ) hint hL2 K
  have hnonneg : 0 ≤ᵐ[μ] dyaFun d K := Filter.Eventually.of_forall (fun ω => by
    have h1 : (0 : ℝ) ≤ ((K : ℝ) + 1) := by positivity
    refine mul_nonneg h1 (Finset.sum_nonneg (fun r _ => ?_))
    exact Finset.sum_nonneg (fun ℓ _ => sq_nonneg _))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hF (c ^ 2)
  have hreal : μ.real {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}
      ≤ ((K : ℝ) + 1) ^ 2 / c ^ 2
          * ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ := by
    have hle : μ.real {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}
        ≤ μ.real {ω | c ^ 2 ≤ dyaFun d K ω} := measureReal_mono hsub
    have h2 : μ.real {ω | c ^ 2 ≤ dyaFun d K ω}
        ≤ (∫ ω, dyaFun d K ω ∂μ) / c ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      simpa only [mul_comm] using hmarkov
    have h3 : ∫ ω, dyaFun d K ω ∂μ
        = ((K : ℝ) + 1) ^ 2 * ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ :=
      integral_dyaFun hint hL2 horth K
    rw [h3] at h2
    refine le_trans hle (le_trans h2 (le_of_eq ?_))
    field_simp
  calc μ {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}
      = ENNReal.ofReal (μ.real {ω | ∃ n, n < 2 ^ (K + 1) ∧ c < |Q d n ω|}) :=
        (ofReal_measureReal (μ := μ) (s := _)).symm
    _ ≤ ENNReal.ofReal (((K : ℝ) + 1) ^ 2 / c ^ 2
          * ∑ t ∈ Finset.range (2 ^ (K + 1)), ∫ ω, (d t ω) ^ 2 ∂μ) :=
        ENNReal.ofReal_le_ofReal hreal

end QOrth

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace QOrth

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      have h : n ≤ 2 ^ n := le_two_pow n
      have h1 : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
      rw [pow_succ]
      omega

/-- Every positive `n` lies in a dyadic block. -/
theorem exists_dyadic_block : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · refine ⟨0, by omega, by omega⟩
    · have hn2 : 1 ≤ n / 2 := by omega
      have hlt : n / 2 < n := by omega
      obtain ⟨k, hk1, hk2⟩ := ih (n / 2) hlt hn2
      have hpk : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have hpk2 : (2 : ℕ) ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
      refine ⟨k + 1, by omega, by omega⟩

/-- **One fixed scale.**  At scale `δ = 1/(j+1)` the dyadic blocks are eventually good. -/
theorem ae_eventually_block_le {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0)
    (hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / 4 ^ k
      * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ)) (j : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ n, 2 ^ k ≤ n → n < 2 ^ (k + 1) →
      |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * 2 ^ k := by
  have hgnn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) ^ 2 / 4 ^ k
      * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ := by
    intro k
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun t _ => ?_))
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hbound : ∀ k : ℕ,
      μ {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
          (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}
        ≤ ENNReal.ofReal (((j : ℝ) + 1) ^ 2 *
          (((k : ℝ) + 1) ^ 2 / 4 ^ k
            * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ)) := by
    intro k
    have hc : 0 < (1 / ((j : ℝ) + 1)) * 2 ^ k := by positivity
    have hsub : {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
        (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}
        ⊆ {ω | ∃ n, n < 2 ^ (k + 1) ∧ (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|} := by
      rintro ω ⟨n, _, hn2, hgt⟩
      exact ⟨n, hn2, hgt⟩
    refine le_trans (measure_mono hsub) (le_trans
      (measure_exists_gt hint hL2 horth (K := k) hc) (le_of_eq ?_))
    have h4 : ((4 : ℝ) ^ k) ≠ 0 := by positivity
    have hc2 : ((1 / ((j : ℝ) + 1)) * 2 ^ k) ^ 2 = 4 ^ k / ((j : ℝ) + 1) ^ 2 := by
      have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
        have h1 : (4 : ℝ) = 2 ^ 2 := by norm_num
        conv_lhs => rw [h1, ← pow_mul]
        rw [← pow_mul]
        congr 1
        omega
      rw [h4, mul_pow, div_pow, one_pow]
      ring
    rw [hc2]
    field_simp
  have hsumμ : (∑' k, μ {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
      (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}) ≠ ∞ := by
    have h1 : ∑' k, μ {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
        (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}
        ≤ ∑' k : ℕ, ENNReal.ofReal (((j : ℝ) + 1) ^ 2 *
          (((k : ℝ) + 1) ^ 2 / 4 ^ k
            * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ)) :=
      ENNReal.tsum_le_tsum hbound
    have h2 : ∑' k : ℕ, ENNReal.ofReal (((j : ℝ) + 1) ^ 2 *
          (((k : ℝ) + 1) ^ 2 / 4 ^ k
            * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ))
        = ENNReal.ofReal (((j : ℝ) + 1) ^ 2 * ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 / 4 ^ k
            * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (hgnn k))
        (hsum.mul_left _), tsum_mul_left]
    rw [h2] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hBC : μ (limsup (fun k => {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
      (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}) atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsumμ
  have hae : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ¬ (∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
      (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|) := by
    rw [ae_iff]
    have hset : {ω | ¬ ∀ᶠ k in atTop, ¬ (∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
        (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|)}
        = limsup (fun k => {ω | ∃ n, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) ∧
            (1 / ((j : ℝ) + 1)) * 2 ^ k < |Q d n ω|}) atTop := by
      ext ω
      simp only [Set.mem_ofPred_eq, not_eventually, not_not, mem_limsup_iff_frequently_mem]
    rw [hset, hBC]
  filter_upwards [hae] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨2 ^ K, fun k hk => ?_⟩
  intro n hn1 hn2
  have hkK : K ≤ k := le_trans (le_two_pow K) hk
  exact le_of_not_gt (fun hcon => hK k hkK ⟨n, hn1, hn2, hcon⟩)

/-- **The strong law for uncorrelated increments.**  No filtration and no adaptedness are used:
centredness plus pairwise uncorrelatedness of the increments, and a `log²`-sharpened variance
criterion, give `Q n / n → 0` almost surely. -/
theorem strong_law_of_orthogonal {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0)
    (hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / 4 ^ k
      * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Q d n ω / n) atTop (𝓝 0) := by
  have key : ∀ j : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * n := by
    intro j
    filter_upwards [ae_eventually_block_le hint hL2 horth hsum j] with ω hω
    obtain ⟨K, hK⟩ := eventually_atTop.1 hω
    refine eventually_atTop.2 ⟨max 1 (2 ^ K), fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, h2k, hlt⟩ := exists_dyadic_block n hn1
    have hkK : K ≤ k := by
      by_contra hc
      push_neg at hc
      have hle : 2 ^ (k + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hb := hK k hkK n h2k hlt
    calc |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * 2 ^ k := hb
      _ ≤ (1 / ((j : ℝ) + 1)) * n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast h2k
  have hall : ∀ᵐ ω ∂μ, ∀ j : ℕ, ∀ᶠ n in atTop,
      |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * n := by
    rw [ae_iff]
    have hset : {ω | ¬ ∀ j : ℕ, ∀ᶠ n in atTop,
        |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * n}
        = ⋃ j : ℕ, {ω | ¬ ∀ᶠ n in atTop,
            |Q d n ω| ≤ (1 / ((j : ℝ) + 1)) * n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, not_forall]
    rw [hset]
    exact measure_iUnion_null (fun j => by
      have h := key j
      rwa [ae_iff] at h)
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hj : (1 : ℝ) / ((m : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    have h1 : 1 < ε * (m : ℝ) := by
      rw [div_lt_iff₀ hε] at hm
      simpa only [one_div, mul_comm] using hm
    nlinarith [hε.le]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω m)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (le_of_lt hpos), div_lt_iff₀ hpos]
  calc |Q d n ω| ≤ (1 / ((m : ℝ) + 1)) * n := hle
    _ < ε * n := mul_lt_mul_of_pos_right hj hpos

/-- **The one-sided form required by the occupation interface**: for every `δ > 0` the raw
partial-sum process is eventually above `-δ n`. -/
theorem eventually_lower_bound {d : ℕ → Ω → ℝ}
    (hint : ∀ t, Integrable (d t) μ) (hL2 : ∀ t, Integrable (fun ω => (d t ω) ^ 2) μ)
    (horth : ∀ s t, s ≠ t → ∫ ω, d s ω * d t ω ∂μ = 0)
    (hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 / 4 ^ k
      * ∑ t ∈ Finset.range (2 ^ (k + 1)), ∫ ω, (d t ω) ^ 2 ∂μ)) :
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -(δ * (n : ℝ)) ≤ Q d n ω := by
  have hmain := strong_law_of_orthogonal hint hL2 horth hsum
  filter_upwards [hmain] with ω hω
  intro δ hδ
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hω (δ / 2) hhalf)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle := hN n (le_trans (le_max_left _ _) hn)
  have hle' : |Q d n ω| / (n : ℝ) < δ / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (le_of_lt hpos)] using hle
  rw [div_lt_iff₀ hpos] at hle'
  have habs := (abs_lt.mp hle').1
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith [habs, hδ, hnn]

end QOrth
