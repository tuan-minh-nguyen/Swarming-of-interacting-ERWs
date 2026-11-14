/-
  **`locsum` residual R3, second-moment route: the sum of the squared ratio products.**

  The comparison `R1Identity.hof_sq_le_Q_add` reduces `(locsum)` for the harmonic functions to a
  bound on `Σ_x Pz(x,ℓ)²` over the window, where `Pz p x ℓ = Π_{u<ℓ} rho(x-u)`.  The paper
  obtains such a bound from a Chernoff bound on the number of marks in each window.  A *weaker*
  estimate suffices and needs no Chernoff and no sliding-window union: the second moment

      ∫ (Pz(x,ℓ))² dμ = b^ℓ,     b = E[rho²] = 1 - q + q ((1-p)/p)² < 1,

  gives, by Markov's inequality for the *sum* over the window,

      P ( Σ_{x∈[a0,b0)} Pz(x,ℓ)² > L^{1/16} ) ≤ C L^{1/16·15} b^ℓ ,

  and `b^ℓ = e^{-κ L^{1/16}}` with `κ = -log b > 0`.  This file proves the moment identity
  (`integral_Pz_sq`, via block independence and the ratio law of `L2Moments`) and the array-level
  sum event.
-/
import Swarm.R2LocMax
import Swarm.R1Obstruction
import Swarm.L2Moments

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

namespace LocSumR1

noncomputable section

/-! ### `Pz` depends only on its block, and is congruent -/

lemma Pz_congr (p : ℝ) (k x : ℕ) {ω ω' : ℕ → Bool} (h : ∀ u < k, ω (x - u) = ω' (x - u)) :
    LocSum.Pz p x k ω = LocSum.Pz p x k ω' := by
  unfold LocSum.Pz
  exact Finset.prod_congr rfl fun u hu => by
    simp only [LocSum.rat]
    rw [h u (Finset.mem_range.1 hu)]

/-- `Pz p x k` as a functional of the mark block `blkS k x`. -/
def Pzblk (p : ℝ) (k x : ℕ) (v : (↑(LocSum.blkS k x)) → Bool) : ℝ :=
  LocSum.Pz p x k (LocSum.ext (LocSum.blkS k x) v)

lemma measurable_Pzblk (p : ℝ) (k x : ℕ) : Measurable (Pzblk p k x) :=
  measurable_of_finite _

lemma Pz_eq_Pzblk (p : ℝ) (k x : ℕ) (ω : ℕ → Bool) :
    LocSum.Pz p x k ω = Pzblk p k x (Finset.restrict (LocSum.blkS k x) ω) := by
  unfold Pzblk
  exact (Pz_congr p k x (fun u hu =>
    LocSum.ext_restrict (LocSum.blkS k x) ω (x - u) (LocSum.mem_blkS hu))).symm

/-- The site `x-k` is not in the block `{x, …, x-k+1}`. -/
lemma not_mem_blkS_sub {k x : ℕ} (hk : k ≤ x) : x - k ∉ LocSum.blkS k x := by
  intro h
  obtain ⟨u, hu, hux⟩ := Finset.mem_image.1 h
  simp only [Finset.mem_range] at hu
  omega

/-- **Independence of `Pz(x,k)²` from `rho(x-k)²`.** -/
lemma indepFun_Pz_sq_rat_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : ℝ) (k x : ℕ) (hk : k ≤ x) :
    IndepFun (fun ω : ℕ → Bool => (LocSum.Pz p x k ω) ^ 2)
      (fun ω : ℕ → Bool => (LocSum.rat p ω (x - k)) ^ 2) (markMeasure (boolMeasure q)) := by
  classical
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have hdisj : Disjoint (LocSum.blkS k x) ({x - k} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    exact not_mem_blkS_sub hk
  have hbase := (iIndepFun_eval (μB := boolMeasure q)).indepFun_finset (LocSum.blkS k x)
    ({x - k} : Finset ℕ) hdisj (fun i => measurable_pi_apply i)
  have hleft : Measurable (fun v : (↑(LocSum.blkS k x)) → Bool =>
      (Pzblk p k x v) ^ 2) := (measurable_Pzblk p k x).pow_const 2
  have hright : Measurable (fun v : (↑({x - k} : Finset ℕ)) → Bool =>
      (LocSum.rat p (LocSum.ext {x - k} v) (x - k)) ^ 2) := measurable_of_finite _
  have hcomp := hbase.comp hleft hright
  have e1 : ((fun v : (↑(LocSum.blkS k x)) → Bool => (Pzblk p k x v) ^ 2) ∘
      (fun (a : ℕ → Bool) (i : (LocSum.blkS k x)) => a (i : ℕ)))
      = fun ω : ℕ → Bool => (LocSum.Pz p x k ω) ^ 2 := by
    funext ω
    show (Pzblk p k x (Finset.restrict (LocSum.blkS k x) ω)) ^ 2 = (LocSum.Pz p x k ω) ^ 2
    rw [← Pz_eq_Pzblk]
  have e2 : ((fun v : (↑({x - k} : Finset ℕ)) → Bool =>
        (LocSum.rat p (LocSum.ext {x - k} v) (x - k)) ^ 2) ∘
      (fun (a : ℕ → Bool) (i : ({x - k} : Finset ℕ)) => a (i : ℕ)))
      = fun ω : ℕ → Bool => (LocSum.rat p ω (x - k)) ^ 2 := by
    funext ω
    show (LocSum.rat p (LocSum.ext {x - k} (({x - k} : Finset ℕ).restrict ω)) (x - k)) ^ 2
      = (LocSum.rat p ω (x - k)) ^ 2
    unfold LocSum.rat
    rw [LocSum.ext_restrict _ _ _ (Finset.mem_singleton_self _)]
  rw [e1, e2] at hcomp
  exact hcomp

/-! ### The second moment of `Pz(x,k)` -/

lemma integrable_Pz_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (k x : ℕ) :
    Integrable (fun ω : ℕ → Bool => (LocSum.Pz p x k ω) ^ 2) (markMeasure (boolMeasure q)) := by
  refine LocSum.integrable_of_bound h0 h1 _ 1
    ((LocSum.measurable_Pz p x k).pow_const 2).aestronglyMeasurable ?_
  intro ω
  have h0' := LocSum.Pz_nonneg hp1 hp2 x k ω
  have h1' := LocSum.Pz_le_one hp1 hp2 x k ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

/-- **`E[Pz(x,k)²] = b^k`** for `k ≤ x`. -/
theorem integral_Pz_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (x : ℕ) :
    ∀ k : ℕ, k ≤ x →
      ∫ ω, (LocSum.Pz p x k ω) ^ 2 ∂(markMeasure (boolMeasure q)) = (LocSum.bC p q) ^ k := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  intro k
  induction k with
  | zero => intro _; simp [LocSum.Pz_zero]
  | succ k ih =>
      intro hk
      have hkx : k ≤ x := le_trans (Nat.le_succ k) hk
      have hstep : ∀ ω : ℕ → Bool,
          (LocSum.Pz p x (k + 1) ω) ^ 2
            = (LocSum.Pz p x k ω) ^ 2 * (LocSum.rat p ω (x - k)) ^ 2 := by
        intro ω
        rw [Pz_succ_right]
        ring
      have hind := indepFun_Pz_sq_rat_sq h0 h1 p k x hkx
      have hI1 := integrable_Pz_sq h0 h1 hp1 hp2 k x
      have hI2 : Integrable (fun ω : ℕ → Bool => (LocSum.rat p ω (x - k)) ^ 2)
          (markMeasure (boolMeasure q)) := by
        refine LocSum.integrable_of_bound h0 h1 _ 1
          (((LocSum.measurable_rat p (x - k)).pow_const 2)).aestronglyMeasurable ?_
        intro ω
        have h0' := LocSum.rat_nonneg hp1 hp2 ω (x - k)
        have h1' := LocSum.rat_le_one hp1 hp2 ω (x - k)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith
      simp only [hstep]
      have hmul := hind.integral_mul_eq_mul_integral hI1.aestronglyMeasurable hI2.aestronglyMeasurable
      simp only [Pi.mul_apply] at hmul
      rw [hmul, ih hkx, LocSum.integral_rat_sq h0 h1 p (x - k), pow_succ]

/-- The `ℝ≥0∞`-valued version. -/
theorem lintegral_Pz_sq {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {p : ℝ}
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {k x : ℕ} (hk : k ≤ x) :
    ∫⁻ ω, ENNReal.ofReal ((LocSum.Pz p x k ω) ^ 2) ∂(markMeasure (boolMeasure q))
      = ENNReal.ofReal ((LocSum.bC p q) ^ k) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_Pz_sq h0 h1 hp1 hp2 k x)
    (Filter.Eventually.of_forall fun ω => by positivity)]
  rw [integral_Pz_sq h0 h1 hp1 hp2 x k hk]

end

end LocSumR1
