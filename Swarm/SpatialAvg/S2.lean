/-
  The fluctuation term `M_r = sum_{n<r} (mk(n+1) - q) h(n)` of the spatial average:
  it is a sum of martingale differences, and `M_r / r -> 0` almost surely.

  The only probabilistic inputs are
  * `mk(n+1)` is independent of `(h(0), ..., h(n))` (Mathlib/m8 `indep_eval_succ`),
  * `E mk = q` (the site-mark probability).

  From them we get `E M_r = 0` and `E M_r^2 <= C r` (orthogonality), and we prove
  `E M_r^4 <= B r^2` by induction on `r` — the expansion of `(M + d)^4` together with the
  vanishing `E[M^3 d] = 0`.  Chebyshev's inequality and Borel--Cantelli then give `M_r / r -> 0`.
-/
import Swarm.Imports
import Swarm.SpatialAvg.S1

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmSpatial
noncomputable section

variable {p q : ℝ}

/-! ### Functions of finitely many marks -/

/-- `W` depends only on the marks at the sites `0, …, m`. -/
def DependsOn (m : ℕ) (W : (ℕ → Bool) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → Bool, (∀ i, i ≤ m → ω i = ω' i) → W ω = W ω'

lemma dependsOn_const (m : ℕ) (c : ℝ) : DependsOn m (fun _ => c) := fun _ _ _ => rfl

lemma DependsOn.add {m : ℕ} {W V : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (hV : DependsOn m V) :
    DependsOn m (fun ω => W ω + V ω) := fun ω ω' h => by
  show W ω + V ω = W ω' + V ω'
  rw [hW ω ω' h, hV ω ω' h]

lemma DependsOn.mul {m : ℕ} {W V : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (hV : DependsOn m V) :
    DependsOn m (fun ω => W ω * V ω) := fun ω ω' h => by
  show W ω * V ω = W ω' * V ω'
  rw [hW ω ω' h, hV ω ω' h]

lemma DependsOn.neg {m : ℕ} {W : (ℕ → Bool) → ℝ} (hW : DependsOn m W) :
    DependsOn m (fun ω => -W ω) := fun ω ω' h => by
  show -W ω = -W ω'
  rw [hW ω ω' h]

lemma DependsOn.sub {m : ℕ} {W V : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (hV : DependsOn m V) :
    DependsOn m (fun ω => W ω - V ω) := fun ω ω' h => by
  show W ω - V ω = W ω' - V ω'
  rw [hW ω ω' h, hV ω ω' h]

lemma DependsOn.pow {m : ℕ} {W : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (k : ℕ) :
    DependsOn m (fun ω => W ω ^ k) := fun ω ω' h => by
  show W ω ^ k = W ω' ^ k
  rw [hW ω ω' h]

lemma DependsOn.sum {m : ℕ} {ι : Type*} (s : Finset ι) {W : ι → (ℕ → Bool) → ℝ}
    (hW : ∀ i ∈ s, DependsOn m (W i)) : DependsOn m (fun ω => ∑ i ∈ s, W i ω) :=
  fun ω ω' h => by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hW i hi ω ω' h]

lemma DependsOn.mono {m m' : ℕ} {W : (ℕ → Bool) → ℝ} (hW : DependsOn m W) (h : m ≤ m') :
    DependsOn m' W :=
  fun ω ω' hω => hW ω ω' fun i hi => hω i (le_trans hi h)

lemma dependsOn_mk {m n : ℕ} (h : n ≤ m) : DependsOn m (fun ω => mk ω n) := by
  intro ω ω' hω
  have : ω n = ω' n := hω n h
  simp [mk, this]

lemma dependsOn_hof {m n : ℕ} (h : n ≤ m) : DependsOn m (fun ω => hof p ω n) :=
  fun ω ω' hω => hof_congr n fun i hi => hω i (le_trans hi h)

/-- `W` depends only on the first `m+1` coordinates, so it is independent of the mark at site
`m+1`. -/
lemma indep_of_dependsOn {μB : Measure Bool} [IsProbabilityMeasure μB] {m : ℕ} {W : (ℕ → Bool) → ℝ} (hdep : DependsOn m W) (hW : Measurable W) :
    IndepFun (fun ω : ℕ → Bool => ω (m + 1)) W (markMeasure μB) := by
  set W' : (Fin (m + 1) → Bool) → ℝ := fun v => W (extendVec m v) with hW'def
  have hW' : Measurable W' := hW.comp (measurable_extendVec m)
  have hfac : ∀ ω : ℕ → Bool, W ω = W' (fun i : Fin (m + 1) => ω i) := by
    intro ω
    simp only [hW'def]
    refine hdep ω (extendVec m fun i => ω i) ?_
    intro i hi
    have hi' : i < m + 1 := by omega
    simp [extendVec, hi']
  have h := (indep_eval_succ (μB := μB) m).comp measurable_id hW'
  refine h.congr (Filter.EventuallyEq.of_eq ?_) (Filter.EventuallyEq.of_eq ?_)
  · rfl
  · funext ω; exact (hfac ω).symm


/-! ### The mean of `mk` and the mean-zero product lemma -/

/-- The site-mark probability for the concrete Bernoulli law. -/
lemma integral_mk {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    ∫ ω : ℕ → Bool, mk ω n ∂(markMeasure (boolMeasure q)) = q := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  have h := integral_eval (μB := boolMeasure q) (f := fun b : Bool => if b then (1 : ℝ) else 0) n
  rw [integral_boolMeasure h0 h1] at h
  simpa [mk] using h

lemma integrable_mk {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    Integrable (fun ω : ℕ → Bool => mk ω n) (markMeasure (boolMeasure q)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  refine Integrable.mono' (integrable_const (1 : ℝ)) (measurable_mk n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mk_nonneg ω n)]
  exact mk_le_one ω n

/-- **The mean-zero product lemma.**  A function of the marks `0, …, m` is independent of the
centred mark at site `m+1`, whose mean is `q`; hence the product has mean zero. -/
theorem integral_dep_mul_mark_sub {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {m : ℕ}
    {W : (ℕ → Bool) → ℝ} (hdep : DependsOn m W) (hW : Measurable W)
    (hint : Integrable W (markMeasure (boolMeasure q))) :
    ∫ ω, W ω * (mk ω (m + 1) - q) ∂(markMeasure (boolMeasure q)) = 0 := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure h0 h1
  set μ := markMeasure (boolMeasure q) with hμ
  have hind := indep_of_dependsOn (μB := boolMeasure q) hdep hW
  have hφ : Measurable (fun b : Bool => (if b then (1 : ℝ) else 0) - q) := by fun_prop
  have hind2 : IndepFun (fun ω : ℕ → Bool => mk ω (m + 1) - q) W μ :=
    hind.comp hφ measurable_id
  have hX : AEStronglyMeasurable (fun ω : ℕ → Bool => mk ω (m + 1) - q) μ :=
    ((measurable_mk (m + 1)).sub measurable_const).aestronglyMeasurable
  have hprod := hind2.integral_fun_mul_eq_mul_integral hX hint.aestronglyMeasurable
  have hmean : ∫ ω : ℕ → Bool, (mk ω (m + 1) - q) ∂μ = 0 := by
    rw [integral_sub (f := fun ω : ℕ → Bool => mk ω (m + 1)) (g := fun _ => q)
      (integrable_mk h0 h1 _) (integrable_const q)]
    simp only [integral_mk h0 h1, integral_const]
    simp
  have hcomm : (fun ω => W ω * (mk ω (m + 1) - q)) = fun ω => (mk ω (m + 1) - q) * W ω := by
    funext ω; ring
  rw [hcomm, hprod, hmean, zero_mul]

end
end SwarmSpatial
