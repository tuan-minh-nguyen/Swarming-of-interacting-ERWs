/-
  **Exponential spatial moments of the forward potential `G_j(x)`** — the second half of display
  `(expmom)` in Proposition "spatial".

  With the site ratios `rho(x) = (1 - omega(x))/omega(x) in {1, (1-p)/p}` (i.i.d.), the paper sets

      G_j(x) = 1 + sum_{l>=1} prod_{u=1}^{l} rho_j(x+u),

  a *forward* recursion.  We truncate it from the far end,

      G_N(x) = 1 + sum_{l=1}^{N} prod_{u=1}^{l} rho(x+u),

  which satisfies the recursion `G_{N+1}(x) = 1 + rho(x+1) G_N(x+1)`; the sequence `G_N(x)` is
  increasing in `N` and increases to the paper's `G(x)`.  Each step peels off a *new* mark at a
  site that is independent of all the marks used so far, which is the mirror image of the
  argument for `h` (`MarkMoments.lean`): the same contraction rate `γ` and the same additive
  constant work, because `1 + y <= y + 2` and `1 + rho y <= 1/p + rho y`.

  The main output is

      ∫⁻ (⨆_N exp (θ G_N(x+1))) dP ≤ M = e^{3θ} + q e^{θ/p}(1 - ρ)/(1-γ),

  that is, `E exp (θ G(x)) ≤ M` for every site `x`, together with the a.s. finiteness of the
  supremum (equivalently, a.s. summability of the defining series).
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess
import Swarm.MarkMoments
import Swarm.MarkTails

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

/-! ### Independence of the mark at a site from all the sites to its right -/

lemma indep_mark_head_future (a N : ℕ) :
    IndepFun (fun ω : ℕ → Bool => ω a) (fun ω => fun i : Fin N => ω (a + 1 + i))
      (markMeasure μB) := by
  classical
  set T : Finset ℕ := (Finset.range N).image (fun i => a + 1 + i) with hT
  have hdisj : Disjoint ({a} : Finset ℕ) T := by
    rw [hT]
    simp only [Finset.disjoint_singleton_left, Finset.mem_image, Finset.mem_range,
      not_exists, not_and]
    intro i _ h
    omega
  have h0 := (iIndepFun_eval (μB := μB)).indepFun_finset ({a} : Finset ℕ) T hdisj measurable_eval
  have hφ : Measurable (fun g : ({a} : Finset ℕ) → Bool => g ⟨a, by simp⟩) := measurable_pi_apply _
  have hψ : Measurable (fun g : T → Bool => fun i : Fin N => g ⟨a + 1 + i, by
      rw [hT]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, rfl⟩⟩) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_apply _
  have h1 := h0.comp hφ hψ
  have e1 : ((fun g : ({a} : Finset ℕ) → Bool => g ⟨a, by simp⟩) ∘
      fun (b : ℕ → Bool) (i : ({a} : Finset ℕ)) => b (i : ℕ)) = fun ω => ω a := by
    funext ω
    simp
  have e2 : ((fun g : T → Bool => fun i : Fin N => g ⟨a + 1 + i, by
        rw [hT]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, rfl⟩⟩) ∘
      fun (b : ℕ → Bool) (i : T) => b (i : ℕ)) = fun ω => fun i : Fin N => ω (a + 1 + i) := by
    funext ω i
    simp
  rw [e1, e2] at h1
  exact h1

/-! ### The truncated forward potential -/

/-- `G_N` as a function of the mark vector `g 0, …, g (N-1)`. -/
def Gv (p : ℝ) : (N : ℕ) → (Fin N → Bool) → ℝ
  | 0, _ => 1
  | N + 1, g => 1 + rhoOf p (g 0) * Gv p N fun i => g i.succ

@[simp] lemma Gv_zero (p : ℝ) (g : Fin 0 → Bool) : Gv p 0 g = 1 := rfl

lemma Gv_succ (p : ℝ) (N : ℕ) (g : Fin (N + 1) → Bool) :
    Gv p (N + 1) g = 1 + rhoOf p (g 0) * Gv p N (fun i => g i.succ) := rfl

/-- The truncated forward potential `G_N(x) = 1 + sum_{l=1}^{N} prod_{u=1}^{l} rho(x+u)`. -/
def Gtrunc (p : ℝ) (ω : ℕ → Bool) (N x : ℕ) : ℝ := Gv p N fun i => ω (x + i)

/-- The recursion `G_{N+1}(x) = 1 + rho(x) G_N(x+1)`. -/
lemma rhoOf_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (b : Bool) :
    0 ≤ rhoOf p b := by
  cases b with
  | false => simp [rhoOf_false]
  | true => simp only [rhoOf_true]; positivity

lemma Gtrunc_succ (p : ℝ) (ω : ℕ → Bool) (N x : ℕ) :
    Gtrunc p ω (N + 1) x = 1 + rhoOf p (ω x) * Gtrunc p ω N (x + 1) := by
  simp only [Gtrunc, Gv_succ]
  have harg : (fun i : Fin N => ω (x + (i.succ : Fin (N + 1)).val))
      = fun i : Fin N => ω (x + 1 + (i : ℕ)) := by
    funext i
    simp only [Fin.val_succ]
    congr 1
    omega
  rw [harg]
  simp

lemma measurable_Gv (p : ℝ) (N : ℕ) : Measurable (Gv p N) := by
  induction N with
  | zero => exact measurable_const
  | succ n ih =>
      have heq : (Gv p (n + 1))
          = fun g : Fin (n + 1) → Bool => 1 + rhoOf p (g 0) * Gv p n (fun i => g i.succ) := by
        funext g
        rw [Gv_succ]
      rw [heq]
      refine Measurable.add measurable_const ?_
      refine Measurable.mul ?_ ?_
      · exact (measurable_rhoOf p).comp (measurable_pi_apply 0)
      · exact ih.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ)

lemma measurable_Gtrunc (p : ℝ) (N x : ℕ) :
    Measurable (fun ω : ℕ → Bool => Gtrunc p ω N x) :=
  (measurable_Gv p N).comp (measurable_pi_iff.mpr fun i => measurable_pi_apply (x + i))

lemma one_le_Gtrunc {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) (N x : ℕ) :
    1 ≤ Gtrunc p ω N x := by
  induction N generalizing x with
  | zero => simp [Gtrunc]
  | succ n ih =>
      rw [Gtrunc_succ]
      have hr : 0 ≤ rhoOf p (ω x) := rhoOf_nonneg hp1 hp2 _
      have := ih (x + 1)
      nlinarith

lemma Gtrunc_mono {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool) :
    ∀ (N x : ℕ), Gtrunc p ω N x ≤ Gtrunc p ω (N + 1) x := by
  intro N
  induction N with
  | zero =>
      intro x
      rw [Gtrunc_succ]
      have hr : 0 ≤ rhoOf p (ω x) := rhoOf_nonneg hp1 hp2 _
      simp only [Gtrunc, Gv_zero]
      nlinarith
  | succ n ih =>
      intro x
      rw [Gtrunc_succ, Gtrunc_succ]
      have hr : 0 ≤ rhoOf p (ω x) := rhoOf_nonneg hp1 hp2 _
      have := ih (x + 1)
      nlinarith

lemma momConst_nonneg {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq0 : 0 ≤ q)
    (hγ1 : γ < 1) : 0 ≤ momConst p q θ γ := by
  unfold momConst
  have h2 : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
    have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
    have : 0 ≤ 1 - (1 - p) / p := by linarith
    positivity
  have h3 : 0 < 1 - γ := by linarith
  have h4 : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := div_nonneg h2 h3.le
  have h5 : 0 ≤ Real.exp (3 * θ) := (Real.exp_pos _).le
  linarith

/-! ### The one-step contraction for the forward recursion -/

/-- The one-step bound for `G`: for `y >= 1`, the branch average of `exp (θ G_{n+1})` contracts
at the same rate `γ` and with the same additive constant as for `h`. -/
lemma G_one_step {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hθ : 0 < θ)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    {y : ℝ} (hy : 1 ≤ y) :
    (1 - q) * Real.exp (θ * (1 + rhoOf p false * y))
        + q * Real.exp (θ * (1 + rhoOf p true * y))
      ≤ γ * Real.exp (θ * y) + q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
  have hbase := one_step_bound hp1 hp2 hq0 hθ hγ y hy
  have hr : 0 ≤ (1 - p) / p := rho_nonneg hp1 hp2
  have hp1' : 1 ≤ 1 / p := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have e1 : Real.exp (θ * (1 + rhoOf p false * y)) ≤ Real.exp (θ * hstep p false y) := by
    apply Real.exp_le_exp.mpr
    simp only [rhoOf_false, hstep_false]
    nlinarith
  have e2 : Real.exp (θ * (1 + rhoOf p true * y)) ≤ Real.exp (θ * hstep p true y) := by
    apply Real.exp_le_exp.mpr
    simp only [rhoOf_true, hstep_true]
    nlinarith
  have h1 : (1 - q) * Real.exp (θ * (1 + rhoOf p false * y))
      ≤ (1 - q) * Real.exp (θ * hstep p false y) :=
    mul_le_mul_of_nonneg_left e1 (by linarith)
  have h2 : q * Real.exp (θ * (1 + rhoOf p true * y))
      ≤ q * Real.exp (θ * hstep p true y) := mul_le_mul_of_nonneg_left e2 hq0
  linarith

/-- **The moment recursion for the truncated forward potential.** -/
theorem lintegral_exp_Gtrunc_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (N x : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N x))
        ∂(markMeasure (boolMeasure q)) ≤ ENNReal.ofReal (momConst p q θ γ) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  induction N generalizing x with
  | zero =>
      have hone : ∀ ω : ℕ → Bool, Gtrunc p ω 0 x = 1 := fun ω => rfl
      simp only [hone, mul_one]
      have hconst : ∫⁻ _ω, ENNReal.ofReal (Real.exp θ) ∂(markMeasure (boolMeasure q))
          = ENNReal.ofReal (Real.exp θ) := by
        rw [lintegral_const, measure_univ, mul_one]
      rw [hconst]
      unfold momConst
      refine ENNReal.ofReal_le_ofReal ?_
      have hC : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
        have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
        have : 0 ≤ 1 - (1 - p) / p := by linarith
        positivity
      have h1γ : 0 < 1 - γ := by linarith
      have := div_nonneg hC h1γ.le
      have h3 : Real.exp θ ≤ Real.exp (3 * θ) := by
        apply Real.exp_le_exp.mpr; linarith
      linarith
  | succ n ih =>
      -- split at the mark of site x+1
      have hmeasY : Measurable (fun ω : ℕ → Bool => Gtrunc p ω n (x + 1)) :=
        measurable_Gtrunc p n (x + 1)
      have hind : IndepFun (fun ω : ℕ → Bool => ω x)
          (fun ω => Gtrunc p ω n (x + 1)) (markMeasure (boolMeasure q)) := by
        have h := (indep_mark_head_future (μB := boolMeasure q) x n).comp
          measurable_id (measurable_Gv p n)
        have e2 : ((Gv p n) ∘ fun ω : ℕ → Bool => fun i : Fin n => ω (x + 1 + i))
            = fun ω => Gtrunc p ω n (x + 1) := by
          funext ω
          simp only [Function.comp, Gtrunc]
        have e1 : (id ∘ fun ω : ℕ → Bool => ω x) = fun ω => ω x := rfl
        rw [e1, e2] at h
        exact h
      have hkey := lintegral_bool_step (P := markMeasure (boolMeasure q))
        (B := fun ω : ℕ → Bool => ω x) (Y := fun ω => Gtrunc p ω n (x + 1))
        (measurable_pi_apply _) hmeasY hind
        (F := fun b y => ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p b * y))))
        (fun b => by
          have : (fun y : ℝ => ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p b * y))))
              = fun y => if b then ENNReal.ofReal (Real.exp (θ * (1 + (1 - p) / p * y)))
                else ENNReal.ofReal (Real.exp (θ * (1 + y))) := by
            cases b <;> simp [rhoOf_true, rhoOf_false]
          rw [this]
          cases b
          · simp only [Bool.false_eq_true, if_false, reduceIte]
            exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
          · simp only [if_true]
            exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop)))
      have htrue : markMeasure (boolMeasure q) ((fun ω : ℕ → Bool => ω x) ⁻¹' {true})
          = ENNReal.ofReal q :=
        markMeasure_true (μB := boolMeasure q) (q := q) (by simp) x
      have hfalse : markMeasure (boolMeasure q) ((fun ω : ℕ → Bool => ω x) ⁻¹' {false})
          = ENNReal.ofReal (1 - q) :=
        markMeasure_false (μB := boolMeasure q) (q := q) hq0 hq1 (by simp) x
      have hchain1 : Measurable (fun ω : ℕ → Bool =>
          1 + rhoOf p true * Gtrunc p ω n (x + 1)) :=
        Measurable.add measurable_const (measurable_const.mul hmeasY)
      have hmeasT : Measurable (fun ω : ℕ → Bool =>
          ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul hchain1))
      have hchain0 : Measurable (fun ω : ℕ → Bool =>
          1 + rhoOf p false * Gtrunc p ω n (x + 1)) :=
        Measurable.add measurable_const (measurable_const.mul hmeasY)
      have hmeasF : Measurable (fun ω : ℕ → Bool =>
          ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul hchain0))
      have hmeasExp : Measurable (fun ω : ℕ → Bool =>
          ENNReal.ofReal (Real.exp (θ * Gtrunc p ω n (x + 1)))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul hmeasY))
      have hCnn : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
        have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
        have : 0 ≤ 1 - (1 - p) / p := by linarith
        positivity
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω (n + 1) x))
              ∂(markMeasure (boolMeasure q))
          = (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) *
              markMeasure (boolMeasure q) ((fun ω : ℕ → Bool => ω x) ⁻¹' {true})
            + (∫⁻ ω, ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) *
              markMeasure (boolMeasure q) ((fun ω : ℕ → Bool => ω x) ⁻¹' {false}) := by
            have hhof : ∀ ω : ℕ → Bool,
                Gtrunc p ω (n + 1) x = 1 + rhoOf p (ω x) * Gtrunc p ω n (x + 1) := by
              intro ω
              rw [Gtrunc_succ]
            simp only [hhof]
            exact hkey
        _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) * ENNReal.ofReal q
            + (∫⁻ ω, ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) * ENNReal.ofReal (1 - q) := by
            rw [htrue, hfalse]
        _ = ENNReal.ofReal q
              * (∫⁻ ω, ENNReal.ofReal
                  (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
                  ∂(markMeasure (boolMeasure q)))
            + ENNReal.ofReal (1 - q)
              * (∫⁻ ω, ENNReal.ofReal
                  (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))
                  ∂(markMeasure (boolMeasure q))) := by
            rw [mul_comm (∫⁻ ω, ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) (ENNReal.ofReal q),
              mul_comm (∫⁻ ω, ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))
                ∂(markMeasure (boolMeasure q))) (ENNReal.ofReal (1 - q))]
        _ = ∫⁻ ω, (ENNReal.ofReal q * ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
              + ENNReal.ofReal (1 - q) * ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1)))))
              ∂(markMeasure (boolMeasure q)) := by
            rw [← lintegral_const_mul _ hmeasT, ← lintegral_const_mul _ hmeasF,
              ← lintegral_add_left (f := fun ω : ℕ → Bool =>
                  ENNReal.ofReal q * ENNReal.ofReal
                    (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1)))))
                (g := fun ω : ℕ → Bool =>
                  ENNReal.ofReal (1 - q) * ENNReal.ofReal
                    (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1)))))
                (measurable_const.mul hmeasT)]
        _ ≤ ∫⁻ ω, ENNReal.ofReal (γ * Real.exp (θ * Gtrunc p ω n (x + 1))
              + q * Real.exp (θ / p) * (1 - (1 - p) / p))
              ∂(markMeasure (boolMeasure q)) := by
            apply lintegral_mono
            intro ω
            dsimp only
            have hy : 1 ≤ Gtrunc p ω n (x + 1) := one_le_Gtrunc hp1 hp2 ω n (x + 1)
            have hb := G_one_step hp1 hp2 hq0 hq1 hθ hγ hy
            have h1 : ENNReal.ofReal q * ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1))))
                = ENNReal.ofReal (q * Real.exp
                    (θ * (1 + rhoOf p true * Gtrunc p ω n (x + 1)))) :=
              (ENNReal.ofReal_mul hq0).symm
            have h2 : ENNReal.ofReal (1 - q) * ENNReal.ofReal
                (Real.exp (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1))))
                = ENNReal.ofReal ((1 - q) * Real.exp
                    (θ * (1 + rhoOf p false * Gtrunc p ω n (x + 1)))) :=
              (ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - q)).symm
            rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            linarith [hb]
        _ = ENNReal.ofReal γ
              * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω n (x + 1)))
                  ∂(markMeasure (boolMeasure q)))
            + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
            have hsplit : (fun ω : ℕ → Bool => ENNReal.ofReal (γ * Real.exp (θ * Gtrunc p ω n (x + 1))
                + q * Real.exp (θ / p) * (1 - (1 - p) / p)))
                = fun ω => ENNReal.ofReal γ * ENNReal.ofReal (Real.exp (θ * Gtrunc p ω n (x + 1)))
                  + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
              funext ω
              rw [ENNReal.ofReal_add (by positivity) hCnn,
                ENNReal.ofReal_mul (le_of_lt hγpos)]
            rw [hsplit,
              lintegral_add_left (f := fun ω : ℕ → Bool =>
                  ENNReal.ofReal γ * ENNReal.ofReal (Real.exp (θ * Gtrunc p ω n (x + 1))))
                (g := fun _ : ℕ → Bool =>
                  ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)))
                (measurable_const.mul hmeasExp),
              lintegral_const_mul _ hmeasExp, lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal γ * ENNReal.ofReal (momConst p q θ γ)
              + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
            have hih := ih (x + 1)
            have h1 : ENNReal.ofReal γ * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω n (x + 1)))
                ∂(markMeasure (boolMeasure q)))
                ≤ ENNReal.ofReal γ * ENNReal.ofReal (momConst p q θ γ) :=
              mul_le_mul_of_nonneg_left hih (by simp)
            exact add_le_add h1 le_rfl
        _ ≤ ENNReal.ofReal (momConst p q θ γ) := by
            have hfix : γ * momConst p q θ γ
                + q * Real.exp (θ / p) * (1 - (1 - p) / p) ≤ momConst p q θ γ := by
              unfold momConst
              have h1γ : 0 < 1 - γ := by linarith
              have hCnn' : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := hCnn
              have hkey : γ * (Real.exp (3 * θ)
                    + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ))
                  + q * Real.exp (θ / p) * (1 - (1 - p) / p)
                  = γ * Real.exp (3 * θ)
                    + q * Real.exp (θ / p) * (1 - (1 - p) / p) * (1 / (1 - γ)) := by
                field_simp
                ring
              rw [hkey]
              have hfac : q * Real.exp (θ / p) * (1 - (1 - p) / p) * (1 / (1 - γ))
                  = q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := by
                rw [mul_one_div]
              rw [hfac]
              have h3 : γ * Real.exp (3 * θ) ≤ Real.exp (3 * θ) := by
                nlinarith [Real.exp_pos (3 * θ)]
              linarith
            rw [← ENNReal.ofReal_mul hγpos.le,
              ← ENNReal.ofReal_add (mul_nonneg hγpos.le (momConst_nonneg hp1 hp2 hq0 hγ1)) hCnn]
            exact ENNReal.ofReal_le_ofReal hfix

/-- **The exponential moment of the forward potential** (second half of (expmom)): for every
site `x`, the supremum of `exp (θ G_N(x+1))` over the truncation level has `lintegral` at most
`M = e^{3θ} + q e^{θ/p}(1-ρ)/(1-γ)`; equivalently `E exp (θ G(x)) ≤ M` whenever the defining
series of `G(x)` converges, and it converges almost surely. -/
theorem lintegral_exp_Gsup_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ)
    (x : ℕ) :
    ∫⁻ ω, (⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1))))
        ∂(markMeasure (boolMeasure q)) ≤ ENNReal.ofReal (momConst p q θ γ) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hmeas : ∀ N, Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) := fun N =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_Gtrunc p N (x + 1))))
  have hmono : Monotone (fun N => fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) := by
    intro N N' hNN' ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmono2 : Gtrunc p ω N (x + 1) ≤ Gtrunc p ω N' (x + 1) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNN'
      clear hNN'
      induction d with
      | zero => simp
      | succ k ih =>
          rw [show N + (k + 1) = (N + k) + 1 by ring]
          exact ih.trans (Gtrunc_mono hp1 hp2 ω (N + k) (x + 1))
    exact mul_le_mul_of_nonneg_left hmono2 hθ.le
  rw [lintegral_iSup hmeas hmono]
  exact iSup_le fun N => lintegral_exp_Gtrunc_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ N (x + 1)

/-- **Almost-sure finiteness of the forward potential.**  Almost surely,
`G(x) = 1 + sum_{l>=1} prod_{u=1}^{l} rho(x+u) < ∞` for every site `x`, and
`E exp (θ G(x)) ≤ M`. -/
theorem Gsup_ne_top_ae {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) :
    ∀ᵐ ω ∂(markMeasure (boolMeasure q)), ∀ x : ℕ,
      (⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) ≠ ⊤ := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hsum : ∀ x : ℕ, ∀ᵐ ω ∂(markMeasure (boolMeasure q)),
      (⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) ≠ ⊤ := by
    intro x
    have hfin := lintegral_exp_Gsup_le hp1 hp2 hq0 hq1 hθ hγpos hγ1 hγ x
    have hne : (∫⁻ ω, (⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1))))
        ∂(markMeasure (boolMeasure q))) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    have hmeasm : Measurable (fun ω : ℕ → Bool =>
        ⨆ N, ENNReal.ofReal (Real.exp (θ * Gtrunc p ω N (x + 1)))) :=
      Measurable.iSup fun N => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (measurable_Gtrunc p N (x + 1))))
    filter_upwards [MeasureTheory.ae_lt_top hmeasm hne] with ω hω using hω.ne
  filter_upwards [ae_all_iff.2 hsum] with ω hω x
  exact hω x

end

end SwarmMarks
