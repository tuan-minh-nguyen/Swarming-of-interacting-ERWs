/-
  **Exponential spatial moments of the marked-site potential `h_j(x)`.**

  This is the `h`-half of display (expmom) in Proposition "spatial" of
  *Swarming of interacting excited random walks*: there are constants `θ = θ(m,p) > 0` and
  `C = C(m,p) < ∞` with

      sup_{x >= 0}  E exp (θ h_j(x)) ≤ C,

  where the marks `B_j(x)` are i.i.d. Bernoulli`(q)`, `q = (1-p)^{m-1}`, and
  `h_j` is the paper's two-branch recursion with `h_j(-1) = 1`.

  The proof is the paper's: the one-step contraction `one_step_bound` (analytic, in
  `RecursionCore.lean`) is integrated against the independent mark at site `x` via
  `lintegral_bool_step`, giving the recursion `b_{n+1} ≤ γ b_n + C` for
  `b_n = ∫⁻ exp (θ h(n))`, whose fixed point bounds `b_n` uniformly.
-/
import Swarm.Imports
import Swarm.RecursionCore
import Swarm.MarkProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open SwarmMarks

namespace SwarmMarks

noncomputable section

variable {μB : Measure Bool} [IsProbabilityMeasure μB]

/-! ### The process `h` driven by the site marks -/

/-- `h(x)` as a function of the site marks `ω 0, …, ω x`, with `h(-1) = 1`. -/
def hof (p : ℝ) (ω : ℕ → Bool) : ℕ → ℝ
  | 0 => hstep p (ω 0) 1
  | n + 1 => hstep p (ω (n + 1)) (hof p ω n)

@[simp] lemma hof_zero (p : ℝ) (ω : ℕ → Bool) : hof p ω 0 = hstep p (ω 0) 1 := rfl

@[simp] lemma hof_succ (p : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    hof p ω (n + 1) = hstep p (ω (n + 1)) (hof p ω n) := rfl

/-- Measurability of `h(n)` as a function of the mark configuration. -/
lemma measurable_hof {p : ℝ} (hp0 : p ≠ 0) (n : ℕ) :
    Measurable (fun ω : ℕ → Bool => hof p ω n) := by
  induction n with
  | zero =>
      have heq : (fun ω : ℕ → Bool => hof p ω 0) = fun ω => 1 + rhoOf p (ω 0) * (1 + 1) := by
        funext ω
        rw [hof_zero, hstep_eq_rho hp0]
      rw [heq]
      exact Measurable.add measurable_const
        ((measurable_rhoOf p |>.comp (measurable_pi_apply 0)).mul measurable_const)
  | succ k ih =>
      have heq : (fun ω : ℕ → Bool => hof p ω (k + 1))
          = fun ω => 1 + rhoOf p (ω (k + 1)) * (1 + hof p ω k) := by
        funext ω
        rw [hof_succ, hstep_eq_rho hp0]
      rw [heq]
      exact Measurable.add measurable_const
        ((measurable_rhoOf p |>.comp (measurable_pi_apply (k + 1))).mul
          (Measurable.add measurable_const ih))

lemma measurable_exp_hstep (p θ : ℝ) (b : Bool) :
    Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (θ * hstep p b y))) := by
  have h1 : Measurable (fun y : ℝ => θ * hstep p b y) := by
    cases b with
    | false => simp only [hstep_false]; fun_prop
    | true => simp only [hstep_true]; fun_prop
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)

/-! ### Elementary bounds along the path -/

lemma one_le_hof {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (ω : ℕ → Bool) (n : ℕ) :
    1 ≤ hof p ω n := by
  induction n with
  | zero => rw [hof_zero]; exact one_le_hstep hp1 hp2 le_rfl
  | succ k ih => rw [hof_succ]; exact one_le_hstep hp1 hp2 ih

lemma hof_zero_le_three {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (ω : ℕ → Bool) :
    hof p ω 0 ≤ 3 := by
  rw [hof_zero]
  have h3 := hstep_le_add_two (p := p) hp1 hp2 (b := ω 0) (h := 1) le_rfl
  linarith

/-! ### `h(n)` depends only on the marks `0, …, n` -/

lemma hof_congr {p : ℝ} {ω ω' : ℕ → Bool} (n : ℕ) (h : ∀ i, i ≤ n → ω i = ω' i) :
    hof p ω n = hof p ω' n := by
  induction n with
  | zero => rw [hof_zero, hof_zero, h 0 le_rfl]
  | succ k ih =>
      rw [hof_succ, hof_succ, h (k + 1) le_rfl,
        ih fun i hi => h i (le_trans hi (Nat.le_succ k))]

/-- The canonical extension of a finite mark vector to an infinite configuration. -/
def extendVec (n : ℕ) (g : Fin (n + 1) → Bool) : ℕ → Bool :=
  fun i => if h : i < n + 1 then g ⟨i, h⟩ else true

lemma measurable_extendVec (n : ℕ) : Measurable (extendVec n) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i < n + 1
  · have heq : (fun g : Fin (n + 1) → Bool => extendVec n g i) = fun g => g ⟨i, h⟩ := by
      funext g; simp [extendVec, h]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun g : Fin (n + 1) → Bool => extendVec n g i) = fun _ => true := by
      funext g; simp [extendVec, h]
    rw [heq]
    exact measurable_const

/-- `h(n)` as a function of the finite mark vector `(ω 0, …, ω n)`. -/
def Hfun (p : ℝ) (n : ℕ) (g : Fin (n + 1) → Bool) : ℝ := hof p (extendVec n g) n

lemma measurable_Hfun {p : ℝ} (hp0 : p ≠ 0) (n : ℕ) : Measurable (Hfun p n) :=
  (measurable_hof hp0 n).comp (measurable_extendVec n)

lemma hof_eq_Hfun (p : ℝ) (n : ℕ) (ω : ℕ → Bool) :
    hof p ω n = Hfun p n (fun i : Fin (n + 1) => ω i) := by
  refine hof_congr n (fun i hi => ?_)
  simp [extendVec, show i < n + 1 by omega]

/-! ### Independence of the next mark from the past -/

lemma indep_eval_succ (n : ℕ) :
    IndepFun (fun ω : ℕ → Bool => ω (n + 1)) (fun ω => fun i : Fin (n + 1) => ω i)
      (markMeasure μB) := by
  have h0 := (iIndepFun_eval (μB := μB)).indepFun_finset ({n + 1} : Finset ℕ)
    (Finset.range (n + 1)) (by simp) measurable_eval
  have hφ : Measurable (fun g : ({n + 1} : Finset ℕ) → Bool => g ⟨n + 1, by simp⟩) :=
    measurable_pi_apply _
  have hψ : Measurable (fun g : (Finset.range (n + 1)) → Bool =>
      fun i : Fin (n + 1) => g ⟨i.val, Finset.mem_range.mpr i.isLt⟩) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact measurable_pi_apply _
  have h1 := h0.comp hφ hψ
  have e1 : ((fun g : ({n + 1} : Finset ℕ) → Bool => g ⟨n + 1, by simp⟩) ∘
      fun (a : ℕ → Bool) (i : ({n + 1} : Finset ℕ)) => a (i : ℕ))
      = fun ω : ℕ → Bool => ω (n + 1) := by
    funext ω
    simp
  have e2 : ((fun g : (Finset.range (n + 1)) → Bool =>
        fun i : Fin (n + 1) => g ⟨i.val, Finset.mem_range.mpr i.isLt⟩) ∘
      fun (a : ℕ → Bool) (i : (Finset.range (n + 1))) => a (i : ℕ))
      = fun ω : ℕ → Bool => fun i : Fin (n + 1) => ω i := by
    funext ω i
    simp
  rw [e1, e2] at h1
  exact h1

/-- The next mark is independent of the whole past `(h(0), …, h(n))`. -/
lemma indep_hof (p : ℝ) (hp0 : p ≠ 0) (n : ℕ) :
    IndepFun (fun ω : ℕ → Bool => ω (n + 1)) (fun ω => hof p ω n) (markMeasure μB) := by
  have h := (indep_eval_succ (μB := μB) n).comp measurable_id (measurable_Hfun hp0 n)
  have e2 : (Hfun p n ∘ fun ω : ℕ → Bool => fun i : Fin (n + 1) => ω i)
      = fun ω => hof p ω n := by
    funext ω
    exact (hof_eq_Hfun p n ω).symm
  have e1 : (id ∘ fun ω : ℕ → Bool => ω (n + 1)) = fun ω => ω (n + 1) := rfl
  rw [e1, e2] at h
  exact h

/-! ### The exponential moment bound -/

/-- **One step of the moment recursion**: splitting the expectation at the independent mark of
site `n+1` and applying the pointwise one-step contraction. -/
lemma lintegral_exp_hof_succ_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω (n + 1))) ∂(markMeasure (boolMeasure q))
      ≤ ENNReal.ofReal γ
          * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω n)) ∂(markMeasure (boolMeasure q)))
        + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hp0 : p ≠ 0 := by linarith
  set P := markMeasure (boolMeasure q)
  have hind : IndepFun (fun ω : ℕ → Bool => ω (n + 1)) (fun ω => hof p ω n) P :=
    indep_hof p hp0 n
  have hmeasY : Measurable (fun ω : ℕ → Bool => hof p ω n) := measurable_hof hp0 n
  have hkey := lintegral_bool_step (P := P) (B := fun ω : ℕ → Bool => ω (n + 1))
    (Y := fun ω => hof p ω n) (measurable_pi_apply _) hmeasY hind
    (F := fun b y => ENNReal.ofReal (Real.exp (θ * hstep p b y)))
    (fun b => measurable_exp_hstep p θ b)
  -- probabilities of the two values of the next mark
  have htrue : P ((fun ω : ℕ → Bool => ω (n + 1)) ⁻¹' {true}) = ENNReal.ofReal q :=
    markMeasure_true (μB := boolMeasure q) (q := q) (by simp) (n + 1)
  have hfalse : P ((fun ω : ℕ → Bool => ω (n + 1)) ⁻¹' {false}) = ENNReal.ofReal (1 - q) :=
    markMeasure_false (μB := boolMeasure q) (q := q) hq0 hq1 (by simp) (n + 1)
  -- measurability of the two branch integrands
  have hmeasT : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n)))) :=
    (measurable_exp_hstep p θ true).comp hmeasY
  have hmeasF : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n)))) :=
    (measurable_exp_hstep p θ false).comp hmeasY
  have hmeasExp : Measurable (fun ω : ℕ → Bool =>
      ENNReal.ofReal (Real.exp (θ * hof p ω n))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hmeasY))
  have hcT : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))) ∂P)
      * ENNReal.ofReal q
      = ENNReal.ofReal q * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))) ∂P :=
    mul_comm _ _
  have hcF : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))) ∂P)
      * ENNReal.ofReal (1 - q)
      = ENNReal.ofReal (1 - q)
        * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))) ∂P :=
    mul_comm _ _
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω (n + 1))) ∂P
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))) ∂P)
          * P ((fun ω : ℕ → Bool => ω (n + 1)) ⁻¹' {true})
        + (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))) ∂P)
          * P ((fun ω : ℕ → Bool => ω (n + 1)) ⁻¹' {false}) := by
        simpa [hof_succ] using hkey
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))) ∂P)
          * ENNReal.ofReal q
        + (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))) ∂P)
          * ENNReal.ofReal (1 - q) := by
        rw [htrue, hfalse]
    _ = ENNReal.ofReal q
          * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))) ∂P)
        + ENNReal.ofReal (1 - q)
          * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))) ∂P) := by
        rw [hcT, hcF]
    _ = ∫⁻ ω, (ENNReal.ofReal q
            * ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n)))
          + ENNReal.ofReal (1 - q)
            * ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n)))) ∂P := by
        rw [← lintegral_const_mul _ hmeasT, ← lintegral_const_mul _ hmeasF,
          ← lintegral_add_left (f := fun ω : ℕ → Bool =>
              ENNReal.ofReal q * ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n))))
            (g := fun ω : ℕ → Bool =>
              ENNReal.ofReal (1 - q) * ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n))))
            (measurable_const.mul hmeasT)]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (γ * Real.exp (θ * hof p ω n)
          + q * Real.exp (θ / p) * (1 - (1 - p) / p)) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        have hge : 1 ≤ hof p ω n := one_le_hof hp1.le hp2 ω n
        have hb := one_step_bound hp1 hp2 hq0 hθ hγ (hof p ω n) hge
        have h1 : ENNReal.ofReal q * ENNReal.ofReal (Real.exp (θ * hstep p true (hof p ω n)))
            = ENNReal.ofReal (q * Real.exp (θ * hstep p true (hof p ω n))) :=
          (ENNReal.ofReal_mul hq0).symm
        have h2 : ENNReal.ofReal (1 - q)
            * ENNReal.ofReal (Real.exp (θ * hstep p false (hof p ω n)))
            = ENNReal.ofReal ((1 - q) * Real.exp (θ * hstep p false (hof p ω n))) :=
          (ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - q)).symm
        rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        linarith [hb]
    _ = ENNReal.ofReal γ
          * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω n)) ∂P)
        + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
        have hCnn : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
          have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
          have : 0 ≤ 1 - (1 - p) / p := by linarith
          positivity
        have hsplit : (fun ω : ℕ → Bool => ENNReal.ofReal (γ * Real.exp (θ * hof p ω n)
            + q * Real.exp (θ / p) * (1 - (1 - p) / p)))
            = fun ω => ENNReal.ofReal γ * ENNReal.ofReal (Real.exp (θ * hof p ω n))
              + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
          funext ω
          rw [ENNReal.ofReal_add (by positivity) hCnn,
            ENNReal.ofReal_mul (le_of_lt hγpos)]
        rw [hsplit,
          lintegral_add_left (f := fun ω : ℕ → Bool =>
              ENNReal.ofReal γ * ENNReal.ofReal (Real.exp (θ * hof p ω n)))
            (g := fun _ : ℕ → Bool => ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)))
            (measurable_const.mul hmeasExp),
          lintegral_const_mul _ hmeasExp, lintegral_const, measure_univ, mul_one]

/-! ### The uniform exponential moment -/

/-- `(1-p)^{m-1} ≤ 1/2` for `m ≥ 2`, `p > 1/2`: the paper's "`q ≤ 1/2`" arithmetic. -/
lemma pow_one_sub_le_half {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    (1 - p) ^ (m - 1) ≤ 1 / 2 := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hle1 : 1 - p ≤ 1 := by linarith
  have h2 : 1 ≤ m - 1 := by omega
  have hmono := pow_le_pow_of_le_one h0 hle1 h2
  have : (1 - p) ≤ 1 / 2 := by linarith
  linarith [hmono]

/-- **The exponential moment recursion.**  If the one-step contraction holds with rate
`γ < 1` and additive constant `C = q e^{θ/p}(1 - (1-p)/p)`, then
`E exp (θ h(n)) ≤ exp (3θ) + C/(1-γ)` for every `n`. -/
theorem lintegral_exp_hof_le {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hγpos : 0 < γ) (hγ1 : γ < 1)
    (hγ : (1 - q) * Real.exp (2 * θ) + q * ((1 - p) / p) * Real.exp (θ / p) ≤ γ) :
    ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω n)) ∂(markMeasure (boolMeasure q))
        ≤ ENNReal.ofReal (Real.exp (3 * θ)
            + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ)) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hCnn : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) := by
    have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
    have : 0 ≤ 1 - (1 - p) / p := by linarith
    positivity
  have h1γ : 0 < 1 - γ := by linarith
  have hMfixed : γ * (Real.exp (3 * θ)
        + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ))
      + q * Real.exp (θ / p) * (1 - (1 - p) / p)
      ≤ Real.exp (3 * θ) + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := by
    have hkey : γ * (Real.exp (3 * θ)
          + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ))
        + q * Real.exp (θ / p) * (1 - (1 - p) / p)
        = γ * Real.exp (3 * θ)
          + q * Real.exp (θ / p) * (1 - (1 - p) / p) * (γ / (1 - γ) + 1) := by
      field_simp
      ring
    have hfac : γ / (1 - γ) + 1 = 1 / (1 - γ) := by
      field_simp
      ring
    rw [hkey, hfac]
    have h1 : γ * Real.exp (3 * θ) ≤ Real.exp (3 * θ) := by
      nlinarith [Real.exp_pos (3 * θ)]
    have h2 : q * Real.exp (θ / p) * (1 - (1 - p) / p) * (1 / (1 - γ))
        = q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := by
      field_simp
    linarith [h1, h2]
  intro n
  induction n with
  | zero =>
      have hbase : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω 0))
          ∂(markMeasure (boolMeasure q)) ≤ ENNReal.ofReal (Real.exp (3 * θ)) := by
        calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω 0)) ∂(markMeasure (boolMeasure q))
            ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (3 * θ)) ∂(markMeasure (boolMeasure q)) := by
              apply lintegral_mono
              intro ω
              dsimp only
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.mpr
              have h3 := hof_zero_le_three hp1.le hp2 ω
              have h4 : θ * hof p ω 0 ≤ θ * 3 := mul_le_mul_of_nonneg_left h3 hθ.le
              linarith
          _ = ENNReal.ofReal (Real.exp (3 * θ)) := by
              rw [lintegral_const, measure_univ, mul_one]
      refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ) := div_nonneg hCnn h1γ.le
      linarith
  | succ k ih =>
      have hstep := lintegral_exp_hof_succ_le hp1 hp2 hq0 hq1 hθ hγpos hγ k
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω (k + 1)))
              ∂(markMeasure (boolMeasure q))
          ≤ ENNReal.ofReal γ
              * (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω k))
                  ∂(markMeasure (boolMeasure q)))
            + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := hstep
        _ ≤ ENNReal.ofReal γ
              * ENNReal.ofReal (Real.exp (3 * θ)
                + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ))
            + ENNReal.ofReal (q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
            gcongr
        _ = ENNReal.ofReal (γ * (Real.exp (3 * θ)
                + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ))
              + q * Real.exp (θ / p) * (1 - (1 - p) / p)) := by
            rw [← ENNReal.ofReal_mul (le_of_lt hγpos),
              ← ENNReal.ofReal_add (by positivity) hCnn]
        _ ≤ ENNReal.ofReal (Real.exp (3 * θ)
              + q * Real.exp (θ / p) * (1 - (1 - p) / p) / (1 - γ)) :=
            ENNReal.ofReal_le_ofReal hMfixed

/-- **Display (expmom), `h`-half.**  For every `m ≥ 2` and `p ∈ (1/2,1)` there are constants
`θ = θ(m,p) > 0` and `C = C(m,p) < ∞` such that, for every site `x`,
`E exp (θ h(x)) ≤ C`, where `h(·)` is the paper's potential driven by i.i.d. Bernoulli marks
with success probability `q = (1-p)^{m-1}`. -/
theorem exists_exp_moment_hof {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
        ∂(markMeasure (boolMeasure ((1 - p) ^ (m - 1)))) ≤ ENNReal.ofReal C := by
  have hq0 : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have := pow_one_sub_le_half hp1 hp2 hm
    linarith
  obtain ⟨θ, hθpos, hθc⟩ := exists_theta hp1 hp2 hq0 (by linarith)
  refine ⟨θ, hθpos, Real.exp (3 * θ)
      + (1 - p) ^ (m - 1) * Real.exp (θ / p) * (1 - (1 - p) / p)
        / (1 - ((1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
          + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p))), ?_, ?_⟩
  · have hCnn : 0 ≤ (1 - p) ^ (m - 1) * Real.exp (θ / p) * (1 - (1 - p) / p) := by
      have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
      have : 0 ≤ 1 - (1 - p) / p := by linarith
      positivity
    have hden : 0 < 1 - ((1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
        + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p)) := by linarith
    have := Real.exp_pos (3 * θ)
    positivity
  · intro x
    have hγpos : 0 < (1 - (1 - p) ^ (m - 1)) * Real.exp (2 * θ)
        + (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by
      have := rho_nonneg hp1 hp2
      have hqnn : (0:ℝ) ≤ (1 - p) ^ (m - 1) := hq0.le
      have hexp : 0 < Real.exp (2 * θ) := Real.exp_pos _
      have hqlt : (1 - p) ^ (m - 1) < 1 := by
        have h0 : (0:ℝ) ≤ 1 - p := by linarith
        have hlt : 1 - p < 1 := by linarith
        exact pow_lt_one₀ h0 hlt (by omega)
      have h1 : 0 < 1 - (1 - p) ^ (m - 1) := by linarith
      have h2 : 0 ≤ (1 - p) ^ (m - 1) * ((1 - p) / p) * Real.exp (θ / p) := by positivity
      nlinarith
    exact lintegral_exp_hof_le hp1 hp2 hq0.le hq1 hθpos hγpos hθc le_rfl x

end

end SwarmMarks
