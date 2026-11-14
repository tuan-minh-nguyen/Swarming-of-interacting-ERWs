/-
  Analytic core of the exponential-moment estimate for the marked-site potential `h^omega`
  (Proposition "spatial", display (expmom), of *Swarming of interacting excited random walks*).

  The paper's `h_j(x)` is the unique solution of

      h_j(x) = (1 + (1 - omega_j(x)) h_j(x-1)) / omega_j(x),   h_j(-1) = 1,

  where `omega_j(x) = 1/2 + (p - 1/2) B_j(x)` is `p` at a marked site (`B_j(x) = 1`) and `1/2`
  elsewhere; hence the two-branch recursion

      h_j(x) = h_j(x-1) + 2                         (unmarked,  B_j(x) = 0),
      h_j(x) = 1/p + ((1-p)/p) h_j(x-1)             (marked,    B_j(x) = 1).

  This file contains no probability.  It proves:

  * the two-branch recursion, the bounds `1 <= h <= h_prev + 2`, and `h <= 3` at the first site;
  * the one-step exponential contraction
      (1-q) e^{theta h(x-1)+2} + q e^{theta (1/p + rho h(x-1))}
          <= gamma e^{theta h(x-1)} + q e^{theta/p} (1 - rho)
    for every `h(x-1) >= 1`, where `gamma = (1-q) e^{2 theta} + q rho e^{theta/p}`;
  * the existence of `theta > 0` with `gamma < 1` for every `q in (0,1]`.

  The exponential moment itself (integrating this inequality over i.i.d. marks) is in
  `MarkMoments.lean`.
-/
import Swarm.Imports

namespace SwarmMarks

noncomputable section

open Real

/-- The one-step (two-branch) recursion of the marked-site potential.  `hstep p false h = h + 2`
at an unmarked site and `hstep p true h = 1/p + ((1-p)/p) h` at a marked site. -/
def hstep (p : ℝ) (b : Bool) (h : ℝ) : ℝ :=
  if b then 1 / p + ((1 - p) / p) * h else h + 2

@[simp] lemma hstep_false (p h : ℝ) : hstep p false h = h + 2 := rfl

@[simp] lemma hstep_true (p h : ℝ) : hstep p true h = 1 / p + ((1 - p) / p) * h := rfl

/-- `h` at site `n-1` for the mark vector `v : Fin n → Bool`, with the boundary value
`h(-1) = 1`.  Thus `h_j(x) = hfin p (x+1) (fun i => B_j i)`. -/
def hfin (p : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 1
  | (n + 1), v => hstep p (v ⟨n, Nat.lt_succ_self n⟩) (hfin p n fun i => v i.castSucc)

@[simp] lemma hfin_zero (p : ℝ) (v : Fin 0 → Bool) : hfin p 0 v = 1 := rfl

lemma hfin_succ (p : ℝ) (n : ℕ) (v : Fin (n + 1) → Bool) :
    hfin p (n + 1) v = hstep p (v ⟨n, Nat.lt_succ_self n⟩) (hfin p n fun i => v i.castSucc) :=
  rfl

/-! ### Elementary bounds -/

lemma rho_nonneg {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) : 0 ≤ (1 - p) / p := by
  positivity

lemma rho_lt_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) : (1 - p) / p < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

lemma one_div_p_le_three {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) : 1 / p ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- Both branches keep `h >= 1`. -/
lemma one_le_hstep {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) {b : Bool} {h : ℝ}
    (hh : 1 ≤ h) : 1 ≤ hstep p b h := by
  cases b with
  | false => simp only [hstep_false]; linarith
  | true =>
      simp only [hstep_true]
      have hr : 0 ≤ (1 - p) / p := by positivity
      have : 0 ≤ ((1 - p) / p) * h := by positivity
      have h2 : 1 / p ≥ 1 := by
        rw [ge_iff_le, le_div_iff₀ (by linarith)]; linarith
      linarith

/-- `h(x) <= h(x-1) + 2` at every site. -/
lemma hstep_le_add_two {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) {b : Bool} {h : ℝ}
    (hh : 1 ≤ h) : hstep p b h ≤ h + 2 := by
  cases b with
  | false => simp only [hstep_false]; linarith
  | true =>
      simp only [hstep_true]
      have hp0 : 0 < p := by linarith
      have hkey : 1 / p + ((1 - p) / p) * h = (1 + (1 - p) * h) / p := by
        field_simp
      rw [hkey, div_le_iff₀ hp0]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * p - 1) (by linarith : (0:ℝ) ≤ h + 1)]

lemma one_le_hfin {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (n : ℕ) (v : Fin n → Bool) :
    1 ≤ hfin p n v := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [hfin_succ]
      exact one_le_hstep hp1 hp2 (ih _)

/-- The value at the first site is at most `3`. -/
lemma hfin_one_le_three {p : ℝ} (hp1 : (1 : ℝ) / 2 ≤ p) (hp2 : p < 1) (v : Fin 1 → Bool) :
    hfin p 1 v ≤ 3 := by
  rw [hfin_succ]
  have h1 : hfin p 0 (fun i : Fin 0 => (v i.castSucc)) = 1 := rfl
  rw [h1]
  cases hv : v ⟨0, Nat.lt_succ_self 0⟩ with
  | false => rw [hstep_false]; norm_num
  | true =>
      rw [hstep_true]
      have hp0 : 0 < p := by linarith
      have hkey : 1 / p + ((1 - p) / p) * 1 = (1 + (1 - p)) / p := by field_simp
      rw [hkey, div_le_iff₀ hp0]
      nlinarith

/-! ### The one-step exponential contraction -/

/-- **The one-step contraction.**  With `gamma = (1-q) e^{2 theta} + q rho e^{theta/p}`,
`rho = (1-p)/p`, `q in [0,1]`, the branch-averaged exponential of `theta * h` contracts at
rate `gamma` up to the additive constant `q e^{theta/p}(1-rho)`.

This is the paper's display in the proof of Proposition "spatial", obtained with the weighted
AM-GM inequality `t^rho <= rho t + (1 - rho)` instead of a limiting supremum. -/
theorem one_step_bound {p q θ γ : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 ≤ q) (_hθ : 0 < θ)
    (hγ : (1 - q) * exp (2 * θ) + q * ((1 - p) / p) * exp (θ / p) ≤ γ) :
    ∀ h : ℝ, 1 ≤ h →
      (1 - q) * exp (θ * hstep p false h) + q * exp (θ * hstep p true h)
        ≤ γ * exp (θ * h) + q * exp (θ / p) * (1 - (1 - p) / p) := by
  intro h hh
  set r := (1 - p) / p with hr
  have hr0 : 0 ≤ r := rho_nonneg hp1 hp2
  have hr1 : r < 1 := rho_lt_one hp1 hp2
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < exp (θ * h) := exp_pos _
  -- rewrite both exponentials
  have e1 : exp (θ * hstep p false h) = exp (2 * θ) * exp (θ * h) := by
    rw [hstep_false, ← exp_add]; congr 1; ring
  have e2 : exp (θ * hstep p true h) = exp (θ / p) * (exp (θ * h)) ^ r := by
    rw [hstep_true]
    have : θ * (1 / p + r * h) = θ / p + (θ * h) * r := by ring
    rw [this, exp_add, Real.rpow_def_of_pos (exp_pos _), log_exp]
  -- weighted AM-GM
  have hgm : (exp (θ * h)) ^ r ≤ r * exp (θ * h) + (1 - r) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := r) (w₂ := 1 - r) (p₁ := exp (θ * h))
      (p₂ := 1) hr0 (by linarith) ht0.le (by norm_num) (by ring)
    simpa using h
  have hrhs : (1 - q) * exp (2 * θ) * exp (θ * h) + q * exp (θ / p) * r * exp (θ * h)
      ≤ γ * exp (θ * h) := by
    have h1 : (1 - q) * exp (2 * θ) * exp (θ * h) + q * exp (θ / p) * r * exp (θ * h)
        = ((1 - q) * exp (2 * θ) + q * r * exp (θ / p)) * exp (θ * h) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hγ ht0.le
  rw [e1, e2]
  have hexp : (0:ℝ) ≤ exp (θ / p) := (exp_pos _).le
  have hq : 0 ≤ q := hq0
  -- expand
  have expand : (1 - q) * (exp (2 * θ) * exp (θ * h))
      + q * (exp (θ / p) * (exp (θ * h)) ^ r)
      ≤ (1 - q) * (exp (2 * θ) * exp (θ * h))
        + q * (exp (θ / p) * (r * exp (θ * h) + (1 - r))) := by
    have h2 : q * (exp (θ / p) * (exp (θ * h)) ^ r)
        ≤ q * (exp (θ / p) * (r * exp (θ * h) + (1 - r))) := by
      apply mul_le_mul_of_nonneg_left _ hq
      exact mul_le_mul_of_nonneg_left hgm hexp
    linarith
  have final : (1 - q) * (exp (2 * θ) * exp (θ * h))
      + q * (exp (θ / p) * (r * exp (θ * h) + (1 - r)))
      ≤ γ * exp (θ * h) + q * exp (θ / p) * (1 - r) := by
    nlinarith [hrhs]
  linarith

/-- **Existence of the contraction parameters.**  For every `q in (0,1]` and `p in (1/2,1)`
there is `theta > 0` with `(1-q) e^{2 theta} + q rho e^{theta/p} < 1`, `rho = (1-p)/p`.

At `theta = 0` the left side equals `1 - q (1 - rho) < 1`, and it is continuous. -/
theorem exists_theta {p q : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ θ : ℝ, 0 < θ ∧ (1 - q) * exp (2 * θ) + q * ((1 - p) / p) * exp (θ / p) < 1 := by
  have hr0 : 0 ≤ (1 - p) / p := rho_nonneg hp1 hp2
  have hr1 : (1 - p) / p < 1 := rho_lt_one hp1 hp2
  have hp0 : 0 < p := by linarith
  set f : ℝ → ℝ := fun θ => (1 - q) * exp (2 * θ) + q * ((1 - p) / p) * exp (θ / p) with hf
  have h0 : f 0 < 1 := by
    simp only [hf, mul_zero, exp_zero, zero_div, mul_one]
    nlinarith
  have hcont : ContinuousAt f 0 := by
    apply ContinuousAt.add
    · exact ContinuousAt.const_mul (by fun_prop) _
    · exact ContinuousAt.const_mul (ContinuousAt.comp (by fun_prop) (by fun_prop)) _
  have hmem : f ⁻¹' Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
    hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε / 2, by positivity, ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
  linarith

end

end SwarmMarks

namespace SwarmMarks

noncomputable section

/-- The ratio multiplier `rho = (1-p)/p` at a marked site and `1` at an unmarked one. -/
def rhoOf (p : ℝ) (b : Bool) : ℝ := if b then (1 - p) / p else 1

lemma rhoOf_false (p : ℝ) : rhoOf p false = 1 := rfl
lemma rhoOf_true (p : ℝ) : rhoOf p true = (1 - p) / p := rfl

lemma measurable_rhoOf (p : ℝ) : Measurable (rhoOf p) := by
  unfold rhoOf
  measurability

/-- `hstep` in multiplicative form: `h(x) = 1 + rho(x) (1 + h(x-1))`. -/
lemma hstep_eq_rho {p : ℝ} (hp0 : p ≠ 0) (b : Bool) (h : ℝ) :
    hstep p b h = 1 + rhoOf p b * (1 + h) := by
  cases b with
  | false => simp only [hstep_false, rhoOf_false, mul_one]; ring
  | true =>
      simp only [hstep_true, rhoOf_true]
      field_simp
      ring

end
end SwarmMarks
