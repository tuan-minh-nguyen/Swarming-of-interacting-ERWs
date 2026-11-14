/-
  **Direction B (m2): the interior `(Zloss)` input from the actual one-step conditional mean.**

  `Regional.condExp_drift_interior` computes the one-step conditional mean of the actual potential
  on the interior region `{X_n^i = k} ∩ {k < M_n^j}`:

      E[1_A (Hpot(X_{n+1}^i) - Hpot(X_n^i)) | F_n]
        =ᵐ 1_A (alpha_n^i h_j(k) - (1 - alpha_n^i) h^w_j(k-1)).

  This file evaluates the deterministic bracket with the paper's own deterministic inputs and
  obtains the inequality `>= 1` *inside the conditional expectation*:

  * `hof_eq_hw` — the actual site-mark potential `hof p (siteMarks p m U j)` is the paper's
    `h^{omega_j}` for `omega_j(x) = omegaAt p m U j x` (both are the `hrec` recursion, driven by
    `rhoOf` / `rOf`, and `RawLogRatio.rho_omegaAt` identifies the ratios);
  * `interior_bracket_ge_one` — on `{0 <= X_n^i < M_n^j}`,
        `1 <= alpha_n^i h_j(k) - (1 - alpha_n^i) h^w_j(k-1)`,
    from `(dominate)` (`Swarming.Trajectory.dominate`), `(unit)` (`SwarmOcc.unit_hw`) and
    `1 <= h_j` (`ExcitedEnv.one_le_hw`), via the deterministic case lemma
    `SwarmOcc.zdrift_interior`;
  * `condExp_drift_interior_ge_one` — consequently
        `1{A} <=ᵐ (arrayMeasure N)[1_A (Hpot(X_{n+1}^i) - Hpot(X_n^i)) | enlFilt p m n]`,
    which is exactly the interior contribution to the paper's `(Zloss)`.
-/
import Swarm.Regional

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmCross

variable {N : ℕ}

/-! ### The actual site-mark potential is the paper's `h^{omega_j}` -/

theorem rhoOf_eq_spatial (p : ℝ) (b : Bool) :
    SwarmMarks.rhoOf p b = SwarmSpatial.rhoOf p b := by
  cases b <;> norm_num [SwarmMarks.rhoOf, SwarmSpatial.rhoOf, SwarmSpatial.omegaOf]

/-- **`h_j = h^{omega_j}`.**  The actual `hof` computed from the site marks of walker `j` is the
paper's potential of the weight function `omega_j(x) = omegaAt p m U j x`. -/
theorem hof_eq_hw {p : ℝ} (hp0 : p ≠ 0) (m : ℕ) (U : Array N) (j : Fin N) (x : ℕ) :
    SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) x
      = ExcitedEnv.hw (fun (v : ℕ) => omegaAt p m U j (v : ℤ)) x := by
  have hne : ∀ u : ℕ, omegaAt p m U j (u : ℤ) ≠ 0 := by
    intro u
    by_cases h : SiteMark p m U j (u : ℤ)
    · rw [show omegaAt p m U j (u : ℤ) = p from by simp [omegaAt, h]]
      exact hp0
    · rw [show omegaAt p m U j (u : ℤ) = 1 / 2 from by simp [omegaAt, h]]
      norm_num
  have hrOf : ∀ u : ℕ, ExcitedEnv.rOf (fun (v : ℕ) => omegaAt p m U j (v : ℤ)) u
      = SwarmMarks.rhoOf p (SwarmLogRatio.siteMarks p m U j u) := by
    intro u
    rw [ExcitedEnv.rOf, SwarmLogRatio.rho_omegaAt, rhoOf_eq_spatial]
  induction x with
  | zero =>
      rw [SwarmMarks.hof_zero, SwarmMarks.hstep_eq_rho hp0, ExcitedEnv.hw_rec' _ hne 0,
        hrOf 0]
      rfl
  | succ k ih =>
      rw [SwarmMarks.hof_succ, SwarmMarks.hstep_eq_rho hp0, ExcitedEnv.hw_rec' _ hne (k + 1),
        hrOf (k + 1), ExcitedEnv.hprev_succ, ih]

/-! ### The interior bracket is at least one -/

/-- **The interior bracket of `(Zloss)` is at least `1`** on `{0 <= X_n^i = k < M_n^j}`.

This is `SwarmOcc.zdrift_interior` fed with the paper's three inputs:
`(dominate)` for the weight comparison, `(unit)` for the Poisson identity of `h^{omega_j}`, and
`1 <= h^w` for the nonnegativity of the sum. -/
theorem interior_bracket_ge_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} {i j : Fin N} (hij : i ≠ j) {k : ℕ} {U : Array N}
    (hx : (trajectory p m U n).pos i = (k : ℤ))
    (hkM : (k : ℤ) < runMax p m U j n) :
    1 ≤ alphaFun p m n i U * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k
      - (1 - alphaFun p m n i U) * hZpot (envH p m j U) ((k : ℤ) - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hx0 : (0 : ℤ) ≤ (trajectory p m U n).pos i := by rw [hx]; exact_mod_cast Nat.zero_le k
  have hprev : hZpot (envH p m j U) ((k : ℤ) - 1)
      = ExcitedEnv.hprev (fun (v : ℕ) => omegaAt p m U j (v : ℤ)) k := by
    rcases k with _ | k'
    · rw [show (((0 : ℕ)) : ℤ) - 1 = (-1 : ℤ) from rfl, hZpot_of_nonpos (by norm_num),
        ExcitedEnv.hprev_zero]
    · have hcast : (((k' + 1 : ℕ)) : ℤ) - 1 = (k' : ℤ) := by push_cast; ring
      rw [hcast, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k'), Int.toNat_natCast,
        ExcitedEnv.hprev_succ]
      exact hof_eq_hw hp0 m U j k'
  -- the paper's weight and potential at the site
  have hwne : omegaAt p m U j (k : ℤ) ≠ 0 := by
    by_cases h : SiteMark p m U j (k : ℤ)
    · rw [show omegaAt p m U j (k : ℤ) = p from by simp [omegaAt, h]]; exact hp0
    · rw [show omegaAt p m U j (k : ℤ) = 1 / 2 from by simp [omegaAt, h]]; norm_num
  have hw0 : 0 ≤ omegaAt p m U j (k : ℤ) := by
    by_cases h : SiteMark p m U j (k : ℤ)
    · rw [show omegaAt p m U j (k : ℤ) = p from by simp [omegaAt, h]]; linarith
    · rw [show omegaAt p m U j (k : ℤ) = 1 / 2 from by simp [omegaAt, h]]; norm_num
  have hw1 : omegaAt p m U j (k : ℤ) ≤ 1 := by
    by_cases h : SiteMark p m U j (k : ℤ)
    · rw [show omegaAt p m U j (k : ℤ) = p from by simp [omegaAt, h]]; linarith
    · rw [show omegaAt p m U j (k : ℤ) = 1 / 2 from by simp [omegaAt, h]]; norm_num
  -- `(dominate)`
  have hαw : omegaAt p m U j (k : ℤ) ≤ alphaFun p m n i U := by
    have hdom := dominate hp1.le m U hij n hx0 (by rw [hx]; exact hkM)
    rw [hx] at hdom
    have halpha : alphaFun p m n i U
        = rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) := rfl
    rw [halpha, hx]
    exact hdom
  -- `1 <= h_j(k)` and `1 <= h_j(k-1)`
  have hω : ∀ u : ℕ, omegaAt p m U j (u : ℤ) = 1 / 2 ∨ omegaAt p m U j (u : ℤ) = p := by
    intro u
    by_cases h : SiteMark p m U j (u : ℤ)
    · right; simp [omegaAt, h]
    · left; simp [omegaAt, h]
  have h1 : 1 ≤ SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k := by
    rw [hof_eq_hw hp0 m U j k]
    exact ExcitedEnv.one_le_hw hp1 hp2 hω k
  have h1' : 1 ≤ hZpot (envH p m j U) ((k : ℤ) - 1) := by
    rw [hprev]
    exact ExcitedEnv.one_le_hprev hp1 hp2 hω k
  -- `(unit)`
  have hunit : omegaAt p m U j (k : ℤ) * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k
      - (1 - omegaAt p m U j (k : ℤ)) * hZpot (envH p m j U) ((k : ℤ) - 1) = 1 := by
    rw [hof_eq_hw hp0 m U j k, hprev]
    exact SwarmOcc.unit_hw (ω := fun u => omegaAt p m U j (u : ℤ)) hwne
  refine SwarmOcc.zdrift_interior hw0 hw1 hαw ?_ ?_ (by linarith [h1, h1']) hunit
  · rw [hof_eq_hw hp0 m U j k]
  · rw [hprev]

/-! ### The interior conditional mean is at least one -/

/-- **The interior contribution to `(Zloss)`**, with the actual trajectory, the actual
`arrayMeasure N` and the actual enlarged filtration: on `A = {X_n^i = k} ∩ {k < M_n^j}`,

    `1{A} <=ᵐ (arrayMeasure N)[1_A (Hpot(X_{n+1}^i) - Hpot(X_n^i)) | enlFilt p m n]`. -/
theorem condExp_drift_interior_ge_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (i j : Fin N) (hij : i ≠ j) (k : ℕ) :
    (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N] condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
            ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  have hle : (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N] fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
          ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => alphaFun p m n i U * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k
          - (1 - alphaFun p m n i U) * hZpot (envH p m j U) ((k : ℤ) - 1)) U := by
    refine Filter.Eventually.of_forall (fun U => ?_)
    dsimp only
    by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
      exact interior_bracket_ge_one hp1 hp2 hij hU.1 hU.2
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  exact hle.trans_eq (condExp_drift_interior hp1 hp2 i j k).symm

/-! ### The negative region's `(Zloss)` contribution -/

/-- `alpha_n^i >= 1/2` for the actual right probability. -/
lemma one_half_le_alphaFun {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp0 : p < 1) (m n : ℕ) (i : Fin N)
    (U : Array N) : (1 : ℝ) / 2 ≤ alphaFun p m n i U := by
  have halpha : alphaFun p m n i U
      = rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) := rfl
  rw [halpha]
  exact one_half_le_rightProbability hp1.le m _ i _

/-- **The negative region's contribution to `(Zloss)`**: on `{X_n^i < 0}` the one-step
conditional drift of the actual potential is `2 alpha_n^i - 1 >= 0`. -/
theorem condExp_drift_neg_ge_zero {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} (i j : Fin N) :
    (fun _ => (0 : ℝ)) ≤ᵐ[arrayMeasure N]
      condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
  have hid := condExp_drift_neg hp0 hp1 (m := m) (n := n) i j
  have hle : (fun _ => (0 : ℝ)) ≤ᵐ[arrayMeasure N]
      fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
        (fun U => 2 * alphaFun p m n i U - 1) U := by
    refine Filter.Eventually.of_forall (fun U => ?_)
    dsimp only
    by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i < 0})
    · rw [Set.indicator_of_mem hU]
      have h := one_half_le_alphaFun hp0 hp1 m n i U
      linarith
    · rw [Set.indicator_of_notMem hU]
  exact hle.trans_eq hid.symm

end Swarming.Enl


