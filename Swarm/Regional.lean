/-
  **Direction B (m2): the one-step Poisson drift on the two regions below the record.**

  `PullOut.condExp_drift_of_adapted` computes the one-step conditional mean of the potential
  increment on any adapted event on which the two environment values are adapted.  This file
  instantiates it on the two regions where that measurability holds for the *actual* environment
  `h_j = hof p (siteMarks p m · j)`, using `BelowMeas.measurable_indicator_hof_of_below`:

  * `condExp_drift_neg` — the region `{X_n^i < 0}`.  There `h^w(x) = h^w(x-1) = 1`, so the
    drift is exactly `2 alpha_n^i - 1` (nonnegative, the paper's `zdrift_neg` input), with no
    environment measurability needed at all;
  * `condExp_drift_interior` — the region `{X_n^i = k} ∩ {k < M_n^j}` for a natural site `k`.
    Both `h_j(k)` and `h_j(k-1)` lie below the record, hence are `enlFilt p m n`-measurable there
    (`measurable_below_hof`), and the drift is exactly

        alpha_n^i h_j(k) - (1 - alpha_n^i) h^w_j(k-1),

    which is the paper's interior term; combined with `(dominate)` and `(unit)` it gives
    `zdrift_interior` (`SwarmOcc.zdrift_interior`).

  The record region and the above-record region are *not* instances: there `h_j(M_n^j)` is not
  `enlFilt`-measurable, and the theorem records that boundary instead of crossing it.
-/
import Swarm.BelowMeas
import Swarm.Zdrift

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory
open SwarmCross

variable {N : ℕ}

/-- The actual environment of walker `j`, as a `(U, x)`-dependent function. -/
noncomputable def envH (p : ℝ) (m : ℕ) (j : Fin N) : Array N → ℕ → ℝ :=
  fun U u => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) u

/-! ### The region `{X_n^i < 0}` -/

/-- **The one-step drift below zero.**  On `{X_n^i < 0}` the potential steps are the constant `1`,
so the drift is exactly `2 alpha_n^i - 1`. -/
theorem condExp_drift_neg {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1)
    {m n : ℕ} (i j : Fin N) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U)
      =ᵐ[arrayMeasure N] fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
          (fun U => 2 * alphaFun p m n i U - 1) U := by
  have hA : MeasurableSet[enlFilt p m n] {U : Array N | (trajectory p m U n).pos i < 0} :=
    enl_pos_measurable p m n le_rfl i (measurableSet_lt measurable_id measurable_const)
  have hz : ∀ U : Array N, (trajectory p m U n).pos i < 0 →
      hZpot (envH p m j U) ((trajectory p m U n).pos i) = 1 := by
    intro U hU
    exact hZpot_of_nonpos (by omega)
  have hz1 : ∀ U : Array N, (trajectory p m U n).pos i < 0 →
      hZpot (envH p m j U) ((trajectory p m U n).pos i - 1) = 1 := by
    intro U hU
    exact hZpot_of_nonpos (by omega)
  have hup : Measurable[enlFilt p m n]
      (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U) := by
    have heq : (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U)
        = fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
          (fun _ => (1 : ℝ)) U := by
      funext U
      by_cases hU : (trajectory p m U n).pos i < 0
      · rw [Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU),
          Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU), hz U hU]
      · rw [Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU),
          Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU)]
    rw [heq]
    exact Measurable.indicator measurable_const hA
  have hdn : Measurable[enlFilt p m n]
      (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U) := by
    have heq : (fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U)
        = fun U => ({U : Array N | (trajectory p m U n).pos i < 0}).indicator
          (fun _ => (1 : ℝ)) U := by
      funext U
      by_cases hU : (trajectory p m U n).pos i < 0
      · rw [Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU),
          Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU), hz1 U hU]
      · rw [Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU),
          Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU)]
    rw [heq]
    exact Measurable.indicator measurable_const hA
  have hcup : ∀ U : Array N, ‖({U : Array N | (trajectory p m U n).pos i < 0}).indicator
      (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U‖ ≤ 1 := by
    intro U
    by_cases hU : (trajectory p m U n).pos i < 0
    · rw [Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU), hz U hU]
      simp
    · rw [Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU)]
      simp
  have hcdn : ∀ U : Array N, ‖({U : Array N | (trajectory p m U n).pos i < 0}).indicator
      (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U‖ ≤ 1 := by
    intro U
    by_cases hU : (trajectory p m U n).pos i < 0
    · rw [Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU), hz1 U hU]
      simp
    · rw [Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU)]
      simp
  refine (condExp_drift_of_adapted (p := p) hp0 hp1 (m := m) (n := n)
    (h := envH p m j) i hA hup hdn 1 zero_le_one hcup hcdn).trans ?_
  refine Filter.EventuallyEq.of_eq ?_
  funext U
  by_cases hU : (trajectory p m U n).pos i < 0
  · rw [Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU),
      Set.indicator_of_mem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (Set.mem_ofPred_eq.mpr hU), hz U hU, hz1 U hU]
    ring
  · rw [Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU),
      Set.indicator_of_notMem (s := {U : Array N | (trajectory p m U n).pos i < 0}) (by simpa using hU)]


/-! ### The interior region `{X_n^i = k} ∩ {k < M_n^j}` -/

/-- On `{X_n^i = k}` the integer-indexed step of the potential at the actual environment is
`h_j(k)`. -/
lemma hZpot_envH_of_pos {p : ℝ} {m n : ℕ} (i j : Fin N) {k : ℕ} {U : Array N}
    (hx : (trajectory p m U n).pos i = (k : ℤ)) :
    hZpot (envH p m j U) ((trajectory p m U n).pos i)
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k := by
  rw [hx, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k), Int.toNat_natCast]
  rfl

/-- The restricted potential step at the actual value is `F_n`-measurable on the interior
region. -/
lemma measurable_indicator_hZpot_at {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (i j : Fin N)
    (k : ℕ) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (hAM : A ⊆ {U : Array N | (k : ℤ) < runMax p m U j n})
    (hAx : A ⊆ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}) :
    Measurable[enlFilt p m n]
      (A.indicator (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i))) := by
  have hbelow := measurable_indicator_hof_of_below (p := p) hp m n j k hA hAM
  have heq : A.indicator (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i))
      = A.indicator (fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k) := by
    funext U
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, hZpot_envH_of_pos i j (hAx hU)]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  rw [heq]
  exact hbelow

/-- The restricted backward potential step at a site below the record is `F_n`-measurable. -/
lemma measurable_indicator_hZpot_pred {p : ℝ} (hp : (1 : ℝ) / 2 ≤ p) (m n : ℕ) (i j : Fin N)
    (k : ℕ) {A : Set (Array N)} (hA : MeasurableSet[enlFilt p m n] A)
    (hAM : A ⊆ {U : Array N | (k : ℤ) < runMax p m U j n})
    (hAx : A ⊆ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)}) :
    Measurable[enlFilt p m n]
      (A.indicator (fun U => hZpot (envH p m j U) ((k : ℤ) - 1))) := by
  rcases k with _ | k'
  · -- site `0`: the backward step is the boundary value `h(-1) = 1`
    have heq : (fun U : Array N => hZpot (envH p m j U) (((0 : ℕ) : ℤ) - 1))
        = fun _ => (1 : ℝ) := by
      funext U
      exact hZpot_of_nonpos (by norm_num)
    rw [heq]
    exact Measurable.indicator measurable_const hA
  · -- site `k'+1`: the backward step is `h_j(k')`, whose site is below the record
    have hAM' : A ⊆ {U : Array N | ((k' : ℕ) : ℤ) < runMax p m U j n} := by
      intro U hU
      have h := hAM hU
      have h2 : ((k' : ℕ) : ℤ) < ((k' + 1 : ℕ) : ℤ) := by push_cast; omega
      exact lt_trans h2 h
    have hbelow := measurable_indicator_hof_of_below (p := p) hp m n j k' hA hAM'
    have heq : (fun U : Array N => hZpot (envH p m j U) (((k' + 1 : ℕ) : ℤ) - 1))
        = fun U => SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k' := by
      funext U
      have hcast : ((k' + 1 : ℕ) : ℤ) - 1 = (k' : ℤ) := by push_cast; ring
      rw [hcast, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k'), Int.toNat_natCast]
      rfl
    rw [heq]
    exact hbelow

/-- **The one-step drift on the interior region** `{X_n^i = k} ∩ {k < M_n^j}`: both
`h_j(k)` and `h^w_j(k-1)` lie below the record, hence are `enlFilt p m n`-measurable there, and
the conditional mean of the potential increment is exactly

    `alpha_n^i h_j(k) - (1 - alpha_n^i) h^w_j(k-1)`. -/
theorem condExp_drift_interior {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m n : ℕ} (i j : Fin N) (k : ℕ) :
    condExp (enlFilt p m n) (arrayMeasure N)
        (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
            ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
          (fun U => SwarmOcc.Hpot (envH p m j U) ((trajectory p m U (n + 1)).pos i)
            - SwarmOcc.Hpot (envH p m j U) ((trajectory p m U n).pos i)) U)
      =ᵐ[arrayMeasure N] fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
            ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
          (fun U => alphaFun p m n i U * SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k
            - (1 - alphaFun p m n i U) * hZpot (envH p m j U) ((k : ℤ) - 1)) U := by
  have hp0 : p ≠ 0 := by linarith
  have hAeq : MeasurableSet[enlFilt p m n] {U : Array N | (trajectory p m U n).pos i = (k : ℤ)} :=
    enl_pos_measurable p m n le_rfl i (measurableSet_singleton (k : ℤ))
  have hAMset : MeasurableSet[enlFilt p m n] {U : Array N | (k : ℤ) < runMax p m U j n} :=
    measurableSet_lt_runMax p m n j k
  have hA : MeasurableSet[enlFilt p m n]
      ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}) := hAeq.inter hAMset
  have hAM : ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
      ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
      ⊆ {U : Array N | (k : ℤ) < runMax p m U j n} := Set.inter_subset_right
  have hAx : ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
      ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
      ⊆ {U : Array N | (trajectory p m U n).pos i = (k : ℤ)} := Set.inter_subset_left
  have hup := measurable_indicator_hZpot_at (p := p) hp1.le m n i j k hA hAM hAx
  have hdnk := measurable_indicator_hZpot_pred (p := p) hp1.le m n i j k hA hAM hAx
  have heqdn : (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
      (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U)
      = fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
      (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U := by
    funext U
    by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, hU.1]
    · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]
  have hdn : Measurable[enlFilt p m n]
      (fun U => ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
          ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U) := by
    rw [heqdn]
    exact hdnk
  -- the uniform bound `2n + 3`
  have hcup : ∀ U : Array N, ‖({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i)) U‖ ≤ 2 * (n : ℝ) + 3 := by
    intro U
    by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
    · rw [Set.indicator_of_mem hU, hZpot_envH_of_pos i j hU.1, Real.norm_eq_abs]
      have hkn : k ≤ n := by
        have h1 : (trajectory p m U n).pos i = (k : ℤ) := hU.1
        have h2 : (trajectory p m U n).pos i ≤ (n : ℤ) := (pos_bounds U n i).2
        have : (k : ℤ) ≤ (n : ℤ) := by rw [← h1]; exact h2
        exact_mod_cast this
      have h := SwarmShiftMarks.abs_hof_le' hp1 hp2 hp0 (SwarmLogRatio.siteMarks p m U j) k
      have hk : 2 * (k : ℝ) + 3 ≤ 2 * (n : ℝ) + 3 := by
        have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        linarith
      exact le_trans h hk
    · rw [Set.indicator_of_notMem hU]; simp only [norm_zero]; positivity
  have hcdnk : ∀ U : Array N, ‖({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U‖ ≤ 2 * (n : ℝ) + 3 := by
    intro U
    by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
    · rw [Set.indicator_of_mem hU, Real.norm_eq_abs]
      rcases k with _ | k'
      · rw [hZpot_of_nonpos (by norm_num)]
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        rw [abs_one]; linarith
      · have hcast : (((k' + 1 : ℕ)) : ℤ) - 1 = (k' : ℤ) := by push_cast; ring
        rw [hcast, hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k'), Int.toNat_natCast]
        have hkn : k' ≤ n := by
          have h1 : (trajectory p m U n).pos i = ((k' + 1 : ℕ) : ℤ) := hU.1
          have h2 : (trajectory p m U n).pos i ≤ (n : ℤ) := (pos_bounds U n i).2
          have h3 : ((k' + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by rw [← h1]; exact h2
          have : ((k' : ℕ) : ℤ) ≤ (n : ℤ) := by
            have : ((k' : ℕ) : ℤ) ≤ ((k' + 1 : ℕ) : ℤ) := by push_cast; omega
            omega
          exact_mod_cast this
        have h := SwarmShiftMarks.abs_hof_le' hp1 hp2 hp0 (SwarmLogRatio.siteMarks p m U j) k'
        have hk : 2 * (k' : ℝ) + 3 ≤ 2 * (n : ℝ) + 3 := by
          have : (k' : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
          linarith
        exact le_trans h hk
    · rw [Set.indicator_of_notMem hU]; simp only [norm_zero]; positivity
  have hcdn : ∀ U : Array N, ‖({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
        ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U‖ ≤ 2 * (n : ℝ) + 3 := by
    intro U
    rw [show ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
          ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((trajectory p m U n).pos i - 1)) U
        = ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
          ∩ {U : Array N | (k : ℤ) < runMax p m U j n}).indicator
        (fun U => hZpot (envH p m j U) ((k : ℤ) - 1)) U from congrFun heqdn U]
    exact hcdnk U
  refine (condExp_drift_of_adapted (p := p) (by linarith) hp2 (m := m) (n := n)
    (h := envH p m j) i hA hup hdn (2 * (n : ℝ) + 3) (by positivity) hcup hcdn).trans ?_
  refine Filter.EventuallyEq.of_eq ?_
  funext U
  by_cases hU : U ∈ ({U : Array N | (trajectory p m U n).pos i = (k : ℤ)}
      ∩ {U : Array N | (k : ℤ) < runMax p m U j n})
  · have hk : (trajectory p m U n).pos i = (k : ℤ) := hU.1
    rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU, hk]
    have hzk : hZpot (envH p m j U) ((k : ℤ))
        = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U j) k := by
      rw [hZpot_of_nonneg (by exact_mod_cast Nat.zero_le k), Int.toNat_natCast]
      rfl
    rw [hzk]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

end Swarming.Enl


