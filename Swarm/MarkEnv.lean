/-
# The marked environment `omega_j` and the comparison `(dominate)`

Third file of the mark layer: the environment attached to the marks, the paper's display
`(dominate)`, and the exact arithmetic of the ballistic constant `a`.

Paper `main_1d_revised.tex`, §2.1 displays `(marks)` and `(dominate)`:

  `B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}`,  `omega_j(x) = 1/2 + (p - 1/2) B_j(x)`,
  and for `i != j`,  `alpha_n^i >= omega_j(X_n^i)`  on  `{0 <= X_n^i < M_n^j}`,

together with the constant `a = E[(1 - omega_j(0))/omega_j(0)] = 1 - (2p-1)(1-p)^{m-1}/p`
and the remark `1/2 < 1 - (1-p)^{m-1} <= a < 1` for `m >= 2`, `p in (1/2,1)`.

* `envOfMark p m U j x` — the paper's `omega_j(x)` as a function of the uniform array;
* `envOfMark_mem` — `omega_j(x) in [1/2, p]`;
* `rightProbability_ge_envOfMark` — **display `(dominate)`**: the actual right-jump probability
  of walker `i` at a nonnegative site below walker `j`'s running maximum dominates `omega_j`;
* `aCoef` and `aCoef_mem` — the paper's `a` lies in `(1/2, 1)`, with the sharper
  `1 - (1-p)^{m-1} <= a`.

Everything is proved; see `ConcreteMarkAudit.lean` for the axiom audit.
-/
import Swarm.MarkOccupation

namespace Swarming.Marks

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped BigOperators

variable {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N}

/-- **The paper's `omega_j(x)`**: right-jump probability `p` at a marked site, `1/2` otherwise. -/
noncomputable def envOfMark (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) : ℝ := by
  classical
  exact if SiteMark p m U j x then p else 1 / 2

theorem envOfMark_of_mark (h : SiteMark p m U j x) : envOfMark p m U j x = p := by
  classical
  simp [envOfMark, h]

theorem envOfMark_of_not_mark (h : ¬ SiteMark p m U j x) : envOfMark p m U j x = 1 / 2 := by
  classical
  simp [envOfMark, h]

/-- `omega_j(x) in [1/2, p]`. -/
theorem envOfMark_mem (hp : 1 / 2 ≤ p) (j : Fin N) (x : ℤ) :
    1 / 2 ≤ envOfMark p m U j x ∧ envOfMark p m U j x ≤ p := by
  classical
  by_cases h : SiteMark p m U j x
  · rw [envOfMark_of_mark h]; exact ⟨hp, le_rfl⟩
  · rw [envOfMark_of_not_mark h]; exact ⟨le_rfl, hp⟩

/-- **Display `(dominate)`.**  If walker `i` sits at time `n` on a nonnegative site below walker
`j`'s running maximum, its right-jump probability is at least `omega_j` of that site: marked
sites are excited for `i` (so its probability is `p`), unmarked sites have probability at least
`1/2`. -/
theorem rightProbability_ge_envOfMark (hp : 1 / 2 ≤ p) {i j : Fin N} (hij : i ≠ j) {n : ℕ}
    (hx0 : 0 ≤ (trajectory p m U n).pos i)
    (hmax : SiteMark p m U j ((trajectory p m U n).pos i) →
      ∃ s ≤ n, (trajectory p m U n).pos i < (trajectory p m U s).pos j) :
    envOfMark p m U j ((trajectory p m U n).pos i)
      ≤ rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
  classical
  by_cases hmark : SiteMark p m U j ((trajectory p m U n).pos i)
  · rw [envOfMark_of_mark hmark]
    exact le_of_eq (rightProbability_eq_p_of_markHit hp hij hx0 ⟨hmark, hmax hmark⟩).symm
  · rw [envOfMark_of_not_mark hmark]
    exact one_half_le_rightProbability hp m _ i _

/-- **The paper's constant** `a = 1 - (2p-1)(1-p)^(m-1)/p`. -/
noncomputable def aCoef (p : ℝ) (m : ℕ) : ℝ :=
  1 - (2 * p - 1) * (1 - p) ^ (m - 1) / p

/-- **The paper's remark**: for `m >= 2` and `p in (1/2,1)`,
`1/2 < 1 - (1-p)^(m-1) <= a < 1`. -/
theorem aCoef_mem (hm : 2 ≤ m) (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    1 / 2 < 1 - (1 - p) ^ (m - 1) ∧ 1 - (1 - p) ^ (m - 1) ≤ aCoef p m ∧ aCoef p m < 1 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hhalf : 1 - p < 1 / 2 := by linarith
  have hk : 1 ≤ m - 1 := Nat.le_sub_of_add_le hm
  have hqle : (1 - p) ^ (m - 1) ≤ 1 - p := by
    have h := pow_le_pow_of_le_one (le_of_lt hq0) (le_of_lt hq1) (m := 1) (n := m - 1) hk
    simpa using h
  have hqpos : (0 : ℝ) < (1 - p) ^ (m - 1) := pow_pos hq0 _
  have hqhalf : (1 - p) ^ (m - 1) < 1 / 2 := lt_of_le_of_lt hqle hhalf
  have hcoef : (2 * p - 1) / p ≤ 1 := by
    rw [div_le_one hp0]
    linarith
  have heq : (2 * p - 1) * (1 - p) ^ (m - 1) / p
      = ((2 * p - 1) / p) * (1 - p) ^ (m - 1) := by field_simp
  refine ⟨by linarith, ?_, ?_⟩
  · rw [aCoef, heq]
    have hstep : ((2 * p - 1) / p) * (1 - p) ^ (m - 1) ≤ 1 * (1 - p) ^ (m - 1) :=
      mul_le_mul_of_nonneg_right hcoef (le_of_lt hqpos)
    linarith
  · rw [aCoef, heq]
    have hpos : 0 < ((2 * p - 1) / p) * (1 - p) ^ (m - 1) :=
      mul_pos (div_pos (by linarith) hp0) hqpos
    linarith

end Swarming.Marks


