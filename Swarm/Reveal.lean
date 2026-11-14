/-
  **The paper's number-of-visits revelation inequality (reveal) and the domination (dominate).**

  In `main_1d_revised.tex`, immediately before Proposition "spatial":

      {M_n^j >= x+1, B_j(x) = 1} ⊆ {L_n^j(x) >= m},                                   (reveal)
      alpha_n^i >= omega_j(X_n^i)   on  {0 <= X_n^i < M_n^j}.                          (dominate)

  Both are *deterministic* statements about the strong trajectory
  `Swarming.Trajectory.trajectory` and the uniform array `Swarming.Uniform.Array N`; only the
  probability space enters when the array is averaged.  They are the mechanism by which the
  environment marks constrain the interaction: a marked site must be *left* `m-1` times to the
  left before it can ever be crossed to the right, so the other walkers are excited there.

  This file proves them from the existing deterministic modules only
  (`UniformArray`, `LocalTime`, `Swarming`, `Trajectory`), nothing is redefined.

  * `SiteMark` is the paper's `B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}`;
  * `omegaAt` is the paper's `omega_j(x) = 1/2 + (p-1/2) B_j(x)`;
  * `runMax` is the paper's `M_n^j = max_{0 <= t <= n} X_t^j`.
-/
import Swarm.Imports
import Swarm.UniformArray
import Swarm.LocalTime
import Swarm.Swarming
import Swarm.Trajectory

namespace Swarming.Trajectory

open Swarming Swarming.Model Swarming.Uniform Swarming.Paths
open Finset

noncomputable section

/-! ### The environment as seen by the trajectory -/

/-- The paper's site mark `B_j(x) = prod_{k=1}^{m-1} 1{U^j(x,k) > p}`: all of the first `m-1`
departure uniforms at the site `x` of walker `j` exceed `p`. -/
def SiteMark {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (m - 1), p < U (j, x, k)

/-- The paper's `omega_j(x) = 1/2 + (p - 1/2) B_j(x)` on nonnegative sites. -/
def omegaAt {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) : ℝ := by
  classical
  exact if SiteMark p m U j x then p else 1 / 2

/-- The running maximum `M_n^j = max_{0 <= t <= n} X_t^j`. -/
def runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun t => (trajectory p m U t).pos j)

lemma le_runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    (trajectory p m U n).pos j ≤ runMax p m U j n :=
  Finset.le_sup' (fun t => (trajectory p m U t).pos j)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

lemma exists_eq_runMax {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    ∃ t ≤ n, (trajectory p m U t).pos j = runMax p m U j n := by
  obtain ⟨t, ht, hte⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (n + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun t => (trajectory p m U t).pos j)
  exact ⟨t, Nat.lt_succ_iff.mp (Finset.mem_range.mp ht), hte.symm⟩

/-! ### Elementary facts about one step -/

lemma drivenStep_eq_one_of_le {u α : ℝ} (h : u ≤ α) : drivenStep u α = 1 := by
  simp [drivenStep, h]

lemma drivenStep_eq_neg_one_of_not_le {u α : ℝ} (h : ¬ u ≤ α) : drivenStep u α = -1 := by
  simp [drivenStep, h]

lemma drivenStep_le_one (u α : ℝ) : drivenStep u α ≤ 1 := by
  unfold drivenStep
  split <;> norm_num

/-- One step moves the walker up by at most one. -/
lemma pos_succ_le {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (j : Fin N) :
    (trajectory p m U (n + 1)).pos j ≤ (trajectory p m U n).pos j + 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  have h := drivenStep_le_one
    (U (j, (trajectory p m U n).pos j, (trajectory p m U n).ell j ((trajectory p m U n).pos j)))
    (rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j))
  omega

/-- The local time stored at the current position is at least one. -/
lemma one_le_ell_of_pos {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) :
    ∀ (n : ℕ) {x : ℤ}, (trajectory p m U n).pos j = x → 1 ≤ (trajectory p m U n).ell j x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      rw [trajectory_zero, initialWalkState] at hx ⊢
      simp only [if_pos hx.symm]
      norm_num
  | succ n ih =>
      intro x hx
      rw [trajectory_succ] at hx ⊢
      rw [nextWalkState_pos] at hx
      rw [nextWalkState_ell, if_pos hx.symm]
      omega

/-! ### A marked site must be left to the left during its first `m-1` visits -/

/-- **The one-visit mechanism.**  If the site `x` is marked, then at any time at which walker `j`
sits at `x` with local time `k` in `{1, ..., m-1}`, the jump just taken is a jump to the *left*:
the departure uniform `U^j(x,k)` exceeds `p`, hence exceeds the right probability. -/
theorem pos_succ_eq_sub_one_of_mark {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N)
    (j : Fin N) {x : ℤ} (hmark : SiteMark p m U j x) {n : ℕ}
    (hpos : (trajectory p m U n).pos j = x)
    (h1 : 1 ≤ (trajectory p m U n).ell j x)
    (hm : (trajectory p m U n).ell j x < m) :
    (trajectory p m U (n + 1)).pos j = x - 1 := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  have hu : p < U (j, x, (trajectory p m U n).ell j x) :=
    hmark _ (Finset.mem_Icc.mpr ⟨h1, by omega⟩)
  have hα : rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j) ≤ p :=
    rightProbability_le_p hp m _ j _
  rw [hpos] at hα
  have hnot : ¬ U (j, (trajectory p m U n).pos j,
        (trajectory p m U n).ell j ((trajectory p m U n).pos j))
      ≤ rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j) := by
    rw [hpos]
    intro hle
    linarith
  rw [drivenStep_eq_neg_one_of_not_le hnot, hpos]
  ring

/-! ### (reveal) -/

/-- **The invariant**: as long as walker `j` has visited a marked site `x >= 0` fewer than `m`
times, it cannot be to the right of `x`. -/
theorem pos_le_of_ell_lt {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) {m : ℕ} (U : Array N)
    (j : Fin N) {x : ℤ} (hx : 0 ≤ x) (hmark : SiteMark p m U j x) :
    ∀ n : ℕ, (trajectory p m U n).ell j x < m → (trajectory p m U n).pos j ≤ x := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [trajectory_zero, initialWalkState]
      simpa using hx
  | succ n ih =>
      intro hell
      have hmono : (trajectory p m U n).ell j x ≤ (trajectory p m U (n + 1)).ell j x := by
        rw [trajectory_succ, nextWalkState_ell]
        split <;> omega
      have helln : (trajectory p m U n).ell j x < m := lt_of_le_of_lt hmono hell
      by_cases hpx : (trajectory p m U n).pos j = x
      · have h1 : 1 ≤ (trajectory p m U n).ell j x := one_le_ell_of_pos p m U j n hpx
        have hstep := pos_succ_eq_sub_one_of_mark hp m U j hmark hpx h1 helln
        rw [hstep]
        omega
      · have hle := ih helln
        have hle' : (trajectory p m U n).pos j ≤ x - 1 := by omega
        have hstep := pos_succ_le p m U n j
        omega

/-- **The paper's (reveal).**  If the site `x >= 0` is marked for walker `j` and walker `j` has
reached `x+1` by time `n`, then it has visited `x` at least `m` times by time `n`. -/
theorem reveal {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N) (j : Fin N)
    {x : ℤ} (hx : 0 ≤ x) (hmark : SiteMark p m U j x) {n : ℕ}
    (hreach : ∃ t ≤ n, x + 1 ≤ (trajectory p m U t).pos j) :
    m ≤ (trajectory p m U n).ell j x := by
  by_contra hcon
  have hell : (trajectory p m U n).ell j x < m := not_le.mp hcon
  obtain ⟨t, ht, htp⟩ := hreach
  have hmono : (trajectory p m U t).ell j x ≤ (trajectory p m U n).ell j x := by
    rw [ell_eq_localTime p m U t j x, ell_eq_localTime p m U n j x]
    exact localTime_mono (fun k => (trajectory p m U k).pos j) ht x
  have hle := pos_le_of_ell_lt hp U j hx hmark t (lt_of_le_of_lt hmono hell)
  omega

/-- **The paper's (reveal)**, with the running maximum and the path local times: on
`{M_n^j >= x+1, B_j(x) = 1}` we have `L_n^j(x) >= m`. -/
theorem reveal_runMax {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N) (j : Fin N)
    {x : ℤ} (hx : 0 ≤ x) (hmark : SiteMark p m U j x) {n : ℕ}
    (hmax : x + 1 ≤ runMax p m U j n) :
    m ≤ localTime (fun k => (trajectory p m U k).pos j) n x := by
  rw [← ell_eq_localTime p m U n j x]
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j n
  exact reveal hp m U j hx hmark ⟨t, ht, by rw [hte]; exact hmax⟩

/-! ### (dominate) -/

/-- **The paper's (dominate).**  For `i != j`, at every site `0 <= X_n^i < M_n^j` the actual right
probability of walker `i` dominates the environment value `omega_j(X_n^i)`: if the site is unmarked
this is trivial (`alpha >= 1/2`), and if it is marked then (reveal) shows that walker `j` has
already activated the site `m` times, so walker `i` is excited there. -/
theorem dominate {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N)
    {i j : Fin N} (hij : i ≠ j) (n : ℕ)
    (h0 : 0 ≤ (trajectory p m U n).pos i)
    (hlt : (trajectory p m U n).pos i < runMax p m U j n) :
    omegaAt p m U j ((trajectory p m U n).pos i)
      ≤ rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
  by_cases hmark : SiteMark p m U j ((trajectory p m U n).pos i)
  · have homega : omegaAt p m U j ((trajectory p m U n).pos i) = p := by
      simp [omegaAt, hmark]
    rw [homega]
    obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j n
    have hreach : ∃ s ≤ n, (trajectory p m U n).pos i + 1 ≤ (trajectory p m U s).pos j := by
      refine ⟨t, ht, ?_⟩
      rw [hte]
      omega
    have hellj : m ≤ (trajectory p m U n).ell j ((trajectory p m U n).pos i) :=
      reveal hp m U j h0 hmark hreach
    have hother : m ≤ otherVisits (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
      have hsum : (if j = i then 0
            else (trajectory p m U n).ell j ((trajectory p m U n).pos i))
          ≤ otherVisits (trajectory p m U n).ell i ((trajectory p m U n).pos i) := by
        dsimp [otherVisits]
        refine Finset.single_le_sum
          (f := fun l : Fin N => if l = i then 0
            else (trajectory p m U n).ell l ((trajectory p m U n).pos i))
          (fun l _ => ?_) (Finset.mem_univ j)
        split <;> omega
      rw [if_neg (Ne.symm hij)] at hsum
      exact hellj.trans hsum
    have hexc : Excited m (trajectory p m U n).ell i ((trajectory p m U n).pos i) := hother
    simp only [rightProbability, hexc, if_true]
    exact le_rfl
  · have homega : omegaAt p m U j ((trajectory p m U n).pos i) = 1 / 2 := by
      simp [omegaAt, hmark]
    rw [homega]
    exact one_half_le_rightProbability hp m _ i _

/-- **The paper's (reveal) as a set inclusion**, for every `n` and every site `x >= 0`:
`{M_n^j >= x+1, B_j(x) = 1} ⊆ {L_n^j(x) >= m}`. -/
theorem reveal_set {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (j : Fin N) {x : ℤ} (hx : 0 ≤ x)
    (n : ℕ) :
    {U : Array N | x + 1 ≤ runMax p m U j n ∧ SiteMark p m U j x}
      ⊆ {U : Array N | m ≤ localTime (fun k => (trajectory p m U k).pos j) n x} := by
  intro U hU
  exact reveal_runMax hp m U j hx hU.2 hU.1

/-- **The paper's (dominate) as a set inclusion**, for every `n` and every pair `i != j`. -/
theorem dominate_set {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) {i j : Fin N} (hij : i ≠ j)
    (n : ℕ) :
    {U : Array N | 0 ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i < runMax p m U j n}
      ⊆ {U : Array N | omegaAt p m U j ((trajectory p m U n).pos i)
          ≤ rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)} := by
  intro U hU
  exact dominate hp m U hij n hU.1 hU.2

end

end Swarming.Trajectory


