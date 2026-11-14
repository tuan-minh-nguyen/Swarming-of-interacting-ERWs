/-
  The last deterministic step of the occupation-time estimate `(occbnd)` of Proposition `ball`,
  and the `N`-independence of its coefficient.

  The paper's proof of `(occbnd)` produces, after summing the drift inequality `(Vdrift)`,

      sum_{t<n} 1{0 <= X^i_t <= M^j_t}
        <= eps n + (Z_n - Z_0) + sum_{t<n} J_{t+1} - Q_n,

  together with three separate almost-sure bounds: `(Jbound)` `sum |J_{t+1}| <= C M^i_n + O(1)`
  and `(Vbound)` `Z_n <= C M^i_n + o(n)`, and `Q_n = o(n)` from the martingale strong law.
  `occbnd_of_pieces` below performs exactly this final summation with explicit constants and
  with the `o(n)` terms replaced by an eventual `delta n` budget (which is all that `o(n)`
  means), and `occbnd_one_eighth` fixes the paper's `eps = 1/8` in the precise shape consumed
  by the verified covering argument `SwarmSpeed.speed_lower_bound`.

  `speed_from_occupation_pieces` composes the result with the already-verified
  `SwarmSpeed.exists_kappa_of_occupation`, so the whole remaining content of Proposition
  `ball` is reduced to the four *explicit* stochastic premises listed in
  `speed_from_occupation_pieces` (the drift inequality, and the `Z`, `J`, `Q` bounds).

  **N-independence.**  Nothing in this file mentions the walker count.  The coefficient
  produced is `2` in `2 * M^i_n` plus the fixed `1/8`, and the correction constant of `F_b`
  is `p^2/(eps (2p-1)^2 (1-p)^(2(m-1)))` (`Fcorr_abs_le_paper`), a function of `(m,p,eps)`
  only.  This is the `kappa`-independence point of the paper, made explicit.
-/
import Swarm.Imports
import Swarm.EnvCore
import Swarm.Fcorr
import Swarm.Speed

open Finset Filter
open scoped BigOperators Topology

namespace SwarmOcc

/-! ### The final summation of the occupation bound -/

/-- **`(occbnd)`, final step.**  From the summed drift inequality and the three eventual
bounds on `Z`, `J`, `Q` (each with a `delta n` slack instead of `o(n)`), the occupation count
satisfies

    Occ n <= 2 M_n + (eps + 3 delta) n + max 0 (-Z_0).

Nothing else is used: in particular no probability, no environment and no walker count. -/
theorem occbnd_of_pieces {Occ Z J Q M : ℕ → ℝ} {ε δ : ℝ} {N : ℕ}
    (hdrift : ∀ n, Occ n ≤ ε * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + δ * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + δ * n)
    (hQ : ∀ n ≥ N, -(δ * n) ≤ Q n) :
    ∀ n ≥ N, Occ n ≤ 2 * M n + (ε + 3 * δ) * n + max 0 (-(Z 0)) := by
  intro n hn
  have h1 := hdrift n
  have h2 := hZ n hn
  have h3 := hJ n hn
  have h4 := hQ n hn
  have h5 : -(Z 0) ≤ max 0 (-(Z 0)) := le_max_right _ _
  nlinarith

/-- **`(occbnd)` with the paper's `eps = 1/8` and an explicit slack budget.**
The drift inequality is run with `1/32` and each of the three `o(n)` terms is budgeted
`n/64`; the constant term `-Z_0` is absorbed once `n >= 32 max 0 (-Z_0)`.  The result is the
exact shape `Occ n <= 2 M_n + (1/8) n` consumed by `SwarmSpeed.speed_lower_bound`. -/
theorem occbnd_one_eighth {Occ Z J Q M : ℕ → ℝ} {N : ℕ}
    (hdrift : ∀ n, Occ n ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈32 * max 0 (-(Z 0))⌉₊, Occ n ≤ 2 * M n + (1 / 8) * n := by
  intro n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hc : max 0 (-(Z 0)) ≤ (n : ℝ) / 32 := by
    have h1 : (⌈32 * max 0 (-(Z 0))⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 : 32 * max 0 (-(Z 0)) ≤ (⌈32 * max 0 (-(Z 0))⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have h := occbnd_of_pieces (ε := 1 / 32) (δ := 1 / 64) hdrift hZ hJ hQ n hN
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **`(occbnd)` in the paper's own shape**, for the actual occupation count
`Occ n = #{t < n : X^i_t <= M^j_t}` of the verified module `Speed`. -/
theorem occbnd_paper (u v : ℕ → ℤ) {Z J Q : ℕ → ℝ} {N : ℕ}
    (hdrift : ∀ n, SwarmSpeed.occ u (SwarmSpeed.runMax v) n
      ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈32 * max 0 (-(Z 0))⌉₊,
      SwarmSpeed.occ u (SwarmSpeed.runMax v) n
        ≤ 2 * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * n :=
  occbnd_one_eighth hdrift hZ hJ hQ

/-! ### Composition with the verified covering argument -/

/-- **Proposition `ball` (lower half) from the four explicit stochastic premises.**
The premises are, for each ordering `(u,v)` of the pair of walkers:

* `hdrift`/`hdrift'` : the summed drift inequality `sum (Vdrift)` with the potential
  `Z = H_{j,·}(X^i_·) - F_{b_·}(X^i_· - M^j_·) + (sum of J) - (martingale Q)`;
* `hZ`/`hZ'` : the `(Vbound)` estimate `Z_n <= M^i_n + n/64` eventually;
* `hJ`/`hJ'` : the `(Jbound)` estimate for the record-cost sum;
* `hQ`/`hQ'` : the martingale strong law in the form `-n/64 <= Q_n`.

`hosc` is the oscillation statement `max(M-X) = o(n)` (paper `(prelim)`).  The conclusion is
the paper's quantitative lower bound `kappa = 7/(80)` for the coefficient `C = 2`. -/
theorem speed_from_occupation_pieces (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) (h0' : 0 ≤ v 0)
    {Z J Q Z' J' Q' : ℕ → ℝ} {N N' : ℕ}
    (hdrift : ∀ n, SwarmSpeed.occ u (SwarmSpeed.runMax v) n
      ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n)
    (hdrift' : ∀ n, SwarmSpeed.occ v (SwarmSpeed.runMax u) n
      ≤ (1 / 32) * n + (Z' n - Z' 0) + J' n - Q' n)
    (hZ' : ∀ n ≥ N', Z' n ≤ (SwarmSpeed.runMax v n : ℝ) + (1 / 64) * n)
    (hJ' : ∀ n ≥ N', J' n ≤ (SwarmSpeed.runMax v n : ℝ) + (1 / 64) * n)
    (hQ' : ∀ n ≥ N', -((1 / 64) * n) ≤ Q' n)
    (hosc : Tendsto (fun n : ℕ => ((SwarmSpeed.runMax u n : ℝ) - (u n : ℝ)) / n)
      atTop (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (κ - ε) * n ≤ (u n : ℝ) := by
  set N₁ := max N ⌈32 * max 0 (-(Z 0))⌉₊ with hN₁
  set N₂ := max N' ⌈32 * max 0 (-(Z' 0))⌉₊ with hN₂
  have hocc : ∀ n ≥ N₁, SwarmSpeed.occ u (SwarmSpeed.runMax v) n
      ≤ 2 * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * n :=
    occbnd_one_eighth hdrift hZ hJ hQ
  have hocc' : ∀ n ≥ N₂, SwarmSpeed.occ v (SwarmSpeed.runMax u) n
      ≤ 2 * (SwarmSpeed.runMax v n : ℝ) + (1 / 8) * n :=
    occbnd_one_eighth hdrift' hZ' hJ' hQ'
  -- unify the two onsets
  exact SwarmSpeed.exists_kappa_of_occupation (u := u) (v := v) (h0 := h0) (C := 2)
    (hC := by norm_num) (N := max N₁ N₂)
    (hocc := fun n hn => hocc n (le_trans (le_max_left _ _) hn))
    (hocc' := fun n hn => hocc' n (le_trans (le_max_right _ _) hn))
    (hosc := hosc)

/-! ### The `N`-free correction constant in the paper's parameters -/

/-- **The correction constant of `F_b` for the paper's parameters.**
With `a = aConst p ((1-p)^{m-1}) = 1 - (2p-1)(1-p)^{m-1}/p` one has `1 - a = (2p-1)q/p`
with `q = (1-p)^{m-1}`, so the bound `|F_b| <= b^2/(eps (1-a)^2)` of `Fcorr_abs_le` reads

    |F_b(g)| <= b^2 p^2 / (eps (2p-1)^2 q^2),

a function of `(m,p,eps)` only — in particular independent of the number of walkers `N`. -/
theorem Fcorr_abs_le_paper {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    {ε b : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (g : ℤ) :
    |Fcorr (ExcitedEnv.aConst p ((1 - p) ^ (m - 1))) ε b g|
      ≤ b ^ 2 * p ^ 2 / (ε * (2 * p - 1) ^ 2 * ((1 - p) ^ (m - 1)) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hq0 : (0 : ℝ) < (1 - p) ^ (m - 1) := pow_pos h1p _
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 / 2 := ExcitedEnv.q_le_half hp1 hp2 hm
  have hbnds := ExcitedEnv.aConst_bounds hp1 hp2 hq0 hq1
  have ha0 : 0 ≤ ExcitedEnv.aConst p ((1 - p) ^ (m - 1)) := by linarith [hbnds.1]
  have ha1 : ExcitedEnv.aConst p ((1 - p) ^ (m - 1)) < 1 := hbnds.2.1
  have hmain := Fcorr_abs_le ha0 ha1 hb hε g
  refine le_trans hmain ?_
  have hone : (1 : ℝ) - ExcitedEnv.aConst p ((1 - p) ^ (m - 1))
      = (2 * p - 1) * ((1 - p) ^ (m - 1)) / p := by
    unfold ExcitedEnv.aConst
    ring
  have h2p : (2 * p - 1) ≠ 0 := by
    intro h; linarith [show (2 * p - 1) = 0 from h]
  have hq : (1 - p) ^ (m - 1) ≠ 0 := ne_of_gt hq0
  rw [hone]
  field_simp
  exact le_rfl


/-! ### Summing the drift inequality: from `(Vdrift)` to `(hdrift)` -/

/-- The paper's occupation indicator `1{0 <= X_t <= r_t}` as a real number. -/
noncomputable def occInd (X r : ℕ → ℤ) (t : ℕ) : ℝ := if 0 ≤ X t ∧ X t ≤ r t then 1 else 0

lemma occInd_nonneg (X r : ℕ → ℤ) (t : ℕ) : 0 ≤ occInd X r t := by
  unfold occInd; split_ifs <;> norm_num

/-- The two-sided occupation count of the paper is dominated by the one-sided count used in
the verified covering argument `SwarmSpeed.occ`. -/
theorem sum_occInd_le_occ (X r : ℕ → ℤ) (n : ℕ) :
    ∑ t ∈ Finset.range n, occInd X r t ≤ SwarmSpeed.occ X r n := by
  unfold occInd SwarmSpeed.occ
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases h : 0 ≤ X t ∧ X t ≤ r t
  · rw [if_pos h, if_pos h.2]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- **Summing `(Vdrift)`.**  If each one-step drift `E_t` dominates `1{0 <= X_t <= r_t} - eps`,
and `Q` is *defined* as the compensator
`Q_n = Z_n - Z_0 + sum_{t<n} J_{t+1} - sum_{t<n} E_t`, then

    sum_{t<n} 1{0 <= X_t <= r_t} <= eps n + (Z_n - Z_0) + sum_{t<n} J_{t+1} - Q_n,

which is hypothesis `hdrift` of `occbnd_of_pieces`.  (In the paper `E_t` is the conditional
expectation of `Z_{t+1} - Z_t + J_{t+1}` and `Q` is the resulting martingale; the passage to
`condExp` and the strong law `Q_n/n -> 0` are the stochastic layer, not asserted here.) -/
theorem sum_drift_bound {Z E J Q : ℕ → ℝ} {ε : ℝ} {ind : ℕ → ℝ}
    (hE : ∀ t, ind t - ε ≤ E t)
    (hQ : ∀ n, Q n = Z n - Z 0 + (∑ t ∈ Finset.range n, J (t + 1))
      - (∑ t ∈ Finset.range n, E t))
    (n : ℕ) :
    ∑ t ∈ Finset.range n, ind t
      ≤ ε * n + (Z n - Z 0) + (∑ t ∈ Finset.range n, J (t + 1)) - Q n := by
  have h1 : ∑ t ∈ Finset.range n, ind t ≤ ∑ t ∈ Finset.range n, (E t + ε) :=
    Finset.sum_le_sum fun t _ => by linarith [hE t]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 := hQ n
  linarith

end SwarmOcc
