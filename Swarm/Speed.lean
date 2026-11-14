/-
  Deterministic core of Proposition `ball` of
  *Swarming of interacting excited random walks* (main_1d_revised.tex), §2.2:
  the occupation-time estimate (occbnd)

      sum_{t<n} 1{0 <= X^i_t <= M^j_t}  <=  C M^i_n + eps n + o(n)

  implies a positive linear lower bound for `X^i_n`, and this bound is uniform in `N`.

  Everything here is a statement about two integer sequences `u`, `v` (the positions of
  walkers `i` and `j`) and their running maxima.  The occupation estimate itself — the
  martingale/submartingale part of the paper's proof, which needs the conditional
  expectation of the Poisson solution — is *not* proved here; it enters as hypothesis
  `hocc`.  What is proved here is the paper's covering argument: from the occupation
  estimate plus the complementarity `1{X^i_t <= M^j_t} + 1{X^j_t <= M^i_t} >= 1` one
  obtains `liminf X^i_n / n >= 7/(40 C)`, and hence `X^i_n -> +inf`.

  The constants are exactly the paper's: with `eps = 1/8` in (occbnd) one gets
  `M^i_n >= 7n/(40C) - O(1)` and finally `kappa = 7/(40C)` (the paper takes `1/(8C)`).
-/
import Swarm.Imports

open Finset Filter
open scoped BigOperators Topology

namespace SwarmSpeed

/-! ### Running maxima -/

/-- The running maximum `M_n = max_{t <= n} u_t` of a `ℤ`-valued path. -/
noncomputable def runMax (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ u

lemma le_runMax {u : ℕ → ℤ} {t n : ℕ} (ht : t ≤ n) : u t ≤ runMax u n :=
  Finset.le_sup' u (Finset.mem_range.mpr (by omega))

lemma runMax_le {u : ℕ → ℤ} {n : ℕ} {c : ℤ} (h : ∀ t ≤ n, u t ≤ c) : runMax u n ≤ c :=
  Finset.sup'_le _ u (fun t ht => h t (by simpa using ht))

lemma runMax_mono (u : ℕ → ℤ) : Monotone (runMax u) := by
  intro a b hab
  exact runMax_le fun t ht => le_runMax (le_trans ht hab)

/-! ### Occupation counts -/

/-- `occ a b n = #{t < n : a t <= b t}`, as a real number. -/
noncomputable def occ (a b : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, if a t ≤ b t then (1 : ℝ) else 0

lemma occ_nonneg (a b : ℕ → ℤ) (n : ℕ) : 0 ≤ occ a b n :=
  sum_nonneg fun t _ => by split_ifs <;> norm_num

lemma occ_mono (a b : ℕ → ℤ) : Monotone (occ a b) := by
  intro m n hmn
  unfold occ
  exact sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    (fun t _ _ => by split_ifs <;> norm_num)

/-- **Complementarity** (paper: `1{X^i_t <= M^j_t} + 1{X^j_t <= M^i_t} >= 1`): at every
time, walker `u` is at or below `v`'s running maximum, or `v` is at or below `u`'s. -/
lemma ind_compl_max (u v : ℕ → ℤ) (t : ℕ) :
    (1 : ℝ) ≤ (if u t ≤ runMax v t then 1 else 0) + (if v t ≤ runMax u t then 1 else 0) := by
  by_cases h : u t ≤ runMax v t
  · rw [if_pos h]; split_ifs <;> norm_num
  · have h1 : v t ≤ runMax v t := le_runMax le_rfl
    have h2 : v t < u t := lt_of_le_of_lt h1 (not_le.mp h)
    have h3 : v t ≤ runMax u t := le_trans h2.le (le_runMax le_rfl)
    rw [if_neg h, if_pos h3]; norm_num

/-- **Complementarity of the occupation counts**: `#{t<n : u_t <= M^v_t} +
#{t<n : v_t <= M^u_t} >= n`. -/
lemma occ_compl (u v : ℕ → ℤ) (n : ℕ) :
    (n : ℝ) ≤ occ u (runMax v) n + occ v (runMax u) n := by
  have hconst : ∑ t ∈ Finset.range n, (1 : ℝ) = (n : ℝ) := by simp
  have hsplit : ∑ t ∈ Finset.range n, ((if u t ≤ runMax v t then (1 : ℝ) else 0) +
      (if v t ≤ runMax u t then (1 : ℝ) else 0)) =
      occ u (runMax v) n + occ v (runMax u) n := by
    unfold occ
    rw [Finset.sum_add_distrib]
  rw [← hconst, ← hsplit]
  exact sum_le_sum fun t _ => ind_compl_max u v t

/-- If `u t <= v t` on the whole interval `[s, n)`, then `u` occupies `n - s` time steps
below `v` before time `n`. -/
lemma occ_tail {u v : ℕ → ℤ} {s n : ℕ} (hs : s ≤ n) (h : ∀ t, s ≤ t → t < n → u t ≤ v t) :
    (n - s : ℝ) ≤ occ u v n := by
  have hsub : Finset.Ico s n ⊆ Finset.range n := by
    intro t ht
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    omega
  have h2 : ∑ t ∈ Finset.Ico s n, (1 : ℝ) = (n - s : ℝ) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hs]
  have h1 : ∑ t ∈ Finset.Ico s n, (1 : ℝ) ≤
      ∑ t ∈ Finset.Ico s n, (if u t ≤ v t then (1 : ℝ) else 0) := by
    refine sum_le_sum fun t ht => ?_
    simp only [Finset.mem_Ico] at ht
    rw [if_pos (h t ht.1 ht.2)]
  have h3 : ∑ t ∈ Finset.Ico s n, (if u t ≤ v t then (1 : ℝ) else 0) ≤ occ u v n := by
    unfold occ
    refine sum_le_sum_of_subset_of_nonneg hsub ?_
    intro t _ _; split_ifs <;> norm_num
  linarith

/-! ### The covering argument -/

/-- **Positive lower speed from an occupation bound** (the deterministic content of
Proposition `ball`, with the paper's `eps = 1/8`): the occupation estimates for *both*
orderings of a pair of walkers, together with the complementarity
`1{u_t <= M^v_t} + 1{v_t <= M^u_t} >= 1`, force `M^u_n >= (7n/8 - (N+2))/(5C)`.

The slack `N + 2` (where `N` is the onset of the occupation estimates) is what allows one
to choose the auxiliary index `s = max N (ceil(4 C r) + 1)`, so that the paper's
covering step applies even when the running maximum `r = M^u_n` is small: one needs
`s >= N` for the estimates to be available and `s > 4 C r` for the joint maximum at time
`s` to exceed `r`. -/
theorem speed_lower_bound (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) {C : ℝ} (hC : 1 ≤ C) {N : ℕ}
    (hocc : ∀ n ≥ N, occ u (runMax v) n ≤ C * (runMax u n : ℝ) + (1 / 8) * n)
    (hocc' : ∀ n ≥ N, occ v (runMax u) n ≤ C * (runMax v n : ℝ) + (1 / 8) * n) :
    ∀ᶠ n in atTop, (7 / 8 : ℝ) * n - ((N : ℝ) + 2) ≤ 5 * C * (runMax u n : ℝ) := by
  have hCpos : (0 : ℝ) < C := by linarith
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  by_contra hcon
  push Not at hcon
  set r : ℝ := (runMax u n : ℝ) with hr
  have hrun : 0 ≤ r := by
    have h1 : u 0 ≤ runMax u n := le_runMax (Nat.zero_le n)
    have h2 : (u 0 : ℝ) ≤ (runMax u n : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast h0
    rw [hr]; linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rcases le_total ((n : ℝ)) (4 * C * r) with hbig | hsmall
  · -- `r >= n/(4C)`, which already gives the claim
    nlinarith [hcon, hbig, hnn, hCpos, hN0]
  · -- the covering step: pick an index `s` with `N <= s < n` and `4 C r < s`
    by_cases hceil : ⌈4 * C * r⌉₊ + 1 ≤ n
    · set s : ℕ := max N (⌈4 * C * r⌉₊ + 1) with hs
      have hsN : N ≤ s := le_max_left _ _
      have hslow : s ≤ n := max_le hn hceil
      have hceil1 : (⌈4 * C * r⌉₊ : ℝ) + 1 ≤ (s : ℝ) := by
        have h1 : ((⌈4 * C * r⌉₊ + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
          exact_mod_cast le_max_right N (⌈4 * C * r⌉₊ + 1)
        push_cast at h1 ⊢
        linarith
      have hsr : 4 * C * r < (s : ℝ) := by
        have h1 : 4 * C * r ≤ (⌈4 * C * r⌉₊ : ℝ) := Nat.le_ceil _
        linarith [hceil1]
      have hocc_s := hocc s hsN
      have hocc'_s := hocc' s hsN
      have hMu_s : (runMax u s : ℝ) ≤ r := by
        have h1 : (runMax u s : ℝ) ≤ (runMax u n : ℝ) := by exact_mod_cast runMax_mono u hslow
        rw [hr]; exact h1
      -- the joint maximum at time `s` exceeds `r`, hence walker `v` does
      have hMv : r < (runMax v s : ℝ) := by
        have hcompl : (s : ℝ) ≤ occ u (runMax v) s + occ v (runMax u) s := occ_compl u v s
        have hMu_s' : occ u (runMax v) s ≤ C * (runMax u s : ℝ) + (1 / 8) * s := hocc_s
        have hMv_s' : occ v (runMax u) s ≤ C * (runMax v s : ℝ) + (1 / 8) * s := hocc'_s
        nlinarith [hcompl, hMu_s', hMv_s', hMu_s, hsr, hCpos,
          mul_le_mul_of_nonneg_left hMu_s hCpos.le]
      have htail : (n - s : ℝ) ≤ occ u (runMax v) n := by
        refine occ_tail hslow (fun t hst htn => ?_)
        have h1 : u t ≤ runMax u t := le_runMax le_rfl
        have h2 : runMax u t ≤ runMax u n := runMax_mono u (le_of_lt htn)
        have h3 : runMax v s ≤ runMax v t := runMax_mono _ hst
        have h4 : (runMax v s : ℝ) ≤ (runMax v t : ℝ) := by exact_mod_cast h3
        have h5 : (u t : ℝ) ≤ r := by
          have h6 : (u t : ℝ) ≤ (runMax u n : ℝ) := by exact_mod_cast le_trans h1 h2
          rw [hr]; exact h6
        have h7 : (u t : ℝ) < (runMax v t : ℝ) := lt_of_le_of_lt h5 (lt_of_lt_of_le hMv h4)
        exact Int.le_of_lt (by exact_mod_cast h7)
      have hocc_n : occ u (runMax v) n ≤ C * r + (1 / 8) * n := by
        have h := hocc n hn
        rw [← hr] at h
        exact h
      -- `s <= N + 4 C r + 2`, and `(7/8) n <= C r + s`
      have hsupper : (s : ℝ) ≤ (N : ℝ) + 4 * C * r + 2 := by
        have h1 : (s : ℝ) ≤ max (N : ℝ) ((⌈4 * C * r⌉₊ : ℝ) + 1) := by
          rw [hs]
          simp [Nat.cast_max]
        have h2 : (⌈4 * C * r⌉₊ : ℝ) + 1 ≤ 4 * C * r + 2 := by
          have := Nat.ceil_lt_add_one (a := 4 * C * r) (by positivity)
          linarith
        have h3 : max (N : ℝ) ((⌈4 * C * r⌉₊ : ℝ) + 1) ≤ (N : ℝ) + 4 * C * r + 2 := by
          rw [max_le_iff]
          constructor
          · nlinarith [hsmall, hCpos, hrun]
          · linarith
        linarith
      nlinarith [htail, hocc_n, hsupper, hcon, hCpos]
    · -- `ceil (4 C r) >= n`, so `r` is already of order `n`
      push Not at hceil
      have h1 : (n : ℝ) < (⌈4 * C * r⌉₊ : ℝ) + 1 := by exact_mod_cast hceil
      have h2 : (⌈4 * C * r⌉₊ : ℝ) < 4 * C * r + 1 := Nat.ceil_lt_add_one (by positivity)
      nlinarith [hcon, h1, h2, hnn, hCpos, hN0]

/-! ### From the occupation bound to the paper's statements -/

/-- The running maximum is `o(n)`, so it can be replaced by the position itself. -/
theorem eventually_linear_speed (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) {C : ℝ} (hC : 1 ≤ C) {N : ℕ}
    (hocc : ∀ n ≥ N, occ u (runMax v) n ≤ C * (runMax u n : ℝ) + (1 / 8) * n)
    (hocc' : ∀ n ≥ N, occ v (runMax u) n ≤ C * (runMax v n : ℝ) + (1 / 8) * n)
    (hosc : Tendsto (fun n : ℕ => ((runMax u n : ℝ) - (u n : ℝ)) / n) atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (7 / (40 * C) - ε) * n ≤ (u n : ℝ) := by
  intro ε hε
  have hCpos : (0 : ℝ) < C := by linarith
  have hδ : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, ((runMax u n : ℝ) - (u n : ℝ)) ≤ δ * n := by
    intro δ hδ0
    have h2 : ∀ᶠ n : ℕ in atTop, ((runMax u n : ℝ) - (u n : ℝ)) / n < δ :=
      hosc.eventually (eventually_lt_nhds hδ0)
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    have hn1' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [div_lt_iff₀ hn1'] at hn
    linarith
  have hbound := speed_lower_bound u v h0 hC hocc hocc'
  have hhalf := hδ (ε / 2) (by linarith)
  have hthr : ∀ᶠ n : ℕ in atTop, 2 * ((N : ℝ) + 2) ≤ (5 * C * ε) * n := by
    have hpos : (0 : ℝ) < 5 * C * ε := by positivity
    have h6 : ∀ᶠ n : ℕ in atTop, 2 * ((N : ℝ) + 2) / (5 * C * ε) ≤ (n : ℝ) := by
      have h7 : ∀ᶠ n : ℕ in atTop, ⌈2 * ((N : ℝ) + 2) / (5 * C * ε)⌉₊ ≤ n :=
        eventually_ge_atTop _
      filter_upwards [h7] with n hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    filter_upwards [h6] with n hn
    rw [div_le_iff₀ hpos] at hn
    linarith
  filter_upwards [hbound, hhalf, hthr] with n hn3 hn4 hn5
  have hkey : 5 * C * (7 / (40 * C)) = 7 / 8 := by
    field_simp
    ring
  have hgoal : 5 * C * ((7 / (40 * C) - ε) * n) ≤ 5 * C * (u n : ℝ) := by
    nlinarith [hn3, hn4, hn5, hkey, hCpos]
  exact le_of_mul_le_mul_left hgoal (by positivity)

/-- **The paper's lower bound in Proposition `ball`**: `7/(40 C) <= liminf X^i_n/n`.
The upper bound `B` on `X^i_n/n` is the separate conclusion `limsup <= 2p-1` of the paper
(obtained there from the martingale (mart)); it is needed here only because `liminf` is
cobounded from above by definition. -/
theorem liminf_speed (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) {C B : ℝ} (hC : 1 ≤ C) {N : ℕ}
    (hocc : ∀ n ≥ N, occ u (runMax v) n ≤ C * (runMax u n : ℝ) + (1 / 8) * n)
    (hocc' : ∀ n ≥ N, occ v (runMax u) n ≤ C * (runMax v n : ℝ) + (1 / 8) * n)
    (hosc : Tendsto (fun n : ℕ => ((runMax u n : ℝ) - (u n : ℝ)) / n) atTop (nhds 0))
    (hup : ∀ᶠ n : ℕ in atTop, (u n : ℝ) / n ≤ B) :
    7 / (40 * C) ≤ liminf (fun n : ℕ => (u n : ℝ) / n) atTop := by
  have hCpos : (0 : ℝ) < C := by linarith
  have hcob : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop
      (fun n : ℕ => (u n : ℝ) / n) :=
    isCoboundedUnder_ge_of_eventually_le atTop hup
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have h := eventually_linear_speed u v h0 hC hocc hocc' hosc ε hε
  have h1 : 7 / (40 * C) - ε ≤
      liminf (fun n : ℕ => (u n : ℝ) / n) atTop := by
    refine le_liminf_of_le hcob ?_
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hn1' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [le_div_iff₀ hn1']
    linarith
  linarith

/-- **Transience to `+∞`** from a positive linear lower bound. -/
theorem tendsto_atTop_of_linear (u : ℕ → ℤ) {a : ℝ} (ha : 0 < a)
    (h : ∀ᶠ n : ℕ in atTop, a * n ≤ (u n : ℝ)) : Tendsto u atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have h1 : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
  have h2 : ∀ᶠ n : ℕ in atTop, (b : ℝ) ≤ a * (n : ℝ) :=
    eventually_atTop.mpr (tendsto_atTop_atTop.mp h1 (b : ℝ))
  exact eventually_atTop.mp (by
    filter_upwards [h, h2] with n hn hn2
    exact_mod_cast le_trans hn2 hn)


/-- **Proposition `ball`, quantitative form with the paper's `kappa`.**  The lower bound
`7/(40 C)` is strictly positive, so the paper's conclusion `exists kappa > 0` holds. -/
theorem exists_kappa_of_occupation (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) {C : ℝ} (hC : 1 ≤ C) {N : ℕ}
    (hocc : ∀ n ≥ N, occ u (runMax v) n ≤ C * (runMax u n : ℝ) + (1 / 8) * n)
    (hocc' : ∀ n ≥ N, occ v (runMax u) n ≤ C * (runMax v n : ℝ) + (1 / 8) * n)
    (hosc : Tendsto (fun n : ℕ => ((runMax u n : ℝ) - (u n : ℝ)) / n) atTop (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (κ - ε) * n ≤ (u n : ℝ) := by
  have hCpos : (0 : ℝ) < C := by linarith
  refine ⟨7 / (40 * C), by positivity, fun ε hε => ?_⟩
  have h := eventually_linear_speed u v h0 hC hocc hocc' hosc ε hε
  filter_upwards [h] with n hn
  linarith

/-- **Proposition `ball`, lower half**: the walker's position is eventually at least
`kappa * n` with `kappa = 7/(40C) > 0`, hence transient. -/
theorem transient_of_occupation (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) {C : ℝ} (hC : 1 ≤ C) {N : ℕ}
    (hocc : ∀ n ≥ N, occ u (runMax v) n ≤ C * (runMax u n : ℝ) + (1 / 8) * n)
    (hocc' : ∀ n ≥ N, occ v (runMax u) n ≤ C * (runMax v n : ℝ) + (1 / 8) * n)
    (hosc : Tendsto (fun n : ℕ => ((runMax u n : ℝ) - (u n : ℝ)) / n) atTop (nhds 0)) :
    Tendsto u atTop atTop := by
  have hCpos : (0 : ℝ) < C := by linarith
  refine tendsto_atTop_of_linear u (a := 7 / (80 * C)) (by positivity) ?_
  have h := eventually_linear_speed u v h0 hC hocc hocc' hosc (7 / (80 * C)) (by positivity)
  have h1 : 7 / (40 * C) - 7 / (80 * C) = 7 / (80 * C) := by
    field_simp
    ring
  filter_upwards [h] with n hn
  rwa [h1] at hn


end SwarmSpeed
