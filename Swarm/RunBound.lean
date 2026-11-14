/-
# A non-asymptotic maximum bound for the site potentials from the absence of long
# unmarked runs

The paper's `(locmax)` display bounds `max_j max{h^*_j(x), G_j(x)}` on a spatial window.  In the
Lean development this is obtained from exponential moments (`WideRepair.array_locmax_hG_wide*`),
and its probabilistic content is an unconditional bound for a *fixed* window.  Two properties are
left implicit there:

* `SwarmMarks.Gsup` is the *real* supremum `⨆ N, Gtrunc p ω N (x+1)`, so at a mark row whose
  truncations are unbounded the junk value `0` is returned and `Gsup ≤ H` carries **no**
  information.  The bound `Gtail ≤ 1 + Gsup` therefore needs `BddAbove (range (Gtrunc …))` as an
  extra hypothesis (`SiteWindow.goodWWin_of_locmax_event`), and that hypothesis is not supplied
  by any accepted probabilistic statement with an explicit rate.
* the quantitative relation between the threshold and the failure probability is proved through
  exponential moments and a polynomial absorption, so the *shape* of the event (which marks are
  bad) is opaque.

This file supplies a completely explicit carrier built from one combinatorial event, the absence
of a run of `K` consecutive unmarked sites.  On that event, **all** potentials are bounded
explicitly and all truncation series are provably bounded above, and the event has the explicit
probability `1 - N·b·(1-q)^K` where `q = (1-p)^(m-1)` is the paper's mark probability.

Main results:

* `SwarmRun.runsOK_cnt` — a stretch of `L` sites inside `[0,b)` contains at least `L/K` marked
  sites;
* `SwarmRun.hof_le_of_runs` — `h_j(x) ≤ 1 + 2K + 2K/(1-ρ)` for **every** `x < b`;
* `SwarmRun.Gtrunc_le_of_runs` — `G_N(x) ≤ 1 + K/(1-ρ)` for **every** `N`, `x` with `x+N ≤ b`;
* `SwarmRun.bddAbove_Gtrunc_of_runs` — hence `BddAbove (range (Gtrunc p ω N (x+1)))` for
  **every** `x < b`: the `BddAbove` hypothesis is discharged, not assumed;
* `SwarmRun.measure_not_runsOK_le` / `..._N` — the failure probability `≤ b·(1-q)^K` per row and
  `≤ N·b·(1-q)^K` for `N` rows.

No `sorry`, no extra axiom, no `native_decide`.
-/
import Swarm.MarkG
import Swarm.MarkN
import Swarm.MarkFuture

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SwarmMarks

namespace SwarmRun

noncomputable section

variable {p : ℝ}

/-! ### 1. The mark counter and the run predicate -/

/-- Number of marked sites among `y, y+1, …, y+L-1`. -/
def cnt (ω : ℕ → Bool) (y L : ℕ) : ℕ :=
  ∑ u ∈ Finset.range L, if ω (y + u) = true then 1 else 0

/-- **No long unmarked run.**  Every block of `K` consecutive sites inside `[0,b)` contains a
marked site. -/
def RunsOK (ω : ℕ → Bool) (b K : ℕ) : Prop :=
  ∀ y : ℕ, y + K ≤ b → ∃ z ∈ Finset.Ico y (y + K), ω z = true

@[simp] lemma cnt_zero (ω : ℕ → Bool) (y : ℕ) : cnt ω y 0 = 0 := by
  simp [cnt]

lemma cnt_succ (ω : ℕ → Bool) (y L : ℕ) :
    cnt ω y (L + 1) = cnt ω y L + (if ω (y + L) = true then 1 else 0) := by
  rw [cnt, Finset.sum_range_succ]
  rfl

lemma cnt_mono {ω : ℕ → Bool} {y L L' : ℕ} (h : L ≤ L') : cnt ω y L ≤ cnt ω y L' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) ?_
  intro u _ _
  split <;> omega

lemma cnt_split (ω : ℕ → Bool) (y M N : ℕ) :
    cnt ω y (M + N) = cnt ω y M + cnt ω (y + M) N := by
  rw [cnt, cnt, cnt, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show y + (M + u) = y + M + u from by omega]

lemma one_le_cnt_of_true {ω : ℕ → Bool} {y K z : ℕ} (hz : z ∈ Finset.Ico y (y + K))
    (h : ω z = true) : 1 ≤ cnt ω y K := by
  obtain ⟨hz1, hz2⟩ := Finset.mem_Ico.mp hz
  have hmem : z - y ∈ Finset.range K := Finset.mem_range.mpr (by omega)
  have hterm : (if ω (y + (z - y)) = true then 1 else 0) = 1 := by
    rw [Nat.add_sub_cancel' hz1, h]; simp
  calc 1 = (if ω (y + (z - y)) = true then 1 else 0) := hterm.symm
    _ ≤ ∑ u ∈ Finset.range K, (if ω (y + u) = true then 1 else 0) :=
        Finset.single_le_sum (f := fun u => if ω (y + u) = true then 1 else 0)
          (fun u _ => by split <;> omega) hmem
    _ = cnt ω y K := rfl

/-- **The combinatorial core of `RunsOK`**: a stretch of `L` sites inside `[0,b)` contains at
least `L / K` marked sites. -/
theorem runsOK_cnt {ω : ℕ → Bool} {b K : ℕ} (h : RunsOK ω b K) (hK : 1 ≤ K) {y L : ℕ}
    (hyL : y + L ≤ b) : L / K ≤ cnt ω y L := by
  have hblock : ∀ t : ℕ, t ≤ L / K → t ≤ cnt ω y (t * K) := by
    intro t ht
    induction t with
    | zero => simp
    | succ s ih =>
        have hs : s ≤ L / K := le_trans (Nat.le_succ s) ht
        have hih := ih hs
        have hle : (s + 1) * K ≤ L :=
          (Nat.le_div_iff_mul_le (by omega : 0 < K)).mp ht
        have hle' : s * K + K ≤ L := by rw [← Nat.succ_mul]; exact hle
        have hrun : 1 ≤ cnt ω (y + s * K) K := by
          have hb : y + s * K + K ≤ b := by omega
          obtain ⟨z, hz, hztrue⟩ := h (y + s * K) hb
          exact one_le_cnt_of_true hz hztrue
        rw [Nat.succ_mul, cnt_split]
        omega
  have hmono : cnt ω y (L / K * K) ≤ cnt ω y L := cnt_mono (Nat.div_mul_le_self L K)
  have := hblock (L / K) le_rfl
  omega

/-! ### 2. The trailing unmarked run and the `h` bound -/

/-- Length of the maximal run of unmarked sites ending at `n`. -/
def trail (ω : ℕ → Bool) : ℕ → ℕ
  | 0 => if ω 0 = true then 0 else 1
  | n + 1 => if ω (n + 1) = true then 0 else trail ω n + 1

@[simp] lemma trail_zero (ω : ℕ → Bool) : trail ω 0 = if ω 0 = true then 0 else 1 := rfl

@[simp] lemma trail_succ (ω : ℕ → Bool) (n : ℕ) :
    trail ω (n + 1) = if ω (n + 1) = true then 0 else trail ω n + 1 := rfl

lemma false_of_not_true {b : Bool} (h : ¬ (b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

lemma trail_le_succ (ω : ℕ → Bool) : ∀ n : ℕ, trail ω n ≤ n + 1 := by
  intro n
  induction n with
  | zero => rw [trail_zero]; split <;> omega
  | succ n ih => rw [trail_succ]; split <;> omega

/-- The trailing run consists of unmarked sites. -/
lemma trail_spec (ω : ℕ → Bool) : ∀ (n j : ℕ), j < trail ω n → ω (n - j) = false := by
  intro n
  induction n with
  | zero =>
      intro j hj
      by_cases h : ω 0 = true
      · rw [trail_zero, if_pos h] at hj; omega
      · have hf : ω 0 = false := false_of_not_true h
        rw [trail_zero, if_neg h] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        simpa using hf
  | succ n ih =>
      intro j hj
      by_cases h : ω (n + 1) = true
      · rw [trail_succ, if_pos h] at hj; omega
      · have hf : ω (n + 1) = false := false_of_not_true h
        rw [trail_succ, if_neg h] at hj
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0; simpa using hf
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
          have hj' : j' < trail ω n := by omega
          have := ih j' hj'
          rwa [show n + 1 - (j' + 1) = n - j' from by omega]

/-- Under `RunsOK`, the trailing unmarked run has length at most `K-1`. -/
lemma trail_le {ω : ℕ → Bool} {b K : ℕ} (h : RunsOK ω b K) (hK : 1 ≤ K) {n : ℕ}
    (hn : n + 1 ≤ b) : trail ω n ≤ K - 1 := by
  by_contra hlt
  push_neg at hlt
  have hKle : K ≤ trail ω n := by omega
  have hKn : K ≤ n + 1 := le_trans hKle (trail_le_succ ω n)
  have hb : (n + 1 - K) + K ≤ b := by omega
  obtain ⟨z, hz, hztrue⟩ := h (n + 1 - K) hb
  obtain ⟨hz1, hz2⟩ := Finset.mem_Ico.mp hz
  have hzle : z ≤ n := by omega
  have hj : n - z < K := by omega
  have := trail_spec ω n (n - z) (lt_of_lt_of_le hj hKle)
  have hsub : n - (n - z) = z := by omega
  rw [hsub] at this
  rw [this] at hztrue
  exact Bool.noConfusion hztrue

/-- **The `h` bound on the no-long-run event.**  For `p > 1/2` and `ρ = (1-p)/p`, every site
below `b` has `h_j(x) ≤ 1 + 2K + 2K/(1-ρ)`. -/
theorem hof_le_of_runs {ω : ℕ → Bool} {b K : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hK : 1 ≤ K) (h : RunsOK ω b K) {n : ℕ} (hn : n + 1 ≤ b) :
    hof p ω n ≤ 1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p)) := by
  have hp0 : p ≠ 0 := by linarith
  set c : ℝ := (1 - p) / p with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by
    rw [hc, div_lt_one (by linarith)]; linarith
  have hden : 0 < 1 - c := by linarith
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  set A : ℝ := (K : ℝ) / (1 - c) with hA
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hden]; nlinarith
  have hcA : c ≤ A := le_trans (le_of_lt hc1) hA1
  have hAK : A * (1 - c) = (K : ℝ) := by rw [hA]; field_simp
  set S : ℝ := 2 * A with hS
  have hSnn : 0 ≤ S := by rw [hS]; nlinarith
  have hSK : S * (1 - c) = 2 * (K : ℝ) := by rw [hS]; nlinarith
  have hinv : ∀ m : ℕ, m ≤ n → hof p ω m ≤ 1 + S + 2 * (trail ω m : ℝ) := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [hof_zero, trail_zero]
        have hstep : hstep p (ω 0) 1 = 1 + rhoOf p (ω 0) * 2 := by
          rw [hstep_eq_rho hp0]; ring
        rw [hstep]
        by_cases hb : ω 0 = true
        · rw [if_pos hb, hb, rhoOf_true, ← hc]
          have : c * 2 ≤ S := by rw [hS]; nlinarith
          push_cast
          linarith
        · rw [if_neg hb]
          have hr : rhoOf p (ω 0) = 1 := by
            rw [false_of_not_true hb, rhoOf_false]
          rw [hr]
          push_cast
          linarith [hSnn]
    | succ m ih =>
        intro hmn
        have hmb : m + 1 ≤ b := by omega
        have htr : trail ω m + 1 ≤ K := by
          have h1 := trail_le h hK (n := m) (by omega)
          omega
        have htrR : ((trail ω m : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast htr
        rw [hof_succ, hstep_eq_rho hp0, trail_succ]
        by_cases hb : ω (m + 1) = true
        · rw [if_pos hb, hb, rhoOf_true, ← hc]
          have h1 : 1 + hof p ω m ≤ 2 + S + 2 * (trail ω m : ℝ) := by
            have := ih (by omega); linarith
          have h2 : c * (1 + hof p ω m) ≤ c * (2 + S + 2 * (trail ω m : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hc0
          have h3 : c * (2 + 2 * (trail ω m : ℝ)) ≤ 2 * (K : ℝ) := by
            have h4 : c * (((trail ω m : ℕ) : ℝ) + 1) ≤ 1 * (K : ℝ) :=
              mul_le_mul hc1.le htrR (by positivity) (by norm_num)
            nlinarith
          have h5 : c * (2 + S + 2 * (trail ω m : ℝ)) ≤ S := by nlinarith [hSK]
          push_cast
          linarith
        · rw [if_neg hb]
          have hr : rhoOf p (ω (m + 1)) = 1 := by
            rw [false_of_not_true hb, rhoOf_false]
          rw [hr, one_mul]
          push_cast
          have := ih (by omega)
          linarith
  calc hof p ω n ≤ 1 + S + 2 * (trail ω n : ℝ) := hinv n le_rfl
    _ ≤ 1 + S + 2 * (K : ℝ) := by
        have htr := trail_le h hK hn
        have : ((trail ω n : ℕ) : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast le_trans htr (by omega)
        linarith
    _ = 1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p)) := by
        rw [hS, hA, hc]; ring

/-! ### 4. The geometric bound -/

lemma geom_partial {c : ℝ} (T : ℕ) :
    (∑ t ∈ Finset.range T, c ^ t) * (1 - c) = 1 - c ^ T := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

lemma sum_pow_div_eq {c : ℝ} (K T : ℕ) :
    ∑ q ∈ Finset.range (K * T), c ^ (q / K) = (K : ℝ) * ∑ t ∈ Finset.range T, c ^ t := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have h1 : ∀ x ∈ Finset.range K, c ^ ((K * T + x) / K) = c ^ T := by
        intro x hx
        rw [Finset.mem_range] at hx
        have hdiv : (K * T + x) / K = T := by
          rw [Nat.div_eq_of_lt_le (k := T) (n := K) (m := K * T + x)]
          · rw [Nat.mul_comm T K]; omega
          · have : (T + 1) * K = K * T + K := by ring
            omega
        rw [hdiv]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_range_succ]
      ring

lemma sum_pow_div_le {c : ℝ} {K : ℕ} (hK : 1 ≤ K) (hc0 : 0 ≤ c) (hc1 : c < 1) (N : ℕ) :
    ∑ q ∈ Finset.range N, c ^ (q / K) ≤ (K : ℝ) / (1 - c) := by
  have hden : 0 < 1 - c := by linarith
  have hNK : N ≤ K * (N / K + 1) := by
    have h1 : K * (N / K) + N % K = N := Nat.div_add_mod N K
    have h2 : N % K < K := Nat.mod_lt N (by omega)
    have h3 : K * (N / K + 1) = K * (N / K) + K := by ring
    omega
  have hmono : ∑ q ∈ Finset.range N, c ^ (q / K)
      ≤ ∑ q ∈ Finset.range (K * (N / K + 1)), c ^ (q / K) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNK) ?_
    intro i _ _
    positivity
  have hgeom : ∑ t ∈ Finset.range (N / K + 1), c ^ t ≤ 1 / (1 - c) := by
    rw [le_div_iff₀ hden]
    have := geom_partial (c := c) (N / K + 1)
    have h2 : 0 ≤ c ^ (N / K + 1) := by positivity
    nlinarith
  calc ∑ q ∈ Finset.range N, c ^ (q / K)
      ≤ ∑ q ∈ Finset.range (K * (N / K + 1)), c ^ (q / K) := hmono
    _ = (K : ℝ) * ∑ t ∈ Finset.range (N / K + 1), c ^ t := sum_pow_div_eq K (N / K + 1)
    _ ≤ (K : ℝ) * (1 / (1 - c)) := by
        apply mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (K : ℝ) / (1 - c) := by ring

/-! ### 3. Products of mark ratios and the forward potential `G` -/

/-- A product of `L` consecutive ratios is at most `ρ` raised to the number of marked sites. -/
lemma prod_rho_le {ω : ℕ → Bool} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (y L : ℕ) :
    ∏ u ∈ Finset.range L, rhoOf p (ω (y + u)) ≤ ((1 - p) / p) ^ (cnt ω y L) := by
  induction L generalizing y with
  | zero => simp
  | succ L ih =>
      have hstep : ((1 - p) / p) ^ (cnt ω y (L + 1))
          = ((1 - p) / p) ^ (cnt ω y L) * rhoOf p (ω (y + L)) := by
        rw [cnt_succ]
        by_cases h : ω (y + L) = true
        · rw [if_pos h, h, rhoOf_true, pow_succ]
        · have hf : ω (y + L) = false := false_of_not_true h
          rw [if_neg h, hf, rhoOf_false, Nat.add_zero, mul_one]
      rw [Finset.prod_range_succ, hstep]
      exact mul_le_mul_of_nonneg_right (ih y) (rhoOf_nonneg hp1 hp2 _)

/-- The truncated forward potential as a sum of products, `G_N(x) = 1 + Σ_{l<N} ∏_{u≤l} ρ(x+u)`. -/
lemma Gtrunc_eq_sum (p : ℝ) (ω : ℕ → Bool) :
    ∀ (N x : ℕ), Gtrunc p ω N x
      = 1 + ∑ l ∈ Finset.range N, ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u)) := by
  intro N
  induction N with
  | zero => intro x; simp [Gtrunc]
  | succ n ih =>
      intro x
      have hprod : ∀ l : ℕ, rhoOf p (ω x) * (∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + 1 + u)))
          = ∏ u ∈ Finset.range (l + 2), rhoOf p (ω (x + u)) := by
        intro l
        rw [Finset.prod_range_succ' (f := fun u => rhoOf p (ω (x + u))) (n := l + 1)]
        rw [mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [show x + (u + 1) = x + 1 + u from by omega]
      rw [Gtrunc_succ, ih (x + 1), mul_add, mul_one, Finset.mul_sum,
        Finset.sum_range_succ' (f := fun l => ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u)))
          (n := n)]
      rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range n) => (hprod l).symm)]
      have h1 : (∏ u ∈ Finset.range (0 + 1), rhoOf p (ω (x + u))) = rhoOf p (ω x) := by
        simp
      rw [h1]
      ring

/-- **The `G` bound on the no-long-run event.** -/
theorem Gtrunc_le_of_runs {ω : ℕ → Bool} {b K : ℕ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (hK : 1 ≤ K) (h : RunsOK ω b K) {N x : ℕ} (hxN : x + N ≤ b) :
    Gtrunc p ω N x ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by
  rw [Gtrunc_eq_sum]
  have hc0 : (0 : ℝ) ≤ (1 - p) / p := by positivity
  have hc1 : (1 - p) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hterm : ∀ l ∈ Finset.range N,
      ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u)) ≤ ((1 - p) / p) ^ ((l + 1) / K) := by
    intro l hl
    rw [Finset.mem_range] at hl
    refine le_trans (prod_rho_le hp1 hp2 x (l + 1)) (pow_le_pow_of_le_one hc0 hc1.le ?_)
    exact runsOK_cnt h hK (y := x) (L := l + 1) (by omega)
  have hsum : ∑ l ∈ Finset.range N, ((1 - p) / p) ^ ((l + 1) / K)
      ≤ ∑ q ∈ Finset.range (N + 1), ((1 - p) / p) ^ (q / K) := by
    rw [Finset.sum_range_succ' (f := fun q => ((1 - p) / p) ^ (q / K)) (n := N)]
    have h0 : (0 : ℝ) ≤ ((1 - p) / p) ^ ((0 : ℕ) / K) := by positivity
    linarith
  have hgeo := sum_pow_div_le (c := (1 - p) / p) (K := K) hK hc0 hc1 (N + 1)
  calc 1 + ∑ l ∈ Finset.range N, ∏ u ∈ Finset.range (l + 1), rhoOf p (ω (x + u))
      ≤ 1 + ∑ l ∈ Finset.range N, ((1 - p) / p) ^ ((l + 1) / K) := by
        have := Finset.sum_le_sum hterm
        linarith
    _ ≤ 1 + ∑ q ∈ Finset.range (N + 1), ((1 - p) / p) ^ (q / K) := by linarith
    _ ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) := by linarith


/-! ### 5. The probability of the carrier -/

lemma markMeasure_eval {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : ℕ) {A : Set Bool}
    (hA : MeasurableSet A) :
    (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ω i ∈ A} = (boolMeasure q) A := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hmap : Measure.map (fun ω : ℕ → Bool => ω i) (markMeasure (boolMeasure q))
      = boolMeasure q := Measure.infinitePi_map_eval (fun _ => boolMeasure q) i
  calc (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ω i ∈ A}
      = (Measure.map (fun ω : ℕ → Bool => ω i) (markMeasure (boolMeasure q))) A :=
        (Measure.map_apply (measurable_pi_apply i) hA).symm
    _ = (boolMeasure q) A := by rw [hmap]

lemma markMeasure_cyl_false {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (y K : ℕ) :
    (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false}
      = ENNReal.ofReal ((1 - q) ^ K) := by
  haveI hprob : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hInd : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) (markMeasure (boolMeasure q)) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd) (Finset.Ico y (y + K))
    (sets := fun _ => {false}) (fun _ _ => measurableSet_singleton false)
  have hset : {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false}
      = ⋂ i ∈ Finset.Ico y (y + K), (fun (ω : ℕ → Bool) => ω i) ⁻¹' {false} := by
    ext ω
    simp
  rw [hset, h]
  have hval : ∀ i ∈ Finset.Ico y (y + K),
      (markMeasure (boolMeasure q)) ((fun (ω : ℕ → Bool) => ω i) ⁻¹' {false})
        = ENNReal.ofReal (1 - q) := by
    intro i _
    have h1 : (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ω i ∈ ({false} : Set Bool)}
        = (boolMeasure q) ({false} : Set Bool) :=
      markMeasure_eval hq0 hq1 i (A := {false}) (measurableSet_singleton false)
    rw [boolMeasure_false] at h1
    exact h1
  rw [Finset.prod_congr rfl hval, Finset.prod_const]
  have hcard : (Finset.Ico y (y + K)).card = K := by
    rw [Nat.card_Ico]; omega
  rw [hcard, ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - q)]

lemma markMeasureN_row_cyl_false {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M : ℕ) (j : Fin M)
    (y K : ℕ) :
    (markMeasureN M (boolMeasure q))
        {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false}
      = ENNReal.ofReal ((1 - q) ^ K) := by
  haveI : IsProbabilityMeasure (boolMeasure q) := isProbabilityMeasure_boolMeasure hq0 hq1
  have hmp := markMeasureN_marginal (μB := boolMeasure q) M j
  have hset : MeasurableSet {ξ : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ξ z = false} := by
    have heq : {ξ : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ξ z = false}
        = ⋂ z ∈ Finset.Ico y (y + K), {ξ : ℕ → Bool | ξ z = false} := by
      ext ξ
      simp
    rw [heq]
    exact Finset.measurableSet_biInter _
      (fun z _ => measurableSet_eq_fun (measurable_pi_apply z) measurable_const)
  calc (markMeasureN M (boolMeasure q))
        {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false}
      = (markMeasure (boolMeasure q)) {ξ : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ξ z = false} := by
        rw [← hmp.map_eq, Measure.map_apply hmp.measurable hset]
        rfl
    _ = ENNReal.ofReal ((1 - q) ^ K) := markMeasure_cyl_false hq0 hq1 y K

/-- **The failure probability of one row is at most `b·(1-q)^K`.** -/
theorem measure_not_runsOK_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b K : ℕ) (hK : 1 ≤ K) :
    (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ¬ RunsOK ω b K}
      ≤ ENNReal.ofReal ((b : ℝ) * (1 - q) ^ K) := by
  have hsub : {ω : ℕ → Bool | ¬ RunsOK ω b K}
      ⊆ ⋃ y ∈ Finset.range b, {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false} := by
    intro ω hω
    simp only [RunsOK, not_forall] at hω
    obtain ⟨y, hyb, hy⟩ := hω
    simp only [not_exists, not_and] at hy
    exact Set.mem_biUnion (Finset.mem_range.mpr (by omega))
      (fun z hz => false_of_not_true (hy z hz))
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le (Finset.range b)
    (fun y => {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false})) ?_
  have heq : ∑ y ∈ Finset.range b,
      (markMeasure (boolMeasure q)) {ω : ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω z = false}
      = ENNReal.ofReal ((b : ℝ) * (1 - q) ^ K) := by
    rw [Finset.sum_congr rfl (fun y _ => markMeasure_cyl_false hq0 hq1 y K),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast b, ← ENNReal.ofReal_mul (by positivity)]
  rw [heq]

/-- **The failure probability for `M` rows is at most `M·b·(1-q)^K`.** -/
theorem measure_not_runsOK_le_N {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (M b K : ℕ) (hK : 1 ≤ K) :
    (markMeasureN M (boolMeasure q)) {ω : Fin M → ℕ → Bool | ∃ j : Fin M, ¬ RunsOK (ω j) b K}
      ≤ ENNReal.ofReal ((M : ℝ) * ((b : ℝ) * (1 - q) ^ K)) := by
  have hsub : {ω : Fin M → ℕ → Bool | ∃ j : Fin M, ¬ RunsOK (ω j) b K}
      ⊆ ⋃ j ∈ Finset.univ, ⋃ y ∈ Finset.range b,
          {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false} := by
    intro ω hω
    obtain ⟨j, hj⟩ := hω
    simp only [RunsOK, not_forall] at hj
    obtain ⟨y, hyb, hy⟩ := hj
    simp only [not_exists, not_and] at hy
    exact Set.mem_biUnion (Finset.mem_univ j) (Set.mem_biUnion
      (Finset.mem_range.mpr (by omega)) (fun z hz => false_of_not_true (hy z hz)))
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le Finset.univ
    (fun j => ⋃ y ∈ Finset.range b,
      {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false})) ?_
  refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    measure_biUnion_finset_le (Finset.range b)
      (fun y => {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false}))) ?_
  have hterm : ∀ j : Fin M, ∑ y ∈ Finset.range b,
      (markMeasureN M (boolMeasure q))
        {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false}
      = ENNReal.ofReal ((b : ℝ) * (1 - q) ^ K) := by
    intro j
    rw [Finset.sum_congr rfl (fun y _ => markMeasureN_row_cyl_false hq0 hq1 M j y K),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast b, ← ENNReal.ofReal_mul (by positivity)]
  have heq : ∑ j ∈ (Finset.univ : Finset (Fin M)), ∑ y ∈ Finset.range b,
      (markMeasureN M (boolMeasure q))
        {ω : Fin M → ℕ → Bool | ∀ z ∈ Finset.Ico y (y + K), ω j z = false}
      = ENNReal.ofReal ((M : ℝ) * ((b : ℝ) * (1 - q) ^ K)) := by
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity)]
  rw [heq]

/-! ### 6. The carrier and its two uses -/

/-- **The explicit carrier.**  Every row is free of runs of `K` consecutive unmarked sites
below level `b`. -/
def Carrier (M b K : ℕ) : Set (Fin M → ℕ → Bool) :=
  {ω | ∀ j : Fin M, RunsOK (ω j) b K}

theorem carrier_compl_prob {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {M b K : ℕ} (hK : 1 ≤ K) :
    (markMeasureN M (boolMeasure q)) (Carrier M b K)ᶜ
      ≤ ENNReal.ofReal ((M : ℝ) * ((b : ℝ) * (1 - q) ^ K)) := by
  have h : (Carrier M b K)ᶜ = {ω : Fin M → ℕ → Bool | ∃ j : Fin M, ¬ RunsOK (ω j) b K} := by
    ext ω
    simp [Carrier]
  rw [h]
  exact measure_not_runsOK_le_N hq0 hq1 M b K hK

/-- On the carrier, every site below `b` has a bounded backward potential. -/
theorem carrier_hof_le {ω : Fin M → ℕ → Bool} (hω : ω ∈ Carrier M b K) (j : Fin M)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hK : 1 ≤ K) {x : ℕ} (hx : x + 1 ≤ b) :
    hof p (ω j) x ≤ 1 + 2 * (K : ℝ) + 2 * ((K : ℝ) / (1 - (1 - p) / p)) :=
  hof_le_of_runs hp1 hp2 hK (hω j) hx

/-- On the carrier, every truncated forward potential inside the window is bounded. -/
theorem carrier_Gtrunc_le {ω : Fin M → ℕ → Bool} (hω : ω ∈ Carrier M b K) (j : Fin M)
    (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hK : 1 ≤ K) {N x : ℕ} (hxN : x + N ≤ b) :
    Gtrunc p (ω j) N x ≤ 1 + (K : ℝ) / (1 - (1 - p) / p) :=
  Gtrunc_le_of_runs hp1 hp2 hK (hω j) hxN

/-- **`BddAbove` is a theorem, not a hypothesis**: for the paper's mark law every truncation
series is bounded above at every site, almost surely. -/
theorem ae_bddAbove_Gtrunc_N {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) (M : ℕ) :
    ∀ᵐ ω ∂(markMeasureN M (boolMeasure ((1 - p) ^ (m - 1)))), ∀ j : Fin M, ∀ x : ℕ,
      BddAbove (Set.range fun n => Gtrunc p (ω j) n (x + 1)) := by
  have hqpos : 0 < (1 - p) ^ (m - 1) := pow_pos (by linarith) _
  have hqhalf : (1 - p) ^ (m - 1) ≤ 1 / 2 := pow_one_sub_le_half hp1 hp2 hm
  obtain ⟨θ, hθ, hθ1⟩ := exists_theta hp1 hp2 hqpos (by linarith)
  have hqm0 : (0 : ℝ) ≤ (1 - p) ^ (m - 1) := by positivity
  have hqm1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have := pow_one_sub_le_half hp1 hp2 hm
    linarith
  set qm : ℝ := (1 - p) ^ (m - 1) with hqm
  set γ : ℝ := (1 - qm) * Real.exp (2 * θ) + qm * ((1 - p) / p) * Real.exp (θ / p) with hγ
  have hqm_lt : qm < 1 := by
    have := pow_one_sub_le_half hp1 hp2 hm
    rw [hqm]; linarith
  have hγpos : 0 < γ := by
    have h1 : 0 < 1 - qm := by linarith
    have h2 : 0 ≤ qm * ((1 - p) / p) * Real.exp (θ / p) := by positivity
    have h3 := Real.exp_pos (2 * θ)
    nlinarith
  have hγ1 : γ < 1 := hθ1
  haveI : IsProbabilityMeasure (boolMeasure qm) := isProbabilityMeasure_boolMeasure hqm0 hqm1
  have hsingle := bddAbove_range_Gtrunc_ae (p := p) (q := qm) (θ := θ) (γ := γ)
    hp1 hp2 hqm0 hqm1 hθ hγpos hγ1 hγ.le
  have hrow : ∀ j : Fin M, ∀ᵐ ω ∂(markMeasureN M (boolMeasure qm)), ∀ x : ℕ,
      BddAbove (Set.range fun n => Gtrunc p (ω j) n (x + 1)) :=
    fun j => markMeasureN_ae M j hsingle
  exact (ae_all_iff (μ := markMeasureN M (boolMeasure qm)) (ι := Fin M)).mpr hrow

/-- **The one carrier, in full.**  The intersection of the run carrier with the set where every
truncation series converges has failure probability at most `M·b·(1-q)^K`, and on it both the
explicit potential bounds and `BddAbove` hold. -/
theorem carrier_inter_prob {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m M b K : ℕ}
    (hm : 2 ≤ m) (hK : 1 ≤ K) :
    (markMeasureN M (boolMeasure ((1 - p) ^ (m - 1))))
        ((Carrier M b K) ∩ {ω | ∀ j : Fin M, ∀ x : ℕ,
          BddAbove (Set.range fun n => Gtrunc p (ω j) n (x + 1))})ᶜ
      ≤ ENNReal.ofReal ((M : ℝ) * ((b : ℝ) * (1 - ((1 - p) ^ (m - 1))) ^ K)) := by
  have hqm0 : (0 : ℝ) ≤ (1 - p) ^ (m - 1) := by positivity
  have hqm1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have := pow_one_sub_le_half hp1 hp2 hm
    linarith
  rw [Set.compl_inter]
  refine le_trans (measure_union_le _ _) ?_
  have hnull : (markMeasureN M (boolMeasure ((1 - p) ^ (m - 1))))
      {ω : Fin M → ℕ → Bool | ∀ j : Fin M, ∀ x : ℕ,
        BddAbove (Set.range fun n => Gtrunc p (ω j) n (x + 1))}ᶜ = 0 := by
    rw [Set.compl_ofPred, ← ae_iff]
    exact ae_bddAbove_Gtrunc_N hp1 hp2 hm M
  rw [hnull]
  simpa using carrier_compl_prob (q := (1 - p) ^ (m - 1)) hqm0 hqm1 hK

end

end SwarmRun
