/-
  Deterministic path content of Lemma `transience` of
  *Swarming of interacting excited random walks* (main_1d_revised.tex), §2.2.

  The paper's proof of `X^i_n -> +infty` splits into three parts:
  (1) the crossing estimate (eq. (cross)), i.e. `P(T_{a_k} < T_{b_k+1}) <= prod r`;
  (2) a Borel--Cantelli argument over the levels `k`, giving that, eventually in `k`,
      *no* time `s <= (k+1)^4` is a "bad" time at which the walker sits at `b_k`, the other
      walker's running maximum exceeds `b_k`, and the walker reaches `a_k` before `b_k+1`;
  (3) a purely pathwise/combinatorial argument concluding `X^i_n -> +infty` from (2) and
      the running-maximum lower bound `M^j_s >= s^{1/4}`.

  This file proves (3) in full together with the discrete skeleton of (1) (unit-step
  intermediate value theorem, first hitting times, `hitBefore`).  Parts (1)-(2) are the
  genuinely probabilistic ingredients; they are *not* assumed here in weakened form: they
  appear as the explicit hypotheses `hbad` (no bad time above level `K`) and `hMv` (the
  running-maximum lower bound), exactly the two statements the probabilistic half of the
  paper's proof supplies for this step.
-/
import Swarm.Imports
import Swarm.Speed

open Finset Filter
open scoped BigOperators Topology

namespace SwarmSpeed

variable {u v : ℕ → ℤ}

/-! ### Unit-step paths -/

/-- A nearest-neighbour path: every increment is `+1` or `-1`. -/
def UnitSteps (u : ℕ → ℤ) : Prop := ∀ n, u (n + 1) = u n + 1 ∨ u (n + 1) = u n - 1

/-- A unit-step path cannot climb faster than `n`. -/
lemma le_of_unitSteps (hu : UnitSteps u) : ∀ n : ℕ, u n ≤ u 0 + (n : ℤ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rcases hu n with h | h
      · rw [h]; push_cast; linarith
      · rw [h]; push_cast; linarith

/-- **Discrete intermediate value theorem** for unit-step paths. -/
lemma exists_eq_of_unitSteps (hu : UnitSteps u) {c : ℤ} :
    ∀ {m n : ℕ}, m ≤ n → u m ≤ c → c ≤ u n → ∃ r, m ≤ r ∧ r ≤ n ∧ u r = c := by
  intro m n
  induction n with
  | zero =>
      intro hmn h1 h2
      have hm0 : m = 0 := Nat.le_zero.mp hmn
      rw [hm0] at h1
      exact ⟨0, by omega, le_rfl, le_antisymm h1 h2⟩
  | succ n ih =>
      intro hmn h1 h2
      rcases Nat.eq_or_lt_of_le hmn with heq | hlt
      · rw [heq] at h1
        exact ⟨n + 1, by omega, le_rfl, le_antisymm h1 h2⟩
      · have hmn' : m ≤ n := by omega
        by_cases hc : c ≤ u n
        · obtain ⟨r, hr1, hr2, hr3⟩ := ih hmn' h1 hc
          exact ⟨r, hr1, by omega, hr3⟩
        · push Not at hc
          rcases hu n with h | h
          · refine ⟨n + 1, by omega, le_rfl, ?_⟩
            rw [h]; omega
          · rw [h] at h2; omega

/-- **Discrete intermediate value theorem, descending form**: if the path starts at or
above `c` and ends at or below `c`, it visits `c`. -/
lemma exists_eq_of_unitSteps' (hu : UnitSteps u) {m n : ℕ} (hmn : m ≤ n) {c : ℤ}
    (h1 : c ≤ u m) (h2 : u n ≤ c) : ∃ r, m ≤ r ∧ r ≤ n ∧ u r = c := by
  have hu' : UnitSteps (fun n => -u n) := by
    intro n
    rcases hu n with h | h
    · right; simp only [h]; ring
    · left; simp only [h]; ring
  have h1' : (fun n => -u n) m ≤ -c := by simp only; linarith
  have h2' : -c ≤ (fun n => -u n) n := by simp only; linarith
  obtain ⟨r, hr1, hr2, hr3⟩ := exists_eq_of_unitSteps hu' hmn h1' h2'
  exact ⟨r, hr1, hr2, by simpa using hr3⟩

/-! ### First hitting times -/

/-- The first time a path hits level `z` (noncomputable; existence is a hypothesis). -/
noncomputable def firstHit (u : ℕ → ℤ) (h : ∀ z, ∃ n, u n = z) (z : ℤ) : ℕ := Nat.find (h z)

lemma firstHit_spec (h : ∀ z, ∃ n, u n = z) (z : ℤ) : u (firstHit u h z) = z :=
  Nat.find_spec (h z)

lemma firstHit_le {h : ∀ z, ∃ n, u n = z} {z : ℤ} {r : ℕ} (hr : u r = z) :
    firstHit u h z ≤ r := Nat.find_min' (h z) hr

lemma firstHit_min {h : ∀ z, ∃ n, u n = z} {z : ℤ} {r : ℕ} (hr : r < firstHit u h z) :
    u r ≠ z := fun hc => Nat.find_min (h z) hr hc

/-- A unit-step path from `0` hits level `z` no earlier than time `z` (`z : ℕ`). -/
lemma le_firstHit (hu : UnitSteps u) (hu0 : u 0 = 0) (h : ∀ z, ∃ n, u n = z) {z : ℕ} :
    z ≤ firstHit u h (z : ℤ) := by
  by_contra hlt
  push Not at hlt
  have h1 : u (firstHit u h (z : ℤ)) ≤ (firstHit u h (z : ℤ) : ℤ) := by
    have h2 := le_of_unitSteps hu (firstHit u h (z : ℤ))
    rw [hu0] at h2; simpa using h2
  have h3 : u (firstHit u h (z : ℤ)) = (z : ℤ) := firstHit_spec h _
  rw [h3] at h1
  have h4 : (firstHit u h (z : ℤ) : ℤ) < (z : ℤ) := by exact_mod_cast hlt
  omega

/-- Hitting times of consecutive levels are ordered. -/
lemma firstHit_mono (hu : UnitSteps u) (hu0 : u 0 = 0) (h : ∀ z, ∃ n, u n = z) {z : ℕ} :
    firstHit u h (z : ℤ) ≤ firstHit u h ((z : ℤ) + 1) := by
  by_contra hlt
  push Not at hlt
  have h1 : u 0 ≤ (z : ℤ) := by rw [hu0]; omega
  have h2 : (z : ℤ) ≤ u (firstHit u h ((z : ℤ) + 1)) := by
    rw [firstHit_spec h]; omega
  obtain ⟨r, _, hr2, hr3⟩ := exists_eq_of_unitSteps hu (m := 0)
    (n := firstHit u h ((z : ℤ) + 1)) (Nat.zero_le _) h1 h2
  have h4 : firstHit u h (z : ℤ) ≤ r := firstHit_le hr3
  omega

/-! ### The "no deep return" condition -/

/-- `hitBefore u s z w`: starting at time `s`, the path `u` reaches level `w` before level `z`.
This is the paper's event `{T_w(s) < T_z(s)}`, in a form that avoids introducing the
possibly-infinite hitting time `T_z`. -/
def hitBefore (u : ℕ → ℤ) (s : ℕ) (z w : ℤ) : Prop :=
  ∃ t, s ≤ t ∧ u t = w ∧ ∀ r, s ≤ r → r < t → u r ≠ z

/-- **A walker does not return deeply below a level it has left**, unless one of the
paper's bad times `s` occurs.  This is the last paragraph of the proof of Lemma
`transience`: if `t` lies in the excursion `[tau_k, tau_{k+1})` of `u` and the walker drops
to `a k`, then the last visit `s` of level `b k` (which exists by the intermediate value
property) is a bad time — `u s = b k`, the other walker's running maximum already exceeds
`b k` (because `s >= k`), and `u` reaches `a k` before `b k + 1` — contradicting `hbad`. -/
theorem excursion_lower (hu : UnitSteps u) (hu0 : u 0 = 0) (h : ∀ z, ∃ n, u n = z)
    {b a : ℕ → ℕ} {k : ℕ} (hab : a k ≤ b k) (hbk : b k < k)
    (hbad : ∀ s ≤ (k + 1) ^ 4, ¬ (u s = (b k : ℤ) ∧ (b k : ℤ) + 1 ≤ runMax v s ∧
      hitBefore u s ((b k : ℤ) + 1) (a k)))
    (hτk : firstHit u h ((k : ℤ) + 1) ≤ (k + 1) ^ 4)
    (hMv : ∀ s, k ≤ s → s ≤ (k + 1) ^ 4 → (b k : ℤ) + 1 ≤ runMax v s)
    {t : ℕ} (ht1 : firstHit u h (k : ℤ) ≤ t) (ht2 : t < firstHit u h ((k : ℤ) + 1)) :
    (a k : ℤ) < u t := by
  classical
  by_contra hcon
  push Not at hcon
  have hk : (a k : ℤ) ≤ (k : ℤ) := by
    have h1 : a k ≤ k := le_of_lt (lt_of_le_of_lt hab hbk)
    exact_mod_cast h1
  have hk' : (k : ℤ) ≤ u (firstHit u h (k : ℤ)) := by rw [firstHit_spec h]
  have hab' : (a k : ℤ) ≤ (b k : ℤ) := by exact_mod_cast hab
  have hbk' : (b k : ℤ) ≤ (k : ℤ) := by exact_mod_cast le_of_lt hbk
  -- last visit `t'` of level `a k` before time `t`
  obtain ⟨r₀, hr₀1, hr₀2, hr₀3⟩ := exists_eq_of_unitSteps' hu ht1 (le_trans hk hk') hcon
  set t' : ℕ := Nat.findGreatest (fun r => u r = (a k : ℤ)) t with ht'
  have ht'le : t' ≤ t := Nat.findGreatest_le t
  have ht'mem : u t' = (a k : ℤ) :=
    Nat.findGreatest_spec (P := fun r => u r = (a k : ℤ)) hr₀2 hr₀3
  have ht'ge : firstHit u h (k : ℤ) ≤ t' :=
    le_trans hr₀1 (Nat.le_findGreatest (P := fun r => u r = (a k : ℤ)) hr₀2 hr₀3)
  -- last visit `s` of level `b k` before time `t'`
  obtain ⟨r₁, hr₁1, hr₁2, hr₁3⟩ :=
    exists_eq_of_unitSteps' hu ht'ge (le_trans hbk' hk') (by rw [ht'mem]; exact hab')
  set s : ℕ := Nat.findGreatest (fun r => u r = (b k : ℤ)) t' with hs
  have hsle : s ≤ t' := Nat.findGreatest_le t'
  have hsmem : u s = (b k : ℤ) :=
    Nat.findGreatest_spec (P := fun r => u r = (b k : ℤ)) hr₁2 hr₁3
  have hsge : firstHit u h (k : ℤ) ≤ s :=
    le_trans hr₁1 (Nat.le_findGreatest (P := fun r => u r = (b k : ℤ)) hr₁2 hr₁3)
  have hk_le_s : k ≤ s := le_trans (le_firstHit hu hu0 h) hsge
  have hs4 : s ≤ (k + 1) ^ 4 := by omega
  have hMvs : (b k : ℤ) + 1 ≤ runMax v s := hMv s hk_le_s hs4
  have hhit : hitBefore u s ((b k : ℤ) + 1) (a k) := by
    refine ⟨t', hsle, ht'mem, ?_⟩
    intro r hr1 hr2 hr3
    have hbk2 : (b k : ℤ) ≤ u r := by rw [hr3]; linarith
    have hbk3 : u t' ≤ (b k : ℤ) := by rw [ht'mem]; exact hab'
    obtain ⟨r', hr'1, hr'2, hr'3⟩ :=
      exists_eq_of_unitSteps' (m := r) (n := t') (c := (b k : ℤ)) hu (le_of_lt hr2) hbk2 hbk3
    have hle1 : r' ≤ s := Nat.le_findGreatest (P := fun r => u r = (b k : ℤ)) (by omega) hr'3
    have hrs : r' = r := by omega
    rw [hrs] at hr'3
    omega
  exact hbad s hs4 ⟨hsmem, hMvs, hhit⟩

/-! ### From "no deep return" to transience -/

/-- **Lemma `transience`, pathwise part.**  If, above some level `K`, there is no bad time
`s <= (k+1)^4` (as in `excursion_lower`), the running maximum of `v` dominates `s^{1/4}` in
that range, level `k+1` is reached before time `(k+1)^4`, and `a k -> infinity`, then
`u n -> +infinity`. -/
theorem tendsto_atTop_of_no_deep_returns (hu : UnitSteps u) (hu0 : u 0 = 0)
    (h : ∀ z, ∃ n, u n = z) {b a : ℕ → ℕ} {K : ℕ}
    (hab : ∀ k ≥ K, a k ≤ b k) (hbk : ∀ k ≥ K, b k < k)
    (ha_mono : Monotone a) (ha : Tendsto a atTop atTop)
    (hbad : ∀ k ≥ K, ∀ s ≤ (k + 1) ^ 4, ¬ (u s = (b k : ℤ) ∧ (b k : ℤ) + 1 ≤ runMax v s ∧
      hitBefore u s ((b k : ℤ) + 1) (a k)))
    (hτk : ∀ k ≥ K, firstHit u h ((k : ℤ) + 1) ≤ (k + 1) ^ 4)
    (hMv : ∀ k ≥ K, ∀ s, k ≤ s → s ≤ (k + 1) ^ 4 → (b k : ℤ) + 1 ≤ runMax v s) :
    Tendsto u atTop atTop := by
  classical
  rw [tendsto_atTop_atTop]
  intro A
  obtain ⟨k₀, hk₀K, hk₀A⟩ : ∃ k, K ≤ k ∧ A ≤ (a k : ℤ) := by
    have h1 : ∀ᶠ k : ℕ in atTop, A ≤ (a k : ℤ) := by
      obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.mp ha) A.toNat
      filter_upwards [eventually_ge_atTop B] with k hk
      have h2 : A.toNat ≤ a k := hB k hk
      have h3 : (A.toNat : ℤ) ≤ (a k : ℤ) := by exact_mod_cast h2
      have h4 : A ≤ (A.toNat : ℤ) := by omega
      linarith
    obtain ⟨k, hk1, hk2⟩ := (h1.and (eventually_ge_atTop K)).exists
    exact ⟨k, hk2, hk1⟩
  refine ⟨firstHit u h (k₀ : ℤ), fun n hn => ?_⟩
  have hk₀n : k₀ ≤ n := le_trans (le_firstHit hu hu0 h) hn
  -- the level `j` of the excursion that contains time `n`
  set P : ℕ → Prop := fun j => firstHit u h (j : ℤ) ≤ n with hP
  have hPk : P k₀ := hn
  set j : ℕ := Nat.findGreatest P (n + 1) with hj
  have hjle : P j := Nat.findGreatest_spec (P := P) (by omega) hPk
  have hjK : k₀ ≤ j := Nat.le_findGreatest (P := P) (by omega) hPk
  have hjle' : firstHit u h (j : ℤ) ≤ n := hjle
  have hjn : j ≤ n := by
    have h2 : j ≤ firstHit u h (j : ℤ) := le_firstHit hu hu0 h
    omega
  have hcast : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  have hlt : n < firstHit u h ((j : ℤ) + 1) := by
    by_contra hle
    push Not at hle
    have hPj1 : P (j + 1) := by
      show firstHit u h (((j + 1 : ℕ)) : ℤ) ≤ n
      rw [hcast]; exact hle
    have h3 : j + 1 ≤ j := Nat.le_findGreatest (P := P) (by omega) hPj1
    omega
  have hjK' : K ≤ j := le_trans hk₀K hjK
  have hexc := excursion_lower hu hu0 h (hab j hjK') (hbk j hjK')
    (hbad j hjK') (hτk j hjK') (hMv j hjK') hjle' hlt
  have hle_a : (a k₀ : ℤ) ≤ (a j : ℤ) := by exact_mod_cast ha_mono hjK
  linarith

end SwarmSpeed
